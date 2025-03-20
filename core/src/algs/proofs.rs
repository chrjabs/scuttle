//! # Proof Writing Functionality

use core::fmt;
use std::{
    io,
    marker::PhantomData,
    sync::{atomic::AtomicBool, Arc},
};

#[cfg(feature = "interrupt-oracle")]
use std::sync::Mutex;

use cadical_veripb_tracer::{CadicalCertCollector, CadicalTracer};
use pigeons::{
    AbsConstraintId, Axiom, ConstraintId, ConstraintLike, Derivation, OperationLike,
    OperationSequence, Order, OrderVar, Proof, ProofGoal, ProofGoalId, ProofOnlyVar, Substitution,
    VarLike,
};
use rustsat::{
    encodings::{atomics, card::DbTotalizer, pb::DbGte, CollectCertClauses},
    instances::ManageVars,
    solvers::Initialize,
    types::{Assignment, Clause, Lit, RsHashMap, TernaryVal, Var},
};
use rustsat_cadical::CaDiCaL;

use crate::{
    types::{Instance, ObjEncoding, Objective, VarManager},
    KernelOptions, Limits, Stats,
};

use super::default_blocking_clause;

/// Trait for initializing algorithms
pub trait InitCert: super::Init {
    type ProofWriter: io::Write;

    /// Initialization of the algorithm providing all optional input
    fn new_cert<Cls>(
        clauses: Cls,
        objs: Vec<Objective>,
        var_manager: VarManager,
        opts: KernelOptions,
        proof: Proof<Self::ProofWriter>,
        block_clause_gen: <Self as super::Init>::BlockClauseGen,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = (Clause, pigeons::AbsConstraintId)>;

    /// Initialization of the algorithm using an [`Instance`] rather than iterators
    fn from_instance_cert(
        inst: Instance,
        opts: KernelOptions,
        proof: Proof<Self::ProofWriter>,
        block_clause_gen: <Self as super::Init>::BlockClauseGen,
    ) -> anyhow::Result<Self> {
        Self::new_cert(
            inst.clauses.into_iter().map(|(cl, id)| (cl, id.unwrap())),
            inst.objs,
            inst.vm,
            opts,
            proof,
            block_clause_gen,
        )
    }
}

pub trait InitCertDefaultBlock: InitCert<BlockClauseGen = fn(Assignment) -> Clause> {
    /// Initializes the algorithm with the default blocking clause generator
    fn new_default_blocking_cert<Cls>(
        clauses: Cls,
        objs: Vec<Objective>,
        var_manager: VarManager,
        opts: KernelOptions,
        proof: Proof<Self::ProofWriter>,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = (Clause, pigeons::AbsConstraintId)>,
    {
        Self::new_cert(
            clauses,
            objs,
            var_manager,
            opts,
            proof,
            default_blocking_clause,
        )
    }

    /// Initializes the algorithm using an [`Instance`] rather than iterators with the default
    /// blocking clause generator
    fn from_instance_default_blocking_cert(
        inst: Instance,
        opts: KernelOptions,
        proof: Proof<Self::ProofWriter>,
    ) -> anyhow::Result<Self> {
        Self::new_cert(
            inst.clauses.into_iter().map(|(cl, id)| (cl, id.unwrap())),
            inst.objs,
            inst.vm,
            opts,
            proof,
            default_blocking_clause,
        )
    }
}

impl<Alg> InitCertDefaultBlock for Alg where Alg: InitCert<BlockClauseGen = fn(Assignment) -> Clause>
{}

/// Stuff to keep in the solver for proof logging
pub struct ProofStuff<ProofW: io::Write> {
    /// The handle of the proof tracer
    pub pt_handle: rustsat_cadical::ProofTracerHandle<CadicalTracer<ProofW>>,
    /// Mapping literal values to other literal values or other expressions
    pub value_map: Vec<(Axiom<AnyVar>, Value)>,
    /// Reified objective constraints
    obj_bound_constrs: RsHashMap<(usize, usize), (Axiom<AnyVar>, AbsConstraintId, AbsConstraintId)>,
}

#[derive(Debug, Clone, Copy)]
pub enum Value {
    Identical(Lit),
    ObjAtLeast(usize, usize),
}

pub fn init_proof<W>(
    writer: W,
    n_constraints: usize,
    objs: &[Objective],
) -> io::Result<pigeons::Proof<W>>
where
    W: io::Write,
{
    let mut proof = pigeons::Proof::new_with_conclusion(
        writer,
        n_constraints,
        false,
        pigeons::OutputGuarantee::None,
        &pigeons::Conclusion::<&str>::Unsat(Some(pigeons::ConstraintId::last(1))),
    )?;
    let order = crate::algs::proofs::objectives_as_order(&objs);
    proof.define_order(&order)?;
    proof.load_order(order.name(), order.used_vars())?;
    Ok(proof)
}

fn objectives_as_order(objs: &[Objective]) -> Order<Var, LbConstraint<OrderVar<Var>>> {
    let mut order = Order::<Var, LbConstraint<_>>::new(String::from("pareto"));
    for (idx, obj) in objs.iter().enumerate() {
        let mult = isize::try_from(obj.unit_weight())
            .expect("can only handle unit weight up to `isize::MAX`");
        let constr = LbConstraint {
            lits: obj
                .iter()
                .flat_map(|(l, w)| {
                    let w = isize::try_from(w).expect("can only handle weights up to `isize::MAX`");
                    let (u, v) = order.use_var(l.var());
                    [
                        (-w * mult, u.axiom(l.is_neg())),
                        (w * mult, v.axiom(l.is_neg())),
                    ]
                })
                .collect(),
            bound: 0,
        };
        // For O_idx, this proof sums up the following constraints
        // - O_idx(u) <= O_idx(v)
        // - O_idx(v) <= O_idx(w)
        // - O_idx(u) > O_idx(w)
        // This will always lead to a contradiction, proving transitivity
        let trans_proof = vec![Derivation::from(
            OperationSequence::<OrderVar<Var>>::from(ConstraintId::abs(idx + 1))
                + ConstraintId::abs(objs.len() + idx + 1)
                + ConstraintId::last(1),
        )];
        order.add_definition_constraint(constr, trans_proof, None)
    }
    order
}

pub fn certify_pmin_cut<ProofW>(
    obj_encs: &[ObjEncoding<
        rustsat::encodings::pb::DbGte,
        rustsat::encodings::card::DbTotalizer,
    >],
    objs: &[Objective],
    costs: &[usize],
    witness: &Assignment,
    max_enc_var: Var,
    proof_stuff: &mut ProofStuff<ProofW>,
    oracle: &mut rustsat_cadical::CaDiCaL<'_, '_>,
) -> io::Result<AbsConstraintId>
where
    ProofW: io::Write + 'static,
{
    #[cfg(feature = "verbose-proofs")]
    {
        use itertools::Itertools;
        oracle
            .proof_tracer_mut(&proof_stuff.pt_handle)
            .proof_mut()
            .comment(&format_args!(
                "Introducing P-minimal cut for costs [{}] based on the following witness:",
                costs.iter().format(", "),
            ))?;
        oracle
            .proof_tracer_mut(&proof_stuff.pt_handle)
            .proof_mut()
            .comment(&format_args!("{witness}"))?;
    }

    // buid the "ideal" cut. this is only valid with the strict proof semantics
    let cut_data: Vec<_> = obj_encs
        .iter()
        .zip(objs)
        .zip(costs)
        .map(|((enc, obj), cst)| {
            if *cst <= obj.lower_bound() {
                debug_assert!(*cst == 0 || obj.reform_id().is_some());
                return (None, obj.reform_id());
            }
            if obj.n_lits() == 1 {
                let lit = !obj.iter().next().unwrap().0;
                return (Some(AnyVar::Solver(lit.var()).axiom(lit.is_neg())), None);
            }
            // weird edge case with a single oll totalizer output as the objective encoding
            if enc.n_output_lits() == 1 {
                let lit = enc.enforce_ub(enc.offset()).unwrap()[0];
                return (Some(AnyVar::Solver(lit.var()).axiom(lit.is_neg())), None);
            }
            let (lit, def) = if enc.is_buffer_empty() {
                // totalizer output semantics are identical with the required semantics, can
                // therefore reuse totalizer output
                let (olit, defs) = enc.output_proof_details(*cst);
                (
                    AnyVar::Solver(olit.var()).axiom(olit.is_neg()),
                    defs.only_if_def,
                )
            } else {
                // totalizer output semantics do _not_ include the entire objective and can
                // therefore not be used
                let (lit, _, def) = get_obj_bound_constraint(*cst, obj, proof_stuff, oracle)
                    .expect("failed to write proof");
                (lit, Some(def))
            };
            debug_assert!(def.is_some());
            (Some(!lit), def)
        })
        .collect();
    let cut = LbConstraint::clause(cut_data.iter().filter_map(|&(l, _)| l));

    let ProofStuff {
        pt_handle,
        value_map,
        ..
    } = proof_stuff;
    let proof = oracle.proof_tracer_mut(pt_handle).proof_mut();

    // Extend witness to encoding variables under strict semantics
    // TODO: avoid clone
    let fixed_witness: Vec<Axiom<AnyVar>> = {
        // NOTE: assignments from `extend_assignment` have precendence, as they weill overwrite
        // assignments coming from the witness
        let mut fixed_witness: Assignment = witness
            .iter()
            .chain(
                obj_encs
                    .iter()
                    .flat_map(|enc| enc.extend_assignment(witness)),
            )
            .collect();
        // NOTE: Need to do this in two steps since the identities depend on the encoding
        // assignments
        let mut solver_vars = Vec::new();
        // TODO: clean this up a bit
        for &(this, that) in value_map.iter() {
            match that {
                Value::Identical(that) => match fixed_witness.lit_value(that) {
                    TernaryVal::True => match this.var() {
                        AnyVar::Proof(_) => solver_vars.push(this),
                        AnyVar::Solver(var) => fixed_witness.assign_lit(var.lit(this.is_neg())),
                    },
                    TernaryVal::False => match this.var() {
                        AnyVar::Proof(_) => solver_vars.push(!this),
                        AnyVar::Solver(var) => fixed_witness.assign_lit(var.lit(!this.is_neg())),
                    },
                    TernaryVal::DontCare => {
                        panic!("need assignment for left of identity ({this:?}, {that})")
                    }
                },
                Value::ObjAtLeast(obj_idx, value) => {
                    if costs[obj_idx] >= value {
                        match this.var() {
                            AnyVar::Proof(_) => solver_vars.push(this),
                            AnyVar::Solver(var) => fixed_witness.assign_lit(var.lit(this.is_neg())),
                        }
                    } else {
                        match this.var() {
                            AnyVar::Proof(_) => solver_vars.push(!this),
                            AnyVar::Solver(var) => {
                                fixed_witness.assign_lit(var.lit(!this.is_neg()))
                            }
                        }
                    }
                }
            }
        }
        fixed_witness
            .into_iter()
            .map(axiom)
            .chain(solver_vars)
            .collect()
    };

    let negation_id = ConstraintId::from(proof.next_id());

    // Map all weakly dominated solutions to the witness itself
    let map_dom = proof.redundant(
        &LbConstraint {
            lits: fixed_witness
                .iter()
                .map(|l| (1, *l))
                .chain(
                    cut.lits
                        .iter()
                        .map(|(_, l)| (isize::try_from(fixed_witness.len() + 1).unwrap(), *l)),
                )
                .collect(),
            bound: isize::try_from(fixed_witness.len())
                .expect("can only handle bounds up to `usize::MAX`"),
        },
        fixed_witness.iter().map(|l| Substitution::from(*l)),
        cut_data
            .into_iter()
            .zip(objs)
            .zip(costs)
            .enumerate()
            .filter_map(|(idx, ((dat, obj), cst))| {
                match dat {
                    (None, Some(reform_id)) => {
                        // Cost is lower bound derived in core boosting
                        debug_assert!(*cst <= obj.lower_bound());
                        Some(ProofGoal::new(
                            ProofGoalId::specific(idx + 2),
                            [Derivation::from(
                                OperationSequence::from(ConstraintId::from(reform_id))
                                    + ConstraintId::last(1),
                            )],
                        ))
                    }
                    (Some(lit), Some(def)) => {
                        // Prove that the witness dominates
                        let mut conf_deriv = (OperationSequence::from(ConstraintId::last(1))
                            * (*cst - obj.lower_bound()))
                            + def;
                        if let Some(reform_id) = obj.reform_id() {
                            conf_deriv += reform_id;
                        }
                        conf_deriv *= obj.unit_weight();
                        conf_deriv += ConstraintId::last(2);
                        Some(ProofGoal::new(
                            ProofGoalId::specific(idx + 2),
                            [
                                Derivation::Rup(LbConstraint::clause([!lit]), vec![negation_id]),
                                Derivation::from(conf_deriv),
                            ],
                        ))
                    }
                    (_, None) => {
                        // Cost is trivial lower bound of objective or objective is trivial
                        // NOTE: third case is that the encoding has only one output
                        // debug_assert!(obj.n_lits() == 1 || *cst == 0);
                        None
                    }
                }
            }),
    )?;

    // Exclude witness
    let exclude = proof.exclude_solution(
        witness
            .clone()
            .truncate(max_enc_var)
            .iter()
            .map(Axiom::from),
    )?;
    #[cfg(feature = "verbose-proofs")]
    proof.equals(
        &LbConstraint::clause(fixed_witness.iter().map(|l| !*l)),
        Some(exclude.into()),
    )?;

    // Add the actual P-minimal cut as a clause
    let cut_id =
        proof.reverse_unit_prop(&cut, [map_dom, exclude].into_iter().map(ConstraintId::from))?;
    // Need to move to core to be able to delete the derivation constraints
    proof.move_ids_to_core([ConstraintId::from(cut_id)])?;

    // Remove auxiliary constraints
    //proof.delete_ids::<AnyVar, LbConstraint<AnyVar>, _, _>(
    proof.delete_ids(
        [exclude, map_dom].into_iter().map(ConstraintId::from),
        [ProofGoal::new(
            ProofGoalId::specific(1),
            [Derivation::Rup(
                Clause::default(),
                vec![ConstraintId::last(1), cut_id.into()],
            )],
        )],
    )?;

    Ok(cut_id)
}

/// Certifies a reification of a cube of assumptions stemming from an encoding
///
/// The certification will make the first assumption equal to the reification literal, while all
/// others are implied by the reification literal
///
/// Returns the ID stating that the first assumption implies the reification literal
pub fn certify_assump_reification<ProofW>(
    oracle: &mut CaDiCaL<'_, '_>,
    proof_stuff: &mut ProofStuff<ProofW>,
    obj: &Objective,
    enc: &ObjEncoding<DbGte, DbTotalizer>,
    value: usize,
    reif_lit: Lit,
    assumps: &[Lit],
) -> anyhow::Result<AbsConstraintId>
where
    ProofW: io::Write + 'static,
{
    #[cfg(feature = "verbose-proofs")]
    oracle
        .proof_tracer_mut(&proof_stuff.pt_handle)
        .proof_mut()
        .comment(&"reification of multiple assumptions for one objective encoding")?;
    Ok(if enc.is_buffer_empty() {
        let ProofStuff {
            pt_handle,
            value_map,
            ..
        } = proof_stuff;
        let proof = oracle.proof_tracer_mut(pt_handle).proof_mut();

        // NOTE: this assumes that the assumptions are outputs in increasing order
        let mut assumps = assumps.iter();
        let a = *assumps.next().unwrap();
        // in the proof, the reification literal is going to be _equal_ to the lowest
        // output
        let clause = atomics::lit_impl_lit(reif_lit, a);
        let if_def = proof.redundant(&clause, [reif_lit.var().substitute_fixed(false)], None)?;
        let only_if_def = proof.redundant(
            &atomics::lit_impl_lit(a, reif_lit),
            [reif_lit.var().substitute_fixed(true)],
            None,
        )?;
        value_map.push((axiom(reif_lit), Value::Identical(a)));
        CadicalCertCollector::new(oracle, pt_handle).add_cert_clause(clause, if_def)?;
        let (first_olit, first_sems) = enc.output_proof_details(value);
        debug_assert_eq!(!first_olit, a);
        // all remaining assumptions are implied by the reification literal
        let mut val = value;
        for &a in assumps {
            let proof = oracle.proof_tracer_mut(pt_handle).proof_mut();
            val = enc.next_higher(val);
            // first convince veripb that `olit -> first_olit`
            let (olit, sems) = enc.output_proof_details(val);
            debug_assert_eq!(!olit, a);
            let implication = proof.operations::<Var>(
                &((OperationSequence::from(first_sems.if_def.unwrap())
                    + sems.only_if_def.unwrap())
                    / (val - value + 1))
                    .saturate(),
            )?;
            #[cfg(feature = "verbose-proofs")]
            proof.equals(
                &rustsat::clause![!olit, first_olit],
                Some(ConstraintId::last(1)),
            )?;
            let clause = atomics::lit_impl_lit(reif_lit, a);
            let id = proof.reverse_unit_prop(&clause, [implication.into(), if_def.into()])?;
            CadicalCertCollector::new(oracle, pt_handle).add_cert_clause(clause, id)?;
            // delete implication
            oracle
                .proof_tracer_mut(pt_handle)
                .proof_mut()
                .delete_ids::<AnyVar, LbConstraint<_>, _, _>(
                    [ConstraintId::from(implication)],
                    None,
                )?;
        }
        only_if_def
    } else {
        // cannot reuse first totalizer output as semantics of the reification literal, need to
        // introduce new proof variable for needed semantics
        let (ideal_lit, def_1, _) = get_obj_bound_constraint(value, obj, proof_stuff, oracle)?;

        let ProofStuff {
            pt_handle,
            value_map,
            ..
        } = proof_stuff;
        let proof = oracle.proof_tracer_mut(pt_handle).proof_mut();

        // the reification variable is implied by the objective bound
        let if_def = proof.redundant(
            &LbConstraint::clause([axiom(!reif_lit), !ideal_lit]),
            [AnyVar::Solver(reif_lit.var()).substitute_fixed(false)],
            None,
        )?;
        let only_if_def = proof.redundant(
            &LbConstraint::clause([axiom(reif_lit), (ideal_lit)]),
            [AnyVar::Solver(reif_lit.var()).substitute_fixed(true)],
            None,
        )?;
        value_map.push((axiom(!reif_lit), Value::ObjAtLeast(obj.idx(), value)));
        let mut val = value;
        for &a in assumps {
            let proof = oracle.proof_tracer_mut(pt_handle).proof_mut();
            let clause = atomics::lit_impl_lit(reif_lit, a);
            let (olit, sems) = enc.output_proof_details(val);
            // NOTE: this assumes that objective encoding variables are higher than GTE variables
            // and that the buffered input variables are first in the assumptions
            let id = if a.var() < olit.var() {
                // this is an input literal with weight higher than the bound
                proof.reverse_unit_prop(
                    &clause,
                    [if_def, def_1].into_iter().map(ConstraintId::from),
                )?
            } else {
                // this is an output literal of a subtree
                debug_assert_eq!(!olit, a);
                let tmp = proof.operations::<AnyVar>(
                    &(OperationSequence::from(def_1) + sems.only_if_def.unwrap()),
                )?;
                let id = proof.reverse_unit_prop(
                    &clause,
                    [if_def, tmp].into_iter().map(ConstraintId::from),
                )?;
                proof.delete_ids::<AnyVar, LbConstraint<AnyVar>, _, _>(
                    [ConstraintId::from(tmp)],
                    None,
                )?;
                val = enc.next_higher(val);
                id
            };
            CadicalCertCollector::new(oracle, pt_handle).add_cert_clause(clause, id)?;
        }
        only_if_def
    })
}

pub fn linsu_certify_lower_bound<ProofW>(
    base_assumps: &[Lit],
    cost: usize,
    core: &[Lit],
    obj: &Objective,
    encoding: &ObjEncoding<DbGte, DbTotalizer>,
    proof_stuff: &mut ProofStuff<ProofW>,
    oracle: &mut rustsat_cadical::CaDiCaL<'_, '_>,
) -> io::Result<AbsConstraintId>
where
    ProofW: io::Write + 'static,
{
    // derive lower bound on objective in proof
    let core_id = oracle
        .proof_tracer_mut(&proof_stuff.pt_handle)
        .core_id()
        .expect("expected core id in proof");
    #[cfg(feature = "verbose-proofs")]
    {
        use itertools::Itertools;
        oracle
            .proof_tracer_mut(&proof_stuff.pt_handle)
            .proof_mut()
            .comment(&format_args!(
                "certifying linsu lower bound for bound {cost} from core [{}]",
                core.iter().format(", ")
            ))?;
    }
    let mut start = 0;
    for &ba in base_assumps {
        if core[start] == !ba {
            start += 1;
        }
    }
    let core_id = if encoding.is_buffer_empty() {
        // encoding has empty buffer, output semantics can therefore be reused for objective bound
        // semantics
        let (first_olit, first_sems) = encoding.output_proof_details(cost);
        if core.len() == 1 {
            // unit core explicitly implies bound
            debug_assert_eq!(core[0], first_olit);
            core_id
        } else {
            let proof = oracle.proof_tracer_mut(&proof_stuff.pt_handle).proof_mut();

            // convince veripb that `core_lit -> first_olit` and therefore
            // rewrite core as `first_olit` unit
            // NOTE: this assumes that
            // - the base assumptions are in the core first
            // - the outputs are in the core in order of increasing value
            let start = if core[start] == first_olit {
                start + 1
            } else {
                start
            };
            let mut implications = Vec::with_capacity(core.len());
            let mut val = cost;
            for &clit in &core[start..] {
                let (mut olit, mut sems) = encoding.output_proof_details(val);
                while clit != olit {
                    val = encoding.next_higher(val);
                    (olit, sems) = encoding.output_proof_details(val);
                }
                let implication = proof.operations::<Var>(
                    &((OperationSequence::from(first_sems.if_def.unwrap())
                        + sems.only_if_def.unwrap())
                        / (val - cost + 1))
                        .saturate(),
                )?;
                #[cfg(feature = "verbose-proofs")]
                proof.equals(
                    &rustsat::clause![!olit, first_olit],
                    Some(ConstraintId::from(implication)),
                )?;
                implications.push(implication);
                val = encoding.next_higher(val);
            }
            if !implications.is_empty() || !base_assumps.is_empty() {
                // NOTE: we always run this case with base assumptions to ensure that all base
                // assumptions are present in the returned ID

                // rewrite the core
                let core_id = proof.reverse_unit_prop(
                    &atomics::cube_impl_lit(base_assumps, first_olit),
                    implications
                        .iter()
                        .copied()
                        .chain([core_id])
                        .map(ConstraintId::from),
                )?;
                if !implications.is_empty() {
                    // delete implications
                    proof.delete_ids::<AnyVar, LbConstraint<_>, _, _>(
                        implications.into_iter().map(ConstraintId::from),
                        None,
                    )?;
                }
                core_id
            } else {
                core_id
            }
        }
    } else {
        // cannot reuse first totalizer output as semantics of the reification literal, need to
        // introduce new proof variable for needed semantics
        let (ideal_lit, def_1, _) = get_obj_bound_constraint(cost, obj, proof_stuff, oracle)?;

        let proof = oracle.proof_tracer_mut(&proof_stuff.pt_handle).proof_mut();

        let mut implications = Vec::with_capacity(core.len());
        let mut val = cost;
        for &clit in &core[start..] {
            let clause = LbConstraint::clause([axiom(!clit), ideal_lit]);
            let (mut olit, mut sems) = encoding.output_proof_details(val);
            let implication = if clit.var() < olit.var() {
                proof.reverse_unit_prop(&clause, [ConstraintId::from(def_1)])?
            } else {
                while clit.var() != olit.var() {
                    val = encoding.next_higher(val);
                    (olit, sems) = encoding.output_proof_details(val);
                }
                let tmp = proof.operations::<AnyVar>(
                    &(OperationSequence::from(def_1) + sems.only_if_def.unwrap()),
                )?;
                let implication = proof.reverse_unit_prop(&clause, [ConstraintId::from(tmp)])?;
                proof.delete_ids::<AnyVar, LbConstraint<AnyVar>, _, _>(
                    [ConstraintId::from(tmp)],
                    None,
                )?;
                val = encoding.next_higher(val);
                implication
            };
            implications.push(implication);
        }
        // rewrite the core
        // we do this always to ensure that all base assumptions and the proof-only var are there
        #[cfg(feature = "verbose-proofs")]
        proof.comment(&"the next constraint is a linsu bound")?;
        let core_id = proof.reverse_unit_prop(
            &LbConstraint::clause(base_assumps.iter().map(|l| axiom(!*l)).chain([ideal_lit])),
            implications
                .iter()
                .copied()
                .chain([core_id])
                .map(ConstraintId::from),
        )?;
        // delete implications
        proof.delete_ids::<AnyVar, LbConstraint<_>, _, _>(
            implications.into_iter().map(ConstraintId::from),
            None,
        )?;
        core_id
    };
    Ok(core_id)
}

pub fn get_obj_bound_constraint<ProofW>(
    value: usize,
    obj: &Objective,
    proof_stuff: &mut ProofStuff<ProofW>,
    oracle: &mut rustsat_cadical::CaDiCaL<'_, '_>,
) -> io::Result<(Axiom<AnyVar>, AbsConstraintId, AbsConstraintId)>
where
    ProofW: io::Write + 'static,
{
    let ProofStuff {
        pt_handle,
        value_map,
        obj_bound_constrs,
    } = proof_stuff;
    let proof = oracle.proof_tracer_mut(pt_handle).proof_mut();

    if let Some((lit, def_1, def_2)) = obj_bound_constrs.get(&(obj.idx(), value)) {
        return Ok((*lit, *def_1, *def_2));
    }
    // introduce a new objective bound reification
    let obj_reif_var = AnyVar::Proof(proof.new_proof_var());
    value_map.push((
        obj_reif_var.pos_axiom(),
        Value::ObjAtLeast(obj.idx(), value),
    ));
    #[cfg(feature = "verbose-proofs")]
    proof.comment(&format_args!(
        "{obj_reif_var} = objective {} is >= {value}",
        obj.idx()
    ))?;
    let bound = isize::try_from(obj.iter().fold(0, |sum, (_, w)| sum + w)).unwrap() + 1
        - isize::try_from(value).unwrap();
    let def_1 = proof.redundant(
        &LbConstraint {
            lits: obj
                .iter()
                .map(|(l, w)| {
                    let w = isize::try_from(w).expect("can only handle weights up to `isize::MAX`");
                    (w, AnyVar::Solver(l.var()).axiom(l.is_pos()))
                })
                .chain([(bound, obj_reif_var.pos_axiom())])
                .collect(),
            bound,
        },
        [obj_reif_var.substitute_fixed(true)],
        [],
    )?;
    let bound = isize::try_from(value).unwrap();
    let def_2 = proof.redundant(
        &LbConstraint {
            lits: obj
                .iter()
                .map(|(l, w)| {
                    let w = isize::try_from(w).expect("can only handle weights up to `isize::MAX`");
                    (w, AnyVar::Solver(l.var()).axiom(l.is_neg()))
                })
                .chain([(bound, obj_reif_var.neg_axiom())])
                .collect(),
            bound,
        },
        [obj_reif_var.substitute_fixed(false)],
        [],
    )?;
    obj_bound_constrs.insert((obj.idx(), value), (obj_reif_var.pos_axiom(), def_1, def_2));
    Ok((obj_reif_var.pos_axiom(), def_1, def_2))
}

pub struct LbConstraint<V: VarLike> {
    lits: Vec<(isize, Axiom<V>)>,
    bound: isize,
}

impl<V: VarLike> LbConstraint<V> {
    pub fn clause<I: IntoIterator<Item = Axiom<V>>>(iter: I) -> Self {
        LbConstraint {
            lits: iter.into_iter().map(|a| (1, a)).collect(),
            bound: 1,
        }
    }
}

impl<V: VarLike> ConstraintLike<V> for LbConstraint<V> {
    fn rhs(&self) -> isize {
        self.bound
    }

    fn sum_iter(&self) -> impl Iterator<Item = (isize, Axiom<V>)> {
        self.lits.iter().copied()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AnyVar {
    Proof(ProofOnlyVar),
    Solver(Var),
}

impl From<ProofOnlyVar> for AnyVar {
    fn from(value: ProofOnlyVar) -> Self {
        AnyVar::Proof(value)
    }
}

impl From<Var> for AnyVar {
    fn from(value: Var) -> Self {
        AnyVar::Solver(value)
    }
}

impl VarLike for AnyVar {
    type Formatter = Self;
}

pub fn axiom(lit: Lit) -> Axiom<AnyVar> {
    AnyVar::Solver(lit.var()).axiom(lit.is_neg())
}

impl fmt::Display for AnyVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AnyVar::Proof(v) => write!(f, "{}", <ProofOnlyVar as VarLike>::Formatter::from(*v)),
            AnyVar::Solver(v) => write!(f, "{}", <Var as VarLike>::Formatter::from(*v)),
        }
    }
}

impl<'term, 'learn, ProofW, OInit, BCG>
    super::Kernel<rustsat_cadical::CaDiCaL<'term, 'learn>, ProofW, OInit, BCG>
where
    ProofW: io::Write,
    OInit: Initialize<rustsat_cadical::CaDiCaL<'term, 'learn>>,
    BCG: Fn(Assignment) -> Clause,
{
    /// **NOTE**: the order must be already loaded in the proof, e.g., through calling
    /// [`init_proof`]
    pub fn new_cert<Cls>(
        clauses: Cls,
        objs: Vec<Objective>,
        var_manager: VarManager,
        bcg: BCG,
        proof: Proof<ProofW>,
        opts: KernelOptions,
    ) -> anyhow::Result<Self>
    where
        ProofW: io::Write + 'static,
        Cls: IntoIterator<Item = (Clause, pigeons::AbsConstraintId)>,
    {
        use rustsat::{encodings::CollectCertClauses, solvers::Solve};

        let mut stats = Stats {
            n_objs: 0,
            n_real_objs: 0,
            n_orig_clauses: 0,
            ..Default::default()
        };
        let mut oracle = OInit::init();
        let pt_handle = oracle.connect_proof_tracer(CadicalTracer::new(proof), true);
        oracle.reserve(var_manager.max_var().unwrap())?;
        let clauses: Vec<_> = clauses.into_iter().collect();
        let orig_cnf = if opts.store_cnf {
            Some(clauses.iter().map(|(cl, _)| cl.clone()).collect())
        } else {
            None
        };
        stats.n_orig_clauses = clauses.len();

        // Add clauses to solver
        let mut collector = CadicalCertCollector::new(&mut oracle, &pt_handle);
        collector.extend_cert_clauses(clauses)?;

        stats.n_objs = objs.len();
        stats.n_real_objs = objs.iter().fold(0, |cnt, o| {
            if matches!(o, Objective::Constant { .. }) {
                cnt
            } else {
                cnt + 1
            }
        });

        // Record objective literal occurrences
        #[cfg(feature = "sol-tightening")]
        let obj_lit_data = {
            use rustsat::types::RsHashMap;

            use crate::types::ObjLitData;

            let mut obj_lit_data: RsHashMap<_, ObjLitData> = RsHashMap::default();
            for (idx, obj) in objs.iter().enumerate() {
                match obj {
                    Objective::Weighted { lits, .. } => {
                        for &olit in lits.keys() {
                            match obj_lit_data.get_mut(&olit) {
                                Some(data) => data.objs.push(idx),
                                None => {
                                    obj_lit_data.insert(olit, ObjLitData { objs: vec![idx] });
                                }
                            }
                        }
                    }
                    Objective::Unweighted { lits, .. } => {
                        for &olit in lits {
                            match obj_lit_data.get_mut(&olit) {
                                Some(data) => data.objs.push(idx),
                                None => {
                                    obj_lit_data.insert(olit, ObjLitData { objs: vec![idx] });
                                }
                            }
                        }
                    }
                    Objective::Constant { .. } => (),
                }
            }
            obj_lit_data
        };
        #[cfg(feature = "sol-tightening")]
        {
            use rustsat::solvers::FreezeVar;
            // Freeze objective variables so that they are not removed
            for o in &objs {
                for (l, _) in o.iter() {
                    oracle.freeze_var(l.var())?;
                }
            }
        }
        #[cfg(feature = "interrupt-oracle")]
        let interrupter = {
            use rustsat::solvers::Interrupt;
            oracle.interrupter()
        };

        Ok(Self {
            oracle,
            var_manager,
            #[cfg(feature = "sol-tightening")]
            obj_lit_data,
            objs,
            orig_cnf,
            block_clause_gen: bcg,
            opts,
            stats,
            lims: Limits::none(),
            inpro: None,
            logger: None,
            term_flag: Arc::new(AtomicBool::new(false)),
            #[cfg(feature = "interrupt-oracle")]
            oracle_interrupter: Arc::new(Mutex::new(Box::new(interrupter))),
            proof_stuff: Some(ProofStuff {
                pt_handle,
                value_map: Vec::default(),
                obj_bound_constrs: RsHashMap::default(),
            }),
            _factory: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs::File,
        io::{BufRead, BufReader},
        path::Path,
        process::Command,
    };

    use pigeons::{Conclusion, ConstraintId, OutputGuarantee};
    use rustsat::lit;

    use crate::types::Objective;

    fn print_file<P: AsRef<Path>>(path: P) {
        println!();
        for line in BufReader::new(File::open(path).expect("could not open file")).lines() {
            println!("{}", line.unwrap());
        }
        println!();
    }

    fn verify_proof<P1: AsRef<Path>, P2: AsRef<Path>>(instance: P1, proof: P2) {
        println!("start checking proof");
        let out = Command::new("veripb")
            .arg(instance.as_ref())
            .arg(proof.as_ref())
            .output()
            .expect("failed to run veripb");
        print_file(proof);
        if out.status.success() {
            return;
        }
        panic!("verification failed: {out:?}")
    }

    fn new_proof(
        num_constraints: usize,
        optimization: bool,
    ) -> pigeons::Proof<tempfile::NamedTempFile> {
        let file = tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
        pigeons::Proof::new_with_conclusion(
            file,
            num_constraints,
            optimization,
            OutputGuarantee::None,
            &Conclusion::<&str>::Unsat(Some(ConstraintId::last(1))),
        )
        .expect("failed to start proof")
    }

    #[test]
    fn order_format() {
        let objectives = [
            Objective::Unweighted {
                offset: 3,
                unit_weight: 2,
                lits: vec![lit![0], !lit![1], lit![2], lit![3]],
                idx: 0,
                lower_bound: 0,
                reform_id: None,
            },
            Objective::Weighted {
                offset: 42,
                lits: [(lit![4], 4), (lit![2], 2), (lit![42], 42)]
                    .into_iter()
                    .collect(),
                idx: 1,
                lower_bound: 0,
                reform_id: None,
            },
            Objective::Constant {
                offset: 11,
                idx: 2,
                lower_bound: 0,
                reform_id: None,
            },
        ];
        let order = super::objectives_as_order(&objectives);
        let formatted = format!("{order}");
        let expected = r#"def_order pareto
  vars
    left u_x1 u_x2 u_x4 u_x43 u_x5 u_x3
    right v_x1 v_x2 v_x4 v_x43 v_x5 v_x3
    aux
  end
  def
    -2 u_x1 2 v_x1 -2 ~u_x2 2 ~v_x2 -2 u_x3 2 v_x3 -2 u_x4 2 v_x4 >= 0 ;
    -4 u_x5 4 v_x5 -2 u_x3 2 v_x3 -42 u_x43 42 v_x43 >= 0 ;
     >= 0 ;
  end
  transitivity
    vars
      fresh_right w_x1 w_x2 w_x4 w_x43 w_x5 w_x3
    end
    proof
      proofgoal #1
        pol 1 4 + -1 +
      qed -1
      proofgoal #2
        pol 2 5 + -1 +
      qed -1
      proofgoal #3
        pol 3 6 + -1 +
      qed -1
    qed
  end
end"#;
        debug_assert_eq!(&formatted, expected);
    }

    #[test]
    fn order_check() {
        let objectives = [
            Objective::Unweighted {
                offset: 3,
                unit_weight: 2,
                lits: vec![lit![0], !lit![1], lit![2], lit![3]],
                idx: 0,
                lower_bound: 0,
                reform_id: None,
            },
            Objective::Weighted {
                offset: 42,
                lits: [(lit![4], 4), (lit![2], 2), (lit![42], 42)]
                    .into_iter()
                    .collect(),
                idx: 1,
                lower_bound: 0,
                reform_id: None,
            },
            Objective::Constant {
                offset: 11,
                idx: 2,
                lower_bound: 0,
                reform_id: None,
            },
        ];
        let order = super::objectives_as_order(&objectives);

        let mut proof = new_proof(0, false);
        proof.define_order(&order).unwrap();
        proof.load_order(order.name(), order.used_vars()).unwrap();

        let proof_file = proof
            .conclude(
                pigeons::OutputGuarantee::None,
                &pigeons::Conclusion::<&str>::None,
            )
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(
            format!("{manifest}/../rustsat/data/empty.opb"),
            proof_file.path(),
        );
    }
}
