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
use pidgeons::{
    AbsConstraintId, Axiom, ConstraintId, ConstraintLike, Derivation, OperationSequence, Order,
    OrderVar, Proof, ProofGoal, ProofGoalId, ProofOnlyVar, VarLike,
};
use rustsat::{
    instances::{Cnf, ManageVars},
    solvers::Initialize,
    types::{Assignment, Clause, Lit, TernaryVal, Var, WLitIter},
};

use crate::{
    types::{Instance, ObjEncoding, Objective, VarManager},
    KernelOptions, Limits, Stats,
};

use super::default_blocking_clause;

/// Trait for initializing algorithms
pub trait InitCert: super::Init {
    type ProofWriter: io::Write;

    /// Initialization of the algorithm providing all optional input
    fn new_cert<Cls, Objs, Obj>(
        clauses: Cls,
        objs: Objs,
        var_manager: VarManager,
        opts: KernelOptions,
        proof: Proof<Self::ProofWriter>,
        block_clause_gen: <Self as super::Init>::BlockClauseGen,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = Clause>,
        Objs: IntoIterator<Item = (Obj, isize)>,
        Obj: WLitIter;

    /// Initialization of the algorithm using an [`Instance`] rather than iterators
    fn from_instance_cert(
        inst: Instance,
        opts: KernelOptions,
        proof: Proof<Self::ProofWriter>,
        block_clause_gen: <Self as super::Init>::BlockClauseGen,
    ) -> anyhow::Result<Self> {
        Self::new_cert(inst.cnf, inst.objs, inst.vm, opts, proof, block_clause_gen)
    }
}

pub trait InitCertDefaultBlock: InitCert<BlockClauseGen = fn(Assignment) -> Clause> {
    /// Initializes the algorithm with the default blocking clause generator
    fn new_default_blocking_cert<Cls, Objs, Obj>(
        clauses: Cls,
        objs: Objs,
        var_manager: VarManager,
        opts: KernelOptions,
        proof: Proof<Self::ProofWriter>,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = Clause>,
        Objs: IntoIterator<Item = (Obj, isize)>,
        Obj: WLitIter,
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
            inst.cnf,
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
                    let (u, v) = if l.is_pos() {
                        (u.pos_axiom(), v.pos_axiom())
                    } else {
                        (u.neg_axiom(), v.neg_axiom())
                    };
                    [(-w * mult, u), (w * mult, v)]
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

pub fn certify_pmin_cut<ProofW: io::Write>(
    obj_encs: &[ObjEncoding<
        rustsat::encodings::pb::DbGte,
        rustsat::encodings::card::DbTotalizer,
    >],
    objs: &[Objective],
    costs: &[usize],
    witness: &Assignment,
    identity_map: &[(Lit, Lit)],
    proof: &mut Proof<ProofW>,
) -> io::Result<AbsConstraintId> {
    #[cfg(feature = "verbose-proofs")]
    {
        proof.comment(&"Introducing P-minimal cut based on the following witness:")?;
        proof.comment(&format_args!("{witness}"))?;
    }

    // buid the "ideal" cut. this is only valid with the strict proof semantics
    let cut: Clause = obj_encs
        .iter()
        .zip(objs)
        .zip(costs)
        .flat_map(|((enc, obj), cst)| {
            if *cst <= enc.offset() {
                return None;
            }
            if obj.n_lits() == 1 {
                return Some(!obj.iter().next().unwrap().0);
            }
            let (olit, _) = enc.output_proof_details(*cst);
            Some(!olit)
        })
        .collect();

    // Extend witness to encoding variables under strict semantics
    // TODO: avoid clone
    let fixed_witness = {
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
        for &(this, that) in identity_map.iter() {
            match fixed_witness.lit_value(this) {
                TernaryVal::True => fixed_witness.assign_lit(that),
                TernaryVal::False => fixed_witness.assign_lit(!that),
                TernaryVal::DontCare => panic!("need assignment for left of identity"),
            }
        }
        fixed_witness
    };

    // Introduce indicator variable for being at accactly the solution in question
    let is_this = AnyVar::Proof(proof.new_proof_var());
    #[cfg(feature = "verbose-proofs")]
    proof.comment(&format_args!(
        "{is_this} = a solution is _exactly_ the witnessing one"
    ))?;
    let bound = isize::try_from(fixed_witness.len()).unwrap();
    // NOTE: need to use the fixed complete witness here to not have to include the totalizer in
    // the RUP hints for the cut constraint
    let is_this_def = proof.redundant(
        &LbConstraint {
            lits: [(bound, is_this.neg_axiom())]
                .into_iter()
                .chain(fixed_witness.iter().map(|l| (1, axiom(l))))
                .collect(),
            bound,
        },
        [is_this.substitute_fixed(false)],
        [],
    )?;

    // Map all weakly dominated solutions to the witness itself
    let map_dom =
        proof.redundant(
            &LbConstraint {
                lits: [(1, is_this.pos_axiom())]
                    .into_iter()
                    .chain(cut.iter().map(|l| (1, axiom(*l))))
                    .collect(),
                bound: 1,
            },
            [is_this.substitute_fixed(true)].into_iter().chain(
                fixed_witness
                    .iter()
                    .map(|l| AnyVar::Solver(l.var()).substitute_fixed(l.is_pos())),
            ),
            obj_encs.iter().zip(objs).zip(costs).enumerate().filter_map(
                |(idx, ((enc, obj), cst))| {
                    if *cst <= enc.offset() || obj.n_lits() <= 1 {
                        return None;
                    }
                    let (olit, sems) = enc.output_proof_details(*cst);
                    Some(ProofGoal::new(
                        ProofGoalId::specific(idx + 2),
                        [
                            Derivation::Rup(
                                LbConstraint {
                                    lits: vec![(1, axiom(olit))],
                                    bound: 1,
                                },
                                vec![(is_this_def + 1).into()],
                            ),
                            Derivation::from(
                                ((OperationSequence::from(ConstraintId::last(1)) * *cst)
                                    + sems.only_if_def.unwrap())
                                    * obj.unit_weight()
                                    + ConstraintId::last(2),
                            ),
                        ],
                    ))
                },
            ),
        )?;

    // Exclude witness
    let exclude = proof.exclude_solution(witness.iter().map(Axiom::from))?;
    #[cfg(feature = "verbose-proofs")]
    proof.equals(
        &LbConstraint {
            lits: fixed_witness
                .iter()
                .map(|l| (1, axiom(!l)))
                .chain([(1, is_this.neg_axiom())])
                .collect(),
            bound: 1,
        },
        Some(exclude.into()),
    )?;

    // Add the actual P-minimal cut as a clause
    let cut_id = proof.reverse_unit_prop(
        &cut,
        [map_dom, is_this_def, exclude]
            .into_iter()
            .map(ConstraintId::from),
    )?;
    // Need to move to core to be able to delete the derivation constraints
    proof.move_ids_to_core([ConstraintId::from(cut_id)])?;

    // Remove auxiliary constraints
    //proof.delete_ids::<AnyVar, LbConstraint<AnyVar>, _, _>(
    proof.delete_ids(
        [exclude, map_dom, is_this_def]
            .into_iter()
            .map(ConstraintId::from),
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

struct LbConstraint<V: VarLike> {
    lits: Vec<(isize, Axiom<V>)>,
    bound: isize,
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
enum AnyVar {
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

fn axiom(lit: Lit) -> Axiom<AnyVar> {
    if lit.is_pos() {
        AnyVar::Solver(lit.var()).pos_axiom()
    } else {
        AnyVar::Solver(lit.var()).neg_axiom()
    }
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
    pub fn new_cert<Cls, Objs, Obj>(
        clauses: Cls,
        objs: Objs,
        var_manager: VarManager,
        bcg: BCG,
        proof: Proof<ProofW>,
        opts: KernelOptions,
    ) -> anyhow::Result<Self>
    where
        ProofW: io::Write + 'static,
        Cls: IntoIterator<Item = Clause>,
        Objs: IntoIterator<Item = (Obj, isize)>,
        Obj: WLitIter,
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
        let clauses: Cnf = clauses.into_iter().collect();
        let orig_cnf = if opts.store_cnf {
            Some(clauses.clone())
        } else {
            None
        };
        stats.n_orig_clauses = clauses.len();

        // Add clauses to solver
        let mut collector = CadicalCertCollector::new(&mut oracle, &pt_handle);
        collector.extend_cert_clauses(
            clauses
                .into_iter()
                .enumerate()
                .map(|(idx, cl)| (cl, AbsConstraintId::new(idx + 1))),
        )?;

        let objs: Vec<_> = objs
            .into_iter()
            .map(|(wlits, offset)| Objective::new(wlits, offset))
            .collect();
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

        // Proof logging: write order to proof
        let order = objectives_as_order(&objs);
        let proof = oracle.proof_tracer_mut(&pt_handle).proof_mut();
        proof.define_order(&order)?;
        proof.load_order(order.name(), order.used_vars())?;

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
            proof_stuff: Some(super::ProofStuff {
                pt_handle,
                identity_map: Vec::default(),
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
    ) -> pidgeons::Proof<tempfile::NamedTempFile> {
        let file = tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
        pidgeons::Proof::new(file, num_constraints, optimization).expect("failed to start proof")
    }

    #[test]
    fn order_format() {
        let objectives = [
            Objective::Unweighted {
                offset: 3,
                unit_weight: 2,
                lits: vec![lit![0], !lit![1], lit![2], lit![3]],
            },
            Objective::Weighted {
                offset: 42,
                lits: [(lit![4], 4), (lit![2], 2), (lit![42], 42)]
                    .into_iter()
                    .collect(),
            },
            Objective::Constant { offset: 11 },
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
            },
            Objective::Weighted {
                offset: 42,
                lits: [(lit![4], 4), (lit![2], 2), (lit![42], 42)]
                    .into_iter()
                    .collect(),
            },
            Objective::Constant { offset: 11 },
        ];
        let order = super::objectives_as_order(&objectives);

        let mut proof = new_proof(0, false);
        proof.define_order(&order).unwrap();
        proof.load_order(order.name(), order.used_vars()).unwrap();

        let proof_file = proof
            .conclude(
                pidgeons::OutputGuarantee::None,
                &pidgeons::Conclusion::<&str>::None,
            )
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(
            format!("{manifest}/../rustsat/data/empty.opb"),
            proof_file.path(),
        );
    }
}
