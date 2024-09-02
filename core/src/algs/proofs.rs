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
    AbsConstraintId, Axiom, ConstraintId, ConstraintLike, OperationSequence, Order, OrderVar,
    Proof, ProofOnlyVar, VarLike,
};
use rustsat::{
    instances::{Cnf, ManageVars},
    solvers::Initialize,
    types::{Assignment, Clause, Lit, Var, WLitIter},
};

use crate::{
    types::{Instance, Objective, VarManager},
    KernelOptions, Limits, Stats,
};

use super::default_blocking_clause;

/// Trait for initializing algorithms
pub trait InitCert: super::Init {
    type ProofWriter;

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
                .map(|(l, w)| {
                    let w = isize::try_from(w).expect("can only handle weights up to `isize::MAX`");
                    let (u, v) = order.use_var(l.var());
                    let (u, v) = if l.is_pos() {
                        (u.pos_axiom(), v.pos_axiom())
                    } else {
                        (u.neg_axiom(), v.neg_axiom())
                    };
                    [(-w * mult, u), (w * mult, v)]
                })
                .flatten()
                .collect(),
            bound: 0,
        };
        // For O_idx, this proof sums up the following constraints
        // - O_idx(u) <= O_idx(v)
        // - O_idx(v) <= O_idx(w)
        // - O_idx(u) > O_idx(w)
        // This will always lead to a contradiction, proving transitivity
        let trans_proof = vec![
            OperationSequence::<OrderVar<Var>>::from(ConstraintId::abs(idx + 1))
                + ConstraintId::abs(objs.len() + idx + 1)
                + ConstraintId::last(1),
        ];
        order.add_definition_constraint(constr, trans_proof, None)
    }
    order
}

pub fn certify_pmin_cut<ProofW: io::Write>(
    block_clause: &Clause,
    witness: &Assignment,
    proof: &mut Proof<ProofW>,
) -> io::Result<AbsConstraintId> {
    // FIXME: remove if acctualy not needed
    // // introduce `not_better_i` for each objective
    // let not_betters = Vec::with_capacity(objs.len());
    // for (_idx, (obj, cost)) in objs.into_iter().zip(costs).enumerate() {
    //     let not_better = proof.new_proof_var();
    //     #[cfg(feature = "verbose-proofs")]
    //     proof.comment(&format_args!(
    //         "{not_better} = the current solution is not better than {cost} on objective {idx}"
    //     ))?;
    //     // O_i >= c_i -> not_better
    //     let cost = isize::try_from(cost).expect("can only handle weights up to `isize::MAX`");
    //     let mut weight_sum = 0;
    //     let sum: Vec<_> = [(cost, not_worse.into())]
    //         .into_iter()
    //         .chain(obj.iter().map(|(l, w)| {
    //             let w = isize::try_from(*w).expect("can only handle weights up to `isize::MAX`");
    //             weight_sum += w;
    //             ((!*l).into(), w)
    //         }))
    //         .collect();
    //     proof.redundant(
    //         &LbConstraint {
    //             lits: sum,
    //             bound: weight_sum - cost + 1,
    //         },
    //         [not_better.substitute_fixed(false)],
    //         None,
    //     )?;
    //     // TODO: do we need the other reification direction here?
    //     not_betters.push(not_better);
    // }
    // let dominated = proof.new_proof_var();
    // #[cfg(feature = "verbose-proofs")]
    // proof.comment(&format_args!(
    //     "{dominated} = the current solution is (weakly) dominated by [{}]",
    //     costs.into_iter().format(", ")
    // ))?;
    // proof.redundant(&LbConstraint{lits: [(1, dominated.into())].chain()}, subs, proof)

    // TODO: figure out if this works with cuts shortened due to bounds

    #[cfg(feature = "verbose-proofs")]
    {
        proof.comment("Introducing P-minimal cut based on the following witness:")?;
        proof.comment(&format_args!("{witness}"))?;
    }

    // Introduce indicator variable for being at accactly the solution in question
    let is_this = AnyVar::Proof(proof.new_proof_var());
    #[cfg(feature = "verbose-proofs")]
    proof.comment(&format_args!(
        "{is_this} = a solution is _exactly_ the witnessing one"
    ))?;
    let bound = isize::try_from(witness.len()).unwrap();
    let is_this_def = proof.redundant(
        &LbConstraint {
            lits: [(bound, is_this.neg_axiom())]
                .into_iter()
                .chain(witness.iter().map(|l| (1, axiom(l))))
                .collect(),
            bound,
        },
        [is_this.substitute_fixed(false)],
        None,
    )?;

    // Map all weakly dominated solutions to the witness itself
    let map_dom = proof.redundant(
        &LbConstraint {
            lits: [(1, is_this.pos_axiom())]
                .into_iter()
                .chain(block_clause.iter().map(|l| (1, axiom(*l))))
                .collect(),
            bound: 1,
        },
        witness
            .iter()
            .map(|l| AnyVar::Solver(l.var()).substitute_fixed(l.is_pos())),
        None,
    )?;

    // Exclude witness
    let exclude = proof.exclude_solution(witness.iter().map(|l| Axiom::from(l)))?;

    // Add the actual P-minimal cut as a clause
    // TODO: provide hints
    let cut_id = proof.reverse_unit_prop(block_clause, Option::<[ConstraintId; 0]>::None)?;

    // Remove auxiliary constraints
    proof.delete_ids(
        [is_this_def, map_dom, exclude]
            .into_iter()
            .map(|id| ConstraintId::from(id)),
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

        // Proof logging: write out OPB file to use as VeriPB input
        // FIXME: This is temporary for getting something off the ground quickly. Long term, also
        // proof log encoding built before to ensure original files can be used
        let mut writer = std::io::BufWriter::new(std::fs::File::create("veripb-input.opb")?);
        let clauses: Cnf = clauses.into_iter().collect();
        let iter = clauses
            .iter()
            .map(|cl| rustsat::instances::fio::opb::FileLine::<Option<_>>::Clause(cl.clone()));
        rustsat::instances::fio::opb::write_opb_lines(
            &mut writer,
            iter,
            rustsat::instances::fio::opb::Options::default(),
        )?;

        let mut stats = Stats {
            n_objs: 0,
            n_real_objs: 0,
            n_orig_clauses: 0,
            ..Default::default()
        };
        let mut oracle = OInit::init();
        oracle.reserve(var_manager.max_var().unwrap())?;
        let orig_cnf = if opts.store_cnf {
            Some(clauses.clone())
        } else {
            None
        };
        stats.n_orig_clauses = clauses.len();

        // Add clauses to solver
        let pt_handle = oracle.connect_proof_tracer(CadicalTracer::new(proof), true);
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
            pt_handle: Some(pt_handle),
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
    left u_x3 u_x5 u_x43 u_x4 u_x1 u_x2
    right v_x3 v_x5 v_x43 v_x4 v_x1 v_x2
    aux
  end
  def
    -2 u_x1 +2 v_x1 -2 ~u_x2 +2 ~v_x2 -2 u_x3 +2 v_x3 -2 u_x4 +2 v_x4 >= 0 ;
    -4 u_x5 +4 v_x5 -2 u_x3 +2 v_x3 -42 u_x43 +42 v_x43 >= 0 ;
     >= 0 ;
  end
  transitivity
    vars
      fresh_right w_x3 w_x5 w_x43 w_x4 w_x1 w_x2
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
end
"#;
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
            .conclude(pidgeons::OutputGuarantee::None, &pidgeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(
            format!("{manifest}/../rustsat/data/empty.opb"),
            proof_file.path(),
        );
        panic!()
    }
}
