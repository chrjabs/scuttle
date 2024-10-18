//! # Multi-Objective IHS Algorithm

use std::io;

use hitting_sets::{BuildSolver, CompleteSolveResult, HittingSetSolver};
use rustsat::{
    solvers::{
        DefaultInitializer, Initialize, SolveIncremental, SolveStats, SolverResult, SolverStats,
    },
    types::{Assignment, Cl, Clause, Lit, RsHashMap, WLitIter},
};
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{
    types::{ParetoFront, VarManager},
    EncodingStats, ExtendedSolveStats, KernelOptions,
    MaybeTerminatedError::{self, Done},
};

use super::Kernel;

#[derive(KernelFunctions, Solve)]
#[solve(bounds = "where O: SolveIncremental + SolveStats,
        Hss: HittingSetSolver,
        ProofW: io::Write,
        OInit: Initialize<O>,
        BCG: Fn(Assignment) -> Clause")]
pub struct Ihs<
    O,
    Hss,
    ProofW = io::BufWriter<std::fs::File>,
    OInit = DefaultInitializer,
    BCG = fn(Assignment) -> Clause,
> where
    ProofW: io::Write,
{
    kernel: Kernel<O, ProofW, OInit, BCG>,
    hitting_set_solver: Hss,
    joint_obj: RsHashMap<Lit, usize>,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

#[oracle_bounds]
impl<O, Hss, ProofW, OInit, BCG> super::Init for Ihs<O, Hss, ProofW, OInit, BCG>
where
    O: SolveIncremental,
    Hss: HittingSetSolver,
    ProofW: io::Write,
    OInit: Initialize<O>,
    BCG: Fn(Assignment) -> Clause,
{
    type Oracle = O;
    type BlockClauseGen = BCG;

    /// Initializes a default solver with a configured oracle and options. The
    /// oracle should _not_ have any clauses loaded yet.
    fn new<Cls, Objs, Obj>(
        clauses: Cls,
        objs: Objs,
        var_manager: VarManager,
        opts: KernelOptions,
        block_clause_gen: BCG,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = Clause>,
        Objs: IntoIterator<Item = (Obj, isize)>,
        Obj: WLitIter,
    {
        let objs: Vec<_> = objs
            .into_iter()
            .map(|(obj, off)| (obj.into_iter().collect::<Vec<_>>(), off))
            .collect();
        let mut joint_obj = RsHashMap::default();
        let mut max_var = rustsat::var![0];
        for (obj, _) in &objs {
            for (l, w) in obj.iter() {
                max_var = std::cmp::max(l.var(), max_var);
                if let Some(val) = joint_obj.get_mut(l) {
                    *val += *w;
                } else {
                    joint_obj.insert(*l, *w);
                }
            }
        }
        let mut builder = Hss::Builder::new(joint_obj.iter().map(|(&l, &w)| (l, w)));
        builder.reserve_vars(max_var.idx() + 1, joint_obj.len());
        let mut hitting_set_solver = builder.init();
        let clauses: Vec<_> = clauses.into_iter().collect();

        // Seed constraints over objective variables
        'outer: for cl in &clauses {
            for lit in cl {
                if !joint_obj.contains_key(lit) && !joint_obj.contains_key(&!*lit) {
                    continue 'outer;
                }
                hitting_set_solver.add_core(cl);
            }
        }

        let kernel = Kernel::new(clauses, objs, var_manager, block_clause_gen, opts)?;
        Ok(Self {
            kernel,
            hitting_set_solver,
            joint_obj,
            pareto_front: Default::default(),
        })
    }
}

impl<O, Hss, ProofW, OInit, BCG> ExtendedSolveStats for Ihs<O, Hss, ProofW, OInit, BCG>
where
    O: SolveStats,
    ProofW: io::Write,
{
    fn oracle_stats(&self) -> SolverStats {
        self.kernel.oracle.stats()
    }

    fn encoding_stats(&self) -> Vec<EncodingStats> {
        vec![]
    }
}

#[oracle_bounds]
impl<O, Hss, ProofW, OInit, BCG> Ihs<O, Hss, ProofW, OInit, BCG>
where
    O: SolveIncremental,
    Hss: HittingSetSolver,
    ProofW: io::Write,
    OInit: Initialize<O>,
    BCG: Fn(Assignment) -> Clause,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> MaybeTerminatedError {
        self.kernel.log_routine_start("ihs")?;
        loop {
            let CompleteSolveResult::Optimal(cost, mut hitting_set) =
                self.hitting_set_solver.optimal_hitting_set()
            else {
                self.kernel.log_routine_end()?;
                return Done(());
            };
            dbg!(cost);
            self.kernel.check_termination()?;
            hitting_set.sort_unstable();
            let mut assumps = vec![];
            'outer: for (l, _) in &self.joint_obj {
                for l2 in &hitting_set {
                    if *l == *l2 {
                        continue 'outer;
                    }
                }
                assumps.push(!*l);
            }
            self.kernel.check_termination()?;
            match self.kernel.solve_assumps(&assumps)? {
                SolverResult::Sat => todo!(),
                SolverResult::Unsat => {
                    let core = self.kernel.oracle.core()?;
                    let core = Cl::new(&core);
                    self.hitting_set_solver.add_core(core);
                }
                SolverResult::Interrupted => unreachable!(),
            }
        }
    }
}
