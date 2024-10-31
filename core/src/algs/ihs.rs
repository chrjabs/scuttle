//! # Multi-Objective IHS Algorithm

use std::io;

use hitting_sets::{BuildSolver, CompleteSolveResult, HittingSetSolver};
use rustsat::{
    solvers::{
        DefaultInitializer, Initialize, SolveIncremental, SolveStats, SolverResult, SolverStats,
    },
    types::{Assignment, Cl, Clause, Lit, RsHashSet, WLitIter},
};
use scuttle_proc::{oracle_bounds, KernelFunctions};

use crate::{
    options::EnumOptions,
    types::{Objective, ParetoFront, VarManager},
    EncodingStats, ExtendedSolveStats, KernelOptions, Limits,
    MaybeTerminatedError::{self, Done},
};

use super::Kernel;

#[derive(KernelFunctions)]
pub struct ParetoIhs<
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
    objective_lits: RsHashSet<Lit>,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

impl<Hss, ProofW, OInit, BCG> super::Solve
    for ParetoIhs<rustsat_cadical::CaDiCaL<'_, '_>, Hss, ProofW, OInit, BCG>
where
    Hss: HittingSetSolver,
    ProofW: io::Write + 'static,
    BCG: Fn(Assignment) -> Clause,
{
    fn solve(&mut self, limits: Limits) -> MaybeTerminatedError {
        self.kernel.start_solving(limits);
        self.alg_main()
    }

    fn all_stats(
        &self,
    ) -> (
        crate::Stats,
        Option<SolverStats>,
        Option<Vec<EncodingStats>>,
    ) {
        use crate::ExtendedSolveStats;
        (
            self.kernel.stats,
            Some(self.oracle_stats()),
            Some(self.encoding_stats()),
        )
    }
}

#[oracle_bounds]
impl<O, Hss, ProofW, OInit, BCG> super::Init for ParetoIhs<O, Hss, ProofW, OInit, BCG>
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
        anyhow::ensure!(
            matches!(opts.enumeration, EnumOptions::NoEnum),
            "cannot enumerate with IHS algorithm"
        );
        let objs: Vec<_> = objs
            .into_iter()
            .map(|(obj, off)| (obj.into_iter().collect::<Vec<_>>(), off))
            .collect();
        let builder = Hss::Builder::new(objs.iter().map(|(obj, _)| obj.iter().copied()));
        let mut hitting_set_solver = builder.init();
        let clauses: Vec<_> = clauses.into_iter().collect();

        // Seed constraints over objective variables
        let obj_vars: RsHashSet<_> = objs
            .iter()
            .flat_map(|(obj, _)| obj.iter().map(|(lit, _)| lit.var()))
            .collect();
        'outer: for cl in &clauses {
            for lit in cl {
                if !obj_vars.contains(&lit.var()) {
                    continue 'outer;
                }
            }
            hitting_set_solver.add_core(cl);
        }
        let objective_lits: RsHashSet<_> = objs
            .iter()
            .flat_map(|(obj, _)| obj.iter().map(|(lit, _)| *lit))
            .collect();

        let kernel = Kernel::new(clauses, objs, var_manager, block_clause_gen, opts)?;
        Ok(Self {
            kernel,
            hitting_set_solver,
            objective_lits,
            pareto_front: Default::default(),
        })
    }
}

impl<O, Hss, ProofW, OInit, BCG> ExtendedSolveStats for ParetoIhs<O, Hss, ProofW, OInit, BCG>
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

impl<Hss, ProofW, OInit, BCG> ParetoIhs<rustsat_cadical::CaDiCaL<'_, '_>, Hss, ProofW, OInit, BCG>
where
    Hss: HittingSetSolver,
    ProofW: io::Write + 'static,
    BCG: Fn(Assignment) -> Clause,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> MaybeTerminatedError {
        self.kernel.log_routine_start("ihs")?;
        loop {
            self.kernel.log_routine_start("extract hitting set")?;
            let CompleteSolveResult::Optimal(cost, mut hitting_set) =
                self.hitting_set_solver.optimal_hitting_set()
            else {
                self.kernel.log_routine_end()?;
                self.kernel.log_routine_end()?;
                return Done(());
            };
            self.kernel.log_routine_end()?;
            if let Some(logger) = &mut self.kernel.logger {
                logger.log_hitting_set(cost)?;
            }
            self.kernel.check_termination()?;
            hitting_set.retain(|lit| self.objective_lits.contains(&!*lit));
            match self.kernel.solve_assumps(&hitting_set)? {
                SolverResult::Sat => {
                    // found pareto-optimal solution
                    let (mut costs, solution) =
                        self.kernel.get_solution_and_internal_costs(false)?;
                    // store solution
                    self.kernel.yield_solutions(
                        costs.clone(),
                        &[],
                        solution,
                        &mut self.pareto_front,
                    )?;
                    // introduce PD cut in the hitting set solver
                    for (obj, cost) in self.kernel.objs.iter().zip(&mut costs) {
                        if let Objective::Unweighted { unit_weight, .. } = obj {
                            *cost *= *unit_weight;
                        }
                    }
                    self.hitting_set_solver.add_pd_cut(&costs);
                }
                SolverResult::Unsat => {
                    loop {
                        let core = self.kernel.oracle.core()?;
                        if core.is_empty() {
                            self.kernel.log_routine_end()?;
                            return Done(());
                        }
                        let (core, _) = self.kernel.trim_core(core, &[], None)?;
                        let (core, _) = self.kernel.minimize_core(core, &[], None)?;
                        let core = Cl::new(&core);
                        self.hitting_set_solver.add_core(core);
                        // NOTE: core is in same order as hitting set, we can therefore remove the
                        // core literals in a single sweep
                        let mut core_idx = 0;
                        hitting_set.retain(|&lit| {
                            while core_idx < core.len() && core[core_idx] < !lit {
                                core_idx += 1;
                            }
                            if core_idx >= core.len() || !lit != core[core_idx] {
                                return true;
                            }
                            false
                        });
                        if hitting_set.is_empty() {
                            break;
                        }
                        match self.kernel.solve_assumps(&hitting_set)? {
                            SolverResult::Sat => break,
                            SolverResult::Unsat => {}
                            SolverResult::Interrupted => unreachable!(),
                        }
                    }
                }
                SolverResult::Interrupted => unreachable!(),
            }
        }
    }
}
