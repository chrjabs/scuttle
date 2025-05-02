//! # Multi-Objective IHS Algorithm

use std::io;

use hitting_sets::{BuildSolver, HittingSetSolver, IncompleteSolveResult};
use rustsat::{
    solvers::{
        DefaultInitializer, Initialize, SolveIncremental, SolveStats, SolverResult, SolverStats,
    },
    types::{Assignment, Cl, Clause, Lit, RsHashSet},
};
use scuttle_proc::{oracle_bounds, KernelFunctions};

use crate::{
    archive::Archive,
    options::EnumOptions,
    types::{Objective, ParetoFront, VarManager},
    CoreBoost, EncodingStats, ExtendedSolveStats, KernelOptions, Limits,
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
    /// Archive of candidate solutions
    candidates: Archive<Assignment>,
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
    fn new<Cls>(
        clauses: Cls,
        objs: Vec<Objective>,
        var_manager: VarManager,
        opts: KernelOptions,
        block_clause_gen: BCG,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = Clause>,
    {
        anyhow::ensure!(
            matches!(opts.enumeration, EnumOptions::NoEnum),
            "cannot enumerate with IHS algorithm"
        );
        let builder = Hss::Builder::new(objs.iter().map(|obj| obj.iter()));
        let mut hitting_set_solver = builder.init();
        let clauses: Vec<_> = clauses.into_iter().collect();

        // Seed constraints over objective variables
        let obj_vars: RsHashSet<_> = objs
            .iter()
            .flat_map(|obj| obj.iter().map(|(lit, _)| lit.var()))
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
            .flat_map(|obj| obj.iter().map(|(lit, _)| lit))
            .collect();

        let kernel = Kernel::new(clauses, objs, var_manager, block_clause_gen, opts)?;
        Ok(Self {
            kernel,
            hitting_set_solver,
            objective_lits,
            pareto_front: Default::default(),
            candidates: Default::default(),
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
        let mut want_optimal = false;
        loop {
            self.kernel.log_routine_start("extract hitting set")?;

            let hitting_set_answer: IncompleteSolveResult =
                if let Some(target) = self.candidates.get_target() {
                    if want_optimal {
                        self.hitting_set_solver.optimal_hitting_set().into()
                    } else {
                        dbg!(target);
                        self.hitting_set_solver.hitting_set(target - 1)
                    }
                } else {
                    self.hitting_set_solver.optimal_hitting_set().into()
                };

            let (cost, mut hitting_set, is_optimal) = match hitting_set_answer {
                IncompleteSolveResult::Optimal(cost, hitting_set) => (cost, hitting_set, true),
                IncompleteSolveResult::Infeasible => {
                    self.kernel.log_routine_end()?;
                    self.kernel.log_routine_end()?;
                    return Done(());
                }
                IncompleteSolveResult::Feasible(cost, hitting_set) => (cost, hitting_set, false),
            };

            self.kernel.log_routine_end()?;
            if let Some(logger) = &mut self.kernel.logger {
                logger.log_hitting_set(cost, is_optimal)?;
            }
            self.kernel.check_termination()?;
            hitting_set.retain(|lit| self.objective_lits.contains(&!*lit));
            match self.kernel.solve_assumps(&hitting_set)? {
                SolverResult::Sat => {
                    let (mut costs, solution) =
                        self.kernel.get_solution_and_internal_costs(false)?;
                    if is_optimal {
                        // found pareto-optimal solution
                        self.candidates.remove_dominated(&costs);
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
                        want_optimal = false;
                    } else {
                        let Some(last_target) = self.candidates.get_target() else {
                            unreachable!(
                                "since the hitting set is not optimal, we must have a target"
                            );
                        };
                        let new_target = costs.iter().copied().sum::<usize>();
                        self.candidates.insert(solution, costs);
                        if new_target >= last_target {
                            want_optimal = true;
                        }
                    }
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
                            SolverResult::Sat => {
                                let (costs, solution) =
                                    self.kernel.get_solution_and_internal_costs(true)?;
                                self.candidates.insert(solution, costs);
                                break;
                            }
                            SolverResult::Unsat => {}
                            SolverResult::Interrupted => unreachable!(),
                        }
                    }
                    want_optimal = false;
                }
                SolverResult::Interrupted => unreachable!(),
            }
        }
    }
}

impl<Hss, ProofW, OInit, BCG> CoreBoost
    for ParetoIhs<rustsat_cadical::CaDiCaL<'_, '_>, Hss, ProofW, OInit, BCG>
where
    Hss: HittingSetSolver,
    ProofW: io::Write + 'static,
    BCG: Fn(Assignment) -> Clause,
{
    fn core_boost(&mut self, _opts: crate::CoreBoostingOptions) -> MaybeTerminatedError<bool> {
        // NOTE: in this case core boosting just means extracting cores over the individual
        // objectives first
        self.kernel.log_routine_start("core boost")?;
        for obj_idx in 0..self.kernel.stats.n_objs {
            let mut mults = vec![0.0; self.kernel.stats.n_objs];
            mults[obj_idx] = 1.0;
            self.hitting_set_solver.change_multipliers(&mults);
            let mut target = None;

            self.kernel.log_routine_start("ihs")?;
            let mut want_optimal = false;
            loop {
                self.kernel.log_routine_start("extract hitting set")?;

                let hitting_set_answer: IncompleteSolveResult = if let Some(target) = target {
                    if want_optimal {
                        self.hitting_set_solver.optimal_hitting_set().into()
                    } else {
                        dbg!(target);
                        self.hitting_set_solver.hitting_set(target - 1)
                    }
                } else {
                    self.hitting_set_solver.optimal_hitting_set().into()
                };

                let (cost, mut hitting_set, is_optimal) = match hitting_set_answer {
                    IncompleteSolveResult::Optimal(cost, hitting_set) => (cost, hitting_set, true),
                    IncompleteSolveResult::Infeasible => {
                        self.kernel.log_routine_end()?;
                        self.kernel.log_routine_end()?;
                        self.kernel.log_routine_end()?;
                        return Done(false);
                    }
                    IncompleteSolveResult::Feasible(cost, hitting_set) => {
                        (cost, hitting_set, false)
                    }
                };

                self.kernel.log_routine_end()?;
                if let Some(logger) = &mut self.kernel.logger {
                    logger.log_hitting_set(cost, is_optimal)?;
                }
                self.kernel.check_termination()?;
                hitting_set.retain(|lit| self.objective_lits.contains(&!*lit));
                match self.kernel.solve_assumps(&hitting_set)? {
                    SolverResult::Sat => {
                        let (costs, solution) =
                            self.kernel.get_solution_and_internal_costs(false)?;
                        if is_optimal {
                            // found optimal solution
                            self.candidates.insert(solution, costs);
                            // this objective is done now
                            break;
                        } else {
                            let Some(target) = &mut target else {
                                unreachable!(
                                    "since the hitting set is not optimal, we must have a target"
                                );
                            };
                            if costs[obj_idx] < *target {
                                *target = costs[obj_idx];
                            } else {
                                want_optimal = true;
                            }
                            self.candidates.insert(solution, costs);
                        }
                    }
                    SolverResult::Unsat => {
                        loop {
                            let core = self.kernel.oracle.core()?;
                            if core.is_empty() {
                                self.kernel.log_routine_end()?;
                                return Done(false);
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
                                SolverResult::Sat => {
                                    let (costs, solution) =
                                        self.kernel.get_solution_and_internal_costs(true)?;
                                    target = Some(std::cmp::min(
                                        costs[obj_idx],
                                        target.unwrap_or(usize::MAX),
                                    ));
                                    self.candidates.insert(solution, costs);
                                    break;
                                }
                                SolverResult::Unsat => {}
                                SolverResult::Interrupted => unreachable!(),
                            }
                        }
                        want_optimal = false;
                    }
                    SolverResult::Interrupted => unreachable!(),
                }
            }
            self.kernel.log_routine_end()?;
        }
        self.kernel.log_routine_end()?;
        let mults = vec![1.0; self.kernel.stats.n_objs];
        self.hitting_set_solver.change_multipliers(&mults);
        Done(true)
    }
}
