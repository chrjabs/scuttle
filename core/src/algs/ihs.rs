//! # Multi-Objective IHS Algorithm

use std::io;

use hitting_sets::{BuildSolver, CompleteSolveResult, HittingSetSolver, IncompleteSolveResult};
use rustsat::{
    solvers::{
        DefaultInitializer, Initialize, SolveIncremental, SolveStats, SolverResult, SolverStats,
    },
    types::{Assignment, Cl, Clause, Lit, RsHashSet, TernaryVal, Var},
};
use scuttle_proc::{oracle_bounds, KernelFunctions};

use crate::{
    algs::coreboosting::CbResult,
    archive::Archive,
    options::{CandidateSeeding, EnumOptions, IhsCbOptions, IhsCbTreatment, IhsOptions},
    termination::ensure,
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
    max_obj_var: Var,
    n_seeded: usize,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
    /// Archive of candidate solutions
    candidates: Archive<Assignment>,
    opts: IhsOptions,
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
        Option<hitting_sets::Statistics>,
    ) {
        use crate::ExtendedSolveStats;
        (
            self.kernel.stats,
            Some(self.oracle_stats()),
            Some(self.encoding_stats()),
            Some(self.hitting_set_solver.statistics()),
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
    type Options = (KernelOptions, IhsOptions);

    /// Initializes a default solver with a configured oracle and options. The
    /// oracle should _not_ have any clauses loaded yet.
    fn new<Cls>(
        clauses: Cls,
        objs: Vec<Objective>,
        var_manager: VarManager,
        (kernel_opts, opts): Self::Options,
        block_clause_gen: BCG,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = Clause>,
    {
        anyhow::ensure!(
            matches!(kernel_opts.enumeration, EnumOptions::NoEnum),
            "cannot enumerate with IHS algorithm"
        );
        let builder = Hss::Builder::new(objs.iter().map(|obj| obj.iter()));
        let mut hitting_set_solver = builder.init();
        let clauses: Vec<_> = clauses.into_iter().collect();

        // Seed constraints over objective variables
        let mut objective_lits = RsHashSet::default();
        let mut max_obj_var = Var::new(0);
        for obj in &objs {
            for (lit, _) in obj.iter() {
                if lit.var() > max_obj_var {
                    max_obj_var = lit.var();
                }
                objective_lits.insert(lit);
            }
        }
        let mut n_seeded = 0;
        if opts.seeding {
            'outer: for cl in &clauses {
                for lit in cl {
                    if !objective_lits.contains(lit) && !objective_lits.contains(&!*lit) {
                        continue 'outer;
                    }
                }
                hitting_set_solver.add_core(cl);
                n_seeded += 1;
            }
        }

        let kernel = Kernel::new(clauses, objs, var_manager, block_clause_gen, kernel_opts)?;
        Ok(Self {
            kernel,
            hitting_set_solver,
            objective_lits,
            max_obj_var,
            n_seeded,
            pareto_front: Default::default(),
            candidates: Default::default(),
            opts,
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
        if let Some(logger) = &mut self.kernel.logger {
            logger.log_seeding_ratio(
                self.kernel.stats.n_orig_clauses as f64 / self.n_seeded as f64,
            )?;
        }
        if (self.kernel.stats.n_orig_clauses as f64 / self.n_seeded as f64 - 1.0).abs()
            < f64::EPSILON
        {
            let term = self.main_fully_seeded();
            self.kernel.log_routine_end()?;
            return term;
        }
        if self.seed_candidates()? {
            return Done(());
        }
        let mut want_optimal = false;
        let joint_objective = {
            let mut jobj = vec![0; self.max_obj_var.idx() + 1];
            for obj in &self.kernel.objs {
                for (lit, weight) in obj.iter() {
                    let mut weight =
                        isize::try_from(weight).expect("weight does not fit in `isize`");
                    if lit.is_neg() {
                        weight *= -1;
                    }
                    jobj[lit.vidx()] += weight;
                }
            }
            jobj
        };
        loop {
            self.kernel.log_routine_start("extract hitting set")?;

            let hitting_set_answer: IncompleteSolveResult =
                if let Some(target) = self.candidates.get_target() {
                    if want_optimal {
                        self.hitting_set_solver.optimal_hitting_set().into()
                    } else {
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
            // sort hitting set by weight for core minimization
            if self.kernel.opts.core_minimization.minimization() {
                // NOTE: we _intentionally_ use stable sort here, so that we preserve literal order
                // on equal weight
                hitting_set.sort_by_key(|l| -joint_objective[l.vidx()].abs());
            }
            match self.kernel.solve_assumps(&hitting_set)? {
                SolverResult::Sat => {
                    let (costs, solution) = self.kernel.get_solution_and_internal_costs(false)?;
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
                        self.hitting_set_solver.add_pd_cut(&costs);
                        want_optimal = false;
                    } else {
                        let last_target = self
                            .candidates
                            .get_target()
                            .expect("since the hitting set is not optimal, we must have a target");
                        let new_target = costs.iter().copied().sum::<usize>();
                        self.candidates.insert(solution, costs);
                        if new_target >= last_target {
                            want_optimal = true;
                        }
                    }
                }
                SolverResult::Unsat => {
                    let mut wce_obj = if self.opts.wce {
                        joint_objective.clone()
                    } else {
                        vec![]
                    };
                    loop {
                        let core = self.kernel.oracle.core()?;
                        if core.is_empty() {
                            self.kernel.log_routine_end()?;
                            return Done(());
                        }
                        let orig_len = core.len();
                        let (core, _) = self.kernel.trim_core(core, &[], None)?;
                        let (core, _) = self.kernel.minimize_core(core, &[], None)?;
                        let core = Cl::new(&core);
                        self.hitting_set_solver.add_core(core);
                        let _len_before = hitting_set.len();
                        if self.opts.wce {
                            let min_cost = core.iter().fold(isize::MAX, |min, lit| {
                                std::cmp::min(wce_obj[lit.vidx()].abs(), min)
                            });
                            if let Some(log) = &mut self.kernel.logger {
                                log.log_core(min_cost.unsigned_abs(), orig_len, core.len())?;
                            }
                            for lit in core {
                                if lit.is_pos() {
                                    wce_obj[lit.vidx()] -= min_cost;
                                } else {
                                    wce_obj[lit.vidx()] += min_cost;
                                }
                            }
                            hitting_set.retain(|&lit| wce_obj[lit.vidx()] != 0);
                        } else {
                            if let Some(log) = &mut self.kernel.logger {
                                log.log_core(usize::MAX, orig_len, core.len())?;
                            }
                            // NOTE: core is in same order as hitting set, we can therefore remove the
                            // core literals in a single sweep, knowing that the
                            // with core minimization, the assumptions are ordered by weight,
                            // otherwise by literal (from the hitting set solver)
                            let mut core_idx = 0;
                            if self.kernel.opts.core_minimization.minimization() {
                                hitting_set.retain(|&lit| {
                                    while core_idx < core.len()
                                        && (joint_objective[core[core_idx].vidx()].abs()
                                            > joint_objective[lit.vidx()].abs()
                                            || (joint_objective[core[core_idx].vidx()].abs()
                                                == joint_objective[lit.vidx()].abs()
                                                && core[core_idx] < !lit))
                                    {
                                        core_idx += 1;
                                    }
                                    if core_idx >= core.len() || !lit != core[core_idx] {
                                        return true;
                                    }
                                    false
                                });
                            } else {
                                hitting_set.retain(|&lit| {
                                    while core_idx < core.len() && core[core_idx] < !lit {
                                        core_idx += 1;
                                    }
                                    if core_idx >= core.len() || !lit != core[core_idx] {
                                        return true;
                                    }
                                    false
                                });
                            };
                        }
                        debug_assert!(
                            hitting_set.len() < _len_before,
                            "something should be removed from the assumptions"
                        );
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

    /// Separate algorithm branch for when the entire instance was seeded into the hitting set
    /// solver
    fn main_fully_seeded(&mut self) -> MaybeTerminatedError {
        debug_assert!(
            (self.kernel.stats.n_orig_clauses as f64 / self.n_seeded as f64 - 1.0).abs()
                < f64::EPSILON
        );
        self.kernel.log_routine_start("ihs (fully seeded)")?;
        loop {
            self.kernel.log_routine_start("extract hitting set")?;
            let hitting_set_answer = self.hitting_set_solver.optimal_hitting_set();
            let (cost, hitting_set) = match hitting_set_answer {
                CompleteSolveResult::Optimal(cost, hitting_set) => (cost, hitting_set),
                CompleteSolveResult::Infeasible => {
                    self.kernel.log_routine_end()?;
                    self.kernel.log_routine_end()?;
                    return Done(());
                }
            };
            self.kernel.log_routine_end()?;
            if let Some(logger) = &mut self.kernel.logger {
                logger.log_hitting_set(cost, true)?;
            }
            self.kernel.check_termination()?;
            let (costs, solution) = self.hitting_set_to_solution_and_internal_costs(hitting_set);
            // store solution
            self.kernel
                .yield_solutions(costs.clone(), &[], solution, &mut self.pareto_front)?;
            // introduce PD cut in the hitting set solver
            self.hitting_set_solver.add_pd_cut(&costs);
        }
    }

    /// Initializes the candidates according to the selected strategy
    fn seed_candidates(&mut self) -> MaybeTerminatedError<bool> {
        match self.opts.candidate_seeding {
            CandidateSeeding::None => Done(false),
            CandidateSeeding::OneSolution => match self.kernel.solve()? {
                SolverResult::Sat => {
                    let (costs, solution) = self.kernel.get_solution_and_internal_costs(false)?;
                    self.candidates.insert(solution, costs);
                    Done(false)
                }
                SolverResult::Unsat => Done(true),
                SolverResult::Interrupted => unreachable!(),
            },
        }
    }

    fn compute_internal_costs(&self, solution: &Assignment) -> Vec<usize> {
        (0..self.kernel.objs.len())
            .map(|idx| {
                let mut cost = 0;
                for (l, w) in self.kernel.objs[idx].iter() {
                    let val = solution.lit_value(l);
                    if val == TernaryVal::True {
                        cost += w;
                    }
                }
                cost
            })
            .collect()
    }

    fn hitting_set_to_solution_and_internal_costs(
        &self,
        hitting_set: Vec<Lit>,
    ) -> (Vec<usize>, Assignment) {
        let sol: Assignment = hitting_set.into_iter().collect();
        let costs = self.compute_internal_costs(&sol);
        debug_assert_eq!(costs.len(), self.kernel.stats.n_objs);
        (costs, sol)
    }
}

impl<Hss, ProofW, OInit, BCG> CoreBoost
    for ParetoIhs<rustsat_cadical::CaDiCaL<'_, '_>, Hss, ProofW, OInit, BCG>
where
    Hss: HittingSetSolver,
    ProofW: io::Write + 'static,
    BCG: Fn(Assignment) -> Clause,
{
    type Options = IhsCbOptions;

    fn core_boost(&mut self, opts: Self::Options) -> MaybeTerminatedError<bool> {
        ensure!(
            self.kernel.stats.n_solve_calls == 0,
            "cannot perform core boosting after solve has been called"
        );
        let Some(cb_res) = self.kernel.core_boost()? else {
            return Done(false);
        };
        self.kernel.check_termination()?;

        self.kernel.log_routine_start("cb post treatment")?;

        if opts.treatment == IhsCbTreatment::Ignore {
            self.objective_lits.clear();

            self.hitting_set_solver.change_objectives(
                cb_res
                    .iter()
                    .map(|res| res.reform.inactives.iter().map(|(l, w)| (*l, *w))),
            );
        }

        for CbResult {
            reform, solution, ..
        } in cb_res
        {
            if let Some(solution) = solution {
                let costs = self.compute_internal_costs(&solution);
                self.candidates.insert(solution, costs);
            }

            if opts.treatment == IhsCbTreatment::Ignore {
                self.objective_lits
                    .extend(reform.inactives.iter().map(|(l, _)| *l));
            }
        }

        self.kernel.log_routine_end()?;

        Done(true)
    }
}
