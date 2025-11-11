//! # Multi-Objective IHS Algorithm

use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};

use anyhow::Context;
use hitting_sets::{BuildSolver, CompleteSolveResult, HittingSetSolver};
use rustsat::{
    solvers::SolverStats,
    types::{Assignment, Lit, TernaryVal},
};

use crate::{
    EncodingStats, Limits, MaybeTerminated,
    MaybeTerminatedError::{self, Done},
    Stats, Termination,
    options::{MipPdOptions, ObjectiveMultipliers},
    types::{DiversePermIter, Instance, NonDomPoint, Objective, ParetoFront},
};

pub struct MipPd<Hss> {
    hitting_set_solver: Option<Hss>,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
    stats: crate::Stats,
    lims: Limits,
    logger: Option<Box<dyn crate::WriteSolverLog>>,
    term_flag: Arc<AtomicBool>,
    /// The objectives
    objs: Vec<Objective>,
    objective_multipliers: Vec<f64>,
    opts: MipPdOptions,
    rng: fastrand::Rng,
}

impl<Hss> super::Solve for MipPd<Hss>
where
    Hss: HittingSetSolver,
{
    fn solve(&mut self, limits: Limits) -> MaybeTerminatedError {
        self.stats.n_solve_calls += 1;
        self.lims = limits;
        let mut hss = self.hitting_set_solver.take().unwrap();
        let res = self.alg_main(&mut hss);
        self.hitting_set_solver = Some(hss);
        res
    }

    fn all_stats(
        &self,
    ) -> (
        crate::Stats,
        Option<SolverStats>,
        Option<Vec<EncodingStats>>,
        Option<hitting_sets::Statistics>,
    ) {
        (
            self.stats,
            None,
            None,
            Some(self.hitting_set_solver.as_ref().unwrap().statistics()),
        )
    }
}

impl<Hss> super::KernelFunctions for MipPd<Hss> {
    fn pareto_front(&self) -> ParetoFront {
        self.pareto_front.clone()
    }

    fn stats(&self) -> crate::Stats {
        self.stats
    }

    fn attach_logger<L: crate::WriteSolverLog + 'static>(&mut self, logger: L) {
        self.logger = Some(Box::new(logger));
    }

    fn detach_logger(&mut self) -> Option<Box<dyn crate::WriteSolverLog>> {
        self.logger.take()
    }

    fn interrupter(&mut self) -> super::Interrupter {
        super::Interrupter {
            term_flag: self.term_flag.clone(),
            #[cfg(feature = "interrupt-oracle")]
            oracle_interrupter: None,
        }
    }
}

impl<Hss> MipPd<Hss>
where
    Hss: HittingSetSolver,
{
    pub fn from_instance_default_blocking(
        inst: Instance,
        opts: MipPdOptions,
    ) -> anyhow::Result<Self> {
        let Instance { clauses, objs, .. } = inst;
        let mut builder = Hss::Builder::new(objs.iter().map(|obj| obj.iter()));
        builder.threads(opts.threads);
        let mut hitting_set_solver = builder.init();

        let mut rng = fastrand::Rng::with_seed(opts.random_seed);

        let weight_sums_and_max = |objs: &[Objective]| {
            let mut max_weight_sum = usize::MAX;
            let mut weight_sums = vec![];
            for obj in objs {
                let sum = obj.iter().fold(0, |sum, (_, w)| sum + w);
                weight_sums.push(sum);
                max_weight_sum = std::cmp::max(max_weight_sum, sum);
            }
            (weight_sums, max_weight_sum)
        };
        let mut objective_multipliers;
        match opts.multipliers {
            ObjectiveMultipliers::Ones => {
                objective_multipliers = vec![1.; objs.len()];
            }
            ObjectiveMultipliers::Normalized => {
                let (sums, max) = weight_sums_and_max(&objs);
                objective_multipliers = sums
                    .into_iter()
                    .map(|sum| (max as f64) / (sum as f64))
                    .collect();
                hitting_set_solver.change_multipliers(&objective_multipliers);
            }
            ObjectiveMultipliers::Random => {
                objective_multipliers =
                    (0..objs.len()).map(|_| f64::from(rng.i8(1..=10))).collect();
                hitting_set_solver.change_multipliers(&objective_multipliers);
            }
            ObjectiveMultipliers::NormalizedRandom => {
                let (sums, max) = weight_sums_and_max(&objs);
                objective_multipliers = sums
                    .into_iter()
                    .map(|sum| (max as f64) / (sum as f64) * f64::from(rng.i8(1..=10)))
                    .collect();
                hitting_set_solver.change_multipliers(&objective_multipliers);
            }
            ObjectiveMultipliers::Lexicographic => {
                objective_multipliers = Vec::with_capacity(objs.len());
                let mut mult = 1;
                for obj in objs.iter().rev() {
                    let sum = obj.iter().fold(0, |sum, (_, w)| sum + w);
                    objective_multipliers.push(mult as f64);
                    mult *= sum;
                    mult += 1;
                }
                objective_multipliers.reverse();
                hitting_set_solver.change_multipliers(&objective_multipliers);
            }
        }

        let stats = Stats {
            n_objs: objs.len(),
            n_real_objs: objs.iter().fold(0, |cnt, o| {
                if matches!(o, Objective::Constant { .. }) {
                    cnt
                } else {
                    cnt + 1
                }
            }),
            n_orig_clauses: clauses.len(),
            ..Default::default()
        };
        for (cl, _) in clauses {
            hitting_set_solver.add_clause(&cl);
        }
        Ok(Self {
            hitting_set_solver: Some(hitting_set_solver),
            pareto_front: Default::default(),
            stats,
            lims: Limits::none(),
            logger: None,
            term_flag: Arc::new(AtomicBool::new(false)),
            objs,
            objective_multipliers,
            opts,
            rng,
        })
    }

    /// Checks the termination flag and terminates if appropriate
    fn check_termination(&self) -> MaybeTerminated {
        if self.term_flag.load(Ordering::Relaxed) {
            MaybeTerminated::Terminated(Termination::Interrupted)
        } else {
            MaybeTerminated::Done(())
        }
    }

    /// Logs a solution. Can return a termination if the solution limit is reached.
    fn log_solution(&mut self) -> MaybeTerminatedError {
        self.stats.n_solutions += 1;
        // Dispatch to logger
        if let Some(logger) = &mut self.logger {
            logger.log_solution().context("logger failed")?;
        }
        // Update limit and check termination
        if let Some(solutions) = &mut self.lims.sols {
            *solutions -= 1;
            if *solutions == 0 {
                return MaybeTerminatedError::Terminated(Termination::SolsLimit);
            }
        }
        Done(())
    }

    /// Logs a non-dominated point. Can return a termination if the non-dominated point limit is reached.
    fn log_non_dominated(&mut self, non_dominated: &NonDomPoint) -> MaybeTerminatedError {
        self.stats.n_non_dominated += 1;
        // Dispatch to logger
        if let Some(logger) = &mut self.logger {
            logger
                .log_non_dominated(non_dominated)
                .context("logger failed")?;
        }
        // Update limit and check termination
        if let Some(pps) = &mut self.lims.pps {
            *pps -= 1;
            if *pps == 0 {
                return MaybeTerminatedError::Terminated(Termination::PPLimit);
            }
        }
        Done(())
    }

    /// Converts an internal cost vector to an external one. Internal cost is
    /// purely the encoding output while external cost takes an offset and
    /// multiplier into account.
    fn externalize_internal_costs(&self, costs: &[usize]) -> Vec<isize> {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        costs
            .iter()
            .enumerate()
            .map(|(idx, &cst)| match self.objs[idx] {
                Objective::Weighted { offset, .. } => {
                    let signed_cst: isize = cst.try_into().expect("cost exceeds `isize`");
                    signed_cst + offset
                }
                Objective::Unweighted {
                    offset,
                    unit_weight,
                    ..
                } => {
                    let signed_mult_cost: isize = (cst * unit_weight)
                        .try_into()
                        .expect("multiplied cost exceeds `isize`");
                    signed_mult_cost + offset
                }
                Objective::Constant { offset, .. } => {
                    debug_assert_eq!(cst, 0);
                    offset
                }
            })
            .collect()
    }

    /// The solving algorithm main routine.
    fn alg_main(&mut self, hss: &mut Hss) -> MaybeTerminatedError {
        if let Some(logger) = &mut self.logger {
            logger.log_routine_start("mip-pd")?;
        }
        if self.opts.precompute_lexicographic > 0 {
            let obj_mult = self.objective_multipliers.clone();
            for idx_perm in DiversePermIter::new(
                0..self.objs.len(),
                self.opts.precompute_lexicographic,
                self.rng.u64(..),
            ) {
                assert_eq!(idx_perm.len(), self.objs.len());
                // compute multipliers for lexicographic optimization
                let mut mult = 1;
                for obj_idx in idx_perm.into_iter() {
                    self.objective_multipliers[obj_idx] = mult as f64;
                    let obj = &self.objs[obj_idx];
                    let sum = obj.iter().fold(0, |sum, (_, w)| sum + w);
                    mult *= sum;
                    mult += 1;
                }
                hss.change_multipliers(&self.objective_multipliers);
                // find optimum
                if let Some(logger) = &mut self.logger {
                    logger.log_routine_start("MIP find solution")?;
                }
                let hitting_set_answer = hss.optimal_hitting_set_callbacks(None, self)?;
                self.check_termination()?;
                let (_, hitting_set) = match hitting_set_answer {
                    CompleteSolveResult::Optimal(cost, hitting_set) => (cost, hitting_set),
                    CompleteSolveResult::Infeasible => {
                        if let Some(logger) = &mut self.logger {
                            logger.log_routine_end()?;
                            logger.log_routine_end()?;
                        }
                        return Done(());
                    }
                };
                if let Some(logger) = &mut self.logger {
                    logger.log_routine_end()?;
                }
                self.check_termination()?;
                let (costs, solution) =
                    self.hitting_set_to_solution_and_internal_costs(hitting_set);
                if self.is_dominated_by_pareto_front(&costs) {
                    continue;
                }
                self.yield_solution(costs, solution)?;
            }
            self.objective_multipliers = obj_mult;
            hss.change_multipliers(&self.objective_multipliers);
            // lazily add PD cuts only now
            for non_dom in self.pareto_front.iter() {
                hss.add_pd_cut(non_dom.internal_costs());
            }
            if let Some(logger) = &mut self.logger {
                logger.log_message(&format!(
                    "precomputed {} lexicographic optima",
                    self.pareto_front.len()
                ))?;
            }
        }
        loop {
            if let Some(logger) = &mut self.logger {
                logger.log_routine_start("MIP find solution")?;
            }
            let hitting_set_answer = hss.optimal_hitting_set_callbacks(None, self)?;
            let (cost, hitting_set) = match hitting_set_answer {
                CompleteSolveResult::Optimal(cost, hitting_set) => (cost, hitting_set),
                CompleteSolveResult::Infeasible => {
                    if let Some(logger) = &mut self.logger {
                        logger.log_routine_end()?;
                        logger.log_routine_end()?;
                    }
                    return Done(());
                }
            };
            if let Some(logger) = &mut self.logger {
                logger.log_routine_end()?;
                logger.log_hitting_set(cost, true)?;
            }
            self.check_termination()?;
            let (costs, solution) = self.hitting_set_to_solution_and_internal_costs(hitting_set);
            // introduce PD cut in the hitting set solver
            hss.add_pd_cut(&costs);
            // store solution
            self.yield_solution(costs, solution)?;
            self.check_termination()?;
        }
    }

    fn yield_solution(&mut self, costs: Vec<usize>, solution: Assignment) -> MaybeTerminatedError {
        let mut non_dominated = NonDomPoint::new(self.externalize_internal_costs(&costs), costs);
        non_dominated.add_sol(solution);
        match self.log_solution() {
            Done(_) => {
                let nd_term = self.log_non_dominated(&non_dominated);
                self.pareto_front.extend([non_dominated]);
                nd_term?;
            }
            MaybeTerminatedError::Terminated(term) => {
                let nd_term = self.log_non_dominated(&non_dominated);
                self.pareto_front.extend([non_dominated]);
                nd_term?;
                return MaybeTerminatedError::Terminated(term);
            }
            MaybeTerminatedError::Error(err) => {
                let nd_term = self.log_non_dominated(&non_dominated);
                self.pareto_front.extend([non_dominated]);
                nd_term?;
                return MaybeTerminatedError::Error(err);
            }
        }
        self.check_termination()?;
        Done(())
    }

    fn compute_internal_costs(&self, solution: &Assignment) -> Vec<usize> {
        (0..self.objs.len())
            .map(|idx| {
                let mut cost = 0;
                for (l, w) in self.objs[idx].iter() {
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
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        (costs, sol)
    }

    fn is_dominated_by_pareto_front(&self, costs: &[usize]) -> bool {
        'non_dom: for non_dom in self.pareto_front.iter() {
            for (&non_dom_cst, &current_cst) in non_dom.internal_costs().iter().zip(costs) {
                if current_cst < non_dom_cst {
                    continue 'non_dom;
                }
            }
            return true;
        }
        false
    }
}

impl<Hss> hitting_sets::Callbacks for MipPd<Hss> {
    fn check_termination(&self) -> bool {
        self.term_flag.load(std::sync::atomic::Ordering::Relaxed)
    }
}
