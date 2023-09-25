//! # Sequential Divide and Conquer

use rustsat::{
    instances::{ManageVars, MultiOptInstance},
    solvers::{SolveIncremental, SolveStats},
    types::{Assignment, Clause, Lit},
};
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{
    solver::{default_blocking_clause, SolverKernel},
    KernelFunctions, Limits, Options, Solve, Termination,
};

use super::Worker;

#[derive(KernelFunctions, Solve)]
#[kernel(kernel = "self.worker.kernel")]
#[solve(bounds = "where VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental + SolveStats")]
pub struct DivCon<VM, O, BCG> {
    /// The single worker structure
    worker: Worker<VM, O, BCG>,
    /// The index of the last non-dominated point in the Pareto front that has
    /// been blocked
    last_blocked: usize,
}

impl<VM, O> DivCon<VM, O, fn(Assignment) -> Clause>
where
    VM: ManageVars,
    O: SolveIncremental,
{
    pub fn new_default_blocking(
        inst: MultiOptInstance<VM>,
        oracle: O,
        opts: Options,
    ) -> Result<Self, Termination> {
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            oracle,
            default_blocking_clause,
            opts,
        )?;
        Ok(Self::init(kernel))
    }
}

impl<VM, O> DivCon<VM, O, fn(Assignment) -> Clause>
where
    VM: ManageVars,
    O: SolveIncremental + Default,
{
    pub fn new_defaults(inst: MultiOptInstance<VM>, opts: Options) -> Result<Self, Termination> {
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            O::default(),
            default_blocking_clause,
            opts,
        )?;
        Ok(Self::init(kernel))
    }
}

impl<VM, O, BCG> DivCon<VM, O, BCG>
where
    VM: ManageVars,
{
    /// Initializes the solver
    fn init(kernel: SolverKernel<VM, O, BCG>) -> Self {
        let worker = Worker::init(kernel);
        Self {
            worker,
            last_blocked: 0,
        }
    }
}

#[oracle_bounds]
impl<VM, O, BCG> DivCon<VM, O, BCG>
where
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + SolveStats,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> Result<(), Termination> {
        self.worker.kernel.log_routine_start("seq-div-con")?;
        let all_objs: Vec<_> = (0..self.worker.kernel.stats.n_objs).collect();
        self.solve_subproblem(&[], &all_objs)?;
        self.worker.kernel.log_routine_end()?;
        return Ok(());
    }

    /// Recurses down into the subproblems and solves them
    fn solve_subproblem(
        &mut self,
        base_assumps: &[Lit],
        obj_idxs: &[usize],
    ) -> Result<(), Termination> {
        // TODO: filtering not just through cutting solutions to avoid unsat calls
        loop {
            let mut ideal = vec![0; self.worker.kernel.stats.n_objs];
            if !self.worker.find_ideal(base_assumps, obj_idxs, &mut ideal)? {
                break;
            }
            if obj_idxs.len() == self.worker.kernel.stats.n_objs {
                if let Some(logger) = &mut self.worker.kernel.logger {
                    logger.log_ideal(&ideal)?;
                }
            }

            // TODO: use upper bound from ideal point computation
            if obj_idxs.len() == 2 && self.worker.kernel.opts.bioptsat {
                self.worker
                    .bioptsat((obj_idxs[0], obj_idxs[1]), base_assumps, None, |_| None)?;
                self.cut_dominated()?;
                return Ok(());
            }
            if obj_idxs.len() == 1 {
                self.worker
                    .linsu_yield(obj_idxs[0], base_assumps, None, None)?;
                self.cut_dominated()?;
                return Ok(());
            }

            // recursion
            for idx in 0..obj_idxs.len() {
                let fixed_obj = obj_idxs[idx];
                let mut subproblem = Vec::from(obj_idxs);
                // TODO: consider using swap_remove here. using remove for now to make debugging less confusing.
                subproblem.remove(idx);
                let mut assumps = Vec::from(base_assumps);
                assumps.extend(self.worker.bound_objective(fixed_obj, ideal[fixed_obj]));
                self.solve_subproblem(&assumps, &subproblem)?;
            }
        }
        Ok(())
    }

    fn cut_dominated(&mut self) -> Result<(), Termination> {
        let mut costs = Vec::new();
        for point_idx in self.last_blocked..self.worker.kernel.pareto_front.len() {
            costs.extend(
                self.worker
                    .kernel
                    .internalize_external_costs(self.worker.kernel.pareto_front[point_idx].costs()),
            );
        }
        let mut points = Vec::new();
        for start_idx in (0..costs.len()).step_by(self.worker.kernel.stats.n_objs) {
            points.push(&costs[start_idx..start_idx + self.worker.kernel.stats.n_objs]);
        }
        self.worker.cut_dominated(&points)?;
        self.last_blocked = self.worker.kernel.pareto_front.len();
        Ok(())
    }
}
