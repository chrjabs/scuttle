//! # Sequential Divide and Conquer

use rustsat::{
    instances::{BasicVarManager, ManageVars, MultiOptInstance},
    solvers::{SolveIncremental, SolveStats},
    types::{Assignment, Clause, Lit},
};
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{
    options::{BuildEncodings, DivConAnchor, DivConOptions},
    solver::{default_blocking_clause, Objective, SolverKernel},
    types::ParetoFront,
    KernelFunctions, KernelOptions, Limits, Solve, Termination,
};

use super::Worker;

#[derive(KernelFunctions, Solve)]
#[kernel(kernel = "self.worker.kernel")]
#[solve(bounds = "where VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental + SolveStats + Default")]
pub struct DivCon<
    VM = BasicVarManager,
    O = rustsat_cadical::CaDiCaL<'static, 'static>,
    BCG = fn(Assignment) -> Clause,
> {
    /// The single worker structure
    worker: Worker<VM, O, BCG>,
    /// The index of the last non-dominated point in the Pareto front that has
    /// been blocked
    last_blocked: usize,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
    /// The algorithm options
    opts: DivConOptions,
}

#[oracle_bounds]
impl<VM, O> DivCon<VM, O, fn(Assignment) -> Clause>
where
    VM: ManageVars,
    O: SolveIncremental,
{
    pub fn new_default_blocking(
        inst: MultiOptInstance<VM>,
        oracle: O,
        opts: DivConOptions,
    ) -> Result<Self, Termination> {
        let kernel_opts = KernelOptions {
            store_cnf: opts.kernel.store_cnf
                || opts.build_encodings == BuildEncodings::CleanRebuild
                || opts.inpro.is_some()
                || opts.reset_after_global_ideal,
            ..opts.kernel
        };
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            oracle,
            default_blocking_clause,
            kernel_opts,
        )?;
        Ok(Self::init(kernel, opts))
    }
}

#[oracle_bounds]
impl<VM, O> DivCon<VM, O, fn(Assignment) -> Clause>
where
    VM: ManageVars,
    O: SolveIncremental + Default,
{
    pub fn new_defaults(
        inst: MultiOptInstance<VM>,
        opts: DivConOptions,
    ) -> Result<Self, Termination> {
        let kernel_opts = KernelOptions {
            store_cnf: opts.kernel.store_cnf
                || opts.build_encodings == BuildEncodings::CleanRebuild
                || opts.inpro.is_some()
                || opts.reset_after_global_ideal,
            ..opts.kernel
        };
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            O::default(),
            default_blocking_clause,
            kernel_opts,
        )?;
        Ok(Self::init(kernel, opts))
    }
}

impl<VM, O, BCG> DivCon<VM, O, BCG>
where
    VM: ManageVars,
{
    /// Initializes the solver
    fn init(kernel: SolverKernel<VM, O, BCG>, opts: DivConOptions) -> Self {
        let worker = Worker::init(kernel);
        Self {
            worker,
            last_blocked: 0,
            pareto_front: Default::default(),
            opts,
        }
    }
}

#[oracle_bounds]
impl<VM, O, BCG> DivCon<VM, O, BCG>
where
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + SolveStats + Default,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> Result<(), Termination> {
        self.worker.kernel.log_routine_start("seq-div-con")?;
        let all_objs: Vec<_> = (0..self.worker.kernel.stats.n_objs)
            .filter(|&oidx| !matches!(self.worker.kernel.objs[oidx], Objective::Constant { .. }))
            .collect();
        debug_assert_eq!(all_objs.len(), self.worker.kernel.stats.n_real_objs);
        self.solve_subproblem(vec![0; self.worker.kernel.stats.n_objs], &[], &all_objs)?;
        self.worker.kernel.log_routine_end()?;
        Ok(())
    }

    /// Recurses down into the subproblems and solves them
    fn solve_subproblem(
        &mut self,
        mut ideal: Vec<usize>,
        base_assumps: &[Lit],
        obj_idxs: &[usize],
    ) -> Result<(), Termination> {
        debug_assert_eq!(ideal.len(), self.worker.kernel.stats.n_objs);
        // TODO: filtering not just through cutting solutions to avoid unsat calls
        loop {
            if obj_idxs.len() == 1 {
                debug_assert!(matches!(
                    self.opts.anchor,
                    DivConAnchor::LinSu
                        | DivConAnchor::NMinus(_)
                        | DivConAnchor::PMinimal(_)
                        | DivConAnchor::LowerBounding(_)
                ));
                self.worker.linsu_yield(
                    obj_idxs[0],
                    base_assumps,
                    None,
                    Some(ideal[obj_idxs[0]]),
                    &mut self.pareto_front,
                    self.opts.rebase_encodings,
                )?;
                self.cut_dominated()?;
                return Ok(());
            }

            if let DivConAnchor::NMinus(x) = self.opts.anchor {
                if obj_idxs.len() <= self.worker.kernel.stats.n_real_objs - x {
                    match obj_idxs.len() {
                        0..=1 => panic!("should never have 0 or 1 objectives here"),
                        2 => {
                            self.worker.bioptsat(
                                (obj_idxs[0], obj_idxs[1]),
                                base_assumps,
                                None,
                                (Some(ideal[obj_idxs[0]]), Some(ideal[obj_idxs[1]])),
                                |_| None,
                                &mut self.pareto_front,
                                self.opts.rebase_encodings,
                            )?;
                            self.cut_dominated()?;
                            return Ok(());
                        }
                        _ => {
                            self.worker.p_minimal(
                                base_assumps,
                                None,
                                &mut self.pareto_front,
                                self.opts.rebase_encodings,
                            )?;
                            return Ok(());
                        }
                    }
                }
            }

            if let DivConAnchor::PMinimal(sub_size) = self.opts.anchor {
                if obj_idxs.len() < self.worker.kernel.stats.n_real_objs
                    && obj_idxs.len() <= sub_size.absolute(self.worker.kernel.stats.n_real_objs)
                {
                    self.worker.p_minimal(
                        base_assumps,
                        None,
                        &mut self.pareto_front,
                        self.opts.rebase_encodings,
                    )?;
                    return Ok(());
                }
            }

            if let DivConAnchor::LowerBounding(sub_size) = self.opts.anchor {
                if obj_idxs.len() < self.worker.kernel.stats.n_real_objs
                    && obj_idxs.len() <= sub_size.absolute(self.worker.kernel.stats.n_real_objs)
                {
                    self.worker.lower_bounding(
                        base_assumps,
                        &mut self.pareto_front,
                        self.opts.rebase_encodings,
                    )?;
                    return Ok(());
                }
            }

            if !self.worker.find_ideal(base_assumps, obj_idxs, &mut ideal)? {
                break;
            }
            if obj_idxs.len() == self.worker.kernel.stats.n_real_objs {
                debug_assert!(base_assumps.is_empty());
                // for master problem
                if let Some(logger) = &mut self.worker.kernel.logger {
                    logger.log_ideal(&ideal)?;
                }

                let mut reset = false;
                if matches!(
                    self.opts.build_encodings,
                    BuildEncodings::Rebuild | BuildEncodings::CleanRebuild
                ) {
                    if self.worker.rebuild_obj_encodings(
                        self.opts.build_encodings == BuildEncodings::CleanRebuild,
                        self.opts.rebase_encodings,
                    )? {
                        reset = true;
                        self.last_blocked = 0;
                        self.cut_dominated()?;
                    }
                }
                if !reset && self.opts.reset_after_global_ideal {
                    self.worker.reset_oracle()?;
                    self.last_blocked = 0;
                    self.cut_dominated()?;
                }
            }

            #[cfg(feature = "data-helpers")]
            if self.opts.enc_clauses_summary {
                self.worker.enc_clauses_summary()?;
                return Ok(());
            }

            // TODO: use upper bound from ideal point computation
            if self.opts.anchor == DivConAnchor::BiOptSat && obj_idxs.len() == 2 {
                self.worker.bioptsat(
                    (obj_idxs[0], obj_idxs[1]),
                    base_assumps,
                    None,
                    (Some(ideal[obj_idxs[0]]), Some(ideal[obj_idxs[1]])),
                    |_| None,
                    &mut self.pareto_front,
                    self.opts.rebase_encodings,
                )?;
                self.cut_dominated()?;
                return Ok(());
            }

            if let DivConAnchor::PMinimal(sub_size) = self.opts.anchor {
                if obj_idxs.len() <= sub_size.absolute(self.worker.kernel.stats.n_real_objs) {
                    if let Some(techs) = &self.opts.inpro {
                        self.worker.inpro_and_reset(techs)?;
                    }
                    self.worker.p_minimal(
                        base_assumps,
                        None,
                        &mut self.pareto_front,
                        self.opts.rebase_encodings,
                    )?;
                    return Ok(());
                }
            }

            if let DivConAnchor::LowerBounding(sub_size) = self.opts.anchor {
                if obj_idxs.len() <= sub_size.absolute(self.worker.kernel.stats.n_real_objs) {
                    if let Some(techs) = &self.opts.inpro {
                        self.worker.inpro_and_reset(techs)?;
                    }
                    self.worker.lower_bounding(
                        base_assumps,
                        &mut self.pareto_front,
                        self.opts.rebase_encodings,
                    )?;
                    return Ok(());
                }
            }

            // recursion
            for idx in 0..obj_idxs.len() {
                let fixed_obj = obj_idxs[idx];
                let mut subproblem = Vec::from(obj_idxs);
                subproblem.remove(idx);
                //subproblem.swap_remove(idx);
                let mut assumps = Vec::from(base_assumps);
                assumps.extend(self.worker.bound_objective(
                    fixed_obj,
                    ideal[fixed_obj],
                    self.opts.rebase_encodings,
                )?);
                self.solve_subproblem(ideal.clone(), &assumps, &subproblem)?;
            }
        }
        Ok(())
    }

    fn cut_dominated(&mut self) -> Result<(), Termination> {
        let mut costs = Vec::new();
        for point_idx in self.last_blocked..self.pareto_front.len() {
            costs.extend(
                self.worker
                    .kernel
                    .internalize_external_costs(self.pareto_front[point_idx].costs()),
            );
        }
        let mut points = Vec::new();
        for start_idx in (0..costs.len()).step_by(self.worker.kernel.stats.n_objs) {
            points.push(&costs[start_idx..start_idx + self.worker.kernel.stats.n_objs]);
        }
        self.worker
            .cut_dominated(&points, self.opts.rebase_encodings)?;
        self.last_blocked = self.pareto_front.len();
        Ok(())
    }
}
