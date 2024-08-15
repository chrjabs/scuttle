//! # Multi-Objective Lower-Bounding Search
//!
//! Algorithm proposed in \[1\].
//!
//! ## References
//!
//! - \[1\] Joao Cortes and Ines Lynce and Vasco M. Maquinho: _New Core-Guided
//!     and Hitting Set Algorithms for Multi-Objective Combinatorial Optimization_,
//!     TACAS 2023.

use rustsat::{
    encodings::{
        self,
        card::{self, DbTotalizer},
        pb::{self, DbGte},
        EncodeStats,
    },
    instances::{BasicVarManager, Cnf, ManageVars, MultiOptInstance},
    solvers::{SolveIncremental, SolveStats, SolverResult, SolverStats},
    types::{Assignment, Clause, Lit},
};
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{
    options::{AfterCbOptions, CoreBoostingOptions},
    termination::ensure,
    types::{NonDomPoint, ParetoFront},
    EncodingStats, ExtendedSolveStats, KernelFunctions, KernelOptions, Limits,
    MaybeTerminatedError::{self, Done},
    Phase, Solve,
};

use super::{
    coreboosting::MergeOllRef, default_blocking_clause, CoreBoost, ObjEncoding, Objective,
    SolverKernel,
};

#[derive(KernelFunctions, Solve)]
#[solve(
    bounds = "where PBE: pb::BoundUpperIncremental + EncodeStats,
        CE: card::BoundUpperIncremental + EncodeStats,
        VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental + SolveStats",
    extended_stats
)]
pub struct LowerBounding<
    O,
    PBE = DbGte,
    CE = DbTotalizer,
    VM = BasicVarManager,
    BCG = fn(Assignment) -> Clause,
> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: Vec<ObjEncoding<PBE, CE>>,
    /// The current fence
    fence: Fence,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

#[oracle_bounds]
impl<O, PBE, CE, VM> LowerBounding<O, PBE, CE, VM, fn(Assignment) -> Clause>
where
    O: SolveIncremental + SolveStats,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
{
    pub fn new_default_blocking(
        inst: MultiOptInstance<VM>,
        oracle: O,
        opts: KernelOptions,
    ) -> anyhow::Result<Self> {
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            oracle,
            default_blocking_clause,
            opts,
        )?;
        Ok(Self::init(kernel)?)
    }
}

#[oracle_bounds]
impl<O, PBE, CE, VM, BCG> LowerBounding<O, PBE, CE, VM, BCG>
where
    O: SolveIncremental + SolveStats + Default,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
{
    pub fn new_default_oracle(
        inst: MultiOptInstance<VM>,
        opts: KernelOptions,
        block_clause_gen: BCG,
    ) -> anyhow::Result<Self> {
        let kernel = SolverKernel::new(inst, O::default(), block_clause_gen, opts)?;
        Ok(Self::init(kernel)?)
    }
}

#[oracle_bounds]
impl<O, PBE, CE, VM> LowerBounding<O, PBE, CE, VM, fn(Assignment) -> Clause>
where
    O: SolveIncremental + SolveStats + Default,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
{
    pub fn new_defaults(inst: MultiOptInstance<VM>, opts: KernelOptions) -> anyhow::Result<Self> {
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            O::default(),
            default_blocking_clause,
            opts,
        )?;
        Ok(Self::init(kernel)?)
    }
}

#[oracle_bounds]
impl<O, PBE, CE, VM, BCG> LowerBounding<O, PBE, CE, VM, BCG>
where
    O: SolveIncremental + SolveStats,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
{
    /// Initializes a default solver with a configured oracle and options. The
    /// oracle should _not_ have any clauses loaded yet.
    pub fn new(
        inst: MultiOptInstance<VM>,
        oracle: O,
        opts: KernelOptions,
        block_clause_gen: BCG,
    ) -> anyhow::Result<Self> {
        let kernel = SolverKernel::new(inst, oracle, block_clause_gen, opts)?;
        Ok(Self::init(kernel)?)
    }
}

impl<O, PBE, CE, VM, BCG> ExtendedSolveStats for LowerBounding<O, PBE, CE, VM, BCG>
where
    O: SolveStats,
    PBE: encodings::EncodeStats,
    CE: encodings::EncodeStats,
{
    fn oracle_stats(&self) -> SolverStats {
        self.kernel.oracle.stats()
    }

    fn encoding_stats(&self) -> Vec<EncodingStats> {
        self.kernel
            .objs
            .iter()
            .zip(self.obj_encs.iter())
            .map(|(obj, enc)| {
                let mut s = EncodingStats {
                    offset: obj.offset(),
                    ..Default::default()
                };
                if let Objective::Unweighted { unit_weight, .. } = obj {
                    s.unit_weight = Some(*unit_weight);
                };
                match enc {
                    ObjEncoding::Weighted(enc, _) => {
                        s.n_vars = enc.n_vars();
                        s.n_clauses = enc.n_clauses()
                    }
                    ObjEncoding::Unweighted(enc, _) => {
                        s.n_vars = enc.n_vars();
                        s.n_clauses = enc.n_clauses()
                    }
                    ObjEncoding::Constant => (),
                };
                s
            })
            .collect()
    }
}

impl<O, PBE, CE, VM, BCG> LowerBounding<O, PBE, CE, VM, BCG>
where
    O: SolveIncremental + SolveStats,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
{
    /// Initializes the solver
    fn init(mut kernel: SolverKernel<VM, O, BCG>) -> Result<Self, rustsat::OutOfMemory> {
        // Initialize objective encodings
        let mut obj_encs = Vec::with_capacity(kernel.objs.len());
        let mut fence_data = Vec::with_capacity(kernel.objs.len());
        for obj in &kernel.objs {
            let mut enc = match obj {
                Objective::Weighted { lits, .. } => ObjEncoding::<PBE, CE>::new_weighted(
                    lits.iter().map(|(&l, &w)| (l, w)),
                    kernel.opts.reserve_enc_vars,
                    &mut kernel.var_manager,
                ),
                Objective::Unweighted { lits, .. } => ObjEncoding::<PBE, CE>::new_unweighted(
                    lits.iter().copied(),
                    kernel.opts.reserve_enc_vars,
                    &mut kernel.var_manager,
                ),
                Objective::Constant { .. } => ObjEncoding::Constant,
            };
            enc.encode_ub_change(0..1, &mut kernel.oracle, &mut kernel.var_manager)?;
            let assumps = enc.enforce_ub(0).unwrap();
            let assump = if assumps.is_empty() {
                None
            } else if 1 == assumps.len() {
                Some(assumps[0])
            } else {
                let mut and_impl = Cnf::new();
                let and_lit = kernel.var_manager.new_var().pos_lit();
                and_impl.add_lit_impl_cube(and_lit, &assumps);
                kernel.oracle.add_cnf(and_impl).unwrap();
                Some(and_lit)
            };
            obj_encs.push(enc);
            fence_data.push((0, assump));
        }
        Ok(Self {
            kernel,
            obj_encs,
            fence: Fence { data: fence_data },
            pareto_front: Default::default(),
        })
    }
}

#[oracle_bounds]
impl<O, PBE, CE, VM, BCG> LowerBounding<O, PBE, CE, VM, BCG>
where
    O: SolveIncremental + SolveStats,
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> MaybeTerminatedError {
        debug_assert_eq!(self.obj_encs.len(), self.kernel.stats.n_objs);
        self.kernel.log_routine_start("lower-bounding")?;
        loop {
            let assumps: Vec<_> = self.fence.assumps().collect();
            let res = self.kernel.solve_assumps(&assumps)?;
            match res {
                SolverResult::Sat => self.kernel.harvest(
                    &self.fence,
                    &mut self.obj_encs,
                    &[],
                    &mut self.pareto_front,
                )?,
                SolverResult::Unsat => {
                    let core = self.kernel.oracle.core()?;
                    if core.is_empty() {
                        self.kernel.log_routine_end()?;
                        return Done(());
                    }
                    #[cfg(debug_assertions)]
                    let old_fence = self.fence.bounds();
                    self.kernel
                        .update_fence(&mut self.fence, core, &mut self.obj_encs)?;
                    #[cfg(debug_assertions)]
                    {
                        let new_fence = self.fence.bounds();
                        let mut increased = false;
                        for idx in 0..old_fence.len() {
                            debug_assert!(old_fence[idx] <= new_fence[idx]);
                            if old_fence[idx] < new_fence[idx] {
                                increased = true;
                            }
                        }
                        if !increased {
                            panic!("fence has not increased");
                        }
                    }
                }
                SolverResult::Interrupted => panic!("should have errored before"),
            }
        }
    }
}

#[oracle_bounds]
impl<O, PBE, CE, VM, BCG> CoreBoost for LowerBounding<O, PBE, CE, VM, BCG>
where
    O: SolveIncremental + SolveStats + Default,
    (PBE, CE): MergeOllRef<PBE = PBE, CE = CE>,
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
{
    fn core_boost(&mut self, opts: CoreBoostingOptions) -> MaybeTerminatedError<bool> {
        ensure!(
            self.kernel.stats.n_solve_calls == 0,
            "cannot perform core boosting after solve has been called"
        );
        let cb_res = if let Some(cb_res) = self.kernel.core_boost()? {
            cb_res
        } else {
            return Done(false);
        };
        self.kernel.check_termination()?;
        let reset_dbs = match &opts.after {
            AfterCbOptions::Nothing => false,
            AfterCbOptions::Reset => {
                self.kernel.reset_oracle(true)?;
                self.kernel.check_termination()?;
                true
            }
            AfterCbOptions::Inpro(techs) => {
                self.obj_encs = self.kernel.inprocess(techs, cb_res)?;
                self.kernel.check_termination()?;
                return Done(true);
            }
        };
        self.kernel.log_routine_start("merge encodings")?;
        for (oidx, (reform, mut tot_db)) in cb_res.into_iter().enumerate() {
            if reset_dbs {
                tot_db.reset_vars();
            }
            if !matches!(self.kernel.objs[oidx], Objective::Constant { .. }) {
                self.obj_encs[oidx] = <(PBE, CE)>::merge(reform, tot_db, opts.rebase);
            }
            self.kernel.check_termination()?;
        }
        self.kernel.log_routine_end()?;
        // Update fence
        for (idx, enc) in self.obj_encs.iter_mut().enumerate() {
            enc.encode_ub_change(
                enc.offset()..enc.offset() + 1,
                &mut self.kernel.oracle,
                &mut self.kernel.var_manager,
            )?;
            let assumps = enc.enforce_ub(enc.offset()).unwrap();
            let assump = if assumps.is_empty() {
                None
            } else if 1 == assumps.len() {
                Some(assumps[0])
            } else {
                let mut and_impl = Cnf::new();
                let and_lit = self.kernel.var_manager.new_var().pos_lit();
                and_impl.add_lit_impl_cube(and_lit, &assumps);
                self.kernel.oracle.add_cnf(and_impl).unwrap();
                Some(and_lit)
            };
            self.fence.data[idx] = (enc.offset(), assump);
        }
        Done(true)
    }
}

/// Data related to the current fence
pub(crate) struct Fence {
    /// The current bounds and enforcing literals
    pub data: Vec<(usize, Option<Lit>)>,
}

impl Fence {
    pub fn assumps(&self) -> impl Iterator<Item = Lit> + '_ {
        self.data.iter().filter_map(|(_, ol)| ol.to_owned())
    }

    pub fn bounds(&self) -> Vec<usize> {
        self.data.iter().map(|&(b, _)| b).collect()
    }
}

#[oracle_bounds]
impl<VM, O, BCG> SolverKernel<VM, O, BCG>
where
    VM: ManageVars,
    O: SolveIncremental + SolveStats,
{
    pub fn update_fence<PBE, CE>(
        &mut self,
        fence: &mut Fence,
        core: Vec<Lit>,
        obj_encs: &mut [ObjEncoding<PBE, CE>],
    ) -> MaybeTerminatedError
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
    {
        'core: for clit in core {
            for (obj_idx, (bound, olit)) in fence.data.iter_mut().enumerate() {
                if let Some(alit) = &olit {
                    if !*alit == clit {
                        // update bound
                        let enc = &mut obj_encs[obj_idx];
                        *bound = enc.next_higher(*bound);
                        enc.encode_ub_change(
                            *bound..*bound + 1,
                            &mut self.oracle,
                            &mut self.var_manager,
                        )?;
                        let assumps = enc.enforce_ub(*bound).unwrap();
                        *olit = if assumps.is_empty() {
                            None
                        } else if 1 == assumps.len() {
                            Some(assumps[0])
                        } else {
                            let mut and_impl = Cnf::new();
                            let and_lit = self.var_manager.new_var().pos_lit();
                            and_impl.add_lit_impl_cube(and_lit, &assumps);
                            self.oracle.add_cnf(and_impl).unwrap();
                            Some(and_lit)
                        };
                        continue 'core;
                    }
                }
            }
            panic!("should never encounter clit that is not in fence");
        }
        if let Some(logger) = &mut self.logger {
            logger.log_fence(&fence.bounds())?
        }
        Done(())
    }
}

#[oracle_bounds]
impl<VM, O, BCG> SolverKernel<VM, O, BCG>
where
    VM: ManageVars,
    O: SolveIncremental + SolveStats,
    BCG: FnMut(Assignment) -> Clause,
{
    /// Runs the P-Minimal algorithm within the fence to harvest solutions
    pub fn harvest<PBE, CE, Col>(
        &mut self,
        fence: &Fence,
        obj_encs: &mut [ObjEncoding<PBE, CE>],
        base_assumps: &[Lit],
        collector: &mut Col,
    ) -> MaybeTerminatedError
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
        Col: Extend<NonDomPoint>,
    {
        debug_assert_eq!(obj_encs.len(), self.stats.n_objs);
        self.log_routine_start("harvest")?;
        let mut assumps = Vec::from(base_assumps);
        loop {
            assumps.drain(base_assumps.len()..);
            // Find minimization starting point
            assumps.extend(fence.assumps());
            let res = self.solve_assumps(&assumps)?;
            if SolverResult::Unsat == res {
                self.log_routine_end()?;
                return Done(());
            }
            self.check_termination()?;

            // Minimize solution
            let (costs, solution) = self.get_solution_and_internal_costs(
                self.opts
                    .heuristic_improvements
                    .solution_tightening
                    .wanted(Phase::OuterLoop),
            )?;
            self.log_candidate(&costs, Phase::OuterLoop)?;
            self.check_termination()?;
            self.phase_solution(solution.clone())?;
            let (costs, solution, block_switch) =
                self.p_minimization(costs, solution, base_assumps, obj_encs)?;

            let assumps: Vec<_> = self.enforce_dominating(&costs, obj_encs)?.collect();
            self.yield_solutions(costs, &assumps, solution, collector)?;

            // Block last Pareto point, if temporarily blocked
            if let Some(block_lit) = block_switch {
                self.oracle.add_unit(block_lit)?;
            }
        }
    }
}
