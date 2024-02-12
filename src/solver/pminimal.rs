//! # $P$-Minimal Model Enumeration for Multi-Objective Optimization
//!
//! This module implements $P$-minimal model enumeration as an algorithm for
//! solving multi-objective optimization problems expressed as boolean logic.
//! Instead of using the order encoding as in \[1\], any cardinality (for
//! unweighted objectives) or pseudo-boolean encoding from
//! [RustSAT](https://github.com/chrjabs/rustsat) can be used. The actual
//! enumeration algorithm follows \[2\].
//!
//! ## References
//!
//! - \[1\] Takehide Soh and Mutsunori Banbara and Naoyuki Tamura and Daniel Le
//!   Berre: _Solving Multiobjective Discrete Optimization Problems with
//!   Propositional Minimal Model Generation_, CP 2017.
//! - \[2\] Miyuki Koshimura and Hidetomo Nabeshima and Hiroshi Fujita and Ryuzo
//!   Hasegawa: _Minimal Model Generation with Respect to an Atom Set_, FTP
//!   2009.

use crate::{
    options::{AfterCbOptions, CoreBoostingOptions, EnumOptions},
    solver::ObjEncoding,
    types::ParetoFront,
    EncodingStats, ExtendedSolveStats, KernelFunctions, KernelOptions, Limits, Phase, Solve,
    Termination,
};
use rustsat::{
    encodings,
    encodings::{
        card::{self, DbTotalizer},
        pb::{self, DbGte},
        EncodeStats,
    },
    instances::{BasicVarManager, Cnf, ManageVars, MultiOptInstance},
    solvers::{SolveIncremental, SolveStats, SolverResult, SolverStats},
    types::{Assignment, Clause, Lit},
};
use rustsat_cadical::CaDiCaL;
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use super::{
    coreboosting::MergeOllRef, default_blocking_clause, CoreBoost, Objective, SolverKernel,
};

/// The solver type. Generics the pseudo-boolean encoding to use for weighted
/// objectives, the cardinality encoding to use for unweighted objectives, the
/// variable manager to use and the SAT backend.
#[derive(KernelFunctions, Solve)]
#[solve(
    bounds = "where PBE: pb::BoundUpperIncremental + EncodeStats,
        CE: card::BoundUpperIncremental + EncodeStats,
        VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental + SolveStats",
    extended_stats
)]
pub struct PMinimal<
    PBE = DbGte,
    CE = DbTotalizer,
    VM = BasicVarManager,
    BCG = fn(Assignment) -> Clause,
    O = CaDiCaL<'static, 'static>,
> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: Vec<ObjEncoding<PBE, CE>>,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

#[oracle_bounds]
impl<PBE, CE, VM, O> PMinimal<PBE, CE, VM, fn(Assignment) -> Clause, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    O: SolveIncremental,
{
    pub fn new_default_blocking(
        inst: MultiOptInstance<VM>,
        oracle: O,
        opts: KernelOptions,
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

#[oracle_bounds]
impl<PBE, CE, VM, BCG, O> PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + Default,
{
    pub fn new_default_oracle(
        inst: MultiOptInstance<VM>,
        opts: KernelOptions,
        block_clause_gen: BCG,
    ) -> Result<Self, Termination> {
        let kernel = SolverKernel::new(inst, O::default(), block_clause_gen, opts)?;
        Ok(Self::init(kernel))
    }
}

#[oracle_bounds]
impl<PBE, CE, VM, O> PMinimal<PBE, CE, VM, fn(Assignment) -> Clause, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    O: SolveIncremental + Default,
{
    pub fn new_defaults(
        inst: MultiOptInstance<VM>,
        opts: KernelOptions,
    ) -> Result<Self, Termination> {
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            O::default(),
            default_blocking_clause,
            opts,
        )?;
        Ok(Self::init(kernel))
    }
}

#[oracle_bounds]
impl<PBE, CE, VM, BCG, O> PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental,
{
    /// Initializes a default solver with a configured oracle and options. The
    /// oracle should _not_ have any clauses loaded yet.
    pub fn new(
        inst: MultiOptInstance<VM>,
        oracle: O,
        opts: KernelOptions,
        block_clause_gen: BCG,
    ) -> Result<Self, Termination> {
        let kernel = SolverKernel::new(inst, oracle, block_clause_gen, opts)?;
        Ok(Self::init(kernel))
    }
}

impl<PBE, CE, VM, BCG, O> ExtendedSolveStats for PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: encodings::EncodeStats,
    CE: encodings::EncodeStats,
    O: SolveStats,
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

impl<PBE, CE, VM, BCG, O> PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
{
    /// Initializes the solver
    fn init(mut kernel: SolverKernel<VM, O, BCG>) -> Self {
        // Initialize objective encodings
        let obj_encs = kernel
            .objs
            .iter()
            .map(|obj| match obj {
                Objective::Weighted { lits, .. } => ObjEncoding::new_weighted(
                    lits.iter().map(|(&l, &w)| (l, w)),
                    kernel.opts.reserve_enc_vars,
                    &mut kernel.var_manager,
                ),
                Objective::Unweighted { lits, .. } => ObjEncoding::new_unweighted(
                    lits.iter().copied(),
                    kernel.opts.reserve_enc_vars,
                    &mut kernel.var_manager,
                ),
                Objective::Constant { .. } => ObjEncoding::Constant,
            })
            .collect();
        Self {
            kernel,
            obj_encs,
            pareto_front: Default::default(),
        }
    }
}

#[oracle_bounds]
impl<PBE, CE, VM, BCG, O> PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + SolveStats,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> Result<(), Termination> {
        debug_assert_eq!(self.obj_encs.len(), self.kernel.stats.n_objs);
        self.kernel.log_routine_start("p-minimal")?;
        loop {
            // Find minimization starting point
            let res = self.kernel.solve()?;
            if SolverResult::Unsat == res {
                self.kernel.log_routine_end()?;
                return Ok(());
            }
            self.kernel.check_termination()?;

            // Minimize solution
            let (costs, solution) = self.kernel.get_solution_and_internal_costs(
                self.kernel
                    .opts
                    .heuristic_improvements
                    .solution_tightening
                    .wanted(Phase::OuterLoop),
            )?;
            self.kernel.log_candidate(&costs, Phase::OuterLoop)?;
            self.kernel.check_termination()?;
            self.kernel.phase_solution(solution.clone())?;
            let (costs, solution, block_switch) =
                self.kernel
                    .p_minimization(costs, solution, &[], &mut self.obj_encs)?;

            let assumps = self.kernel.enforce_dominating(&costs, &mut self.obj_encs);
            self.kernel
                .yield_solutions(costs, &assumps, solution, &mut self.pareto_front)?;

            // Block last Pareto point, if temporarily blocked
            if let Some(block_lit) = block_switch {
                self.kernel.oracle.add_unit(block_lit)?;
            }
        }
    }
}

#[oracle_bounds]
impl<PBE, CE, VM, BCG, O> CoreBoost for PMinimal<PBE, CE, VM, BCG, O>
where
    (PBE, CE): MergeOllRef<PBE = PBE, CE = CE>,
    VM: ManageVars,
    O: SolveIncremental + SolveStats + Default,
{
    fn core_boost(&mut self, opts: CoreBoostingOptions) -> Result<bool, Termination> {
        if self.kernel.stats.n_solve_calls > 0 {
            return Err(Termination::CbAfterSolve);
        }
        let cb_res = if let Some(cb_res) = self.kernel.core_boost()? {
            cb_res
        } else {
            return Ok(false);
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
                return Ok(true);
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
        Ok(true)
    }
}

#[oracle_bounds]
impl<VM, O, BCG> SolverKernel<VM, O, BCG>
where
    VM: ManageVars,
    O: SolveIncremental + SolveStats,
{
    /// Executes P-minimization from a cost and solution starting point
    pub fn p_minimization<PBE, CE>(
        &mut self,
        mut costs: Vec<usize>,
        mut solution: Assignment,
        base_assumps: &[Lit],
        obj_encs: &mut [ObjEncoding<PBE, CE>],
    ) -> Result<(Vec<usize>, Assignment, Option<Lit>), Termination>
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
    {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        self.log_routine_start("p minimization")?;
        let mut block_switch = None;
        let mut assumps = Vec::from(base_assumps);
        #[cfg(feature = "coarse-convergence")]
        let mut coarse = true;
        loop {
            let bound_costs: Vec<_> = costs
                .iter()
                .enumerate()
                .map(|(_oidx, &c)| {
                    #[cfg(feature = "coarse-convergence")]
                    if coarse {
                        return obj_encs[_oidx].coarse_ub(c);
                    }
                    c
                })
                .collect();
            // Force next solution to dominate the current one
            assumps.drain(base_assumps.len()..);
            assumps.extend(self.enforce_dominating(&bound_costs, obj_encs));
            // Block solutions dominated by the current one
            if self.opts.enumeration == EnumOptions::NoEnum {
                // Block permanently since no enumeration at Pareto point
                let block_clause = self.dominated_block_clause(&costs, obj_encs);
                self.oracle.add_clause(block_clause)?;
            } else {
                // Permanently block last candidate
                if let Some(block_lit) = block_switch {
                    self.oracle.add_unit(block_lit)?;
                }
                // Temporarily block to allow for enumeration at Pareto point
                let block_lit = self.tmp_block_dominated(&costs, obj_encs);
                block_switch = Some(block_lit);
                assumps.push(block_lit);
            }

            // Check if dominating solution exists
            let res = self.solve_assumps(&assumps)?;
            if res == SolverResult::Unsat {
                #[cfg(feature = "coarse-convergence")]
                if bound_costs != costs {
                    // Switch to fine convergence
                    coarse = false;
                    continue;
                }
                self.log_routine_end()?;
                // Termination criteria, return last solution and costs
                return Ok((costs, solution, block_switch));
            }
            self.check_termination()?;

            (costs, solution) = self.get_solution_and_internal_costs(
                self.opts
                    .heuristic_improvements
                    .solution_tightening
                    .wanted(Phase::Minimization),
            )?;
            self.log_candidate(&costs, Phase::Minimization)?;
            self.check_termination()?;
            self.phase_solution(solution.clone())?;
        }
    }

    /// Gets assumptions to enforce that the next solution dominates the given
    /// cost point.
    pub fn enforce_dominating<PBE, CE>(
        &mut self,
        costs: &[usize],
        obj_encs: &mut [ObjEncoding<PBE, CE>],
    ) -> Vec<Lit>
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
    {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        let mut assumps = vec![];
        costs.iter().enumerate().for_each(|(idx, &cst)| {
            let enc = &mut obj_encs[idx];
            enc.encode_ub_change(cst..cst + 1, &mut self.oracle, &mut self.var_manager);
            assumps.extend(enc.enforce_ub(cst).unwrap());
        });
        assumps
    }

    /// Gets a clause blocking solutions (weakly) dominated by the given cost point,
    /// given objective encodings.
    pub fn dominated_block_clause<PBE, CE>(
        &mut self,
        costs: &[usize],
        obj_encs: &mut [ObjEncoding<PBE, CE>],
    ) -> Clause
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
    {
        debug_assert_eq!(costs.len(), obj_encs.len());
        costs
            .iter()
            .enumerate()
            .filter_map(|(idx, &cst)| {
                // Don't block
                if cst <= obj_encs[idx].offset() {
                    return None;
                }
                let enc = &mut obj_encs[idx];
                if let ObjEncoding::Constant = enc {
                    return None;
                }
                // Encode and add to solver
                enc.encode_ub_change(cst - 1..cst, &mut self.oracle, &mut self.var_manager);
                let assumps = enc.enforce_ub(cst - 1).unwrap();
                if assumps.len() == 1 {
                    Some(assumps[0])
                } else {
                    let mut and_impl = Cnf::new();
                    let and_lit = self.var_manager.new_var().pos_lit();
                    and_impl.add_lit_impl_cube(and_lit, &assumps);
                    self.oracle.add_cnf(and_impl).unwrap();
                    Some(and_lit)
                }
            })
            .collect()
    }

    /// Temporarily blocks solutions dominated by the given cost point. Returns
    /// and assumption that needs to be enforced in order for the blocking to be
    /// enforced.
    pub fn tmp_block_dominated<PBE, CE>(
        &mut self,
        costs: &[usize],
        obj_encs: &mut [ObjEncoding<PBE, CE>],
    ) -> Lit
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
    {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        let mut clause = self.dominated_block_clause(costs, obj_encs);
        let block_lit = self.var_manager.new_var().pos_lit();
        clause.add(block_lit);
        self.oracle.add_clause(clause).unwrap();
        !block_lit
    }
}
