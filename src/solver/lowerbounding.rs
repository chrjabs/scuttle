//! # Multi-Objective Lower-Bounding Search
//!
//! Algorithm proposed in \[1\].
//!
//! ## References
//!
//! - \[1\] Joao Cortes and Ines Lynce and Vasco M. Maquinho: _New Core-Guided
//! and Hitting Set Algorithms for Multi-Objective Combinatorial Optimization_,
//! TACAS 2023.

use rustsat::{
    encodings::{self, card, pb},
    instances::{Cnf, ManageVars, MultiOptInstance},
    solvers::{
        ControlSignal, FlipLit, PhaseLit, SolveIncremental, SolveStats, SolverResult, SolverStats,
        Terminate,
    },
    types::{Assignment, Clause, Lit},
};

use crate::{
    options::EnumOptions, types::ParetoFront, EncodingStats, ExtendedSolveStats, Limits, Options,
    Phase, Solve, Stats, Termination, WriteSolverLog,
};

use super::{default_blocking_clause, ObjEncoding, Objective, SolverKernel};

pub struct LowerBounding<PBE, CE, VM, BCG, O> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: Vec<ObjEncoding<PBE, CE>>,
    /// The current fence
    fence: Fence,
}

impl<PBE, CE, VM, O> LowerBounding<PBE, CE, VM, fn(Assignment) -> Clause, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
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

impl<PBE, CE, VM, BCG, O> LowerBounding<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + Default,
{
    pub fn new_default_oracle(
        inst: MultiOptInstance<VM>,
        opts: Options,
        block_clause_gen: BCG,
    ) -> Result<Self, Termination> {
        let kernel = SolverKernel::new(inst, O::default(), block_clause_gen, opts)?;
        Ok(Self::init(kernel))
    }
}

impl<PBE, CE, VM, O> LowerBounding<PBE, CE, VM, fn(Assignment) -> Clause, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
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

impl<PBE, CE, VM, BCG, O> LowerBounding<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental,
{
    /// Initializes a default solver with a configured oracle and options. The
    /// oracle should _not_ have any clauses loaded yet.
    pub fn new(
        inst: MultiOptInstance<VM>,
        oracle: O,
        opts: Options,
        block_clause_gen: BCG,
    ) -> Result<Self, Termination> {
        let kernel = SolverKernel::new(inst, oracle, block_clause_gen, opts)?;
        Ok(Self::init(kernel))
    }
}

impl<PBE, CE, VM, BCG, O> Solve for LowerBounding<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + PhaseLit + FlipLit + Default + Terminate<'static>,
{
    fn solve(&mut self, limits: Limits) -> Result<(), Termination> {
        self.kernel.start_solving(limits);
        self.alg_main()
    }

    fn pareto_front(&self) -> ParetoFront {
        self.kernel.pareto_front.clone()
    }

    fn stats(&self) -> Stats {
        self.kernel.stats
    }

    fn attach_logger<L: WriteSolverLog + 'static>(&mut self, logger: L) {
        self.kernel.attach_logger(logger)
    }

    fn detach_logger(&mut self) -> Option<Box<dyn WriteSolverLog>> {
        self.kernel.detach_logger()
    }

    fn attach_terminator(&mut self, term_cb: fn() -> ControlSignal) {
        self.kernel.attach_terminator(term_cb)
    }

    fn detach_terminator(&mut self) {
        self.kernel.detach_terminator()
    }
}

impl<PBE, CE, VM, BCG, O> ExtendedSolveStats for LowerBounding<PBE, CE, VM, BCG, O>
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
                    ObjEncoding::Weighted(enc) => {
                        s.n_vars = enc.n_vars();
                        s.n_clauses = enc.n_clauses()
                    }
                    ObjEncoding::Unweighted(enc) => {
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

impl<PBE, CE, VM, BCG, O> LowerBounding<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
    O: SolveIncremental,
{
    /// Initializes the solver
    fn init(mut kernel: SolverKernel<VM, O, BCG>) -> Self {
        // Initialize objective encodings
        let (obj_encs, fence_data) = kernel
            .objs
            .iter()
            .map(|obj| {
                let mut enc = match obj {
                    Objective::Weighted { lits, .. } => ObjEncoding::<PBE, CE>::new_weighted(
                        lits.iter().map(|(&l, &w)| (l, w)),
                        kernel.opts.reserve_enc_vars,
                        &mut kernel.var_manager,
                    ),
                    Objective::Unweighted { lits, .. } => ObjEncoding::<PBE, CE>::new_unweighted(
                        lits.iter().map(|&l| l),
                        kernel.opts.reserve_enc_vars,
                        &mut kernel.var_manager,
                    ),
                    Objective::Constant { .. } => ObjEncoding::Constant,
                };
                kernel
                    .oracle
                    .add_cnf(enc.encode_ub_change(0..1, &mut kernel.var_manager))
                    .expect("couldn't add cnf to oracle");
                let assumps = enc.enforce_ub(0).unwrap();
                let assump = if assumps.is_empty() {
                    None
                } else if 1 == assumps.len() {
                    Some(assumps[0])
                } else {
                    let mut and_impl = Cnf::new();
                    let and_lit = kernel.var_manager.new_var().pos_lit();
                    and_impl.add_lit_impl_cube(and_lit, assumps);
                    kernel.oracle.add_cnf(and_impl).unwrap();
                    Some(and_lit)
                };
                (enc, (0, assump))
            })
            .unzip();
        Self {
            kernel,
            obj_encs,
            fence: Fence { data: fence_data },
        }
    }
}

impl<PBE, CE, VM, BCG, O> LowerBounding<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + PhaseLit + FlipLit,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> Result<(), Termination> {
        debug_assert_eq!(self.obj_encs.len(), self.kernel.stats.n_objs);
        loop {
            let res = self.kernel.solve_assumps(self.fence.assumps())?;
            match res {
                SolverResult::Sat => self.harvest()?,
                SolverResult::Unsat => {
                    let core = self.kernel.oracle.core()?;
                    if core.is_empty() {
                        return Ok(());
                    }
                    self.update_fence(core)?;
                }
                SolverResult::Interrupted => panic!("should have errored before"),
            }
        }
    }

    fn update_fence(&mut self, core: Vec<Lit>) -> Result<(), Termination> {
        'core: for clit in core {
            for (obj_idx, (bound, olit)) in self.fence.data.iter_mut().enumerate() {
                if let Some(alit) = &olit {
                    if !*alit == clit {
                        // update bound
                        let enc = &mut self.obj_encs[obj_idx];
                        *bound = enc.next_higher(*bound);
                        self.kernel.oracle.add_cnf(
                            enc.encode_ub_change(*bound..*bound + 1, &mut self.kernel.var_manager),
                        )?;
                        let assumps = enc.enforce_ub(*bound).unwrap();
                        *olit = if assumps.is_empty() {
                            None
                        } else if 1 == assumps.len() {
                            Some(assumps[0])
                        } else {
                            let mut and_impl = Cnf::new();
                            let and_lit = self.kernel.var_manager.new_var().pos_lit();
                            and_impl.add_lit_impl_cube(and_lit, assumps);
                            self.kernel.oracle.add_cnf(and_impl).unwrap();
                            Some(and_lit)
                        };
                        continue 'core;
                    }
                }
            }
            panic!("should never encounter clit that is not in fence");
        }
        if let Some(logger) = &mut self.kernel.logger {
            logger.log_fence(self.fence.bounds())?
        }
        Ok(())
    }

    /// Runs the P-Minimal algorithm within the fence to harvest solutions
    fn harvest(&mut self) -> Result<(), Termination> {
        debug_assert_eq!(self.obj_encs.len(), self.kernel.stats.n_objs);
        loop {
            // Find minimization starting point
            let res = self.kernel.solve_assumps(self.fence.assumps())?;
            if SolverResult::Unsat == res {
                return Ok(());
            }
            self.kernel.check_terminator()?;

            // Minimize solution
            let (costs, solution) = self.kernel.get_solution_and_internal_costs(
                self.kernel
                    .opts
                    .heuristic_improvements
                    .solution_tightening
                    .wanted(Phase::OuterLoop),
            )?;
            self.kernel.log_candidate(&costs, Phase::OuterLoop)?;
            self.kernel.check_terminator()?;
            self.kernel.phase_solution(solution.clone())?;
            let (costs, solution, block_switch) = self.p_minimization(costs, solution)?;

            let assumps = self.enforce_dominating(&costs);
            self.kernel.yield_solutions(costs, assumps, solution)?;

            // Block last Pareto point, if temporarily blocked
            if let Some(block_lit) = block_switch {
                self.kernel.oracle.add_unit(block_lit)?;
            }
        }
    }

    /// Executes P-minimization from a cost and solution starting point
    fn p_minimization(
        &mut self,
        mut costs: Vec<usize>,
        mut solution: Assignment,
    ) -> Result<(Vec<usize>, Assignment, Option<Lit>), Termination> {
        debug_assert_eq!(costs.len(), self.kernel.stats.n_objs);
        let mut block_switch = None;
        loop {
            // Force next solution to dominate the current one
            let mut assumps = self.enforce_dominating(&costs);
            // Block solutions dominated by the current one
            if self.kernel.opts.enumeration == EnumOptions::NoEnum {
                // Block permanently since no enumeration at Pareto point
                let block_clause = self
                    .kernel
                    .dominated_block_clause(&costs, &mut self.obj_encs);
                self.kernel.oracle.add_clause(block_clause)?;
            } else {
                // Permanently block last candidate
                if let Some(block_lit) = block_switch {
                    self.kernel.oracle.add_unit(block_lit)?;
                }
                // Temporarily block to allow for enumeration at Pareto point
                let block_lit = self.tmp_block_dominated(&costs);
                block_switch = Some(block_lit);
                assumps.push(block_lit);
            }

            // Check if dominating solution exists
            let res = self.kernel.solve_assumps(assumps)?;
            if res == SolverResult::Unsat {
                // Termination criteria, return last solution and costs
                return Ok((costs, solution, block_switch));
            }
            self.kernel.check_terminator()?;

            (costs, solution) = self.kernel.get_solution_and_internal_costs(
                self.kernel
                    .opts
                    .heuristic_improvements
                    .solution_tightening
                    .wanted(Phase::Minimization),
            )?;
            self.kernel.log_candidate(&costs, Phase::Minimization)?;
            self.kernel.check_terminator()?;
            self.kernel.phase_solution(solution.clone())?;
        }
    }

    /// Gets assumptions to enforce that the next solution dominates the given
    /// cost point.
    fn enforce_dominating(&mut self, costs: &Vec<usize>) -> Vec<Lit> {
        debug_assert_eq!(costs.len(), self.kernel.stats.n_objs);
        let mut assumps = vec![];
        costs.iter().enumerate().for_each(|(idx, &cst)| {
            let enc = &mut self.obj_encs[idx];
            self.kernel
                .oracle
                .add_cnf(enc.encode_ub_change(cst..cst + 1, &mut self.kernel.var_manager))
                .unwrap();
            assumps.extend(enc.enforce_ub(cst).unwrap());
        });
        assumps
    }

    /// Temporarily blocks solutions dominated by the given cost point. Returns
    /// and assumption that needs to be enforced in order for the blocking to be
    /// enforced.
    fn tmp_block_dominated(&mut self, costs: &Vec<usize>) -> Lit {
        debug_assert_eq!(costs.len(), self.kernel.stats.n_objs);
        let mut clause = self
            .kernel
            .dominated_block_clause(costs, &mut self.obj_encs);
        let block_lit = self.kernel.var_manager.new_var().pos_lit();
        clause.add(block_lit);
        self.kernel.oracle.add_clause(clause).unwrap();
        !block_lit
    }
}

/// Data related to the current fence
struct Fence {
    /// The current bounds and enforcing literals
    data: Vec<(usize, Option<Lit>)>,
}

impl Fence {
    fn assumps(&self) -> Vec<Lit> {
        self.data
            .iter()
            .filter_map(|(_, ol)| ol.to_owned())
            .collect()
    }
    
    fn bounds(&self) -> Vec<usize> {
        self.data.iter().map(|&(b, _)| b).collect()
    }
}
