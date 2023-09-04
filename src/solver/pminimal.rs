//! The P-Minimal model enumeration algorithm

use crate::{
    options::EnumOptions, types::ParetoPoint, EncodingStats, ExtendedSolveStats, Limits, Options,
    ParetoFront, Phase, Solve, Stats, Termination, WriteSolverLog,
};
use rustsat::{
    encodings,
    encodings::{card, pb},
    instances::{Cnf, ManageVars, MultiOptInstance},
    solvers::{
        ControlSignal, FlipLit, PhaseLit, SolveIncremental, SolveStats, SolverResult, SolverStats,
        Terminate,
    },
    types::{Assignment, Clause, Lit, LitIter, WLitIter},
};

use super::{default_blocking_clause, Objective, SolverKernel};

/// The solver type. Generics the pseudo-boolean encoding to use for weighted
/// objectives, the cardinality encoding to use for unweighted objectives, the
/// variable manager to use and the SAT backend.
pub struct PMinimal<PBE, CE, VM, BCG, O> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: Vec<ObjEncoding<PBE, CE>>,
}

impl<PBE, CE, VM, O> PMinimal<PBE, CE, VM, fn(Assignment) -> Clause, O>
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

impl<PBE, CE, VM, BCG, O> PMinimal<PBE, CE, VM, BCG, O>
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

impl<PBE, CE, VM, O> PMinimal<PBE, CE, VM, fn(Assignment) -> Clause, O>
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

impl<PBE, CE, VM, BCG, O> PMinimal<PBE, CE, VM, BCG, O>
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

impl<PBE, CE, VM, BCG, O> Solve<VM, BCG> for PMinimal<PBE, CE, VM, BCG, O>
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

impl<PBE, CE, VM, BCG, O> ExtendedSolveStats for PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental + encodings::EncodeStats,
    CE: card::BoundUpperIncremental + encodings::EncodeStats,
    O: SolveIncremental + SolveStats,
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

impl<PBE, CE, VM, BCG, O> PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
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
                    lits.iter().map(|&l| l),
                    kernel.opts.reserve_enc_vars,
                    &mut kernel.var_manager,
                ),
                Objective::Constant { .. } => ObjEncoding::Constant,
            })
            .collect();
        Self { kernel, obj_encs }
    }
}

impl<PBE, CE, VM, BCG, O> PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + PhaseLit + FlipLit,
{
    /// The solving algorithm main routine. This will never return [`Ok`] but
    /// Result is used as a return type to be able to use `?` syntax for
    /// termination from subroutines.
    fn alg_main(&mut self) -> Result<(), Termination> {
        debug_assert_eq!(self.obj_encs.len(), self.kernel.stats.n_objs);
        loop {
            // Find minimization starting point
            let res = self.kernel.oracle.solve()?;
            self.kernel.log_oracle_call(res, Phase::OuterLoop)?;
            if res == SolverResult::Unsat {
                return Ok(());
            } else if res == SolverResult::Interrupted {
                return Err(Termination::Callback);
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

            self.enumerate_at_pareto_point(costs, solution)?;

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
                let block_clause = self.dominated_block_clause(&costs);
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
            let res = self.kernel.oracle.solve_assumps(assumps)?;
            if res == SolverResult::Interrupted {
                return Err(Termination::Callback);
            }
            self.kernel.log_oracle_call(res, Phase::Minimization)?;
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

    /// Enumerates solutions at a Pareto point
    fn enumerate_at_pareto_point(
        &mut self,
        costs: Vec<usize>,
        mut solution: Assignment,
    ) -> Result<(), Termination> {
        debug_assert_eq!(costs.len(), self.kernel.stats.n_objs);
        self.kernel.unphase_solution()?;

        // Assumptions to enforce staying at the Pareto point
        let assumps = self.enforce_dominating(&costs);

        // Create Pareto point
        let mut pareto_point = ParetoPoint::new(self.kernel.externalize_internal_costs(costs));

        // Truncate internal solution to only include original variables
        solution = solution.truncate(self.kernel.max_orig_var);

        loop {
            // TODO: add debug assert checking solution cost
            pareto_point.add_sol(solution.clone());
            match self.kernel.log_solution() {
                Ok(_) => (),
                Err(term) => {
                    let pp_term = self.kernel.log_pareto_point(&pareto_point);
                    self.kernel.pareto_front.add_pp(pareto_point);
                    pp_term?;
                    return Err(term);
                }
            }
            if match self.kernel.opts.enumeration {
                EnumOptions::NoEnum => true,
                EnumOptions::Solutions(Some(limit)) => pareto_point.n_sols() >= limit,
                EnumOptions::PMCSs(Some(limit)) => pareto_point.n_sols() >= limit,
                _unlimited => false,
            } {
                let pp_term = self.kernel.log_pareto_point(&pareto_point);
                self.kernel.pareto_front.add_pp(pareto_point);
                return pp_term;
            }
            self.kernel.check_terminator()?;

            // Block last solution
            match self.kernel.opts.enumeration {
                EnumOptions::Solutions(_) => {
                    self.kernel
                        .oracle
                        .add_clause((self.kernel.block_clause_gen)(solution))?
                }
                EnumOptions::PMCSs(_) => self
                    .kernel
                    .oracle
                    .add_clause(self.kernel.block_pareto_mcs(solution))?,
                EnumOptions::NoEnum => panic!("Should never reach this"),
            }

            // Find next solution
            let res = self.kernel.oracle.solve_assumps(assumps.clone())?;
            if res == SolverResult::Interrupted {
                return Err(Termination::Callback);
            }
            self.kernel.log_oracle_call(res, Phase::Enumeration)?;
            if res == SolverResult::Unsat {
                let pp_term = self.kernel.log_pareto_point(&pareto_point);
                // All solutions enumerated
                self.kernel.pareto_front.add_pp(pareto_point);
                return pp_term;
            }
            self.kernel.check_terminator()?;
            solution = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
        }
    }

    /// Gets assumptions to enforce that the next solution dominates the given
    /// cost point.
    fn enforce_dominating(&mut self, costs: &Vec<usize>) -> Vec<Lit> {
        debug_assert_eq!(costs.len(), self.kernel.stats.n_objs);
        let mut assumps = vec![];
        costs.iter().enumerate().for_each(|(idx, &cst)| {
            match &mut self.obj_encs[idx] {
                ObjEncoding::Weighted(encoding) => {
                    // Encode and add to solver
                    self.kernel
                        .oracle
                        .add_cnf(
                            encoding.encode_ub_change(cst..cst + 1, &mut self.kernel.var_manager),
                        )
                        .unwrap();
                    // Extend assumptions
                    assumps.extend(encoding.enforce_ub(cst).unwrap());
                }
                ObjEncoding::Unweighted(encoding) => {
                    // Encode and add to solver
                    self.kernel
                        .oracle
                        .add_cnf(
                            encoding.encode_ub_change(cst..cst + 1, &mut self.kernel.var_manager),
                        )
                        .unwrap();
                    // Extend assumptions
                    assumps.extend(encoding.enforce_ub(cst).unwrap());
                }
                ObjEncoding::Constant => (),
            }
        });
        assumps
    }

    /// Temporarily blocks solutions dominated by the given cost point. Returns
    /// and assumption that needs to be enforced in order for the blocking to be
    /// enforced.
    fn tmp_block_dominated(&mut self, costs: &Vec<usize>) -> Lit {
        debug_assert_eq!(costs.len(), self.kernel.stats.n_objs);
        let mut clause = self.dominated_block_clause(costs);
        let block_lit = self.kernel.var_manager.new_var().pos_lit();
        clause.add(block_lit);
        self.kernel.oracle.add_clause(clause).unwrap();
        !block_lit
    }

    /// Gets a clause blocking solutions dominated by the given cost point.
    fn dominated_block_clause(&mut self, costs: &Vec<usize>) -> Clause {
        debug_assert_eq!(costs.len(), self.kernel.stats.n_objs);
        let mut clause = Clause::new();
        costs.iter().enumerate().for_each(|(idx, &cst)| {
            // Don't block
            if cst == 0 {
                return;
            }
            match &mut self.obj_encs[idx] {
                ObjEncoding::Weighted(encoding) => {
                    // Encode and add to solver
                    self.kernel
                        .oracle
                        .add_cnf(
                            encoding.encode_ub_change(cst - 1..cst, &mut self.kernel.var_manager),
                        )
                        .unwrap();
                    // Add one enforcing assumption to clause
                    let assumps = encoding.enforce_ub(cst - 1).unwrap();
                    if assumps.len() == 1 {
                        clause.add(assumps[0]);
                    } else {
                        let mut and_impl = Cnf::new();
                        let and_lit = self.kernel.var_manager.new_var().pos_lit();
                        and_impl.add_lit_impl_cube(and_lit, assumps);
                        self.kernel.oracle.add_cnf(and_impl).unwrap();
                        clause.add(and_lit);
                    }
                }
                ObjEncoding::Unweighted(encoding) => {
                    // Encode and add to solver
                    self.kernel
                        .oracle
                        .add_cnf(
                            encoding.encode_ub_change(cst - 1..cst, &mut self.kernel.var_manager),
                        )
                        .unwrap();
                    // Add one enforcing assumption to clause
                    let assumps = encoding.enforce_ub(cst - 1).unwrap();
                    if assumps.len() == 1 {
                        clause.add(assumps[0]);
                    } else {
                        let mut and_impl = Cnf::new();
                        let and_lit = self.kernel.var_manager.new_var().pos_lit();
                        and_impl.add_lit_impl_cube(and_lit, assumps);
                        self.kernel.oracle.add_cnf(and_impl).unwrap();
                        clause.add(and_lit);
                    }
                }
                ObjEncoding::Constant => (),
            }
        });
        clause
    }
}

/// Internal data associated with an objective
enum ObjEncoding<PBE, CE> {
    Weighted(PBE),
    Unweighted(CE),
    Constant,
}

impl<PBE, CE> ObjEncoding<PBE, CE>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
{
    /// Initializes a new objective encoding for a weighted objective
    fn new_weighted<VM: ManageVars, LI: WLitIter>(
        lits: LI,
        reserve: bool,
        var_manager: &mut VM,
    ) -> Self {
        let mut encoding = PBE::from_iter(lits);
        if reserve {
            encoding.reserve(var_manager);
        }
        ObjEncoding::Weighted(encoding)
    }

    /// Initializes a new objective encoding for a weighted objective
    fn new_unweighted<VM: ManageVars, LI: LitIter>(
        lits: LI,
        reserve: bool,
        var_manager: &mut VM,
    ) -> Self {
        let mut encoding = CE::from_iter(lits);
        if reserve {
            encoding.reserve(var_manager);
        }
        ObjEncoding::Unweighted(encoding)
    }
}
