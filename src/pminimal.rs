//! This the main module of the solver containing the implementation of the algorithm.

use std::ops::Not;

use crate::{
    default_blocking_clause, types::ParetoPoint, EncodingStats, ExtendedSolveStats, Limits,
    LoggerError, Options, OracleStats, ParetoFront, Phase, Solve, Stats, Termination,
    WriteSolverLog,
};
use rustsat::{
    encodings,
    encodings::{card, pb},
    instances::{ManageVars, MultiOptInstance, Objective, CNF},
    solvers::{ControlSignal, DefIncSolver, IncrementalSolve, SolveStats, SolverResult, Terminate},
    types::{Assignment, Clause, Lit, RsHashMap, RsHashSet, TernaryVal, Var},
    var,
};

/// The solver type. Generics the pseudo-boolean encoding to use for weighted
/// objectives, the cardinality encoding to use for unweighted objectives, the
/// variable manager to use and the SAT backend.
pub struct PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: pb::IncUB + 'static,
    CE: card::IncUB + 'static,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: IncrementalSolve + Default + Terminate<'static>,
{
    /// The SAT solver backend
    oracle: O,
    /// The variable manager keeping track of variables
    var_manager: VM,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: Vec<ObjEncoding<PBE, CE>>,
    /// All clauses that contain objective literals. Only populated when using
    /// model tightening. If blocking literals were added by the solver, the
    /// blocking literal is _not_ in the clause kept here.
    obj_clauses: Vec<Clause>,
    /// Maps soft clauses to blocking literals
    blits: RsHashMap<Clause, Lit>,
    /// Objective literal data
    obj_lit_data: RsHashMap<Lit, ObjLitData>,
    /// The maximum variable of the original encoding after introducing blocking
    /// variables
    max_orig_var: Var,
    /// Generator of blocking clauses
    block_clause_gen: BCG,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
    /// Configuration options
    opts: Options,
    /// Running statistics
    stats: Stats,
    /// Limits for the current solving run
    lims: Limits,
    /// Loggers to log with
    loggers: Vec<Option<Box<dyn WriteSolverLog>>>,
    /// Termination callback
    term_cb: Option<fn() -> ControlSignal>,
}

impl<PBE, CE, VM> PMinimal<PBE, CE, VM, fn(Assignment) -> Clause, DefIncSolver<'static, '_>>
where
    PBE: pb::IncUB,
    CE: card::IncUB,
    VM: ManageVars,
{
    /// Initializes a default solver
    pub fn default_init(inst: MultiOptInstance<VM>) -> Self {
        Self::init_with_options(inst, Options::default(), default_blocking_clause)
    }

    /// Initializes a default solver with options
    pub fn default_init_with_options(inst: MultiOptInstance<VM>, opts: Options) -> Self {
        Self::init_with_options(inst, opts, default_blocking_clause)
    }
}

impl<PBE, CE, VM, BCG, O> Solve<VM, BCG> for PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: pb::IncUB,
    CE: card::IncUB,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: IncrementalSolve + Default + Terminate<'static>,
{
    fn init_with_options(inst: MultiOptInstance<VM>, opts: Options, block_clause_gen: BCG) -> Self {
        let (constr, objs) = inst.decompose();
        let (cnf, var_manager) = constr.as_cnf();
        let mut solver = PMinimal {
            oracle: O::default(),
            var_manager,
            obj_encs: vec![],
            obj_clauses: vec![],
            blits: RsHashMap::default(),
            obj_lit_data: RsHashMap::default(),
            max_orig_var: var![0],
            block_clause_gen,
            pareto_front: ParetoFront::new(),
            opts,
            stats: Stats::default(),
            lims: Limits::none(),
            loggers: vec![],
            term_cb: None,
        };
        solver.init(cnf, objs);
        solver
    }

    fn solve(&mut self, limits: Limits) -> Result<(), Termination> {
        self.lims = limits;
        self.alg_main()
    }

    fn pareto_front(&self) -> ParetoFront {
        self.pareto_front.clone()
    }

    fn stats(&self) -> Stats {
        self.stats
    }

    type LoggerId = usize;

    fn attach_logger(&mut self, boxed_logger: Box<dyn WriteSolverLog>) -> Self::LoggerId {
        if let Some((idx, opt_logger)) = self
            .loggers
            .iter_mut()
            .enumerate()
            .find(|(_, opt_logger)| opt_logger.is_none())
        {
            *opt_logger = Some(boxed_logger);
            return idx;
        }
        self.loggers.push(Some(boxed_logger));
        self.loggers.len() - 1
    }

    fn detach_logger(&mut self, id: Self::LoggerId) -> Option<Box<dyn WriteSolverLog>> {
        if id >= self.loggers.len() {
            None
        } else {
            self.loggers[id].take()
        }
    }

    fn attach_terminator(&mut self, term_cb: fn() -> ControlSignal) {
        self.term_cb = Some(term_cb);
        self.oracle.attach_terminator(term_cb);
    }

    fn detach_terminator(&mut self) {
        self.term_cb = None;
    }
}

impl<PBE, CE, VM, BCG, O> ExtendedSolveStats for PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: pb::IncUB + encodings::EncodeStats,
    CE: card::IncUB + encodings::EncodeStats,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: IncrementalSolve + SolveStats + Default + Terminate<'static>,
{
    fn oracle_stats(&self) -> OracleStats {
        OracleStats {
            n_sat_solves: self.oracle.n_sat_solves(),
            n_unsat_solves: self.oracle.n_unsat_solves(),
            n_clauses: self.oracle.n_clauses(),
            n_vars: self.oracle.n_vars(),
            avg_clause_len: self.oracle.avg_clause_len(),
            cpu_solve_time: self.oracle.cpu_solve_time(),
        }
    }

    fn encoding_stats(&self) -> Vec<EncodingStats> {
        self.obj_encs
            .iter()
            .map(|obj_enc| match obj_enc {
                ObjEncoding::Weighted { encoding, offset } => EncodingStats {
                    n_clauses: encoding.n_clauses(),
                    n_vars: encoding.n_vars(),
                    offset: *offset,
                    unit_weight: None,
                },
                ObjEncoding::Unweighted {
                    encoding,
                    offset,
                    unit_weight,
                } => EncodingStats {
                    n_clauses: encoding.n_clauses(),
                    n_vars: encoding.n_vars(),
                    offset: *offset,
                    unit_weight: Some(*unit_weight),
                },
            })
            .collect()
    }
}

/// Initializes a solver with the default settings

impl<PBE, CE, VM, BCG, O> PMinimal<PBE, CE, VM, BCG, O>
where
    PBE: pb::IncUB,
    CE: card::IncUB,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: IncrementalSolve + Default + Terminate<'static>,
{
    /// Initializes the solver
    fn init(&mut self, mut cnf: CNF, objs: Vec<Objective>) {
        self.stats.n_objs = objs.len();
        self.obj_encs.reserve_exact(objs.len());
        // Add objectives to solver
        let mut obj_cnf = CNF::new();
        objs.into_iter()
            .for_each(|obj| obj_cnf.extend(self.add_objective(obj)));
        // Store objective clauses
        cnf.iter().for_each(|cl| {
            let is_obj_cl =
                cl.iter()
                    .fold(false, |is_obj_cl, l| match self.obj_lit_data.get_mut(l) {
                        Some(lit_data) => {
                            // Track occurrences of objective literals
                            lit_data.clauses.push(self.obj_clauses.len());
                            true
                        }
                        None => is_obj_cl,
                    });
            if is_obj_cl {
                // Save copy of clause that contains objective literal
                self.obj_clauses.push(cl.clone());
            }
        });
        // Add hard clauses and relaxed soft clauses to oracle
        cnf.extend(obj_cnf);
        self.max_orig_var = self
            .var_manager
            .max_var()
            .expect("No variables in instance");
        self.oracle.reserve(self.max_orig_var).unwrap();
        self.oracle.add_cnf(cnf).unwrap();
    }

    /// The solving algorithm main routine. This will never return [`Ok`] but
    /// Result is used as a return type to be able to use `?` syntax for
    /// termination from subroutines.
    fn alg_main(&mut self) -> Result<(), Termination> {
        debug_assert_eq!(self.obj_encs.len(), self.stats.n_objs);
        loop {
            // Find minimization starting point
            let res = self.oracle.solve().unwrap();
            self.log_oracle_call(res, Phase::OuterLoop)?;
            if res == SolverResult::UNSAT {
                return Ok(());
            }
            debug_assert_eq!(res, SolverResult::SAT);
            self.check_terminator()?;

            // Minimize solution
            let (costs, solution) = self.get_solution_and_internal_costs(Phase::OuterLoop)?;
            self.log_candidate(&costs, Phase::OuterLoop)?;
            self.check_terminator()?;
            let (costs, solution, block_switch) = self.p_minimization(costs, solution)?;

            self.enumerate_at_pareto_point(costs, solution)?;

            // Block last Pareto point, if temporarily blocked
            if let Some(block_lit) = block_switch {
                self.oracle.add_unit(block_lit).unwrap();
            }
        }
    }

    /// Executes P-minimization from a cost and solution starting point
    fn p_minimization(
        &mut self,
        mut costs: Vec<usize>,
        mut solution: Assignment,
    ) -> Result<(Vec<usize>, Assignment, Option<Lit>), Termination> {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        let mut block_switch = None;
        loop {
            // Force next solution to dominate the current one
            let mut assumps = self.enforce_dominating(&costs);
            // Block solutions dominated by the current one
            if self.opts.max_sols_per_pp == Some(1) {
                // Block permanently since no enumeration at Pareto point
                let block_clause = self.dominated_block_clause(&costs);
                self.oracle.add_clause(block_clause).unwrap();
            } else {
                // Permanently block last candidate
                if let Some(block_lit) = block_switch {
                    self.oracle.add_unit(block_lit).unwrap();
                }
                // Temporarily block to allow for enumeration at Pareto point
                let block_lit = self.tmp_block_dominated(&costs);
                block_switch = Some(block_lit);
                assumps.push(block_lit);
            }

            // Check if dominating solution exists
            let res = self.oracle.solve_assumps(assumps).unwrap();
            debug_assert_ne!(res, SolverResult::Interrupted);
            self.log_oracle_call(res, Phase::Minimization)?;
            if res == SolverResult::UNSAT {
                // Termination criteria, return last solution and costs
                return Ok((costs, solution, block_switch));
            }
            self.check_terminator()?;

            (costs, solution) = self.get_solution_and_internal_costs(Phase::Minimization)?;
            self.log_candidate(&costs, Phase::Minimization)?;
            self.check_terminator()?;
        }
    }

    /// Enumerates solutions at a Pareto point
    fn enumerate_at_pareto_point(
        &mut self,
        costs: Vec<usize>,
        mut solution: Assignment,
    ) -> Result<(), Termination> {
        debug_assert_eq!(costs.len(), self.stats.n_objs);

        // Assumptions to enforce staying at the Pareto point
        let assumps = self.enforce_dominating(&costs);

        // Create Pareto point
        let mut pareto_point = ParetoPoint::new(self.externalize_internal_costs(costs));

        loop {
            // TODO: add debug assert checking solution cost
            pareto_point.add_sol(solution.clone());
            match self.log_solution() {
                Ok(_) => (),
                Err(term) => {
                    let pp_term = self.log_pareto_point(&pareto_point);
                    self.pareto_front.add_pp(pareto_point);
                    pp_term?;
                    return Err(term);
                }
            }
            if let Some(max_pp_sols) = self.opts.max_sols_per_pp {
                if max_pp_sols >= pareto_point.n_sols() {
                    let pp_term = self.log_pareto_point(&pareto_point);
                    self.pareto_front.add_pp(pareto_point);
                    return pp_term;
                }
            }
            self.check_terminator()?;

            // Block last solution
            self.oracle
                .add_clause((self.block_clause_gen)(solution))
                .unwrap();

            // Find next solution
            let res = self.oracle.solve_assumps(assumps.clone()).unwrap();
            debug_assert_ne!(res, SolverResult::Interrupted);
            self.log_oracle_call(res, Phase::Enumeration)?;
            if res == SolverResult::UNSAT {
                // All solutions enumerated
                self.pareto_front.add_pp(pareto_point);
                return Ok(());
            }
            self.check_terminator()?;
            solution = self.oracle.solution(self.max_orig_var).unwrap();
        }
    }

    /// Gets the current objective costs without offset or multiplier. The phase
    /// parameter is needed to determine if the solution should be heuristically
    /// improved.
    fn get_solution_and_internal_costs(
        &mut self,
        phase: Phase,
    ) -> Result<(Vec<usize>, Assignment), Termination> {
        let mut costs = Vec::new();
        costs.resize(self.stats.n_objs, 0);
        let mut sol = self.oracle.solution(self.max_orig_var).unwrap();
        let tightening = self
            .opts
            .heuristic_improvements
            .solution_tightening
            .wanted(phase);
        let learning = self
            .opts
            .heuristic_improvements
            .tightening_clauses
            .wanted(phase);
        let costs = (0..self.obj_encs.len())
            .map(|idx| {
                self.get_cost_with_heuristic_improvements(idx, &mut sol, tightening, learning)
            })
            .collect::<Result<Vec<usize>, _>>()?;
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        Ok((costs, sol))
    }

    /// Performs heuristic solution improvement and computes the improved
    /// (internal) cost for one objective
    fn get_cost_with_heuristic_improvements(
        &mut self,
        obj_idx: usize,
        sol: &mut Assignment,
        tightening: bool,
        learning: bool,
    ) -> Result<usize, Termination> {
        debug_assert!(obj_idx < self.stats.n_objs);
        let mut reduction = 0;
        let mut learned_cnf = CNF::new();
        let cost = self.obj_encs[obj_idx].iter().fold(0, |cst, (l, w)| {
            if let Some(val) = sol.lit_value(l) {
                if val == TernaryVal::True {
                    if (tightening || learning) && !self.obj_lit_data.contains_key(&!l) {
                        // If tightening or learning and the negated literal
                        // does not appear in any objective
                        if let Some(witness) = self.find_flip_witness(l, sol) {
                            // Has a witness -> literal can be flipped or clause learned
                            if learning {
                                // Create learned clause from flip witness
                                let mut learned_clause =
                                    Clause::from_iter(witness.into_iter().map(Lit::not));
                                learned_clause.add(!l);
                                learned_cnf.add_clause(learned_clause);
                            }
                            if tightening {
                                // Flip literal
                                sol.assign_lit(!l);
                                reduction += w;
                                cst
                            } else {
                                cst + w
                            }
                        } else {
                            cst + w
                        }
                    } else {
                        cst + w
                    }
                } else {
                    cst
                }
            } else {
                cst
            }
        });
        if tightening || learning {
            self.log_heuristic_obj_improvement(obj_idx, cost + reduction, cost, learned_cnf.len())?;
        }
        self.oracle.add_cnf(learned_cnf).unwrap();
        Ok(cost)
    }

    /// Finds witness that allows flipping a given literal. A witness here is a
    /// subset of the solution that satisfies all clauses in which lit appears.
    /// This assumes that flipping the literal will not make the solution worse.
    fn find_flip_witness(&self, lit: Lit, sol: &Assignment) -> Option<RsHashSet<Lit>> {
        debug_assert!(self.obj_lit_data.contains_key(&lit));
        let lit_data = self.obj_lit_data.get(&lit).unwrap();
        lit_data
            .clauses
            .iter()
            .fold(Some(RsHashSet::default()), |witness, cl_idx| {
                if let Some(mut witness) = witness {
                    if let Some(other) =
                        self.obj_clauses[*cl_idx]
                            .iter()
                            .fold(None, |sat_lit, other| {
                                if sat_lit.is_some() || *other == lit {
                                    sat_lit
                                } else if sol.lit_value(*other).unwrap() == TernaryVal::True {
                                    Some(*other)
                                } else {
                                    sat_lit
                                }
                            })
                    {
                        witness.insert(other);
                        Some(witness)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
    }

    /// Converts an internal cost vector to an external one. Internal cost is
    /// purely the encoding output while external cost takes an offset and
    /// multiplier into account.
    fn externalize_internal_costs(&self, costs: Vec<usize>) -> Vec<isize> {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        costs
            .into_iter()
            .enumerate()
            .map(|(idx, cst)| match self.obj_encs[idx] {
                ObjEncoding::Weighted { offset, .. } => {
                    let signed_cst: isize = cst.try_into().expect("cost exceeds `isize`");
                    signed_cst + offset
                }
                ObjEncoding::Unweighted {
                    offset,
                    unit_weight,
                    ..
                } => {
                    let signed_mult_cost: isize = (cst * unit_weight)
                        .try_into()
                        .expect("multiplied cost exceeds `isize`");
                    signed_mult_cost + offset
                }
            })
            .collect()
    }

    /// Gets assumptions to enforce that the next solution dominates the given
    /// cost point.
    fn enforce_dominating(&mut self, costs: &Vec<usize>) -> Vec<Lit> {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        let mut assumps = vec![];
        costs.iter().enumerate().for_each(|(idx, &cst)| {
            match &mut self.obj_encs[idx] {
                ObjEncoding::Weighted { encoding, .. } => {
                    // Encode and add to solver
                    self.oracle
                        .add_cnf(
                            encoding
                                .encode_ub_change(cst, cst, &mut self.var_manager)
                                .unwrap(),
                        )
                        .unwrap();
                    // Extend assumptions
                    assumps.extend(encoding.enforce_ub(cst).unwrap());
                }
                ObjEncoding::Unweighted { encoding, .. } => {
                    // Encode and add to solver
                    self.oracle
                        .add_cnf(
                            encoding
                                .encode_ub_change(cst, cst, &mut self.var_manager)
                                .unwrap(),
                        )
                        .unwrap();
                    // Extend assumptions
                    assumps.extend(encoding.enforce_ub(cst).unwrap());
                }
            }
        });
        assumps
    }

    /// Temporarily blocks solutions dominated by the given cost point. Returns
    /// and assumption that needs to be enforced in order for the blocking to be
    /// enforced.
    fn tmp_block_dominated(&mut self, costs: &Vec<usize>) -> Lit {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        let mut clause = self.dominated_block_clause(costs);
        let block_lit = self.var_manager.new_var().pos_lit();
        clause.add(block_lit);
        self.oracle.add_clause(clause).unwrap();
        !block_lit
    }

    /// Gets a clause blocking solutions dominated by the given cost point.
    fn dominated_block_clause(&mut self, costs: &Vec<usize>) -> Clause {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        let mut clause = Clause::new();
        costs.iter().enumerate().for_each(|(idx, &cst)| {
            // Don't block
            if cst == 0 {
                return;
            }
            match &mut self.obj_encs[idx] {
                ObjEncoding::Weighted { encoding, .. } => {
                    // Encode and add to solver
                    self.oracle
                        .add_cnf(
                            encoding
                                .encode_ub_change(cst - 1, cst - 1, &mut self.var_manager)
                                .unwrap(),
                        )
                        .unwrap();
                    // Add one enforcing assumption to clause
                    let assumps = encoding.enforce_ub(cst - 1).unwrap();
                    if assumps.len() == 1 {
                        clause.add(assumps[0]);
                    } else {
                        let mut and_impl = CNF::new();
                        let and_lit = self.var_manager.new_var().pos_lit();
                        and_impl.add_lit_impl_cube(and_lit, assumps);
                        self.oracle.add_cnf(and_impl).unwrap();
                        clause.add(and_lit);
                    }
                }
                ObjEncoding::Unweighted { encoding, .. } => {
                    // Encode and add to solver
                    self.oracle
                        .add_cnf(
                            encoding
                                .encode_ub_change(cst - 1, cst - 1, &mut self.var_manager)
                                .unwrap(),
                        )
                        .unwrap();
                    // Add one enforcing assumption to clause
                    let assumps = encoding.enforce_ub(cst - 1).unwrap();
                    if assumps.len() == 1 {
                        clause.add(assumps[0]);
                    } else {
                        let mut and_impl = CNF::new();
                        let and_lit = self.var_manager.new_var().pos_lit();
                        and_impl.add_lit_impl_cube(and_lit, assumps);
                        self.oracle.add_cnf(and_impl).unwrap();
                        clause.add(and_lit);
                    }
                }
            }
        });
        clause
    }

    /// Checks the termination callback and terminates if appropriate
    fn check_terminator(&mut self) -> Result<(), Termination> {
        if let Some(cb) = &mut self.term_cb {
            if cb() == ControlSignal::Terminate {
                return Err(Termination::Callback);
            }
        }
        Ok(())
    }

    /// Logs a cost point candidate. Can error a termination if the candidates limit is reached.
    fn log_candidate(&mut self, costs: &Vec<usize>, phase: Phase) -> Result<(), Termination> {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        self.stats.n_candidates += 1;
        // Dispatch to loggers
        if let Err(log_err) =
            self.loggers
                .iter_mut()
                .fold(Ok(()), |res: Result<(), LoggerError>, opt_logger| {
                    if res.is_ok() {
                        if let Some(logger) = opt_logger {
                            logger.log_candidate(costs, phase)?
                        }
                        Ok(())
                    } else {
                        res
                    }
                })
        {
            return Err(Termination::LoggerError(log_err));
        }
        // Update limit and check termination
        if let Some(candidates) = &mut self.lims.candidates {
            *candidates -= 1;
            if *candidates == 0 {
                return Err(Termination::CandidatesLimit);
            }
        }
        Ok(())
    }

    /// Logs an oracle call. Can return a termination if the oracle call limit is reached.
    fn log_oracle_call(&mut self, result: SolverResult, phase: Phase) -> Result<(), Termination> {
        self.stats.n_oracle_calls += 1;
        // Dispatch to loggers
        if let Err(log_err) =
            self.loggers
                .iter_mut()
                .fold(Ok(()), |res: Result<(), LoggerError>, opt_logger| {
                    if res.is_ok() {
                        if let Some(logger) = opt_logger {
                            logger.log_oracle_call(result, phase)?
                        }
                        Ok(())
                    } else {
                        res
                    }
                })
        {
            return Err(Termination::LoggerError(log_err));
        }
        // Update limit and check termination
        if let Some(oracle_calls) = &mut self.lims.oracle_calls {
            *oracle_calls -= 1;
            if *oracle_calls == 0 {
                return Err(Termination::OracleCallsLimit);
            }
        }
        Ok(())
    }

    /// Logs a solution. Can return a termination if the solution limit is reached.
    fn log_solution(&mut self) -> Result<(), Termination> {
        self.stats.n_solutions += 1;
        // Dispatch to loggers
        if let Err(log_err) =
            self.loggers
                .iter_mut()
                .fold(Ok(()), |res: Result<(), LoggerError>, opt_logger| {
                    if res.is_ok() {
                        if let Some(logger) = opt_logger {
                            logger.log_solution()?
                        }
                        Ok(())
                    } else {
                        res
                    }
                })
        {
            return Err(Termination::LoggerError(log_err));
        }
        // Update limit and check termination
        if let Some(solutions) = &mut self.lims.sols {
            *solutions -= 1;
            if *solutions == 0 {
                return Err(Termination::SolsLimit);
            }
        }
        Ok(())
    }

    /// Logs a Pareto point. Can return a termination if the Pareto point limit is reached.
    fn log_pareto_point(&mut self, pareto_point: &ParetoPoint) -> Result<(), Termination> {
        self.stats.n_pareto_points += 1;
        // Dispatch to loggers
        if let Err(log_err) =
            self.loggers
                .iter_mut()
                .fold(Ok(()), |res: Result<(), LoggerError>, opt_logger| {
                    if res.is_ok() {
                        if let Some(logger) = opt_logger {
                            logger.log_pareto_point(pareto_point)?
                        }
                        Ok(())
                    } else {
                        res
                    }
                })
        {
            return Err(Termination::LoggerError(log_err));
        }
        // Update limit and check termination
        if let Some(pps) = &mut self.lims.pps {
            *pps -= 1;
            if *pps == 0 {
                return Err(Termination::PPLimit);
            }
        }
        Ok(())
    }

    /// Logs a heuristic objective improvement. Can return a logger error.
    fn log_heuristic_obj_improvement(
        &mut self,
        obj_idx: usize,
        apparent_cost: usize,
        improved_cost: usize,
        learned_clauses: usize,
    ) -> Result<(), Termination> {
        self.stats.n_pareto_points += 1;
        // Dispatch to loggers
        if let Err(log_err) =
            self.loggers
                .iter_mut()
                .fold(Ok(()), |res: Result<(), LoggerError>, opt_logger| {
                    if res.is_ok() {
                        if let Some(logger) = opt_logger {
                            logger.log_heuristic_obj_improvement(
                                obj_idx,
                                apparent_cost,
                                improved_cost,
                                learned_clauses,
                            )?
                        }
                        Ok(())
                    } else {
                        res
                    }
                })
        {
            return Err(Termination::LoggerError(log_err));
        }
        Ok(())
    }

    /// Adds a new objective to the solver. This shall only be called during
    /// initialization.
    fn add_objective(&mut self, obj: Objective) -> CNF {
        let mut cnf = CNF::new();
        if obj.weighted() {
            // Add weighted objective
            let (soft_cl, offset) = obj.as_soft_cls();
            let lits: RsHashMap<Lit, usize> = soft_cl
                .into_iter()
                .map(|(cl, w)| {
                    let (olit, opt_cls_info) = self.add_soft_clause(cl);
                    // Track the objective index for the objective literal
                    match self.obj_lit_data.get_mut(&olit) {
                        Some(data) => data.objs.push(self.obj_encs.len()),
                        None => {
                            self.obj_lit_data.insert(
                                olit,
                                ObjLitData {
                                    objs: vec![self.obj_encs.len()],
                                    clauses: vec![],
                                },
                            );
                        }
                    };
                    // Add hard clause to CNF and track olit appearance
                    if let Some((cls_idx, hard_cl)) = opt_cls_info {
                        cnf.add_clause(hard_cl);
                        if self.opts.heuristic_improvements.must_store_clauses() {
                            self.obj_lit_data
                                .get_mut(&olit)
                                .unwrap()
                                .clauses
                                .push(cls_idx);
                        }
                    };
                    (olit, w)
                })
                .collect();
            // Initialize encoder for objective
            self.obj_encs.push(ObjEncoding::new_weighted(
                lits,
                offset,
                self.opts.reserve_enc_vars,
                &mut self.var_manager,
            ));
        } else {
            // Add unweighted objective
            let (soft_cl, unit_weight, offset) = obj.as_unweighted_soft_cls();
            let lits: Vec<Lit> = soft_cl
                .into_iter()
                .map(|cl| {
                    let (olit, opt_cls_info) = self.add_soft_clause(cl);
                    // Track the objective index for the objective literal
                    match self.obj_lit_data.get_mut(&olit) {
                        Some(data) => data.objs.push(self.obj_encs.len()),
                        None => {
                            self.obj_lit_data.insert(
                                olit,
                                ObjLitData {
                                    objs: vec![self.obj_encs.len()],
                                    clauses: vec![],
                                },
                            );
                        }
                    };
                    // Add hard clause to CNF and track olit appearance
                    if let Some((cls_idx, hard_cl)) = opt_cls_info {
                        cnf.add_clause(hard_cl);
                        if self.opts.heuristic_improvements.must_store_clauses() {
                            self.obj_lit_data
                                .get_mut(&olit)
                                .unwrap()
                                .clauses
                                .push(cls_idx);
                        }
                    };
                    olit
                })
                .collect();
            // Initialize encoder for objective
            self.obj_encs.push(ObjEncoding::new_unweighted(
                lits,
                offset,
                unit_weight,
                self.opts.reserve_enc_vars,
                &mut self.var_manager,
            ));
        }
        cnf
    }

    /// Adds a soft clause to the solver, returns an objective literal. If the
    /// clause has been newly relaxed, also returns the index of the clause in
    /// [`PMinimal::obj_clauses`] as well as the relaxed clause to be added to
    /// the oracle.
    fn add_soft_clause(&mut self, mut cls: Clause) -> (Lit, Option<(usize, Clause)>) {
        if cls.len() == 1 {
            // No blit needed
            return (cls[0], None);
        }
        if self.blits.contains_key(&cls) {
            // Reuse clause with blit that was already added
            let blit = self.blits[&cls];
            return (blit, None);
        }
        // Get new blit
        let blit = self.var_manager.new_var().pos_lit();
        // Save blit in case same soft clause reappears
        // TODO: find way to not have to clone the clause here
        self.blits.insert(cls.clone(), blit);
        if self.opts.heuristic_improvements.must_store_clauses() {
            // Add clause to the saved objective clauses
            self.obj_clauses.push(cls.clone());
        }
        // Relax clause and return so that it is added to the oracle
        cls.add(blit);
        (blit, Some((self.obj_clauses.len() - 1, cls)))
    }
}

/// Data regarding an objective literal
struct ObjLitData {
    /// Objectives that the literal appears in
    objs: Vec<usize>,
    /// Clauses that the literal appears in. The entries are indices in
    /// [`PMinimal::obj_clauses`]. Only populated when using model tightening.
    clauses: Vec<usize>,
}

/// Internal data associated with an objective
enum ObjEncoding<PBE, CE>
where
    PBE: pb::IncUB,
    CE: card::IncUB,
{
    Weighted {
        offset: isize,
        encoding: PBE,
    },
    Unweighted {
        offset: isize,
        unit_weight: usize,
        encoding: CE,
    },
}

impl<PBE, CE> ObjEncoding<PBE, CE>
where
    PBE: pb::IncUB,
    CE: card::IncUB,
{
    /// Initializes a new objective encoding for a weighted objective
    fn new_weighted<VM: ManageVars>(
        lits: RsHashMap<Lit, usize>,
        offset: isize,
        reserve: bool,
        var_manager: &mut VM,
    ) -> Self {
        let mut encoding = PBE::from_iter(lits);
        if reserve {
            encoding.reserve(var_manager);
        }
        ObjEncoding::Weighted { offset, encoding }
    }

    /// Initializes a new objective encoding for a weighted objective
    fn new_unweighted<VM: ManageVars>(
        lits: Vec<Lit>,
        offset: isize,
        unit_weight: usize,
        reserve: bool,
        var_manager: &mut VM,
    ) -> Self {
        let mut encoding = CE::from_iter(lits);
        if reserve {
            encoding.reserve(var_manager);
        }
        ObjEncoding::Unweighted {
            offset,
            unit_weight,
            encoding,
        }
    }

    /// Unified iterator over encodings
    fn iter(&self) -> ObjEncIter<'_, PBE, CE> {
        match self {
            ObjEncoding::Weighted { encoding, .. } => ObjEncIter::Weighted(encoding.iter()),
            ObjEncoding::Unweighted { encoding, .. } => ObjEncIter::Unweighted(encoding.iter()),
        }
    }
}

enum ObjEncIter<'a, PBE, CE>
where
    PBE: pb::IncUB + 'static,
    CE: card::IncUB + 'static,
{
    Weighted(PBE::Iter<'a>),
    Unweighted(CE::Iter<'a>),
}

impl<PBE, CE> Iterator for ObjEncIter<'_, PBE, CE>
where
    PBE: pb::IncUB,
    CE: card::IncUB,
{
    type Item = (Lit, usize);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ObjEncIter::Weighted(iter) => iter.next(),
            ObjEncIter::Unweighted(iter) => iter.next().map(|l| (l, 1)),
        }
    }
}
