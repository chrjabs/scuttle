//! Core solver functionality shared between different algorithms

use std::{
    marker::PhantomData,
    ops::Not,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};

#[cfg(feature = "interrupt-oracle")]
use std::sync::Mutex;

use anyhow::Context;
use maxpre::MaxPre;
use rustsat::{
    encodings::{card, pb},
    instances::{Cnf, ManageVars},
    solvers::{
        DefaultInitializer, Initialize, SolveIncremental, SolveStats, SolverResult, SolverStats,
    },
    types::{Assignment, Clause, Lit, RsHashMap, TernaryVal, WLitIter},
};
use scuttle_proc::oracle_bounds;

#[cfg(feature = "sol-tightening")]
use maxpre::PreproClauses;

use crate::{
    options::{CoreBoostingOptions, EnumOptions},
    types::{Instance, NonDomPoint, ObjEncoding, ObjLitData, Objective, ParetoFront, VarManager},
    EncodingStats, KernelOptions, Limits, MaybeTerminated,
    MaybeTerminatedError::{self, Done, Error, Terminated},
    Phase, Stats, Termination, WriteSolverLog,
};

pub mod bioptsat;
pub mod lowerbounding;
pub mod pminimal;

mod coreboosting;
mod coreguided;

/// Trait for initializing algorithms
pub trait Init: Sized {
    type Oracle: SolveIncremental;
    type BlockClauseGen: Fn(Assignment) -> Clause;
    type ProofWriter;

    /// Initialization of the algorithm providing all optional input
    fn new<Cls, Objs, Obj>(
        clauses: Cls,
        objs: Objs,
        var_manager: VarManager,
        opts: KernelOptions,
        proof: Option<pidgeons::Proof<Self::ProofWriter>>,
        block_clause_gen: Self::BlockClauseGen,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = Clause>,
        Objs: IntoIterator<Item = (Obj, isize)>,
        Obj: WLitIter;

    /// Initialization of the algorithm using an [`Instance`] rather than iterators
    fn from_instance(
        inst: Instance,
        opts: KernelOptions,
        proof: Option<pidgeons::Proof<Self::ProofWriter>>,
        block_clause_gen: Self::BlockClauseGen,
    ) -> anyhow::Result<Self> {
        Self::new(inst.cnf, inst.objs, inst.vm, opts, proof, block_clause_gen)
    }
}

pub trait InitDefaultBlock: Init<BlockClauseGen = fn(Assignment) -> Clause> {
    /// Initializes the algorithm with the default blocking clause generator
    fn new_default_blocking<Cls, Objs, Obj>(
        clauses: Cls,
        objs: Objs,
        var_manager: VarManager,
        opts: KernelOptions,
        proof: Option<pidgeons::Proof<Self::ProofWriter>>,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = Clause>,
        Objs: IntoIterator<Item = (Obj, isize)>,
        Obj: WLitIter,
    {
        Self::new(
            clauses,
            objs,
            var_manager,
            opts,
            proof,
            default_blocking_clause,
        )
    }

    /// Initializes the algorithm using an [`Instance`] rather than iterators with the default
    /// blocking clause generator
    fn from_instance_default_blocking(
        inst: Instance,
        opts: KernelOptions,
        proof: Option<pidgeons::Proof<Self::ProofWriter>>,
    ) -> anyhow::Result<Self> {
        Self::new(
            inst.cnf,
            inst.objs,
            inst.vm,
            opts,
            proof,
            default_blocking_clause,
        )
    }
}

impl<Alg> InitDefaultBlock for Alg where Alg: Init<BlockClauseGen = fn(Assignment) -> Clause> {}

/// Solving interface for each algorithm
pub trait Solve: KernelFunctions {
    /// Solves the instance under given limits. If not fully solved, returns an
    /// early termination reason.
    fn solve(&mut self, limits: Limits) -> MaybeTerminatedError;
    /// Gets all statistics from the solver
    fn all_stats(&self) -> (Stats, Option<SolverStats>, Option<Vec<EncodingStats>>);
}

/// Core boosting interface
pub trait CoreBoost {
    /// Performs core boosting. Returns false if instance is unsat.    
    fn core_boost(&mut self, opts: CoreBoostingOptions) -> MaybeTerminatedError<bool>;
}

/// Shared functionality provided by the [`SolverKernel`]
pub trait KernelFunctions {
    /// Gets the Pareto front discovered so far
    fn pareto_front(&self) -> ParetoFront;
    /// Gets tracked statistics from the solver
    fn stats(&self) -> Stats;
    /// Attaches a logger to the solver
    fn attach_logger<L: WriteSolverLog + 'static>(&mut self, logger: L);
    /// Detaches a logger from the solver
    fn detach_logger(&mut self) -> Option<Box<dyn WriteSolverLog>>;
    /// Gets an iterrupter to the solver
    fn interrupter(&mut self) -> Interrupter;
}

pub struct Interrupter {
    /// Termination flag of the solver
    term_flag: Arc<AtomicBool>,
    /// The terminator of the underlying SAT oracle
    #[cfg(feature = "interrupt-oracle")]
    oracle_interrupter: Arc<Mutex<Box<dyn rustsat::solvers::InterruptSolver + Send>>>,
}

#[cfg(feature = "interrupt-oracle")]
impl Interrupter {
    /// Interrupts the solver asynchronously
    pub fn interrupt(&mut self) {
        self.term_flag.store(true, Ordering::Relaxed);
        self.oracle_interrupter.lock().unwrap().interrupt();
    }
}

#[cfg(not(feature = "interrupt-oracle"))]
impl Interrupter {
    /// Interrupts the solver asynchronously
    pub fn interrupt(&mut self) {
        self.term_flag.store(true, Ordering::Relaxed);
    }
}

/// Kernel struct shared between all solvers
///
/// # Generics
///
/// - `O`: the SAT solver oracle
/// - `ProofW`: the proof writer
/// - `OInit`: the oracle initializer
/// - `BCG`: the blocking clause generator
struct SolverKernel<O, ProofW, OInit = DefaultInitializer, BCG = fn(Assignment) -> Clause> {
    /// The SAT solver backend
    oracle: O,
    /// The variable manager keeping track of variables
    var_manager: VarManager,
    #[cfg(feature = "sol-tightening")]
    /// Objective literal data
    obj_lit_data: RsHashMap<Lit, ObjLitData>,
    /// The objectives
    objs: Vec<Objective>,
    /// The stored original clauses, if needed
    orig_cnf: Option<Cnf>,
    /// Generator of blocking clauses
    block_clause_gen: BCG,
    /// Configuration options
    opts: KernelOptions,
    /// Running statistics
    stats: Stats,
    /// Limits for the current solving run
    lims: Limits,
    /// An optional inprocessor that has been run at some stage
    inpro: Option<MaxPre>,
    /// Logger to log with
    logger: Option<Box<dyn WriteSolverLog>>,
    /// Termination flag
    term_flag: Arc<AtomicBool>,
    /// The oracle interrupter
    #[cfg(feature = "interrupt-oracle")]
    oracle_interrupter: Arc<Mutex<Box<dyn rustsat::solvers::InterruptSolver + Send>>>,
    /// The VeriPB proof
    proof: Option<pidgeons::Proof<ProofW>>,
    /// Phantom marker for oracle factory
    _factory: PhantomData<OInit>,
}

#[oracle_bounds]
impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG>
where
    O: SolveIncremental,
    OInit: Initialize<O>,
    BCG: Fn(Assignment) -> Clause,
{
    pub fn new<Cls, Objs, Obj>(
        clauses: Cls,
        objs: Objs,
        var_manager: VarManager,
        bcg: BCG,
        proof: Option<pidgeons::Proof<ProofW>>,
        opts: KernelOptions,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = Clause>,
        Objs: IntoIterator<Item = (Obj, isize)>,
        Obj: WLitIter,
    {
        let mut stats = Stats {
            n_objs: 0,
            n_real_objs: 0,
            n_orig_clauses: 0,
            ..Default::default()
        };
        let mut oracle = OInit::init();
        oracle.reserve(var_manager.max_var().unwrap())?;
        let orig_cnf = if opts.store_cnf {
            let cnf: Cnf = clauses.into_iter().collect();
            stats.n_orig_clauses = cnf.len();
            oracle.add_cnf_ref(&cnf)?;
            Some(cnf)
        } else {
            for cl in clauses.into_iter() {
                stats.n_orig_clauses += 1;
                oracle.add_clause(cl)?;
            }
            None
        };
        let objs: Vec<_> = objs
            .into_iter()
            .map(|(wlits, offset)| Objective::new(wlits, offset))
            .collect();
        stats.n_objs = objs.len();
        stats.n_real_objs = objs.iter().fold(0, |cnt, o| {
            if matches!(o, Objective::Constant { .. }) {
                cnt
            } else {
                cnt + 1
            }
        });
        // Record objective literal occurrences
        #[cfg(feature = "sol-tightening")]
        let obj_lit_data = {
            let mut obj_lit_data: RsHashMap<_, ObjLitData> = RsHashMap::default();
            for (idx, obj) in objs.iter().enumerate() {
                match obj {
                    Objective::Weighted { lits, .. } => {
                        for &olit in lits.keys() {
                            match obj_lit_data.get_mut(&olit) {
                                Some(data) => data.objs.push(idx),
                                None => {
                                    obj_lit_data.insert(olit, ObjLitData { objs: vec![idx] });
                                }
                            }
                        }
                    }
                    Objective::Unweighted { lits, .. } => {
                        for &olit in lits {
                            match obj_lit_data.get_mut(&olit) {
                                Some(data) => data.objs.push(idx),
                                None => {
                                    obj_lit_data.insert(olit, ObjLitData { objs: vec![idx] });
                                }
                            }
                        }
                    }
                    Objective::Constant { .. } => (),
                }
            }
            obj_lit_data
        };
        #[cfg(feature = "sol-tightening")]
        // Freeze objective variables so that they are not removed
        for o in &objs {
            for (l, _) in o.iter() {
                oracle.freeze_var(l.var())?;
            }
        }
        #[cfg(feature = "interrupt-oracle")]
        let interrupter = oracle.interrupter();
        Ok(Self {
            oracle,
            var_manager,
            #[cfg(feature = "sol-tightening")]
            obj_lit_data,
            objs,
            orig_cnf,
            block_clause_gen: bcg,
            opts,
            stats,
            lims: Limits::none(),
            inpro: None,
            logger: None,
            term_flag: Arc::new(AtomicBool::new(false)),
            #[cfg(feature = "interrupt-oracle")]
            oracle_interrupter: Arc::new(Mutex::new(Box::new(interrupter))),
            proof,
            _factory: PhantomData,
        })
    }
}

impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG> {
    fn start_solving(&mut self, limits: Limits) {
        self.stats.n_solve_calls += 1;
        self.lims = limits;
    }

    fn attach_logger<L: WriteSolverLog + 'static>(&mut self, logger: L) {
        self.logger = Some(Box::new(logger));
    }

    fn detach_logger(&mut self) -> Option<Box<dyn WriteSolverLog>> {
        self.logger.take()
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
                Objective::Constant { offset } => {
                    debug_assert_eq!(cst, 0);
                    offset
                }
            })
            .collect()
    }

    /// Blocks the current Pareto-MCS by blocking all blocking variables that are set
    fn block_pareto_mcs(&self, sol: Assignment) -> Clause {
        let mut blocking_clause = Clause::new();
        self.objs.iter().for_each(|oe| {
            oe.iter().for_each(|(l, _)| {
                if sol.lit_value(l) == TernaryVal::True {
                    blocking_clause.add(-l)
                }
            })
        });
        blocking_clause
            .normalize()
            .expect("Tautological blocking clause")
    }

    /// Checks the termination flag and terminates if appropriate
    fn check_termination(&self) -> MaybeTerminated {
        if self.term_flag.load(Ordering::Relaxed) {
            MaybeTerminated::Terminated(Termination::Interrupted)
        } else {
            MaybeTerminated::Done(())
        }
    }

    /// Logs a cost point candidate. Can error a termination if the candidates limit is reached.
    fn log_candidate(&mut self, costs: &[usize], phase: Phase) -> MaybeTerminatedError {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        self.stats.n_candidates += 1;
        // Dispatch to logger
        if let Some(logger) = &mut self.logger {
            logger
                .log_candidate(costs, phase)
                .context("logger failed")?;
        }
        // Update limit and check termination
        if let Some(candidates) = &mut self.lims.candidates {
            *candidates -= 1;
            if *candidates == 0 {
                return Terminated(Termination::CandidatesLimit);
            }
        }
        Done(())
    }

    /// Logs an oracle call. Can return a termination if the oracle call limit is reached.
    fn log_oracle_call(&mut self, result: SolverResult) -> MaybeTerminatedError {
        self.stats.n_oracle_calls += 1;
        // Dispatch to logger
        if let Some(logger) = &mut self.logger {
            logger.log_oracle_call(result).context("logger failed")?;
        }
        // Update limit and check termination
        if let Some(oracle_calls) = &mut self.lims.oracle_calls {
            *oracle_calls -= 1;
            if *oracle_calls == 0 {
                return Terminated(Termination::OracleCallsLimit);
            }
        }
        Done(())
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
                return Terminated(Termination::SolsLimit);
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
                return Terminated(Termination::PPLimit);
            }
        }
        Done(())
    }

    #[cfg(feature = "sol-tightening")]
    /// Logs a heuristic objective improvement. Can return a logger error.
    fn log_heuristic_obj_improvement(
        &mut self,
        obj_idx: usize,
        apparent_cost: usize,
        improved_cost: usize,
    ) -> anyhow::Result<()> {
        // Dispatch to logger
        if let Some(logger) = &mut self.logger {
            logger
                .log_heuristic_obj_improvement(obj_idx, apparent_cost, improved_cost)
                .context("logger failed")?;
        }
        Ok(())
    }

    /// Logs a routine start
    fn log_routine_start(&mut self, desc: &'static str) -> anyhow::Result<()> {
        // Dispatch to logger
        if let Some(logger) = &mut self.logger {
            logger.log_routine_start(desc).context("logger failed")?;
        }
        Ok(())
    }

    /// Logs a routine end
    fn log_routine_end(&mut self) -> anyhow::Result<()> {
        // Dispatch to logger
        if let Some(logger) = &mut self.logger {
            logger.log_routine_end().context("logger failed")?;
        }
        Ok(())
    }
}

#[cfg(feature = "interrupt-oracle")]
impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG>
where
    O: rustsat::solvers::Interrupt,
{
    fn interrupter(&mut self) -> Interrupter {
        Interrupter {
            term_flag: self.term_flag.clone(),
            oracle_interrupter: self.oracle_interrupter.clone(),
        }
    }
}

#[cfg(not(feature = "interrupt-oracle"))]
impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG> {
    fn interrupter(&mut self) -> Interrupter {
        Interrupter {
            term_flag: self.term_flag.clone(),
        }
    }
}

#[cfg(feature = "sol-tightening")]
impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG>
where
    O: SolveIncremental + rustsat::solvers::FlipLit,
{
    /// Performs heuristic solution improvement and computes the improved
    /// (internal) cost for one objective
    pub fn get_cost_with_heuristic_improvements(
        &mut self,
        obj_idx: usize,
        sol: &mut Assignment,
        mut tightening: bool,
    ) -> anyhow::Result<usize> {
        debug_assert!(obj_idx < self.stats.n_objs);
        let mut reduction = 0;
        // TODO: iterate over objective literals by weight
        let mut cost = 0;
        let mut used_sol = sol;
        let mut rec_sol;
        if let Some(inpro) = &mut self.inpro {
            // TODO: don't reconstruct every time
            // since tightening is done in the solver, cannot do this with inprocessing
            tightening = false;
            rec_sol = inpro.reconstruct(used_sol.clone());
            used_sol = &mut rec_sol;
        }
        for (l, w) in self.objs[obj_idx].iter() {
            let val = used_sol.lit_value(l);
            if val == TernaryVal::True {
                if tightening && !self.obj_lit_data.contains_key(&!l) {
                    // If tightening and the negated literal does not appear in
                    // any objective
                    if self.oracle.flip_lit(!l)? {
                        used_sol.assign_lit(!l);
                        reduction += w;
                        continue;
                    }
                }
                cost += w;
            }
        }
        if reduction > 0 {
            debug_assert!(tightening);
            // get assignment from the solver again to trigger reconstruction stack
            *used_sol = self.oracle.solution(used_sol.max_var().unwrap())?;
            debug_assert_eq!(
                self.get_cost_with_heuristic_improvements(obj_idx, used_sol, false)?,
                cost
            );
        }
        if tightening {
            self.log_heuristic_obj_improvement(obj_idx, cost + reduction, cost)?;
        }
        Ok(cost)
    }
}

#[cfg(not(feature = "sol-tightening"))]
impl<O, ProofW, OInit, BCG, ProofW> SolverKernel<O, ProofW, OInit, BCG>
where
    O: SolveIncremental,
{
    /// Performs heuristic solution improvement and computes the improved
    /// (internal) cost for one objective
    fn get_cost_with_heuristic_improvements(
        &mut self,
        obj_idx: usize,
        sol: &mut Assignment,
        _tightening: bool,
    ) -> anyhow::Result<usize> {
        debug_assert!(obj_idx < self.stats.n_objs);
        let mut cost = 0;
        for (l, w) in self.objs[obj_idx].iter() {
            let val = sol.lit_value(l);
            if val == TernaryVal::True {
                cost += w;
            }
        }
        Ok(cost)
    }
}

#[cfg(feature = "phasing")]
impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG>
where
    O: rustsat::solvers::PhaseLit,
{
    /// If solution-guided search is turned on, phases the entire solution in
    /// the oracle
    fn phase_solution(&mut self, solution: Assignment) -> anyhow::Result<()> {
        if !self.opts.solution_guided_search {
            return Ok(());
        }
        for lit in solution.into_iter() {
            self.oracle.phase_lit(lit)?;
        }
        Ok(())
    }

    /// If solution-guided search is turned on, unphases every variable in the
    /// solver
    fn unphase_solution(&mut self) -> anyhow::Result<()> {
        if !self.opts.solution_guided_search {
            return Ok(());
        }
        for idx in 0..self.var_manager.max_var().unwrap().idx32() + 1 {
            self.oracle.unphase_var(rustsat::var![idx])?;
        }
        Ok(())
    }
}

#[cfg(not(feature = "phasing"))]
impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG> {
    /// If solution-guided search is turned on, phases the entire solution in
    /// the oracle
    fn phase_solution(&mut self, _solution: Assignment) -> anyhow::Result<()> {
        Ok(())
    }

    /// If solution-guided search is turned on, unphases every variable in the
    /// solver
    fn unphase_solution(&mut self) -> anyhow::Result<()> {
        Ok(())
    }
}

#[oracle_bounds]
impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG>
where
    O: SolveIncremental,
    BCG: Fn(Assignment) -> Clause,
{
    /// Yields Pareto-optimal solutions. The given assumptions must only allow
    /// for solutions at the non-dominated point with given cost. If the options
    /// ask for enumeration, will enumerate all solutions at this point.
    fn yield_solutions<Col: Extend<NonDomPoint>>(
        &mut self,
        costs: Vec<usize>,
        assumps: &[Lit],
        mut solution: Assignment,
        collector: &mut Col,
    ) -> MaybeTerminatedError {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        self.log_routine_start("yield solutions")?;
        self.unphase_solution()?;

        // Create Pareto point
        let mut non_dominated = NonDomPoint::new(self.externalize_internal_costs(&costs));

        loop {
            debug_assert_eq!(
                (0..self.stats.n_objs)
                    .map(|idx| {
                        self.get_cost_with_heuristic_improvements(idx, &mut solution, false)
                            .unwrap()
                    })
                    .collect::<Vec<_>>(),
                costs
            );

            // Truncate internal solution to only include instance variables
            solution = solution.truncate(self.var_manager.max_orig_var());

            non_dominated.add_sol(solution.clone());
            match self.log_solution() {
                Done(_) => (),
                Terminated(term) => {
                    let nd_term = self.log_non_dominated(&non_dominated);
                    collector.extend([non_dominated]);
                    nd_term?;
                    return Terminated(term);
                }
                Error(err) => {
                    let nd_term = self.log_non_dominated(&non_dominated);
                    collector.extend([non_dominated]);
                    nd_term?;
                    return Error(err);
                }
            }
            if match self.opts.enumeration {
                EnumOptions::NoEnum => true,
                EnumOptions::Solutions(Some(limit)) => non_dominated.n_sols() >= limit,
                EnumOptions::PMCSs(Some(limit)) => non_dominated.n_sols() >= limit,
                _unlimited => false,
            } {
                let pp_term = self.log_non_dominated(&non_dominated);
                collector.extend([non_dominated]);
                self.log_routine_end()?;
                return pp_term;
            }
            self.check_termination()?;

            // Block last solution
            match self.opts.enumeration {
                EnumOptions::Solutions(_) => {
                    self.oracle.add_clause((self.block_clause_gen)(solution))?
                }
                EnumOptions::PMCSs(_) => self.oracle.add_clause(self.block_pareto_mcs(solution))?,
                EnumOptions::NoEnum => panic!("Should never reach this"),
            }

            // Find next solution
            let res = self.solve_assumps(assumps)?;
            if res == SolverResult::Unsat {
                let pp_term = self.log_non_dominated(&non_dominated);
                // All solutions enumerated
                collector.extend([non_dominated]);
                self.log_routine_end()?;
                return pp_term;
            }
            self.check_termination()?;
            solution = self.oracle.solution(self.var_manager.max_var().unwrap())?;
        }
    }
}

#[oracle_bounds]
impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG>
where
    O: SolveIncremental + SolveStats,
    BCG: Fn(Assignment) -> Clause,
{
    /// Performs linear sat-unsat search on a given objective and yields
    /// solutions found at the optimum.
    fn linsu_yield<PBE, CE, Col>(
        &mut self,
        obj_idx: usize,
        encoding: &mut ObjEncoding<PBE, CE>,
        base_assumps: &[Lit],
        upper_bound: Option<(usize, Option<Assignment>)>,
        lower_bound: Option<usize>,
        collector: &mut Col,
    ) -> MaybeTerminatedError<Option<usize>>
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
        Col: Extend<NonDomPoint>,
    {
        let (cost, mut sol) = if let Some(res) =
            self.linsu(obj_idx, encoding, base_assumps, upper_bound, lower_bound)?
        {
            res
        } else {
            // nothing to yield
            return Done(None);
        };
        let costs: Vec<_> = (0..self.stats.n_objs)
            .map(|idx| {
                self.get_cost_with_heuristic_improvements(idx, &mut sol, false)
                    .unwrap()
            })
            .collect();
        debug_assert_eq!(costs[obj_idx], cost);
        // bound obj
        let mut assumps = Vec::from(base_assumps);
        encoding.encode_ub_change(cost..cost + 1, &mut self.oracle, &mut self.var_manager)?;
        assumps.extend(encoding.enforce_ub(cost).unwrap());
        self.yield_solutions(costs, &assumps, sol, collector)?;
        Done(Some(cost))
    }
}

#[oracle_bounds]
impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG>
where
    O: SolveIncremental + SolveStats,
{
    /// Gets the current objective costs without offset or multiplier. The phase
    /// parameter is needed to determine if the solution should be heuristically
    /// improved.
    fn get_solution_and_internal_costs(
        &mut self,
        tightening: bool,
    ) -> anyhow::Result<(Vec<usize>, Assignment)> {
        let mut sol = self.oracle.solution(self.var_manager.max_var().unwrap())?;
        let costs = (0..self.objs.len())
            .map(|idx| self.get_cost_with_heuristic_improvements(idx, &mut sol, tightening))
            .collect::<Result<Vec<usize>, _>>()?;
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        Ok((costs, sol))
    }

    /// Performs linear sat-unsat search on a given objective.
    fn linsu<PBE, CE>(
        &mut self,
        obj_idx: usize,
        encoding: &mut ObjEncoding<PBE, CE>,
        base_assumps: &[Lit],
        upper_bound: Option<(usize, Option<Assignment>)>,
        lower_bound: Option<usize>,
    ) -> MaybeTerminatedError<Option<(usize, Assignment)>>
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
    {
        self.log_routine_start("linsu")?;

        let lower_bound = lower_bound.unwrap_or(0);

        let mut assumps = Vec::from(base_assumps);
        let (mut cost, mut sol) = if let Some(bound) = upper_bound {
            bound
        } else {
            let res = self.solve_assumps(&assumps)?;
            if res == SolverResult::Unsat {
                self.log_routine_end()?;
                return Done(None);
            }
            let mut sol = self.oracle.solution(self.var_manager.max_orig_var())?;
            let cost = self.get_cost_with_heuristic_improvements(obj_idx, &mut sol, true)?;
            (cost, Some(sol))
        };
        #[cfg(feature = "coarse-convergence")]
        let mut coarse = true;
        while cost > lower_bound {
            let bound = '_bound: {
                #[cfg(feature = "coarse-convergence")]
                if coarse {
                    break '_bound encoding.coarse_ub(cost - 1);
                }
                cost - 1
            };
            assumps.drain(base_assumps.len()..);
            encoding.encode_ub_change(bound..bound + 1, &mut self.oracle, &mut self.var_manager)?;
            assumps.extend(encoding.enforce_ub(bound).unwrap());
            match self.solve_assumps(&assumps)? {
                SolverResult::Sat => {
                    let mut thissol = self.oracle.solution(self.var_manager.max_orig_var())?;
                    let new_cost =
                        self.get_cost_with_heuristic_improvements(obj_idx, &mut thissol, false)?;
                    debug_assert!(new_cost < cost);
                    let costs: Vec<_> = (0..self.stats.n_objs)
                        .map(|oidx| {
                            self.get_cost_with_heuristic_improvements(oidx, &mut thissol, false)
                                .unwrap()
                        })
                        .collect();
                    self.log_candidate(&costs, Phase::Linsu)?;
                    sol = Some(thissol);
                    cost = new_cost;
                    if cost == lower_bound {
                        self.log_routine_end()?;
                        return Done(Some((cost, sol.unwrap())));
                    }
                }
                SolverResult::Unsat => {
                    #[cfg(feature = "coarse-convergence")]
                    if bound + 1 < cost {
                        coarse = false;
                        continue;
                    }
                    break;
                }
                _ => unreachable!(),
            }
        }
        // make sure to have a solution
        if sol.is_none() {
            encoding.encode_ub_change(cost..cost + 1, &mut self.oracle, &mut self.var_manager)?;
            assumps.extend(encoding.enforce_ub(cost).unwrap());
            let res = self.solve_assumps(&assumps)?;
            debug_assert_eq!(res, SolverResult::Sat);
            sol = Some(self.oracle.solution(self.var_manager.max_orig_var())?);
        }
        self.log_routine_end()?;
        Done(Some((cost, sol.unwrap())))
    }
}

impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG>
where
    O: SolveIncremental,
{
    /// Wrapper around the oracle with call logging and interrupt detection.
    /// Assumes that the oracle is unlimited.
    fn solve(&mut self) -> MaybeTerminatedError<SolverResult> {
        self.log_routine_start("oracle call")?;
        let res = self.oracle.solve()?;
        self.log_routine_end()?;
        self.check_termination()?;
        self.log_oracle_call(res)?;
        Done(res)
    }

    /// Wrapper around the oracle with call logging and interrupt detection.
    /// Assumes that the oracle is unlimited.
    fn solve_assumps(&mut self, assumps: &[Lit]) -> MaybeTerminatedError<SolverResult> {
        self.log_routine_start("oracle call")?;
        let res = self.oracle.solve_assumps(assumps)?;
        self.log_routine_end()?;
        self.check_termination()?;
        self.log_oracle_call(res)?;
        Done(res)
    }
}

#[oracle_bounds]
impl<O, ProofW, OInit, BCG> SolverKernel<O, ProofW, OInit, BCG>
where
    O: SolveIncremental,
    OInit: Initialize<O>,
{
    /// Resets the oracle and returns an error when the original [`Cnf`] was not stored.
    fn reset_oracle(&mut self, include_var_manager: bool) -> anyhow::Result<()> {
        anyhow::ensure!(
            self.opts.store_cnf,
            "cannot reset oracle without having stored the CNF"
        );
        self.log_routine_start("reset-oracle")?;
        self.oracle = OInit::init();
        if include_var_manager {
            self.oracle.reserve(self.var_manager.max_enc_var())?;
        } else {
            self.oracle.reserve(self.var_manager.max_var().unwrap())?;
        }
        self.oracle.add_cnf(self.orig_cnf.clone().unwrap())?;
        #[cfg(feature = "interrupt-oracle")]
        {
            *self.oracle_interrupter.lock().unwrap() = Box::new(self.oracle.interrupter());
        }
        #[cfg(feature = "sol-tightening")]
        // Freeze objective variables so that they are not removed
        for o in &self.objs {
            for (l, _) in o.iter() {
                self.oracle.freeze_var(l.var())?;
            }
        }
        if include_var_manager {
            self.var_manager
                .forget_from(self.var_manager.max_enc_var() + 1);
        }
        self.log_routine_end()?;
        Ok(())
    }
}

/// The default blocking clause generator
pub fn default_blocking_clause(sol: Assignment) -> Clause {
    Clause::from_iter(sol.into_iter().map(Lit::not))
}
