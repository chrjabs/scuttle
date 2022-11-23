//! # $P$-Minimal Model Enumeration for Multi-Objective Optimization
//!
//! This library implements $P$-minimal model enumeration as an algorithm for
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

use std::{fmt, ops::Not};

use rustsat::{
    instances::{ManageVars, MultiOptInstance},
    solvers::{ControlSignal, SolverError, SolverResult, SolverStats},
    types::{Assignment, Clause, Lit},
};

pub mod options;
pub use options::{Limits, Options};

pub mod types;
use types::{ParetoFront, ParetoPoint};

mod pminimal;
pub use crate::pminimal::PMinimal;

#[cfg(feature = "build-binary")]
pub mod cli;

/// Main interface for using this multi-objective optimization solver
pub trait Solve<VM, BCG>
where
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
{
    /// Initializes a new solver from a multi-objective optimization instance
    fn init(inst: MultiOptInstance<VM>, block_clause_gen: BCG) -> Self
    where
        Self: Sized,
    {
        Self::init_with_options(inst, Options::default(), block_clause_gen)
    }
    /// Initializes a new solver with given options from a multi-objective
    /// optimization instance
    fn init_with_options(inst: MultiOptInstance<VM>, opts: Options, block_clause_gen: BCG) -> Self;
    /// Solves the instance under given limits. If not fully solved, errors an
    /// early termination reason.
    fn solve(&mut self, limits: Limits) -> Result<(), Termination>;
    /// Gets the Pareto front discovered so far
    fn pareto_front(&self) -> ParetoFront;
    /// Gets tracked statistics from the solver
    fn stats(&self) -> Stats;
    /// A type to identify a logger
    type LoggerId;
    /// Attaches a logger to the solver
    fn attach_logger(&mut self, boxed_logger: Box<dyn WriteSolverLog>) -> Self::LoggerId;
    /// Detaches a logger from the solver
    fn detach_logger(&mut self, id: Self::LoggerId) -> Option<Box<dyn WriteSolverLog>>;
    /// Attaches a terminator callback. Only one callback can be attached at a time.
    fn attach_terminator(&mut self, term_cb: fn() -> ControlSignal);
    /// Detaches the termination callback
    fn detach_terminator(&mut self);
}

/// Trait for getting statistics from the solver
pub trait ExtendedSolveStats {
    /// Gets statistics from the internal oracle
    fn oracle_stats(&self) -> SolverStats;
    /// Gets statistics from the objective encodings
    fn encoding_stats(&self) -> Vec<EncodingStats>;
}

/// Early termination reasons for [`Solve::solve`]
#[derive(Debug)]
pub enum Termination {
    /// Terminated because of maximum number of Pareto points reached
    PPLimit,
    /// Terminated because of maximum number of solutions reached
    SolsLimit,
    /// Terminated because of maximum number of candidates reached
    CandidatesLimit,
    /// Terminated because of maximum number of oracle calls reached
    OracleCallsLimit,
    /// Termination because an attached logger failed
    LoggerError(LoggerError),
    /// Termination because of termination callback
    Callback,
    /// An error occured in the oracle
    OracleError(SolverError),
}

impl From<SolverError> for Termination {
    fn from(se: SolverError) -> Self {
        Termination::OracleError(se)
    }
}

impl From<LoggerError> for Termination {
    fn from(le: LoggerError) -> Self {
        Termination::LoggerError(le)
    }
}

/// Algorithm phases that the solver can be in
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// Outer loop
    OuterLoop,
    /// $P$-minimization of a model
    Minimization,
    /// Enumeration of solutions at a Pareto point
    Enumeration,
}

impl fmt::Display for Phase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Phase::OuterLoop => write!(f, "outer-loop"),
            Phase::Minimization => write!(f, "minimization"),
            Phase::Enumeration => write!(f, "enumeration"),
        }
    }
}

/// Statistics of the solver
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct Stats {
    /// The number of calls to [`Solve::solve`]
    pub n_solve_calls: usize,
    /// The number of Pareto-optimal solutions found
    pub n_solutions: usize,
    /// The number of Pareto points found
    pub n_pareto_points: usize,
    /// The number of candidates explored
    pub n_candidates: usize,
    /// The number of calls to the SAT oracle
    pub n_oracle_calls: usize,
    /// The number of objectives in the solver
    pub n_objs: usize,
    /// The number of original clauses
    pub n_orig_clauses: usize,
}

/// Statistics of a used cardinality or pseudo-boolean encodings
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct EncodingStats {
    /// The number of clauses in the encoding
    pub n_clauses: usize,
    /// The number of variables in the encoding
    pub n_vars: usize,
    /// The objective offset
    pub offset: isize,
    /// The unit weight, if the objective is unweighted
    pub unit_weight: Option<usize>,
}

/// A logger to attach to a solver
pub trait WriteSolverLog {
    /// Adds a candidate cost point to the log
    fn log_candidate(&mut self, costs: &[usize], phase: Phase) -> Result<(), LoggerError>;
    /// Adds an oracle call to the log
    fn log_oracle_call(&mut self, result: SolverResult, phase: Phase) -> Result<(), LoggerError>;
    /// Adds a solution to the log
    fn log_solution(&mut self) -> Result<(), LoggerError>;
    /// Adds a Pareto point to the log
    fn log_pareto_point(&mut self, pareto_point: &ParetoPoint) -> Result<(), LoggerError>;
    /// Adds a heuristic objective improvement to the log
    fn log_heuristic_obj_improvement(
        &mut self,
        obj_idx: usize,
        apparent_cost: usize,
        improved_cost: usize,
        learned_clauses: usize,
    ) -> Result<(), LoggerError>;
}

/// Error type for loggers
pub struct LoggerError {
    ierror: Box<dyn fmt::Display>,
}

impl LoggerError {
    fn new<IE: fmt::Display + 'static>(ierror: IE) -> Self {
        LoggerError {
            ierror: Box::new(ierror),
        }
    }
}

impl fmt::Display for LoggerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LoggerError: {}", self.ierror)
    }
}

impl fmt::Debug for LoggerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LoggerError: {}", self.ierror)
    }
}

/// The default blocking clause generator
pub fn default_blocking_clause(sol: Assignment) -> Clause {
    Clause::from_iter(sol.into_iter().map(Lit::not))
}
