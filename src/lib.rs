//! # Scuttle
//!
//! A multi-objective MaxSAT solver with multiple algorithms implemented.

use std::fmt;

use rustsat::solvers::{SolverError, SolverResult, SolverStats};

pub mod options;
#[cfg(feature = "div-con")]
pub use options::DivConOptions;
pub use options::{CoreBoostingOptions, KernelOptions, Limits};

pub mod types;
use types::NonDomPoint;

pub mod solver;
pub use solver::CoreBoost;
pub use solver::KernelFunctions;
pub use solver::Solve;

// Reexport algorithms
pub use solver::bioptsat::BiOptSat;
pub use solver::lowerbounding::LowerBounding;
pub use solver::pminimal::PMinimal;

#[cfg(feature = "binary-deps")]
pub mod cli;

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
    /// The instance does not contain any variables
    NoVars,
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
    /// Termination because of external interrupt
    Interrupted,
    /// An error occured in the oracle
    OracleError(SolverError),
    /// Attempted to reset oracle without having stored the original CNF
    ResetWithoutCnf,
    /// Called core boosting after calling solve
    CbAfterSolve,
}

impl Termination {
    pub fn is_error(&self) -> bool {
        matches!(
            self,
            Termination::LoggerError(_)
                | Termination::OracleError(_)
                | Termination::ResetWithoutCnf
                | Termination::CbAfterSolve
        )
    }
}

impl fmt::Display for Termination {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Termination::NoVars => write!(f, "Instance does not contain any variables"),
            Termination::PPLimit => {
                write!(f, "Solver terminated early because of Pareto point limit")
            }
            Termination::SolsLimit => {
                write!(f, "Solver terminated early because of solution limit")
            }
            Termination::CandidatesLimit => {
                write!(f, "Solver terminated early because of candidate limit")
            }
            Termination::OracleCallsLimit => {
                write!(f, "Solver terminated early because of oracle call limit")
            }
            Termination::LoggerError(log_error) => {
                write!(f, "Solver terminated because logger failed: {}", log_error)
            }
            Termination::Interrupted => {
                write!(f, "Solver terminated early because of interrupt signal")
            }
            Termination::OracleError(oe) => {
                write!(f, "The SAT oracle returned an error: {}", oe)
            }
            Termination::ResetWithoutCnf => write!(
                f,
                "Tried to reset the SAT oracle without having stored the original clauses"
            ),
            Termination::CbAfterSolve => {
                write!(f, "Tried to call core boosting after calling solve")
            }
        }
    }
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
    /// Linsu sub algorithm
    Linsu,
}

impl fmt::Display for Phase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Phase::OuterLoop => write!(f, "outer-loop"),
            Phase::Minimization => write!(f, "minimization"),
            Phase::Enumeration => write!(f, "enumeration"),
            Phase::Linsu => write!(f, "linsu"),
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
    /// The number of non-dominated points found
    pub n_non_dominated: usize,
    /// The number of candidates explored
    pub n_candidates: usize,
    /// The number of calls to the SAT oracle
    pub n_oracle_calls: usize,
    /// The number of objectives in the solver
    pub n_objs: usize,
    /// The number of non-constant objectives in the solver
    pub n_real_objs: usize,
    /// The number of original clauses
    pub n_orig_clauses: usize,
}

/// Statistics of a used cardinality or pseudo-boolean encodings
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub struct EncodingStats {
    /// The number of clauses in the encoding
    pub n_clauses: usize,
    /// The number of variables in the encoding
    pub n_vars: u32,
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
    fn log_oracle_call(&mut self, result: SolverResult) -> Result<(), LoggerError>;
    /// Adds a solution to the log
    fn log_solution(&mut self) -> Result<(), LoggerError>;
    /// Adds a non-dominated point to the log
    fn log_non_dominated(&mut self, pareto_point: &NonDomPoint) -> Result<(), LoggerError>;
    /// Adds a heuristic objective improvement to the log
    fn log_heuristic_obj_improvement(
        &mut self,
        obj_idx: usize,
        apparent_cost: usize,
        improved_cost: usize,
    ) -> Result<(), LoggerError>;
    /// Adds a fence change in the lower-bounding algorithm to the log
    fn log_fence(&mut self, fence: &[usize]) -> Result<(), LoggerError>;
    /// Adds a new routine starting to the log
    fn log_routine_start(&mut self, desc: &'static str) -> Result<(), LoggerError>;
    /// Adds a new routine ending to the log
    fn log_routine_end(&mut self) -> Result<(), LoggerError>;
    /// Adds end of solving to the log
    fn log_end_solve(&mut self) -> Result<(), LoggerError>;
    /// Adds an updated ideal point to the log
    fn log_ideal(&mut self, ideal: &[usize]) -> Result<(), LoggerError>;
    /// Adds an updated nadir point to the log
    fn log_nadir(&mut self, nadir: &[usize]) -> Result<(), LoggerError>;
    /// Adds an extracted core to the log
    fn log_core(&mut self, weight: usize, len: usize, red_len: usize) -> Result<(), LoggerError>;
    /// Adds a core exhaustion to the log
    fn log_core_exhaustion(&mut self, exhausted: usize, weight: usize) -> Result<(), LoggerError>;
    /// Adds an inprocessing step to the log
    fn log_inprocessing(
        &mut self,
        cls_before_after: (usize, usize),
        fixed_lits: usize,
        obj_range_before_after: Vec<(usize, usize)>,
    ) -> Result<(), LoggerError>;
    /// Logs any string
    fn log_message(&mut self, msg: &str) -> Result<(), LoggerError>;
}

/// Error type for loggers
pub struct LoggerError {
    ierror: Box<dyn fmt::Display>,
}

impl LoggerError {
    pub fn new<IE: fmt::Display + 'static>(ierror: IE) -> Self {
        LoggerError {
            ierror: Box::new(ierror),
        }
    }
}

impl From<std::io::Error> for LoggerError {
    fn from(value: std::io::Error) -> Self {
        Self {
            ierror: Box::new(value),
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
