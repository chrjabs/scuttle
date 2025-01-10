//! # Scuttle
//!
//! A multi-objective MaxSAT solver with multiple algorithms implemented.
#![feature(try_trait_v2)]

use std::fmt;

use rustsat::solvers::{SolverResult, SolverStats};

pub mod options;
pub use options::{CoreBoostingOptions, KernelOptions, Limits};

pub mod types;
use types::NonDomPoint;

pub mod prepro;

pub mod algs;
pub use algs::{
    CoreBoost, Init, InitCert, InitCertDefaultBlock, InitDefaultBlock, KernelFunctions, Solve,
};

// Reexport algorithms
pub use algs::bioptsat::BiOptSat;
pub use algs::lowerbounding::LowerBounding;
pub use algs::pminimal::PMinimal;

pub(crate) mod termination;
pub use termination::MaybeTerminated;
pub use termination::MaybeTerminatedError;
pub use termination::Termination;

/// Trait for getting statistics from the solver
pub trait ExtendedSolveStats {
    /// Gets statistics from the internal oracle
    fn oracle_stats(&self) -> SolverStats;
    /// Gets statistics from the objective encodings
    fn encoding_stats(&self) -> Vec<EncodingStats>;
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
    fn log_candidate(&mut self, costs: &[usize], phase: Phase) -> anyhow::Result<()>;
    /// Adds an oracle call to the log
    fn log_oracle_call(&mut self, result: SolverResult) -> anyhow::Result<()>;
    /// Adds a solution to the log
    fn log_solution(&mut self) -> anyhow::Result<()>;
    /// Adds a non-dominated point to the log
    fn log_non_dominated(&mut self, pareto_point: &NonDomPoint) -> anyhow::Result<()>;
    #[cfg(feature = "sol-tightening")]
    /// Adds a heuristic objective improvement to the log
    fn log_heuristic_obj_improvement(
        &mut self,
        obj_idx: usize,
        apparent_cost: usize,
        improved_cost: usize,
    ) -> anyhow::Result<()>;
    /// Adds a fence change in the lower-bounding algorithm to the log
    fn log_fence(&mut self, fence: &[usize]) -> anyhow::Result<()>;
    /// Adds a new routine starting to the log
    fn log_routine_start(&mut self, desc: &'static str) -> anyhow::Result<()>;
    /// Adds a new routine ending to the log
    fn log_routine_end(&mut self) -> anyhow::Result<()>;
    /// Adds end of solving to the log
    fn log_end_solve(&mut self) -> anyhow::Result<()>;
    /// Adds an updated ideal point to the log
    fn log_ideal(&mut self, ideal: &[usize]) -> anyhow::Result<()>;
    /// Adds an updated nadir point to the log
    fn log_nadir(&mut self, nadir: &[usize]) -> anyhow::Result<()>;
    /// Adds an extracted core to the log
    fn log_core(&mut self, weight: usize, len: usize, red_len: usize) -> anyhow::Result<()>;
    /// Adds a core exhaustion to the log
    fn log_core_exhaustion(&mut self, exhausted: usize, weight: usize) -> anyhow::Result<()>;
    /// Adds an inprocessing step to the log
    fn log_inprocessing(
        &mut self,
        cls_before_after: (usize, usize),
        fixed_lits: usize,
        obj_range_before_after: Vec<(usize, usize)>,
    ) -> anyhow::Result<()>;
    /// Logs any string
    fn log_message(&mut self, msg: &str) -> anyhow::Result<()>;
}
