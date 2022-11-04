//! # Options
//!
//! This module contains all configuration options or the $P$-minimal solver.

/// Configuration options for the $P$-minimal solver
#[derive(Clone)]
pub struct Options {
    /// The maximum number of solutions to enumerate per Pareto point
    pub max_sols_per_pp: Option<usize>,
    /// Whether to perform model tightening
    pub model_tightening: bool,
    /// Reserve encoding variables in advance
    pub reserve_enc_vars: bool,
}

impl Default for Options {
    /// Get the default options
    fn default() -> Self {
        Options {
            max_sols_per_pp: Some(1),
            model_tightening: false,
            reserve_enc_vars: false,
        }
    }
}

/// Limits for a call to [`Solver::solve`]
#[derive(Clone)]
pub struct Limits {
    /// The maximum number of Pareto points to enumerate
    pub pps: Option<usize>,
    /// The maximum number of solutions to enumerate
    pub sols: Option<usize>,
    /// The maximum number of candidates to consider
    pub candidates: Option<usize>,
    /// The maximum number of SAT oracle calls to make
    pub oracle_calls: Option<usize>,
}

impl Limits {
    /// No limits
    pub fn none() -> Limits {
        Limits {
            pps: None,
            sols: None,
            candidates: None,
            oracle_calls: None,
        }
    }
}
