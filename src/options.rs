//! # Options
//!
//! This module contains all configuration options or the $P$-minimal solver.

/// Configuration options for the $P$-minimal solver
pub struct Options {
    /// The maximum number of solutions to enumerate per Pareto point
    pub max_sols_per_pp: Option<usize>,
    /// Whether to perform model tightening
    pub model_tightening: bool,
}

impl Default for Options {
    /// Get the default options
    fn default() -> Self {
        Options {
            max_sols_per_pp: Some(1),
            model_tightening: false,
        }
    }
}
