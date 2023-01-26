//! # Options
//!
//! This module contains all configuration options or the $P$-minimal solver.

use std::fmt;

#[cfg(feature = "build-binary")]
use clap::ValueEnum;

use crate::Phase;

/// Configuration options for the $P$-minimal solver
#[derive(Clone, Copy)]
pub struct Options {
    /// The Pareto point enumeration mode
    pub enumeration: EnumOptions,
    /// Heuristic solution improvement options
    pub heuristic_improvements: HeurImprOptions,
    /// Reserve encoding variables in advance
    pub reserve_enc_vars: bool,
}

impl Default for Options {
    /// Get the default options
    fn default() -> Self {
        Options {
            enumeration: Default::default(),
            heuristic_improvements: Default::default(),
            reserve_enc_vars: false,
        }
    }
}

/// Enumeration options for the $P$-minimal solver
#[derive(Default, Clone, Copy, PartialEq, Eq)]
pub enum EnumOptions {
    #[default]
    /// Don't enumerate at each Pareto point
    NoEnum,
    /// Enumerate Pareto-optimal solutions (with an optional limit) at each
    /// Pareto point using the provided blocking clause generator
    Solutions(Option<usize>),
    /// Enumerate Pareto-MCSs (with an optional limit) at each Pareto point
    PMCSs(Option<usize>),
}

/// Options regarding heuristic solution improvement
#[derive(Clone, Copy)]
pub struct HeurImprOptions {
    /// When to perform solution tightening (flipping objective literals that can
    /// be flipped without breaking satisfiability)
    pub solution_tightening: HeurImprWhen,
    /// When to learn tightening clauses from a solution. Tightening clauses
    /// lazily build equivalences for the objective literals.
    pub tightening_clauses: HeurImprWhen,
}

impl HeurImprOptions {
    /// Checks whether the solver needs to store objective clauses for solution
    /// improvement
    pub(crate) fn must_store_clauses(&self) -> bool {
        self.solution_tightening != HeurImprWhen::Never
            || self.tightening_clauses != HeurImprWhen::Never
    }

    /// No heuristic improvements
    pub fn none() -> Self {
        Self {
            solution_tightening: HeurImprWhen::Never,
            tightening_clauses: HeurImprWhen::Never,
        }
    }

    /// Always all heuristic improvements
    pub fn all() -> Self {
        Self {
            solution_tightening: HeurImprWhen::Always,
            tightening_clauses: HeurImprWhen::Always,
        }
    }
}

impl Default for HeurImprOptions {
    fn default() -> Self {
        Self {
            // Note: solution tightening apparently broken when negated literal
            // in other objective
            solution_tightening: HeurImprWhen::Never,
            tightening_clauses: HeurImprWhen::Never,
        }
    }
}

/// Options for when solution improvement can be performed
#[derive(Clone, Copy, Default, PartialEq, Eq)]
#[cfg_attr(feature = "build-binary", derive(ValueEnum))]
pub enum HeurImprWhen {
    /// Never perform solution improvement
    #[default]
    Never,
    /// Always perform solution improvement
    Always,
    /// Only perform solution improvement in outer loop
    OuterLoop,
}

impl HeurImprWhen {
    /// Checks whether the technique is wanted for a given phase
    pub(crate) fn wanted(&self, phase: Phase) -> bool {
        if phase == Phase::Enumeration {
            return false;
        }
        match self {
            HeurImprWhen::Never => false,
            HeurImprWhen::Always => true,
            HeurImprWhen::OuterLoop => phase == Phase::OuterLoop,
        }
    }
}

impl fmt::Display for HeurImprWhen {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HeurImprWhen::Never => write!(f, "never"),
            HeurImprWhen::Always => write!(f, "always"),
            HeurImprWhen::OuterLoop => write!(f, "outer-loop"),
        }
    }
}

/// Limits for a call to [`Solver::solve`]
#[derive(Clone, Copy, Default)]
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
