//! # Options
//!
//! This module contains all configuration options or the $P$-minimal solver.

use std::fmt;

use crate::Phase;

/// Solver-wide configuration options
#[derive(Clone, Copy)]
pub struct KernelOptions {
    /// The Pareto point enumeration mode
    pub enumeration: EnumOptions,
    /// Reserve encoding variables in advance
    pub reserve_enc_vars: bool,
    /// Heuristic solution improvement options
    pub heuristic_improvements: HeurImprOptions,
    /// Solution-guided search (aka phasing solutions)
    pub solution_guided_search: bool,
}

impl Default for KernelOptions {
    fn default() -> Self {
        KernelOptions {
            enumeration: Default::default(),
            reserve_enc_vars: false,
            heuristic_improvements: Default::default(),
            solution_guided_search: false,
        }
    }
}

impl KernelOptions {
    pub fn set_enumeration(&mut self, enumeration: EnumOptions) {
        self.enumeration = enumeration;
    }
}

#[derive(Clone, Copy)]
pub struct DivConOptions {
    pub kernel: KernelOptions,
    /// Using BiOptSat as recursion anchor in DivCon
    pub bioptsat: bool,
}

impl Default for DivConOptions {
    fn default() -> Self {
        Self {
            kernel: Default::default(),
            bioptsat: true,
        }
    }
}

impl DivConOptions {
    pub fn set_enumeration(&mut self, enumeration: EnumOptions) {
        self.kernel.set_enumeration(enumeration)
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
}

impl HeurImprOptions {
    /// No heuristic improvements
    pub fn none() -> Self {
        Self {
            solution_tightening: HeurImprWhen::Never,
        }
    }

    /// Always all heuristic improvements
    pub fn all() -> Self {
        Self {
            solution_tightening: HeurImprWhen::Always,
        }
    }
}

impl Default for HeurImprOptions {
    fn default() -> Self {
        Self {
            solution_tightening: HeurImprWhen::OuterLoop,
        }
    }
}

/// Options for when solution improvement can be performed
#[derive(Clone, Copy, Default, PartialEq, Eq)]
#[cfg_attr(feature = "binary-deps", derive(clap::ValueEnum))]
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
