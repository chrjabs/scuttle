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
    /// Core trimming (in core-guided algorithms)
    pub core_trimming: bool,
    /// Core minimization (in core-guided algorithms)
    pub core_minimization: bool,
    /// Core exhaustion (in OLL)
    pub core_exhaustion: bool,
    /// Store the original clauses
    pub store_cnf: bool,
}

impl Default for KernelOptions {
    fn default() -> Self {
        KernelOptions {
            enumeration: Default::default(),
            reserve_enc_vars: false,
            heuristic_improvements: Default::default(),
            solution_guided_search: false,
            core_trimming: false,
            core_minimization: false,
            core_exhaustion: false,
            store_cnf: false,
        }
    }
}

impl KernelOptions {
    pub fn set_enumeration(&mut self, enumeration: EnumOptions) {
        self.enumeration = enumeration;
    }
}

#[derive(Clone, Default)]
pub struct CoreBoostingOptions {
    /// Whether to merge or rebase the encoding
    pub rebase: bool,
    /// What to do after core boosting
    pub after: AfterCbOptions,
}

#[derive(Clone, Default, PartialEq, Eq)]
pub enum AfterCbOptions {
    /// Don't do anything special after core boosting
    #[default]
    Nothing,
    /// Reset the SAT oracle after core boosting
    Reset,
    /// Perform MaxPre "inprocessing" after core boosting
    Inpro(String),
}

pub type KernelWithCbOptions = (KernelOptions, Option<CoreBoostingOptions>);

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
#[cfg_attr(feature = "clap", derive(clap::ValueEnum))]
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

/// Limits for a call to [`crate::Solve::solve`]
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

/// Possible recursion anchors for the divide and conquer algorithm
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub enum DivConAnchor {
    /// Linear Sat-Unsat for single-objective subproblems
    LinSu,
    /// BiOptSat (Sat-Unsat) for bi-objective subproblems
    #[default]
    BiOptSat,
    /// P-Minimal at subproblems of given size
    PMinimal(SubProblemSize),
    /// Run lower-bounding algorithm at subproblems of given size
    LowerBounding(SubProblemSize),
    /// Run the appropriate anchor (Linear Sat-Unsat / BiOptSat / P-Minimal) at
    /// subproblems of size `n-x`.
    NMinus(usize),
}

impl fmt::Display for DivConAnchor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DivConAnchor::LinSu => write!(f, "lin-su"),
            DivConAnchor::BiOptSat => write!(f, "bioptsat"),
            DivConAnchor::PMinimal(size) => write!(f, "p-minimal({})", size),
            DivConAnchor::LowerBounding(size) => write!(f, "lower-bounding({})", size),
            DivConAnchor::NMinus(x) => write!(f, "n-minus({})", x),
        }
    }
}

/// Possible options for building objective encodings in divide and conquer
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "clap", derive(clap::ValueEnum))]
pub enum BuildEncodings {
    /// Only once after the first ideal point
    #[default]
    Once,
    /// Rebuild after each ideal point but don't restart the oracle
    Rebuild,
    /// Restart the oracle after each ideal point and rebuild the encodings
    CleanRebuild,
}

impl fmt::Display for BuildEncodings {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BuildEncodings::Once => write!(f, "once"),
            BuildEncodings::Rebuild => write!(f, "rebuild"),
            BuildEncodings::CleanRebuild => write!(f, "clean-rebuild"),
        }
    }
}

/// Specifying the size of a subproblem
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SubProblemSize {
    /// An absolute subproblem size
    Abs(usize),
    /// A subproblem `x` smaller than the original problem
    Smaller(usize),
}

impl SubProblemSize {
    /// Calculates the absolute problem size given the original instance size
    pub fn absolute(&self, prob_size: usize) -> usize {
        match self {
            SubProblemSize::Abs(abs) => *abs,
            SubProblemSize::Smaller(smaller) => prob_size - *smaller,
        }
    }
}

impl fmt::Display for SubProblemSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SubProblemSize::Abs(size) => write!(f, "+{}", size),
            SubProblemSize::Smaller(size) => write!(f, "-{}", size),
        }
    }
}
