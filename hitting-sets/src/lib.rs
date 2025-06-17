//! # Hitting Set Solvers
//!
//! This crate contains a uniform interface to various hitting set solvers intended to be used in
//! IHS-style MaxSAT algorithms.

use std::{fmt, num::NonZero, str};

use rustsat::types::{Cl, Lit};

mod map;
use map::{IndexedVar, VarMap};

#[cfg(feature = "highs")]
mod highs;
#[cfg(feature = "highs")]
pub use highs::{Builder as HighsBuilder, Solver as HighsSolver};

#[cfg(any(feature = "gurobi9", feature = "gurobi12"))]
mod gurobi;
#[cfg(any(feature = "gurobi9", feature = "gurobi12"))]
pub use gurobi::{Builder as GurobiBuilder, Solver as GurobiSolver};

pub const EPSILON: f64 = 0.05;
pub const TRUE: f64 = 1. - EPSILON;
pub const FALSE: f64 = 0. + EPSILON;

#[derive(Debug, PartialEq)]
pub enum CompleteSolveResult {
    Optimal(f64, Vec<Lit>),
    Infeasible,
}

impl From<IncompleteSolveResult> for CompleteSolveResult {
    fn from(value: IncompleteSolveResult) -> Self {
        match value {
            IncompleteSolveResult::Optimal(cost, hs) => CompleteSolveResult::Optimal(cost, hs),
            IncompleteSolveResult::Infeasible => CompleteSolveResult::Infeasible,
            IncompleteSolveResult::Feasible(_, _) => {
                panic!("cannot convert incomplete result to complete")
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum IncompleteSolveResult {
    Optimal(f64, Vec<Lit>),
    Infeasible,
    Feasible(f64, Vec<Lit>),
}

impl From<CompleteSolveResult> for IncompleteSolveResult {
    fn from(value: CompleteSolveResult) -> Self {
        match value {
            CompleteSolveResult::Optimal(cost, hs) => IncompleteSolveResult::Optimal(cost, hs),
            CompleteSolveResult::Infeasible => IncompleteSolveResult::Infeasible,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Threads {
    Auto,
    N(NonZero<u16>),
}

impl fmt::Display for Threads {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Threads::Auto => write!(f, "auto"),
            Threads::N(n) => write!(f, "{n}"),
        }
    }
}

impl Default for Threads {
    fn default() -> Self {
        Threads::N(NonZero::new(1).unwrap())
    }
}

#[derive(Debug, thiserror::Error, Clone)]
pub enum ThreadsParseError {
    #[error("Thread must bei either a positive integer or `auto`")]
    NonInt(#[from] std::num::ParseIntError),
    #[error("Number of threads must be positive")]
    Zero,
}

impl str::FromStr for Threads {
    type Err = ThreadsParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "auto" {
            return Ok(Threads::Auto);
        }
        let Some(n) = NonZero::new(u16::from_str(s)?) else {
            return Err(ThreadsParseError::Zero);
        };
        Ok(Threads::N(n))
    }
}

/// Trait specifying the unified interface to various hitting set solvers
pub trait HittingSetSolver {
    /// The type that can be used to build a solver of this type
    type Builder: BuildSolver<Solver = Self>;

    /// Changes the multipliers for the individual objectives
    ///
    /// The default multipliers are 1 for each objective
    fn change_multipliers(&mut self, multi: &[f64]);

    /// Adds a new core to the solver
    fn add_core(&mut self, core: &Cl);

    /// Adds a clause to the solver
    ///
    /// In contrast to [`HittingSetSolver::add_core`], this does not assume that all variables are
    /// in the objectives
    fn add_clause(&mut self, clause: &Cl);

    /// Computes an optimal hitting set for the currently given cores
    fn optimal_hitting_set<I>(&mut self, start: I) -> CompleteSolveResult
    where
        I: IntoIterator<Item = Lit>;

    /// Computes a hitting set for the currently given cores and stops once a solution better than
    /// the given starting point is found
    fn hitting_set<I>(&mut self, start: I) -> IncompleteSolveResult
    where
        I: IntoIterator<Item = Lit>;

    /// Adds a PD cut to the hitting set solver
    fn add_pd_cut(&mut self, costs: &[usize]);

    /// Gets the statistics of the hitting set solver
    fn statistics(&self) -> Statistics;

    /// Gets an iterator over the objectives in the hitting set solver
    fn objectives(&self) -> impl Iterator<Item = impl Iterator<Item = (Lit, usize)>>;

    /// Adds a learned unit to the hitting set solver
    fn learn_unit(&mut self, unit: Lit);
}

/// Trait for initializing a new solver
pub trait BuildSolver {
    /// The solver type that can be initialized with this building
    type Solver: HittingSetSolver;

    /// Initializes a new solver builder with default options and given objective weights
    fn new<Outer, Inner>(objectives: Outer) -> Self
    where
        Outer: IntoIterator<Item = Inner>,
        Inner: IntoIterator<Item = (Lit, usize)>;

    /// Initializes a solver from the given building
    fn init(self) -> Self::Solver;

    /// Sets the number of threads to solve with
    ///
    /// # Default
    ///
    /// The default value shall be `1`
    fn threads(&mut self, threads: Threads) -> &mut Self;

    /// Whether to use provided solutions as starting points for search
    ///
    /// # Default
    ///
    /// The default value shall `true`
    fn use_starting_points(&mut self, use_start: bool) -> &mut Self;
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Statistics {
    pub solve_time: std::time::Duration,
    pub n_solves: usize,
    pub n_cores: usize,
    pub n_learned_units: usize,
}
