//! # Hitting Set Solvers
//!
//! This crate contains a uniform interface to various hitting set solvers intended to be used in
//! IHS-style MaxSAT algorithms.

use std::time::Duration;

use rustsat::types::{Cl, Lit};

mod map;
use map::{IndexedVar, VarMap};

#[cfg(feature = "highs")]
mod highs;
#[cfg(feature = "highs")]
pub use highs::{Builder as HighsBuilder, Solver as HighsSolver};

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
            IncompleteSolveResult::Feasible(_, _) | IncompleteSolveResult::Unknown => {
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
    Unknown,
}

impl From<CompleteSolveResult> for IncompleteSolveResult {
    fn from(value: CompleteSolveResult) -> Self {
        match value {
            CompleteSolveResult::Optimal(cost, hs) => IncompleteSolveResult::Optimal(cost, hs),
            CompleteSolveResult::Infeasible => IncompleteSolveResult::Infeasible,
        }
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

    /// Computes an optimal hitting set for the currently given cores
    fn optimal_hitting_set(&mut self) -> CompleteSolveResult;

    /// Computes a hitting set for the currently given cores under a time limit
    fn hitting_set(&mut self, time_limit: Duration) -> IncompleteSolveResult;

    /// Adds a PD cut to the hitting set solver
    fn add_pd_cut(&mut self, costs: &[usize]);
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
    fn threads(&mut self, threads: u32) -> &mut Self;
}
