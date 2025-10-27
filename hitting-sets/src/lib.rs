//! # Hitting Set Solvers
//!
//! This crate contains a uniform interface to various hitting set solvers intended to be used in
//! IHS-style MaxSAT algorithms.
#![feature(try_trait_v2)]

use std::{fmt, num::NonZero, str};

use rustsat::types::{Cl, Lit, RsHashMap, Var};

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

#[derive(Debug, PartialEq)]
pub enum ReducedCostsResult {
    ReducedCosts {
        obj_val: f64,
        rcs: Vec<(Var, bool, f64)>,
    },
    Infeasible,
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
    fn add_core(&mut self, core: &Cl, origin: CoreOrigin) {
        self.add_card_core(core.as_ref(), 1, origin);
    }

    /// Adds a cardinality core to the solver
    fn add_card_core(&mut self, lits: &[Lit], bound: usize, origin: CoreOrigin);

    /// Adds a clause to the solver
    ///
    /// In contrast to [`HittingSetSolver::add_core`], this does not assume that all variables are
    /// in the objectives
    fn add_clause(&mut self, clause: &Cl) {
        self.add_card(clause.as_ref(), 1);
    }

    /// Adds a cardinality constraint to the solver
    ///
    /// In contrast to [`HittingSetSolver::add_card_core`], this does not assume that all variables
    /// are in the objectives
    fn add_card(&mut self, lits: &[Lit], bound: usize);

    /// Adds a cardinality equality constraint to the solver
    fn add_card_eq(&mut self, lits: &[Lit], value: usize);

    /// Adds a reified cardinality constraint of for `sum(lits) >= bound -> reif`
    fn add_reified_card(&mut self, lits: &[Lit], bound: usize, reif: Lit, equivalence: bool);

    fn optimal_hitting_set_callbacks<I, Cb>(
        &mut self,
        start: I,
        cb: &mut Cb,
    ) -> MaybeTerminated<CompleteSolveResult>
    where
        I: IntoIterator<Item = Lit>,
        Cb: Callbacks;

    fn hitting_set_callbacks<I, Cb>(
        &mut self,
        start: I,
        cb: &mut Cb,
    ) -> MaybeTerminated<IncompleteSolveResult>
    where
        I: IntoIterator<Item = Lit>,
        Cb: Callbacks;

    /// Computes an optimal hitting set for the currently given cores
    fn optimal_hitting_set<I>(&mut self, start: I) -> CompleteSolveResult
    where
        I: IntoIterator<Item = Lit>,
    {
        self.optimal_hitting_set_callbacks(start, &mut ()).unwrap()
    }

    /// Computes a hitting set for the currently given cores and stops once a solution better than
    /// the given starting point is found
    fn hitting_set<I>(&mut self, start: I) -> IncompleteSolveResult
    where
        I: IntoIterator<Item = Lit>,
    {
        self.hitting_set_callbacks(start, &mut ()).unwrap()
    }

    /// Computes the reduced costs of the objective variables by solving the LP relaxation of the
    /// problem
    fn reduced_costs_callback<Cb>(&mut self, cb: &mut Cb) -> MaybeTerminated<ReducedCostsResult>
    where
        Cb: Callbacks;

    /// Fixes certain literals by changing their bounds
    ///
    /// Returns false if unsatisfiability is detected
    fn fix<I>(&mut self, to_fix: I) -> bool
    where
        I: IntoIterator<Item = Lit>;

    /// Removes all fixings done via [`HittingSetSolver::fix`]
    fn unfix_all(&mut self);

    /// Adds a PD cut to the hitting set solver
    fn add_pd_cut(&mut self, costs: &[usize]);

    /// Changes the objectives in the solver
    fn change_objectives<Outer, Inner>(&mut self, objectives: Outer)
    where
        Outer: IntoIterator<Item = (Inner, usize)>,
        Inner: IntoIterator<Item = (Lit, usize)>;

    /// Change the lower bounds for the objectives
    fn change_lower_bounds<Iter>(&mut self, lower_bounds: Iter)
    where
        Iter: IntoIterator<Item = usize>;

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

    /// Register to the solver that the user might want to solve an LP relaxation later
    fn might_need_lp(&mut self, might_need: bool) -> &mut Self;
}

/// Trait for solver callbacks
pub trait Callbacks {
    /// If this returns true, the solver should terminate
    fn check_termination(&self) -> bool;
}

impl Callbacks for () {
    fn check_termination(&self) -> bool {
        false
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CoreOrigin {
    Seeding,
    CoreBoosting,
    Normal,
    Abstract,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Statistics {
    pub solve_time: std::time::Duration,
    pub lp_solve_time: std::time::Duration,
    pub n_solves: usize,
    pub n_lp_solves: usize,
    pub n_cores: usize,
    pub n_abstract_cores: usize,
    pub n_seeded: usize,
    pub n_learned_units: usize,
}

#[derive(Debug, Clone, Default)]
struct Obj {
    lits: RsHashMap<Lit, usize>,
    offset: usize,
    lower_bound: usize,
}

/// Return type for interruptible functions
#[derive(Debug, PartialEq)]
pub enum MaybeTerminated<T = ()> {
    /// The operation finished with a return value
    Done(T),
    /// The operation was terminated early
    Terminated,
}

impl<T> MaybeTerminated<T> {
    pub fn unwrap(self) -> T {
        match self {
            MaybeTerminated::Done(val) => val,
            MaybeTerminated::Terminated => {
                panic!("called `MaybeTerminated::unwrap()` on a `Terminated` value")
            }
        }
    }

    pub fn map<T2>(self, mut map: impl FnMut(T) -> T2) -> MaybeTerminated<T2> {
        match self {
            MaybeTerminated::Done(val) => MaybeTerminated::Done(map(val)),
            MaybeTerminated::Terminated => MaybeTerminated::Terminated,
        }
    }
}

impl<T> std::ops::Try for MaybeTerminated<T> {
    type Output = T;

    type Residual = MaybeTerminated<std::convert::Infallible>;

    fn from_output(output: Self::Output) -> Self {
        MaybeTerminated::Done(output)
    }

    fn branch(self) -> std::ops::ControlFlow<Self::Residual, Self::Output> {
        match self {
            MaybeTerminated::Done(val) => std::ops::ControlFlow::Continue(val),
            MaybeTerminated::Terminated => {
                std::ops::ControlFlow::Break(MaybeTerminated::Terminated)
            }
        }
    }
}

impl<T> std::ops::FromResidual<MaybeTerminated<std::convert::Infallible>> for MaybeTerminated<T> {
    fn from_residual(residual: <Self as std::ops::Try>::Residual) -> Self {
        let MaybeTerminated::Terminated = residual;
        MaybeTerminated::Terminated
    }
}
