//! # Types
//!
//! Shared types for the $P$-minimal solver.

use rustsat::types::Assignment;

/// The Pareto front of an instance. This is the return type of the solver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParetoFront<S = Assignment>
where
    S: Clone + Eq,
{
    pps: Vec<ParetoPoint<S>>,
}

impl<S> ParetoFront<S>
where
    S: Clone + Eq,
{
    /// Initializes a new Pareto front
    pub(crate) fn new() -> Self {
        ParetoFront { pps: vec![] }
    }

    /// Adds a Pareto point to the Pareto front. Returns a mutable reference to
    /// the Pareto point in the Pareto front.
    pub(crate) fn add_pp(&mut self, pp: ParetoPoint<S>) {
        self.pps.push(pp)
    }

    /// Converts all solutions to another type
    pub fn convert_solutions<C, S2>(self, conv: &mut C) -> ParetoFront<S2>
    where
        S2: Clone + Eq,
        C: FnMut(S) -> S2,
    {
        ParetoFront {
            pps: self
                .pps
                .into_iter()
                .map(|pp| pp.convert_solutions(conv))
                .collect(),
        }
    }

    /// Gets the number of Pareto points
    pub fn n_pps(&self) -> usize {
        self.pps.len()
    }
}

impl<'a, S> IntoIterator for &'a ParetoFront<S>
where
    S: Clone + Eq,
{
    type Item = &'a ParetoPoint<S>;

    type IntoIter = std::slice::Iter<'a, ParetoPoint<S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.pps.iter()
    }
}

impl<S> IntoIterator for ParetoFront<S>
where
    S: Clone + Eq,
{
    type Item = ParetoPoint<S>;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.pps.into_iter()
    }
}

/// A point on the Pareto front. This is a point in _objective_ space, i.e., a
/// tuple of costs. Multiple Pareto-optimal solutions can be associated with one
/// Pareto point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParetoPoint<S = Assignment>
where
    S: Clone + Eq,
{
    costs: Vec<isize>,
    sols: Vec<S>,
}

impl<S> ParetoPoint<S>
where
    S: Clone + Eq,
{
    /// Constructs a new Pareto point
    pub(crate) fn new(costs: Vec<isize>) -> Self {
        ParetoPoint {
            costs,
            sols: vec![],
        }
    }

    /// Adds a solution to the Pareto point
    pub(crate) fn add_sol(&mut self, sol: S) {
        self.sols.push(sol)
    }

    /// Gets the number of solutions in the Pareto point
    pub fn n_sols(&self) -> usize {
        self.sols.len()
    }

    /// Converts all solutions to another type
    pub fn convert_solutions<C, S2>(self, conv: &mut C) -> ParetoPoint<S2>
    where
        S2: Clone + Eq,
        C: FnMut(S) -> S2,
    {
        ParetoPoint {
            costs: self.costs,
            sols: self.sols.into_iter().map(conv).collect(),
        }
    }

    /// Gets the costs of the Pareto point
    pub fn costs(&self) -> &Vec<isize> {
        &self.costs
    }
}

impl<'a, S> IntoIterator for &'a ParetoPoint<S>
where
    S: Clone + Eq,
{
    type Item = &'a S;

    type IntoIter = std::slice::Iter<'a, S>;

    fn into_iter(self) -> Self::IntoIter {
        self.sols.iter()
    }
}

impl<S> IntoIterator for ParetoPoint<S>
where
    S: Clone + Eq,
{
    type Item = S;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.sols.into_iter()
    }
}
