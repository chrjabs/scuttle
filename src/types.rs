//! # Types
//!
//! Shared types for the $P$-minimal solver.

use std::ops::Index;

use rustsat::types::Assignment;

/// The Pareto front of an instance. This is the return type of the solver.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ParetoFront<S = Assignment>
where
    S: Clone + Eq,
{
    ndoms: Vec<NonDomPoint<S>>,
}

impl<S> ParetoFront<S>
where
    S: Clone + Eq,
{
    /// Converts all solutions to another type
    pub fn convert_solutions<C, S2>(self, conv: &mut C) -> ParetoFront<S2>
    where
        S2: Clone + Eq,
        C: FnMut(S) -> S2,
    {
        ParetoFront {
            ndoms: self
                .ndoms
                .into_iter()
                .map(|pp| pp.convert_solutions(conv))
                .collect(),
        }
    }

    /// Gets the number of non-dominated points
    pub fn len(&self) -> usize {
        self.ndoms.len()
    }

    /// Checks if the Pareto front is empty
    pub fn is_empty(&self) -> bool {
        self.ndoms.is_empty()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, NonDomPoint<S>> {
        self.ndoms.iter()
    }
}

impl<S: Clone + Eq> Index<usize> for ParetoFront<S> {
    type Output = NonDomPoint<S>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.ndoms[index]
    }
}

impl<'a, S> IntoIterator for &'a ParetoFront<S>
where
    S: Clone + Eq,
{
    type Item = &'a NonDomPoint<S>;

    type IntoIter = std::slice::Iter<'a, NonDomPoint<S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.ndoms.iter()
    }
}

impl<S> IntoIterator for ParetoFront<S>
where
    S: Clone + Eq,
{
    type Item = NonDomPoint<S>;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.ndoms.into_iter()
    }
}

impl<S> Extend<NonDomPoint<S>> for ParetoFront<S>
where
    S: Clone + Eq,
{
    fn extend<T: IntoIterator<Item = NonDomPoint<S>>>(&mut self, iter: T) {
        self.ndoms.extend(iter)
    }
}

/// A point on the Pareto front. This is a point in _objective_ space, i.e., a
/// tuple of costs. Multiple Pareto-optimal solutions can be associated with one
/// non-dominated point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NonDomPoint<S = Assignment>
where
    S: Clone + Eq,
{
    costs: Vec<isize>,
    sols: Vec<S>,
}

impl<S> NonDomPoint<S>
where
    S: Clone + Eq,
{
    /// Constructs a new non-dominated point
    pub(crate) fn new(mut costs: Vec<isize>) -> Self {
        costs.shrink_to_fit();
        NonDomPoint {
            costs,
            sols: vec![],
        }
    }

    /// Adds a solution to the non-dominated point
    pub(crate) fn add_sol(&mut self, sol: S) {
        self.sols.push(sol)
    }

    /// Gets the number of solutions in the non-dominated point
    pub fn n_sols(&self) -> usize {
        self.sols.len()
    }

    /// Converts all solutions to another type
    pub fn convert_solutions<C, S2>(self, conv: &mut C) -> NonDomPoint<S2>
    where
        S2: Clone + Eq,
        C: FnMut(S) -> S2,
    {
        NonDomPoint {
            costs: self.costs,
            sols: self.sols.into_iter().map(conv).collect(),
        }
    }

    /// Gets the costs of the non-dominated point
    pub fn costs(&self) -> &Vec<isize> {
        &self.costs
    }
}

impl<'a, S> IntoIterator for &'a NonDomPoint<S>
where
    S: Clone + Eq,
{
    type Item = &'a S;

    type IntoIter = std::slice::Iter<'a, S>;

    fn into_iter(self) -> Self::IntoIter {
        self.sols.iter()
    }
}

impl<S> IntoIterator for NonDomPoint<S>
where
    S: Clone + Eq,
{
    type Item = S;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.sols.into_iter()
    }
}
