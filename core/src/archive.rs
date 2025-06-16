//! # Archive of Non-Dominated Solutions

use std::collections::BinaryHeap;

/// A non-dominated archive of solutions
#[derive(Debug, Clone, Default)]
pub struct Archive<S>(BinaryHeap<Elem<S>>);

impl<S> Archive<S> {
    /// Inserts a new solution into the archive
    pub fn insert(&mut self, sol: S, costs: Vec<usize>) {
        self.0.retain(|e| !weakly_dominates(&costs, &e.costs));
        self.0.push(Elem { costs, sol });
    }

    /// Gets the target value (sum of objectives) of the best candidate
    pub fn head(&self) -> Option<&Elem<S>> {
        self.0.peek()
    }

    /// Removes all solutions weakly dominated by the given cost vector from the archive
    pub fn remove_dominated(&mut self, costs: &[usize]) {
        self.0.retain(|e| !weakly_dominates(costs, &e.costs));
    }

    /// Pops the next element from the archive
    pub fn pop(&mut self) -> Option<(Vec<usize>, S)> {
        self.0.pop().map(|e| (e.costs, e.sol))
    }
}

#[derive(Debug, Clone)]
pub struct Elem<S> {
    costs: Vec<usize>,
    sol: S,
}

impl<S> Elem<S> {
    pub fn costs(&self) -> &[usize] {
        &self.costs
    }

    pub fn sol(&self) -> &S {
        &self.sol
    }
}

impl<S> Ord for Elem<S> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // NOTE: intentionally reversed to sort by smallest objective sum
        let self_sum = self.costs.iter().sum::<usize>();
        let other_sum = other.costs.iter().sum::<usize>();
        std::cmp::Reverse(self_sum).cmp(&std::cmp::Reverse(other_sum))
    }
}

impl<S> PartialOrd for Elem<S> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<S> Eq for Elem<S> {}

impl<S> PartialEq for Elem<S> {
    fn eq(&self, other: &Self) -> bool {
        self.costs == other.costs
    }
}

fn weakly_dominates(first: &[usize], second: &[usize]) -> bool {
    for (f, s) in first.iter().zip(second) {
        if s < f {
            return false;
        }
    }
    true
}
