//! # Archive of Non-Dominated Solutions

use std::collections::BinaryHeap;

/// A non-dominated archive of solutions
#[derive(Debug, Clone, Default)]
pub struct Archive<S>(BinaryHeap<Elem<S>>);

impl<S> Archive<S> {
    fn compute_ord(multipliers: &[f64], costs: &[usize]) -> f64 {
        debug_assert_eq!(multipliers.len(), costs.len());
        multipliers
            .iter()
            .zip(costs)
            .map(|(&mult, &cst)| mult * (cst as f64))
            .sum()
    }

    /// Changes the objective multipliers that the archive is sorted based on
    pub fn reorder(&mut self, multipliers: &[f64]) {
        let mut heap = std::mem::take(&mut self.0).into_vec();
        for elem in heap.iter_mut() {
            elem.ord = Self::compute_ord(multipliers, &elem.costs);
        }
        self.0 = BinaryHeap::from(heap);
    }

    /// Inserts a new solution into the archive
    pub fn insert(&mut self, sol: S, mut costs: Vec<usize>, multipliers: &[f64]) {
        costs.shrink_to_fit();
        self.0.retain(|e| !weakly_dominates(&costs, &e.costs));
        let ord = Self::compute_ord(multipliers, &costs);
        self.0.push(Elem { ord, costs, sol });
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

    /// Iterates over the elements in the archive in arbitrary order
    pub fn iter(&self) -> impl Iterator<Item = &Elem<S>> {
        self.0.iter()
    }

    /// Checks whether the archive is empty
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

#[derive(Debug, Clone)]
pub struct Elem<S> {
    ord: f64,
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

    pub fn ord(&self) -> f64 {
        self.ord
    }
}

impl<S> Ord for Elem<S> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // NOTE: intentionally reversed to sort by smallest objective sum
        other.ord.total_cmp(&self.ord)
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

#[cfg(test)]
mod tests {
    #[test]
    fn lowest_first() {
        let mut archive = super::Archive::default();
        archive.insert('a', vec![1, 1, 1], &[1., 1., 1.]);
        archive.insert('b', vec![2, 1, 1], &[1., 1., 1.]);
        let head = archive.head().unwrap();
        assert_eq!(*head.sol(), 'a');
    }
}
