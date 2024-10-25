//! # Variable Mapping Functionality

use rustsat::types::Var;

/// A struct for mapping [`Var`] to solver-internal variables
#[derive(Debug)]
pub struct VarMap<T> {
    forward: Vec<Option<T>>,
    backward: Vec<Var>,
}

impl<T> VarMap<T> {
    /// Initializes a new variable map
    ///
    /// Will reserve `external` space for external variables ([`Var`]) and `internal` space for
    /// internal variables
    pub fn new(external: usize, internal: usize) -> Self {
        Self {
            forward: Vec::with_capacity(external),
            backward: Vec::with_capacity(internal),
        }
    }
}

impl<T> VarMap<T>
where
    T: IndexedVar + std::fmt::Debug,
{
    /// For a variable, returns it's internal representation. If none is tracked, generates a new
    /// one with `if_not`.
    ///
    /// `if_not` must return a new `T` indexing to the next free value
    ///
    /// # Panics
    ///
    /// - If the value returned from `if_not` does not index to the next free value
    /// - If the negated literal is already part of the map
    pub fn ensure_mapped<New>(&mut self, external: Var, mut if_not: New) -> T
    where
        New: FnMut() -> T,
    {
        if let Some(Some(mapped)) = self.forward.get(external.idx()) {
            assert_eq!(external, self[mapped]);
            return mapped.clone();
        }
        let mapped = if_not();
        assert_eq!(mapped.index(), self.backward.len());
        self.backward.push(external);
        if self.forward.len() <= external.idx() {
            self.forward.resize(external.idx() + 1, None);
        }
        self.forward[external.idx()] = Some(mapped);
        self[external].clone()
    }
}

impl<T> std::ops::Index<Var> for VarMap<T> {
    type Output = T;

    fn index(&self, index: Var) -> &Self::Output {
        self.forward[index.idx()].as_ref().unwrap()
    }
}

impl<T> std::ops::Index<usize> for VarMap<T> {
    type Output = Var;

    fn index(&self, index: usize) -> &Self::Output {
        &self.backward[index]
    }
}

impl<T> std::ops::Index<T> for VarMap<T>
where
    T: IndexedVar + Copy,
{
    type Output = Var;

    fn index(&self, index: T) -> &Self::Output {
        &self.backward[index.index()]
    }
}

impl<T> std::ops::Index<&T> for VarMap<T>
where
    T: IndexedVar,
{
    type Output = Var;

    fn index(&self, index: &T) -> &Self::Output {
        &self.backward[index.index()]
    }
}

/// Trait for variables that an index can be gotten from
pub trait IndexedVar: Clone {
    fn index(&self) -> usize;
}
