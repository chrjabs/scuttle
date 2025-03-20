//! # Types
//!
//! Shared types for the $P$-minimal solver.

use std::{
    cmp,
    ops::{Index, Range},
};

use rustsat::{
    encodings::{card, pb, totdb, CollectCertClauses, CollectClauses},
    instances::{ManageVars, ReindexVars},
    types::{
        constraints::PbConstraint, Assignment, Clause, Lit, LitIter, RsHashMap, Var, WLitIter,
    },
};

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
        #[cfg(all(debug_assertions, feature = "check-non-dominance"))]
        {
            let cost_set = rustsat::types::RsHashSet::from_iter(
                self.ndoms.iter().map(|nd| nd.costs().clone()),
            );
            let check_dominated = |c1: &Vec<isize>, c2: &Vec<isize>| -> bool {
                let mut dom = 0;
                for (c1, c2) in c1.iter().zip(c2.iter()) {
                    if c1 < c2 {
                        if dom <= 0 {
                            dom = -1;
                        } else {
                            return false;
                        }
                    } else if c2 < c1 {
                        if dom >= 0 {
                            dom = 1;
                        } else {
                            return false;
                        }
                    }
                }
                return dom != 0;
            };
            for ndom in iter.into_iter() {
                for cost in &cost_set {
                    debug_assert!(!check_dominated(ndom.costs(), cost));
                }
                debug_assert!(!cost_set.contains(ndom.costs()));
                self.ndoms.push(ndom);
            }
            return;
        }
        #[cfg(not(all(debug_assertions, feature = "check-non-dominance")))]
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

    /// Gets an iterator over references to the solutions
    pub fn iter(&self) -> impl Iterator<Item = &S> {
        self.sols.iter()
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

/// Data regarding an objective
#[derive(Debug, Clone)]
pub enum Objective {
    Weighted {
        offset: isize,
        lits: RsHashMap<Lit, usize>,
        idx: usize,
        lower_bound: usize,
        reform_id: Option<pigeons::AbsConstraintId>,
    },
    Unweighted {
        offset: isize,
        unit_weight: usize,
        lits: Vec<Lit>,
        idx: usize,
        lower_bound: usize,
        reform_id: Option<pigeons::AbsConstraintId>,
    },
    Constant {
        offset: isize,
        idx: usize,
        lower_bound: usize,
        reform_id: Option<pigeons::AbsConstraintId>,
    },
}

impl Objective {
    /// Initializes the objective from a soft lit iterator and an offset
    pub fn new<Iter: WLitIter>(lits: Iter, offset: isize, idx: usize) -> Self {
        let lits: Vec<_> = lits.into_iter().collect();
        if lits.is_empty() {
            return Objective::Constant {
                offset,
                idx,
                lower_bound: 0,
                reform_id: None,
            };
        }
        let unit_weight = lits[0].1;
        let weighted = 'detect_weighted: {
            for (_, w) in &lits {
                if *w != unit_weight {
                    break 'detect_weighted true;
                }
            }
            false
        };
        if weighted {
            Objective::Weighted {
                offset,
                lits: lits.into_iter().collect(),
                idx,
                lower_bound: 0,
                reform_id: None,
            }
        } else {
            Objective::Unweighted {
                offset,
                unit_weight,
                lits: lits.into_iter().map(|(l, _)| l).collect(),
                idx,
                lower_bound: 0,
                reform_id: None,
            }
        }
    }

    /// Gets the offset of the objective
    pub fn offset(&self) -> isize {
        match self {
            Objective::Weighted { offset, .. } => *offset,
            Objective::Unweighted { offset, .. } => *offset,
            Objective::Constant { offset, .. } => *offset,
        }
    }

    /// Gets the unit weight of the objective
    pub fn unit_weight(&self) -> usize {
        match self {
            Objective::Weighted { .. } | Objective::Constant { .. } => 1,
            Objective::Unweighted { unit_weight, .. } => *unit_weight,
        }
    }

    /// Unified iterator over encodings
    pub fn iter(&self) -> ObjIter<'_> {
        match self {
            Objective::Weighted { lits, .. } => ObjIter::Weighted(lits.iter()),
            Objective::Unweighted { lits, .. } => ObjIter::Unweighted(lits.iter()),
            Objective::Constant { .. } => ObjIter::Constant,
        }
    }

    /// Gets the number of literals in the objective
    pub fn n_lits(&self) -> usize {
        match self {
            Objective::Weighted { lits, .. } => lits.len(),
            Objective::Unweighted { lits, .. } => lits.len(),
            Objective::Constant { .. } => 0,
        }
    }

    /// Gets the index of the objective
    pub fn idx(&self) -> usize {
        match self {
            Objective::Weighted { idx, .. }
            | Objective::Unweighted { idx, .. }
            | Objective::Constant { idx, .. } => *idx,
        }
    }

    /// Gets the reformulation ID of the objective
    pub fn reform_id(&self) -> Option<pigeons::AbsConstraintId> {
        match self {
            Objective::Weighted { reform_id, .. }
            | Objective::Unweighted { reform_id, .. }
            | Objective::Constant { reform_id, .. } => *reform_id,
        }
    }

    /// Sets the lower bound of the objective
    pub fn set_lower_bound(&mut self, new_lower_bound: usize) {
        match self {
            Objective::Weighted { lower_bound, .. }
            | Objective::Unweighted { lower_bound, .. }
            | Objective::Constant { lower_bound, .. } => *lower_bound = new_lower_bound,
        }
    }

    /// Gets the lower bound of the objective
    pub fn lower_bound(&self) -> usize {
        match self {
            Objective::Weighted { lower_bound, .. }
            | Objective::Unweighted { lower_bound, .. }
            | Objective::Constant { lower_bound, .. } => *lower_bound,
        }
    }

    /// Sets the objective reformulation ID
    pub fn set_reform_id(&mut self, new_reform_id: Option<pigeons::AbsConstraintId>) {
        match self {
            Objective::Weighted { reform_id, .. }
            | Objective::Unweighted { reform_id, .. }
            | Objective::Constant { reform_id, .. } => *reform_id = new_reform_id,
        }
    }
}

pub enum ObjIter<'a> {
    Weighted(std::collections::hash_map::Iter<'a, Lit, usize>),
    Unweighted(std::slice::Iter<'a, Lit>),
    Constant,
}

impl Iterator for ObjIter<'_> {
    type Item = (Lit, usize);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ObjIter::Weighted(iter) => iter.next().map(|(&l, &w)| (l, w)),
            ObjIter::Unweighted(iter) => iter.next().map(|&l| (l, 1)),
            ObjIter::Constant => None,
        }
    }
}

/// An objective encoding for either a weighted or an unweighted objective
#[derive(Debug)]
pub(crate) enum ObjEncoding<PBE, CE> {
    Weighted(PBE, usize),
    Unweighted(CE, usize),
    Constant,
}

impl<PBE, CE> ObjEncoding<PBE, CE>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
{
    /// Initializes a new objective encoding for a weighted objective
    pub fn new_weighted<VM: ManageVars, LI: WLitIter>(
        lits: LI,
        reserve: bool,
        var_manager: &mut VM,
    ) -> Self {
        let mut encoding = PBE::from_iter(lits);
        if reserve {
            encoding.reserve(var_manager);
        }
        ObjEncoding::Weighted(encoding, 0)
    }
}

impl<PBE, CE> ObjEncoding<PBE, CE>
where
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
{
    /// Initializes a new objective encoding for a weighted objective
    pub fn new_unweighted<VM: ManageVars, LI: LitIter>(
        lits: LI,
        reserve: bool,
        var_manager: &mut VM,
    ) -> Self {
        let mut encoding = CE::from_iter(lits);
        if reserve {
            encoding.reserve(var_manager);
        }
        ObjEncoding::Unweighted(encoding, 0)
    }
}

impl<PBE, CE> ObjEncoding<PBE, CE> {
    /// Gets the offset of the encoding
    pub fn offset(&self) -> usize {
        match self {
            ObjEncoding::Weighted(_, offset) => *offset,
            ObjEncoding::Unweighted(_, offset) => *offset,
            ObjEncoding::Constant => 0,
        }
    }
}

impl<PBE, CE> ObjEncoding<PBE, CE>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
{
    /// Gets the next higher objective value
    pub fn next_higher(&self, val: usize) -> usize {
        match self {
            ObjEncoding::Weighted(enc, offset) => enc.next_higher(val - offset) + offset,
            ObjEncoding::Unweighted(..) => val + 1,
            ObjEncoding::Constant => val,
        }
    }

    /// Encodes the given range
    pub fn encode_ub_change<Col>(
        &mut self,
        range: Range<usize>,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), rustsat::OutOfMemory>
    where
        Col: CollectClauses,
    {
        match self {
            ObjEncoding::Weighted(enc, offset) => enc.encode_ub_change(
                if range.start >= *offset {
                    range.start - *offset
                } else {
                    0
                }..if range.end >= *offset {
                    range.end - *offset
                } else {
                    0
                },
                collector,
                var_manager,
            ),
            ObjEncoding::Unweighted(enc, offset) => enc.encode_ub_change(
                if range.start >= *offset {
                    range.start - *offset
                } else {
                    0
                }..if range.end >= *offset {
                    range.end - *offset
                } else {
                    0
                },
                collector,
                var_manager,
            ),
            ObjEncoding::Constant => Ok(()),
        }
    }

    /// Enforces the given upper bound
    pub fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, rustsat::encodings::Error> {
        match self {
            ObjEncoding::Weighted(enc, offset) => {
                if ub >= *offset {
                    enc.enforce_ub(ub - *offset)
                } else {
                    Err(rustsat::encodings::Error::Unsat)
                }
            }
            ObjEncoding::Unweighted(enc, offset) => {
                if ub >= *offset {
                    enc.enforce_ub(ub - *offset)
                } else {
                    Err(rustsat::encodings::Error::Unsat)
                }
            }
            ObjEncoding::Constant => Ok(vec![]),
        }
    }

    /// Gets a coarse upper bound
    #[cfg(feature = "coarse-convergence")]
    pub fn coarse_ub(&self, ub: usize) -> usize {
        match self {
            ObjEncoding::Weighted(enc, offset) => {
                if ub >= *offset {
                    enc.coarse_ub(ub - *offset) + offset
                } else {
                    ub
                }
            }
            _ => ub,
        }
    }
}

impl<PBE, CE> ObjEncoding<PBE, CE>
where
    PBE: pb::BoundUpperIncremental + pb::cert::BoundUpperIncremental,
    CE: card::BoundUpperIncremental + card::cert::BoundUpperIncremental,
{
    /// Encodes the given range
    pub fn encode_ub_change_cert<Col, ProofW>(
        &mut self,
        range: Range<usize>,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<ProofW>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        ProofW: std::io::Write,
    {
        match self {
            ObjEncoding::Weighted(enc, offset) => {
                #[cfg(feature = "verbose-proofs")]
                proof.comment(&"extend generalized totalizer")?;
                enc.encode_ub_change_cert(
                    if range.start >= *offset {
                        range.start - *offset
                    } else {
                        0
                    }..if range.end >= *offset {
                        range.end - *offset
                    } else {
                        0
                    },
                    collector,
                    var_manager,
                    proof,
                )?;
            }
            ObjEncoding::Unweighted(enc, offset) => {
                #[cfg(feature = "verbose-proofs")]
                proof.comment(&"extend totalizer")?;
                enc.encode_ub_change_cert(
                    if range.start >= *offset {
                        range.start - *offset
                    } else {
                        0
                    }..if range.end >= *offset {
                        range.end - *offset
                    } else {
                        0
                    },
                    collector,
                    var_manager,
                    proof,
                )?;
            }
            ObjEncoding::Constant => (),
        }
        Ok(())
    }
}

impl ObjEncoding<pb::DbGte, card::DbTotalizer> {
    pub fn output_proof_details(&self, value: usize) -> (Lit, totdb::cert::SemDefs) {
        match self {
            ObjEncoding::Weighted(enc, offset) => {
                enc.output_proof_details(value - *offset).unwrap()
            }
            ObjEncoding::Unweighted(enc, offset) => {
                enc.output_proof_details(value - *offset).unwrap()
            }
            ObjEncoding::Constant => {
                panic!("cannot get output proof details for constant objective")
            }
        }
    }

    pub fn extend_assignment<'slf>(
        &'slf self,
        assign: &'slf Assignment,
    ) -> impl Iterator<Item = Lit> + 'slf {
        match self {
            ObjEncoding::Weighted(enc, _) => enc.strictly_extend_assignment(assign),
            ObjEncoding::Unweighted(enc, _) => enc.strictly_extend_assignment(assign),
            ObjEncoding::Constant => None.into_iter().flatten(),
        }
    }

    pub fn is_buffer_empty(&self) -> bool {
        match self {
            ObjEncoding::Weighted(enc, _) => enc.is_buffer_empty(),
            ObjEncoding::Unweighted(_, _) | ObjEncoding::Constant => true,
        }
    }

    pub fn n_output_lits(&self) -> usize {
        match self {
            ObjEncoding::Weighted(enc, _) => enc.n_output_lits(),
            ObjEncoding::Unweighted(enc, _) => enc.n_output_lits(),
            ObjEncoding::Constant => 0,
        }
    }
}

#[cfg(feature = "sol-tightening")]
/// Data regarding an objective literal
pub(crate) struct ObjLitData {
    /// Objectives that the literal appears in
    pub objs: Vec<usize>,
}

#[derive(Debug, Clone, Copy)]
pub struct VarManager {
    next_var: Var,
    max_orig_var: Var,
    max_enc_var: Var,
}

impl VarManager {
    /// Creates a new varaible manager, keeping track of different variable types
    ///
    /// - `max_orig_var` is the maximum variable in the _original_ instance, (e.g., the OPB file)
    /// - `max_enc_var` is the maximum variable in the encoded CNF instance with a linear
    ///     objective, i.e., this might include variables used for encoding PB constraints and for
    ///     relaxing soft clauses
    ///
    /// # Panics
    ///
    /// If `max_enc_var < max_orig_var`
    pub fn new(max_orig_var: Var, max_enc_var: Var) -> Self {
        assert!(max_enc_var >= max_orig_var);
        VarManager {
            max_orig_var,
            max_enc_var,
            next_var: max_enc_var + 1,
        }
    }

    pub(crate) fn mark_max_orig_var(&mut self) {
        self.max_orig_var = self.next_var - 1;
        self.max_enc_var = cmp::max(self.max_enc_var, self.max_orig_var);
    }

    pub(crate) fn mark_max_enc_var(&mut self) {
        self.max_enc_var = self.next_var - 1;
    }

    pub fn max_orig_var(&self) -> Var {
        self.max_orig_var
    }

    pub fn max_enc_var(&self) -> Var {
        self.max_enc_var
    }
}

impl Default for VarManager {
    fn default() -> Self {
        Self {
            next_var: Var::new(0),
            max_orig_var: Var::new(0),
            max_enc_var: Var::new(0),
        }
    }
}

impl ManageVars for VarManager {
    fn new_var(&mut self) -> Var {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    fn max_var(&self) -> Option<Var> {
        if self.next_var == Var::new(0) {
            None
        } else {
            Some(self.next_var - 1)
        }
    }

    fn increase_next_free(&mut self, v: Var) -> bool {
        if v > self.next_var {
            self.next_var = v;
            return true;
        };
        false
    }

    fn combine(&mut self, other: Self) {
        if other.next_var > self.next_var {
            self.next_var = other.next_var;
        };
    }

    fn n_used(&self) -> u32 {
        self.next_var.idx32()
    }

    fn forget_from(&mut self, min_var: Var) {
        self.next_var = std::cmp::min(self.next_var, min_var);
    }
}

/// Manager for reindexing an existing instance
#[derive(PartialEq, Eq)]
pub struct Reindexer {
    next_var: Var,
    in_map: RsHashMap<Var, Var>,
    out_map: Vec<Var>,
    old_max_orig_var: Var,
}

impl Reindexer {
    pub fn new(old_max_orig_var: Var) -> Self {
        Reindexer {
            next_var: Var::new(0),
            in_map: RsHashMap::default(),
            out_map: Vec::default(),
            old_max_orig_var,
        }
    }

    pub fn old_max_orig_var(&self) -> Var {
        self.old_max_orig_var
    }
}

impl ReindexVars for Reindexer {
    fn reindex(&mut self, in_var: Var) -> Var {
        if let Some(v) = self.in_map.get(&in_var) {
            *v
        } else {
            let v = self.new_var();
            self.in_map.insert(in_var, v);
            self.out_map.push(in_var);
            v
        }
    }

    fn reverse(&self, out_var: Var) -> Option<Var> {
        if out_var.idx() >= self.out_map.len() {
            return None;
        }
        Some(self.out_map[out_var.idx()])
    }
}

impl ManageVars for Reindexer {
    fn new_var(&mut self) -> Var {
        let v = self.next_var;
        self.next_var = v + 1;
        v
    }

    fn max_var(&self) -> Option<Var> {
        if self.next_var == Var::new(0) {
            None
        } else {
            Some(self.next_var - 1)
        }
    }

    fn increase_next_free(&mut self, v: Var) -> bool {
        if v > self.next_var {
            self.next_var = v;
            return true;
        };
        false
    }

    fn combine(&mut self, other: Self) {
        if other.next_var > self.next_var {
            self.next_var = other.next_var;
        };
        self.in_map.extend(other.in_map);
    }

    fn n_used(&self) -> u32 {
        self.next_var.idx32()
    }

    fn forget_from(&mut self, min_var: Var) {
        self.in_map.retain(|_, v| *v < min_var);
        self.out_map.truncate(min_var.idx() + 1);
        self.next_var = std::cmp::min(self.next_var, min_var);
    }
}

#[derive(Debug, Clone)]
pub struct Parsed {
    pub(crate) constraints: Vec<PbConstraint>,
    pub(crate) objs: Vec<rustsat::instances::Objective>,
    pub(crate) vm: VarManager,
}

#[derive(Debug, Clone)]
pub struct Instance {
    pub(crate) clauses: Vec<(Clause, Option<pigeons::AbsConstraintId>)>,
    pub(crate) objs: Vec<Objective>,
    pub(crate) vm: VarManager,
}

impl Instance {
    pub fn n_clauses(&self) -> usize {
        self.clauses.len()
    }

    pub fn n_objs(&self) -> usize {
        self.objs.len()
    }

    pub fn iter_clauses(&self) -> impl Iterator<Item = &Clause> {
        self.clauses.iter().map(|(cl, _)| cl)
    }
}
