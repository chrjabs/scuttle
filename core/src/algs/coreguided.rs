//! # Core-Guided Search Functionality

use std::io;

use cadical_veripb_tracer::CadicalCertCollector;
use pigeons::{AbsConstraintId, ConstraintId, OperationSequence};
use rustsat::{
    encodings::{
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        totdb::{Db as TotDb, Node, Semantics},
    },
    instances::ManageVars,
    solvers::{
        LimitConflicts, Solve, SolveIncremental,
        SolverResult::{Interrupted, Sat, Unsat},
    },
    types::{Assignment, Clause, Lit, RsHashMap, RsHashSet, Var},
};

use crate::{
    algs::proofs,
    MaybeTerminatedError::{self, Done},
};

use super::{Kernel, Objective};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReformData {
    pub root: NodeId,
    pub oidx: usize,
    pub tot_weight: usize,
    pub proof_id: Option<pigeons::AbsConstraintId>,
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub enum Inactives {
    Weighted(RsHashMap<Lit, usize>),
    Unweighted {
        lits: Vec<Lit>,
        active: RsHashSet<Lit>,
    },
    #[default]
    Constant,
}

impl Inactives {
    pub fn iter(&self) -> InactIter {
        self.into()
    }

    pub fn assumps(&self) -> impl Iterator<Item = Lit> + '_ {
        self.iter().map(|(&l, _)| !l)
    }

    pub fn len(&self) -> usize {
        match self {
            Inactives::Weighted(map) => map.len(),
            Inactives::Unweighted { lits, .. } => lits.len(),
            Inactives::Constant => 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            Inactives::Weighted(map) => map.is_empty(),
            Inactives::Unweighted { lits, .. } => lits.is_empty(),
            Inactives::Constant => true,
        }
    }

    pub fn final_cleanup(&mut self) {
        self.cleanup();
        let to_constant = match self {
            Inactives::Weighted(map) => map.is_empty(),
            Inactives::Unweighted { lits, .. } => lits.is_empty(),
            Inactives::Constant => false,
        };
        if to_constant {
            *self = Inactives::Constant;
        }
    }

    pub fn cleanup(&mut self) {
        match self {
            Inactives::Weighted(map) => map.retain(|_, w| *w > 0),
            Inactives::Unweighted { lits, active } => {
                lits.retain(|l| !active.contains(l));
                active.clear();
            }
            Inactives::Constant => (),
        }
    }

    pub fn insert(&mut self, lit: Lit, weight: usize) {
        match self {
            Inactives::Weighted(map) => {
                map.insert(lit, weight);
            }
            Inactives::Unweighted { lits, .. } => {
                debug_assert_eq!(weight, 1);
                lits.push(lit);
            }
            Inactives::Constant => panic!(),
        }
    }

    pub fn relax(&mut self, lit: Lit, core_weight: usize) -> usize {
        match self {
            Inactives::Weighted(map) => {
                if let Some(lit_weight) = map.get_mut(&lit) {
                    *lit_weight -= core_weight;
                    *lit_weight
                } else {
                    panic!()
                }
            }
            Inactives::Unweighted { active, .. } => {
                debug_assert_eq!(core_weight, 1);
                active.insert(lit);
                0
            }
            Inactives::Constant => panic!(),
        }
    }

    pub fn into_map(mut self) -> RsHashMap<Lit, usize> {
        self.cleanup();
        match self {
            Inactives::Weighted(map) => map,
            Inactives::Unweighted { lits, .. } => lits.into_iter().map(|l| (l, 1)).collect(),
            Inactives::Constant => RsHashMap::default(),
        }
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Lit, &usize) -> bool,
    {
        match self {
            Inactives::Weighted(map) => map.retain(|l, w| f(l, w)),
            Inactives::Unweighted { lits, .. } => lits.retain(|l| f(l, &1)),
            Inactives::Constant => (),
        }
    }
}

impl<'a> IntoIterator for &'a Inactives {
    type Item = (&'a Lit, &'a usize);

    type IntoIter = InactIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub enum InactIter<'a> {
    Weighted(std::collections::hash_map::Iter<'a, Lit, usize>),
    Unweighted(std::slice::Iter<'a, Lit>),
    Constant,
}

impl<'a> From<&'a Inactives> for InactIter<'a> {
    fn from(value: &'a Inactives) -> Self {
        match value {
            Inactives::Weighted(map) => Self::Weighted(map.iter()),
            Inactives::Unweighted { lits, .. } => Self::Unweighted(lits.iter()),
            Inactives::Constant => Self::Constant,
        }
    }
}

impl<'a> Iterator for InactIter<'a> {
    type Item = (&'a Lit, &'a usize);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            InactIter::Weighted(iter) => iter.next(),
            InactIter::Unweighted(iter) => iter.next().map(|l| (l, &1)),
            InactIter::Constant => None,
        }
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct OllReformulation {
    /// Inactive literals, aka the reformulated objective
    pub inactives: Inactives,
    /// Mapping totalizer output assumption to totalizer data
    pub reformulations: RsHashMap<Lit, ReformData>,
    /// The constant offset derived by the reformulation
    pub offset: usize,
    /// The objective reformulation constraint in the proof
    pub reform_id: Option<AbsConstraintId>,
}

impl From<&Objective> for OllReformulation {
    fn from(value: &Objective) -> Self {
        match value {
            Objective::Weighted { lits, .. } => OllReformulation {
                inactives: Inactives::Weighted(lits.clone()),
                ..Default::default()
            },
            Objective::Unweighted { lits, .. } => OllReformulation {
                inactives: Inactives::Unweighted {
                    lits: lits.clone(),
                    active: Default::default(),
                },
                ..Default::default()
            },
            Objective::Constant { .. } => OllReformulation {
                ..Default::default()
            },
        }
    }
}

struct CoreData {
    idx: usize,
    len: usize,
    weight: usize,
    proof_id: Option<pigeons::AbsConstraintId>,
}

impl<'learn, 'term, ProofW, OInit, BCG>
    Kernel<rustsat_cadical::CaDiCaL<'learn, 'term>, ProofW, OInit, BCG>
where
    ProofW: io::Write + 'static,
{
    /// OLL core-guided search over an objective. The implementation includes the following
    /// refinements:
    /// - Weight-aware core extraction
    /// - Core trimming
    /// - Core exhaustion
    ///
    /// When using base assumptions, the user has to guarantee that a potential
    /// subsequent call is only made with tighter constraints.
    ///
    /// The `exact_reformulation` argument specifies whether in the proof, we want to have an
    /// exact objective reformulation including all lazy totalizer outputs, or only the ones built
    pub fn oll(
        &mut self,
        reform: &mut OllReformulation,
        base_assumps: &[Lit],
        tot_db: &mut TotDb,
        exact_reformulation: bool,
    ) -> MaybeTerminatedError<Option<Assignment>> {
        if matches!(reform.inactives, Inactives::Constant) {
            match self.solve_assumps(base_assumps)? {
                Sat => {
                    return Done(Some(
                        self.oracle.solution(self.var_manager.max_var().unwrap())?,
                    ))
                }
                Unsat => return Done(None),
                Interrupted => unreachable!(),
            }
        }
        self.log_routine_start("oll")?;

        // cores not yet reformulated (because of WCE)
        let mut unreform_cores = vec![];
        let mut core_cons = vec![];

        let mut assumps = Vec::from(base_assumps);
        // sort base assumptions for filtering them out efficiently
        assumps.sort_unstable();
        assumps.extend(reform.inactives.assumps());

        // need to keep track of reformulations that are not in the hash map anymore, namely unit
        // cores and fully built totalizers
        let mut reform_ids = vec![];

        loop {
            match &mut reform.inactives {
                Inactives::Weighted(inacts) => {
                    // Build assumptions sorted by weight
                    assumps[base_assumps.len()..]
                        .sort_unstable_by_key(|&l| -(inacts[&!l] as isize));
                    // Remove assumptions that turned active
                    while assumps.len() > base_assumps.len()
                        && inacts[&!assumps[assumps.len() - 1]] == 0
                    {
                        assumps.pop();
                    }
                }
                Inactives::Unweighted { .. } => {
                    reform.inactives.cleanup();
                    assumps.drain(base_assumps.len()..);
                    assumps.extend(reform.inactives.assumps());
                }
                Inactives::Constant => unreachable!(),
            }

            match self.solve_assumps(&assumps)? {
                Interrupted => unreachable!(),
                Sat => {
                    if unreform_cores.is_empty() {
                        let sol = self.oracle.solution(self.var_manager.max_var().unwrap())?;
                        reform.inactives.final_cleanup();

                        if exact_reformulation {
                            // reserve totalizer output variables since they are required for the pseudo
                            // semantics when proof logging
                            for &ReformData { root, oidx, .. } in reform.reformulations.values() {
                                tot_db[root].reserve_vars(oidx + 1.., &mut self.var_manager);
                            }
                        }

                        if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.proof_stuff {
                            let proof = self.oracle.proof_tracer_mut(pt_handle).proof_mut();
                            if exact_reformulation {
                                // extend reformulation ids to include _all_ totalizer outputs
                                for ReformData {
                                    root,
                                    oidx,
                                    proof_id,
                                    ..
                                } in reform.reformulations.values_mut()
                                {
                                    if *oidx + 1 >= tot_db[*root].len() {
                                        continue;
                                    };
                                    let mut reform_ops =
                                        OperationSequence::<Var>::from(proof_id.unwrap());
                                    let leafs: Vec<_> = tot_db.leaf_iter(*root).collect();
                                    for val in *oidx + 2..=tot_db[*root].max_val() {
                                        reform_ops *= val - 1;
                                        reform_ops += tot_db
                                            .ensure_semantics(
                                                *root,
                                                0,
                                                val,
                                                leafs.iter().copied(),
                                                proof,
                                            )?
                                            .only_if_def
                                            .unwrap();
                                        reform_ops /= val;
                                    }
                                    let new_id = proof.operations::<Var>(&reform_ops)?;
                                    proof.delete_ids::<Var, Clause, _, _>(
                                        [ConstraintId::from(proof_id.unwrap())],
                                        None,
                                    )?;
                                    *proof_id = Some(new_id);
                                }
                            }
                            // derive objective reformulation
                            let ops = reform_ids
                                .iter()
                                .fold(OperationSequence::<Var>::empty(), |seq, (c, w)| {
                                    seq + OperationSequence::<Var>::from(*c) * *w
                                });
                            let ops = reform.reformulations.values().fold(ops, |seq, re| {
                                seq + OperationSequence::<Var>::from(re.proof_id.unwrap())
                                    * re.tot_weight
                            });
                            if !ops.is_empty() {
                                #[cfg(feature = "verbose-proofs")]
                                proof.comment(&"final oll reformulation")?;
                                reform.reform_id = Some(proof.operations(&ops)?);
                                if !reform_ids.is_empty() {
                                    // delete fully exhausted reformulations
                                    proof.delete_ids::<Var, Clause, _, _>(
                                        reform_ids.into_iter().map(|(c, _)| ConstraintId::from(c)),
                                        None,
                                    )?;
                                }
                            }
                        }

                        self.log_routine_end()?;
                        return Done(Some(sol));
                    }
                    // NOTE: hardening is not sound for core boosting

                    // Reformulate cores
                    for CoreData {
                        idx,
                        len,
                        weight,
                        proof_id,
                    } in unreform_cores.drain(..)
                    {
                        let con = tot_db.merge(&core_cons[idx..idx + len]);
                        debug_assert_eq!(con.offset(), 0);
                        debug_assert_eq!(con.multiplier(), 1);
                        let root = con.id;
                        let (olit, oidx, proof_id) =
                            self.exhaust_core(root, base_assumps, tot_db, proof_id)?;
                        if oidx > 1 {
                            reform.offset += (oidx - 1) * weight;
                            if let Some(log) = &mut self.logger {
                                log.log_core_exhaustion(oidx, weight)?;
                            }
                        }
                        if oidx < tot_db[root].len() {
                            reform.inactives.insert(olit, weight);

                            reform.reformulations.insert(
                                olit,
                                ReformData {
                                    root,
                                    oidx,
                                    tot_weight: weight,
                                    proof_id,
                                },
                            );
                            assumps.push(!olit);
                        } else if let Some(proof_id) = proof_id {
                            reform_ids.push((proof_id, weight));
                        }
                    }
                    core_cons.clear();
                }
                Unsat => {
                    let mut core = self.oracle.core()?;

                    if !base_assumps.is_empty() {
                        // filter out base assumptions
                        // NOTE: this relies on the fact that the core is in the same order as the
                        // assumptions going into the solver
                        let mut base_assumps_idx = 0;
                        core.retain(|&lit| {
                            while base_assumps_idx < base_assumps.len()
                                && assumps[base_assumps_idx] < !lit
                            {
                                base_assumps_idx += 1;
                            }
                            if base_assumps_idx >= base_assumps.len()
                                || !lit != assumps[base_assumps_idx]
                            {
                                return true;
                            }
                            false
                        });
                    }
                    if core.is_empty() {
                        // unsat
                        self.log_routine_end()?;
                        return Done(None);
                    }

                    let mut core_id =
                        if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.proof_stuff {
                            let core_id = self.oracle.proof_tracer_mut(pt_handle).core_id();
                            debug_assert!(core_id.is_some());
                            core_id
                        } else {
                            None
                        };

                    let orig_len = core.len();
                    (core, core_id) = self.minimize_core(core, base_assumps, core_id)?;
                    (core, core_id) = self.trim_core(core, base_assumps, core_id)?;
                    let core_weight = match &reform.inactives {
                        Inactives::Weighted(inact) => core
                            .iter()
                            .fold(usize::MAX, |cw, l| std::cmp::min(cw, inact[l])),
                        Inactives::Unweighted { .. } => 1,
                        Inactives::Constant => unreachable!(),
                    };
                    reform.offset += core_weight;
                    // Log core
                    if let Some(log) = &mut self.logger {
                        log.log_core(core_weight, orig_len, core.len())?;
                    }
                    // Extend tot if output in core
                    let mut cons = Vec::with_capacity(core.len());
                    for olit in &core {
                        let inact_weight = reform.inactives.relax(*olit, core_weight);
                        if let Some(&ReformData {
                            root,
                            oidx,
                            tot_weight,
                            proof_id,
                        }) = reform.reformulations.get(olit)
                        {
                            cons.push(NodeCon::single(root, oidx + 1, 1));
                            if inact_weight > 0 {
                                continue;
                            }
                            // remove old output to only have one entry per totalizer in outputs
                            // map
                            reform.reformulations.remove(olit);
                            if oidx + 1 >= tot_db[root].len() {
                                // make sure to keep proof_id around
                                if let Some(proof_id) = proof_id {
                                    reform_ids.push((proof_id, tot_weight));
                                }
                                continue;
                            }
                            let new_olit = self.build_output(root, oidx + 1, tot_db)?;
                            reform.inactives.insert(new_olit, tot_weight);

                            let proof_id = if let Some(proofs::ProofStuff { pt_handle, .. }) =
                                &self.proof_stuff
                            {
                                // Extend reformulation in proof and delete old reformulation
                                // constraint
                                let proof_id = proof_id.expect(
                                    "expected a reformulation proof id while proof logging",
                                );
                                let proof = self.oracle.proof_tracer_mut(pt_handle).proof_mut();
                                #[cfg(feature = "verbose-proofs")]
                                proof.comment(&format_args!(
                                    "extending core reformulation {root} from oidx {oidx}"
                                ))?;
                                let only_if_def = tot_db
                                    .get_semantics(root, 0, oidx + 2)
                                    .unwrap()
                                    .only_if_def
                                    .unwrap();
                                let new_id = proof.operations::<Var>(
                                    &(((OperationSequence::from(proof_id) * (oidx + 1))
                                        + only_if_def)
                                        / (oidx + 2)),
                                )?;
                                proof.delete_ids::<Var, Clause, _, _>(
                                    [ConstraintId::from(proof_id)],
                                    None,
                                )?;
                                Some(new_id)
                            } else {
                                None
                            };

                            reform.reformulations.insert(
                                new_olit,
                                ReformData {
                                    root,
                                    oidx: oidx + 1,
                                    tot_weight,
                                    proof_id,
                                },
                            );
                            assumps.push(!new_olit);
                        } else {
                            let id = tot_db.insert(Node::Leaf(*olit));
                            cons.push(NodeCon::full(id));
                        }
                    }
                    debug_assert_eq!(core.len(), cons.len());

                    if cons.len() > 1 {
                        // Save core for reformulation
                        unreform_cores.push(CoreData {
                            idx: core_cons.len(),
                            len: cons.len(),
                            weight: core_weight,
                            proof_id: core_id,
                        });
                        core_cons.extend(cons);
                    } else if let Some(core_id) = core_id {
                        // keep track of units
                        reform_ids.push((core_id, core_weight));
                    }
                }
            }
        }
    }

    /// Exhausts a core
    fn exhaust_core(
        &mut self,
        root: NodeId,
        base_assumps: &[Lit],
        tot_db: &mut TotDb,
        core_id: Option<pigeons::AbsConstraintId>,
    ) -> MaybeTerminatedError<(Lit, usize, Option<pigeons::AbsConstraintId>)> {
        let mut proof_reform = core_id.map(OperationSequence::from);

        if !self.opts.core_exhaustion {
            let olit = self.build_output(root, 1, tot_db)?;
            let proof_id = if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.proof_stuff {
                let only_if_def = tot_db
                    .get_semantics(root, 0, 2)
                    .unwrap()
                    .only_if_def
                    .unwrap();
                Some(
                    self.oracle
                        .proof_tracer_mut(pt_handle)
                        .proof_mut()
                        .operations::<Var>(&((proof_reform.unwrap() + only_if_def) / 2))?,
                )
            } else {
                None
            };

            return Done((olit, 1, proof_id));
        }

        self.log_routine_start("core-exhaustion")?;

        let mut assumps = Vec::from(base_assumps);
        assumps.push(Lit::positive(0));

        let mut bound = 1;
        let mut olit = rustsat::lit![0];
        let core_len = tot_db[root].len();
        debug_assert!(core_len > bound);
        while bound < core_len {
            olit = self.build_output(root, bound, tot_db)?;

            if let Some(proof_reform) = &mut proof_reform {
                // Build up reformulation over core exhaustion
                let if_def = tot_db
                    .get_semantics(root, 0, bound + 1)
                    .unwrap()
                    .if_def
                    .unwrap();
                *proof_reform *= bound;
                *proof_reform += if_def;
                *proof_reform /= bound + 1;
            }

            #[cfg(feature = "limit-conflicts")]
            self.oracle.limit_conflicts(Some(50000))?;
            assumps[base_assumps.len()] = !olit;
            let res = self.solve_assumps(&assumps)?;
            if res != Unsat {
                break;
            }

            if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.proof_stuff {
                let proof_reform = proof_reform
                    .as_mut()
                    .expect("expected reformulation while proof logging");
                let core_id = self.oracle.proof_tracer_mut(pt_handle).core_id().unwrap();
                *proof_reform += core_id;
            }

            bound += 1;
        }

        #[cfg(feature = "limit-conflicts")]
        self.oracle.limit_conflicts(None)?;

        let proof_id = if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.proof_stuff {
            // Write the reformulation to the proof
            let proof_reform = proof_reform.expect("expected reformulation while proof logging");
            let proof = self.oracle.proof_tracer_mut(pt_handle).proof_mut();
            #[cfg(feature = "verbose-proofs")]
            proof.comment(&format_args!(
                "core reformulation from core exhaustion up to bound {bound}"
            ))?;
            Some(proof.operations::<Var>(&proof_reform)?)
        } else {
            None
        };

        self.log_routine_end()?;
        Done((olit, bound, proof_id))
    }

    /// Minimizes a core
    fn minimize_core(
        &mut self,
        mut core: Vec<Lit>,
        base_assumps: &[Lit],
        mut proof_id: Option<pigeons::AbsConstraintId>,
    ) -> MaybeTerminatedError<(Vec<Lit>, Option<pigeons::AbsConstraintId>)> {
        if !self.opts.core_minimization {
            return Done((core, proof_id));
        }
        if core.len() <= 1 {
            return Done((core, proof_id));
        }

        self.log_routine_start("core-minimization")?;

        let mut assumps = Vec::from(base_assumps);

        // **Note**: this assumes that the core is ordered by weight
        let sorted_core: Vec<_> = core.iter().rev().copied().collect();

        #[cfg(feature = "limit-conflicts")]
        self.oracle.limit_conflicts(Some(1000))?;
        for drop_lit in sorted_core {
            assumps.extend(core.iter().filter_map(|&l| {
                if l == drop_lit {
                    return None;
                }
                Some(!l)
            }));
            let ret = self.solve_assumps(&assumps)?;
            if ret == Unsat {
                core = self.oracle.core()?;
                if !base_assumps.is_empty() {
                    // filter out base assumptions
                    // NOTE: this relies on the fact that the core is in the same order as the
                    // assumptions going into the solver
                    let mut base_assumps_idx = 0;
                    core.retain(|&lit| {
                        while base_assumps_idx < base_assumps.len()
                            && assumps[base_assumps_idx] < !lit
                        {
                            base_assumps_idx += 1;
                        }
                        if base_assumps_idx >= base_assumps.len()
                            || !lit != assumps[base_assumps_idx]
                        {
                            return true;
                        }
                        false
                    });
                }
                proof_id = if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.proof_stuff {
                    let core_id = self.oracle.proof_tracer_mut(pt_handle).core_id();
                    debug_assert!(core_id.is_some());
                    core_id
                } else {
                    None
                };
            }
            assumps.drain(base_assumps.len()..);
        }

        #[cfg(feature = "limit-conflicts")]
        self.oracle.limit_conflicts(None)?;
        self.log_routine_end()?;
        Done((core, proof_id))
    }

    /// Trims a core
    fn trim_core(
        &mut self,
        mut core: Vec<Lit>,
        base_assumps: &[Lit],
        mut proof_id: Option<pigeons::AbsConstraintId>,
    ) -> MaybeTerminatedError<(Vec<Lit>, Option<pigeons::AbsConstraintId>)> {
        if !self.opts.core_trimming {
            return Done((core, proof_id));
        }
        if core.len() <= 1 {
            return Done((core, proof_id));
        }

        self.log_routine_start("core-trimming")?;

        let mut assumps = Vec::from(base_assumps);

        while core.len() > 1 {
            let size_before = core.len();
            assumps.extend(core.iter().map(|&l| !l));
            let ret = self.solve_assumps(&assumps)?;
            debug_assert_eq!(ret, Unsat);
            core = self.oracle.core()?;
            if !base_assumps.is_empty() {
                // filter out base assumptions
                // NOTE: this relies on the fact that the core is in the same order as the
                // assumptions going into the solver
                let mut base_assumps_idx = 0;
                core.retain(|&lit| {
                    while base_assumps_idx < base_assumps.len() && assumps[base_assumps_idx] < !lit
                    {
                        base_assumps_idx += 1;
                    }
                    if base_assumps_idx >= base_assumps.len() || !lit != assumps[base_assumps_idx] {
                        return true;
                    }
                    false
                });
            }
            proof_id = if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.proof_stuff {
                let core_id = self.oracle.proof_tracer_mut(pt_handle).core_id();
                debug_assert!(core_id.is_some());
                core_id
            } else {
                None
            };
            if core.len() == size_before {
                break;
            }
            assumps.drain(base_assumps.len()..);
        }

        self.log_routine_end()?;

        Done((core, proof_id))
    }

    /// Encode a totalzier output, either with or without proof logging
    fn build_output(
        &mut self,
        root: NodeId,
        oidx: usize,
        tot_db: &mut TotDb,
    ) -> anyhow::Result<Lit> {
        if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.proof_stuff {
            let proof: *mut _ = self.oracle.proof_tracer_mut(pt_handle).proof_mut();
            #[cfg(feature = "verbose-proofs")]
            {
                unsafe { &mut *proof }
                    .comment(&format_args!("extending totalizer {root} to {oidx}"))?;
            }
            let mut collector = CadicalCertCollector::new(&mut self.oracle, pt_handle);
            let mut leafs = vec![rustsat::lit![0]; tot_db[root].n_leafs()];
            tot_db
                .define_unweighted_cert(
                    root,
                    oidx,
                    Semantics::If,
                    &mut collector,
                    &mut self.var_manager,
                    unsafe { &mut *proof },
                    (&mut leafs, false, false),
                )
                .map(|(ol, _)| ol)
        } else {
            Ok(tot_db.define_unweighted(
                root,
                oidx,
                Semantics::If,
                &mut self.oracle,
                &mut self.var_manager,
            )?)
        }
    }
}
