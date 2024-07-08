//! # Core-Guided Search Functionality

use rustsat::{
    encodings::{
        card::dbtotalizer::{INode, Node, TotDb},
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
    },
    instances::{Cnf, ManageVars},
    solvers::{
        SolveIncremental, SolveStats,
        SolverResult::{Interrupted, Sat, Unsat},
    },
    types::{Assignment, Lit, RsHashMap, RsHashSet},
};
use scuttle_proc::oracle_bounds;

use crate::MaybeTerminatedError::{self, Done};

use super::{Objective, SolverKernel};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TotOutput {
    pub root: NodeId,
    pub oidx: usize,
    pub tot_weight: usize,
}

#[derive(Default, Clone, PartialEq, Eq, Debug)]
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
        if let Inactives::Unweighted { lits, .. } = self {
            let mut set = RsHashSet::default();
            for l in lits {
                if set.contains(&l) {
                    // change to weighted
                    *self = Inactives::Weighted(std::mem::take(self).into_map());
                    break;
                }
                set.insert(l);
            }
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

    pub fn add(&mut self, lit: Lit, weight: usize) {
        debug_assert!(weight > 0);
        match self {
            Inactives::Weighted(map) => {
                if let Some(w) = map.get_mut(&lit) {
                    *w += weight;
                } else {
                    map.insert(lit, weight);
                }
            }
            Inactives::Unweighted { lits, .. } => {
                if weight > 1 {
                    *self = Inactives::Weighted(std::mem::take(self).into_map());
                    self.insert(lit, weight);
                    return;
                }
                lits.push(lit);
            }
            Inactives::Constant => {
                if weight > 1 {
                    *self = Inactives::Weighted(RsHashMap::default());
                } else {
                    *self = Inactives::Unweighted {
                        lits: vec![],
                        active: RsHashSet::default(),
                    };
                }
                self.insert(lit, weight);
            }
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
            Inactives::Unweighted { lits, .. } => {
                let mut map = RsHashMap::default();
                for l in lits {
                    if let Some(w) = map.get_mut(&l) {
                        *w += 1;
                    } else {
                        map.insert(l, 1);
                    }
                }
                map
            }
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

#[derive(Default, Clone, PartialEq, Eq, Debug)]
pub struct OllReformulation {
    /// Inactive literals, aka the reformulated objective
    pub inactives: Inactives,
    /// Mapping totalizer output assumption to totalizer data
    pub outputs: RsHashMap<Lit, TotOutput>,
    /// The constant offset derived by the reformulation
    pub offset: usize,
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

impl OllReformulation {
    /// Extends the reformulation with another reformulation
    pub fn extend(&mut self, other: &OllReformulation) {
        for (l, w) in other.inactives.iter() {
            self.inactives.add(*l, *w);
        }
        for (l, out) in &other.outputs {
            debug_assert!(!self.outputs.contains_key(l));
            self.outputs.insert(*l, *out);
        }
        self.offset += other.offset;
    }
}

struct CoreData {
    idx: usize,
    len: usize,
    weight: usize,
}

#[oracle_bounds]
impl<VM, O, BCG> SolverKernel<VM, O, BCG>
where
    VM: ManageVars,
    O: SolveIncremental + SolveStats,
{
    /// OLL core-guided search over an objective. The implementation includes the following
    /// refinements:
    /// - Weight-aware core extraction
    /// - Core trimming
    /// - Core exhaustion
    /// When using base assumptions, the user has to guarantee that a potential
    /// subsequent call is only made with tighter constraints.
    pub fn oll(
        &mut self,
        reform: &mut OllReformulation,
        base_assumps: &[Lit],
        tot_db: &mut TotDb,
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
                        self.log_routine_end()?;
                        return Done(Some(sol));
                    }
                    // TODO: maybe get solution and do hardening
                    // Reformulate cores
                    let mut encs = Cnf::new();
                    for CoreData { idx, len, weight } in unreform_cores.drain(..) {
                        let con = tot_db.merge(&core_cons[idx..idx + len]);
                        debug_assert_eq!(con.offset(), 0);
                        debug_assert_eq!(con.multiplier(), 1);
                        let root = con.id;
                        let oidx = self.exhaust_core(root, base_assumps, tot_db)?;
                        if oidx > 1 {
                            reform.offset += (oidx - 1) * weight;
                            if let Some(log) = &mut self.logger {
                                log.log_core_exhaustion(oidx, weight)?;
                            }
                        }
                        if oidx < tot_db[root].len() {
                            let olit = tot_db.define_pos_tot(
                                root,
                                oidx,
                                &mut encs,
                                &mut self.var_manager,
                            )?;
                            reform.inactives.insert(olit, weight);
                            reform.outputs.insert(
                                olit,
                                TotOutput {
                                    root,
                                    oidx,
                                    tot_weight: weight,
                                },
                            );
                            assumps.push(!olit);
                        }
                    }
                    self.oracle.add_cnf(encs)?;
                    core_cons.clear();
                }
                Unsat => {
                    let mut core = self.oracle.core()?;
                    if !base_assumps.is_empty() {
                        // filter out base assumptions
                        // !!! Note: this relies on the fact that the core is in the same order as the
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
                    let orig_len = core.len();
                    core = self.minimize_core(core, base_assumps)?;
                    core = self.trim_core(core, base_assumps)?;
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
                    let mut encs = Cnf::new();
                    let mut cons = Vec::with_capacity(core.len());
                    for olit in &core {
                        let inact_weight = reform.inactives.relax(*olit, core_weight);
                        if let Some(&TotOutput {
                            root,
                            oidx,
                            tot_weight,
                        }) = reform.outputs.get(olit)
                        {
                            cons.push(NodeCon::single(root, oidx + 1, 1));
                            if inact_weight > 0 {
                                continue;
                            }
                            // remove old output to only have one entry per totalizer in outputs
                            // map
                            reform.outputs.remove(olit);
                            if oidx + 1 >= tot_db[root].len() {
                                continue;
                            }
                            let new_olit = tot_db.define_pos_tot(
                                root,
                                oidx + 1,
                                &mut encs,
                                &mut self.var_manager,
                            )?;
                            reform.inactives.insert(new_olit, tot_weight);
                            reform.outputs.insert(
                                new_olit,
                                TotOutput {
                                    root,
                                    oidx: oidx + 1,
                                    tot_weight,
                                },
                            );
                            assumps.push(!new_olit);
                        } else {
                            let id = tot_db.insert(Node::leaf(*olit));
                            cons.push(NodeCon::full(id));
                        }
                    }
                    debug_assert_eq!(core.len(), cons.len());
                    self.oracle.add_cnf(encs)?;
                    if cons.len() > 1 {
                        // Save core for reformulation
                        unreform_cores.push(CoreData {
                            idx: core_cons.len(),
                            len: cons.len(),
                            weight: core_weight,
                        });
                        core_cons.extend(cons);
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
    ) -> MaybeTerminatedError<usize> {
        if !self.opts.core_exhaustion {
            return Done(1);
        }

        self.log_routine_start("core-exhaustion")?;

        let mut assumps = Vec::from(base_assumps);
        assumps.push(Lit::positive(0));

        let mut bound = 1;
        let core_len = tot_db[root].len();
        while bound < core_len {
            let olit =
                tot_db.define_pos_tot(root, bound, &mut self.oracle, &mut self.var_manager)?;
            #[cfg(feature = "limit-conflicts")]
            self.oracle.limit_conflicts(Some(50000))?;
            assumps[base_assumps.len()] = !olit;
            let res = self.solve_assumps(&assumps)?;
            if res != Unsat {
                break;
            }
            bound += 1;
        }

        #[cfg(feature = "limit-conflicts")]
        self.oracle.limit_conflicts(None)?;
        self.log_routine_end()?;
        Done(bound)
    }

    /// Minimizes a core
    fn minimize_core(
        &mut self,
        mut core: Vec<Lit>,
        base_assumps: &[Lit],
    ) -> MaybeTerminatedError<Vec<Lit>> {
        if !self.opts.core_minimization {
            return Done(core);
        }
        if core.len() <= 1 {
            return Done(core);
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
                    // !!! Note: this relies on the fact that the core is in the same order as the
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
            }
            assumps.drain(base_assumps.len()..);
        }

        #[cfg(feature = "limit-conflicts")]
        self.oracle.limit_conflicts(None)?;
        self.log_routine_end()?;
        Done(core)
    }

    /// Trims a core
    fn trim_core(
        &mut self,
        mut core: Vec<Lit>,
        base_assumps: &[Lit],
    ) -> MaybeTerminatedError<Vec<Lit>> {
        if !self.opts.core_trimming {
            return Done(core);
        }
        if core.len() <= 1 {
            return Done(core);
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
                // !!! Note: this relies on the fact that the core is in the same order as the
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
            if core.len() == size_before {
                break;
            }
            assumps.drain(base_assumps.len()..);
        }

        self.log_routine_end()?;

        Done(core)
    }
}
