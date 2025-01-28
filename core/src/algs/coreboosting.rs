//! # Core Boosting as Preprocessing

use std::io;

use maxpre::{MaxPre, PreproClauses};
use rustsat::{
    clause,
    encodings::{
        card::{self, DbTotalizer},
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        pb::{self, DbGte},
        totdb::{Db as TotDb, Node, Semantics},
    },
    instances::ManageVars,
    solvers::{Initialize, SolveIncremental, SolveStats},
    types::RsHashMap,
};
use scuttle_proc::oracle_bounds;

use crate::{
    termination::ensure,
    MaybeTerminatedError::{self, Done},
};

use super::{
    coreguided::{Inactives, OllReformulation, ReformData},
    Kernel, ObjEncoding, Objective,
};

pub(super) trait MergeOllRef {
    type PBE: pb::BoundUpperIncremental;
    type CE: card::BoundUpperIncremental;

    /// Merges totalizer node connections into an objective encoding.
    fn merge_cons(
        cons: Vec<NodeCon>,
        tot_db: TotDb,
        offset: usize,
        max_leaf_weight: usize,
    ) -> ObjEncoding<Self::PBE, Self::CE>;

    /// Merges the current OLL reformulation into an objective encoding. If
    /// `rebase` is true, does not perform a merge but uses all totalizer
    /// outputs as individual input literals to the encoding, if applicable.
    fn merge(
        reform: OllReformulation,
        tot_db: TotDb,
        rebase: bool,
    ) -> ObjEncoding<Self::PBE, Self::CE>;
}

impl MergeOllRef for (DbGte, DbTotalizer) {
    type PBE = DbGte;
    type CE = DbTotalizer;

    fn merge_cons(
        mut cons: Vec<NodeCon>,
        mut tot_db: TotDb,
        offset: usize,
        max_leaf_weight: usize,
    ) -> ObjEncoding<Self::PBE, Self::CE> {
        let root = tot_db.merge_thorough(&mut cons);
        if root.multiplier() == 1 {
            match &tot_db[root.id] {
                Node::Leaf(_) | Node::Unit(_) => ObjEncoding::Unweighted(
                    DbTotalizer::from_raw(root.id, root.offset(), tot_db),
                    offset,
                ),
                Node::General(_) => {
                    debug_assert!(root.offset() == 0);
                    ObjEncoding::Weighted(DbGte::from_raw(root, tot_db, max_leaf_weight), offset)
                }
                Node::Dummy => unreachable!(),
            }
        } else {
            ObjEncoding::Weighted(DbGte::from_raw(root, tot_db, max_leaf_weight), offset)
        }
    }

    fn merge(
        reform: OllReformulation,
        mut tot_db: TotDb,
        rebase: bool,
    ) -> ObjEncoding<Self::PBE, Self::CE> {
        if matches!(reform.inactives, Inactives::Constant) {
            // core boosting derived constant objective
            return ObjEncoding::Constant;
        }
        let mut cons = vec![];
        let mut max_leaf_weight = 0;
        for (lit, &weight) in &reform.inactives {
            max_leaf_weight = std::cmp::max(weight, max_leaf_weight);
            if let Some(&ReformData {
                root,
                oidx,
                tot_weight,
                ..
            }) = reform.reformulations.get(lit)
            {
                debug_assert_ne!(weight, 0);
                debug_assert!(oidx < tot_db[root].len());
                max_leaf_weight = std::cmp::max(tot_weight, max_leaf_weight);
                if rebase {
                    // ignore totalizer structure
                    cons.push(NodeCon::single(root, oidx + 1, weight));
                    for idx in oidx + 1..tot_db[root].len() {
                        cons.push(NodeCon::single(root, idx + 1, tot_weight));
                    }
                } else {
                    // preserve totalizer structure
                    if tot_weight == weight {
                        cons.push(NodeCon::offset_weighted(root, oidx, weight))
                    } else {
                        cons.push(NodeCon::single(root, oidx + 1, weight));
                        if oidx + 1 < tot_db[root].len() {
                            cons.push(NodeCon::offset_weighted(root, oidx + 1, tot_weight))
                        }
                    }
                }
            } else {
                let node = tot_db.insert(Node::Leaf(*lit));
                cons.push(NodeCon::weighted(node, weight));
            }
        }
        Self::merge_cons(cons, tot_db, reform.offset, max_leaf_weight)
    }
}

impl<'learn, 'term, ProofW, OInit, BCG>
    Kernel<rustsat_cadical::CaDiCaL<'learn, 'term>, ProofW, OInit, BCG>
where
    ProofW: io::Write + 'static,
{
    /// Performs core boosting on the instance by executing single-objective OLL
    /// on each objective individually. Returns the OLL reformulations or
    /// [`None`], if unsat.
    pub fn core_boost(&mut self) -> MaybeTerminatedError<Option<Vec<(OllReformulation, TotDb)>>> {
        self.log_routine_start("core boost")?;
        let mut unsat = false;
        let mut res = Vec::with_capacity(self.stats.n_objs);
        for obj_idx in 0..self.stats.n_objs {
            let mut reform = (&self.objs[obj_idx]).into();
            let mut tot_db = TotDb::default();
            if !matches!(self.objs[obj_idx], Objective::Constant { .. }) {
                match self.oll(&mut reform, &[], &mut tot_db, true)? {
                    Some(_) => (), // TODO: maybe make use of solution?
                    None => {
                        unsat = true;
                        break;
                    }
                };
            }

            if let Some(super::proofs::ProofStuff { pt_handle, .. }) = &self.proof_stuff {
                let proof = self.oracle.proof_tracer_mut(pt_handle).proof_mut();
                // check that the reformulation is correct
                #[cfg(feature = "verbose-proofs")]
                if let Some(reform_id) = reform.reform_id {
                    let tot_db_ref = &tot_db;
                    proof.comment(&format_args!(
                        "check oll reformulation constraint for objective {obj_idx}"
                    ))?;
                    proof.equals(
                        &rustsat::types::constraints::PbConstraint::new_lb(
                            self.objs[obj_idx]
                                .iter()
                                .map(|(l, w)| (l, isize::try_from(w).unwrap()))
                                .chain(
                                    reform
                                        .inactives
                                        .iter()
                                        .map(|(&l, &w)| (l, -isize::try_from(w).unwrap())),
                                )
                                .chain(reform.reformulations.values().flat_map(
                                    |&ReformData {
                                         root,
                                         oidx,
                                         tot_weight,
                                         ..
                                     }| {
                                        (oidx + 2..=tot_db[root].max_val()).map(move |val| {
                                            (
                                                tot_db_ref[root][val],
                                                -isize::try_from(tot_weight).unwrap(),
                                            )
                                        })
                                    },
                                )),
                            isize::try_from(reform.offset).unwrap(),
                        ),
                        Some(pigeons::ConstraintId::from(reform_id)),
                    )?;
                }

                // peculiar case where we only have one oll totalizer as the final encoding, need to
                // ensure we have the pseudo semantics defined
                if reform.inactives.len() == 1 && reform.reformulations.len() == 1 {
                    let reform_data = reform.reformulations.values().next().unwrap();
                    if tot_db[reform_data.root].max_val() - reform_data.oidx > 1 {
                        // if only one literal, the semantics are defined on the fly and not cached
                        let leafs: Vec<_> = (reform_data.oidx + 1
                            ..=tot_db[reform_data.root].max_val())
                            .map(|val| (tot_db[reform_data.root][val], 1))
                            .collect();
                        tot_db.ensure_semantics(
                            reform_data.root,
                            reform_data.oidx,
                            reform_data.oidx + 1,
                            leafs.into_iter(),
                            proof,
                        )?;
                    }
                }
            }

            self.objs[obj_idx].set_reform_id(reform.reform_id);
            self.objs[obj_idx].set_lower_bound(reform.offset);
            res.push((reform, tot_db));
        }
        self.log_routine_end()?;
        if let Some(logger) = &mut self.logger {
            let ideal: Vec<_> = res.iter().map(|reform| reform.0.offset).collect();
            logger.log_ideal(&ideal)?;
        }
        Done(if unsat { None } else { Some(res) })
    }
}

#[oracle_bounds]
impl<O, ProofW, OInit, BCG> Kernel<O, ProofW, OInit, BCG>
where
    O: SolveIncremental + SolveStats,
    ProofW: io::Write,
    OInit: Initialize<O>,
{
    /// Performs inprocessing, i.e., preprocessing with MaxPre after core boosting.
    pub fn inprocess<PBE, CE>(
        &mut self,
        techniques: &str,
        mut reforms: Vec<(OllReformulation, TotDb)>,
    ) -> MaybeTerminatedError<Vec<ObjEncoding<PBE, CE>>>
    where
        (PBE, CE): MergeOllRef<PBE = PBE, CE = CE>,
    {
        debug_assert!(self.proof_stuff.is_none());

        ensure!(
            self.opts.store_cnf,
            "cannot reset oracle without having stored the CNF"
        );
        // Reset oracle
        self.oracle = OInit::init();
        #[cfg(feature = "interrupt-oracle")]
        {
            *self.oracle_interrupter.lock().unwrap() = Box::new(self.oracle.interrupter());
        }
        // Collect instance with reformulated objectives
        let mut orig_cnf = self.orig_cnf.clone().unwrap();
        let mut all_outputs: Vec<_> = reforms
            .iter()
            .map(|reform| reform.0.reformulations.clone())
            .collect();
        let mut objs = Vec::with_capacity(reforms.len());
        for (obj_idx, (reform, tot_db)) in reforms.iter_mut().enumerate() {
            tot_db.reset_encoded(Semantics::IfAndOnlyIf);
            let mut softs = Vec::with_capacity(reform.inactives.len());
            for (lit, weight) in reform.inactives.iter() {
                if let Some(ReformData {
                    root,
                    oidx,
                    tot_weight,
                    proof_id,
                }) = reform.reformulations.get(lit)
                {
                    for idx in *oidx..tot_db[*root].len() {
                        let olit = tot_db.define_unweighted(
                            *root,
                            idx,
                            Semantics::If,
                            &mut orig_cnf,
                            &mut self.var_manager,
                        )?;
                        if idx == *oidx {
                            softs.push((clause![!olit], *weight));
                        } else {
                            all_outputs[obj_idx].insert(
                                olit,
                                ReformData {
                                    root: *root,
                                    oidx: idx,
                                    tot_weight: *tot_weight,
                                    proof_id: *proof_id,
                                },
                            );
                            softs.push((clause![!olit], *tot_weight));
                        }
                    }
                } else {
                    softs.push((clause![!*lit], *weight));
                };
            }
            objs.push((softs, 0));
        }
        // Inprocess
        self.log_routine_start("inprocessing")?;
        let cls_before = orig_cnf.len() + objs.iter().fold(0, |cnt, (obj, _)| cnt + obj.len());
        let mut ranges: Vec<_> = objs
            .iter()
            .map(|(obj, _)| (obj.iter().fold(0, |rng, (_, w)| rng + w), 0))
            .collect();
        let mut inpro = MaxPre::new(orig_cnf, objs, true);
        inpro.preprocess(techniques, 0, 1e9);
        let (inpro_cnf, inpro_objs) = inpro.prepro_instance();
        inpro_objs
            .iter()
            .zip(ranges.iter_mut())
            .for_each(|((obj, _), (_, after))| *after = obj.iter().fold(0, |rng, (_, w)| rng + w));
        self.log_routine_end()?;
        if let Some(logger) = self.logger.as_mut() {
            logger.log_inprocessing(
                (cls_before, inpro.n_prepro_clauses() as usize),
                inpro.n_prepro_fixed_lits() as usize,
                ranges,
            )?;
        }
        self.inpro = Some(inpro);
        self.check_termination()?;
        // Reinit oracle
        self.oracle.reserve(self.var_manager.max_var().unwrap())?;
        self.oracle.add_cnf(inpro_cnf)?;
        #[cfg(feature = "sol-tightening")]
        // Freeze objective variables so that they are not removed
        for (o, _) in &inpro_objs {
            for (cl, _) in o.iter() {
                debug_assert_eq!(cl.len(), 1);
                self.oracle.freeze_var(cl[0].var())?;
            }
        }
        self.check_termination()?;
        // Build encodings
        let mut encs = Vec::with_capacity(self.stats.n_objs);
        for (obj_idx, ((softs, offset), (reform, mut tot_db))) in
            inpro_objs.into_iter().zip(reforms).enumerate()
        {
            debug_assert!(offset >= 0);
            let outputs = &all_outputs[obj_idx];
            let mut tots_to_add: RsHashMap<NodeId, (Vec<bool>, usize)> = RsHashMap::default();
            let mut cons = vec![];
            if softs.is_empty() {
                self.objs[obj_idx] = Objective::Constant {
                    offset: self.objs[obj_idx].offset() + reform.offset as isize + offset,
                    idx: obj_idx,
                    lower_bound: reform.offset,
                    reform_id: reform.reform_id,
                };
                continue;
            }
            let mut max_leaf_weight = 0;
            for (cl, w) in softs {
                debug_assert_eq!(cl.len(), 1);
                max_leaf_weight = std::cmp::max(w, max_leaf_weight);
                let olit = !cl[0];
                if let Some(ReformData {
                    root,
                    oidx,
                    tot_weight,
                    ..
                }) = outputs.get(&olit)
                {
                    if w < *tot_weight {
                        cons.push(NodeCon::single(*root, oidx + 1, w));
                        continue;
                    }
                    if let Some((tot_data, _)) = tots_to_add.get_mut(root) {
                        debug_assert!(!tot_data[*oidx]);
                        tot_data[*oidx] = true;
                    } else {
                        let mut dat = vec![false; tot_db[*root].len()];
                        dat[*oidx] = true;
                        tots_to_add.insert(*root, (dat, *tot_weight));
                    }
                } else {
                    // original obj literal or introduced by inprocessing
                    let node = tot_db.insert(Node::Leaf(olit));
                    cons.push(NodeCon::weighted(node, w));
                }
            }
            // actually build the encoding
            self.log_routine_start("merge encodings")?;
            for (root, (data, weight)) in tots_to_add {
                let mut offset = usize::MAX;
                let mut len = None;
                for (oidx, active) in data.into_iter().enumerate() {
                    if active && oidx < offset {
                        offset = oidx;
                    }
                    if !active && oidx > offset {
                        len = Some(oidx - offset)
                    }
                    if active && len.is_some() {
                        panic!("found gap in totalizer")
                    }
                }
                if let Some(len) = len {
                    cons.push(NodeCon::limited(root, offset, len, weight));
                } else {
                    cons.push(NodeCon::offset_weighted(root, offset, weight));
                }
            }
            self.check_termination()?;
            encs.push(<(PBE, CE)>::merge_cons(
                cons,
                tot_db,
                reform.offset + (offset as usize),
                max_leaf_weight,
            ));
            self.log_routine_end()?;
        }
        Done(encs)
    }
}
