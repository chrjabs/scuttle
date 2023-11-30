//! # Divide and Conquer Multi-Objective Optimization

use std::cell::RefCell;

use maxpre::{MaxPre, PreproClauses};
use rustsat::{
    clause,
    encodings::{
        atomics,
        card::{
            self,
            dbtotalizer::{Node, TotDb},
        },
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        pb::dbgte::referenced::{Gte, GteCell},
    },
    instances::{Cnf, ManageVars},
    solvers::{SolveIncremental, SolveStats, SolverResult},
    types::{Assignment, Clause, Lit, RsHashMap},
};
use scuttle_proc::oracle_bounds;

mod sequential;
pub use sequential::DivCon as SeqDivCon;

use crate::{types::NonDomPoint, Phase, Termination};

use super::{
    coreguided::{OllReformulation, TotOutput},
    lowerbounding::Fence,
    ObjEncoding, Objective, SolverKernel,
};

#[derive(Clone, Copy)]
struct ObjEncData {
    root: NodeCon,
    offset: usize,
    max_leaf_weight: usize,
    first_node: Option<NodeId>,
}

struct Worker<VM, O, BCG> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// The objective reformulations
    reforms: Vec<OllReformulation>,
    /// The objective encodings and an offset
    encodings: Vec<Option<ObjEncData>>,
    /// The totalizer database
    tot_db: TotDb,
}

impl<VM, O, BCG> Worker<VM, O, BCG> {
    /// Initializes the solver
    fn init(kernel: SolverKernel<VM, O, BCG>) -> Self {
        let mut reforms: Vec<_> = kernel.objs.iter().map(|obj| obj.into()).collect();
        reforms.shrink_to_fit();
        let mut encodings = vec![None; kernel.stats.n_objs];
        encodings.shrink_to_fit();
        Self {
            kernel,
            reforms,
            encodings,
            tot_db: Default::default(),
        }
    }
}

#[oracle_bounds]
impl<VM, O, BCG> Worker<VM, O, BCG>
where
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + SolveStats + Default,
{
    /// Finds the ideal point of the working instance under given assumptions for certain objectives by executing OLL
    /// single-objective optimization. Returns false if the entire pareto front
    /// was found.
    fn find_ideal(
        &mut self,
        assumps: &[Lit],
        obj_idxs: &[usize],
        ideal: &mut [usize],
    ) -> Result<bool, Termination> {
        self.kernel.log_routine_start("find_ideal")?;
        let mut cont = true;
        for &obj_idx in obj_idxs {
            let mut tmp_reform;
            let reform = if assumps.is_empty() {
                &mut self.reforms[obj_idx]
            } else {
                // under assumptions, don't keep the computed reformulation
                tmp_reform = self.reforms[obj_idx].clone();
                &mut tmp_reform
            };
            match self.kernel.oll(reform, assumps, &mut self.tot_db)? {
                Some(_) => (),
                None => {
                    cont = false;
                    break;
                }
            };
            // TODO: maybe make use of solution?
            ideal[obj_idx] = reform.offset;
        }
        self.kernel.log_routine_end()?;
        Ok(cont)
    }

    /// Solves a bi-objective subproblem with the BiOptSat algorithm. This is
    /// the recursion anchor solving the smallest subproblems. BiOptSat is run
    /// in the LSU variant.
    ///
    /// `starting_point`: optional starting point with known cost of increasing
    /// objective
    ///
    /// `lookup`: for a value of the increasing objective, checks if the
    /// non-dominated point has already been discovered and returns the
    /// corresponding value of the decreasing objective
    fn bioptsat<Lookup, Col>(
        &mut self,
        (inc_obj, dec_obj): (usize, usize),
        base_assumps: &[Lit],
        starting_point: Option<(usize, Assignment)>,
        (inc_lb, dec_lb): (Option<usize>, Option<usize>),
        lookup: Lookup,
        collector: &mut Col,
        rebase_encodings: bool,
    ) -> Result<(), Termination>
    where
        Lookup: Fn(usize) -> Option<usize>,
        Col: Extend<NonDomPoint>,
    {
        if self.encodings[inc_obj].is_none() {
            self.encodings[inc_obj] = Some(self.build_obj_encoding(inc_obj, rebase_encodings)?);
        }
        if self.encodings[dec_obj].is_none() {
            self.encodings[dec_obj] = Some(self.build_obj_encoding(dec_obj, rebase_encodings)?);
        }

        let tot_db_cell = RefCell::from(&mut self.tot_db);

        let mut inc_enc: ObjEncoding<_, card::DefIncUpperBounding> = ObjEncoding::Weighted(
            GteCell::new(
                self.encodings[inc_obj].as_ref().unwrap().root,
                self.encodings[inc_obj].as_ref().unwrap().max_leaf_weight,
                &tot_db_cell,
            ),
            self.encodings[inc_obj].as_ref().unwrap().offset,
        );
        let mut dec_enc: ObjEncoding<_, card::DefIncUpperBounding> = ObjEncoding::Weighted(
            GteCell::new(
                self.encodings[dec_obj].as_ref().unwrap().root,
                self.encodings[dec_obj].as_ref().unwrap().max_leaf_weight,
                &tot_db_cell,
            ),
            self.encodings[dec_obj].as_ref().unwrap().offset,
        );

        self.kernel.bioptsat(
            (inc_obj, dec_obj),
            (&mut inc_enc, &mut dec_enc),
            base_assumps,
            starting_point,
            (inc_lb, dec_lb),
            lookup,
            collector,
        )
    }

    fn linsu_yield<Col: Extend<NonDomPoint>>(
        &mut self,
        obj_idx: usize,
        base_assumps: &[Lit],
        upper_bound: Option<(usize, Option<Assignment>)>,
        lower_bound: Option<usize>,
        collector: &mut Col,
        rebase_encodings: bool,
    ) -> Result<Option<usize>, Termination> {
        if self.encodings[obj_idx].is_none() {
            self.encodings[obj_idx] = Some(self.build_obj_encoding(obj_idx, rebase_encodings)?);
        }

        let mut enc: ObjEncoding<_, card::DefIncUpperBounding> = ObjEncoding::Weighted(
            Gte::new(
                self.encodings[obj_idx].as_ref().unwrap().root,
                self.encodings[obj_idx].as_ref().unwrap().max_leaf_weight,
                &mut self.tot_db,
            ),
            self.encodings[obj_idx].as_ref().unwrap().offset,
        );

        let lower_bound = std::cmp::max(lower_bound.unwrap_or(0), self.reforms[obj_idx].offset);

        self.kernel.linsu_yield(
            obj_idx,
            &mut enc,
            base_assumps,
            upper_bound,
            Some(lower_bound),
            collector,
        )
    }

    fn p_minimal<Col: Extend<NonDomPoint>>(
        &mut self,
        base_assumps: &[Lit],
        mut starting_point: Option<Assignment>,
        collector: &mut Col,
        rebase_encodings: bool,
    ) -> Result<(), Termination> {
        self.kernel.log_routine_start("p-minimal")?;
        for oidx in 0..self.kernel.stats.n_objs {
            if self.encodings[oidx].is_none()
                && !matches!(self.kernel.objs[oidx], Objective::Constant { .. })
            {
                self.encodings[oidx] = Some(self.build_obj_encoding(oidx, rebase_encodings)?);
                self.kernel.check_termination()?;
            }
        }
        let tot_db_cell = RefCell::from(&mut self.tot_db);
        let mut obj_encs: Vec<_> = self
            .encodings
            .iter()
            .map(|enc| match enc.as_ref() {
                Some(enc) => ObjEncoding::<_, card::DefIncUpperBounding>::Weighted(
                    GteCell::new(enc.root, enc.max_leaf_weight, &tot_db_cell),
                    enc.offset,
                ),
                None => ObjEncoding::Constant,
            })
            .collect();
        let mut assumps = Vec::from(base_assumps);
        loop {
            // Find minimization starting point
            let (costs, solution) = if let Some(mut sol) = starting_point.take() {
                let costs: Vec<_> = (0..self.kernel.stats.n_objs)
                    .map(|oidx| {
                        self.kernel
                            .get_cost_with_heuristic_improvements(oidx, &mut sol, false)
                            .unwrap()
                    })
                    .collect();
                (costs, sol)
            } else {
                let res = self.kernel.solve_assumps(base_assumps)?;
                if SolverResult::Unsat == res {
                    self.kernel.log_routine_end()?;
                    return Ok(());
                }
                self.kernel.check_termination()?;
                self.kernel.get_solution_and_internal_costs(
                    self.kernel
                        .opts
                        .heuristic_improvements
                        .solution_tightening
                        .wanted(Phase::OuterLoop),
                )?
            };

            // Minimize solution
            self.kernel.log_candidate(&costs, Phase::OuterLoop)?;
            self.kernel.check_termination()?;
            self.kernel.phase_solution(solution.clone())?;
            let (costs, solution, block_switch) =
                self.kernel
                    .p_minimization(costs, solution, base_assumps, &mut obj_encs)?;

            assumps.drain(base_assumps.len()..);
            assumps.extend(self.kernel.enforce_dominating(&costs, &mut obj_encs));
            self.kernel
                .yield_solutions(costs, &assumps, solution, collector)?;

            // Block last Pareto point, if temporarily blocked
            if let Some(block_lit) = block_switch {
                self.kernel.oracle.add_unit(block_lit)?;
            }
        }
    }

    fn lower_bounding<Col: Extend<NonDomPoint>>(
        &mut self,
        base_assumps: &[Lit],
        collector: &mut Col,
        rebase_encodings: bool,
    ) -> Result<(), Termination> {
        self.kernel.log_routine_start("lower-bounding")?;

        for oidx in 0..self.kernel.stats.n_objs {
            if self.encodings[oidx].is_none()
                && !matches!(self.kernel.objs[oidx], Objective::Constant { .. })
            {
                self.encodings[oidx] = Some(self.build_obj_encoding(oidx, rebase_encodings)?);
                self.kernel.check_termination()?;
            }
        }
        let tot_db_cell = RefCell::from(&mut self.tot_db);
        let (mut obj_encs, fence_data): (Vec<_>, _) = self
            .encodings
            .iter()
            .map(|enc| {
                let (mut enc, offset) = match enc.as_ref() {
                    Some(enc) => (
                        ObjEncoding::<_, card::DefIncUpperBounding>::Weighted(
                            GteCell::new(enc.root, enc.max_leaf_weight, &tot_db_cell),
                            enc.offset,
                        ),
                        enc.offset,
                    ),
                    None => (ObjEncoding::Constant, 0),
                };
                enc.encode_ub_change(
                    offset..offset + 1,
                    &mut self.kernel.oracle,
                    &mut self.kernel.var_manager,
                );
                let assumps = enc.enforce_ub(offset).unwrap();
                let assump = if assumps.is_empty() {
                    None
                } else if 1 == assumps.len() {
                    Some(assumps[0])
                } else {
                    let mut and_impl = Cnf::new();
                    let and_lit = self.kernel.var_manager.new_var().pos_lit();
                    and_impl.add_lit_impl_cube(and_lit, &assumps);
                    self.kernel.oracle.add_cnf(and_impl).unwrap();
                    Some(and_lit)
                };
                (enc, (offset, assump))
            })
            .unzip();
        let mut fence = Fence { data: fence_data };

        let mut assumps = Vec::from(base_assumps);
        // sort base assumptions for filtering them out efficiently
        assumps.sort_unstable();
        loop {
            assumps.drain(base_assumps.len()..);
            assumps.extend(fence.assumps());
            let res = self.kernel.solve_assumps(&assumps)?;
            match res {
                SolverResult::Sat => {
                    self.kernel
                        .harvest(&fence, &mut obj_encs, base_assumps, collector)?
                }
                SolverResult::Unsat => {
                    let mut core = self.kernel.oracle.core()?;
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
                        self.kernel.log_routine_end()?;
                        return Ok(());
                    }
                    #[cfg(debug_assertions)]
                    let old_fence = fence.bounds();
                    self.kernel.update_fence(&mut fence, core, &mut obj_encs)?;
                    #[cfg(debug_assertions)]
                    {
                        let new_fence = fence.bounds();
                        let mut increased = false;
                        for idx in 0..old_fence.len() {
                            debug_assert!(old_fence[idx] <= new_fence[idx]);
                            if old_fence[idx] < new_fence[idx] {
                                increased = true;
                            }
                        }
                        if !increased {
                            panic!("fence has not increased");
                        }
                    }
                }
                SolverResult::Interrupted => panic!("should have errored before"),
            }
        }
    }

    /// Cuts away the areas dominated by the points in `self.discovered`
    fn cut_dominated(
        &mut self,
        points: &[&[usize]],
        rebase_encodings: bool,
    ) -> Result<(), Termination> {
        for &cost in points {
            let clause = cost
                .iter()
                .enumerate()
                .filter_map(|(obj_idx, &cost)| {
                    if matches!(self.kernel.objs[obj_idx], Objective::Constant { .. }) {
                        debug_assert_eq!(cost, 0);
                        return None;
                    }
                    let reform = &self.reforms[obj_idx];
                    if cost <= reform.offset {
                        // if reformulation has derived this lower bound, no
                        // solutions will ever be <= cost and this literal can
                        // be dropped from the clause
                        return None;
                    }
                    if self.encodings[obj_idx].is_none() {
                        match self.build_obj_encoding(obj_idx, rebase_encodings) {
                            Ok(enc) => self.encodings[obj_idx] = Some(enc),
                            Err(term) => return Some(Err(term)),
                        }
                    }
                    let units = match self.bound_objective(obj_idx, cost - 1, rebase_encodings) {
                        Ok(units) => units,
                        Err(term) => return Some(Err(term)),
                    };
                    debug_assert!(!units.is_empty());
                    if units.len() == 1 {
                        Some(Ok(units[0]))
                    } else {
                        let and_lit = self.kernel.var_manager.new_var().pos_lit();
                        self.kernel
                            .oracle
                            .extend(atomics::lit_impl_cube(and_lit, &units));
                        Some(Ok(and_lit))
                    }
                })
                .collect::<Result<Clause, Termination>>()?;
            self.kernel.oracle.add_clause(clause)?;
        }
        Ok(())
    }

    /// Bounds an objective at `<= bound`
    fn bound_objective(
        &mut self,
        obj_idx: usize,
        bound: usize,
        rebase_encodings: bool,
    ) -> Result<Vec<Lit>, Termination> {
        debug_assert!(bound >= self.reforms[obj_idx].offset);
        if bound == self.reforms[obj_idx].offset {
            return Ok(self.reforms[obj_idx]
                .inactives
                .iter()
                .map(|(&l, _)| !l)
                .collect());
        }
        if self.encodings[obj_idx].is_none() {
            self.encodings[obj_idx] = Some(self.build_obj_encoding(obj_idx, rebase_encodings)?);
        }

        let enc = self.encodings[obj_idx].as_ref().unwrap();
        let bound = bound - enc.offset;
        let mut assumps = vec![];
        for val in self.tot_db[enc.root.id].vals(
            enc.root.rev_map_round_up(bound + 1)..=enc.root.rev_map(bound + enc.max_leaf_weight),
        ) {
            assumps.push(
                !self
                    .tot_db
                    .define_pos(
                        enc.root.id,
                        val,
                        &mut self.kernel.oracle,
                        &mut self.kernel.var_manager,
                    )
                    .unwrap(),
            )
        }
        Ok(assumps)
    }

    /// Merges the current OLL reformulation into a GTE. If `rebase` is true,
    /// does not perform a merge but uses all totalizer outputs as individual
    /// input literals to the GTE.
    fn build_obj_encoding(
        &mut self,
        obj_idx: usize,
        rebase: bool,
    ) -> Result<ObjEncData, Termination> {
        self.kernel.log_routine_start("build-encoding")?;
        let reform = &self.reforms[obj_idx];
        let mut cons = vec![];
        let mut max_leaf_weight = 0;
        for (lit, &weight) in &reform.inactives {
            max_leaf_weight = std::cmp::max(weight, max_leaf_weight);
            if let Some(&TotOutput {
                root,
                oidx,
                tot_weight,
            }) = reform.outputs.get(lit)
            {
                debug_assert_ne!(weight, 0);
                debug_assert!(oidx < self.tot_db[root].len());
                max_leaf_weight = std::cmp::max(tot_weight, max_leaf_weight);
                if rebase {
                    // ignore totalizer structure
                    cons.push(NodeCon::single(root, oidx + 1, weight));
                    for idx in oidx + 1..self.tot_db[root].len() {
                        cons.push(NodeCon::single(root, idx + 1, tot_weight));
                    }
                } else {
                    // preserve totalizer structure
                    if tot_weight == weight {
                        cons.push(NodeCon::offset_weighted(root, oidx, weight))
                    } else {
                        cons.push(NodeCon::single(root, oidx + 1, weight));
                        if oidx + 1 < self.tot_db[root].len() {
                            cons.push(NodeCon::offset_weighted(root, oidx + 1, tot_weight))
                        }
                    }
                }
            } else {
                let node = self.tot_db.insert(Node::Leaf(*lit));
                cons.push(NodeCon::weighted(node, weight));
            }
        }
        self.kernel.check_termination()?;
        cons.sort_unstable_by_key(|con| con.multiplier());
        debug_assert!(!cons.is_empty());
        // Note: set first_node _after_ inserting new input literals
        let first_node = if cons.len() == 1 {
            None
        } else {
            Some(NodeId(self.tot_db.len()))
        };
        // Detect sequences of connections of equal weight and merge them
        let mut seg_begin = 0;
        let mut seg_end = 0;
        let mut merged_cons = vec![];
        loop {
            seg_end += 1;
            if seg_end < cons.len() && cons[seg_end].multiplier() == cons[seg_begin].multiplier() {
                continue;
            }
            if seg_end > seg_begin + 1 {
                // merge lits of equal weight
                let mut seg: Vec<_> = cons[seg_begin..seg_end]
                    .iter()
                    .map(|&con| con.reweight(1))
                    .collect();
                seg.sort_unstable_by_key(|&con| self.tot_db.con_len(con));
                let con = self.tot_db.merge_balanced(&seg);
                debug_assert_eq!(con.multiplier(), 1);
                merged_cons.push(con.reweight(cons[seg_begin].multiplier().try_into().unwrap()));
            } else {
                merged_cons.push(cons[seg_begin])
            }
            seg_begin = seg_end;
            if seg_end >= cons.len() {
                break;
            }
        }
        self.kernel.check_termination()?;
        merged_cons.sort_unstable_by_key(|&con| self.tot_db.con_len(con));
        self.kernel.check_termination()?;
        let enc = ObjEncData {
            root: self.tot_db.merge_balanced(&merged_cons),
            offset: reform.offset,
            max_leaf_weight,
            first_node,
        };
        self.kernel.log_routine_end()?;
        Ok(enc)
    }

    /// Resets the oracle
    fn reset_oracle(&mut self) -> Result<(), Termination> {
        debug_assert!(self.kernel.orig_cnf.is_some());
        self.kernel.reset_oracle(true)?;
        self.tot_db.reset_vars();
        self.kernel.check_termination()?;
        Ok(())
    }

    /// Rebuilds all existing objective encodings. If `clean` is set, does so by
    /// restarting the oracle. Returns `true` if the oracle was restarted.
    fn rebuild_obj_encodings(&mut self, clean: bool, rebase: bool) -> Result<bool, Termination> {
        self.kernel.log_routine_start("rebuilding encodings")?;
        debug_assert!(!clean || self.kernel.orig_cnf.is_some());
        if clean {
            // Drain encodings
            let mut reform_offset = 0;
            let mut encs: Vec<_> = self
                .encodings
                .iter()
                .filter_map(|e| *e)
                .filter(|e| e.first_node.is_some())
                .collect();
            if encs.is_empty() {
                self.kernel.log_routine_end()?;
                return Ok(false);
            }
            encs.sort_unstable_by_key(|e| e.first_node);
            for enc in encs.iter().rev() {
                debug_assert!(enc.first_node.unwrap() <= enc.root.id);
                self.tot_db
                    .drain(enc.first_node.unwrap()..=enc.root.id)
                    .unwrap();
                reform_offset += enc.root.id + 1 - enc.first_node.unwrap();
            }
            // Reset oracle
            self.kernel.reset_oracle(true)?;
            self.tot_db.reset_vars();
            self.kernel.check_termination()?;
            // Adjust reformulations. Totalizers in the reformulation are either
            // _before_ or _after_ all of the drained encodings (not in
            // between), so we can do this once here rather than in the loop.
            for reform in &mut self.reforms {
                let outputs = reform.outputs.clone();
                let inactives = reform.inactives.clone().as_map();
                reform.outputs.clear();
                reform.inactives.retain(|lit, _| !outputs.contains_key(lit));
                for (
                    old_olit,
                    TotOutput {
                        mut root,
                        oidx,
                        tot_weight,
                    },
                ) in outputs
                {
                    if root > encs[0].first_node.unwrap() {
                        debug_assert!(root > encs[encs.len() - 1].root.id);
                        root -= reform_offset;
                    }
                    // Rebuild encoding for required outputs
                    let olit = self.tot_db.define_pos_tot(
                        root,
                        oidx,
                        &mut self.kernel.oracle,
                        &mut self.kernel.var_manager,
                    );
                    // Update output map
                    reform.outputs.insert(
                        olit,
                        TotOutput {
                            root,
                            oidx,
                            tot_weight,
                        },
                    );
                    // Update inactives
                    reform.inactives.insert(olit, inactives[&old_olit]);
                }
                self.kernel.check_termination()?;
            }
        }
        for oidx in 0..self.encodings.len() {
            if self.encodings[oidx].is_none() {
                continue;
            }
            self.encodings[oidx] = Some(self.build_obj_encoding(oidx, rebase)?);
            self.kernel.check_termination()?;
        }
        self.kernel.log_routine_end()?;
        Ok(clean)
    }

    fn inpro_and_reset(&mut self, techniques: &str) -> Result<(), Termination> {
        if !self.kernel.opts.store_cnf {
            return Err(Termination::ResetWithoutCnf);
        }
        // Reset oracle
        self.kernel.oracle = O::default();
        #[cfg(feature = "interrupt-oracle")]
        {
            *self.kernel.oracle_interrupter.lock().unwrap() =
                Box::new(self.kernel.oracle.interrupter());
        }
        // Collect instance with reformulated objectives
        let mut orig_cnf = self.kernel.orig_cnf.clone().unwrap();
        self.tot_db.reset_encoded();
        let mut all_outputs: Vec<_> = self
            .reforms
            .iter()
            .map(|reform| reform.outputs.clone())
            .collect();
        let objs: Vec<(Vec<_>, isize)> = self
            .reforms
            .iter()
            .enumerate()
            .map(|(obj_idx, reform)| {
                (
                    reform
                        .inactives
                        .iter()
                        .flat_map(|(lit, weight)| {
                            let lits: Vec<_> = if let Some(TotOutput {
                                root,
                                oidx,
                                tot_weight,
                            }) = reform.outputs.get(lit)
                            {
                                (*oidx..self.tot_db[*root].len())
                                    .map(|idx| {
                                        let olit = self.tot_db.define_pos_tot(
                                            *root,
                                            idx,
                                            &mut orig_cnf,
                                            &mut self.kernel.var_manager,
                                        );
                                        if idx == *oidx {
                                            (clause![!olit], *weight)
                                        } else {
                                            all_outputs[obj_idx].insert(
                                                olit,
                                                TotOutput {
                                                    root: *root,
                                                    oidx: idx,
                                                    tot_weight: *tot_weight,
                                                },
                                            );
                                            (clause![!olit], *tot_weight)
                                        }
                                    })
                                    .collect()
                            } else {
                                (0..1).map(|_| (clause![!*lit], *weight)).collect()
                            };
                            lits.into_iter()
                        })
                        .collect(),
                    0,
                )
            })
            .collect();
        // Inprocess
        self.kernel.log_routine_start("inprocessing")?;
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
        self.kernel.log_routine_end()?;
        if let Some(logger) = self.kernel.logger.as_mut() {
            logger.log_inprocessing(
                (cls_before, inpro.n_prepro_clauses() as usize),
                inpro.n_prepro_fixed_lits() as usize,
                ranges,
            )?;
        }
        self.kernel.inpro = Some(inpro);
        self.kernel.check_termination()?;
        // Reinit oracle
        self.kernel
            .oracle
            .reserve(self.kernel.var_manager.max_var().unwrap())?;
        self.kernel.oracle.add_cnf(inpro_cnf)?;
        #[cfg(feature = "sol-tightening")]
        // Freeze objective variables so that they are not removed
        for (o, _) in &inpro_objs {
            for (cl, _) in o.iter() {
                debug_assert_eq!(cl.len(), 1);
                self.kernel.oracle.freeze_var(cl[0].var())?;
            }
        }
        self.kernel.check_termination()?;
        // Build encodings
        for (idx, (softs, offset)) in inpro_objs.iter().enumerate() {
            debug_assert!(*offset >= 0);
            let reform = &mut self.reforms[idx];
            let outputs = &all_outputs[idx];
            let mut tots_to_add: RsHashMap<NodeId, (Vec<bool>, usize)> = RsHashMap::default();
            let mut cons = vec![];
            reform.offset += *offset as usize;
            if softs.is_empty() {
                self.kernel.objs[idx] = Objective::Constant {
                    offset: self.kernel.objs[idx].offset() + reform.offset as isize,
                };
                continue;
            }
            let mut max_leaf_weight = 0;
            for (cl, w) in softs {
                debug_assert_eq!(cl.len(), 1);
                max_leaf_weight = std::cmp::max(*w, max_leaf_weight);
                let olit = !cl[0];
                if let Some(TotOutput {
                    root,
                    oidx,
                    tot_weight,
                }) = outputs.get(&olit)
                {
                    if *w < *tot_weight {
                        cons.push(NodeCon::single(*root, oidx + 1, *w));
                        continue;
                    }
                    if let Some((tot_data, _)) = tots_to_add.get_mut(root) {
                        debug_assert!(!tot_data[*oidx]);
                        tot_data[*oidx] = true;
                    } else {
                        let mut dat = vec![false; self.tot_db[*root].len()];
                        dat[*oidx] = true;
                        tots_to_add.insert(*root, (dat, *tot_weight));
                    }
                } else {
                    // original obj literal or introduced by inprocessing
                    let node = self.tot_db.insert(Node::Leaf(olit));
                    cons.push(NodeCon::weighted(node, *w));
                }
            }
            // actually build the encoding
            self.kernel.log_routine_start("build-encoding")?;
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
            self.kernel.check_termination()?;
            cons.sort_unstable_by_key(|con| con.multiplier());
            debug_assert!(!cons.is_empty());
            let first_node = if cons.len() == 1 {
                None
            } else {
                Some(NodeId(self.tot_db.len()))
            };
            // Detect sequences of connections of equal weight and merge them
            let mut seg_begin = 0;
            let mut seg_end = 0;
            let mut merged_cons = vec![];
            loop {
                seg_end += 1;
                if seg_end < cons.len()
                    && cons[seg_end].multiplier() == cons[seg_begin].multiplier()
                {
                    continue;
                }
                if seg_end > seg_begin + 1 {
                    // merge lits of equal weight
                    let mut seg: Vec<_> = cons[seg_begin..seg_end]
                        .iter()
                        .map(|&con| con.reweight(1))
                        .collect();
                    seg.sort_unstable_by_key(|&con| self.tot_db.con_len(con));
                    let con = self.tot_db.merge_balanced(&seg);
                    debug_assert_eq!(con.multiplier(), 1);
                    merged_cons
                        .push(con.reweight(cons[seg_begin].multiplier().try_into().unwrap()));
                } else {
                    merged_cons.push(cons[seg_begin])
                }
                seg_begin = seg_end;
                if seg_end >= cons.len() {
                    break;
                }
            }
            self.kernel.check_termination()?;
            merged_cons.sort_unstable_by_key(|&con| self.tot_db.con_len(con));
            self.kernel.check_termination()?;
            self.encodings[idx] = Some(ObjEncData {
                root: self.tot_db.merge_balanced(&merged_cons),
                offset: reform.offset,
                max_leaf_weight,
                first_node,
            });
            self.kernel.log_routine_end()?;
        }
        Ok(())
    }

    #[cfg(feature = "data-helpers")]
    fn enc_clauses_summary(&mut self) -> Result<(), Termination> {
        self.kernel.solve()?;
        self.tot_db.reset_encoded();
        let db_bak = self.tot_db.clone();
        let (cost, _) = self.kernel.get_solution_and_internal_costs(true)?;

        // Merging
        let mut cnf = Cnf::new();
        for oidx in 0..self.kernel.stats.n_objs {
            if matches!(self.kernel.objs[oidx], Objective::Constant { .. }) {
                continue;
            }
            let enc = self.build_obj_encoding(oidx, false)?;
            let bound = cost[oidx] - enc.offset;
            for val in self.tot_db[enc.root.id].vals(
                enc.root.rev_map_round_up(bound + 1)
                    ..=enc.root.rev_map(bound + enc.max_leaf_weight),
            ) {
                self.tot_db
                    .define_pos(enc.root.id, val, &mut cnf, &mut self.kernel.var_manager)
                    .unwrap();
            }
        }
        self.kernel
            .log_message(&format!("encoding clauses with merging: n={}", cnf.len()))?;

        self.tot_db = db_bak;

        // No merging
        let mut cnf = Cnf::new();
        for oidx in 0..self.kernel.stats.n_objs {
            if matches!(self.kernel.objs[oidx], Objective::Constant { .. }) {
                continue;
            }
            let enc = self.build_obj_encoding(oidx, true)?;
            let bound = cost[oidx] - enc.offset;
            for val in self.tot_db[enc.root.id].vals(
                enc.root.rev_map_round_up(bound + 1)
                    ..=enc.root.rev_map(bound + enc.max_leaf_weight),
            ) {
                self.tot_db
                    .define_pos(enc.root.id, val, &mut cnf, &mut self.kernel.var_manager)
                    .unwrap();
            }
        }
        self.kernel.log_message(&format!(
            "encoding clauses without merging: n={}",
            cnf.len()
        ))?;
        
        use::rustsat::encodings::pb::BoundUpper;

        // No core boosting
        let mut cnf = Cnf::new();
        for oidx in 0..self.kernel.stats.n_objs {
            if matches!(self.kernel.objs[oidx], Objective::Constant { .. }) {
                continue;
            }
            let mut enc = rustsat::encodings::pb::DbGte::from_iter(self.kernel.objs[oidx].iter());
            let bound = cost[oidx];
            enc.encode_ub(bound..=bound, &mut cnf, &mut self.kernel.var_manager);
        }
        self.kernel.log_message(&format!(
            "encoding clauses without core boosting: n={}",
            cnf.len()
        ))?;

        Ok(())
    }
}
