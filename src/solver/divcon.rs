//! # Divide and Conquer Multi-Objective Optimization

use std::cell::RefCell;

use rustsat::{
    encodings::{
        atomics,
        card::{
            self,
            dbtotalizer::{Node, TotDb},
        },
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        pb::dbgte::referenced::{Gte, GteCell},
    },
    instances::ManageVars,
    solvers::{SolveIncremental, SolveStats, SolverResult},
    types::{Assignment, Clause, Lit},
};
use scuttle_proc::oracle_bounds;

mod sequential;
pub use sequential::DivCon as SeqDivCon;

use crate::{types::NonDomPoint, Phase, Termination};

use super::{
    coreguided::{OllReformulation, TotOutput},
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
                None => return Ok(false),
            };
            // TODO: maybe make use of solution?
            ideal[obj_idx] = reform.offset;
        }
        self.kernel.log_routine_end()?;
        Ok(true)
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
    ) -> Result<(), Termination>
    where
        Lookup: Fn(usize) -> Option<usize>,
        Col: Extend<NonDomPoint>,
    {
        if self.encodings[inc_obj].is_none() {
            self.encodings[inc_obj] = Some(self.build_obj_encoding(inc_obj));
        }
        if self.encodings[dec_obj].is_none() {
            self.encodings[dec_obj] = Some(self.build_obj_encoding(dec_obj));
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
    ) -> Result<Option<usize>, Termination> {
        if self.encodings[obj_idx].is_none() {
            self.encodings[obj_idx] = Some(self.build_obj_encoding(obj_idx));
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
    ) -> Result<(), Termination> {
        self.kernel.log_routine_start("p-minimal")?;
        (0..self.kernel.stats.n_objs).for_each(|oidx| {
            if self.encodings[oidx].is_none() {
                self.encodings[oidx] = Some(self.build_obj_encoding(oidx));
            }
        });
        let tot_db_cell = RefCell::from(&mut self.tot_db);
        let mut obj_encs: Vec<_> = self
            .encodings
            .iter()
            .map(|enc| {
                let enc = enc.as_ref().unwrap();
                ObjEncoding::<_, card::DefIncUpperBounding>::Weighted(
                    GteCell::new(enc.root, enc.max_leaf_weight, &tot_db_cell),
                    enc.offset,
                )
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

    /// Cuts away the areas dominated by the points in `self.discovered`
    fn cut_dominated(&mut self, points: &[&[usize]]) -> Result<(), Termination> {
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
                        self.encodings[obj_idx] = Some(self.build_obj_encoding(obj_idx));
                    }
                    let units = self.bound_objective(obj_idx, cost - 1);
                    debug_assert!(!units.is_empty());
                    if units.len() == 1 {
                        Some(units[0])
                    } else {
                        let and_lit = self.kernel.var_manager.new_var().pos_lit();
                        self.kernel
                            .oracle
                            .extend(atomics::lit_impl_cube(and_lit, &units));
                        Some(and_lit)
                    }
                })
                .collect();
            self.kernel.oracle.add_clause(clause)?;
        }
        Ok(())
    }

    /// Bounds an objective at `<= bound`
    fn bound_objective(&mut self, obj_idx: usize, bound: usize) -> Vec<Lit> {
        debug_assert!(bound >= self.reforms[obj_idx].offset);
        if bound == self.reforms[obj_idx].offset {
            return self.reforms[obj_idx]
                .inactives
                .iter()
                .map(|(&l, _)| !l)
                .collect();
        }
        if self.encodings[obj_idx].is_none() {
            self.encodings[obj_idx] = Some(self.build_obj_encoding(obj_idx));
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
        assumps
    }

    /// Merges the current OLL reformulation into a GTE
    fn build_obj_encoding(&mut self, obj_idx: usize) -> ObjEncData {
        self.kernel.log_routine_start("build-encoding").unwrap();
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
                if tot_weight == weight {
                    cons.push(NodeCon::offset_weighted(root, oidx, weight))
                } else {
                    cons.push(NodeCon::single(root, oidx + 1, weight));
                    if oidx + 1 < self.tot_db[root].len() {
                        cons.push(NodeCon::offset_weighted(root, oidx + 1, tot_weight))
                    }
                }
            } else {
                let node = self.tot_db.insert(Node::Leaf(*lit));
                cons.push(NodeCon::weighted(node, weight));
            }
        }
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
        merged_cons.sort_unstable_by_key(|&con| self.tot_db.con_len(con));
        let enc = ObjEncData {
            root: self.tot_db.merge_balanced(&merged_cons),
            offset: reform.offset,
            max_leaf_weight,
            first_node,
        };
        self.kernel.log_routine_end().unwrap();
        enc
    }

    /// Rebuilds all existing objective encodings. If `clean` is set, does so by
    /// restarting the oracle.
    fn rebuild_obj_encodings(&mut self, clean: bool) -> Result<(), Termination> {
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
                return Ok(());
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
            // Adjust reformulations. Totalizers in the reformulation are either
            // _before_ or _after_ all of the drained encodings (not in
            // between), so we can do this once here rather than in the loop.
            for reform in &mut self.reforms {
                let outputs = reform.outputs.clone();
                let inactives = reform.inactives.clone();
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
            }
        }
        for oidx in 0..self.encodings.len() {
            if self.encodings[oidx].is_none() {
                continue;
            }
            self.encodings[oidx] = Some(self.build_obj_encoding(oidx));
        }
        self.kernel.log_routine_end()?;
        Ok(())
    }
}
