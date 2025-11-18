//! # SAT-UNSAT Variant of LeximaxIST

use std::{cmp::Reverse, io};

use rustsat::{
    encodings::{
        EncodeStats,
        am1::{Encode as _, Pairwise},
        card::{BoundUpper, Totalizer},
        nodedb::{NodeById, NodeCon, NodeLike},
        pb::GeneralizedTotalizer,
        totdb::{self, Semantics},
    },
    instances::ManageVars,
    solvers::{Initialize, SolveIncremental, SolveStats, SolverResult},
    types::{Assignment, Clause, Lit, RsHashMap},
};
use scuttle_proc::oracle_bounds;
use tracing::{Level, info, instrument, span, trace};

use crate::{
    EncodingStats, LeximaxIst,
    MaybeTerminatedError::{self, Done},
    algs::{
        CoreBoost, Kernel, ObjEncoding, Objective,
        coreboosting::CbResult,
        coreguided::{Inactives, OllReformulation, ReformData},
    },
    options::{AfterCbOptions, CoreBoostingOptions},
    termination::ensure,
    types::ParetoFront,
};

use super::OptVariant;

#[derive(Debug)]
struct ObjData<PBE, CE> {
    enc: ObjEncoding<PBE, CE>,
    reform: OllReformulation,
}

/// The MSU3 optimization variant
pub struct Msu3<PBE = GeneralizedTotalizer, CE = Totalizer> {
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_data: Vec<ObjData<PBE, CE>>,
}

#[oracle_bounds]
impl<O, OInit, BCG> OptVariant<O, OInit, BCG> for Msu3<GeneralizedTotalizer, Totalizer>
where
    O: SolveIncremental + SolveStats,
    BCG: Fn(Assignment) -> Clause,
{
    fn encoding_stats(&self, objectives: &[Objective]) -> Vec<EncodingStats> {
        objectives
            .iter()
            .zip(&self.obj_data)
            .map(|(obj, ObjData { enc, .. })| {
                let mut s = EncodingStats {
                    offset: obj.offset(),
                    ..Default::default()
                };
                if let Objective::Unweighted { unit_weight, .. } = obj {
                    s.unit_weight = Some(*unit_weight);
                };
                match enc {
                    ObjEncoding::Weighted(enc, _) => {
                        s.n_vars = enc.n_vars();
                        s.n_clauses = enc.n_clauses()
                    }
                    ObjEncoding::Unweighted(enc, _) => {
                        s.n_vars = enc.n_vars();
                        s.n_clauses = enc.n_clauses()
                    }
                    ObjEncoding::Constant(_) => (),
                };
                s
            })
            .collect()
    }

    fn init(kernel: &mut Kernel<O, io::BufWriter<std::fs::File>, OInit, BCG>) -> Self {
        // Initialize objective encodings
        let obj_data = kernel
            .objs
            .iter()
            .map(|obj| match obj {
                Objective::Weighted { .. } => ObjData {
                    enc: ObjEncoding::new_weighted(
                        [],
                        kernel.opts.reserve_enc_vars,
                        &mut kernel.var_manager,
                    ),
                    reform: obj.into(),
                },
                Objective::Unweighted { .. } => ObjData {
                    enc: ObjEncoding::new_unweighted(
                        [],
                        kernel.opts.reserve_enc_vars,
                        &mut kernel.var_manager,
                    ),
                    reform: obj.into(),
                },
                Objective::Constant { .. } => ObjData {
                    enc: ObjEncoding::Constant(0),
                    reform: obj.into(),
                },
            })
            .collect();
        Self { obj_data }
    }

    fn alg_main(
        &mut self,
        kernel: &mut Kernel<O, io::BufWriter<std::fs::File>, OInit, BCG>,
        pareto_front: &mut ParetoFront,
        starting_point: Option<(Vec<usize>, Assignment)>,
    ) -> MaybeTerminatedError {
        let (mut costs, mut sol) = if let Some(start) = starting_point {
            start
        } else {
            let res = kernel.solve()?;
            if res == SolverResult::Unsat {
                return Done(());
            }
            kernel.check_termination()?;
            kernel.get_solution_and_internal_costs(true)?
        };
        info!(target: "candidate", ?costs);

        let mut max_val = costs
            .iter()
            .zip(&kernel.objs)
            .map(|(c, o)| (c * o.unit_weight()) as isize + o.offset())
            .max()
            .unwrap();
        let obj_offsets = {
            let mut offsets: Vec<_> = self
                .obj_data
                .iter()
                .zip(&kernel.objs)
                .map(|(dat, obj)| (dat.enc.offset() * obj.unit_weight()) as isize + obj.offset())
                .collect();
            offsets.sort_unstable_by_key(|v| Reverse(*v));
            offsets
        };
        let mut max_vals = vec![0; kernel.objs.len()];
        let mut all_ignore_switches = vec![Lit::positive(0); kernel.objs.len() * kernel.objs.len()];
        let mut inactive: RsHashMap<Lit, Vec<usize>> = RsHashMap::default();
        for (obj_idx, dat) in self.obj_data.iter().enumerate() {
            for assump in dat.reform.inactives.assumps() {
                if let Some(idxs) = inactive.get_mut(&!assump) {
                    idxs.push(obj_idx)
                } else {
                    inactive.insert(!assump, vec![obj_idx]);
                }
            }
        }
        for iteration in 0..kernel.objs.len() {
            if iteration > 0 {
                for switch in &mut all_ignore_switches
                    [iteration * kernel.objs.len()..(iteration + 1) * kernel.objs.len()]
                {
                    *switch = kernel.var_manager.new_lit();
                }
            }
            let ignore_switches = &all_ignore_switches
                [iteration * kernel.objs.len()..(iteration + 1) * kernel.objs.len()];
            if iteration == 1 {
                let mut enc: Pairwise = ignore_switches.iter().copied().collect();
                enc.encode(&mut kernel.oracle, &mut kernel.var_manager)?;
            } else if iteration > 1 {
                let mut enc: Totalizer = ignore_switches.iter().copied().collect();
                enc.encode_ub(
                    iteration..=iteration,
                    &mut kernel.oracle,
                    &mut kernel.var_manager,
                )?;
                for unit in enc.enforce_ub(iteration)? {
                    kernel.oracle.add_unit(unit)?;
                }
            }
            let mut bound = obj_offsets[iteration];
            while bound < max_val {
                trace!(target: "leximax-iter", iteration, bound);
                let assump_lit = if iteration == 0 {
                    Lit::positive(0)
                } else {
                    kernel.var_manager.new_lit()
                };
                let mut below_bound = 0;
                let mut assumptions = vec![];
                let span = span!(Level::DEBUG, "extending objective encodings").entered();
                for ((obj, dat), &ignore_switch) in kernel
                    .objs
                    .iter()
                    .zip(&mut self.obj_data)
                    .zip(ignore_switches)
                {
                    assumptions.extend(dat.reform.inactives.assumps());
                    let bound = (bound - obj.offset()).unsigned_abs() / obj.unit_weight();
                    if bound >= dat.enc.offset() {
                        dat.enc.encode_ub_change(
                            bound..bound + 1,
                            &mut kernel.oracle,
                            &mut kernel.var_manager,
                        )?;
                        if iteration == 0 {
                            assumptions.extend(dat.enc.enforce_ub(bound).unwrap());
                        } else {
                            for unit in dat.enc.enforce_ub(bound).unwrap() {
                                // relax this unit with the ignore switch and the current
                                // assumption literal
                                kernel.oracle.add_ternary(unit, ignore_switch, assump_lit)?;
                            }
                        }
                    } else {
                        // objective can't be below the required bound
                        debug_assert!(below_bound < iteration);
                        below_bound += 1;
                        kernel.oracle.add_binary(ignore_switch, assump_lit)?;
                    }
                    kernel.check_termination()?;
                }
                span.exit();
                if iteration > 0 {
                    assumptions.push(!assump_lit);
                }

                // totalizer outputs can be inactive and assumptions from enforcing a bound
                // this also allows for weeding out assumptions in a single sweep
                assumptions.sort_unstable();
                assumptions.dedup();

                let res = kernel.solve_assumps(&assumptions)?;
                kernel.check_termination()?;
                if res == SolverResult::Sat {
                    (costs, sol) = kernel.get_solution_and_internal_costs(false)?;
                    break;
                }

                // disjoint core loop
                let mut bump_bound = true;
                let mut redo_prev_bounds = vec![false; kernel.objs.len()];
                'disjoint: loop {
                    // analyze core
                    let core = kernel.oracle.core()?;
                    if core.is_empty() {
                        return Done(());
                    }
                    for &core_lit in &core {
                        let Some(obj_idxs) = inactive.remove(&core_lit) else {
                            continue;
                        };
                        bump_bound = false;
                        for obj_idx in obj_idxs {
                            let dat = &mut self.obj_data[obj_idx];
                            let weight = match &dat.reform.inactives {
                                Inactives::Weighted(inact) => inact[&core_lit],
                                Inactives::Unweighted { .. } => 1,
                                Inactives::Constant => unreachable!(),
                            };
                            dat.reform.inactives.relax(core_lit, weight);
                            let Some(&ReformData {
                                root,
                                oidx,
                                tot_weight,
                                proof_id,
                            }) = dat.reform.reformulations.get(&core_lit)
                            else {
                                dat.enc.extend([(core_lit, weight)]);
                                redo_prev_bounds[obj_idx] = true;
                                continue;
                            };
                            // remove old output to only have one entry per totalizer in outputs
                            // map
                            dat.reform.reformulations.remove(&core_lit);
                            if oidx + 1 >= dat.enc.db_ref()[root].len() {
                                continue;
                            }
                            let new_olit = dat.enc.db_mut().define_unweighted(
                                root,
                                oidx + 1,
                                Semantics::If,
                                &mut kernel.oracle,
                                &mut kernel.var_manager,
                            )?;
                            dat.reform.inactives.insert(new_olit, tot_weight);
                            debug_assert!(!inactive.contains_key(&new_olit));
                            inactive.insert(new_olit, vec![obj_idx]);
                            dat.reform.reformulations.insert(
                                new_olit,
                                ReformData {
                                    root,
                                    oidx: oidx + 1,
                                    tot_weight,
                                    proof_id,
                                },
                            );
                        }
                    }
                    // weed out assumptions for disjoint cores
                    let mut new_len = 0;
                    let mut core_idx = 0;
                    for assump_idx in 0..assumptions.len() {
                        while core_idx < core.len() && !core[core_idx] < assumptions[assump_idx] {
                            core_idx += 1;
                        }
                        if core_idx < core.len() && assumptions[assump_idx] == !core[core_idx] {
                            continue;
                        }
                        if assump_idx != new_len {
                            assumptions.swap(assump_idx, new_len);
                        }
                        new_len += 1;
                    }
                    if new_len == 0 {
                        break 'disjoint;
                    }
                    assumptions.truncate(new_len);
                    // recall oracle with weeded out assumptions
                    let res = kernel.solve_assumps(&assumptions)?;
                    kernel.check_termination()?;
                    if res == SolverResult::Sat {
                        let (found_costs, found_sol) =
                            kernel.get_solution_and_internal_costs(false)?;
                        let mut found_sorted = found_costs.clone();
                        found_sorted.sort_unstable_by_key(|v| Reverse(*v));
                        let mut costs_sorted = costs.clone();
                        costs_sorted.sort_unstable_by_key(|v| Reverse(*v));
                        if found_sorted < costs_sorted {
                            (costs, sol) = (found_costs, found_sol);
                        }
                        break 'disjoint;
                    }
                }
                for dat in &mut self.obj_data {
                    dat.reform.inactives.cleanup();
                }
                if iteration > 0 && redo_prev_bounds.iter().any(|v| *v) {
                    let span = span!(Level::DEBUG, "extending objective encodings").entered();
                    for (prev_iteration, bound) in max_vals[0..iteration].iter().enumerate() {
                        for (((obj, dat), &ignore_switch), _) in kernel
                            .objs
                            .iter()
                            .zip(&mut self.obj_data)
                            .zip(
                                &all_ignore_switches[prev_iteration * kernel.objs.len()
                                    ..(prev_iteration + 1) * kernel.objs.len()],
                            )
                            .zip(&redo_prev_bounds)
                            .filter(|(((_, _), _), redo)| **redo)
                        {
                            // some literals have newly become active and the previous hardened bounds have
                            // to be redone
                            let bound = (bound - obj.offset()).unsigned_abs() / obj.unit_weight();
                            if bound >= dat.enc.offset() {
                                dat.enc.encode_ub_change(
                                    bound..bound + 1,
                                    &mut kernel.oracle,
                                    &mut kernel.var_manager,
                                )?;
                                if prev_iteration == 0 {
                                    for unit in dat.enc.enforce_ub(bound).unwrap() {
                                        kernel.oracle.add_unit(unit)?;
                                    }
                                } else {
                                    for unit in dat.enc.enforce_ub(bound).unwrap() {
                                        // relax this unit with the ignore switch and the current
                                        // assumption literal
                                        kernel.oracle.add_binary(unit, ignore_switch)?;
                                    }
                                }
                            } else {
                                // objective can't be below the required bound
                                kernel.oracle.add_unit(ignore_switch)?;
                            }
                            kernel.check_termination()?;
                        }
                    }
                    span.exit();
                }
                if bump_bound {
                    // did not find any inactive literals in core, so bump bound on max
                    bound = self
                        .obj_data
                        .iter()
                        .zip(&kernel.objs)
                        .map(|(dat, obj)| {
                            let bound = (bound - obj.offset()).unsigned_abs() / obj.unit_weight();
                            (dat.enc.next_higher(bound) * obj.unit_weight()) as isize + obj.offset()
                        })
                        .min()
                        .unwrap();
                }

                // allow oracle to remove reified clauses
                if iteration > 0 {
                    kernel.oracle.add_unit(assump_lit)?;
                }
            }
            info!(target: "candidate", ?costs);
            max_vals[iteration] = bound;
            // harden only bounds on encodings, not inactives
            let span = span!(Level::DEBUG, "extending objective encodings").entered();
            for ((obj, dat), &ignore_switch) in kernel.objs.iter().zip(&mut self.obj_data).zip(
                &all_ignore_switches
                    [iteration * kernel.objs.len()..(iteration + 1) * kernel.objs.len()],
            ) {
                let bound = (bound - obj.offset()).unsigned_abs() / obj.unit_weight();
                if bound >= dat.enc.offset() {
                    dat.enc.encode_ub_change(
                        bound..bound + 1,
                        &mut kernel.oracle,
                        &mut kernel.var_manager,
                    )?;
                    if iteration == 0 {
                        for unit in dat.enc.enforce_ub(bound).unwrap() {
                            kernel.oracle.add_unit(unit)?;
                        }
                    } else {
                        for unit in dat.enc.enforce_ub(bound).unwrap() {
                            // relax this unit with the ignore switch and the current
                            // assumption literal
                            kernel.oracle.add_binary(unit, ignore_switch)?;
                        }
                    }
                } else {
                    // objective can't be below the required bound
                    kernel.oracle.add_unit(ignore_switch)?;
                }
                kernel.check_termination()?;
            }
            span.exit();
            debug_assert_eq!(
                {
                    let mut sorted_costs: Vec<_> = costs
                        .iter()
                        .zip(&kernel.objs)
                        .map(|(c, o)| (c * o.unit_weight()) as isize + o.offset())
                        .collect();
                    sorted_costs.sort_unstable_by_key(|v| Reverse(*v));
                    sorted_costs[iteration]
                },
                bound
            );
            max_val = {
                let mut sorted_costs: Vec<_> = costs
                    .iter()
                    .zip(&kernel.objs)
                    .map(|(c, o)| (c * o.unit_weight()) as isize + o.offset())
                    .collect();
                sorted_costs.sort_unstable_by_key(|v| Reverse(*v));
                sorted_costs[std::cmp::min(iteration + 1, kernel.objs.len() - 1)]
            };
        }
        // TODO: properly deal with permuted objective values here
        kernel.yield_solutions(costs, &[], sol, pareto_front)?;
        Done(())
    }
}

impl<'learn, 'term, OInit, BCG> CoreBoost
    for LeximaxIst<
        rustsat_cadical::CaDiCaL<'learn, 'term>,
        Msu3<GeneralizedTotalizer, Totalizer>,
        OInit,
        BCG,
    >
where
    OInit: Initialize<rustsat_cadical::CaDiCaL<'learn, 'term>>,
{
    #[instrument(name = "core-boost", skip(self), fields(opts = %opts))]
    fn core_boost(&mut self, opts: CoreBoostingOptions) -> MaybeTerminatedError<bool> {
        ensure!(
            self.kernel.stats.n_solve_calls == 0,
            "cannot perform core boosting after solve has been called"
        );
        let Some(cb_res) = self.kernel.core_boost()? else {
            return Done(false);
        };
        self.kernel.check_termination()?;
        let reset_dbs = match &opts.after {
            AfterCbOptions::Nothing => false,
            AfterCbOptions::Reset => {
                self.kernel.reset_oracle(true)?;
                self.kernel.check_termination()?;
                true
            }
            #[cfg(feature = "maxpre")]
            AfterCbOptions::Inpro(techs) => {
                self.obj_encs = self.kernel.inprocess(techs, cb_res)?;
                self.kernel.check_termination()?;
                return Done(true);
            }
        };
        let span = span!(Level::DEBUG, "merge-encodings");
        let _enter = span.enter();
        for (
            oidx,
            CbResult {
                reform,
                mut tot_db,
                solution,
            },
        ) in cb_res.into_iter().enumerate()
        {
            if reset_dbs {
                debug_assert!(self.kernel.proof_stuff.is_none());
                tot_db.reset_vars();
            }
            if !matches!(self.kernel.objs[oidx], Objective::Constant { .. }) {
                self.opt.obj_data[oidx].enc = merge_totalizers(&reform, tot_db, opts.rebase);
            }
            self.opt.obj_data[oidx].reform = reform;

            if let Some(solution) = solution {
                let costs = self.kernel.compute_costs(&solution);
                self.starting_point = Some(
                    if let Some((start_costs, start)) = self.starting_point.take() {
                        let mut start_sorted = start_costs.clone();
                        start_sorted.sort_unstable_by_key(|v| Reverse(*v));
                        let mut costs_sorted = costs.clone();
                        costs_sorted.sort_unstable_by_key(|v| Reverse(*v));
                        if costs_sorted < start_sorted {
                            (costs, solution)
                        } else {
                            (start_costs, start)
                        }
                    } else {
                        (costs, solution)
                    },
                );
            }

            self.kernel.check_termination()?;
        }
        Done(true)
    }
}

fn merge_totalizers(
    reform: &OllReformulation,
    mut tot_db: totdb::Db,
    rebase: bool,
) -> ObjEncoding<GeneralizedTotalizer, Totalizer> {
    // merge only totalizers, keeping inactives
    if matches!(reform.inactives, Inactives::Constant) {
        // core boosting derived constant objective
        return ObjEncoding::Constant(reform.offset);
    }
    let mut cons = vec![];
    let mut max_leaf_weight = 0;
    for (lit, &weight) in &reform.inactives {
        let Some(&ReformData {
            root,
            oidx,
            tot_weight,
            ..
        }) = reform.reformulations.get(lit)
        else {
            continue;
        };
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
    }
    if cons.is_empty() {
        match reform.inactives {
            Inactives::Weighted(_) => {
                ObjEncoding::Weighted(GeneralizedTotalizer::default(), reform.offset)
            }
            Inactives::Unweighted { .. } => {
                ObjEncoding::Unweighted(Totalizer::default(), reform.offset)
            }
            Inactives::Constant => unreachable!(),
        }
    } else {
        let root = tot_db.merge_thorough(&mut cons);
        match reform.inactives {
            Inactives::Weighted(_) => ObjEncoding::Weighted(
                GeneralizedTotalizer::from_raw(root, tot_db, max_leaf_weight),
                reform.offset,
            ),
            Inactives::Unweighted { .. } => ObjEncoding::Unweighted(
                Totalizer::from_raw(root.id, root.offset(), tot_db),
                reform.offset,
            ),
            Inactives::Constant => unreachable!(),
        }
    }
}
