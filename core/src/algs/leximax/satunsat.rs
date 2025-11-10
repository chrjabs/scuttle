//! # SAT-UNSAT Variant of LeximaxIST

use std::{cmp::Reverse, io};

use rustsat::{
    encodings::{
        self, Monotone,
        am1::{Encode as _, Pairwise},
        card::{self, Totalizer},
        pb::{self, GeneralizedTotalizer},
    },
    instances::ManageVars,
    solvers::{Initialize, SolveIncremental, SolveStats, SolverResult},
    types::{Assignment, Clause, Lit},
};
use scuttle_proc::oracle_bounds;
use tracing::{Level, info, instrument, span, trace};

use crate::{
    EncodingStats, LeximaxIst,
    MaybeTerminatedError::{self, Done},
    algs::{CoreBoost, Kernel, ObjEncoding, Objective, coreboosting::MergeOllRef},
    options::CoreBoostingOptions,
    types::ParetoFront,
};

use super::OptVariant;

/// The Sat-Unsat optimization variant
pub struct SatUnsat<PBE = GeneralizedTotalizer, CE = Totalizer> {
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: Vec<ObjEncoding<PBE, CE>>,
}

#[oracle_bounds]
impl<O, PBE, CE, OInit, BCG> OptVariant<O, OInit, BCG> for SatUnsat<PBE, CE>
where
    O: SolveIncremental + SolveStats,
    PBE: encodings::EncodeStats + pb::BoundUpperIncremental + FromIterator<(Lit, usize)> + Monotone,
    CE: encodings::EncodeStats + card::BoundUpperIncremental + FromIterator<Lit> + Monotone,
    BCG: Fn(Assignment) -> Clause,
{
    fn encoding_stats(&self, objectives: &[Objective]) -> Vec<EncodingStats> {
        objectives
            .iter()
            .zip(&self.obj_encs)
            .map(|(obj, enc)| {
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
                    ObjEncoding::Constant => (),
                };
                s
            })
            .collect()
    }

    fn init(kernel: &mut Kernel<O, io::BufWriter<std::fs::File>, OInit, BCG>) -> Self {
        // Initialize objective encodings
        let obj_encs = kernel
            .objs
            .iter()
            .map(|obj| match obj {
                Objective::Weighted { lits, .. } => ObjEncoding::new_weighted(
                    lits.iter().map(|(&l, &w)| (l, w)),
                    kernel.opts.reserve_enc_vars,
                    &mut kernel.var_manager,
                ),
                Objective::Unweighted { lits, .. } => ObjEncoding::new_unweighted(
                    lits.iter().copied(),
                    kernel.opts.reserve_enc_vars,
                    &mut kernel.var_manager,
                ),
                Objective::Constant { .. } => ObjEncoding::Constant,
            })
            .collect();
        Self { obj_encs }
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
        let mut next_max_val = max_val;
        for iteration in 0..kernel.objs.len() {
            max_val = next_max_val;
            let mut found_sol = false;
            let ignore_switches = if iteration == 0 {
                vec![Lit::positive(0); kernel.objs.len()]
            } else {
                let ignore_switches: Vec<_> = kernel
                    .objs
                    .iter()
                    .map(|_| kernel.var_manager.new_lit())
                    .collect();
                if iteration == 1 {
                    let mut enc: Pairwise = ignore_switches.iter().copied().collect();
                    enc.encode(&mut kernel.oracle, &mut kernel.var_manager)?;
                } else {
                    let mut enc: CE = ignore_switches.iter().copied().collect();
                    enc.encode_ub(
                        iteration..=iteration,
                        &mut kernel.oracle,
                        &mut kernel.var_manager,
                    )?;
                    for unit in enc.enforce_ub(iteration)? {
                        kernel.oracle.add_unit(unit)?;
                    }
                }
                ignore_switches
            };
            'minimize: while max_val > 0 {
                trace!(target: "leximax-iter", iteration, max_val);
                let assump_lit = if iteration == 0 {
                    Lit::positive(0)
                } else {
                    kernel.var_manager.new_lit()
                };
                let mut below_bound = 0;
                let mut assumptions = vec![];
                let span = span!(Level::DEBUG, "extending objective encodings").entered();
                for ((obj, enc), &ignore_switch) in kernel
                    .objs
                    .iter()
                    .zip(&mut self.obj_encs)
                    .zip(&ignore_switches)
                {
                    let bound = (max_val - obj.offset()).unsigned_abs() / obj.unit_weight() - 1;
                    if bound >= enc.offset() {
                        enc.encode_ub_change(
                            bound..bound + 1,
                            &mut kernel.oracle,
                            &mut kernel.var_manager,
                        )?;
                        if iteration == 0 {
                            assumptions.extend(enc.enforce_ub(bound).unwrap());
                        } else {
                            for unit in enc.enforce_ub(bound).unwrap() {
                                // relax this unit with the ignore switch and the current
                                // assumption literal
                                kernel.oracle.add_ternary(unit, ignore_switch, assump_lit)?;
                            }
                        }
                    } else {
                        // objective can't be below the required bound
                        if below_bound >= iteration {
                            break 'minimize;
                        }
                        below_bound += 1;
                        kernel.oracle.add_binary(ignore_switch, assump_lit)?;
                    }
                    kernel.check_termination()?;
                }
                span.exit();
                if iteration > 0 {
                    assumptions.push(!assump_lit);
                }
                let res = kernel.solve_assumps(&assumptions)?;
                kernel.check_termination()?;
                if res == SolverResult::Unsat {
                    // allow oracle to remove reified clauses
                    if iteration > 0 {
                        kernel.oracle.add_unit(assump_lit)?;
                    }
                    break;
                }
                (costs, sol) = kernel.get_solution_and_internal_costs(false)?;
                info!(target: "candidate", ?costs);
                (max_val, next_max_val) = {
                    let mut sorted_costs: Vec<_> = costs
                        .iter()
                        .zip(&kernel.objs)
                        .map(|(c, o)| (c * o.unit_weight()) as isize + o.offset())
                        .collect();
                    sorted_costs.sort_unstable_by_key(|v| Reverse(*v));
                    (
                        sorted_costs[iteration],
                        sorted_costs[std::cmp::min(iteration + 1, kernel.objs.len() - 1)],
                    )
                };
                found_sol = true;
                // harden bound
                let span = span!(Level::DEBUG, "extending objective encodings").entered();
                for ((obj, enc), &ignore_switch) in kernel
                    .objs
                    .iter()
                    .zip(&mut self.obj_encs)
                    .zip(&ignore_switches)
                {
                    let bound = (max_val - obj.offset()).unsigned_abs() / obj.unit_weight();
                    if bound >= enc.offset() {
                        enc.encode_ub_change(
                            bound..bound + 1,
                            &mut kernel.oracle,
                            &mut kernel.var_manager,
                        )?;
                        if iteration == 0 {
                            for unit in enc.enforce_ub(bound).unwrap() {
                                kernel.oracle.add_unit(unit)?;
                            }
                        } else {
                            for unit in enc.enforce_ub(bound).unwrap() {
                                // relax this unit with the ignore switch
                                kernel.oracle.add_binary(unit, ignore_switch)?;
                            }
                        }
                    } else if iteration > 0 {
                        // objective can't be below the required bound
                        kernel.oracle.add_unit(ignore_switch)?;
                    }
                    kernel.check_termination()?;
                }
                span.exit();
                // allow oracle to remove reified clauses
                if iteration > 0 {
                    kernel.oracle.add_unit(assump_lit)?;
                }
            }
            if !found_sol {
                // if we didn't see a solution, we didn't harden bounds, and we didn't compute the
                // correct `next_max_val`
                next_max_val = {
                    let mut sorted_costs: Vec<_> = costs
                        .iter()
                        .zip(&kernel.objs)
                        .map(|(c, o)| (c * o.unit_weight()) as isize + o.offset())
                        .collect();
                    sorted_costs.sort_unstable_by_key(|v| Reverse(*v));
                    sorted_costs[std::cmp::min(iteration + 1, kernel.objs.len() - 1)]
                };
                let span = span!(Level::DEBUG, "extending objective encodings").entered();
                for ((obj, enc), &ignore_switch) in kernel
                    .objs
                    .iter()
                    .zip(&mut self.obj_encs)
                    .zip(&ignore_switches)
                {
                    let bound = (max_val - obj.offset()).unsigned_abs() / obj.unit_weight();
                    if bound >= enc.offset() {
                        enc.encode_ub_change(
                            bound..bound + 1,
                            &mut kernel.oracle,
                            &mut kernel.var_manager,
                        )?;
                        if iteration == 0 {
                            for unit in enc.enforce_ub(bound).unwrap() {
                                kernel.oracle.add_unit(unit)?;
                            }
                        } else {
                            for unit in enc.enforce_ub(bound).unwrap() {
                                // relax this unit with the ignore switch
                                kernel.oracle.add_binary(unit, ignore_switch)?;
                            }
                        }
                    } else if iteration > 0 {
                        // objective can't be below the required bound
                        kernel.oracle.add_unit(ignore_switch)?;
                    }
                    kernel.check_termination()?;
                }
                span.exit();
            }
        }
        // TODO: properly deal with permuted objective values here
        kernel.yield_solutions(costs, &[], sol, pareto_front)?;
        Done(())
    }
}

impl<'learn, 'term, PBE, CE, OInit, BCG> CoreBoost
    for LeximaxIst<rustsat_cadical::CaDiCaL<'learn, 'term>, SatUnsat<PBE, CE>, OInit, BCG>
where
    (PBE, CE): MergeOllRef<PBE = PBE, CE = CE>,
    OInit: Initialize<rustsat_cadical::CaDiCaL<'learn, 'term>>,
{
    #[instrument(name = "core-boost", skip(self), fields(opts = %opts))]
    fn core_boost(&mut self, opts: CoreBoostingOptions) -> MaybeTerminatedError<bool> {
        todo!()
    }
}
