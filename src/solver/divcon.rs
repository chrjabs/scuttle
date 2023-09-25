//! # Divide and Conquer Multi-Objective Optimization

use rustsat::{
    encodings::{
        atomics,
        card::dbtotalizer::{Node, TotDb},
        nodedb::{NodeById, NodeCon, NodeLike},
        pb::dpw,
    },
    instances::ManageVars,
    lit,
    solvers::{
        SolveIncremental, SolveStats,
        SolverResult::{Sat, Unsat},
    },
    types::{Assignment, Clause, Lit},
};
use scuttle_proc::{oracle_bounds, KernelFunctions};

mod sequential;
pub use sequential::DivCon as SeqDivCon;

use crate::{KernelFunctions, Termination};

use super::{
    coreguided::{OllReformulation, TotOutput},
    SolverKernel,
};

#[derive(Clone)]
struct ObjEncData {
    structure: dpw::Structure,
    offset: usize,
}

#[derive(KernelFunctions)]
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
    O: SolveIncremental + SolveStats,
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
    fn bioptsat<Lookup>(
        &mut self,
        (inc_obj, dec_obj): (usize, usize),
        base_assumps: &[Lit],
        starting_point: Option<(usize, Assignment)>,
        lookup: Lookup,
    ) -> Result<(), Termination>
    where
        Lookup: Fn(usize) -> Option<usize>,
    {
        self.kernel.log_routine_start("bioptsat")?;

        if self.encodings[inc_obj].is_none() {
            self.encodings[inc_obj] = Some(self.build_obj_encoding(inc_obj));
        }
        if self.encodings[dec_obj].is_none() {
            self.encodings[dec_obj] = Some(self.build_obj_encoding(dec_obj));
        }

        let mut assumps = Vec::from(base_assumps);
        let (mut inc_cost, mut sol) = if let Some(bound) = starting_point {
            bound
        } else {
            let res = self.kernel.solve_assumps(&assumps)?;
            debug_assert_eq!(res, Sat);
            let mut sol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
            let cost = self
                .kernel
                .get_cost_with_heuristic_improvements(inc_obj, &mut sol, true)?;
            (cost, sol)
        };
        let mut dec_cost;
        let mut last_inc_cost = None;
        loop {
            // minimize inc_obj
            (inc_cost, sol) = if let Some(res) = self.linsu(
                inc_obj,
                &assumps,
                Some((inc_cost, Some(sol))),
                last_inc_cost.map(|lc| lc + 1),
            )? {
                res
            } else {
                // no solutions
                return Ok(());
            };
            last_inc_cost = Some(inc_cost);
            dec_cost = self
                .kernel
                .get_cost_with_heuristic_improvements(dec_obj, &mut sol, false)?;
            if let Some(found) = lookup(inc_cost) {
                dec_cost = found;
            } else {
                // bound inc_obj
                assumps.extend(self.bound_objective(inc_obj, inc_cost));
                // minimize dec_obj
                dec_cost = self.linsu_yield(dec_obj, &assumps, Some((dec_cost, Some(sol))), None)?.unwrap();
            };
            // termination condition 1: can't decrease decreasing objective further
            if dec_cost <= self.reforms[dec_obj].offset {
                break;
            }
            // skip to next non-dom
            assumps.drain(base_assumps.len()..);
            assumps.extend(self.bound_objective(dec_obj, dec_cost - 1));
            (sol, inc_cost) = match self.kernel.solve_assumps(&assumps)? {
                Sat => {
                    let mut sol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
                    let cost = self
                        .kernel
                        .get_cost_with_heuristic_improvements(inc_obj, &mut sol, true)?;
                    (sol, cost)
                }
                Unsat => break,
                _ => panic!(),
            };
        }
        self.kernel.log_routine_end()?;
        return Ok(());
    }

    fn linsu_yield(
        &mut self,
        obj_idx: usize,
        base_assumps: &[Lit],
        upper_bound: Option<(usize, Option<Assignment>)>,
        lower_bound: Option<usize>,
    ) -> Result<Option<usize>, Termination> {
        let (cost, mut sol) =
            if let Some(res) = self.linsu(obj_idx, base_assumps, upper_bound, lower_bound)? {
                res
            } else {
                // nothing to yield
                return Ok(None);
            };
        let costs: Vec<_> = (0..self.kernel.stats.n_objs)
            .map(|idx| {
                self.kernel
                    .get_cost_with_heuristic_improvements(idx, &mut sol, false)
                    .unwrap()
            })
            .collect();
        debug_assert_eq!(costs[obj_idx], cost);
        // bound obj
        let mut assumps = Vec::from(base_assumps);
        let enc = self.encodings[obj_idx].as_ref().unwrap();
        dpw::encode_output(
            &enc.structure,
            (cost - enc.offset) / (1 << enc.structure.output_power()),
            &mut self.tot_db,
            &mut self.kernel.oracle,
            &mut self.kernel.var_manager,
        );
        assumps
            .extend(dpw::enforce_ub(&enc.structure, cost - enc.offset, &mut self.tot_db).unwrap());
        self.kernel.yield_solutions(costs, &assumps, sol)?;
        Ok(Some(cost))
    }

    fn linsu(
        &mut self,
        obj_idx: usize,
        base_assumps: &[Lit],
        upper_bound: Option<(usize, Option<Assignment>)>,
        lower_bound: Option<usize>,
    ) -> Result<Option<(usize, Assignment)>, Termination> {
        self.kernel.log_routine_start("linsu")?;

        if self.encodings[obj_idx].is_none() {
            self.encodings[obj_idx] = Some(self.build_obj_encoding(obj_idx));
        }

        let lower_bound = std::cmp::max(lower_bound.unwrap_or(0), self.reforms[obj_idx].offset);

        let mut assumps = Vec::from(base_assumps);
        let (mut cost, mut sol) = if let Some(bound) = upper_bound {
            bound
        } else {
            let res = self.kernel.solve_assumps(&assumps)?;
            if res == Unsat {
                return Ok(None);
            }
            let mut sol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
            let cost = self
                .kernel
                .get_cost_with_heuristic_improvements(obj_idx, &mut sol, true)?;
            (cost, Some(sol))
        };
        let enc = self.encodings[obj_idx].as_ref().unwrap();
        let output_weight = 1 << (enc.structure.output_power());
        if cost == lower_bound {
            // make sure to have a solution
            if sol.is_none() {
                assumps.extend(self.bound_objective(obj_idx, cost));
                let res = self.kernel.solve_assumps(&assumps)?;
                debug_assert_eq!(res, Sat);
                sol = Some(self.kernel.oracle.solution(self.kernel.max_orig_var)?);
            }
            self.kernel.log_routine_end()?;
            return Ok(Some((cost, sol.unwrap())));
        }
        assumps.push(lit![0]);
        // coarse convergence
        while (cost - enc.offset) >= output_weight {
            let oidx = (cost - enc.offset) / output_weight - 1;
            debug_assert!(oidx < self.tot_db[enc.structure.root].len());
            dpw::encode_output(
                &enc.structure,
                oidx,
                &mut self.tot_db,
                &mut self.kernel.oracle,
                &mut self.kernel.var_manager,
            );
            assumps[base_assumps.len()] = !self.tot_db[enc.structure.root][oidx];
            match self.kernel.solve_assumps(&assumps)? {
                Sat => {
                    let mut thissol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
                    let new_cost = self.kernel.get_cost_with_heuristic_improvements(
                        obj_idx,
                        &mut thissol,
                        false,
                    )?;
                    debug_assert!(new_cost < cost);
                    sol = Some(thissol);
                    cost = new_cost;
                    if cost == lower_bound {
                        self.kernel.log_routine_end()?;
                        return Ok(Some((cost, sol.unwrap())));
                    }
                }
                Unsat => break,
                _ => panic!(),
            }
        }
        if (cost - enc.offset) % output_weight == 0 {
            // first call of fine convergence would not set any tares
            debug_assert_eq!(
                if cost - enc.offset > 0 {
                    dpw::enforce_ub(&enc.structure, cost - enc.offset - 1, &mut self.tot_db)
                        .unwrap()
                        .len()
                } else {
                    1
                },
                1
            );
            // make sure to have a solution
            if sol.is_none() {
                assumps.extend(self.bound_objective(obj_idx, cost));
                let res = self.kernel.solve_assumps(&assumps)?;
                debug_assert_eq!(res, Sat);
                sol = Some(self.kernel.oracle.solution(self.kernel.max_orig_var)?);
            }

            self.kernel.log_routine_end()?;
            return Ok(Some((cost, sol.unwrap())));
        }
        dpw::encode_output(
            &enc.structure,
            (cost - enc.offset - 1) / output_weight,
            &mut self.tot_db,
            &mut self.kernel.oracle,
            &mut self.kernel.var_manager,
        );
        // fine convergence
        while cost - enc.offset > 0 {
            assumps.drain(base_assumps.len()..);
            assumps.extend(
                dpw::enforce_ub(&enc.structure, cost - enc.offset - 1, &mut self.tot_db).unwrap(),
            );
            match self.kernel.solve_assumps(&assumps)? {
                Sat => {
                    let mut thissol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
                    let new_cost = self.kernel.get_cost_with_heuristic_improvements(
                        obj_idx,
                        &mut thissol,
                        false,
                    )?;
                    debug_assert!(new_cost < cost);
                    sol = Some(thissol);
                    cost = new_cost;
                    if cost == lower_bound {
                        self.kernel.log_routine_end()?;
                        return Ok(Some((cost, sol.unwrap())));
                    }
                }
                Unsat => break,
                _ => panic!(),
            }
        }
        // make sure to have a solution
        if sol.is_none() {
            assumps.extend(self.bound_objective(obj_idx, cost));
            let res = self.kernel.solve_assumps(&assumps)?;
            debug_assert_eq!(res, Sat);
            sol = Some(self.kernel.oracle.solution(self.kernel.max_orig_var)?);
        }
        self.kernel.log_routine_end()?;
        Ok(Some((cost, sol.unwrap())))
    }

    /// Cuts away the areas dominated by the points in `self.discovered`
    fn cut_dominated(&mut self, points: &[&[usize]]) -> Result<(), Termination> {
        for &cost in points {
            let clause = cost
                .into_iter()
                .enumerate()
                .filter_map(|(obj_idx, &cost)| {
                    if self.encodings[obj_idx].is_none() {
                        self.encodings[obj_idx] = Some(self.build_obj_encoding(obj_idx));
                    }
                    let enc = self.encodings[obj_idx].as_ref().unwrap();
                    let reform = &self.reforms[obj_idx];
                    if cost <= reform.offset {
                        // if reformulation has derived this lower bound, no
                        // solutions will ever be <= cost and this literal can
                        // be dropped from the clause
                        return None;
                    }
                    dpw::encode_output(
                        &enc.structure,
                        (cost - enc.offset - 1) / (1 << enc.structure.output_power()),
                        &mut self.tot_db,
                        &mut self.kernel.oracle,
                        &mut self.kernel.var_manager,
                    );
                    let units =
                        dpw::enforce_ub(&enc.structure, cost - enc.offset - 1, &mut self.tot_db)
                            .unwrap();
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
        if bound <= self.reforms[obj_idx].offset {
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
        dpw::encode_output(
            &enc.structure,
            (bound - enc.offset) / (1 << enc.structure.output_power()),
            &mut self.tot_db,
            &mut self.kernel.oracle,
            &mut self.kernel.var_manager,
        );
        dpw::enforce_ub(&enc.structure, bound - enc.offset, &mut self.tot_db).unwrap()
    }

    fn build_obj_encoding(&mut self, obj_idx: usize) -> ObjEncData {
        let reform = &self.reforms[obj_idx];
        let mut cons = vec![];
        for (lit, &weight) in &reform.inactives {
            if let Some(&TotOutput {
                root,
                oidx,
                tot_weight,
            }) = reform.outputs.get(lit)
            {
                debug_assert_ne!(weight, 0);
                if tot_weight == weight {
                    cons.push((
                        NodeCon {
                            id: root,
                            offset: oidx,
                            divisor: 1,
                        },
                        weight,
                    ))
                } else {
                    let node = self.tot_db.insert(Node::Leaf(*lit));
                    cons.push((NodeCon::full(node), weight));
                    if oidx + 1 < self.tot_db[root].len() {
                        cons.push((
                            NodeCon {
                                id: root,
                                offset: oidx + 1,
                                divisor: 1,
                            },
                            tot_weight,
                        ))
                    }
                }
            } else {
                let node = self.tot_db.insert(Node::Leaf(*lit));
                cons.push((NodeCon::full(node), weight));
            }
        }
        ObjEncData {
            structure: dpw::build_structure(
                cons.into_iter(),
                &mut self.tot_db,
                &mut self.kernel.var_manager,
            ),
            offset: reform.offset,
        }
    }
}
