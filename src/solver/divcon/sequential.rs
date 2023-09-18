//! # Sequential Divide and Conquer

use rustsat::{
    encodings::{
        atomics,
        card::dbtotalizer::{Node, TotDb},
        nodedb::{NodeById, NodeCon, NodeLike},
        pb::dpw,
    },
    instances::{ManageVars, MultiOptInstance},
    lit,
    solvers::{
        SolveIncremental, SolveStats,
        SolverResult::{Sat, Unsat},
    },
    types::{Assignment, Clause, Lit, RsHashMap},
};
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{
    solver::{coreguided::TotOutput, default_blocking_clause, SolverKernel},
    KernelFunctions, Limits, Options, Solve, Termination,
};

use super::{super::coreguided::OllReformulation, ObjEncData};

#[derive(KernelFunctions, Solve)]
#[solve(bounds = "where VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental + SolveStats")]
pub struct DivCon<VM, O, BCG> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// The objective reformulations
    reforms: Vec<OllReformulation>,
    /// The ideal point of the current working instance
    ideal: Vec<usize>,
    /// The objective function encodings and an offset
    encodings: Vec<Option<ObjEncData>>,
    /// The index of the last non-dominated point in the Pareto front that has
    /// been blocked
    last_blocked: usize,
    /// The totalizer database
    tot_db: TotDb,
}

impl<VM, O> DivCon<VM, O, fn(Assignment) -> Clause>
where
    VM: ManageVars,
    O: SolveIncremental,
{
    pub fn new_default_blocking(
        inst: MultiOptInstance<VM>,
        oracle: O,
        opts: Options,
    ) -> Result<Self, Termination> {
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            oracle,
            default_blocking_clause,
            opts,
        )?;
        Ok(Self::init(kernel))
    }
}

impl<VM, O> DivCon<VM, O, fn(Assignment) -> Clause>
where
    VM: ManageVars,
    O: SolveIncremental + Default,
{
    pub fn new_defaults(inst: MultiOptInstance<VM>, opts: Options) -> Result<Self, Termination> {
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            O::default(),
            default_blocking_clause,
            opts,
        )?;
        Ok(Self::init(kernel))
    }
}

impl<VM, O, BCG> DivCon<VM, O, BCG>
where
    VM: ManageVars,
{
    /// Initializes the solver
    fn init(kernel: SolverKernel<VM, O, BCG>) -> Self {
        debug_assert!(kernel.stats.n_objs <= 3);
        let mut reforms: Vec<_> = kernel.objs.iter().map(|obj| obj.into()).collect();
        reforms.shrink_to_fit();
        let mut ideal = vec![0; kernel.stats.n_objs];
        ideal.shrink_to_fit();
        let mut encodings = vec![None; kernel.stats.n_objs];
        encodings.shrink_to_fit();
        Self {
            kernel,
            reforms,
            ideal,
            encodings,
            last_blocked: 0,
            tot_db: Default::default(),
        }
    }
}

#[oracle_bounds]
impl<VM, O, BCG> DivCon<VM, O, BCG>
where
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + SolveStats,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> Result<(), Termination> {
        self.kernel.log_routine_start("seq-div-con")?;
        loop {
            if !self.find_ideal()? {
                return Ok(());
            }
            if let Some(logger) = &mut self.kernel.logger {
                logger.log_ideal(&self.ideal)?;
            }
            self.solve_subproblems()?;
            self.cut_dominated()?;
        }
    }

    /// Finds the ideal point of the working instance by executing OLL
    /// single-objective optimization. Returns false if the entire pareto front
    /// was found.
    fn find_ideal(&mut self) -> Result<bool, Termination> {
        self.kernel.log_routine_start("find_ideal")?;
        for obj_idx in 0..self.kernel.stats.n_objs {
            match self
                .kernel
                .oll(&mut self.reforms[obj_idx], &[], &mut self.tot_db)?
            {
                Some(_) => (),
                None => return Ok(false),
            };
            // TODO: maybe make use of solution?
            self.ideal[obj_idx] = self.reforms[obj_idx].offset;
        }
        self.kernel.log_routine_end()?;
        Ok(true)
    }

    /// Recurses down into the subproblems and solves them
    fn solve_subproblems(&mut self) -> Result<(), Termination> {
        if self.kernel.stats.n_objs == 2 {
            return self.bioptsat((0, 1), &[], None, |_| None);
        }
        debug_assert_eq!(self.kernel.stats.n_objs, 3);

        // TODO: do this filtering properly
        let mut filter = RsHashMap::default();
        let mut last_in_filter = self.kernel.pareto_front.len();
        for ideal_obj in 0..3 {
            let ideal_val = self.reforms[ideal_obj].offset;
            let assumps: Vec<_> = self.reforms[ideal_obj]
                .inactives
                .iter()
                .map(|(l, _)| !*l)
                .collect();

            let inc_obj = (ideal_obj + 1) % 3;
            let dec_obj = (ideal_obj + 2) % 3;
            let lookup = |ival| {
                let mut key = [None, None, None];
                key[inc_obj] = Some(ival);
                key[ideal_obj] = Some(ideal_val);
                filter.get(&key).map(|val| *val)
            };
            // TODO: use upper bound from ideal point computation
            self.bioptsat((inc_obj, dec_obj), &assumps, None, lookup)?;

            for ndom in self.kernel.pareto_front.iter().skip(last_in_filter) {
                for missing in 0..3 {
                    let cost = self.kernel.internalize_external_costs(ndom.costs());
                    let mut key = [Some(cost[0]), Some(cost[1]), Some(cost[2])];
                    key[missing] = None;
                    filter.insert(key, cost[missing]);
                }
            }
            last_in_filter = self.kernel.pareto_front.len();
        }
        Ok(())
    }

    /// Solves a bi-objective subproblem with the BiOptSat algorithm. This is
    /// the recursion anchor solving the smallest subproblems. BiOptSat is run
    /// in the LSU variant.
    ///
    /// `lookup`: for a value of the increasing objective, checks if the
    /// non-dominated point has already been discovered and returns the
    /// corresponding value of the decreasing objective
    fn bioptsat<Lookup>(
        &mut self,
        (inc_obj, dec_obj): (usize, usize),
        base_assumps: &[Lit],
        upper_bound: Option<(Assignment, usize)>,
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
        let (mut sol, mut inc_cost) = if let Some(bound) = upper_bound {
            bound
        } else {
            let res = self.kernel.solve_assumps(&assumps)?;
            debug_assert_eq!(res, Sat);
            let mut sol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
            let cost = self
                .kernel
                .get_cost_with_heuristic_improvements(inc_obj, &mut sol, true)?;
            (sol, cost)
        };
        let mut dec_cost;
        let mut last_inc_cost = None;
        loop {
            // minimize inc_obj
            (sol, inc_cost) = self.linsu(
                inc_obj,
                &assumps,
                Some((sol, inc_cost)),
                last_inc_cost.map(|lc| lc + 1),
            )?;
            last_inc_cost = Some(inc_cost);
            dec_cost = self
                .kernel
                .get_cost_with_heuristic_improvements(dec_obj, &mut sol, false)?;
            if let Some(found) = lookup(inc_cost) {
                dec_cost = found;
            } else {
                // bound inc_obj
                let inc_enc = self.encodings[inc_obj].as_ref().unwrap();
                dpw::encode_output(
                    &inc_enc.structure,
                    (inc_cost - inc_enc.offset) / (1 << inc_enc.structure.output_power()),
                    &mut self.tot_db,
                    &mut self.kernel.oracle,
                    &mut self.kernel.var_manager,
                );
                assumps.extend(
                    dpw::enforce_ub(
                        &inc_enc.structure,
                        inc_cost - inc_enc.offset,
                        &mut self.tot_db,
                    )
                    .unwrap(),
                );
                // minimize dec_obj
                (sol, dec_cost) = self.linsu(dec_obj, &assumps, Some((sol, dec_cost)), None)?;
                debug_assert_eq!(
                    self.kernel
                        .get_cost_with_heuristic_improvements(inc_obj, &mut sol, false)?,
                    inc_cost
                );
                // bound dec_obj
                let dec_enc = self.encodings[dec_obj].as_ref().unwrap();
                dpw::encode_output(
                    &dec_enc.structure,
                    (dec_cost - dec_enc.offset) / (1 << dec_enc.structure.output_power()),
                    &mut self.tot_db,
                    &mut self.kernel.oracle,
                    &mut self.kernel.var_manager,
                );
                assumps.extend(
                    dpw::enforce_ub(
                        &dec_enc.structure,
                        dec_cost - dec_enc.offset,
                        &mut self.tot_db,
                    )
                    .unwrap(),
                );
                // yield solutions
                let costs: Vec<_> = (0..self.kernel.stats.n_objs)
                    .map(|idx| {
                        self.kernel
                            .get_cost_with_heuristic_improvements(idx, &mut sol, false)
                            .unwrap()
                    })
                    .collect();
                debug_assert_eq!(costs[inc_obj], inc_cost);
                debug_assert_eq!(costs[dec_obj], dec_cost);
                self.kernel.yield_solutions(costs, &assumps, sol)?;
            };
            // termination condition 1: can't decrease decreasing objective further
            if dec_cost <= self.reforms[dec_obj].offset {
                break;
            }
            // skip to next non-dom
            assumps.drain(base_assumps.len()..);
            let dec_enc = self.encodings[dec_obj].as_ref().unwrap();
            assumps.extend(
                dpw::enforce_ub(
                    &dec_enc.structure,
                    dec_cost - dec_enc.offset - 1,
                    &mut self.tot_db,
                )
                .unwrap(),
            );
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

    fn linsu(
        &mut self,
        obj_idx: usize,
        base_assumps: &[Lit],
        upper_bound: Option<(Assignment, usize)>,
        lower_bound: Option<usize>,
    ) -> Result<(Assignment, usize), Termination> {
        self.kernel.log_routine_start("linsu")?;

        if self.encodings[obj_idx].is_none() {
            self.encodings[obj_idx] = Some(self.build_obj_encoding(obj_idx));
        }

        let lower_bound = std::cmp::max(lower_bound.unwrap_or(0), self.reforms[obj_idx].offset);

        let mut assumps = Vec::from(base_assumps);
        let (mut sol, mut cost) = if let Some(bound) = upper_bound {
            bound
        } else {
            let res = self.kernel.solve_assumps(&assumps)?;
            debug_assert_eq!(res, Sat);
            let mut sol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
            let cost = self
                .kernel
                .get_cost_with_heuristic_improvements(obj_idx, &mut sol, true)?;
            (sol, cost)
        };
        if cost == lower_bound {
            self.kernel.log_routine_end()?;
            return Ok((sol, cost));
        }
        let enc = self.encodings[obj_idx].as_ref().unwrap();
        let output_weight = 1 << (enc.structure.output_power());
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
                    sol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
                    let new_cost = self
                        .kernel
                        .get_cost_with_heuristic_improvements(obj_idx, &mut sol, false)?;
                    debug_assert!(new_cost < cost);
                    cost = new_cost;
                    if cost == lower_bound {
                        self.kernel.log_routine_end()?;
                        return Ok((sol, cost));
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
            self.kernel.log_routine_end()?;
            return Ok((sol, cost));
        }
        dpw::encode_output(
            &enc.structure,
            (cost - enc.offset - 1) / (1 << enc.structure.output_power()),
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
                    sol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
                    let new_cost = self
                        .kernel
                        .get_cost_with_heuristic_improvements(obj_idx, &mut sol, false)?;
                    debug_assert!(new_cost < cost);
                    cost = new_cost;
                    if cost == lower_bound {
                        self.kernel.log_routine_end()?;
                        return Ok((sol, cost));
                    }
                }
                Unsat => break,
                _ => panic!(),
            }
        }
        self.kernel.log_routine_end()?;
        Ok((sol, cost))
    }

    /// Cuts away the areas dominated by the points in `self.discovered`
    fn cut_dominated(&mut self) -> Result<(), Termination> {
        for point_idx in self.last_blocked..self.kernel.pareto_front.len() {
            let cost = self
                .kernel
                .internalize_external_costs(self.kernel.pareto_front[point_idx].costs());
            let clause = cost
                .into_iter()
                .enumerate()
                .filter_map(|(obj_idx, cost)| {
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
        self.last_blocked = self.kernel.pareto_front.len();
        Ok(())
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
