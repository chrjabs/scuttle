//! # Core-Guided Multi-Objective Prototype for (up to) 3 Objectives

use rustsat::{
    encodings::{
        atomics,
        card::dbtotalizer::{Node, TotDb},
        nodedb::{NodeById, NodeCon, NodeLike},
        pb::dpw,
    },
    instances::{ManageVars, MultiOptInstance},
    lit,
    solvers::{SolveIncremental, SolveStats, SolverResult},
    types::{Assignment, Clause, Lit},
};
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{
    solver::coreguided::TotOutput, types::ParetoFront, KernelFunctions, Limits, Options, Solve,
    Termination,
};

use super::{coreguided::OllReformulation, default_blocking_clause, SolverKernel};

#[derive(KernelFunctions, Solve)]
#[solve(bounds = "where VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental + SolveStats")]
pub struct TriCore<VM, O, BCG> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// The objective reformulations
    reforms: [Option<OllReformulation>; 3],
    /// The ideal point of the current working instance
    ideal: [usize; 3],
    /// The nadir point of the current working instance
    nadir: [usize; 3],
    /// The objective function encodings and an offset
    encodings: [Option<(dpw::Structure, usize)>; 3],
    /// The cost tuples discovered this iteration
    disc_costs: Vec<[usize; 3]>,
    /// The totalizer database
    tot_db: TotDb,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

impl<VM, O> TriCore<VM, O, fn(Assignment) -> Clause>
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

impl<VM, O> TriCore<VM, O, fn(Assignment) -> Clause>
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

impl<VM, O, BCG> TriCore<VM, O, BCG>
where
    VM: ManageVars,
{
    /// Initializes the solver
    fn init(kernel: SolverKernel<VM, O, BCG>) -> Self {
        debug_assert!(kernel.stats.n_objs <= 3);
        let mut solver = Self {
            kernel,
            reforms: [None, None, None],
            ideal: [0; 3],
            nadir: [0; 3],
            encodings: [None, None, None],
            disc_costs: Default::default(),
            tot_db: Default::default(),
            pareto_front: Default::default(),
        };
        // Initialize objective reformulations
        for (idx, obj) in solver.kernel.objs.iter().enumerate() {
            solver.reforms[idx] = Some(obj.into());
            // nadir point is initialized with zeroes first to make comparison
            // for the termination criterion easier
            solver.nadir[idx] = usize::MAX;
        }
        solver
    }
}

#[oracle_bounds]
impl<VM, O, BCG> TriCore<VM, O, BCG>
where
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + SolveStats,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> Result<(), Termination> {
        let empty_space = |ideal: &[usize; 3], nadir: &[usize; 3]| {
            nadir[0] <= ideal[0] + 1 && nadir[1] <= ideal[1] + 1 && nadir[2] <= ideal[2] + 1
        };
        self.kernel.log_routine_start("tri-core")?;
        loop {
            if !self.find_ideal()? {
                break;
            }
            if let Some(logger) = &mut self.kernel.logger {
                logger.log_ideal(&self.ideal)?;
            }
            self.find_nadir()?;
            if let Some(logger) = &mut self.kernel.logger {
                logger.log_nadir(&self.nadir)?;
            }
            self.cut_nadir()?;
            if empty_space(&self.ideal, &self.nadir) {
                break;
            }
            self.block_remaining()?;
        }
        self.kernel.log_routine_end()?;
        Ok(())
    }

    /// Finds the ideal point of the working instance by executing OLL
    /// single-objective optimization. Returns false if the entire pareto front
    /// was found.
    fn find_ideal(&mut self) -> Result<bool, Termination> {
        self.kernel.log_routine_start("find_ideal")?;
        for obj_idx in 0..self.kernel.stats.n_objs {
            let mut obj_ref = self.reforms[obj_idx].take().unwrap();
            match self.kernel.oll(&mut obj_ref, &[], &mut self.tot_db)? {
                Some(_) => (),
                None => return Ok(false),
            };
            // TODO: maybe make use of solution?
            self.ideal[obj_idx] = obj_ref.offset;
            self.reforms[obj_idx] = Some(obj_ref)
        }
        self.kernel.log_routine_end()?;
        Ok(true)
    }

    /// Find the nadir point of the working instance by solving all permutations
    /// of lexicographic optimization with LSU
    fn find_nadir(&mut self) -> Result<(), Termination> {
        self.kernel.log_routine_start("find_nadir")?;
        if self.kernel.stats.n_objs == 2 {
            self.find_nadir_2()?;
        } else {
            self.find_nadir_3()?;
        }
        self.kernel.log_routine_end()?;
        Ok(())
    }

    /// Introduces the nadir point cut
    fn cut_nadir(&mut self) -> Result<(), Termination> {
        for obj_idx in 0..self.kernel.stats.n_objs {
            if self.nadir[obj_idx] == self.ideal[obj_idx] {
                continue;
            }
            let (enc, offset) = self.encodings[obj_idx].as_ref().unwrap();
            dpw::encode_output(
                enc,
                (self.nadir[obj_idx] - offset - 1) / (1 << enc.output_power()),
                &mut self.tot_db,
                &mut self.kernel.oracle,
                &mut self.kernel.var_manager,
            );
            for unit in
                dpw::enforce_ub(enc, self.nadir[obj_idx] - offset - 1, &mut self.tot_db).unwrap()
            {
                self.kernel.oracle.add_unit(unit)?;
            }
        }
        Ok(())
    }

    /// Blocks all solutions that are not cut by the nadir cut with a P-Minimal
    /// clause
    fn block_remaining(&mut self) -> Result<(), Termination> {
        if self.kernel.stats.n_objs == 2 {
            return Ok(());
        }
        let below_nadir = |cost: &[usize; 3]| {
            cost[0] < self.nadir[0] && cost[1] < self.nadir[1] && cost[2] < self.nadir[2]
        };
        for cost in self.disc_costs.drain(..) {
            if !below_nadir(&cost) {
                continue;
            }
            let clause = cost
                .into_iter()
                .enumerate()
                .filter_map(|(idx, cst)| {
                    let (enc, offset) = self.encodings[idx].as_ref().unwrap();
                    if cst - offset == 0 {
                        return None;
                    }
                    dpw::encode_output(
                        enc,
                        (cst - offset - 1) / (1 << enc.output_power()),
                        &mut self.tot_db,
                        &mut self.kernel.oracle,
                        &mut self.kernel.var_manager,
                    );
                    let units = dpw::enforce_ub(enc, cst - offset - 1, &mut self.tot_db).unwrap();
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

    fn build_obj_encoding(&mut self, obj_idx: usize) -> (dpw::Structure, usize) {
        let reform = self.reforms[obj_idx].as_ref().unwrap();
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
        (
            dpw::build_structure(
                cons.into_iter(),
                &mut self.tot_db,
                &mut self.kernel.var_manager,
            ),
            reform.offset,
        )
    }

    fn find_nadir_2(&mut self) -> Result<(), Termination> {
        for ideal_obj in 0..self.kernel.stats.n_objs {
            let obj_ref = self.reforms[ideal_obj].as_ref().unwrap();
            let mut base_assumps: Vec<_> = obj_ref.inactives.iter().map(|(l, _)| !*l).collect();
            let other_obj = (ideal_obj + 1) % self.kernel.stats.n_objs;
            if self.ideal[ideal_obj] == self.nadir[ideal_obj] {
                // non-dom point already found in previous permutation
                debug_assert_eq!(ideal_obj, 1);
                self.nadir[other_obj] = self.ideal[other_obj];
                return Ok(());
            }
            if self.encodings[other_obj].is_none() {
                self.encodings[other_obj] = Some(self.build_obj_encoding(other_obj));
            }
            let (sol, other_cost) = self.linsu(other_obj, &base_assumps)?;
            self.nadir[other_obj] = other_cost;
            let (enc, offset) = self.encodings[other_obj].as_ref().unwrap();
            dpw::encode_output(
                enc,
                (other_cost - offset) / (1 << enc.output_power()),
                &mut self.tot_db,
                &mut self.kernel.oracle,
                &mut self.kernel.var_manager,
            );
            base_assumps
                .extend(dpw::enforce_ub(enc, other_cost - offset, &mut self.tot_db).unwrap());
            let mut costs = vec![0; self.kernel.stats.n_objs];
            costs[ideal_obj] = self.reforms[ideal_obj].as_ref().unwrap().offset;
            costs[other_obj] = other_cost;
            self.kernel
                .yield_solutions(costs, &base_assumps, sol, &mut self.pareto_front)?;
        }
        Ok(())
    }

    fn find_nadir_3(&mut self) -> Result<(), Termination> {
        self.nadir = [0, 0, 0];
        let mut skip = [
            [false, false, false],
            [false, false, false],
            [false, false, false],
        ];
        for ideal_obj in 0..self.kernel.stats.n_objs {
            let obj_ref = self.reforms[ideal_obj].as_ref().unwrap();
            let mut base_assumps: Vec<_> = obj_ref.inactives.iter().map(|(l, _)| !*l).collect();
            let ideal_assump_len = base_assumps.len();
            let mut last_three = usize::MAX;
            for second_obj in 1..self.kernel.stats.n_objs {
                let second_obj = (ideal_obj + second_obj) % self.kernel.stats.n_objs;
                if skip[ideal_obj][second_obj] {
                    continue;
                }
                if self.encodings[second_obj].is_none() {
                    self.encodings[second_obj] = Some(self.build_obj_encoding(second_obj));
                }
                let (_, second_cost) = self.linsu(second_obj, &base_assumps)?;
                if second_cost == self.ideal[second_obj] {
                    skip[second_obj][ideal_obj] = true;
                }
                if second_cost >= last_three {
                    continue;
                }

                let (enc, offset) = self.encodings[second_obj].as_ref().unwrap();
                dpw::encode_output(
                    enc,
                    (second_cost - offset) / (1 << enc.output_power()),
                    &mut self.tot_db,
                    &mut self.kernel.oracle,
                    &mut self.kernel.var_manager,
                );
                base_assumps
                    .extend(dpw::enforce_ub(enc, second_cost - offset, &mut self.tot_db).unwrap());

                let third_obj = 3 - ideal_obj - second_obj;
                if self.encodings[third_obj].is_none() {
                    self.encodings[third_obj] = Some(self.build_obj_encoding(third_obj));
                }
                let (sol, third_cost) = self.linsu(third_obj, &base_assumps)?;
                self.nadir[third_obj] = std::cmp::max(third_cost, self.nadir[third_obj]);
                last_three = third_cost;

                if third_cost == self.ideal[third_obj] {
                    self.nadir = self.ideal;
                    return Ok(());
                }

                let (enc, offset) = self.encodings[third_obj].as_ref().unwrap();
                dpw::encode_output(
                    enc,
                    (third_cost - offset) / (1 << enc.output_power()),
                    &mut self.tot_db,
                    &mut self.kernel.oracle,
                    &mut self.kernel.var_manager,
                );
                base_assumps
                    .extend(dpw::enforce_ub(enc, third_cost - offset, &mut self.tot_db).unwrap());

                let mut costs = vec![0; self.kernel.stats.n_objs];
                costs[ideal_obj] = self.reforms[ideal_obj].as_ref().unwrap().offset;
                costs[second_obj] = second_cost;
                costs[third_obj] = third_cost;
                self.kernel
                    .yield_solutions(costs, &base_assumps, sol, &mut self.pareto_front)?;

                let mut costs = [0, 0, 0];
                costs[ideal_obj] = self.reforms[ideal_obj].as_ref().unwrap().offset;
                costs[second_obj] = second_cost;
                costs[third_obj] = third_cost;
                self.disc_costs.push(costs);

                base_assumps.drain(ideal_assump_len..);
            }
        }
        Ok(())
    }

    fn linsu(
        &mut self,
        obj_idx: usize,
        base_assumps: &[Lit],
    ) -> Result<(Assignment, usize), Termination> {
        self.kernel.log_routine_start("linsu")?;
        let mut assumps = Vec::from(base_assumps);
        let res = self.kernel.solve_assumps(&assumps)?;
        debug_assert_eq!(res, SolverResult::Sat);
        let mut sol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
        let mut cost = self
            .kernel
            .get_cost_with_heuristic_improvements(obj_idx, &mut sol, true)?;
        if cost == 0 {
            self.kernel.log_routine_end()?;
            return Ok((sol, cost));
        }
        let (enc, offset) = self.encodings[obj_idx].as_ref().unwrap();
        let output_weight = 1 << (enc.output_power());
        assumps.push(lit![0]);
        // coarse convergence
        while (cost - offset) >= output_weight {
            let oidx = (cost - offset) / output_weight - 1;
            debug_assert!(oidx < self.tot_db[enc.root].len());
            dpw::encode_output(
                enc,
                oidx,
                &mut self.tot_db,
                &mut self.kernel.oracle,
                &mut self.kernel.var_manager,
            );
            assumps[base_assumps.len()] = !self.tot_db[enc.root][oidx];
            match self.kernel.solve_assumps(&assumps)? {
                SolverResult::Sat => {
                    sol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
                    let new_cost = self
                        .kernel
                        .get_cost_with_heuristic_improvements(obj_idx, &mut sol, false)?;
                    debug_assert!(new_cost < cost);
                    cost = new_cost;
                    if cost == 0 {
                        self.kernel.log_routine_end()?;
                        return Ok((sol, cost));
                    }
                }
                SolverResult::Unsat => break,
                SolverResult::Interrupted => panic!(),
            }
        }
        if (cost - offset) % output_weight == 0 {
            // first call of fine convergence would not set any tares
            debug_assert_eq!(
                if cost - offset > 0 {
                    dpw::enforce_ub(enc, cost - offset - 1, &mut self.tot_db)
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
            &enc,
            (cost - offset - 1) / (1 << enc.output_power()),
            &mut self.tot_db,
            &mut self.kernel.oracle,
            &mut self.kernel.var_manager,
        );
        // fine convergence
        while cost - offset > 0 {
            assumps.drain(base_assumps.len()..);
            assumps.extend(dpw::enforce_ub(enc, cost - offset - 1, &mut self.tot_db).unwrap());
            match self.kernel.solve_assumps(&assumps)? {
                SolverResult::Sat => {
                    sol = self.kernel.oracle.solution(self.kernel.max_orig_var)?;
                    let new_cost = self
                        .kernel
                        .get_cost_with_heuristic_improvements(obj_idx, &mut sol, false)?;
                    debug_assert!(new_cost < cost);
                    cost = new_cost
                }
                SolverResult::Unsat => break,
                SolverResult::Interrupted => panic!(),
            }
        }
        self.kernel.log_routine_end()?;
        Ok((sol, cost))
    }
}
