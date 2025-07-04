//! # Hitting Set Solver Interface for the HiGHS Solver

use std::{cmp, ops};

use highs::{Col, HighsModelStatus, Model, RowProblem, Sense, Solution};
use rustsat::types::{Lit, RsHashMap, Var};

use crate::{CompleteSolveResult, IncompleteSolveResult};

use super::{BuildSolver, CoreOrigin, HittingSetSolver, Obj, VarMap};

pub struct Solver {
    objectives: Vec<Obj>,
    map: VarMap<Col>,
    state: State,
    statistics: super::Statistics,
    use_start: bool,
}

#[derive(Default)]
enum State {
    Init {
        problem: RowProblem,
        options: Options,
    },
    Main(Model),
    #[default]
    Working,
}

impl HittingSetSolver for Solver {
    type Builder = Builder;

    fn change_multipliers(&mut self, multi: &[f64]) {
        match &mut self.state {
            State::Init { problem, .. } => {
                for (var, &col) in self.map.iter() {
                    let weight = self.objectives.iter().zip(multi).fold(
                        0.,
                        |sum, (Obj { lits, .. }, &mult)| {
                            if let Some(&weight) = lits.get(&var.pos_lit()) {
                                return sum + (weight as f64) * mult;
                            }
                            if let Some(&weight) = lits.get(&var.neg_lit()) {
                                return sum - (weight as f64) * mult;
                            }
                            sum
                        },
                    );
                    problem.change_column_cost(col, weight);
                }
            }
            State::Main(model) => {
                for (var, &col) in self.map.iter() {
                    let weight = self.objectives.iter().zip(multi).fold(
                        0.,
                        |sum, (Obj { lits, .. }, &mult)| {
                            if let Some(&weight) = lits.get(&var.pos_lit()) {
                                return sum + (weight as f64) * mult;
                            }
                            if let Some(&weight) = lits.get(&var.neg_lit()) {
                                return sum - (weight as f64) * mult;
                            }
                            sum
                        },
                    );
                    model.change_column_cost(col, weight);
                }
            }
            State::Working => unreachable!("working state should never happen externally"),
        }
    }

    fn add_card_core(&mut self, lits: &[Lit], bound: usize, origin: CoreOrigin) {
        self.statistics.n_cores += 1;
        match origin {
            CoreOrigin::Seeding => {
                self.statistics.n_seeded += 1;
            }
            CoreOrigin::CoreBoosting => (),
            CoreOrigin::Normal => (),
            CoreOrigin::Abstract => {
                self.statistics.n_abstract_cores += 1;
            }
        }
        let bound = lits.iter().fold(
            i32::try_from(bound).expect("`bound` does not fit in `i32`"),
            |b, lit| if lit.is_neg() { b - 1 } else { b },
        );
        self.state.add_row(
            bound..,
            lits.iter()
                .map(|lit| (self.map[lit.var()], if lit.is_pos() { 1. } else { -1. })),
        );
    }

    fn add_card(&mut self, lits: &[Lit], bound: usize) {
        let bound = lits.iter().fold(
            i32::try_from(bound).expect("`bound` does not fit in `i32`"),
            |b, lit| if lit.is_neg() { b - 1 } else { b },
        );
        let factors: Vec<_> = lits
            .iter()
            .map(|lit| {
                (
                    self.map
                        .ensure_mapped(lit.var(), |_| self.state.new_binary_col(0.)),
                    if lit.is_pos() { 1. } else { -1. },
                )
            })
            .collect();
        self.state.add_row(bound.., factors);
    }

    fn add_card_eq(&mut self, lits: &[Lit], value: usize) {
        let value = lits.iter().fold(
            i32::try_from(value).expect("`value` does not fit in `i32`"),
            |b, lit| if lit.is_neg() { b - 1 } else { b },
        );
        let factors: Vec<_> = lits
            .iter()
            .map(|lit| {
                (
                    self.map
                        .ensure_mapped(lit.var(), |_| self.state.new_binary_col(0.)),
                    if lit.is_pos() { 1. } else { -1. },
                )
            })
            .collect();
        self.state.add_row(value..=value, factors);
    }

    fn add_reified_card(&mut self, lits: &[Lit], bound: usize, reif: Lit, equivalence: bool) {
        let (bound, n_pos) = lits.iter().fold(
            (
                i32::try_from(bound).expect("`bound` does not fit in `i32`"),
                0,
            ),
            |(b, n), lit| {
                if lit.is_neg() {
                    (b - 1, n)
                } else {
                    (b, n + 1)
                }
            },
        );
        let mut factors: Vec<_> = lits
            .iter()
            .map(|lit| {
                (
                    self.map
                        .ensure_mapped(lit.var(), |_| self.state.new_binary_col(0.)),
                    if lit.is_pos() { 1. } else { -1. },
                )
            })
            .collect();
        let big_m = n_pos - bound + 1;
        let ind = self
            .map
            .ensure_mapped(reif.var(), |_| self.state.new_binary_col(0.));
        factors.push((ind, (big_m * if reif.is_pos() { -1 } else { 1 }) as f64));
        self.state.add_row(
            ..=if reif.is_pos() { bound - 1 } else { n_pos },
            factors.iter().copied(),
        );

        if equivalence {
            let n_neg = i32::try_from(lits.len()).expect("more than `i32::MAX` lits") - n_pos;
            let big_m = bound - n_neg;
            factors.last_mut().unwrap().1 = (big_m * if reif.is_pos() { -1 } else { 1 }) as f64;
            self.state
                .add_row(if reif.is_pos() { -n_neg } else { bound }.., factors);
        }
    }

    fn optimal_hitting_set<I>(&mut self, start: I) -> CompleteSolveResult
    where
        I: IntoIterator<Item = Lit>,
    {
        self.solve(start, true).into()
    }

    fn hitting_set<I>(&mut self, start: I) -> IncompleteSolveResult
    where
        I: IntoIterator<Item = Lit>,
    {
        self.solve(start, false)
    }

    fn add_pd_cut(&mut self, costs: &[usize]) {
        debug_assert_eq!(costs.len(), self.objectives.len());
        let non_zeroes: Vec<_> = costs
            .iter()
            .zip(&self.objectives)
            .enumerate()
            .filter_map(|(idx, (&cost, Obj { lower_bound, .. }))| {
                if cost <= *lower_bound {
                    None
                } else {
                    Some(idx)
                }
            })
            .collect();
        match non_zeroes.len() {
            // make infeasible
            0 => self.state.add_row(1.., []),
            1 => {
                let obj = &self.objectives[non_zeroes[0]].lits;
                let cost = costs[non_zeroes[0]];
                let sub_cost = obj.iter().fold(
                    0,
                    |sub, (lit, &cost)| if lit.is_neg() { sub + cost } else { sub },
                );
                let bound =
                    (cost - self.objectives[non_zeroes[0]].offset - 1) as f64 - sub_cost as f64;
                self.state.add_row(
                    ..=bound,
                    obj.iter().map(|(&lit, &cost)| {
                        (
                            self.map[lit.var()],
                            if lit.is_pos() {
                                cost as f64
                            } else {
                                -(cost as f64)
                            },
                        )
                    }),
                );
            }
            2 => {
                // special case, using only one aux var and two constraints
                let aux = self.state.new_binary_col(0.);

                // constraint for first objective
                let obj = &self.objectives[non_zeroes[0]].lits;
                let cost = costs[non_zeroes[0]];
                let sub_cost = obj.iter().fold(
                    0,
                    |sub, (lit, &cost)| if lit.is_neg() { sub + cost } else { sub },
                );
                let bound =
                    (cost - self.objectives[non_zeroes[0]].offset - 1) as f64 - sub_cost as f64;
                let aux_coeff = obj.iter().fold(
                    0,
                    |max, (lit, &cost)| if lit.is_pos() { max + cost } else { max },
                ) as f64
                    - bound;
                self.state.add_row(
                    ..=bound,
                    self.objectives[non_zeroes[0]]
                        .lits
                        .iter()
                        .map(|(&lit, &cost)| {
                            (
                                self.map[lit.var()],
                                if lit.is_pos() {
                                    cost as f64
                                } else {
                                    -(cost as f64)
                                },
                            )
                        })
                        .chain([(aux, -aux_coeff)]),
                );
                // constraint for second objective
                let obj = &self.objectives[non_zeroes[1]].lits;
                let cost = costs[non_zeroes[1]];
                let sub_cost = obj.iter().fold(
                    0,
                    |sub, (lit, &cost)| if lit.is_neg() { sub + cost } else { sub },
                );
                let bound =
                    (cost - self.objectives[non_zeroes[1]].offset - 1) as f64 - sub_cost as f64;
                let aux_coeff = obj.iter().fold(
                    0,
                    |max, (lit, &cost)| if lit.is_pos() { max + cost } else { max },
                ) as f64
                    - bound;
                self.state.add_row(
                    ..=bound + aux_coeff,
                    self.objectives[non_zeroes[1]]
                        .lits
                        .iter()
                        .map(|(&lit, &cost)| {
                            (
                                self.map[lit.var()],
                                if lit.is_pos() {
                                    cost as f64
                                } else {
                                    -(cost as f64)
                                },
                            )
                        })
                        .chain([(aux, aux_coeff)]),
                );
            }
            p => {
                let auxs: Vec<_> = (0..p).map(|_| self.state.new_binary_col(0.)).collect();
                // reified constraints for each objective
                for (obj_idx, &aux) in non_zeroes.into_iter().zip(&auxs) {
                    let obj = &self.objectives[obj_idx].lits;
                    let cost = costs[obj_idx];
                    let sub_cost = obj.iter().fold(
                        0,
                        |sub, (lit, &cost)| if lit.is_neg() { sub + cost } else { sub },
                    );
                    let bound =
                        (cost - self.objectives[obj_idx].offset - 1) as f64 - sub_cost as f64;
                    let aux_coeff = obj.iter().fold(
                        0,
                        |max, (lit, &cost)| if lit.is_pos() { max + cost } else { max },
                    ) as f64
                        - bound;
                    self.state.add_row(
                        ..=bound,
                        obj.iter()
                            .map(|(&lit, &cost)| {
                                (
                                    self.map[lit.var()],
                                    if lit.is_pos() {
                                        cost as f64
                                    } else {
                                        -(cost as f64)
                                    },
                                )
                            })
                            .chain([(aux, -aux_coeff)]),
                    );
                }
                // clause over the reified constraints
                self.state
                    .add_row(1. - p as f64.., auxs.into_iter().map(|aux| (aux, -1.)));
            }
        }
    }

    fn change_objectives<Outer, Inner>(&mut self, objectives: Outer)
    where
        Outer: IntoIterator<Item = (Inner, usize)>,
        Inner: IntoIterator<Item = (Lit, usize)>,
    {
        let _n_old_objs = self.objectives.len();
        self.objectives = objectives
            .into_iter()
            .zip(&self.objectives)
            .map(|((inner, offset), Obj { lower_bound, .. })| Obj {
                lits: inner.into_iter().collect(),
                offset,
                lower_bound: cmp::max(*lower_bound, offset),
            })
            .collect();
        debug_assert_eq!(_n_old_objs, self.objectives.len());
        let mut vars: Vec<Var> = self
            .objectives
            .iter()
            .flat_map(|Obj { lits, .. }| lits.keys().copied().map(Lit::var))
            .collect();
        vars.sort_unstable();
        vars.dedup();
        match &mut self.state {
            State::Init { problem, .. } => {
                // clear old objective weights
                for (_, &col) in self.map.iter() {
                    problem.change_column_cost(col, 0.);
                }
                // update objectives
                for var in vars {
                    let weight = self.objectives.iter().fold(0., |sum, Obj{lits,..}| {
                        if let Some(&weight) = lits.get(&var.pos_lit()) {
                            return sum + (weight as f64);
                        }
                        if let Some(&weight) = lits.get(&var.neg_lit()) {
                            return sum - (weight as f64);
                        }
                        sum
                    });
                    let col = self.map.ensure_mapped(var, |_| problem.add_integer_column(weight, 0..=1));
                    problem.change_column_cost(col, weight);
                }
            }
            State::Main(_) => todo!("since this is only used in core boosting, the solver should alwasy be in the Init state"),
            State::Working => unreachable!("working state should never happen externally"),
        }
    }

    fn change_lower_bounds<Iter>(&mut self, lower_bounds: Iter)
    where
        Iter: IntoIterator<Item = usize>,
    {
        for (lb, Obj { lower_bound, .. }) in
            lower_bounds.into_iter().zip(self.objectives.iter_mut())
        {
            *lower_bound = lb;
        }
    }

    fn statistics(&self) -> super::Statistics {
        self.statistics
    }

    fn objectives(&self) -> impl Iterator<Item = impl Iterator<Item = (Lit, usize)>> {
        self.objectives
            .iter()
            .map(|Obj { lits, .. }| lits.iter().map(|(&l, &w)| (l, w)))
    }

    fn learn_unit(&mut self, unit: Lit) {
        self.statistics.n_learned_units += 1;
        let col = self.map[unit.var()];
        self.state.fix_value(col, unit.is_pos());
    }
}

#[inline]
fn collect_hitting_set(sol: &Solution, map: &VarMap<Col>) -> Vec<Lit> {
    sol.columns()
        .iter()
        .enumerate()
        .take(map.max_mapped().unwrap().index() + 1)
        .filter_map(|(idx, val)| {
            let var = map.map_back(idx)?;
            if *val >= super::TRUE {
                Some(var.pos_lit())
            } else if *val <= super::FALSE {
                Some(var.neg_lit())
            } else {
                panic!("variable assigned to non-integer value");
            }
        })
        .collect()
}

impl Solver {
    fn transition_to_main(&mut self) {
        let State::Init { problem, options } = std::mem::take(&mut self.state) else {
            panic!("`transition_to_main` must be called in `State::Init`")
        };
        let mut model = problem.optimise(Sense::Minimise);
        model.set_option("threads", options.threads);
        self.state = State::Main(model);
    }

    fn solve<I>(&mut self, start: I, optimal: bool) -> IncompleteSolveResult
    where
        I: IntoIterator<Item = Lit>,
    {
        self.statistics.n_solves += 1;
        let start_time = cpu_time::ProcessTime::now();
        if matches!(self.state, State::Init { .. }) {
            self.transition_to_main();
        }
        let State::Main(mut model) = std::mem::take(&mut self.state) else {
            unreachable!();
        };

        // handle starting point
        let mut target = 0.;
        let mut start_vec = if self.use_start {
            vec![0.; model.num_cols()]
        } else {
            vec![]
        };
        for l in start {
            if let Some(col) = self.map.map(l.var()) {
                if !optimal {
                    for Obj { lits, .. } in &self.objectives {
                        if let Some(&weight) = lits.get(&l) {
                            if l.is_pos() {
                                target += weight as f64;
                            } else {
                                target -= weight as f64;
                            }
                        }
                    }
                };
                if self.use_start && l.is_pos() {
                    start_vec[col.index()] = 1.;
                }
            }
        }
        if self.use_start {
            model.set_solution(Some(&start_vec), None, None, None);
        }
        if !optimal {
            model.set_option("objective_target", target);
        }

        let solved = model.solve();
        if solved.status() == HighsModelStatus::Infeasible {
            let mut model = Model::from(solved);
            if !optimal {
                model.set_option("objective_target", -f64::INFINITY);
            }
            self.state = State::Main(model);
            self.statistics.solve_time += start_time.elapsed();
            return IncompleteSolveResult::Infeasible;
        }
        if solved.status() == HighsModelStatus::ObjectiveTarget {
            debug_assert!(!optimal);
            let solution = solved.get_solution();
            let cost = solved.get_objective_value();
            let mut model = Model::from(solved);
            model.set_option("objective_target", -f64::INFINITY);
            self.state = State::Main(model);
            let hitting_set = collect_hitting_set(&solution, &self.map);
            self.statistics.solve_time += start_time.elapsed();
            return IncompleteSolveResult::Feasible(cost, hitting_set);
        }
        assert_eq!(solved.status(), HighsModelStatus::Optimal);
        let solution = solved.get_solution();
        let cost = solved.get_objective_value();
        let mut model = Model::from(solved);
        if !optimal {
            model.set_option("objective_target", -f64::INFINITY);
        }
        self.state = State::Main(model);
        let hitting_set = collect_hitting_set(&solution, &self.map);
        self.statistics.solve_time += start_time.elapsed();
        IncompleteSolveResult::Optimal(cost, hitting_set)
    }
}

impl State {
    fn add_row<N, B>(&mut self, bounds: B, row_factors: impl IntoIterator<Item = (Col, f64)>)
    where
        N: Into<f64> + Copy,
        B: ops::RangeBounds<N>,
    {
        match self {
            State::Init { problem, .. } => {
                problem.add_row(bounds, row_factors);
            }
            State::Main(model) => {
                model.add_row(bounds, row_factors);
            }
            State::Working => unreachable!("cannot add row in working state"),
        }
    }

    fn new_binary_col(&mut self, factor: f64) -> Col {
        match self {
            State::Init { problem, .. } => problem.add_integer_column(factor, 0..=1),
            State::Main(model) => model.add_integer_column(factor, 0..=1, []),
            State::Working => unreachable!("cannot add col in working state"),
        }
    }

    fn fix_value(&mut self, col: Col, val: bool) {
        match self {
            State::Init { problem, .. } => {
                if val {
                    problem.change_column_bounds(col, 1.0..=1.);
                } else {
                    problem.change_column_bounds(col, 0.0..=0.);
                }
            }
            State::Main(model) => {
                if val {
                    model.change_column_bounds(col, 1.0..=1.);
                } else {
                    model.change_column_bounds(col, 0.0..=0.);
                }
            }
            State::Working => unreachable!("cannot learn unit in working state"),
        }
    }
}

/// The [`BuildSolver`] type for the HiGHS solver
pub struct Builder {
    objectives: Vec<RsHashMap<Lit, usize>>,
    options: Options,
    use_start: bool,
}

struct Options {
    threads: i32,
}

impl BuildSolver for Builder {
    type Solver = Solver;

    fn new<Outer, Inner>(objectives: Outer) -> Self
    where
        Outer: IntoIterator<Item = Inner>,
        Inner: IntoIterator<Item = (Lit, usize)>,
    {
        let objectives: Vec<RsHashMap<_, _>> = objectives
            .into_iter()
            .map(|inner| inner.into_iter().collect())
            .collect();
        debug_assert!(!objectives.is_empty());
        Builder {
            objectives,
            options: Options { threads: 1 },
            use_start: true,
        }
    }

    fn init(self) -> Self::Solver {
        // Initialize problem with all objective variables
        let mut problem = RowProblem::default();
        let mut vars: Vec<Var> = self
            .objectives
            .iter()
            .flat_map(|obj| obj.keys().copied().map(Lit::var))
            .collect();
        vars.sort_unstable();
        vars.dedup();
        let mut map = VarMap::new(vars.last().map_or(0, |var| var.idx() + 1), vars.len());
        for var in vars {
            let weight = self.objectives.iter().fold(0., |sum, obj| {
                if let Some(&weight) = obj.get(&var.pos_lit()) {
                    return sum + (weight as f64);
                }
                if let Some(&weight) = obj.get(&var.neg_lit()) {
                    return sum - (weight as f64);
                }
                sum
            });
            map.ensure_mapped(var, |_| problem.add_integer_column(weight, 0..=1));
        }
        Solver {
            objectives: self
                .objectives
                .into_iter()
                .map(|lits| Obj {
                    lits,
                    ..Obj::default()
                })
                .collect(),
            map,
            state: State::Init {
                problem,
                options: self.options,
            },
            statistics: super::Statistics::default(),
            use_start: self.use_start,
        }
    }

    fn threads(&mut self, threads: super::Threads) -> &mut Self {
        self.options.threads = match threads {
            crate::Threads::Auto => 0,
            crate::Threads::N(non_zero) => i32::from(non_zero.get()),
        };
        self
    }

    fn use_starting_points(&mut self, use_start: bool) -> &mut Self {
        self.use_start = use_start;
        self
    }
}

impl super::IndexedVar for Col {
    fn index(&self) -> usize {
        Col::index(*self)
    }
}
