//! # Hitting Set Solver Interface for the HiGHS Solver

use std::ops;

use highs::{Col, HighsModelStatus, Model, RowProblem, Sense, Solution};
use rustsat::types::{Cl, Lit, RsHashMap, Var};

use crate::{CompleteSolveResult, IncompleteSolveResult};

use super::{BuildSolver, HittingSetSolver, VarMap};

pub struct Solver {
    objectives: Vec<RsHashMap<Lit, usize>>,
    map: VarMap<Col>,
    state: State,
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
                    let weight = self
                        .objectives
                        .iter()
                        .zip(multi)
                        .fold(0., |sum, (obj, &mult)| {
                            if let Some(&weight) = obj.get(&var.pos_lit()) {
                                return sum + (weight as f64) * mult;
                            }
                            if let Some(&weight) = obj.get(&var.neg_lit()) {
                                return sum - (weight as f64) * mult;
                            }
                            sum
                        });
                    problem.change_column_cost(col, weight);
                }
            }
            State::Main(model) => {
                for (var, &col) in self.map.iter() {
                    let weight = self
                        .objectives
                        .iter()
                        .zip(multi)
                        .fold(0., |sum, (obj, &mult)| {
                            if let Some(&weight) = obj.get(&var.pos_lit()) {
                                return sum + (weight as f64) * mult;
                            }
                            if let Some(&weight) = obj.get(&var.neg_lit()) {
                                return sum - (weight as f64) * mult;
                            }
                            sum
                        });
                    model.change_column_cost(col, weight);
                }
            }
            State::Working => unreachable!("working state should never happen externally"),
        }
    }

    fn add_core(&mut self, core: &Cl) {
        let bound = core
            .iter()
            .fold(1, |b, lit| if lit.is_neg() { b - 1 } else { b });
        self.state.add_row(
            bound..,
            core.iter()
                .map(|lit| (self.map[lit.var()], if lit.is_pos() { 1. } else { -1. })),
        );
    }

    fn optimal_hitting_set(&mut self) -> CompleteSolveResult {
        self.solve(None).into()
    }

    fn hitting_set(&mut self, target_value: usize) -> IncompleteSolveResult {
        self.solve(Some(target_value))
    }

    fn add_pd_cut(&mut self, costs: &[usize]) {
        debug_assert_eq!(costs.len(), self.objectives.len());
        let non_zeroes: Vec<_> = costs
            .iter()
            .enumerate()
            .filter_map(|(idx, &cost)| if cost == 0 { None } else { Some(idx) })
            .collect();
        match non_zeroes.len() {
            // make infeasible
            0 => self.state.add_row(1.., []),
            1 => {
                let obj = &self.objectives[non_zeroes[0]];
                let cost = costs[non_zeroes[0]];
                let sub_cost = obj.iter().fold(
                    0,
                    |sub, (lit, &cost)| if lit.is_neg() { sub + cost } else { sub },
                );
                let bound = (cost - 1) as f64 - sub_cost as f64;
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
                let obj = &self.objectives[non_zeroes[0]];
                let cost = costs[non_zeroes[0]];
                let sub_cost = obj.iter().fold(
                    0,
                    |sub, (lit, &cost)| if lit.is_neg() { sub + cost } else { sub },
                );
                let bound = (cost - 1) as f64 - sub_cost as f64;
                let aux_coeff = obj.iter().fold(
                    0,
                    |max, (lit, &cost)| if lit.is_pos() { max + cost } else { max },
                ) as f64
                    - bound;
                self.state.add_row(
                    ..=bound,
                    self.objectives[non_zeroes[0]]
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
                let obj = &self.objectives[non_zeroes[1]];
                let cost = costs[non_zeroes[1]];
                let sub_cost = obj.iter().fold(
                    0,
                    |sub, (lit, &cost)| if lit.is_neg() { sub + cost } else { sub },
                );
                let bound = (cost - 1) as f64 - sub_cost as f64;
                let aux_coeff = obj.iter().fold(
                    0,
                    |max, (lit, &cost)| if lit.is_pos() { max + cost } else { max },
                ) as f64
                    - bound;
                self.state.add_row(
                    ..=bound + aux_coeff,
                    self.objectives[non_zeroes[1]]
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
                for (nz_idx, obj_idx) in non_zeroes.into_iter().enumerate() {
                    let aux = auxs[nz_idx];
                    let obj = &self.objectives[obj_idx];
                    let cost = costs[obj_idx];
                    let sub_cost = obj.iter().fold(
                        0,
                        |sub, (lit, &cost)| if lit.is_neg() { sub + cost } else { sub },
                    );
                    let bound = (cost - 1) as f64 - sub_cost as f64;
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
}

#[inline]
fn collect_hitting_set(sol: &Solution, map: &VarMap<Col>) -> Vec<Lit> {
    // NOTE: only taking the first `map.max_mapped` entries, since after that we have aux vars from
    // PD cuts
    sol.columns()
        .iter()
        .enumerate()
        .take(map.max_mapped().unwrap().index() + 1)
        .map(|(idx, val)| {
            if *val >= super::TRUE {
                map[idx].pos_lit()
            } else if *val <= super::FALSE {
                map[idx].neg_lit()
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

    fn solve(&mut self, target_value: Option<usize>) -> IncompleteSolveResult {
        if matches!(self.state, State::Init { .. }) {
            self.transition_to_main();
        }
        let State::Main(mut model) = std::mem::take(&mut self.state) else {
            unreachable!();
        };
        if let Some(target_value) = target_value {
            model.set_option("objective_target", target_value as f64);
        }
        let solved = model.solve();
        if solved.status() == HighsModelStatus::Infeasible {
            let mut model = Model::from(solved);
            if target_value.is_some() {
                model.set_option("objective_target", -f64::INFINITY);
            }
            self.state = State::Main(model);
            return IncompleteSolveResult::Infeasible;
        }
        if solved.status() == HighsModelStatus::ObjectiveTarget {
            assert!(target_value.is_some());
            let solution = solved.get_solution();
            let cost = solved.get_objective_value();
            let mut model = Model::from(solved);
            model.set_option("objective_target", -f64::INFINITY);
            self.state = State::Main(model);
            let hitting_set = collect_hitting_set(&solution, &self.map);
            return IncompleteSolveResult::Feasible(cost, hitting_set);
        }
        assert_eq!(solved.status(), HighsModelStatus::Optimal);
        let solution = solved.get_solution();
        let cost = solved.get_objective_value();
        let mut model = Model::from(solved);
        if target_value.is_some() {
            model.set_option("objective_target", -f64::INFINITY);
        }
        self.state = State::Main(model);
        let hitting_set = collect_hitting_set(&solution, &self.map);
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
}

/// The [`BuildSolver`] type for the HiGHS solver
pub struct Builder {
    objectives: Vec<RsHashMap<Lit, usize>>,
    options: Options,
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
            map.ensure_mapped(var, || problem.add_integer_column(weight, 0..=1));
        }
        Solver {
            objectives: self.objectives,
            map,
            state: State::Init {
                problem,
                options: self.options,
            },
        }
    }

    fn threads(&mut self, threads: u32) -> &mut Self {
        self.options.threads =
            i32::try_from(threads).expect("`threads` must be at most `i32::MAX`");
        self
    }
}

impl super::IndexedVar for Col {
    fn index(&self) -> usize {
        Col::index(*self)
    }
}
