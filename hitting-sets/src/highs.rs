//! # Hitting Set Solver Interface for the HiGHS Solver

use std::time::Duration;

use highs::{Col, HighsModelStatus, Model, RowProblem, Sense};
use rustsat::types::{Cl, Lit, RsHashMap, Var};

use crate::{CompleteSolveResult, IncompleteSolveResult};

use super::{BuildSolver, HittingSetSolver, VarMap};

pub struct Solver {
    objectives: Vec<RsHashMap<Lit, usize>>,
    multipliers: Vec<f64>,
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

fn get_joint_weight(var: Var, objectives: &[RsHashMap<Lit, usize>], multipliers: &[f64]) -> f64 {
    objectives
        .iter()
        .zip(multipliers)
        .fold(0., |sum, (obj, &mult)| {
            if let Some(&weight) = obj.get(&var.pos_lit()) {
                return sum + (weight as f64) * mult;
            }
            if let Some(&weight) = obj.get(&var.neg_lit()) {
                return sum - (weight as f64) * mult;
            }
            sum
        })
}

impl HittingSetSolver for Solver {
    type Builder = Builder;

    fn change_multipliers(&mut self, multi: &[f64]) {
        self.multipliers.clear();
        self.multipliers.extend(multi.iter().copied());
        match self.state {
            State::Init { .. } => {}
            State::Main(_) => {
                todo!("Update model")
            }
            State::Working => unreachable!("working state should never happen externally"),
        }
    }

    fn add_core(&mut self, core: &Cl) {
        let mut state = std::mem::take(&mut self.state);
        match &mut state {
            State::Init { problem, .. } => {
                let row: Vec<_> = core
                    .iter()
                    .map(|lit| {
                        (
                            self.map.ensure_mapped(lit.var(), || {
                                let weight = get_joint_weight(
                                    lit.var(),
                                    &self.objectives,
                                    &self.multipliers,
                                );
                                problem.add_integer_column(weight, 0..=1)
                            }),
                            if lit.is_pos() { 1. } else { -1. },
                        )
                    })
                    .collect();
                problem.add_row(1.., row);
            }
            State::Main(model) => {
                let row: Vec<_> = core
                    .iter()
                    .map(|lit| {
                        (
                            self.map.ensure_mapped(lit.var(), || {
                                let weight = get_joint_weight(
                                    lit.var(),
                                    &self.objectives,
                                    &self.multipliers,
                                );
                                model.add_integer_column(weight, 0..=1, [])
                            }),
                            if lit.is_pos() { 1. } else { -1. },
                        )
                    })
                    .collect();
                model.add_row(1.., row);
            }
            State::Working => unreachable!("working state should never happen externally"),
        }
        self.state = state;
    }

    fn optimal_hitting_set(&mut self) -> CompleteSolveResult {
        self.solve(None).into()
    }

    fn hitting_set(&mut self, time_limit: Duration) -> IncompleteSolveResult {
        self.solve(Some(time_limit))
    }

    fn add_pd_cut(&mut self, costs: &[usize]) {
        todo!()
    }
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

    fn solve(&mut self, time_limit: Option<Duration>) -> IncompleteSolveResult {
        if matches!(self.state, State::Init { .. }) {
            self.transition_to_main();
        }
        let State::Main(mut model) = std::mem::take(&mut self.state) else {
            unreachable!();
        };
        if let Some(time_limit) = time_limit {
            model.set_option("time_limit", time_limit.as_secs() as f64);
        }
        let solved = model.solve();
        if solved.status() == HighsModelStatus::Infeasible {
            let mut model = Model::from(solved);
            if time_limit.is_some() {
                model.set_option("time_limit", f64::INFINITY);
            }
            self.state = State::Main(model);
            return IncompleteSolveResult::Infeasible;
        }
        if solved.status() == HighsModelStatus::ReachedTimeLimit {
            assert!(time_limit.is_some());
            let mut model = Model::from(solved);
            model.set_option("time_limit", f64::INFINITY);
            self.state = State::Main(model);
            // TODO: figure out how to get a feasible solution
            return IncompleteSolveResult::Unknown;
        }
        assert_eq!(solved.status(), HighsModelStatus::Optimal);
        let solution = solved.get_solution();
        let mut model = Model::from(solved);
        if time_limit.is_some() {
            model.set_option("time_limit", f64::INFINITY);
        }
        self.state = State::Main(model);
        let hitting_set: Vec<_> = solution
            .columns()
            .iter()
            .enumerate()
            .map(|(idx, val)| {
                if *val >= super::TRUE {
                    self.map[idx].pos_lit()
                } else if *val <= super::FALSE {
                    self.map[idx].neg_lit()
                } else {
                    panic!("variable assigned to non-integer value");
                }
            })
            .collect();
        let cost = hitting_set.iter().fold(0., |sum, lit| {
            if lit.is_pos() {
                sum + get_joint_weight(lit.var(), &self.objectives, &self.multipliers)
            } else {
                sum
            }
        });
        IncompleteSolveResult::Optimal(cost, hitting_set)
    }
}

/// The [`BuildSolver`] type for the HiGHS solver
pub struct Builder {
    objectives: Vec<RsHashMap<Lit, usize>>,
    reserve_vars: (usize, usize),
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
        Builder {
            objectives,
            reserve_vars: (0, 0),
            options: Options { threads: 1 },
        }
    }

    fn init(self) -> Self::Solver {
        let multipliers = vec![1.; self.objectives.len()];
        Solver {
            objectives: self.objectives,
            multipliers,
            map: VarMap::new(self.reserve_vars.0, self.reserve_vars.1),
            state: State::Init {
                problem: RowProblem::default(),
                options: self.options,
            },
        }
    }

    fn reserve_vars(&mut self, external: usize, internal: usize) -> &mut Self {
        self.reserve_vars = (external, internal);
        self
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
