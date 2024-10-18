//! # Hitting Set Solver Interface for the HiGHS Solver

use std::time::Duration;

use highs::{Col, HighsModelStatus, Model, RowProblem, Sense};
use rustsat::types::{Cl, Lit, RsHashMap};

use super::{BuildSolver, HittingSetSolver, VarMap};

pub struct Solver {
    weights: RsHashMap<Lit, usize>,
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

    fn add_core(&mut self, core: &Cl) {
        let mut state = std::mem::take(&mut self.state);
        match &mut state {
            State::Init { problem, .. } => {
                let row: Vec<_> = core
                    .iter()
                    .map(|lit| {
                        (
                            self.map.ensure_mapped(*lit, || {
                                problem.add_integer_column(
                                    (*self.weights.get(lit).unwrap()) as f64,
                                    0..=1,
                                )
                            }),
                            1_f64,
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
                            self.map.ensure_mapped(*lit, || {
                                model.add_integer_column(
                                    (*self.weights.get(lit).unwrap()) as f64,
                                    0..=1,
                                    [],
                                )
                            }),
                            1_f64,
                        )
                    })
                    .collect();
                model.add_row(1.., row);
            }
            State::Working => unreachable!("working state should never happen externally"),
        }
        self.state = state;
    }

    fn optimal_hitting_set(&mut self) -> (usize, Vec<Lit>) {
        self.solve(None).unwrap()
    }

    fn hitting_set(&mut self, time_limit: Duration) -> Option<(usize, Vec<Lit>)> {
        self.solve(Some(time_limit))
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

    fn solve(&mut self, time_limit: Option<Duration>) -> Option<(usize, Vec<Lit>)> {
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
        if solved.status() == HighsModelStatus::ReachedTimeLimit {
            assert!(time_limit.is_some());
            let mut model = Model::from(solved);
            model.set_option("time_limit", f64::INFINITY);
            self.state = State::Main(model);
            return None;
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
            .filter_map(|(idx, val)| {
                if *val >= super::TRUE {
                    Some(self.map[idx])
                } else {
                    None
                }
            })
            .collect();
        let cost = hitting_set
            .iter()
            .fold(0, |sum, lit| sum + self.weights[lit]);
        Some((cost, hitting_set))
    }
}

/// The [`BuildSolver`] type for the HiGHS solver
pub struct Builder {
    weights: RsHashMap<Lit, usize>,
    reserve_vars: (usize, usize),
    options: Options,
}

struct Options {
    threads: i32,
}

impl BuildSolver for Builder {
    type Solver = Solver;

    fn new<I>(weights: I) -> Self
    where
        I: IntoIterator<Item = (Lit, usize)>,
    {
        Builder {
            weights: weights.into_iter().collect(),
            reserve_vars: (0, 0),
            options: Options { threads: 1 },
        }
    }

    fn init(self) -> Self::Solver {
        Solver {
            weights: self.weights,
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
