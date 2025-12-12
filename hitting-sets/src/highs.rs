//! # Hitting Set Solver Interface for the HiGHS Solver

use std::cmp;

use highs::{Col, HighsModelStatus, Model, Solution};
use rustsat::types::{Lit, RsHashMap, TernaryVal, Var};

use crate::{
    Callbacks, CompleteSolveResult, IncompleteSolveResult,
    MaybeTerminated::{self, Done},
    ReducedCostsResult,
};

use super::{BuildSolver, CoreOrigin, HittingSetSolver, Obj, VarMap};

pub struct Solver {
    objectives: Vec<Obj>,
    map: VarMap<Col>,
    statistics: super::Statistics,
    use_start: bool,
    units: Vec<TernaryVal>,
    model: model::Model,
}

impl HittingSetSolver for Solver {
    type Builder = Builder;

    fn change_multipliers(&mut self, multi: &[f64]) {
        for (var, &col) in self.map.iter() {
            let weight =
                self.objectives
                    .iter()
                    .zip(multi)
                    .fold(0., |sum, (Obj { lits, .. }, &mult)| {
                        if let Some(&weight) = lits.get(&var.pos_lit()) {
                            return sum + (weight as f64) * mult;
                        }
                        if let Some(&weight) = lits.get(&var.neg_lit()) {
                            return sum - (weight as f64) * mult;
                        }
                        sum
                    });
            self.model.set_obj_coeff(col, weight);
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
        self.model.add_row(
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
                        .ensure_mapped(lit.var(), |_| self.model.new_binary_col(0.)),
                    if lit.is_pos() { 1. } else { -1. },
                )
            })
            .collect();
        self.model.add_row(bound.., factors);
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
                        .ensure_mapped(lit.var(), |_| self.model.new_binary_col(0.)),
                    if lit.is_pos() { 1. } else { -1. },
                )
            })
            .collect();
        self.model.add_row(value..=value, factors);
    }

    fn add_reified_card(&mut self, lits: &[Lit], bound: usize, reif: Lit, equivalence: bool) {
        let (bound, n_pos) = lits.iter().fold(
            (
                i32::try_from(bound).expect("`bound` does not fit in `i32`"),
                0,
            ),
            |(b, n), lit| {
                if lit.is_neg() { (b - 1, n) } else { (b, n + 1) }
            },
        );
        let mut factors: Vec<_> = lits
            .iter()
            .map(|lit| {
                (
                    self.map
                        .ensure_mapped(lit.var(), |_| self.model.new_binary_col(0.)),
                    if lit.is_pos() { 1. } else { -1. },
                )
            })
            .collect();
        let big_m = n_pos - bound + 1;
        let ind = self
            .map
            .ensure_mapped(reif.var(), |_| self.model.new_binary_col(0.));
        factors.push((ind, (big_m * if reif.is_pos() { -1 } else { 1 }) as f64));
        self.model.add_row(
            ..=if reif.is_pos() { bound - 1 } else { n_pos },
            factors.iter().copied(),
        );

        if equivalence {
            let n_neg = i32::try_from(lits.len()).expect("more than `i32::MAX` lits") - n_pos;
            let big_m = bound - n_neg;
            factors.last_mut().unwrap().1 = (big_m * if reif.is_pos() { -1 } else { 1 }) as f64;
            self.model
                .add_row(if reif.is_pos() { -n_neg } else { bound }.., factors);
        }
    }

    fn optimal_hitting_set_callbacks<I, Cb>(
        &mut self,
        start: I,
        cb: &mut Cb,
    ) -> MaybeTerminated<CompleteSolveResult>
    where
        I: IntoIterator<Item = Lit>,
        Cb: Callbacks,
    {
        self.statistics.n_solves += 1;
        self.solve_ip(start, true, cb)
            .map(CompleteSolveResult::from)
    }

    fn hitting_set_callbacks<I, Cb>(
        &mut self,
        start: I,
        cb: &mut Cb,
    ) -> MaybeTerminated<IncompleteSolveResult>
    where
        I: IntoIterator<Item = Lit>,
        Cb: Callbacks,
    {
        self.statistics.n_solves += 1;
        self.solve_ip(start, false, cb)
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
            0 => self.model.add_row(1.., []),
            1 => {
                let obj = &self.objectives[non_zeroes[0]].lits;
                let cost = costs[non_zeroes[0]];
                let sub_cost = obj.iter().fold(
                    0,
                    |sub, (lit, &cost)| if lit.is_neg() { sub + cost } else { sub },
                );
                let bound =
                    (cost - self.objectives[non_zeroes[0]].offset - 1) as f64 - sub_cost as f64;
                self.model.add_row(
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
                let aux = self.model.new_binary_col(0.);

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
                self.model.add_row(
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
                self.model.add_row(
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
                let auxs: Vec<_> = (0..p).map(|_| self.model.new_binary_col(0.)).collect();
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
                    self.model.add_row(
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
                self.model
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
        // clear old objective weights
        for (_, &gv) in self.map.iter() {
            self.model.set_obj_coeff(gv, 0.);
        }
        // update objectives
        for var in vars {
            let weight = self.objectives.iter().fold(0., |sum, Obj { lits, .. }| {
                if let Some(&weight) = lits.get(&var.pos_lit()) {
                    return sum + (weight as f64);
                }
                if let Some(&weight) = lits.get(&var.neg_lit()) {
                    return sum - (weight as f64);
                }
                sum
            });
            let col = self
                .map
                .ensure_mapped(var, |_| self.model.new_binary_col(weight));
            self.model.set_obj_coeff(col, weight);
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
        if self.units.len() <= col.index() {
            self.units.resize(col.index() + 1, TernaryVal::DontCare);
        }
        self.units[col.index()] = TernaryVal::from(unit.is_pos());
        self.model.fix_value(col, unit.is_pos());
    }

    fn reduced_costs_callback<Cb>(&mut self, _cb: &mut Cb) -> MaybeTerminated<ReducedCostsResult>
    where
        Cb: Callbacks,
    {
        let start_time = cpu_time::ProcessTime::now();
        let (ip, Some(lp)) = self.model.get_models() else {
            panic!("cannot get reduced costs without lp");
        };

        let solved = lp.solve();
        if solved.status() == HighsModelStatus::Unknown {
            let lp = Model::from(solved);
            self.model.put_models(ip, Some(lp));
            self.statistics.lp_solve_time += start_time.elapsed();
            return MaybeTerminated::Terminated;
        }
        if solved.status() == HighsModelStatus::Infeasible {
            let lp = Model::from(solved);
            self.model.put_models(ip, Some(lp));
            self.statistics.lp_solve_time += start_time.elapsed();
            return Done(ReducedCostsResult::Infeasible);
        }
        assert_eq!(solved.status(), HighsModelStatus::Optimal);
        let solution = solved.get_solution();
        debug_assert_eq!(solution.columns().len(), solution.dual_columns().len());
        let res = ReducedCostsResult::ReducedCosts {
            obj_val: solved.objective_value(),
            rcs: self
                .map
                .iter()
                .zip(solution.columns())
                .zip(solution.dual_columns())
                .filter_map(|(((rv, _), &val), &rc)| {
                    if val >= crate::TRUE {
                        Some((rv, true, rc))
                    } else if val <= crate::FALSE {
                        Some((rv, false, rc))
                    } else {
                        None
                    }
                })
                .collect(),
        };
        let lp = Model::from(solved);
        self.model.put_models(ip, Some(lp));
        Done(res)
    }

    fn fix<I>(&mut self, to_fix: I) -> bool
    where
        I: IntoIterator<Item = Lit>,
    {
        for lit in to_fix {
            let var = self.map[lit.var()];
            let unit = self
                .units
                .get(var.index())
                .copied()
                .unwrap_or(TernaryVal::DontCare);
            if unit.to_bool_with_def(lit.is_pos()) != lit.is_pos() {
                // fixing disagrees with unit -> unsat
                return false;
            }
            self.model.fix_value(var, lit.is_pos());
        }
        true
    }

    fn unfix_all(&mut self) {
        self.model
            .unfix_cols(self.map.iter().filter_map(|(_, &gv)| {
                if self
                    .units
                    .get(gv.index())
                    .is_none_or(|&u| u == TernaryVal::DontCare)
                {
                    Some(gv)
                } else {
                    None
                }
            }));
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
    pub fn solve_ip<I, Cb>(
        &mut self,
        start: I,
        optimal: bool,
        cb: &mut Cb,
    ) -> MaybeTerminated<IncompleteSolveResult>
    where
        I: IntoIterator<Item = Lit>,
        Cb: Callbacks,
    {
        let start_time = cpu_time::ProcessTime::now();
        let (mut ip, lp) = self.model.get_models();

        // handle starting point
        let mut target = 0.;
        let mut start_vec = if self.use_start {
            vec![0.; ip.num_cols()]
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
            ip.set_solution(Some(&start_vec), None, None, None);
        }
        if !optimal {
            ip.set_option("objective_target", target);
        }

        let solved = ip.solve_with_callback(&mut HighsCallbacks(cb));
        if solved.status() == HighsModelStatus::Unknown {
            let mut ip = Model::from(solved);
            if !optimal {
                ip.set_option("objective_target", -f64::INFINITY);
            }
            self.model.put_models(ip, lp);
            self.statistics.solve_time += start_time.elapsed();
            return MaybeTerminated::Terminated;
        }
        if solved.status() == HighsModelStatus::Infeasible {
            let mut ip = Model::from(solved);
            if !optimal {
                ip.set_option("objective_target", -f64::INFINITY);
            }
            self.model.put_models(ip, lp);
            self.statistics.solve_time += start_time.elapsed();
            return Done(IncompleteSolveResult::Infeasible);
        }
        if solved.status() == HighsModelStatus::ObjectiveTarget {
            debug_assert!(!optimal);
            let solution = solved.get_solution();
            let cost = solved.objective_value();
            let mut ip = Model::from(solved);
            ip.set_option("objective_target", -f64::INFINITY);
            self.model.put_models(ip, lp);
            let hitting_set = collect_hitting_set(&solution, &self.map);
            self.statistics.solve_time += start_time.elapsed();
            return Done(IncompleteSolveResult::Feasible(cost, hitting_set));
        }
        assert_eq!(solved.status(), HighsModelStatus::Optimal);
        let solution = solved.get_solution();
        let cost = solved.objective_value();
        let mut ip = Model::from(solved);
        if !optimal {
            ip.set_option("objective_target", -f64::INFINITY);
        }
        self.model.put_models(ip, lp);
        let hitting_set = collect_hitting_set(&solution, &self.map);
        self.statistics.solve_time += start_time.elapsed();
        Done(IncompleteSolveResult::Optimal(cost, hitting_set))
    }
}

/// Highs callback wrapper around crate callbacks
struct HighsCallbacks<'cb, Cb>(&'cb mut Cb);

impl<Cb> highs::Callback for HighsCallbacks<'_, Cb>
where
    Cb: Callbacks,
{
    fn callback(
        &mut self,
        _context: highs::callback::CallbackOuterContext<'_>,
    ) -> highs::callback::CallbackReturn {
        let mut ret = highs::callback::CallbackReturn::default();
        ret.set_interrupt(self.0.check_termination());
        ret
    }
}

/// The [`BuildSolver`] type for the HiGHS solver
pub struct Builder {
    objectives: Vec<RsHashMap<Lit, usize>>,
    options: Options,
    use_start: bool,
    might_need_lp: bool,
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
            might_need_lp: false,
        }
    }

    fn init(self) -> Self::Solver {
        // Initialize model with all objective variables
        let mut vars: Vec<Var> = self
            .objectives
            .iter()
            .flat_map(|obj| obj.keys().copied().map(Lit::var))
            .collect();
        vars.sort_unstable();
        vars.dedup();
        let mut map = VarMap::new(vars.last().map_or(0, |var| var.idx() + 1), vars.len());
        let obj = vars.into_iter().map(|var| {
            let weight = self.objectives.iter().fold(0., |sum, obj| {
                if let Some(&weight) = obj.get(&var.pos_lit()) {
                    return sum + (weight as f64);
                }
                if let Some(&weight) = obj.get(&var.neg_lit()) {
                    return sum - (weight as f64);
                }
                sum
            });
            (var, weight)
        });
        let model = model::Model::new(obj, self.options, self.might_need_lp, &mut map);
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
            statistics: super::Statistics::default(),
            use_start: self.use_start,
            model,
            units: vec![],
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

    fn might_need_lp(&mut self, _might_need: bool) -> &mut Self {
        self.might_need_lp = true;
        self
    }
}

impl super::IndexedVar for Col {
    fn index(&self) -> usize {
        Col::index(*self)
    }
}

mod model {
    use std::ops::RangeBounds;

    use highs::{Col, RowProblem, Sense};
    use rustsat::types::Var;

    use crate::map::VarMap;

    /// HiGHS model with LP relaxation
    ///
    /// Encapsulated to help with keeping the models in sync
    pub struct Model(State);

    #[derive(Default)]
    enum State {
        Init {
            ip: RowProblem,
            lp: Option<RowProblem>,
            options: super::Options,
        },
        Main {
            ip: highs::Model,
            lp: Option<highs::Model>,
        },
        #[default]
        Working,
    }

    impl Model {
        pub fn new<Obj>(
            obj: Obj,
            options: super::Options,
            might_need_lp: bool,
            var_map: &mut VarMap<Col>,
        ) -> Self
        where
            Obj: IntoIterator<Item = (Var, f64)>,
        {
            let mut ip = RowProblem::default();
            let mut lp = if might_need_lp {
                Some(RowProblem::default())
            } else {
                None
            };

            for (var, weight) in obj {
                var_map.ensure_mapped(var, |_| {
                    let ip_col = ip.add_integer_column(weight, 0..=1);
                    if let Some(lp) = &mut lp {
                        let lp_col = lp.add_column(weight, 0..=1);
                        debug_assert_eq!(ip_col, lp_col);
                    }
                    ip_col
                });
            }

            Self(State::Init { ip, lp, options })
        }

        pub fn set_obj_coeff(&mut self, col: Col, coeff: f64) {
            match &mut self.0 {
                State::Init { ip, lp, .. } => {
                    ip.change_column_cost(col, coeff);
                    if let Some(lp) = lp {
                        lp.change_column_cost(col, coeff);
                    }
                }
                State::Main { ip, lp } => {
                    ip.change_column_cost(col, coeff);
                    if let Some(lp) = lp {
                        lp.change_column_cost(col, coeff);
                    }
                }
                State::Working => unreachable!("working state should never happen externally"),
            }
        }

        pub fn add_row<N: Into<f64> + Copy>(
            &mut self,
            bounds: impl RangeBounds<N> + Clone,
            row_factors: impl IntoIterator<Item = (Col, f64)>,
        ) {
            match &mut self.0 {
                State::Init { ip, lp, .. } => {
                    if let Some(lp) = lp {
                        let row_factors: Vec<_> = row_factors.into_iter().collect();
                        ip.add_row(bounds.clone(), row_factors.iter().copied());
                        lp.add_row(bounds, row_factors);
                    } else {
                        ip.add_row(bounds, row_factors);
                    }
                }
                State::Main { ip, lp } => {
                    if let Some(lp) = lp {
                        let row_factors: Vec<_> = row_factors.into_iter().collect();
                        ip.add_row(bounds.clone(), row_factors.iter().copied());
                        lp.add_row(bounds, row_factors);
                    } else {
                        ip.add_row(bounds, row_factors);
                    }
                }
                State::Working => unreachable!("cannot add row in working state"),
            }
        }

        pub fn new_binary_col(&mut self, factor: f64) -> Col {
            match &mut self.0 {
                State::Init { ip, lp, .. } => {
                    let ip_col = ip.add_integer_column(factor, 0..=1);
                    if let Some(lp) = lp {
                        let lp_col = lp.add_column(factor, 0..=1);
                        debug_assert_eq!(ip_col, lp_col);
                    }
                    ip_col
                }
                State::Main { ip, lp } => {
                    let ip_col = ip.add_integer_column(factor, 0..=1, []);
                    if let Some(lp) = lp {
                        let lp_col = lp.add_col(factor, 0..=1, []);
                        debug_assert_eq!(ip_col, lp_col);
                    }
                    ip_col
                }
                State::Working => unreachable!("cannot add col in working state"),
            }
        }

        pub fn fix_value(&mut self, col: Col, val: bool) {
            match &mut self.0 {
                State::Init { ip, lp, .. } => {
                    if val {
                        ip.change_column_bounds(col, 1.0..=1.);
                    } else {
                        ip.change_column_bounds(col, 0.0..=0.);
                    }
                    if let Some(lp) = lp {
                        if val {
                            lp.change_column_bounds(col, 1.0..=1.);
                        } else {
                            lp.change_column_bounds(col, 0.0..=0.);
                        }
                    }
                }
                State::Main { ip, lp } => {
                    if val {
                        ip.change_column_bounds(col, 1.0..=1.);
                    } else {
                        ip.change_column_bounds(col, 0.0..=0.);
                    }
                    if let Some(lp) = lp {
                        if val {
                            lp.change_column_bounds(col, 1.0..=1.);
                        } else {
                            lp.change_column_bounds(col, 0.0..=0.);
                        }
                    }
                }
                State::Working => unreachable!("cannot learn unit in working state"),
            }
        }

        pub fn unfix_cols<I>(&mut self, cols: I)
        where
            I: IntoIterator<Item = Col>,
        {
            for col in cols {
                match &mut self.0 {
                    State::Init { ip, lp, .. } => {
                        ip.change_column_bounds(col, 0.0..=1.);
                        if let Some(lp) = lp {
                            lp.change_column_bounds(col, 0.0..=1.);
                        }
                    }
                    State::Main { ip, lp } => {
                        ip.change_column_bounds(col, 0.0..=1.);
                        if let Some(lp) = lp {
                            lp.change_column_bounds(col, 0.0..=1.);
                        }
                    }
                    State::Working => unreachable!("cannot learn unit in working state"),
                }
            }
        }

        pub fn get_models(&mut self) -> (highs::Model, Option<highs::Model>) {
            match std::mem::take(&mut self.0) {
                State::Init { ip, lp, options } => {
                    // transition to main
                    let mut ip = ip.optimise(Sense::Minimise);
                    ip.set_option("threads", options.threads);
                    let tolerance = 1e-9;
                    ip.set_option("mip_feasibility_tolerance", tolerance);
                    ip.set_option("primal_feasibility_tolerance", tolerance);
                    ip.set_option("dual_feasibility_tolerance", tolerance);
                    ip.set_option("primal_residual_tolerance", tolerance);
                    ip.set_option("dual_residual_tolerance", tolerance);
                    let lp = lp.map(|lp| {
                        let mut lp = lp.optimise(Sense::Minimise);
                        lp.set_option("threads", options.threads);
                        lp
                    });
                    (ip, lp)
                }
                State::Main { ip, lp } => (ip, lp),
                State::Working => unreachable!(),
            }
        }

        pub fn put_models(&mut self, ip: highs::Model, lp: Option<highs::Model>) {
            self.0 = State::Main { ip, lp };
        }
    }
}
