//! # Hitting Set Solver Interface for the Gurobi Solver

use std::cmp;

use grb::{Env, Status, c, expr::Expr, param};
use rustsat::types::{Lit, RsHashMap, TernaryVal, Var};

use crate::{
    Callbacks, CompleteSolveResult, IncompleteSolveResult,
    MaybeTerminated::{self, Done},
    ReducedCostsResult,
    map::IndexedVar,
};

use super::{BuildSolver, CoreOrigin, HittingSetSolver, Obj, VarMap};

pub struct Solver {
    objectives: Vec<Obj>,
    map: VarMap<grb::Var>,
    units: Vec<TernaryVal>,
    model: model::Model,
    statistics: super::Statistics,
    use_start: bool,
}

impl HittingSetSolver for Solver {
    type Builder = Builder;

    fn change_multipliers(&mut self, multi: &[f64]) {
        for (var, gv) in self.map.iter() {
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
            self.model.set_obj_coeff(*gv, weight);
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
        let mut bound = bound as f64;
        let mut expr = Expr::Constant(0.);
        for lit in lits {
            if lit.is_pos() {
                expr = expr + self.map[lit.var()];
            } else {
                bound -= 1.;
                expr = expr - self.map[lit.var()];
            }
        }
        self.model.add_constr("core", c!(expr >= bound));
    }

    fn add_card(&mut self, lits: &[Lit], bound: usize) {
        let mut bound = bound as f64;
        let mut expr = Expr::Constant(0.);
        let model = &mut self.model;
        for lit in lits {
            if lit.is_pos() {
                expr = expr
                    + self
                        .map
                        .ensure_mapped(lit.var(), |v| model.add_var(&format!("{v}"), 0.));
            } else {
                bound -= 1.;
                expr = expr
                    - self
                        .map
                        .ensure_mapped(lit.var(), |v| model.add_var(&format!("{v}"), 0.));
            }
        }
        self.model.add_constr("card", c!(expr >= bound));
    }

    fn add_card_eq(&mut self, lits: &[Lit], value: usize) {
        let mut value = value as f64;
        let mut expr = Expr::Constant(0.);
        let model = &mut self.model;
        for lit in lits {
            if lit.is_pos() {
                expr = expr
                    + self
                        .map
                        .ensure_mapped(lit.var(), |v| model.add_var(&format!("{v}"), 0.));
            } else {
                value -= 1.;
                expr = expr
                    - self
                        .map
                        .ensure_mapped(lit.var(), |v| model.add_var(&format!("{v}"), 0.));
            }
        }
        self.model.add_constr("card_eq", c!(expr == value));
    }

    fn add_reified_card(&mut self, lits: &[Lit], bound: usize, reif: Lit, equivalence: bool) {
        let model = &mut self.model;
        let ind = self
            .map
            .ensure_mapped(reif.var(), |v| model.add_var(&format!("{v}"), 0.));
        let mut expr = Expr::Constant(0.);
        let mut bound = bound as f64;
        for lit in lits {
            if lit.is_pos() {
                expr = expr
                    + self
                        .map
                        .ensure_mapped(lit.var(), |v| model.add_var(&format!("{v}"), 0.));
            } else {
                bound -= 1.;
                expr = expr
                    - self
                        .map
                        .ensure_mapped(lit.var(), |v| model.add_var(&format!("{v}"), 0.));
            }
        }
        if equivalence {
            self.model.add_indicator_constr(
                &format!("{reif}-reification-only-if"),
                ind,
                reif.is_pos(),
                c!(expr.clone() >= bound),
            );
        }
        self.model.add_indicator_constr(
            &format!("{reif}-reification-if"),
            ind,
            reif.is_neg(),
            c!(expr <= bound - 1.),
        );
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
        self.solve(start, true, cb).map(CompleteSolveResult::from)
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
        self.solve(start, false, cb)
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
            0 => {
                self.model.add_constr("infeasible", c!(1 <= 0));
            }
            1 => {
                let mut bound =
                    (costs[non_zeroes[0]] - self.objectives[non_zeroes[0]].offset - 1) as f64;
                let mut expr = Expr::Constant(0.);
                for (&lit, &cost) in self.objectives[non_zeroes[0]].lits.iter() {
                    if lit.is_pos() {
                        expr = expr + Expr::Term(cost as f64, self.map[lit.var()]);
                    } else {
                        bound -= cost as f64;
                        expr = expr - Expr::Term(cost as f64, self.map[lit.var()]);
                    }
                }
                self.model.add_constr("objective bound", c!(expr <= bound));
            }
            2 => {
                // special case, using only one aux var and two constraints
                let aux = self.model.add_var("pd-cut-aux", 0.);

                // constraint for first objective
                let mut bound =
                    (costs[non_zeroes[0]] - self.objectives[non_zeroes[0]].offset - 1) as f64;
                let mut expr = Expr::Constant(0.);
                for (&lit, &cost) in self.objectives[non_zeroes[0]].lits.iter() {
                    if lit.is_pos() {
                        expr = expr + Expr::Term(cost as f64, self.map[lit.var()]);
                    } else {
                        bound -= cost as f64;
                        expr = expr - Expr::Term(cost as f64, self.map[lit.var()]);
                    }
                }
                self.model
                    .add_indicator_constr("pd-cut-indicator-0", aux, true, c!(expr <= bound));

                // constraint for second objective
                let mut bound =
                    (costs[non_zeroes[1]] - self.objectives[non_zeroes[1]].offset - 1) as f64;
                let mut expr = Expr::Constant(0.);
                for (&lit, &cost) in self.objectives[non_zeroes[1]].lits.iter() {
                    if lit.is_pos() {
                        expr = expr + Expr::Term(cost as f64, self.map[lit.var()]);
                    } else {
                        bound -= cost as f64;
                        expr = expr - Expr::Term(cost as f64, self.map[lit.var()]);
                    }
                }
                self.model.add_indicator_constr(
                    "pd-cut-indicator-1",
                    aux,
                    false,
                    c!(expr <= bound),
                );
            }
            p => {
                let auxs: Vec<_> = (0..p)
                    .map(|idx| self.model.add_var(&format!("pd-cut-aux-{idx}"), 0.))
                    .collect();
                // indicator constraints for each objective
                for (nz_idx, (obj_idx, &aux)) in non_zeroes.into_iter().zip(&auxs).enumerate() {
                    let mut bound = (costs[obj_idx] - self.objectives[obj_idx].offset - 1) as f64;
                    let mut expr = Expr::Constant(0.);
                    for (&lit, &cost) in self.objectives[obj_idx].lits.iter() {
                        if lit.is_pos() {
                            expr = expr + Expr::Term(cost as f64, self.map[lit.var()]);
                        } else {
                            bound -= cost as f64;
                            expr = expr - Expr::Term(cost as f64, self.map[lit.var()]);
                        }
                    }
                    self.model.add_indicator_constr(
                        &format!("pd-cut-indicator-{nz_idx}"),
                        aux,
                        true,
                        c!(expr <= bound),
                    );
                }
                // clause over the indicators
                let mut expr = Expr::Constant(0.);
                for aux in auxs {
                    expr = expr + aux;
                }
                self.model.add_constr("pd-cut", c!(expr >= 1));
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
            let gv = self
                .map
                .ensure_mapped(var, |v| self.model.add_var(&format!("{v}"), weight));
            self.model.set_obj_coeff(gv, weight);
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
        let var = self.map[unit.var()];
        if self.units.len() <= var.index() {
            self.units.resize(var.index() + 1, TernaryVal::DontCare);
        }
        self.units[var.index()] = TernaryVal::from(unit.is_pos());
        self.model.fix_var(var, unit.is_pos());
    }

    fn reduced_costs_callback<Cb>(&mut self, cb: &mut Cb) -> MaybeTerminated<ReducedCostsResult>
    where
        Cb: Callbacks,
    {
        self.statistics.n_lp_solves += 1;
        let start_time = cpu_time::ProcessTime::now();

        let status = self.model.optimize_lp(&mut GurobiCallbacks(cb));
        if status == Status::Interrupted {
            self.statistics.lp_solve_time += start_time.elapsed();
            return MaybeTerminated::Terminated;
        }
        if status == Status::Infeasible {
            self.statistics.lp_solve_time += start_time.elapsed();
            return Done(ReducedCostsResult::Infeasible);
        }
        debug_assert_eq!(status, Status::Optimal);
        let lp_vals = self.model.lp_vals(self.map.iter().map(|(_, &gv)| gv));
        let rcs = self.model.reduced_costs(self.map.iter().map(|(_, &gv)| gv));
        self.statistics.lp_solve_time += start_time.elapsed();
        Done(ReducedCostsResult::ReducedCosts {
            obj_val: self.model.lp_obj_val(),
            rcs: self
                .map
                .iter()
                .zip(lp_vals)
                .zip(rcs)
                .filter_map(|(((rv, _), val), rc)| {
                    if val >= crate::TRUE {
                        Some((rv, true, rc))
                    } else if val <= crate::FALSE {
                        Some((rv, false, rc))
                    } else {
                        None
                    }
                })
                .collect(),
        })
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
            self.model.fix_var(var, lit.is_pos());
        }
        true
    }

    fn unfix_all(&mut self) {
        self.model
            .unfix_vars(self.map.iter().filter_map(|(_, &gv)| {
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

impl Solver {
    fn solve<I, Cb>(
        &mut self,
        start: I,
        optimal: bool,
        cb: &mut Cb,
    ) -> MaybeTerminated<IncompleteSolveResult>
    where
        I: IntoIterator<Item = Lit>,
        Cb: Callbacks,
    {
        self.statistics.n_solves += 1;
        let start_time = cpu_time::ProcessTime::now();

        // handle starting point
        let mut target = 0.;
        self.model.update();
        for l in start {
            if let Some(&col) = self.map.map(l.var()) {
                if !optimal && l.is_pos() {
                    target += self.model.get_obj_coeff(col);
                };
                if self.use_start {
                    self.model.set_ip_start(col, l.is_pos());
                }
            }
        }
        let env = self.model.env();
        if optimal {
            env.set(param::BestObjStop, -f64::INFINITY)
        } else {
            env.set(param::BestObjStop, target)
        }
        .expect("failed to set target value");

        let status = self.model.optimize_ip(&mut GurobiCallbacks(cb));
        if status == Status::Interrupted {
            self.statistics.solve_time += start_time.elapsed();
            return MaybeTerminated::Terminated;
        }
        if status == Status::Infeasible {
            self.statistics.solve_time += start_time.elapsed();
            return Done(IncompleteSolveResult::Infeasible);
        }
        if status == Status::UserObjLimit {
            debug_assert!(!optimal);
            let (cost, hitting_set) = self.get_solution();
            self.statistics.solve_time += start_time.elapsed();
            return Done(IncompleteSolveResult::Feasible(cost, hitting_set));
        };
        debug_assert_eq!(status, Status::Optimal);
        let (cost, hitting_set) = self.get_solution();
        self.statistics.solve_time += start_time.elapsed();
        Done(IncompleteSolveResult::Optimal(cost, hitting_set))
    }

    fn get_solution(&self) -> (f64, Vec<Lit>) {
        let cost = self.model.ip_obj_val();
        let vals = self.model.ip_vals(self.map.iter().map(|(_, &gv)| gv));
        let hitting_set: Vec<_> = self
            .map
            .iter()
            .zip(vals)
            .map(|((rv, _), val)| rv.lit(!val))
            .collect();
        (cost, hitting_set)
    }
}

/// Gurobi callback wrapper around crate callbacks
struct GurobiCallbacks<'cb, Cb>(&'cb mut Cb);

impl<Cb> grb::callback::Callback for GurobiCallbacks<'_, Cb>
where
    Cb: Callbacks,
{
    fn callback(&mut self, w: grb::prelude::Where) -> grb::callback::CbResult {
        let terminate = self.0.check_termination();
        match w {
            grb::prelude::Where::Polling(polling_ctx) => {
                if terminate {
                    polling_ctx.terminate()
                }
            }
            grb::prelude::Where::PreSolve(pre_solve_ctx) => {
                if terminate {
                    pre_solve_ctx.terminate()
                }
            }
            grb::prelude::Where::Simplex(simplex_ctx) => {
                if terminate {
                    simplex_ctx.terminate()
                }
            }
            grb::prelude::Where::MIP(mipctx) => {
                if terminate {
                    mipctx.terminate()
                }
            }
            grb::prelude::Where::MIPSol(mipsol_ctx) => {
                if terminate {
                    mipsol_ctx.terminate()
                }
            }
            grb::prelude::Where::MIPNode(mipnode_ctx) => {
                if terminate {
                    mipnode_ctx.terminate()
                }
            }
            grb::prelude::Where::Message(message_ctx) => {
                if terminate {
                    message_ctx.terminate()
                }
            }
            grb::prelude::Where::Barrier(barrier_ctx) => {
                if terminate {
                    barrier_ctx.terminate()
                }
            }
            grb::prelude::Where::IIS(iisctx) => {
                if terminate {
                    iisctx.terminate()
                }
            }
            _ => (),
        }
        Ok(())
    }
}

pub struct Builder {
    objectives: Vec<RsHashMap<Lit, usize>>,
    env: Env,
    use_start: bool,
    might_need_lp: bool,
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
        let mut env = Env::empty().expect("failed to initialize Gurobi environment");
        env.set(param::LogFile, "".to_string())
            .expect("failed to silence Gurobi");
        env.set(param::LogToConsole, 0)
            .expect("failed to silence Gurobi");
        env.set(param::Threads, 1)
            .expect("failed to set parameter `Threads` for Gurobi");
        env.set(param::IntegralityFocus, 1)
            .expect("failed to set parameter `IntegralityFocus` for Gurobi");
        Builder {
            objectives,
            env: env.start().expect("failed to start Gurobi environment"),
            use_start: true,
            might_need_lp: false,
        }
    }

    fn init(self) -> Self::Solver {
        let Builder {
            objectives,
            env,
            use_start,
            might_need_lp,
        } = self;
        let mut model = model::Model::new(&env, might_need_lp);
        let mut vars: Vec<Var> = objectives
            .iter()
            .flat_map(|obj| obj.keys().copied().map(Lit::var))
            .collect();
        vars.sort_unstable();
        vars.dedup();
        let mut map = VarMap::new(vars.last().map_or(0, |var| var.idx() + 1), vars.len());
        for var in vars {
            let weight = objectives.iter().fold(0., |sum, obj| {
                if let Some(&weight) = obj.get(&var.pos_lit()) {
                    return sum + (weight as f64);
                }
                if let Some(&weight) = obj.get(&var.neg_lit()) {
                    return sum - (weight as f64);
                }
                sum
            });
            map.ensure_mapped(var, |v| model.add_var(&format!("{v}"), weight));
        }
        Solver {
            objectives: objectives
                .into_iter()
                .map(|lits| Obj {
                    lits,
                    ..Obj::default()
                })
                .collect(),
            map,
            units: vec![],
            model,
            statistics: super::Statistics::default(),
            use_start,
        }
    }

    fn threads(&mut self, threads: super::Threads) -> &mut Self {
        let threads = match threads {
            crate::Threads::Auto => 0,
            crate::Threads::N(non_zero) => i32::from(non_zero.get()),
        };
        self.env
            .set(param::Threads, threads)
            .expect("failed to set parameter `Threads` for Gurobi");
        self
    }

    fn use_starting_points(&mut self, use_start: bool) -> &mut Self {
        self.use_start = use_start;
        self
    }

    fn might_need_lp(&mut self, might_need: bool) -> &mut Self {
        self.might_need_lp = might_need;
        self
    }
}

impl IndexedVar for grb::Var {
    fn index(&self) -> usize {
        use grb::ModelObject;
        usize::try_from(self.id()).expect("invalid Gurobi variable index")
    }
}

mod model {
    use grb::{
        Expr, ModelObject, Var, add_binvar, add_ctsvar, attr, callback::Callback, constr::IneqExpr,
        expr::LinExpr,
    };

    /// Gurobi model with LP relaxation
    ///
    /// Encapsulated to help with keeping the models in sync
    pub struct Model {
        model: grb::Model,
        might_need_lp: bool,
        relax: Option<grb::Model>,
    }

    impl Model {
        pub fn new(env: &grb::Env, might_need_lp: bool) -> Self {
            Self {
                model: grb::Model::with_env("hitting-sets", env)
                    .expect("failed to initialize Gurobi model"),
                might_need_lp,
                relax: None,
            }
        }

        pub fn env(&mut self) -> &mut grb::Env {
            self.model.get_env_mut()
        }

        pub fn set_obj_coeff(&mut self, var: Var, coeff: f64) {
            self.model
                .set_obj_attr(attr::Obj, &var, coeff)
                .expect("failed to set objective coefficient");
            if let Some(relax) = &mut self.relax {
                relax
                    .set_obj_attr(attr::Obj, &Var::from_raw(var.id(), relax.id()), coeff)
                    .expect("failed to set objective coefficient (LP)");
            }
        }

        pub fn get_obj_coeff(&mut self, var: Var) -> f64 {
            self.model
                .get_obj_attr(attr::Obj, &var)
                .expect("failed to get objective coefficient")
        }

        pub fn set_ip_start(&mut self, var: Var, val: bool) {
            self.model
                .set_obj_attr(attr::Start, &var, if val { 1.0 } else { 0.0 })
                .expect("failed to set starting value");
        }

        pub fn add_var(&mut self, name: &str, obj: f64) -> Var {
            let model = &mut self.model;
            let ip_var =
                add_binvar!(model, name: name, obj: obj).expect("failed to create Gurobi variable");
            if let Some(relax) = &mut self.relax {
                let lp_var = add_ctsvar!(relax, name: name, obj: obj, bounds: 0..1_f64)
                    .expect("failed to create Gurobi variable (LP)");
                debug_assert_eq!(grb::Var::from_raw(ip_var.id(), relax.id()), lp_var);
            }
            ip_var
        }

        pub fn fix_var(&mut self, var: Var, val: bool) {
            if val {
                self.model
                    .set_obj_attr(attr::LB, &var, 1.)
                    .expect("failed to set variable bound");
                if let Some(relax) = &mut self.relax {
                    let lp_var = Var::from_raw(var.id(), relax.id());
                    relax
                        .set_obj_attr(attr::LB, &lp_var, 1.)
                        .expect("failed to set variable bound (LB)");
                }
            } else {
                self.model
                    .set_obj_attr(attr::UB, &var, 0.)
                    .expect("failed to set variable bound");
                if let Some(relax) = &mut self.relax {
                    let lp_var = Var::from_raw(var.id(), relax.id());
                    relax
                        .set_obj_attr(attr::UB, &lp_var, 0.)
                        .expect("failed to set variable bound (LB)");
                }
            }
        }

        pub fn unfix_vars<I>(&mut self, vars: I)
        where
            I: IntoIterator<Item = Var>,
        {
            let vars: Vec<_> = vars.into_iter().collect();
            self.model.update().expect("failed to update model");
            self.model
                .set_obj_attr_batch(attr::UB, vars.iter().map(|&v| (v, 1.)))
                .expect("failed to set variable bounds");
            self.model
                .set_obj_attr_batch(attr::LB, vars.iter().map(|&v| (v, 0.)))
                .expect("failed to set variable bounds");
            if let Some(relax) = &mut self.relax {
                relax.update().expect("failed to update model (lp)");
                relax
                    .set_obj_attr_batch(
                        attr::UB,
                        vars.iter().map(|&v| {
                            let lp_var = Var::from_raw(v.id(), relax.id());
                            (lp_var, 1.)
                        }),
                    )
                    .expect("failed to set variable bounds (LB)");
                relax
                    .set_obj_attr_batch(
                        attr::LB,
                        vars.iter().map(|&v| {
                            let lp_var = Var::from_raw(v.id(), relax.id());
                            (lp_var, 0.)
                        }),
                    )
                    .expect("failed to set variable bounds (LB)");
            }
        }

        pub fn add_constr(&mut self, name: &str, con: IneqExpr) {
            if let Some(relax) = &mut self.relax {
                let IneqExpr {
                    lhs,
                    sense,
                    rhs: Expr::Constant(rhs),
                } = &con
                else {
                    panic!("unexpected type of constraint");
                };
                let con = match lhs {
                    Expr::Constant(lhs) => IneqExpr {
                        lhs: Expr::Constant(*lhs),
                        sense: *sense,
                        rhs: Expr::Constant(*rhs),
                    },
                    Expr::Linear(lhs) => IneqExpr {
                        lhs: {
                            let new_expr: LinExpr = lhs
                                .iter_terms()
                                .map(|(&var, &coeff)| (coeff, Var::from_raw(var.id(), relax.id())))
                                .collect();
                            new_expr + lhs.get_offset()
                        },
                        sense: *sense,
                        rhs: Expr::Constant(*rhs),
                    },
                    _ => panic!("unexpected type of constraint"),
                };
                relax
                    .add_constr(name, con)
                    .expect("failed to add constraint to Gurobi (LP)");
            }
            self.model
                .add_constr(name, con)
                .expect("failed to add constraint to Gurobi");
        }

        pub fn add_indicator_constr(&mut self, name: &str, ind: Var, ind_val: bool, con: IneqExpr) {
            if self.might_need_lp {
                let relax = self.relax.get_or_insert_with(|| {
                    self.model.update().expect("failed to update model");
                    let relax = self
                        .model
                        .try_clone()
                        .expect("failed to clone model for LP");
                    let vars = relax
                        .get_vars()
                        .expect("failed to get variables of LP model");
                    relax
                        .set_obj_attr_batch(
                            attr::VType,
                            vars.iter().map(|&v| (v, grb::VarType::Continuous)),
                        )
                        .expect("failed to relax variable integrality");
                    relax
                });
                // Can't get reduced costs with indicator constraints, so need to model them as
                // big-M here
                let ind = Var::from_raw(ind.id(), relax.id());
                let IneqExpr {
                    lhs: Expr::Linear(lhs),
                    sense,
                    rhs: Expr::Constant(rhs),
                } = &con
                else {
                    panic!("unexpected type of constraint");
                };
                let rhs = *rhs;
                let rhs =
                    match sense {
                        grb::ConstrSense::Equal => panic!("equality constraints not supported"),
                        grb::ConstrSense::Greater => {
                            let min_lhs = lhs.iter_terms().fold(0., |min, (_, &coeff)| {
                                if coeff < 0. { min + coeff } else { min }
                            });
                            let big_m = rhs - min_lhs;
                            if ind_val {
                                rhs - big_m + (big_m * ind)
                            } else {
                                rhs - (big_m * ind)
                            }
                        }
                        grb::ConstrSense::Less => {
                            let max_lhs = lhs.iter_terms().fold(0., |max, (_, &coeff)| {
                                if coeff > 0. { max + coeff } else { max }
                            });
                            let big_m = max_lhs - rhs;
                            if ind_val {
                                rhs + big_m - (big_m * ind)
                            } else {
                                rhs + (big_m * ind)
                            }
                        }
                    };
                let con = IneqExpr {
                    lhs: {
                        let new_expr: LinExpr = lhs
                            .iter_terms()
                            .map(|(&var, &coeff)| (coeff, Var::from_raw(var.id(), relax.id())))
                            .collect();
                        new_expr + lhs.get_offset()
                    },
                    sense: *sense,
                    rhs,
                };
                relax
                    .add_constr(name, con)
                    .expect("failed to add indicator constraint to Gurobi (LP)");
            }
            self.model
                .add_genconstr_indicator(name, ind, ind_val, con)
                .expect("failed to add indicator constraint to Gurobi");
        }

        pub fn update(&mut self) {
            self.model.update().expect("failed to update model");
            if let Some(relax) = &mut self.relax {
                relax.update().expect("failed to update model (LP)");
            }
        }

        pub fn optimize_ip<Cb>(&mut self, callback: &mut Cb) -> grb::Status
        where
            Cb: Callback,
        {
            self.model
                .optimize_with_callback(callback)
                .expect("failed to optimize with Gurobi");
            self.model.status().expect("failed to get model status")
        }

        pub fn ip_obj_val(&self) -> f64 {
            self.model
                .get_attr(attr::ObjVal)
                .expect("failed to get objective value")
        }

        pub fn ip_vals<I>(&self, vars: I) -> impl Iterator<Item = bool>
        where
            I: IntoIterator<Item = Var>,
        {
            self.model
                .get_obj_attr_batch(attr::X, vars)
                .expect("failed to get variable values")
                .into_iter()
                .map(|val| {
                    if val >= crate::TRUE {
                        true
                    } else if val <= crate::FALSE {
                        false
                    } else {
                        panic!("variable assigned to non-interger value");
                    }
                })
        }

        pub fn optimize_lp<Cb>(&mut self, callback: &mut Cb) -> grb::Status
        where
            Cb: Callback,
        {
            let relax = self.relax.get_or_insert_with(|| {
                debug_assert!(self.might_need_lp);
                self.model.update().expect("failed to update model");
                let relax = self
                    .model
                    .try_clone()
                    .expect("failed to clone model for LP");
                let vars = relax
                    .get_vars()
                    .expect("failed to get variables of LP model");
                relax
                    .set_obj_attr_batch(
                        attr::VType,
                        vars.iter().map(|&v| (v, grb::VarType::Continuous)),
                    )
                    .expect("failed to relax variable integrality");
                relax
            });
            relax
                .optimize_with_callback(callback)
                .expect("failed to optimize with Gurobi (LP)");
            relax.status().expect("failed to get model status (LP)")
        }

        pub fn lp_obj_val(&self) -> f64 {
            let Some(relax) = &self.relax else {
                panic!("need to have an LP for getting LP objective value");
            };
            relax
                .get_attr(attr::ObjVal)
                .expect("failed to get objective value (LP)")
        }

        pub fn lp_vals<I>(&self, vars: I) -> Vec<f64>
        where
            I: IntoIterator<Item = Var>,
        {
            let Some(relax) = &self.relax else {
                panic!("need to have an LP for LP values");
            };
            relax
                .get_obj_attr_batch(
                    attr::X,
                    vars.into_iter().map(|v| Var::from_raw(v.id(), relax.id())),
                )
                .expect("failed to get variable values")
        }

        pub fn reduced_costs<I>(&self, vars: I) -> Vec<f64>
        where
            I: IntoIterator<Item = Var>,
        {
            let Some(relax) = &self.relax else {
                panic!("need to have an LP for getting reduced costs");
            };
            relax
                .get_obj_attr_batch(
                    attr::RC,
                    vars.into_iter().map(|v| Var::from_raw(v.id(), relax.id())),
                )
                .expect("failed to get reduced costs")
        }
    }
}
