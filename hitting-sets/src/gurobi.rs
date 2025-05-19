//! # Hitting Set Solver Interface for the Gurobi Solver

use grb::{add_binvar, attr, c, expr::Expr, param, Env, Model, Status};
use rustsat::types::{Cl, Lit, RsHashMap, Var};

use crate::{CompleteSolveResult, IncompleteSolveResult};

use super::{BuildSolver, HittingSetSolver, VarMap};

pub struct Solver {
    objectives: Vec<RsHashMap<Lit, usize>>,
    map: VarMap<grb::Var>,
    model: Model,
    statistics: super::Statistics,
}

impl HittingSetSolver for Solver {
    type Builder = Builder;

    fn change_multipliers(&mut self, multi: &[f64]) {
        for (var, gv) in self.map.iter() {
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
            self.model
                .set_obj_attr(attr::Obj, gv, weight)
                .expect("failed to set objective coefficient");
        }
    }

    fn add_core(&mut self, core: &Cl) {
        self.statistics.n_cores += 1;
        let mut bound = 1.;
        let mut expr = Expr::Constant(0.);
        for lit in core {
            if lit.is_pos() {
                expr = expr + self.map[lit.var()];
            } else {
                bound -= 1.;
                expr = expr - self.map[lit.var()];
            }
        }
        self.model
            .add_constr("core", c!(expr >= bound))
            .expect("failed adding core to Gurobi");
    }

    fn optimal_hitting_set(&mut self) -> CompleteSolveResult {
        self.solve(None).into()
    }

    fn hitting_set(&mut self, target_value: usize) -> IncompleteSolveResult {
        self.solve(Some(target_value)).into()
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
            0 => {
                self.model
                    .add_constr("infeasible", c!(1 <= 0))
                    .expect("failed to add infeasible constraint");
            }
            1 => {
                let mut bound = (costs[non_zeroes[0]] - 1) as f64;
                let mut expr = Expr::Constant(0.);
                for (&lit, &cost) in self.objectives[non_zeroes[0]].iter() {
                    if lit.is_pos() {
                        expr = expr + Expr::Term(cost as f64, self.map[lit.var()]);
                    } else {
                        bound -= cost as f64;
                        expr = expr - Expr::Term(cost as f64, self.map[lit.var()]);
                    }
                }
                self.model
                    .add_constr("objective bound", c!(expr <= bound))
                    .expect("failed to add objective bound constraint");
            }
            2 => {
                // special case, using only one aux var and two constraints
                let model = &mut self.model;
                let aux =
                    add_binvar!(model, name: "pd-cut-aux").expect("failed to create variable");

                // constraint for first objective
                let mut bound = (costs[non_zeroes[0]] - 1) as f64;
                let mut expr = Expr::Constant(0.);
                for (&lit, &cost) in self.objectives[non_zeroes[0]].iter() {
                    if lit.is_pos() {
                        expr = expr + Expr::Term(cost as f64, self.map[lit.var()]);
                    } else {
                        bound -= cost as f64;
                        expr = expr - Expr::Term(cost as f64, self.map[lit.var()]);
                    }
                }
                self.model
                    .add_genconstr_indicator("pd-cut-indicator-0", aux, true, c!(expr <= bound))
                    .expect("failed to add PD cut indicator");

                // constraint for second objective
                let mut bound = (costs[non_zeroes[1]] - 1) as f64;
                let mut expr = Expr::Constant(0.);
                for (&lit, &cost) in self.objectives[non_zeroes[1]].iter() {
                    if lit.is_pos() {
                        expr = expr + Expr::Term(cost as f64, self.map[lit.var()]);
                    } else {
                        bound -= cost as f64;
                        expr = expr - Expr::Term(cost as f64, self.map[lit.var()]);
                    }
                }
                self.model
                    .add_genconstr_indicator("pd-cut-indicator-1", aux, false, c!(expr <= bound))
                    .expect("failed to add PD cut indicator");
            }
            p => {
                let model = &mut self.model;
                let auxs: Vec<_> = (0..p)
                    .map(|idx| {
                        add_binvar!(model, name: &format!("pd-cut-aux-{idx}"))
                            .expect("failed to create variable")
                    })
                    .collect();
                // indicator constraints for each objective
                for (nz_idx, (obj_idx, &aux)) in non_zeroes.into_iter().zip(&auxs).enumerate() {
                    let mut bound = (costs[obj_idx] - 1) as f64;
                    let mut expr = Expr::Constant(0.);
                    for (&lit, &cost) in self.objectives[obj_idx].iter() {
                        if lit.is_pos() {
                            expr = expr + Expr::Term(cost as f64, self.map[lit.var()]);
                        } else {
                            bound -= cost as f64;
                            expr = expr - Expr::Term(cost as f64, self.map[lit.var()]);
                        }
                    }
                    self.model
                        .add_genconstr_indicator(
                            &format!("pd-cut-indicator-{nz_idx}"),
                            aux,
                            true,
                            c!(expr <= bound),
                        )
                        .expect("failed to add PD cut indicator");
                }
                // clause over the indicators
                let mut expr = Expr::Constant(0.);
                for aux in auxs {
                    expr = expr + aux;
                }
                self.model
                    .add_constr("pd-cut", c!(expr >= 1))
                    .expect("failed to add PD cut");
            }
        }
    }

    fn statistics(&self) -> super::Statistics {
        self.statistics
    }
}

impl Solver {
    fn solve(&mut self, target_value: Option<usize>) -> IncompleteSolveResult {
        self.statistics.n_solves += 1;
        let start = cpu_time::ProcessTime::now();
        self.set_target(target_value);
        self.model
            .optimize()
            .expect("failed to optimize with Gurobi");
        let status = self.model.status().expect("failed to get model status");
        if status == Status::Infeasible {
            self.statistics.solve_time += start.elapsed();
            return IncompleteSolveResult::Infeasible;
        }
        if status == Status::UserObjLimit {
            debug_assert!(target_value.is_some());
            let (cost, hitting_set) = self.get_solution();
            self.statistics.solve_time += start.elapsed();
            return IncompleteSolveResult::Feasible(cost, hitting_set);
        };
        debug_assert_eq!(status, Status::Optimal);
        let (cost, hitting_set) = self.get_solution();
        self.statistics.solve_time += start.elapsed();
        IncompleteSolveResult::Optimal(cost, hitting_set)
    }

    fn set_target(&mut self, target_value: Option<usize>) {
        let env = self.model.get_env_mut();
        if let Some(target_value) = target_value {
            env.set(param::BestObjStop, target_value as f64)
        } else {
            env.set(param::BestObjStop, -f64::INFINITY)
        }
        .expect("failed to set target value");
    }

    fn get_solution(&self) -> (f64, Vec<Lit>) {
        let cost = self
            .model
            .get_attr(attr::ObjVal)
            .expect("failed to get objective value");
        let hitting_set: Vec<_> = self
            .map
            .iter()
            .map(|(rv, gv)| {
                let val = self
                    .model
                    .get_obj_attr(attr::X, gv)
                    .expect("failed to get variable value");
                if val >= super::TRUE {
                    rv.pos_lit()
                } else if val <= super::FALSE {
                    rv.neg_lit()
                } else {
                    panic!("variable assigned to non-interger value");
                }
            })
            .collect();
        (cost, hitting_set)
    }
}

pub struct Builder {
    objectives: Vec<RsHashMap<Lit, usize>>,
    env: Env,
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
        Builder {
            objectives,
            env: env.start().expect("failed to start Gurobi environment"),
        }
    }

    fn init(self) -> Self::Solver {
        let Builder { objectives, env } = self;
        let mut model =
            Model::with_env("hitting-sets", &env).expect("failed to initialize Gurobi model");
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
            map.ensure_mapped(var, |v| {
                add_binvar!(model, name: &format!("{v}"), obj: weight)
                    .expect("failed to create Gurobi variable")
            });
        }
        Solver {
            objectives,
            map,
            model,
            statistics: super::Statistics::default(),
        }
    }

    fn threads(&mut self, threads: u32) -> &mut Self {
        self.env
            .set(
                param::Threads,
                i32::try_from(threads).expect("`threads` must be at most `i32::MAX`"),
            )
            .expect("failed to set parameter `Threads` for Gurobi");
        self
    }
}

impl super::IndexedVar for grb::Var {
    fn index(&self) -> usize {
        use grb::ModelObject;
        usize::try_from(self.id()).expect("invalid Gurobi variable index")
    }
}
