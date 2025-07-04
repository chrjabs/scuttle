//! # Multi-Objective IHS Algorithm

use std::io;

use hitting_sets::{
    BuildSolver, CompleteSolveResult, CoreOrigin, HittingSetSolver, IncompleteSolveResult,
};
use rustsat::{
    encodings::{
        nodedb::{NodeById, NodeId, NodeLike},
        totdb::{Db as TotDb, Semantics},
    },
    instances::ManageVars,
    solvers::{
        DefaultInitializer, Initialize, Learn, SolveIncremental, SolveStats, SolverResult,
        SolverStats,
    },
    types::{Assignment, Cl, Clause, Lit, RsHashMap, RsHashSet, TernaryVal, Var},
};
use scuttle_proc::{oracle_bounds, KernelFunctions};

use crate::{
    algs::{coreboosting::CbResult, coreguided::ReformData},
    archive::Archive,
    options::{CandidateSeeding, EnumOptions, IhsCbOptions, IhsCbTreatment, IhsOptions},
    termination::ensure,
    types::{Objective, ParetoFront, VarManager},
    CoreBoost, EncodingStats, ExtendedSolveStats, KernelOptions, Limits,
    MaybeTerminatedError::{self, Done},
};

use super::Kernel;

#[derive(KernelFunctions)]
pub struct ParetoIhs<O, Hss, OInit = DefaultInitializer, BCG = fn(Assignment) -> Clause> {
    kernel: Kernel<O, io::BufWriter<std::fs::File>, OInit, BCG>,
    hitting_set_solver: Hss,
    objective_lits: RsHashSet<Lit>,
    max_obj_var: Var,
    n_seeded: usize,
    cb_data: CbData,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
    /// Archive of candidate solutions
    candidates: Archive<Assignment>,
    opts: IhsOptions,
}

impl<'slv, Hss, OInit, BCG> super::Solve
    for ParetoIhs<rustsat_cadical::CaDiCaL<'_, 'slv>, Hss, OInit, BCG>
where
    Hss: HittingSetSolver + 'slv,
    BCG: Fn(Assignment) -> Clause,
{
    fn solve(&mut self, limits: Limits) -> MaybeTerminatedError {
        self.kernel.start_solving(limits);
        self.alg_main()
    }

    fn all_stats(
        &self,
    ) -> (
        crate::Stats,
        Option<SolverStats>,
        Option<Vec<EncodingStats>>,
        Option<hitting_sets::Statistics>,
    ) {
        use crate::ExtendedSolveStats;
        (
            self.kernel.stats,
            Some(self.oracle_stats()),
            Some(self.encoding_stats()),
            Some(self.hitting_set_solver.statistics()),
        )
    }
}

#[oracle_bounds]
impl<O, Hss, OInit, BCG> super::Init for ParetoIhs<O, Hss, OInit, BCG>
where
    O: SolveIncremental,
    Hss: HittingSetSolver,
    OInit: Initialize<O>,
    BCG: Fn(Assignment) -> Clause,
{
    type Oracle = O;
    type BlockClauseGen = BCG;
    type Options = (KernelOptions, IhsOptions);

    /// Initializes a default solver with a configured oracle and options. The
    /// oracle should _not_ have any clauses loaded yet.
    fn new<Cls>(
        clauses: Cls,
        objs: Vec<Objective>,
        var_manager: VarManager,
        (kernel_opts, opts): Self::Options,
        block_clause_gen: BCG,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = Clause>,
    {
        anyhow::ensure!(
            matches!(kernel_opts.enumeration, EnumOptions::NoEnum),
            "cannot enumerate with IHS algorithm"
        );
        let mut builder = Hss::Builder::new(objs.iter().map(|obj| obj.iter()));
        builder.threads(opts.hss_threads);
        builder.use_starting_points(opts.starting_points);
        let mut hitting_set_solver = builder.init();
        let clauses: Vec<_> = clauses.into_iter().collect();

        // Seed constraints over objective variables
        let mut objective_lits = RsHashSet::default();
        let mut max_obj_var = Var::new(0);
        for obj in &objs {
            for (lit, _) in obj.iter() {
                if lit.var() > max_obj_var {
                    max_obj_var = lit.var();
                }
                objective_lits.insert(lit);
            }
        }
        let mut n_seeded = 0;
        if opts.seeding {
            'outer: for cl in &clauses {
                for lit in cl {
                    if !objective_lits.contains(lit) && !objective_lits.contains(&!*lit) {
                        continue 'outer;
                    }
                }
                hitting_set_solver.add_core(cl, CoreOrigin::Seeding);
                n_seeded += 1;
            }
        }

        let kernel = Kernel::new(clauses, objs, var_manager, block_clause_gen, kernel_opts)?;
        Ok(Self {
            kernel,
            hitting_set_solver,
            objective_lits,
            max_obj_var,
            n_seeded,
            cb_data: CbData::None,
            pareto_front: Default::default(),
            candidates: Default::default(),
            opts,
        })
    }
}

impl<O, Hss, OInit, BCG> ExtendedSolveStats for ParetoIhs<O, Hss, OInit, BCG>
where
    O: SolveStats,
{
    fn oracle_stats(&self) -> SolverStats {
        self.kernel.oracle.stats()
    }

    fn encoding_stats(&self) -> Vec<EncodingStats> {
        vec![]
    }
}

impl<'slv, Hss, OInit, BCG> ParetoIhs<rustsat_cadical::CaDiCaL<'_, 'slv>, Hss, OInit, BCG>
where
    Hss: HittingSetSolver + 'slv,
    BCG: Fn(Assignment) -> Clause,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> MaybeTerminatedError {
        self.kernel.log_routine_start("ihs")?;
        if let Some(logger) = &mut self.kernel.logger {
            logger.log_seeding_ratio(
                self.n_seeded as f64 / self.kernel.stats.n_orig_clauses as f64,
            )?;
        }
        if !matches!(
            self.cb_data,
            CbData::Ignore | CbData::TranslateReform { .. }
        ) && (self.n_seeded as f64 / self.kernel.stats.n_orig_clauses as f64 - 1.0).abs()
            < f64::EPSILON
        {
            let term = self.main_fully_seeded();
            self.kernel.log_routine_end()?;
            return term;
        }
        if self.seed_candidates()? {
            return Done(());
        }
        let mut want_optimal = false;
        let joint_objective = {
            let mut jobj = vec![0; self.max_obj_var.idx() + 1];
            for obj in self.hitting_set_solver.objectives() {
                for (lit, weight) in obj {
                    let mut weight =
                        isize::try_from(weight).expect("weight does not fit in `isize`");
                    if lit.is_neg() {
                        weight *= -1;
                    }
                    jobj[lit.vidx()] += weight;
                }
            }
            jobj
        };
        loop {
            self.kernel.log_routine_start("extract hitting set")?;

            let hitting_set_answer: IncompleteSolveResult =
                if let Some(head) = self.candidates.head() {
                    if want_optimal {
                        self.hitting_set_solver
                            .optimal_hitting_set(head.sol())
                            .into()
                    } else {
                        self.hitting_set_solver.hitting_set(head.sol())
                    }
                } else {
                    self.hitting_set_solver.optimal_hitting_set(None).into()
                };

            let (cost, hitting_set, is_optimal) = match hitting_set_answer {
                IncompleteSolveResult::Optimal(cost, hitting_set) => (cost, hitting_set, true),
                IncompleteSolveResult::Infeasible => {
                    self.kernel.log_routine_end()?;
                    self.kernel.log_routine_end()?;
                    return Done(());
                }
                IncompleteSolveResult::Feasible(cost, hitting_set) => (cost, hitting_set, false),
            };

            self.kernel.log_routine_end()?;
            if let Some(logger) = &mut self.kernel.logger {
                logger.log_hitting_set(cost, is_optimal)?;
            }

            let mut assumps = hitting_set.clone();

            self.kernel.check_termination()?;
            assumps.retain(|lit| self.objective_lits.contains(&!*lit));
            // sort hitting set by weight for core minimization
            if self.opts.core_minimization.minimization() {
                // NOTE: we _intentionally_ use stable sort here, so that we preserve literal order
                // on equal weight
                assumps.sort_by_key(|l| -joint_objective[l.vidx()].abs());
            }
            if let CbData::TranslateReform { dbs, olit_map, .. } = &mut self.cb_data {
                for &a in &assumps {
                    if let Some((obj_idx, id, oidx)) = olit_map[a.vidx()] {
                        let lit = dbs[obj_idx].define_unweighted(
                            id,
                            oidx,
                            Semantics::If,
                            &mut self.kernel.oracle,
                            &mut self.kernel.var_manager,
                        )?;
                        debug_assert_eq!(a, !lit);
                    }
                }
            };
            match self.oracle_with_unit_learner(&assumps)? {
                SolverResult::Sat => {
                    let (costs, solution) = self.kernel.get_solution_and_internal_costs(false)?;
                    if is_optimal {
                        // found pareto-optimal solution
                        self.candidates.remove_dominated(&costs);
                        // store solution
                        self.kernel.yield_solutions(
                            costs.clone(),
                            &[],
                            solution,
                            &mut self.pareto_front,
                        )?;
                        // introduce PD cut in the hitting set solver
                        self.hitting_set_solver.add_pd_cut(&costs);
                        want_optimal = false;
                    } else {
                        let old_head_cost = self
                            .candidates
                            .head()
                            .expect("since the hitting set is not optimal, we must have a target")
                            .costs()
                            .iter()
                            .sum();
                        let new_target = costs.iter().copied().sum::<usize>();
                        self.candidates.insert(solution, costs);
                        if new_target >= old_head_cost {
                            want_optimal = true;
                        }
                    }
                    continue;
                }
                SolverResult::Unsat => {
                    let mut wce_obj = joint_objective.clone();
                    loop {
                        let core = self.kernel.oracle.core()?;
                        if core.is_empty() {
                            self.kernel.log_routine_end()?;
                            return Done(());
                        }
                        let orig_len = core.len();
                        let core = self.minimize_core(core)?;
                        if let CbData::TranslateReform {
                            katsirelos,
                            dbs,
                            olit_map,
                            translated,
                        } = &mut self.cb_data
                        {
                            // these won't be modified here
                            let olit_map = &*olit_map;

                            if core.len() == 1 {
                                let lit = core[0];
                                if let Some((obj_idx, node, oidx)) = olit_map[lit.vidx()] {
                                    // NOTE: translate abstract unit core back.
                                    // We intentionally _don't_ check whether the literal has been
                                    // translated yet here, since we want to add the translated core either
                                    // way
                                    if translated.len() <= lit.vidx() {
                                        translated.resize(lit.vidx() + 1, false);
                                    }
                                    let mut lits = vec![];
                                    let db = &dbs[obj_idx];
                                    for info in db.leaf_iter(node) {
                                        debug_assert_eq!(
                                            info.weight, 1,
                                            "OLL core reformulations are unweighted"
                                        );
                                        debug_assert_eq!(
                                            info.val_range.end - info.val_range.start,
                                            1,
                                            "should only ever have single leaves in OLL core"
                                        );
                                        let node = &db[info.id];
                                        let lit = node[info.val_range.start];
                                        if node.is_leaf() {
                                            debug_assert_eq!(
                                                info.val_range.start, 1,
                                                "true leaf must have value 1"
                                            );
                                        } else {
                                            debug_assert!(
                                                translated[lit.vidx()],
                                                "this literal must have
                                        appeared in a core, which must have been translated after
                                        core boosting"
                                            );
                                        }
                                        lits.push(lit);
                                    }
                                    self.hitting_set_solver.add_card_core(
                                        &lits,
                                        oidx + 1,
                                        CoreOrigin::Normal,
                                    );
                                    translated[lit.vidx()] = true;
                                } else {
                                    self.hitting_set_solver.learn_unit(lit);
                                }
                            } else {
                                // introduce necessary translations in HSS
                                for &lit in &core {
                                    if let Some((obj_idx, node, oidx)) = olit_map[lit.vidx()] {
                                        if translated.len() <= lit.vidx() {
                                            translated.resize(lit.vidx() + 1, false);
                                        } else if translated[lit.vidx()] {
                                            continue;
                                        }
                                        let mut lits = vec![];
                                        let db = &dbs[obj_idx];
                                        for info in db.leaf_iter(node) {
                                            debug_assert_eq!(
                                                info.weight, 1,
                                                "OLL core reformulations are unweighted"
                                            );
                                            debug_assert_eq!(
                                                info.val_range.end - info.val_range.start,
                                                1,
                                                "should only ever have single leaves in OLL core"
                                            );
                                            let node = &db[info.id];
                                            let lit = node[info.val_range.start];
                                            if node.is_leaf() {
                                                debug_assert_eq!(
                                                    info.val_range.start, 1,
                                                    "true leaf must have value 1"
                                                );
                                            } else {
                                                debug_assert!(
                                                    translated[lit.vidx()],
                                                    "this literal must have
                                        appeared in a core, which must have been translated after
                                        core boosting"
                                                );
                                            }
                                            lits.push(lit);
                                        }
                                        if *katsirelos {
                                            dbs[obj_idx][node]
                                                .reserve_vars(2.., &mut self.kernel.var_manager);
                                            let n_leafs = lits.len();
                                            for val in dbs[obj_idx][node].vals(2..) {
                                                let lit = dbs[obj_idx][node][val];
                                                lits.push(!lit);
                                                translated[lit.vidx()] = true;
                                            }
                                            debug_assert_eq!(lits.len(), n_leafs * 2 - 1);
                                            // LP_OLL eformulation from Katsirelos SAT'25
                                            // (3) constraint, reformulated as follows
                                            //   * sum(x) - sum(o) = 1
                                            //   * sum(x) + sum(not o) = k (since there are k-1 o vars)
                                            self.hitting_set_solver.add_card_eq(&lits, n_leafs);
                                            // (4)/(5) ordering constraints, slightly adapted from paper to drop e vars
                                            //   * o_j >= o_j+1
                                            for pair in lits[n_leafs..].windows(2) {
                                                self.hitting_set_solver
                                                    .add_clause(Cl::new(&[!pair[0], pair[1]]));
                                            }
                                        } else {
                                            self.hitting_set_solver.add_reified_card(
                                                &lits,
                                                oidx + 1,
                                                lit,
                                                false,
                                            );
                                            translated[lit.vidx()] = true;
                                        }
                                    }
                                }

                                self.hitting_set_solver
                                    .add_core(core.as_ref(), CoreOrigin::Normal);
                            }
                        } else if core.len() == 1 {
                            self.hitting_set_solver.learn_unit(core[0]);
                        } else {
                            self.hitting_set_solver
                                .add_core(core.as_ref(), CoreOrigin::Normal);
                        }
                        self.weed_out_assumptions(&core, &mut assumps, &mut wce_obj)?;
                        if let Some(log) = &mut self.kernel.logger {
                            log.log_ihs_core(orig_len, core.len(), false)?;
                        }
                        if assumps.is_empty() {
                            break;
                        }
                        match self.oracle_with_unit_learner(&assumps)? {
                            SolverResult::Sat => {
                                let (costs, solution) =
                                    self.kernel.get_solution_and_internal_costs(true)?;
                                self.candidates.insert(solution, costs);
                                break;
                            }
                            SolverResult::Unsat => {}
                            SolverResult::Interrupted => unreachable!(),
                        }
                        self.kernel.check_termination()?;
                    }
                    want_optimal = false;
                }
                SolverResult::Interrupted => unreachable!(),
            }

            self.kernel.check_termination()?;

            // Abstract cores based on core boosting
            let mut cb_data = std::mem::take(&mut self.cb_data);
            if let CbData::Abstract {
                reforms,
                translated,
            } = &mut cb_data
            {
                // Abstract the hitting set to the reformulated objective
                let assign: Assignment = hitting_set.iter().copied().collect();
                let mut abstracted = Assignment::default();
                let mut joint_objective = vec![0; self.kernel.var_manager.n_used() as usize + 1];
                let mut olit_map = RsHashMap::default();
                for (
                    obj_idx,
                    (
                        CbReformData {
                            db,
                            ref keep_lits,
                            ref remaining_tots,
                        },
                        obj,
                    ),
                ) in reforms.iter_mut().zip(self.kernel.objs.iter()).enumerate()
                {
                    for &lit in keep_lits {
                        if assign.lit_value(lit) == TernaryVal::False {
                            debug_assert_ne!(abstracted.lit_value(lit), TernaryVal::True);
                            abstracted.assign_lit(!lit);
                            let mut weight = isize::try_from(obj.weight(lit))
                                .expect("weight does not fit in `isize`");
                            if lit.is_neg() {
                                weight *= -1;
                            }
                            joint_objective[lit.vidx()] += weight;
                        }
                    }
                    for &(node, weight) in remaining_tots {
                        let value = db.value(node, &assign);
                        if value < db[node].max_val() {
                            let lit = db.define_unweighted(
                                node,
                                value,
                                Semantics::If,
                                &mut self.kernel.oracle,
                                &mut self.kernel.var_manager,
                            )?;
                            debug_assert_eq!(abstracted.lit_value(lit), TernaryVal::DontCare);
                            abstracted.assign_lit(!lit);
                            olit_map.insert(lit, (obj_idx, node, value + 1));
                            if joint_objective.len() <= lit.vidx() {
                                joint_objective.resize(lit.vidx() + 1, 0);
                            }
                            debug_assert_eq!(joint_objective[lit.vidx()], 0);
                            joint_objective[lit.vidx()] =
                                isize::try_from(weight).expect("weight does not fit in `isize`");
                        }
                    }
                }
                self.kernel.check_termination()?;
                // Extract cores over the reformulated objective
                let mut assumps: Vec<Lit> = abstracted.into_iter().collect();
                // sort hitting set by weight for core minimization
                if self.opts.core_minimization.minimization() {
                    // NOTE: we _intentionally_ use stable sort here, so that we preserve literal order
                    // on equal weight
                    assumps.sort_by_key(|l| -joint_objective[l.vidx()].abs());
                }
                loop {
                    match self.oracle_with_unit_learner(&assumps)? {
                        SolverResult::Sat => {
                            let (costs, solution) =
                                self.kernel.get_solution_and_internal_costs(true)?;
                            self.candidates.insert(solution, costs);
                            break;
                        }
                        SolverResult::Unsat => {}
                        SolverResult::Interrupted => unreachable!(),
                    }
                    self.kernel.check_termination()?;
                    let core = self.kernel.oracle.core()?;
                    debug_assert!(!core.is_empty());
                    let orig_len = core.len();
                    let core = self.minimize_core(core)?;

                    if core.len() == 1 {
                        let lit = core[0];
                        if let Some(&(obj_idx, node, bound)) = olit_map.get(&lit) {
                            // NOTE: translate abstract unit core back.
                            // We intentionally _don't_ check whether the literal has been
                            // translated yet here, since we want to add the translated core either
                            // way
                            if translated.len() <= lit.vidx() {
                                translated.resize(lit.vidx() + 1, false);
                            }
                            let mut lits = vec![];
                            let db = &reforms[obj_idx].db;
                            for info in db.leaf_iter(node) {
                                debug_assert_eq!(
                                    info.weight, 1,
                                    "OLL core reformulations are unweighted"
                                );
                                debug_assert_eq!(
                                    info.val_range.end - info.val_range.start,
                                    1,
                                    "should only ever have single leaves in OLL core"
                                );
                                let node = &db[info.id];
                                let lit = node[info.val_range.start];
                                if node.is_leaf() {
                                    debug_assert_eq!(
                                        info.val_range.start, 1,
                                        "true leaf must have value 1"
                                    );
                                } else {
                                    debug_assert!(
                                        translated[lit.vidx()],
                                        "this literal must have
                                        appeared in a core, which must have been translated after
                                        core boosting"
                                    );
                                }
                                lits.push(lit);
                            }
                            self.hitting_set_solver.add_card_core(
                                &lits,
                                bound,
                                CoreOrigin::Abstract,
                            );
                            translated[lit.vidx()] = true;
                        } else {
                            self.hitting_set_solver.learn_unit(lit);
                        }
                    } else {
                        // introduce necessary translations in HSS
                        for &lit in &core {
                            if let Some(&(obj_idx, node, bound)) = olit_map.get(&lit) {
                                if translated.len() <= lit.vidx() {
                                    translated.resize(lit.vidx() + 1, false);
                                } else if translated[lit.vidx()] {
                                    continue;
                                }
                                let mut lits = vec![];
                                let db = &reforms[obj_idx].db;
                                for info in db.leaf_iter(node) {
                                    debug_assert_eq!(
                                        info.weight, 1,
                                        "OLL core reformulations are unweighted"
                                    );
                                    debug_assert_eq!(
                                        info.val_range.end - info.val_range.start,
                                        1,
                                        "should only ever have single leaves in OLL core"
                                    );
                                    let node = &db[info.id];
                                    let lit = node[info.val_range.start];
                                    if node.is_leaf() {
                                        debug_assert_eq!(
                                            info.val_range.start, 1,
                                            "true leaf must have value 1"
                                        );
                                    } else {
                                        debug_assert!(
                                            translated[lit.vidx()],
                                            "this literal must have
                                        appeared in a core, which must have been translated after
                                        core boosting"
                                        );
                                    }
                                    lits.push(lit);
                                }
                                self.hitting_set_solver
                                    .add_reified_card(&lits, bound, lit, false);
                                translated[lit.vidx()] = true;
                            }
                        }

                        self.hitting_set_solver
                            .add_core(core.as_ref(), CoreOrigin::Abstract);
                    }
                    self.weed_out_assumptions(&core, &mut assumps, &mut joint_objective)?;
                    if let Some(log) = &mut self.kernel.logger {
                        log.log_ihs_core(orig_len, core.len(), true)?;
                    }
                    if assumps.is_empty() {
                        break;
                    }
                }
            }
            self.cb_data = cb_data;
        }
    }

    /// Separate algorithm branch for when the entire instance was seeded into the hitting set
    /// solver
    fn main_fully_seeded(&mut self) -> MaybeTerminatedError {
        debug_assert!(
            (self.n_seeded as f64 / self.kernel.stats.n_orig_clauses as f64 - 1.0).abs()
                < f64::EPSILON
        );
        self.kernel.log_routine_start("ihs (fully seeded)")?;
        loop {
            self.kernel.log_routine_start("extract hitting set")?;
            let hitting_set_answer = self.hitting_set_solver.optimal_hitting_set(None);
            let (cost, hitting_set) = match hitting_set_answer {
                CompleteSolveResult::Optimal(cost, hitting_set) => (cost, hitting_set),
                CompleteSolveResult::Infeasible => {
                    self.kernel.log_routine_end()?;
                    self.kernel.log_routine_end()?;
                    return Done(());
                }
            };
            self.kernel.log_routine_end()?;
            if let Some(logger) = &mut self.kernel.logger {
                logger.log_hitting_set(cost, true)?;
            }
            self.kernel.check_termination()?;
            let (costs, solution) = self.hitting_set_to_solution_and_internal_costs(hitting_set);
            // store solution
            self.kernel
                .yield_solutions(costs.clone(), &[], solution, &mut self.pareto_front)?;
            // introduce PD cut in the hitting set solver
            self.hitting_set_solver.add_pd_cut(&costs);
        }
    }

    /// Initializes the candidates according to the selected strategy
    fn seed_candidates(&mut self) -> MaybeTerminatedError<bool> {
        match self.opts.candidate_seeding {
            CandidateSeeding::None => Done(false),
            CandidateSeeding::OneSolution => match self.kernel.solve()? {
                SolverResult::Sat => {
                    let (costs, solution) = self.kernel.get_solution_and_internal_costs(false)?;
                    self.candidates.insert(solution, costs);
                    Done(false)
                }
                SolverResult::Unsat => Done(true),
                SolverResult::Interrupted => unreachable!(),
            },
        }
    }

    fn hitting_set_to_solution_and_internal_costs(
        &self,
        hitting_set: Vec<Lit>,
    ) -> (Vec<usize>, Assignment) {
        let sol: Assignment = hitting_set.into_iter().collect();
        let costs = self.kernel.compute_costs(&sol);
        debug_assert_eq!(costs.len(), self.kernel.stats.n_objs);
        (costs, sol)
    }

    fn minimize_core(&mut self, core: Vec<Lit>) -> MaybeTerminatedError<Vec<Lit>> {
        std::mem::swap(
            &mut self.opts.core_minimization,
            &mut self.kernel.opts.core_minimization,
        );
        let (core, _) = self.kernel.trim_core(core, &[], None)?;
        let (core, _) = self.kernel.minimize_core(core, &[], None)?;
        std::mem::swap(
            &mut self.opts.core_minimization,
            &mut self.kernel.opts.core_minimization,
        );
        Done(core)
    }

    fn oracle_with_unit_learner(&mut self, assumps: &[Lit]) -> MaybeTerminatedError<SolverResult> {
        let hss = (&mut self.hitting_set_solver) as *mut Hss;
        let obj_lits = (&mut self.objective_lits) as *mut RsHashSet<Lit>;
        self.kernel.oracle.attach_learner(
            move |cl| {
                debug_assert_eq!(cl.len(), 1);
                // SAFETY: the callback will only ever be called from within the oracle call on the
                // next line
                let hss = unsafe { &mut *hss };
                let obj_lits = unsafe { &mut *obj_lits };
                if obj_lits.contains(&cl[0]) || obj_lits.contains(&!cl[0]) {
                    hss.learn_unit(cl[0]);
                }
            },
            0,
        );
        let res = self.kernel.solve_assumps(assumps);
        self.kernel.oracle.detach_learner();
        let res = res?;
        self.kernel.check_termination()?;
        Done(res)
    }

    fn weed_out_assumptions(
        &mut self,
        core: &[Lit],
        assumps: &mut Vec<Lit>,
        wce_obj: &mut [isize],
    ) -> MaybeTerminatedError {
        let _len_before = assumps.len();
        if self.opts.wce {
            let min_cost = core.iter().fold(isize::MAX, |min, lit| {
                std::cmp::min(wce_obj[lit.vidx()].abs(), min)
            });
            for lit in core {
                if lit.is_pos() {
                    wce_obj[lit.vidx()] -= min_cost;
                } else {
                    wce_obj[lit.vidx()] += min_cost;
                }
            }
            assumps.retain(|&lit| wce_obj[lit.vidx()] != 0);
        } else {
            // NOTE: core is in same order as hitting set, we can therefore remove the
            // core literals in a single sweep, knowing that the
            // with core minimization, the assumptions are ordered by weight,
            // otherwise by literal (from the hitting set solver / abstraction)
            let mut core_idx = 0;
            if self.opts.core_minimization.minimization() {
                assumps.retain(|&lit| {
                    while core_idx < core.len()
                        && (wce_obj[core[core_idx].vidx()].abs() > wce_obj[lit.vidx()].abs()
                            || (wce_obj[core[core_idx].vidx()].abs() == wce_obj[lit.vidx()].abs()
                                && core[core_idx] < !lit))
                    {
                        core_idx += 1;
                    }
                    if core_idx >= core.len() || !lit != core[core_idx] {
                        return true;
                    }
                    false
                });
            } else {
                assumps.retain(|&lit| {
                    while core_idx < core.len() && core[core_idx] < !lit {
                        core_idx += 1;
                    }
                    if core_idx >= core.len() || !lit != core[core_idx] {
                        return true;
                    }
                    false
                });
            };
        }
        debug_assert!(
            assumps.len() < _len_before,
            "something should be removed from the assumptions"
        );
        Done(())
    }
}

impl<'slv, Hss, OInit, BCG> CoreBoost
    for ParetoIhs<rustsat_cadical::CaDiCaL<'_, 'slv>, Hss, OInit, BCG>
where
    Hss: HittingSetSolver + 'slv,
    BCG: Fn(Assignment) -> Clause,
{
    type Options = IhsCbOptions;

    fn core_boost(&mut self, opts: Self::Options) -> MaybeTerminatedError<bool> {
        ensure!(
            self.kernel.stats.n_solve_calls == 0,
            "cannot perform core boosting after solve has been called"
        );
        let mut cores = vec![vec![]; self.kernel.stats.n_objs];
        let Some(cb_res) = self.kernel.core_boost_with_callbacks(
            |kernel, _, sol| {
                let costs = kernel.compute_costs(&sol);
                self.candidates.insert(sol, costs);
            },
            |_, obj_idx, id, bound| cores[obj_idx].push((id, bound)),
        )?
        else {
            return Done(false);
        };
        self.kernel.check_termination()?;

        self.kernel.log_routine_start("cb post treatment")?;

        if opts.treatment.reform() {
            self.objective_lits.clear();
        }

        let mut translated = vec![false; self.kernel.var_manager.n_used() as usize + 1];
        let mut olit_map = vec![None; self.kernel.var_manager.n_used() as usize + 1];
        let mut reform_objs = Vec::with_capacity(cb_res.len());
        let mut reforms = Vec::with_capacity(cb_res.len());
        let mut lower_bounds = Vec::with_capacity(cb_res.len());
        let mut tot_dbs = Vec::with_capacity(cb_res.len());
        for (
            obj_idx,
            (
                CbResult {
                    reform,
                    solution,
                    mut tot_db,
                },
                cores,
            ),
        ) in cb_res.into_iter().zip(cores).enumerate()
        {
            if let Some(solution) = solution {
                let costs = self.kernel.compute_costs(&solution);
                self.candidates.insert(solution, costs);
            }

            match opts.treatment {
                IhsCbTreatment::Ignore => {
                    let mut reform_obj = Vec::with_capacity(reform.inactives.len());
                    for (&lit, &weight) in &reform.inactives {
                        reform_obj.push((lit, weight));
                        self.objective_lits.insert(lit);
                        self.max_obj_var = std::cmp::max(self.max_obj_var, lit.var());
                        if let Some(&ReformData {
                            root,
                            oidx,
                            tot_weight,
                            ..
                        }) = reform.reformulations.get(&lit)
                        {
                            debug_assert_ne!(weight, 0);
                            debug_assert!(oidx < tot_db[root].len());
                            for idx in oidx + 1..tot_db[root].len() {
                                let lit = tot_db.define_unweighted(
                                    root,
                                    idx,
                                    Semantics::If,
                                    &mut self.kernel.oracle,
                                    &mut self.kernel.var_manager,
                                )?;
                                reform_obj.push((lit, tot_weight));
                                self.objective_lits.insert(lit);
                                self.max_obj_var = std::cmp::max(self.max_obj_var, lit.var());
                            }
                        }
                    }
                    reform_objs.push((reform_obj, reform.offset));
                }
                IhsCbTreatment::Translate
                | IhsCbTreatment::TranslateKatsirelos
                | IhsCbTreatment::TranslateReform
                | IhsCbTreatment::TranslateKatsirelosReform
                | IhsCbTreatment::Abstract => {
                    for (root, bound) in cores {
                        let mut to_translate = vec![];
                        let mut lits = vec![];
                        for info in tot_db.leaf_iter(root) {
                            debug_assert_eq!(
                                info.weight, 1,
                                "OLL core reformulations are unweighted"
                            );
                            debug_assert_eq!(
                                info.val_range.end - info.val_range.start,
                                1,
                                "should only ever have single leaves in OLL core"
                            );
                            let node = &tot_db[info.id];
                            if node.is_leaf() {
                                debug_assert_eq!(
                                    info.val_range.start, 1,
                                    "true leaf must have value 1"
                                );
                                lits.push(node[1]);
                            } else {
                                to_translate.push(info);
                            }
                        }

                        // translate totalizer outputs from lower layers
                        for info in to_translate {
                            let val = info.val_range.start;
                            let lit = tot_db[info.id][val];
                            lits.push(lit);
                            if translated[lit.vidx()] {
                                continue;
                            }
                            let mut lits = vec![];
                            for info in tot_db.leaf_iter(info.id) {
                                debug_assert_eq!(
                                    info.weight, 1,
                                    "OLL core reformulations are unweighted"
                                );
                                debug_assert_eq!(
                                    info.val_range.end - info.val_range.start,
                                    1,
                                    "should only ever have single leaves in OLL core"
                                );
                                let node = &tot_db[info.id];
                                let lit = node[info.val_range.start];
                                if node.is_leaf() {
                                    debug_assert_eq!(
                                        info.val_range.start, 1,
                                        "true leaf must have value 1"
                                    );
                                } else {
                                    debug_assert!(
                                            translated[lit.vidx()],
                                            "this literal must have appeared in a another core, which must have been before in `cores`"
                                            );
                                }
                                lits.push(lit);
                            }
                            if opts.treatment.katsirelos() {
                                tot_db[info.id].reserve_vars(2.., &mut self.kernel.var_manager);
                                let n_leafs = lits.len();
                                for val in tot_db[info.id].vals(2..) {
                                    let lit = tot_db[info.id][val];
                                    lits.push(!lit);
                                    translated[lit.vidx()] = true;
                                }
                                debug_assert_eq!(lits.len(), n_leafs * 2 - 1);
                                // LP_OLL eformulation from Katsirelos SAT'25
                                // (3) constraint, reformulated as follows
                                //   * sum(x) - sum(o) = 1
                                //   * sum(x) + sum(not o) = k (since there are k-1 o vars)
                                self.hitting_set_solver.add_card_eq(&lits, n_leafs);
                                // (4)/(5) ordering constraints, slightly adapted from paper to drop e vars
                                //   * o_j >= o_j+1
                                for pair in lits[n_leafs..].windows(2) {
                                    self.hitting_set_solver
                                        .add_clause(Cl::new(&[!pair[0], pair[1]]));
                                }
                            } else {
                                self.hitting_set_solver
                                    .add_reified_card(&lits, val, lit, false);
                                translated[lit.vidx()] = true;
                            }
                        }
                        // NOTE: all variables in the core were introduced in the HSS in the above
                        // loop, even if they are not from the original objective
                        self.hitting_set_solver.add_card_core(
                            &lits,
                            bound,
                            CoreOrigin::CoreBoosting,
                        );
                    }

                    lower_bounds.push(reform.offset);
                    if matches!(
                        opts.treatment,
                        IhsCbTreatment::TranslateReform | IhsCbTreatment::TranslateKatsirelosReform
                    ) {
                        let mut reform_obj = Vec::with_capacity(reform.inactives.len());
                        for (&lit, &weight) in &reform.inactives {
                            reform_obj.push((lit, weight));
                            self.objective_lits.insert(lit);
                            self.max_obj_var = std::cmp::max(self.max_obj_var, lit.var());
                            // NOTE: we only _reserve_ variables here, but lazily encode them
                            // whenever they appear negated in a hitting set
                            if let Some(&ReformData {
                                root,
                                oidx,
                                tot_weight,
                                ..
                            }) = reform.reformulations.get(&lit)
                            {
                                debug_assert_ne!(weight, 0);
                                debug_assert!(oidx < tot_db[root].len());
                                olit_map[lit.vidx()] = Some((obj_idx, root, oidx));
                                tot_db[root].reserve_vars(oidx + 2.., &mut self.kernel.var_manager);
                                if olit_map.len() <= self.kernel.var_manager.n_used() as usize {
                                    olit_map.resize(
                                        self.kernel.var_manager.n_used() as usize + 1,
                                        None,
                                    );
                                }
                                let mut last_lit = lit;
                                for idx in oidx + 1..tot_db[root].len() {
                                    let lit = tot_db[root][idx + 1];
                                    reform_obj.push((lit, tot_weight));
                                    self.objective_lits.insert(lit);
                                    self.max_obj_var = std::cmp::max(self.max_obj_var, lit.var());
                                    olit_map[lit.vidx()] = Some((obj_idx, root, idx));
                                    // Ordering constraints over totalizer output variables in HSS
                                    self.hitting_set_solver
                                        .add_clause(Cl::new(&[last_lit, !lit]));
                                    last_lit = lit;
                                }
                            }
                        }
                        tot_dbs.push(tot_db);
                        reform_objs.push((reform_obj, reform.offset));
                    } else if opts.treatment == IhsCbTreatment::Abstract {
                        let mut keep_lits = vec![];
                        let mut remaining_tots = vec![];
                        for (&lit, _) in reform.inactives.iter() {
                            if let Some(&ReformData {
                                root, tot_weight, ..
                            }) = reform.reformulations.get(&lit)
                            {
                                remaining_tots.push((root, tot_weight));
                            } else {
                                keep_lits.push(lit);
                            }
                        }
                        reforms.push(CbReformData {
                            db: tot_db,
                            keep_lits,
                            remaining_tots,
                        });
                    }
                }
            }
        }

        match opts.treatment {
            IhsCbTreatment::Ignore => {
                self.cb_data = CbData::Ignore;
                self.hitting_set_solver.change_objectives(reform_objs);
            }
            IhsCbTreatment::Translate | IhsCbTreatment::TranslateKatsirelos => {
                self.cb_data = CbData::Translate;
                self.hitting_set_solver.change_lower_bounds(lower_bounds);
            }
            IhsCbTreatment::TranslateReform | IhsCbTreatment::TranslateKatsirelosReform => {
                self.cb_data = CbData::TranslateReform {
                    katsirelos: opts.treatment.katsirelos(),
                    dbs: tot_dbs,
                    olit_map,
                    translated,
                };
                self.hitting_set_solver.change_objectives(reform_objs);
            }
            IhsCbTreatment::Abstract => {
                self.cb_data = CbData::Abstract {
                    reforms,
                    translated,
                };
                self.hitting_set_solver.change_lower_bounds(lower_bounds);
            }
        }

        self.kernel.log_routine_end()?;
        self.kernel.check_termination()?;

        Done(true)
    }
}

#[derive(Debug, Default)]
enum CbData {
    #[default]
    None,
    Ignore,
    Translate,
    TranslateReform {
        katsirelos: bool,
        dbs: Vec<TotDb>,
        olit_map: Vec<Option<(usize, NodeId, usize)>>,
        translated: Vec<bool>,
    },
    Abstract {
        reforms: Vec<CbReformData>,
        translated: Vec<bool>,
    },
}

#[derive(Debug)]
struct CbReformData {
    db: TotDb,
    keep_lits: Vec<Lit>,
    remaining_tots: Vec<(NodeId, usize)>,
}
