//! # Paretop-k
//!
//! Finding the non-dominated set via single-objective core-guided search where everytime an
//! optimal solution is found, we are blocking all solutions dominated by it and keep going.

use rustsat::{
    encodings::{
        self,
        card::{self, dbtotalizer::TotDb, DbTotalizer},
        pb::{self, DbGte},
        EncodeStats,
    },
    instances::{BasicVarManager, ManageVars, MultiOptInstance},
    solvers::{SolveIncremental, SolveStats, SolverStats},
    types::{Assignment, Clause, Lit},
};
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{
    options::AfterCbOptions,
    termination::ensure,
    types::ParetoFront,
    CoreBoost, CoreBoostingOptions, EncodingStats, ExtendedSolveStats, KernelFunctions,
    KernelOptions, Limits,
    MaybeTerminatedError::{self, Done},
    Solve,
};

use super::{
    coreboosting::MergeOllRef, coreguided::OllReformulation, default_blocking_clause, ObjEncoding,
    Objective, SolverKernel,
};

/// A solver type for the Paretop-k algorithm
///
/// # Generics
///
/// - `O`: the SAT solver backend
/// - `PBE`: the pseudo-Boolean objective encoding
/// - `CE`: the cardinality objective encoding
/// - `VM`: the variable manager of the input
/// - `BCG`: the blocking clause generator
#[derive(KernelFunctions, Solve)]
#[solve(
    bounds = "where PBE: pb::BoundUpperIncremental + EncodeStats,
        CE: card::BoundUpperIncremental + EncodeStats,
        VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental + SolveStats",
    extended_stats
)]
pub struct ParetopK<
    O,
    PBE = DbGte,
    CE = DbTotalizer,
    VM = BasicVarManager,
    BCG = fn(Assignment) -> Clause,
> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: Vec<ObjEncoding<PBE, CE>>,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
    /// The current reformulation of the joint objective
    reform: OllReformulation,
    /// The totalzier database for single-objective OLL
    tot_db: TotDb,
}

#[oracle_bounds]
impl<O, PBE, CE, VM> ParetopK<O, PBE, CE, VM, fn(Assignment) -> Clause>
where
    O: SolveIncremental,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
{
    pub fn new_default_blocking(
        inst: MultiOptInstance<VM>,
        oracle: O,
        opts: KernelOptions,
    ) -> anyhow::Result<Self> {
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            oracle,
            default_blocking_clause,
            opts,
        )?;
        Ok(Self::init(kernel))
    }
}

#[oracle_bounds]
impl<O, PBE, CE, VM, BCG> ParetopK<O, PBE, CE, VM, BCG>
where
    O: SolveIncremental + Default,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
{
    pub fn new_default_oracle(
        inst: MultiOptInstance<VM>,
        opts: KernelOptions,
        block_clause_gen: BCG,
    ) -> anyhow::Result<Self> {
        let kernel = SolverKernel::new(inst, O::default(), block_clause_gen, opts)?;
        Ok(Self::init(kernel))
    }
}

#[oracle_bounds]
impl<O, PBE, CE, VM> ParetopK<O, PBE, CE, VM, fn(Assignment) -> Clause>
where
    O: SolveIncremental + Default,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
{
    pub fn new_defaults(inst: MultiOptInstance<VM>, opts: KernelOptions) -> anyhow::Result<Self> {
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            O::default(),
            default_blocking_clause,
            opts,
        )?;
        Ok(Self::init(kernel))
    }
}

#[oracle_bounds]
impl<O, PBE, CE, VM, BCG> ParetopK<O, PBE, CE, VM, BCG>
where
    O: SolveIncremental,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
{
    /// Initializes a default solver with a configured oracle and options. The
    /// oracle should _not_ have any clauses loaded yet.
    pub fn new(
        inst: MultiOptInstance<VM>,
        oracle: O,
        opts: KernelOptions,
        block_clause_gen: BCG,
    ) -> anyhow::Result<Self> {
        let kernel = SolverKernel::new(inst, oracle, block_clause_gen, opts)?;
        Ok(Self::init(kernel))
    }
}

impl<O, PBE, CE, VM, BCG> ExtendedSolveStats for ParetopK<O, PBE, CE, VM, BCG>
where
    O: SolveStats,
    PBE: encodings::EncodeStats,
    CE: encodings::EncodeStats,
{
    fn oracle_stats(&self) -> SolverStats {
        self.kernel.oracle.stats()
    }

    fn encoding_stats(&self) -> Vec<EncodingStats> {
        self.kernel
            .objs
            .iter()
            .zip(self.obj_encs.iter())
            .map(|(obj, enc)| {
                let mut s = EncodingStats {
                    offset: obj.offset(),
                    ..Default::default()
                };
                if let Objective::Unweighted { unit_weight, .. } = obj {
                    s.unit_weight = Some(*unit_weight);
                };
                match enc {
                    ObjEncoding::Weighted(enc, _) => {
                        s.n_vars = enc.n_vars();
                        s.n_clauses = enc.n_clauses()
                    }
                    ObjEncoding::Unweighted(enc, _) => {
                        s.n_vars = enc.n_vars();
                        s.n_clauses = enc.n_clauses()
                    }
                    ObjEncoding::Constant => (),
                };
                s
            })
            .collect()
    }
}

impl<O, PBE, CE, VM, BCG> ParetopK<O, PBE, CE, VM, BCG>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
{
    /// Initializes the solver
    fn init(mut kernel: SolverKernel<VM, O, BCG>) -> Self {
        // Initialize objective encodings
        let obj_encs = kernel
            .objs
            .iter()
            .map(|obj| match obj {
                Objective::Weighted { lits, .. } => ObjEncoding::new_weighted(
                    lits.iter().map(|(&l, &w)| (l, w)),
                    kernel.opts.reserve_enc_vars,
                    &mut kernel.var_manager,
                ),
                Objective::Unweighted { lits, .. } => ObjEncoding::new_unweighted(
                    lits.iter().copied(),
                    kernel.opts.reserve_enc_vars,
                    &mut kernel.var_manager,
                ),
                Objective::Constant { .. } => ObjEncoding::Constant,
            })
            .collect();
        let mut joint_obj = OllReformulation::default();
        for obj in kernel.objs.iter() {
            joint_obj.extend(&obj.into());
        }
        joint_obj.inactives.final_cleanup();
        Self {
            kernel,
            obj_encs,
            pareto_front: Default::default(),
            reform: joint_obj,
            tot_db: TotDb::default(),
        }
    }
}

#[oracle_bounds]
impl<O, PBE, CE, VM, BCG> ParetopK<O, PBE, CE, VM, BCG>
where
    O: SolveIncremental + SolveStats,
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> MaybeTerminatedError {
        debug_assert_eq!(self.obj_encs.len(), self.kernel.stats.n_objs);
        self.kernel.log_routine_start("paretop-k")?;
        loop {
            // run single-objective OLL on joint objective
            let Some(mut sol) = self.kernel.oll(&mut self.reform, &[], &mut self.tot_db)? else {
                return Done(());
            };
            let costs = (0..self.kernel.objs.len())
                .map(|idx| {
                    self.kernel
                        .get_cost_with_heuristic_improvements(idx, &mut sol, false)
                })
                .collect::<Result<Vec<usize>, _>>()?;
            self.kernel.check_termination()?;
            debug_assert_eq!(costs.iter().sum::<usize>(), self.reform.offset);

            // enumerate at non-dominated point
            let assumps: Vec<_> = self
                .kernel
                .enforce_dominating(&costs, &mut self.obj_encs)?
                .collect();
            self.kernel
                .yield_solutions(&costs, &assumps, sol, &mut self.pareto_front)?;

            // block dominated solutions
            let block_clause = self
                .kernel
                .dominated_block_clause(&costs, &mut self.obj_encs)?;
            self.kernel.oracle.add_clause(block_clause)?;
        }
    }
}

#[oracle_bounds]
impl<O, PBE, CE, VM, BCG> CoreBoost for ParetopK<O, PBE, CE, VM, BCG>
where
    O: SolveIncremental + SolveStats + Default,
    (PBE, CE): MergeOllRef<PBE = PBE, CE = CE>,
    VM: ManageVars,
{
    fn core_boost(&mut self, opts: CoreBoostingOptions) -> MaybeTerminatedError<bool> {
        ensure!(
            self.kernel.stats.n_solve_calls == 0,
            "cannot perform core boosting after solve has been called"
        );
        let cb_res = if let Some(cb_res) = self.kernel.core_boost()? {
            cb_res
        } else {
            return Done(false);
        };
        self.kernel.check_termination()?;
        let reset_dbs = match &opts.after {
            AfterCbOptions::Nothing => false,
            AfterCbOptions::Reset => {
                self.kernel.reset_oracle(true)?;
                self.kernel.check_termination()?;
                true
            }
            AfterCbOptions::Inpro(techs) => {
                self.obj_encs = self.kernel.inprocess(techs, cb_res)?;
                self.kernel.check_termination()?;
                return Done(true);
            }
        };
        self.kernel.log_routine_start("merge encodings")?;
        self.reform = OllReformulation::default();
        for (oidx, (reform, mut tot_db)) in cb_res.into_iter().enumerate() {
            if reset_dbs {
                tot_db.reset_vars();
            }
            // FIXME: this doesn't work like this. we we need to merge the different tot dbs and
            // keep them for the joint objective
            todo!();
            self.reform.extend(&reform);
            if !matches!(self.kernel.objs[oidx], Objective::Constant { .. }) {
                self.obj_encs[oidx] = <(PBE, CE)>::merge(reform, tot_db, opts.rebase);
            }
            self.kernel.check_termination()?;
        }
        self.kernel.log_routine_end()?;
        Done(true)
    }
}
