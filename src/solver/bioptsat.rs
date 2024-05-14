//! # BiOptSat Algorithm for Bi-Objective Optimization
//!
//! ## References
//!
//! - \[1\] Christoph Jabs and Jeremias Berg and Andreas Niskanen and Matti
//! Järvisalo: _MaxSAT-Based Bi-Objective Boolean Optimization_, SAT 2022.

use rustsat::{
    encodings::{
        self,
        card::{self, DbTotalizer},
        pb::{self, DbGte},
        EncodeStats,
    },
    instances::{BasicVarManager, ManageVars, MultiOptInstance},
    solvers::{SolveIncremental, SolveStats, SolverResult, SolverStats},
    types::{Assignment, Clause, Lit},
};
use rustsat_cadical::CaDiCaL;
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{
    options::{AfterCbOptions, CoreBoostingOptions},
    termination::ensure,
    types::{NonDomPoint, ParetoFront},
    EncodingStats, ExtendedSolveStats, KernelFunctions, KernelOptions, Limits,
    MaybeTerminatedError::{self, Done},
    Solve,
};

use super::{
    coreboosting::MergeOllRef, default_blocking_clause, CoreBoost, ObjEncoding, Objective,
    SolverKernel,
};

#[derive(KernelFunctions, Solve)]
#[solve(
    bounds = "where PBE: pb::BoundUpperIncremental + EncodeStats,
        CE: card::BoundUpperIncremental + EncodeStats,
        VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental + SolveStats",
    extended_stats
)]
pub struct BiOptSat<
    PBE = DbGte,
    CE = DbTotalizer,
    VM = BasicVarManager,
    BCG = fn(Assignment) -> Clause,
    O = CaDiCaL<'static, 'static>,
> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: (ObjEncoding<PBE, CE>, ObjEncoding<PBE, CE>),
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

#[oracle_bounds]
impl<PBE, CE, VM, O> BiOptSat<PBE, CE, VM, fn(Assignment) -> Clause, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    O: SolveIncremental + SolveStats,
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
impl<PBE, CE, VM, BCG, O> BiOptSat<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + SolveStats + Default,
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
impl<PBE, CE, VM, O> BiOptSat<PBE, CE, VM, fn(Assignment) -> Clause, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    O: SolveIncremental + SolveStats + Default,
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
impl<PBE, CE, VM, BCG, O> BiOptSat<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + SolveStats,
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

impl<PBE, CE, VM, BCG, O> ExtendedSolveStats for BiOptSat<PBE, CE, VM, BCG, O>
where
    PBE: encodings::EncodeStats,
    CE: encodings::EncodeStats,
    O: SolveStats,
{
    fn oracle_stats(&self) -> SolverStats {
        self.kernel.oracle.stats()
    }

    fn encoding_stats(&self) -> Vec<EncodingStats> {
        self.kernel
            .objs
            .iter()
            .zip([&self.obj_encs.0, &self.obj_encs.1])
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

impl<PBE, CE, VM, BCG, O> BiOptSat<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    O: SolveIncremental + SolveStats,
{
    /// Initializes the solver
    fn init(mut kernel: SolverKernel<VM, O, BCG>) -> Self {
        assert_eq!(kernel.stats.n_objs, 2);
        // Initialize objective encodings
        let inc_enc = match &kernel.objs[0] {
            Objective::Weighted { lits, .. } => ObjEncoding::<PBE, CE>::new_weighted(
                lits.iter().map(|(&l, &w)| (l, w)),
                kernel.opts.reserve_enc_vars,
                &mut kernel.var_manager,
            ),
            Objective::Unweighted { lits, .. } => ObjEncoding::<PBE, CE>::new_unweighted(
                lits.iter().copied(),
                kernel.opts.reserve_enc_vars,
                &mut kernel.var_manager,
            ),
            Objective::Constant { .. } => ObjEncoding::Constant,
        };
        let dec_enc = match &kernel.objs[1] {
            Objective::Weighted { lits, .. } => ObjEncoding::<PBE, CE>::new_weighted(
                lits.iter().map(|(&l, &w)| (l, w)),
                kernel.opts.reserve_enc_vars,
                &mut kernel.var_manager,
            ),
            Objective::Unweighted { lits, .. } => ObjEncoding::<PBE, CE>::new_unweighted(
                lits.iter().copied(),
                kernel.opts.reserve_enc_vars,
                &mut kernel.var_manager,
            ),
            Objective::Constant { .. } => ObjEncoding::Constant,
        };
        Self {
            kernel,
            obj_encs: (inc_enc, dec_enc),
            pareto_front: Default::default(),
        }
    }
}

#[oracle_bounds]
impl<PBE, CE, VM, BCG, O> BiOptSat<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + SolveStats,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> MaybeTerminatedError {
        self.kernel.bioptsat(
            (0, 1),
            (&mut self.obj_encs.0, &mut self.obj_encs.1),
            &[],
            None,
            (None, None),
            |_| None,
            &mut self.pareto_front,
        )
    }
}

#[oracle_bounds]
impl<PBE, CE, VM, BCG, O> CoreBoost for BiOptSat<PBE, CE, VM, BCG, O>
where
    (PBE, CE): MergeOllRef<PBE = PBE, CE = CE>,
    VM: ManageVars,
    O: SolveIncremental + SolveStats + Default,
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
                let mut encs = self.kernel.inprocess(techs, cb_res)?;
                self.obj_encs.1 = encs.pop().unwrap();
                self.obj_encs.0 = encs.pop().unwrap();
                self.kernel.check_termination()?;
                return Done(true);
            }
        };
        self.kernel.log_routine_start("merge encodings")?;
        for (oidx, (reform, mut tot_db)) in cb_res.into_iter().enumerate() {
            if reset_dbs {
                tot_db.reset_vars();
            }
            if !matches!(self.kernel.objs[oidx], Objective::Constant { .. }) {
                if oidx == 0 {
                    self.obj_encs.0 = <(PBE, CE)>::merge(reform, tot_db, opts.rebase);
                } else {
                    self.obj_encs.1 = <(PBE, CE)>::merge(reform, tot_db, opts.rebase);
                }
            }
            self.kernel.check_termination()?;
        }
        self.kernel.log_routine_end()?;
        Done(true)
    }
}

#[oracle_bounds]
impl<VM, O, BCG> SolverKernel<VM, O, BCG>
where
    VM: ManageVars,
    O: SolveIncremental + SolveStats,
    BCG: FnMut(Assignment) -> Clause,
{
    /// Runs the BiOptSat algorithm on two objectives. BiOptSat is run in the
    /// LSU variant.
    ///
    /// `starting_point`: optional starting point with known cost of increasing
    /// objective
    ///
    /// `lookup`: for a value of the increasing objective, checks if the
    /// non-dominated point has already been discovered and returns the
    /// corresponding value of the decreasing objective
    pub fn bioptsat<PBE, CE, Lookup, Col>(
        &mut self,
        (inc_obj, dec_obj): (usize, usize),
        (inc_encoding, dec_encoding): (&mut ObjEncoding<PBE, CE>, &mut ObjEncoding<PBE, CE>),
        base_assumps: &[Lit],
        starting_point: Option<(usize, Assignment)>,
        (inc_lb, dec_lb): (Option<usize>, Option<usize>),
        lookup: Lookup,
        collector: &mut Col,
    ) -> MaybeTerminatedError
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
        Lookup: Fn(usize) -> Option<usize>,
        Col: Extend<NonDomPoint>,
    {
        self.log_routine_start("bioptsat")?;

        let mut inc_lb = inc_lb.unwrap_or(inc_encoding.offset());
        let dec_lb = dec_lb.unwrap_or(dec_encoding.offset());

        let mut assumps = Vec::from(base_assumps);
        let (mut inc_cost, mut sol) = if let Some(bound) = starting_point {
            bound
        } else {
            let res = self.solve_assumps(&assumps)?;
            if res == SolverResult::Unsat {
                return Done(());
            }
            let mut sol = self.oracle.solution(self.max_inst_var)?;
            let cost = self.get_cost_with_heuristic_improvements(inc_obj, &mut sol, true)?;
            (cost, sol)
        };
        let mut dec_cost;
        loop {
            // minimize inc_obj
            (inc_cost, sol) = if let Some(res) = self.linsu(
                inc_obj,
                inc_encoding,
                &assumps,
                Some((inc_cost, Some(sol))),
                Some(inc_lb),
            )? {
                res
            } else {
                // no solutions
                self.log_routine_end()?;
                return Done(());
            };
            inc_lb = inc_cost + 1;
            dec_cost = self.get_cost_with_heuristic_improvements(dec_obj, &mut sol, false)?;
            if let Some(found) = lookup(inc_cost) {
                dec_cost = found;
            } else {
                // bound inc_obj
                inc_encoding.encode_ub_change(
                    inc_cost..inc_cost + 1,
                    &mut self.oracle,
                    &mut self.var_manager,
                )?;
                assumps.extend(inc_encoding.enforce_ub(inc_cost).unwrap());
                // minimize dec_obj
                dec_cost = self
                    .linsu_yield(
                        dec_obj,
                        dec_encoding,
                        &assumps,
                        Some((dec_cost, Some(sol))),
                        Some(dec_lb),
                        collector,
                    )?
                    .unwrap();
            };
            // termination condition: can't decrease decreasing objective further
            if dec_cost <= dec_lb {
                break;
            }
            // skip to next non-dom
            assumps.drain(base_assumps.len()..);
            dec_encoding.encode_ub_change(
                dec_cost - 1..dec_cost,
                &mut self.oracle,
                &mut self.var_manager,
            )?;
            assumps.extend(dec_encoding.enforce_ub(dec_cost - 1).unwrap());
            (sol, inc_cost) = match self.solve_assumps(&assumps)? {
                SolverResult::Sat => {
                    let mut sol = self.oracle.solution(self.max_inst_var)?;
                    let cost =
                        self.get_cost_with_heuristic_improvements(inc_obj, &mut sol, true)?;
                    (sol, cost)
                }
                SolverResult::Unsat => break,
                _ => panic!(),
            };
        }
        self.log_routine_end()?;
        Done(())
    }
}
