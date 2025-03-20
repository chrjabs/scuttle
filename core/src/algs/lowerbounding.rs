//! # Multi-Objective Lower-Bounding Search
//!
//! Algorithm proposed in \[1\].
//!
//! ## References
//!
//! - \[1\] Joao Cortes and Ines Lynce and Vasco M. Maquinho: _New Core-Guided
//!     and Hitting Set Algorithms for Multi-Objective Combinatorial Optimization_,
//!     TACAS 2023.

use std::{fs, io};

use cadical_veripb_tracer::CadicalCertCollector;
use pigeons::ConstraintId;
use rustsat::{
    clause,
    encodings::{
        self,
        card::{self, DbTotalizer},
        pb::{self, DbGte},
    },
    solvers::{
        DefaultInitializer, Initialize, Solve, SolveIncremental, SolveStats, SolverResult,
        SolverStats,
    },
    types::{Assignment, Clause, Lit, Var},
};
use scuttle_proc::KernelFunctions;

use crate::{
    options::{AfterCbOptions, CoreBoostingOptions},
    termination::ensure,
    types::{NonDomPoint, ParetoFront, VarManager},
    EncodingStats, ExtendedSolveStats, KernelFunctions, KernelOptions, Limits,
    MaybeTerminatedError::{self, Done},
    Phase,
};

use super::{coreboosting::MergeOllRef, proofs, CoreBoost, Kernel, ObjEncoding, Objective};

/// The lower-bounding algorithm type
///
/// # Generics
///
/// - `O`: the SAT solver oracle
/// - `PBE`: pseudo-Boolean objective encoding
/// - `CE`: cardinality objective encoding
/// - `ProofW`: the proof writer
/// - `OInit`: the oracle initializer
/// - `BCG`: the blocking clause generator
#[derive(KernelFunctions)]
pub struct LowerBounding<
    O,
    PBE = DbGte,
    CE = DbTotalizer,
    ProofW = io::BufWriter<fs::File>,
    OInit = DefaultInitializer,
    BCG = fn(Assignment) -> Clause,
> where
    ProofW: io::Write,
{
    /// The solver kernel
    kernel: Kernel<O, ProofW, OInit, BCG>,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: Vec<ObjEncoding<PBE, CE>>,
    /// The current fence
    fence: Fence,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

impl<'learn, 'term, ProofW, OInit, BCG> super::Solve
    for LowerBounding<
        rustsat_cadical::CaDiCaL<'term, 'learn>,
        DbGte,
        DbTotalizer,
        ProofW,
        OInit,
        BCG,
    >
where
    BCG: Fn(Assignment) -> Clause,
    ProofW: io::Write + 'static,
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
    ) {
        use crate::ExtendedSolveStats;
        (
            self.kernel.stats,
            Some(self.oracle_stats()),
            Some(self.encoding_stats()),
        )
    }
}

impl<'learn, 'term, ProofW, OInit, BCG> super::Init
    for LowerBounding<
        rustsat_cadical::CaDiCaL<'learn, 'term>,
        DbGte,
        DbTotalizer,
        ProofW,
        OInit,
        BCG,
    >
where
    ProofW: io::Write + 'static,
    OInit: Initialize<rustsat_cadical::CaDiCaL<'learn, 'term>>,
    BCG: Fn(Assignment) -> Clause,
{
    type Oracle = rustsat_cadical::CaDiCaL<'learn, 'term>;
    type BlockClauseGen = BCG;

    /// Initializes a default solver with a configured oracle and options. The
    /// oracle should _not_ have any clauses loaded yet.
    fn new<Cls>(
        clauses: Cls,
        objs: Vec<Objective>,
        var_manager: VarManager,
        opts: KernelOptions,
        block_clause_gen: BCG,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = Clause>,
    {
        let kernel = Kernel::new(clauses, objs, var_manager, block_clause_gen, opts)?;
        Self::init(kernel)
    }
}

impl<'term, 'learn, ProofW, OInit, BCG> super::InitCert
    for LowerBounding<
        rustsat_cadical::CaDiCaL<'term, 'learn>,
        DbGte,
        DbTotalizer,
        ProofW,
        OInit,
        BCG,
    >
where
    OInit: Initialize<rustsat_cadical::CaDiCaL<'term, 'learn>>,
    ProofW: io::Write + 'static,
    BCG: Fn(Assignment) -> Clause,
{
    type ProofWriter = ProofW;

    /// Initializes a default solver with a configured oracle and options. The
    /// oracle should _not_ have any clauses loaded yet.
    fn new_cert<Cls>(
        clauses: Cls,
        objs: Vec<Objective>,
        var_manager: VarManager,
        opts: KernelOptions,
        proof: pigeons::Proof<Self::ProofWriter>,
        block_clause_gen: BCG,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = (Clause, pigeons::AbsConstraintId)>,
    {
        let kernel = Kernel::new_cert(clauses, objs, var_manager, block_clause_gen, proof, opts)?;
        Self::init(kernel)
    }
}

impl<O, PBE, CE, ProofW, OInit, BCG> ExtendedSolveStats
    for LowerBounding<O, PBE, CE, ProofW, OInit, BCG>
where
    O: SolveStats,
    ProofW: io::Write,
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

impl<O, PBE, CE, ProofW, OInit, BCG> LowerBounding<O, PBE, CE, ProofW, OInit, BCG>
where
    ProofW: io::Write + 'static,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
{
    /// Initializes the solver
    fn init(mut kernel: Kernel<O, ProofW, OInit, BCG>) -> anyhow::Result<Self> {
        // Initialize objective encodings
        let fence_data = Vec::with_capacity(kernel.objs.len());
        let obj_encs = kernel
            .objs
            .iter()
            .map(|obj| match obj {
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
            })
            .collect();
        Ok(Self {
            kernel,
            obj_encs,
            fence: Fence { data: fence_data },
            pareto_front: Default::default(),
        })
    }
}

impl<'learn, 'term, ProofW, OInit, BCG>
    LowerBounding<rustsat_cadical::CaDiCaL<'learn, 'term>, DbGte, DbTotalizer, ProofW, OInit, BCG>
where
    ProofW: io::Write + 'static,
    BCG: Fn(Assignment) -> Clause,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> MaybeTerminatedError {
        debug_assert_eq!(self.obj_encs.len(), self.kernel.stats.n_objs);
        self.kernel.log_routine_start("lower-bounding")?;
        // Initialize fence here if not yet done
        if self.fence.data.is_empty() {
            for enc in self.obj_encs.iter_mut() {
                if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.kernel.proof_stuff {
                    let proof: *mut _ = self.kernel.oracle.proof_tracer_mut(pt_handle).proof_mut();
                    let mut collector =
                        CadicalCertCollector::new(&mut self.kernel.oracle, pt_handle);
                    enc.encode_ub_change_cert(
                        enc.offset()..enc.offset() + 1,
                        &mut collector,
                        &mut self.kernel.var_manager,
                        unsafe { &mut *proof },
                    )?;
                } else {
                    enc.encode_ub_change(
                        enc.offset()..enc.offset() + 1,
                        &mut self.kernel.oracle,
                        &mut self.kernel.var_manager,
                    )?;
                }
                let assumps = enc.enforce_ub(enc.offset()).unwrap();
                self.fence.data.push((enc.offset(), assumps));
            }
        }
        loop {
            let assumps: Vec<_> = self.fence.assumps().collect();
            let res = self.kernel.solve_assumps(&assumps)?;
            match res {
                SolverResult::Sat => self.kernel.harvest(
                    &self.fence,
                    &mut self.obj_encs,
                    &[],
                    &mut self.pareto_front,
                )?,
                SolverResult::Unsat => {
                    let core = self.kernel.oracle.core()?;
                    if core.is_empty() {
                        self.kernel.log_routine_end()?;
                        return Done(());
                    }
                    #[cfg(debug_assertions)]
                    let old_fence = self.fence.bounds();
                    self.kernel
                        .update_fence(&mut self.fence, core, &mut self.obj_encs)?;
                    #[cfg(debug_assertions)]
                    {
                        let new_fence = self.fence.bounds();
                        let mut increased = false;
                        for idx in 0..old_fence.len() {
                            debug_assert!(old_fence[idx] <= new_fence[idx]);
                            if old_fence[idx] < new_fence[idx] {
                                increased = true;
                            }
                        }
                        if !increased {
                            panic!("fence has not increased");
                        }
                    }
                }
                SolverResult::Interrupted => panic!("should have errored before"),
            }
        }
    }
}

impl<'learn, 'term, PBE, CE, ProofW, OInit, BCG> CoreBoost
    for LowerBounding<rustsat_cadical::CaDiCaL<'learn, 'term>, PBE, CE, ProofW, OInit, BCG>
where
    ProofW: io::Write + 'static,
    (PBE, CE): MergeOllRef<PBE = PBE, CE = CE>,
    OInit: Initialize<rustsat_cadical::CaDiCaL<'learn, 'term>>,
{
    fn core_boost(&mut self, opts: CoreBoostingOptions) -> MaybeTerminatedError<bool> {
        ensure!(
            self.kernel.stats.n_solve_calls == 0,
            "cannot perform core boosting after solve has been called"
        );
        let Some(cb_res) = self.kernel.core_boost()? else {
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
        for (oidx, (reform, mut tot_db)) in cb_res.into_iter().enumerate() {
            if reset_dbs {
                debug_assert!(self.kernel.proof_stuff.is_none());
                tot_db.reset_vars();
            }
            if !matches!(self.kernel.objs[oidx], Objective::Constant { .. }) {
                if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.kernel.proof_stuff {
                    if !reform.reformulations.is_empty() {
                        // delete remaining reformulation constraints from proof
                        let proof = self.kernel.oracle.proof_tracer_mut(pt_handle).proof_mut();
                        #[cfg(feature = "verbose-proofs")]
                        proof.comment(&format_args!(
                            "deleting remaining reformulation constraints from OLL of objective {oidx}"
                        ))?;
                        proof.delete_ids::<Var, Clause, _, _>(
                            reform
                                .reformulations
                                .values()
                                .map(|re| ConstraintId::from(re.proof_id.unwrap())),
                            None,
                        )?;
                    }
                }

                self.obj_encs[oidx] = <(PBE, CE)>::merge(reform, tot_db, opts.rebase);
            }
            self.kernel.check_termination()?;
        }
        self.kernel.log_routine_end()?;
        Done(true)
    }
}

/// Data related to the current fence
pub(crate) struct Fence {
    /// The current bounds and enforcing literals
    pub data: Vec<(usize, Vec<Lit>)>,
}

impl Fence {
    pub fn assumps(&self) -> impl Iterator<Item = Lit> + '_ {
        self.data
            .iter()
            .flat_map(|(_, assumps)| assumps.iter().copied())
    }

    pub fn bounds(&self) -> Vec<usize> {
        self.data.iter().map(|&(b, _)| b).collect()
    }
}

impl<'learn, 'term, ProofW, OInit, BCG>
    Kernel<rustsat_cadical::CaDiCaL<'learn, 'term>, ProofW, OInit, BCG>
where
    ProofW: io::Write + 'static,
{
    pub fn update_fence(
        &mut self,
        fence: &mut Fence,
        core: Vec<Lit>,
        obj_encs: &mut [ObjEncoding<DbGte, DbTotalizer>],
    ) -> MaybeTerminatedError {
        let mut found = vec![false; fence.data.len()];
        'core: for clit in core {
            for (obj_idx, (bound, assumps)) in fence.data.iter_mut().enumerate() {
                if found[obj_idx] {
                    // the bound for this objective has already been increased
                    continue;
                }
                let mut matches = false;
                for alit in assumps.iter() {
                    if !*alit == clit {
                        matches = true;
                        break;
                    }
                }
                if matches {
                    found[obj_idx] = true;
                    // update bound
                    let enc = &mut obj_encs[obj_idx];
                    *bound = enc.next_higher(*bound);
                    self.extend_encoding(enc, *bound..*bound + 1)?;
                    *assumps = enc.enforce_ub(*bound).unwrap();
                    continue 'core;
                }
            }
        }
        if let Some(logger) = &mut self.logger {
            logger.log_fence(&fence.bounds())?
        }
        Done(())
    }
}

impl<'term, 'learn, ProofW, OInit, BCG>
    Kernel<rustsat_cadical::CaDiCaL<'term, 'learn>, ProofW, OInit, BCG>
where
    ProofW: io::Write + 'static,
    BCG: Fn(Assignment) -> Clause,
{
    /// Runs the P-Minimal algorithm within the fence to harvest solutions
    pub fn harvest<Col>(
        &mut self,
        fence: &Fence,
        obj_encs: &mut [ObjEncoding<DbGte, DbTotalizer>],
        base_assumps: &[Lit],
        collector: &mut Col,
    ) -> MaybeTerminatedError
    where
        Col: Extend<NonDomPoint>,
    {
        debug_assert_eq!(obj_encs.len(), self.stats.n_objs);
        self.log_routine_start("harvest")?;
        let mut assumps = Vec::from(base_assumps);
        loop {
            assumps.drain(base_assumps.len()..);
            // Find minimization starting point
            assumps.extend(fence.assumps());
            let res = self.solve_assumps(&assumps)?;
            if SolverResult::Unsat == res {
                self.log_routine_end()?;
                return Done(());
            }
            self.check_termination()?;

            // Minimize solution
            let (costs, solution) = self.get_solution_and_internal_costs(
                self.opts
                    .heuristic_improvements
                    .solution_tightening
                    .wanted(Phase::OuterLoop),
            )?;
            self.log_candidate(&costs, Phase::OuterLoop)?;
            self.check_termination()?;
            self.phase_solution(solution.clone())?;
            let (costs, solution, block_switch) =
                self.p_minimization(costs, solution, base_assumps, obj_encs)?;

            let assumps: Vec<_> = self.enforce_dominating(&costs, obj_encs)?.collect();
            self.yield_solutions(costs.clone(), &assumps, solution.clone(), collector)?;

            // Block last Pareto point, if temporarily blocked
            if let Some((block_lit, ids)) = block_switch {
                if let Some(proof_stuff) = &mut self.proof_stuff {
                    use pigeons::{ConstraintId, Derivation, ProofGoal, ProofGoalId};
                    use rustsat::encodings::CollectCertClauses;

                    let (reified_cut, reified_assump_ids) = ids.unwrap();
                    let id = proofs::certify_pmin_cut(
                        obj_encs,
                        &self.objs,
                        &costs,
                        &solution,
                        self.var_manager.max_enc_var(),
                        proof_stuff,
                        &mut self.oracle,
                    )?;
                    let proof = self
                        .oracle
                        .proof_tracer_mut(&proof_stuff.pt_handle)
                        .proof_mut();
                    let hints = [ConstraintId::last(2), ConstraintId::last(1), id.into()]
                        .into_iter()
                        .chain(reified_assump_ids.iter().map(|id| ConstraintId::from(*id)));
                    let unit = clause![block_lit];
                    let unit_id = proof.redundant(
                        &unit,
                        [],
                        [ProofGoal::new(
                            ProofGoalId::from(ConstraintId::from(reified_cut)),
                            [Derivation::Rup(clause![], hints.collect())],
                        )],
                    )?;
                    cadical_veripb_tracer::CadicalCertCollector::new(
                        &mut self.oracle,
                        &proof_stuff.pt_handle,
                    )
                    .add_cert_clause(unit, unit_id)?;
                } else {
                    self.oracle.add_unit(block_lit)?;
                }
            }
        }
    }
}
