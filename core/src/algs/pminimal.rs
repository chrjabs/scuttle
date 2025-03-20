//! # $P$-Minimal Model Enumeration for Multi-Objective Optimization
//!
//! This module implements $P$-minimal model enumeration as an algorithm for
//! solving multi-objective optimization problems expressed as boolean logic.
//! Instead of using the order encoding as in \[1\], any cardinality (for
//! unweighted objectives) or pseudo-boolean encoding from
//! [RustSAT](https://github.com/chrjabs/rustsat) can be used. The actual
//! enumeration algorithm follows \[2\].
//!
//! ## References
//!
//! - \[1\] Takehide Soh and Mutsunori Banbara and Naoyuki Tamura and Daniel Le
//!     Berre: _Solving Multiobjective Discrete Optimization Problems with
//!     Propositional Minimal Model Generation_, CP 2017.
//! - \[2\] Miyuki Koshimura and Hidetomo Nabeshima and Hiroshi Fujita and Ryuzo
//!     Hasegawa: _Minimal Model Generation with Respect to an Atom Set_, FTP
//!     2009.
use std::{fs, io};

use cadical_veripb_tracer::CadicalCertCollector;
use pigeons::{AbsConstraintId, ConstraintId};
use rustsat::{
    clause,
    encodings::{
        self, atomics,
        card::{self, DbTotalizer},
        pb::{self, DbGte},
    },
    instances::ManageVars,
    solvers::{
        DefaultInitializer, Initialize, Solve, SolveIncremental, SolveStats, SolverResult,
        SolverStats,
    },
    types::{Assignment, Clause, Lit, Var},
};
use scuttle_proc::{oracle_bounds, KernelFunctions};

use crate::{
    options::{AfterCbOptions, CoreBoostingOptions, EnumOptions},
    termination::ensure,
    types::{ParetoFront, VarManager},
    EncodingStats, ExtendedSolveStats, KernelFunctions, KernelOptions, Limits,
    MaybeTerminatedError::{self, Done},
    Phase,
};

use super::{coreboosting::MergeOllRef, proofs, CoreBoost, Kernel, ObjEncoding, Objective};

/// The $P$-minimal algorithm type
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
pub struct PMinimal<
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
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

impl<'learn, 'term, ProofW, OInit, BCG> super::Solve
    for PMinimal<rustsat_cadical::CaDiCaL<'term, 'learn>, DbGte, DbTotalizer, ProofW, OInit, BCG>
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

#[oracle_bounds]
impl<O, PBE, CE, ProofW, OInit, BCG> super::Init for PMinimal<O, PBE, CE, ProofW, OInit, BCG>
where
    O: SolveIncremental,
    ProofW: io::Write,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    OInit: Initialize<O>,
    BCG: Fn(Assignment) -> Clause,
{
    type Oracle = O;
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
        Ok(Self::init(kernel))
    }
}

impl<'term, 'learn, PBE, CE, ProofW, OInit, BCG> super::InitCert
    for PMinimal<rustsat_cadical::CaDiCaL<'term, 'learn>, PBE, CE, ProofW, OInit, BCG>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
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
        Ok(Self::init(kernel))
    }
}

impl<O, PBE, CE, ProofW, OInit, BCG> ExtendedSolveStats for PMinimal<O, PBE, CE, ProofW, OInit, BCG>
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

impl<O, PBE, CE, ProofW, OInit, BCG> PMinimal<O, PBE, CE, ProofW, OInit, BCG>
where
    ProofW: io::Write,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
{
    /// Initializes the solver
    fn init(mut kernel: Kernel<O, ProofW, OInit, BCG>) -> Self {
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
        Self {
            kernel,
            obj_encs,
            pareto_front: Default::default(),
        }
    }
}

impl<'learn, 'term, ProofW, OInit, BCG>
    PMinimal<rustsat_cadical::CaDiCaL<'learn, 'term>, DbGte, DbTotalizer, ProofW, OInit, BCG>
where
    BCG: Fn(Assignment) -> Clause,
    ProofW: io::Write + 'static,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> MaybeTerminatedError {
        debug_assert_eq!(self.obj_encs.len(), self.kernel.stats.n_objs);
        self.kernel.log_routine_start("p-minimal")?;
        loop {
            // Find minimization starting point
            let res = self.kernel.solve()?;
            if SolverResult::Unsat == res {
                self.kernel.log_routine_end()?;
                return Done(());
            }
            self.kernel.check_termination()?;

            // Minimize solution
            let (costs, solution) = self.kernel.get_solution_and_internal_costs(
                self.kernel
                    .opts
                    .heuristic_improvements
                    .solution_tightening
                    .wanted(Phase::OuterLoop),
            )?;
            self.kernel.log_candidate(&costs, Phase::OuterLoop)?;
            self.kernel.check_termination()?;
            self.kernel.phase_solution(solution.clone())?;
            let (costs, solution, block_switch) =
                self.kernel
                    .p_minimization(costs, solution, &[], &mut self.obj_encs)?;

            let assumps: Vec<_> = self
                .kernel
                .enforce_dominating(&costs, &mut self.obj_encs)?
                .collect();
            self.kernel.yield_solutions(
                costs.clone(),
                &assumps,
                solution.clone(),
                &mut self.pareto_front,
            )?;

            // Block last Pareto point, if temporarily blocked
            if let Some((block_lit, ids)) = block_switch {
                if let Some(proof_stuff) = &mut self.kernel.proof_stuff {
                    use pigeons::{ConstraintId, Derivation, ProofGoal, ProofGoalId};
                    use rustsat::encodings::CollectCertClauses;

                    let (reified_cut, reified_assump_ids) = ids.unwrap();
                    let id = proofs::certify_pmin_cut(
                        &self.obj_encs,
                        &self.kernel.objs,
                        &costs,
                        &solution,
                        self.kernel.var_manager.max_enc_var(),
                        proof_stuff,
                        &mut self.kernel.oracle,
                    )?;
                    let proof = self
                        .kernel
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
                        &mut self.kernel.oracle,
                        &proof_stuff.pt_handle,
                    )
                    .add_cert_clause(unit, unit_id)?;
                } else {
                    self.kernel.oracle.add_unit(block_lit)?;
                }
            }
        }
    }
}

impl<'learn, 'term, PBE, CE, ProofW, OInit, BCG> CoreBoost
    for PMinimal<rustsat_cadical::CaDiCaL<'learn, 'term>, PBE, CE, ProofW, OInit, BCG>
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

impl<'term, 'learn, ProofW, OInit, BCG>
    Kernel<rustsat_cadical::CaDiCaL<'term, 'learn>, ProofW, OInit, BCG>
where
    ProofW: io::Write + 'static,
{
    /// Executes P-minimization from a cost and solution starting point
    pub fn p_minimization(
        &mut self,
        mut costs: Vec<usize>,
        mut solution: Assignment,
        base_assumps: &[Lit],
        obj_encs: &mut [ObjEncoding<DbGte, DbTotalizer>],
    ) -> MaybeTerminatedError<(
        Vec<usize>,
        Assignment,
        Option<(Lit, Option<(AbsConstraintId, Vec<AbsConstraintId>)>)>,
    )> {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        self.log_routine_start("p minimization")?;
        let mut block_switch: Option<(Lit, Option<(AbsConstraintId, Vec<AbsConstraintId>)>)> = None;
        let mut assumps = Vec::from(base_assumps);
        #[cfg(feature = "coarse-convergence")]
        let mut coarse = true;
        loop {
            #[cfg(feature = "coarse-convergence")]
            let bound_costs: Vec<_> = costs
                .iter()
                .enumerate()
                .map(|(_oidx, &c)| {
                    if coarse {
                        return obj_encs[_oidx].coarse_ub(c);
                    }
                    c
                })
                .collect();
            assumps.drain(base_assumps.len()..);
            // Block solutions dominated by the current one
            if self.opts.enumeration == EnumOptions::NoEnum {
                // Block permanently since no enumeration at Pareto point
                let (block_clause, reification_ids) =
                    self.dominated_block_clause(&costs, obj_encs)?;
                if let Some(proof_stuff) = &mut self.proof_stuff {
                    use rustsat::encodings::CollectCertClauses;

                    // this adds the "ideal cut"
                    let cut_id = proofs::certify_pmin_cut(
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
                    // since there might be reifications of multiple assumptions per one encoding
                    // involved, the actual clause might differ and is added as rup here
                    let clause_id = proof.reverse_unit_prop(
                        &block_clause,
                        reification_ids
                            .into_iter()
                            .chain([cut_id])
                            .map(ConstraintId::from),
                    )?;
                    let mut collector = cadical_veripb_tracer::CadicalCertCollector::new(
                        &mut self.oracle,
                        &proof_stuff.pt_handle,
                    );
                    collector.add_cert_clause(block_clause, clause_id)?;
                } else {
                    self.oracle.add_clause(block_clause)?;
                }
            } else {
                // Permanently block last cadidate
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
                            .chain(reified_assump_ids.into_iter().map(ConstraintId::from));
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
                // Temporarily block to allow for enumeration at Pareto point
                let block_info = self.tmp_block_dominated(&costs, obj_encs)?;
                let blit = block_info.0;
                block_switch = Some(block_info);
                assumps.push(blit);
            }
            // Force next solution to dominate the current one
            #[cfg(not(feature = "coarse-convergence"))]
            assumps.extend(self.enforce_dominating(&costs, obj_encs)?);
            #[cfg(feature = "coarse-convergence")]
            assumps.extend(self.enforce_dominating_cert(&bound_costs, obj_encs)?);

            // Check if dominating solution exists
            let res = self.solve_assumps(&assumps)?;
            if res == SolverResult::Unsat {
                #[cfg(feature = "coarse-convergence")]
                if bound_costs != costs {
                    // Switch to fine convergence
                    coarse = false;
                    continue;
                }
                self.log_routine_end()?;
                // Termination criteria, return last solution and costs
                return Done((costs, solution, block_switch));
            }
            self.check_termination()?;

            (costs, solution) = self.get_solution_and_internal_costs(
                self.opts
                    .heuristic_improvements
                    .solution_tightening
                    .wanted(Phase::Minimization),
            )?;
            self.log_candidate(&costs, Phase::Minimization)?;
            self.check_termination()?;
            self.phase_solution(solution.clone())?;
        }
    }

    /// Gets assumptions to enforce that the next solution dominates the given
    /// cost point.
    pub fn enforce_dominating<'a>(
        &'a mut self,
        costs: &'a [usize],
        obj_encs: &'a mut [ObjEncoding<DbGte, DbTotalizer>],
    ) -> anyhow::Result<impl Iterator<Item = Lit> + 'a> {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.proof_stuff {
            let proof: *mut _ = self.oracle.proof_tracer_mut(pt_handle).proof_mut();
            #[cfg(feature = "verbose-proofs")]
            {
                use itertools::Itertools;
                let proof = unsafe { &mut *proof };
                proof.comment(&format_args!(
                    "building assumptions to dominate [{}]",
                    costs.iter().format(", ")
                ))?;
            }
            let mut collector = CadicalCertCollector::new(&mut self.oracle, pt_handle);
            for (idx, &cst) in costs.iter().enumerate() {
                let enc = &mut obj_encs[idx];
                enc.encode_ub_change_cert(
                    cst..cst + 1,
                    &mut collector,
                    &mut self.var_manager,
                    unsafe { &mut *proof },
                )?;
            }
        } else {
            for (idx, &cst) in costs.iter().enumerate() {
                let enc = &mut obj_encs[idx];
                enc.encode_ub_change(cst..cst + 1, &mut self.oracle, &mut self.var_manager)?;
            }
        }
        Ok(costs.iter().enumerate().flat_map(|(idx, &cst)| {
            let enc = &mut obj_encs[idx];
            enc.enforce_ub(cst).unwrap().into_iter()
        }))
    }

    /// Gets a clause blocking solutions (weakly) dominated by the given cost point,
    /// given objective encodings.
    pub fn dominated_block_clause(
        &mut self,
        costs: &[usize],
        obj_encs: &mut [ObjEncoding<DbGte, DbTotalizer>],
    ) -> anyhow::Result<(Clause, Vec<AbsConstraintId>)> {
        debug_assert_eq!(costs.len(), obj_encs.len());
        let mut reification_ids = Vec::new();
        let mut clause = Clause::default();
        for (idx, &cst) in costs.iter().enumerate() {
            // Don't block
            if cst <= obj_encs[idx].offset() {
                continue;
            }
            let enc = &mut obj_encs[idx];
            if matches!(enc, ObjEncoding::Constant) {
                continue;
            }
            // Encode and add to solver
            self.extend_encoding(enc, cst - 1..cst)?;
            let assumps = enc.enforce_ub(cst - 1)?;
            if assumps.len() == 1 {
                clause.add(assumps[0]);
            } else {
                debug_assert!(!assumps.is_empty());
                let and_lit = self.var_manager.new_var().pos_lit();
                if let Some(proof_stuff) = &mut self.proof_stuff {
                    let only_if_def = proofs::certify_assump_reification(
                        &mut self.oracle,
                        proof_stuff,
                        &self.objs[idx],
                        enc,
                        cst,
                        and_lit,
                        &assumps,
                    )?;
                    reification_ids.push(only_if_def);
                } else {
                    for cl in atomics::lit_impl_cube(and_lit, &assumps) {
                        self.oracle.add_clause(cl)?;
                    }
                }
                clause.add(and_lit)
            }
        }
        Ok((clause, reification_ids))
    }

    /// Temporarily blocks solutions dominated by the given cost point. Returns
    /// and assumption that needs to be enforced in order for the blocking to be
    /// enforced.
    pub fn tmp_block_dominated(
        &mut self,
        costs: &[usize],
        obj_encs: &mut [ObjEncoding<DbGte, DbTotalizer>],
    ) -> anyhow::Result<(Lit, Option<(AbsConstraintId, Vec<AbsConstraintId>)>)> {
        use pigeons::VarLike;

        debug_assert_eq!(costs.len(), self.stats.n_objs);
        let (mut clause, reification_ids) = self.dominated_block_clause(costs, obj_encs)?;
        let block_lit = self.var_manager.new_var().pos_lit();
        clause.add(block_lit);
        self.oracle.add_clause_ref(&clause).unwrap();
        if let Some(proofs::ProofStuff { pt_handle, .. }) = &self.proof_stuff {
            let proof = self.oracle.proof_tracer_mut(pt_handle).proof_mut();
            let id = proof.redundant(&clause, [block_lit.var().substitute_fixed(true)], None)?;
            Ok((!block_lit, Some((id, reification_ids))))
        } else {
            Ok((!block_lit, None))
        }
    }
}
