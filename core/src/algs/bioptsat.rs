//! # BiOptSat Algorithm for Bi-Objective Optimization
//!
//! ## References
//!
//! - \[1\] Christoph Jabs and Jeremias Berg and Andreas Niskanen and Matti
//!     Järvisalo: _MaxSAT-Based Bi-Objective Boolean Optimization_, SAT 2022.

use std::{fs, io};

use cadical_veripb_tracer::CadicalCertCollector;
use pigeons::{ConstraintId, OperationLike, OperationSequence, VarLike};
use rustsat::{
    clause,
    encodings::{
        self, atomics,
        card::{self, DbTotalizer},
        pb::{self, DbGte},
        CollectCertClauses,
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
    options::{AfterCbOptions, CoreBoostingOptions},
    termination::ensure,
    types::{NonDomPoint, ParetoFront, VarManager},
    EncodingStats, ExtendedSolveStats, KernelFunctions, KernelOptions, Limits,
    MaybeTerminatedError::{self, Done},
};

use super::{coreboosting::MergeOllRef, proofs, CoreBoost, Kernel, ObjEncoding, Objective};

/// The BiOptSat algorithm type
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
pub struct BiOptSat<
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
    obj_encs: [ObjEncoding<PBE, CE>; 2],
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

impl<'learn, 'term, ProofW, OInit, BCG> super::Solve
    for BiOptSat<rustsat_cadical::CaDiCaL<'term, 'learn>, DbGte, DbTotalizer, ProofW, OInit, BCG>
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
impl<O, PBE, CE, ProofW, OInit, BCG> super::Init for BiOptSat<O, PBE, CE, ProofW, OInit, BCG>
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
    for BiOptSat<rustsat_cadical::CaDiCaL<'term, 'learn>, PBE, CE, ProofW, OInit, BCG>
where
    ProofW: io::Write,
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

impl<O, PBE, CE, ProofW, OInit, BCG> ExtendedSolveStats for BiOptSat<O, PBE, CE, ProofW, OInit, BCG>
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
            .zip(&self.obj_encs)
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

impl<O, PBE, CE, ProofW, OInit, BCG> BiOptSat<O, PBE, CE, ProofW, OInit, BCG>
where
    O: SolveIncremental,
    ProofW: io::Write,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
{
    /// Initializes the solver
    fn init(mut kernel: Kernel<O, ProofW, OInit, BCG>) -> Self {
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
            obj_encs: [inc_enc, dec_enc],
            pareto_front: Default::default(),
        }
    }
}

impl<'learn, 'term, ProofW, OInit, BCG>
    BiOptSat<rustsat_cadical::CaDiCaL<'learn, 'term>, DbGte, DbTotalizer, ProofW, OInit, BCG>
where
    ProofW: io::Write + 'static,
    BCG: Fn(Assignment) -> Clause,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> MaybeTerminatedError {
        self.kernel.bioptsat(
            (0, 1),
            &mut self.obj_encs,
            &[],
            None,
            (None, None),
            |_| None,
            &mut self.pareto_front,
        )
    }
}

impl<'learn, 'term, PBE, CE, ProofW, OInit, BCG> CoreBoost
    for BiOptSat<rustsat_cadical::CaDiCaL<'learn, 'term>, PBE, CE, ProofW, OInit, BCG>
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
                let mut encs = self.kernel.inprocess(techs, cb_res)?;
                self.obj_encs[1] = encs.pop().unwrap();
                self.obj_encs[0] = encs.pop().unwrap();
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

                if oidx == 0 {
                    self.obj_encs[0] = <(PBE, CE)>::merge(reform, tot_db, opts.rebase);
                } else {
                    self.obj_encs[1] = <(PBE, CE)>::merge(reform, tot_db, opts.rebase);
                }
            }
            self.kernel.check_termination()?;
        }
        self.kernel.log_routine_end()?;
        Done(true)
    }
}

impl<'learn, 'term, ProofW, OInit, BCG>
    Kernel<rustsat_cadical::CaDiCaL<'learn, 'term>, ProofW, OInit, BCG>
where
    ProofW: io::Write + 'static,
    BCG: Fn(Assignment) -> Clause,
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
    pub fn bioptsat<Lookup, Col>(
        &mut self,
        (inc_obj, dec_obj): (usize, usize),
        encodings: &mut [ObjEncoding<DbGte, DbTotalizer>],
        base_assumps: &[Lit],
        starting_point: Option<(usize, Assignment)>,
        (inc_lb, dec_lb): (Option<usize>, Option<usize>),
        lookup: Lookup,
        collector: &mut Col,
    ) -> MaybeTerminatedError
    where
        Lookup: Fn(usize) -> Option<usize>,
        Col: Extend<NonDomPoint>,
    {
        self.log_routine_start("bioptsat")?;

        debug_assert_eq!(encodings.len(), 2);

        let mut inc_lb = inc_lb.unwrap_or(encodings[0].offset());
        let dec_lb = dec_lb.unwrap_or(encodings[1].offset());

        let mut assumps = Vec::from(base_assumps);
        let (mut inc_cost, mut sol) = if let Some(bound) = starting_point {
            bound
        } else {
            let res = self.solve_assumps(&assumps)?;
            if res == SolverResult::Unsat {
                return Done(());
            }
            let mut sol = self.oracle.solution(self.var_manager.max_var().unwrap())?;
            let cost = self.get_cost_with_heuristic_improvements(inc_obj, &mut sol, true)?;
            (cost, sol)
        };
        let mut dec_cost;
        let mut last_dec_lb_id = None;
        let mut last_cut_id = None;
        loop {
            // minimize inc_obj
            let Some((new_inc_cost, new_sol, inc_lb_id)) = self.linsu(
                inc_obj,
                &mut encodings[0],
                base_assumps,
                Some((inc_cost, Some(sol))),
                Some(inc_lb),
            )?
            else {
                // no solutions
                self.log_routine_end()?;
                return Done(());
            };
            (inc_cost, sol) = (new_inc_cost, new_sol);

            dec_cost = self.get_cost_with_heuristic_improvements(dec_obj, &mut sol, false)?;
            let mut dec_lb_id = None;
            if let Some(found) = lookup(inc_cost) {
                // lookup not supported with proofs
                debug_assert!(self.proof_stuff.is_none());
                dec_cost = found;
            } else {
                // bound inc_obj
                self.extend_encoding(&mut encodings[0], inc_cost..inc_cost + 1)?;
                assumps.drain(base_assumps.len()..);
                assumps.extend(encodings[0].enforce_ub(inc_cost).unwrap());
                // minimize dec_obj
                (dec_cost, sol, dec_lb_id) = self
                    .linsu_yield(
                        dec_obj,
                        &mut encodings[1],
                        &assumps,
                        Some((dec_cost, Some(sol))),
                        Some(dec_lb),
                        collector,
                    )?
                    .unwrap();
            };
            // termination condition: can't decrease decreasing objective further
            if dec_cost <= dec_lb {
                if let Some(proof_stuff) = &mut self.proof_stuff {
                    // don't support base assumptions for proof logging for now
                    debug_assert!(base_assumps.is_empty());
                    // get p-min cut for current solution in proof
                    let pmin_cut_id = proofs::certify_pmin_cut(
                        encodings,
                        &self.objs,
                        &[inc_cost, dec_cost],
                        &sol,
                        self.var_manager.max_enc_var(),
                        proof_stuff,
                        &mut self.oracle,
                    )?;
                    let proof = self
                        .oracle
                        .proof_tracer_mut(&proof_stuff.pt_handle)
                        .proof_mut();
                    // derive cut that will be added
                    let cut_id = if inc_cost <= encodings[0].offset() {
                        pmin_cut_id
                    } else {
                        // global lower bound on increasing objective in proof
                        let inc_lb_id = if inc_cost == inc_lb {
                            // manually derive lower bound from last cut
                            let lb_id = proof.operations::<Var>(
                                &(OperationSequence::from(last_cut_id.unwrap())
                                    + last_dec_lb_id.unwrap()),
                            )?;
                            #[cfg(feature = "verbose-proofs")]
                            {
                                if encodings[0].is_buffer_empty() {
                                    let (olit, _) = encodings[0].output_proof_details(inc_cost);
                                    proof.equals(
                                        &pigeons::Axiom::from(olit),
                                        Some(pigeons::ConstraintId::from(lb_id)),
                                    )?;
                                }
                                // otherwise, this should equal the proof-only variable
                            }
                            lb_id
                        } else {
                            inc_lb_id.unwrap()
                        };
                        proof.operations::<Var>(
                            &(OperationSequence::from(inc_lb_id) + pmin_cut_id),
                        )?
                    };
                    #[cfg(feature = "verbose-proofs")]
                    {
                        proof.equals(
                            &rustsat::clause![],
                            Some(pigeons::ConstraintId::from(cut_id)),
                        )?;
                    }
                    proof.update_default_conclusion::<Var>(
                        pigeons::OutputGuarantee::None,
                        &pigeons::Conclusion::Unsat(Some(ConstraintId::from(cut_id))),
                    );
                }
                break;
            }
            // skip to next non-dom
            self.extend_encoding(&mut encodings[1], dec_cost - 1..dec_cost)?;

            if let Some(proof_stuff) = &mut self.proof_stuff {
                // don't support base assumptions for proof logging for now
                debug_assert!(base_assumps.is_empty());
                // get p-min cut for current solution in proof
                let pmin_cut_id = proofs::certify_pmin_cut(
                    encodings,
                    &self.objs,
                    &[inc_cost, dec_cost],
                    &sol,
                    self.var_manager.max_enc_var(),
                    proof_stuff,
                    &mut self.oracle,
                )?;

                // while we know the assumptions, simplify dec_lb_id
                let (first_olit, first_sems) =
                    encodings[0].output_proof_details(encodings[0].next_higher(inc_cost));
                dec_lb_id = if encodings[0].is_buffer_empty() {
                    if assumps.len() <= 1 {
                        debug_assert!(assumps.len() != 1 || assumps[0] == !first_olit);
                        // already minimal
                        dec_lb_id
                    } else {
                        let proof = self
                            .oracle
                            .proof_tracer_mut(&proof_stuff.pt_handle)
                            .proof_mut();

                        let start = if assumps[0] == !first_olit { 1 } else { 0 };
                        let mut implications = Vec::with_capacity(assumps.len());
                        let mut val = encodings[0].next_higher(encodings[0].next_higher(inc_cost));
                        for &a in &assumps[start..] {
                            let (olit, sems) = encodings[0].output_proof_details(val);
                            debug_assert_eq!(a, !olit);
                            let implication = proof.operations::<Var>(
                                &((OperationSequence::from(first_sems.if_def.unwrap())
                                    + sems.only_if_def.unwrap())
                                    / (val - inc_cost + 2))
                                    .saturate(),
                            )?;
                            #[cfg(feature = "verbose-proofs")]
                            proof.equals(
                                &rustsat::clause![!olit, first_olit],
                                Some(ConstraintId::from(implication)),
                            )?;
                            implications.push(implication);
                            val = encodings[0].next_higher(val);
                        }
                        debug_assert!(!implications.is_empty());
                        // rewrite the derived bound
                        let shortened = proof.operations::<Var>(
                            &(implications
                                .iter()
                                .fold(OperationSequence::from(dec_lb_id.unwrap()), |s, imp| {
                                    s + *imp
                                })
                                .saturate()),
                        )?;
                        // delete implications
                        proof.delete_ids::<Var, Clause, _, _>(
                            implications.into_iter().map(ConstraintId::from),
                            None,
                        )?;
                        Some(shortened)
                    }
                } else {
                    let (ideal_lit, def_1, _) = proofs::get_obj_bound_constraint(
                        dec_cost,
                        &self.objs[1],
                        proof_stuff,
                        &mut self.oracle,
                    )?;
                    let proof = self
                        .oracle
                        .proof_tracer_mut(&proof_stuff.pt_handle)
                        .proof_mut();
                    let mut implications = Vec::with_capacity(assumps.len());
                    let mut val = inc_cost + 1;
                    for &a in &assumps {
                        let (olit, sems) = encodings[0].output_proof_details(val);
                        let clause = proofs::LbConstraint::clause([
                            !proofs::AnyVar::Solver(a.var()).axiom(a.is_neg()),
                            ideal_lit,
                        ]);
                        let implication = if a.var() < olit.var() {
                            debug_assert!(a.var() <= self.var_manager.max_enc_var());
                            // this is an input literal with weight higher than the bound
                            proof.reverse_unit_prop(&clause, [ConstraintId::from(def_1)])?
                        } else {
                            // this is an output literal of a subtree
                            debug_assert_eq!(!olit, a);
                            let tmp = proof.operations::<Var>(
                                &(OperationSequence::from(def_1) + sems.only_if_def.unwrap()),
                            )?;
                            let id = proof.reverse_unit_prop(&clause, [ConstraintId::from(tmp)])?;
                            proof
                                .delete_ids::<Var, Clause, _, _>([ConstraintId::from(tmp)], None)?;
                            val = encodings[1].next_higher(val);
                            id
                        };
                        implications.push(implication);
                    }
                    debug_assert!(!implications.is_empty());
                    // rewrite the derived bound
                    let shortened = proof.operations::<Var>(
                        &(implications
                            .iter()
                            .fold(OperationSequence::from(dec_lb_id.unwrap()), |s, imp| {
                                s + *imp
                            })
                            .saturate()),
                    )?;
                    // delete implications
                    proof.delete_ids::<Var, Clause, _, _>(
                        implications.into_iter().map(ConstraintId::from),
                        None,
                    )?;
                    Some(shortened)
                };

                let proof = self
                    .oracle
                    .proof_tracer_mut(&proof_stuff.pt_handle)
                    .proof_mut();

                // derive cut that will be added
                let cut_id = if inc_cost <= encodings[0].offset() {
                    pmin_cut_id
                } else {
                    // global lower bound on increasing objective in proof
                    let inc_lb_id = if inc_cost == inc_lb {
                        // manually derive lower bound from last cut
                        let lb_id = proof.operations::<Var>(
                            &(OperationSequence::from(last_cut_id.unwrap())
                                + last_dec_lb_id.unwrap()),
                        )?;
                        #[cfg(feature = "verbose-proofs")]
                        {
                            if encodings[0].is_buffer_empty() {
                                let (olit, _) = encodings[0].output_proof_details(inc_cost);
                                proof.comment(&"here")?;
                                proof.equals(
                                    &pigeons::Axiom::from(olit),
                                    Some(pigeons::ConstraintId::from(lb_id)),
                                )?;
                            }
                        }
                        lb_id
                    } else {
                        inc_lb_id.unwrap()
                    };
                    proof.operations::<Var>(&(OperationSequence::from(inc_lb_id) + pmin_cut_id))?
                };
                #[cfg(feature = "verbose-proofs")]
                {
                    if encodings[1].is_buffer_empty() {
                        let (olit, _) = encodings[1].output_proof_details(dec_cost);
                        proof.equals(
                            &pigeons::Axiom::from(!olit),
                            Some(pigeons::ConstraintId::from(cut_id)),
                        )?;
                    }
                }
                last_cut_id = Some(cut_id);

                // add cut
                let assumps = encodings[1].enforce_ub(dec_cost - 1)?;

                if encodings[1].is_buffer_empty() {
                    let (first_olit, first_sems) = encodings[1].output_proof_details(dec_cost);
                    debug_assert_eq!(!first_olit, assumps[0]);
                    CadicalCertCollector::new(&mut self.oracle, &proof_stuff.pt_handle)
                        .add_cert_clause(clause![assumps[0]], cut_id)?;

                    let mut val = dec_cost;
                    for &a in &assumps[1..] {
                        val = encodings[1].next_higher(val);
                        // first convince veripb that `olit -> first_olit`
                        let (olit, sems) = encodings[1].output_proof_details(val);
                        debug_assert_eq!(!olit, a);
                        let proof = self
                            .oracle
                            .proof_tracer_mut(&proof_stuff.pt_handle)
                            .proof_mut();
                        let implication = proof.operations::<Var>(
                            &((OperationSequence::from(first_sems.if_def.unwrap())
                                + sems.only_if_def.unwrap())
                                / (val - dec_cost + 1))
                                .saturate(),
                        )?;
                        #[cfg(feature = "verbose-proofs")]
                        proof.equals(
                            &clause![!olit, first_olit],
                            Some(pigeons::ConstraintId::from(implication)),
                        )?;
                        let id = proof
                            .operations::<Var>(&(OperationSequence::from(cut_id) + implication))?;
                        CadicalCertCollector::new(&mut self.oracle, &proof_stuff.pt_handle)
                            .add_cert_clause(clause![a], id)?;
                        self.oracle
                            .proof_tracer_mut(&proof_stuff.pt_handle)
                            .proof_mut()
                            .delete_ids::<Var, Clause, _, _>(
                                [ConstraintId::from(implication)],
                                None,
                            )?;
                    }
                } else {
                    let (ideal_lit, def_1, _) = proofs::get_obj_bound_constraint(
                        dec_cost,
                        &self.objs[1],
                        proof_stuff,
                        &mut self.oracle,
                    )?;
                    let mut val = dec_cost;
                    for &a in &assumps {
                        let proof = self
                            .oracle
                            .proof_tracer_mut(&proof_stuff.pt_handle)
                            .proof_mut();
                        let clause = proofs::LbConstraint::clause([
                            ideal_lit,
                            proofs::AnyVar::Solver(a.var()).axiom(a.is_neg()),
                        ]);
                        let (olit, sems) = encodings[1].output_proof_details(val);
                        let implication = if a.var() < olit.var() {
                            debug_assert!(a.var() <= self.var_manager.max_enc_var());
                            // this is an input literal with weight higher than the bound
                            proof.reverse_unit_prop(&clause, [ConstraintId::from(def_1)])?
                        } else {
                            // this is an output literal of a subtree
                            debug_assert_eq!(!olit, a);
                            let tmp = proof.operations::<Var>(
                                &(OperationSequence::from(def_1) + sems.only_if_def.unwrap()),
                            )?;
                            let id = proof.reverse_unit_prop(&clause, [ConstraintId::from(tmp)])?;
                            proof
                                .delete_ids::<Var, Clause, _, _>([ConstraintId::from(tmp)], None)?;
                            val = encodings[1].next_higher(val);
                            id
                        };
                        let id = proof
                            .operations::<Var>(&(OperationSequence::from(cut_id) + implication))?;
                        CadicalCertCollector::new(&mut self.oracle, &proof_stuff.pt_handle)
                            .add_cert_clause(clause![a], id)?;
                        self.oracle
                            .proof_tracer_mut(&proof_stuff.pt_handle)
                            .proof_mut()
                            .delete_ids::<Var, Clause, _, _>(
                                [ConstraintId::from(implication)],
                                None,
                            )?;
                    }
                }
            } else {
                for cl in
                    atomics::cube_impl_cube(base_assumps, &encodings[1].enforce_ub(dec_cost - 1)?)
                {
                    self.oracle.add_clause(cl)?;
                }
            }
            inc_lb = inc_cost + 1;
            last_dec_lb_id = dec_lb_id;

            (sol, inc_cost) = match self.solve_assumps(base_assumps)? {
                SolverResult::Sat => {
                    let mut sol = self.oracle.solution(self.var_manager.max_var().unwrap())?;
                    let cost =
                        self.get_cost_with_heuristic_improvements(inc_obj, &mut sol, true)?;
                    (sol, cost)
                }
                SolverResult::Unsat => {
                    break;
                }
                _ => panic!(),
            };
        }
        self.log_routine_end()?;
        Done(())
    }
}
