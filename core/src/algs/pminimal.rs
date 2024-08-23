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

use rustsat::{
    encodings::{
        self,
        card::{self, DbTotalizer},
        pb::{self, DbGte},
        EncodeStats,
    },
    instances::{Cnf, ManageVars},
    solvers::{
        DefaultInitializer, Initialize, SolveIncremental, SolveStats, SolverResult, SolverStats,
    },
    types::{Assignment, Clause, Lit, WLitIter},
};
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{
    algs::ObjEncoding,
    options::{AfterCbOptions, CoreBoostingOptions, EnumOptions},
    termination::ensure,
    types::{ParetoFront, VarManager},
    EncodingStats, ExtendedSolveStats, KernelFunctions, KernelOptions, Limits,
    MaybeTerminatedError::{self, Done},
    Phase, Solve,
};

use super::{coreboosting::MergeOllRef, CoreBoost, Kernel, Objective};

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
#[derive(KernelFunctions, Solve)]
#[solve(bounds = "where PBE: pb::BoundUpperIncremental + EncodeStats,
        CE: card::BoundUpperIncremental + EncodeStats,
        BCG: Fn(Assignment) -> Clause,
        O: SolveIncremental + SolveStats")]
pub struct PMinimal<
    O,
    PBE = DbGte,
    CE = DbTotalizer,
    ProofW = io::BufWriter<fs::File>,
    OInit = DefaultInitializer,
    BCG = fn(Assignment) -> Clause,
> {
    /// The solver kernel
    kernel: Kernel<O, ProofW, OInit, BCG>,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: Vec<ObjEncoding<PBE, CE>>,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

#[oracle_bounds]
impl<O, PBE, CE, ProofW, OInit, BCG> super::Init for PMinimal<O, PBE, CE, ProofW, OInit, BCG>
where
    O: SolveIncremental,
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    ProofW: io::Write,
    OInit: Initialize<O>,
    BCG: Fn(Assignment) -> Clause,
{
    type Oracle = O;
    type BlockClauseGen = BCG;
    type ProofWriter = ProofW;

    /// Initializes a default solver with a configured oracle and options. The
    /// oracle should _not_ have any clauses loaded yet.
    fn new<Cls, Objs, Obj>(
        clauses: Cls,
        objs: Objs,
        var_manager: VarManager,
        opts: KernelOptions,
        proof: Option<pidgeons::Proof<ProofW>>,
        block_clause_gen: BCG,
    ) -> anyhow::Result<Self>
    where
        Cls: IntoIterator<Item = Clause>,
        Objs: IntoIterator<Item = (Obj, isize)>,
        Obj: WLitIter,
    {
        let kernel = Kernel::new(clauses, objs, var_manager, block_clause_gen, proof, opts)?;
        Ok(Self::init(kernel))
    }
}

impl<O, PBE, CE, ProofW, OInit, BCG> ExtendedSolveStats for PMinimal<O, PBE, CE, ProofW, OInit, BCG>
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

impl<O, PBE, CE, ProofW, OInit, BCG> PMinimal<O, PBE, CE, ProofW, OInit, BCG>
where
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

#[oracle_bounds]
impl<O, PBE, CE, ProofW, OInit, BCG> PMinimal<O, PBE, CE, ProofW, OInit, BCG>
where
    O: SolveIncremental + SolveStats,
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    BCG: Fn(Assignment) -> Clause,
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
            self.kernel
                .yield_solutions(costs, &assumps, solution, &mut self.pareto_front)?;

            // Block last Pareto point, if temporarily blocked
            if let Some(block_lit) = block_switch {
                self.kernel.oracle.add_unit(block_lit)?;
            }
        }
    }
}

#[oracle_bounds]
impl<O, PBE, CE, ProofW, OInit, BCG> CoreBoost for PMinimal<O, PBE, CE, ProofW, OInit, BCG>
where
    O: SolveIncremental + SolveStats,
    (PBE, CE): MergeOllRef<PBE = PBE, CE = CE>,
    OInit: Initialize<O>,
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
        for (oidx, (reform, mut tot_db)) in cb_res.into_iter().enumerate() {
            if reset_dbs {
                tot_db.reset_vars();
            }
            if !matches!(self.kernel.objs[oidx], Objective::Constant { .. }) {
                self.obj_encs[oidx] = <(PBE, CE)>::merge(reform, tot_db, opts.rebase);
            }
            self.kernel.check_termination()?;
        }
        self.kernel.log_routine_end()?;
        Done(true)
    }
}

#[oracle_bounds]
impl<O, ProofW, OInit, BCG> Kernel<O, ProofW, OInit, BCG>
where
    O: SolveIncremental + SolveStats,
{
    /// Executes P-minimization from a cost and solution starting point
    pub fn p_minimization<PBE, CE>(
        &mut self,
        mut costs: Vec<usize>,
        mut solution: Assignment,
        base_assumps: &[Lit],
        obj_encs: &mut [ObjEncoding<PBE, CE>],
    ) -> MaybeTerminatedError<(Vec<usize>, Assignment, Option<Lit>)>
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
    {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        self.log_routine_start("p minimization")?;
        let mut block_switch = None;
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
            // Force next solution to dominate the current one
            assumps.drain(base_assumps.len()..);
            #[cfg(not(feature = "coarse-convergence"))]
            assumps.extend(self.enforce_dominating(&costs, obj_encs)?);
            #[cfg(feature = "coarse-convergence")]
            assumps.extend(self.enforce_dominating(&bound_costs, obj_encs)?);
            // Block solutions dominated by the current one
            if self.opts.enumeration == EnumOptions::NoEnum {
                // Block permanently since no enumeration at Pareto point
                let block_clause = self.dominated_block_clause(&costs, obj_encs)?;
                self.oracle.add_clause(block_clause)?;
            } else {
                // Permanently block last candidate
                if let Some(block_lit) = block_switch {
                    self.oracle.add_unit(block_lit)?;
                }
                // Temporarily block to allow for enumeration at Pareto point
                let block_lit = self.tmp_block_dominated(&costs, obj_encs)?;
                block_switch = Some(block_lit);
                assumps.push(block_lit);
            }

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
    pub fn enforce_dominating<'a, PBE, CE>(
        &'a mut self,
        costs: &'a [usize],
        obj_encs: &'a mut [ObjEncoding<PBE, CE>],
    ) -> Result<impl Iterator<Item = Lit> + 'a, rustsat::OutOfMemory>
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
    {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        for (idx, &cst) in costs.iter().enumerate() {
            let enc = &mut obj_encs[idx];
            enc.encode_ub_change(cst..cst + 1, &mut self.oracle, &mut self.var_manager)?;
        }
        Ok(costs.iter().enumerate().flat_map(|(idx, &cst)| {
            let enc = &mut obj_encs[idx];
            enc.enforce_ub(cst).unwrap().into_iter()
        }))
    }

    /// Gets a clause blocking solutions (weakly) dominated by the given cost point,
    /// given objective encodings.
    pub fn dominated_block_clause<PBE, CE>(
        &mut self,
        costs: &[usize],
        obj_encs: &mut [ObjEncoding<PBE, CE>],
    ) -> Result<Clause, rustsat::OutOfMemory>
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
    {
        debug_assert_eq!(costs.len(), obj_encs.len());
        let mut clause = Clause::default();
        for (idx, &cst) in costs.iter().enumerate() {
            // Don't block
            if cst <= obj_encs[idx].offset() {
                continue;
            }
            let enc = &mut obj_encs[idx];
            if let ObjEncoding::Constant = enc {
                continue;
            }
            // Encode and add to solver
            enc.encode_ub_change(cst - 1..cst, &mut self.oracle, &mut self.var_manager)?;
            let assumps = enc.enforce_ub(cst - 1).unwrap();
            if assumps.len() == 1 {
                clause.add(assumps[0]);
            } else {
                let mut and_impl = Cnf::new();
                let and_lit = self.var_manager.new_var().pos_lit();
                and_impl.add_lit_impl_cube(and_lit, &assumps);
                self.oracle.add_cnf(and_impl).unwrap();
                clause.add(and_lit)
            }
        }
        Ok(clause)
    }

    /// Temporarily blocks solutions dominated by the given cost point. Returns
    /// and assumption that needs to be enforced in order for the blocking to be
    /// enforced.
    pub fn tmp_block_dominated<PBE, CE>(
        &mut self,
        costs: &[usize],
        obj_encs: &mut [ObjEncoding<PBE, CE>],
    ) -> Result<Lit, rustsat::OutOfMemory>
    where
        PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
    {
        debug_assert_eq!(costs.len(), self.stats.n_objs);
        let mut clause = self.dominated_block_clause(costs, obj_encs)?;
        let block_lit = self.var_manager.new_var().pos_lit();
        clause.add(block_lit);
        self.oracle.add_clause(clause).unwrap();
        Ok(!block_lit)
    }
}
