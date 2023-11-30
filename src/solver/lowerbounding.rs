//! # Multi-Objective Lower-Bounding Search
//!
//! Algorithm proposed in \[1\].
//!
//! ## References
//!
//! - \[1\] Joao Cortes and Ines Lynce and Vasco M. Maquinho: _New Core-Guided
//! and Hitting Set Algorithms for Multi-Objective Combinatorial Optimization_,
//! TACAS 2023.

use rustsat::{
    encodings::{
        self,
        card::{self, DbTotalizer},
        pb::{self, DbGte},
        EncodeStats,
    },
    instances::{BasicVarManager, Cnf, ManageVars, MultiOptInstance},
    solvers::{SolveIncremental, SolveStats, SolverResult, SolverStats},
    types::{Assignment, Clause, Lit},
};
use rustsat_cadical::CaDiCaL;
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{
    types::ParetoFront, EncodingStats, ExtendedSolveStats, KernelFunctions, KernelOptions, Limits,
    Solve, Termination,
};

use super::{default_blocking_clause, ObjEncoding, Objective, SolverKernel};

#[derive(KernelFunctions, Solve)]
#[solve(
    bounds = "where PBE: pb::BoundUpperIncremental + EncodeStats,
        CE: card::BoundUpperIncremental + EncodeStats,
        VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental + SolveStats",
    extended_stats
)]
pub struct LowerBounding<
    PBE = DbGte,
    CE = DbTotalizer,
    VM = BasicVarManager,
    BCG = fn(Assignment) -> Clause,
    O = CaDiCaL<'static, 'static>,
> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: Vec<ObjEncoding<PBE, CE>>,
    /// The current fence
    fence: Fence,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

#[oracle_bounds]
impl<PBE, CE, VM, O> LowerBounding<PBE, CE, VM, fn(Assignment) -> Clause, O>
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
    ) -> Result<Self, Termination> {
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
impl<PBE, CE, VM, BCG, O> LowerBounding<PBE, CE, VM, BCG, O>
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
    ) -> Result<Self, Termination> {
        let kernel = SolverKernel::new(inst, O::default(), block_clause_gen, opts)?;
        Ok(Self::init(kernel))
    }
}

#[oracle_bounds]
impl<PBE, CE, VM, O> LowerBounding<PBE, CE, VM, fn(Assignment) -> Clause, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    O: SolveIncremental + SolveStats + Default,
{
    pub fn new_defaults(
        inst: MultiOptInstance<VM>,
        opts: KernelOptions,
    ) -> Result<Self, Termination> {
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
impl<PBE, CE, VM, BCG, O> LowerBounding<PBE, CE, VM, BCG, O>
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
    ) -> Result<Self, Termination> {
        let kernel = SolverKernel::new(inst, oracle, block_clause_gen, opts)?;
        Ok(Self::init(kernel))
    }
}

impl<PBE, CE, VM, BCG, O> ExtendedSolveStats for LowerBounding<PBE, CE, VM, BCG, O>
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

impl<PBE, CE, VM, BCG, O> LowerBounding<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental + FromIterator<(Lit, usize)>,
    CE: card::BoundUpperIncremental + FromIterator<Lit>,
    VM: ManageVars,
    O: SolveIncremental + SolveStats,
{
    /// Initializes the solver
    fn init(mut kernel: SolverKernel<VM, O, BCG>) -> Self {
        // Initialize objective encodings
        let (obj_encs, fence_data) = kernel
            .objs
            .iter()
            .map(|obj| {
                let mut enc = match obj {
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
                enc.encode_ub_change(0..1, &mut kernel.oracle, &mut kernel.var_manager);
                let assumps = enc.enforce_ub(0).unwrap();
                let assump = if assumps.is_empty() {
                    None
                } else if 1 == assumps.len() {
                    Some(assumps[0])
                } else {
                    let mut and_impl = Cnf::new();
                    let and_lit = kernel.var_manager.new_var().pos_lit();
                    and_impl.add_lit_impl_cube(and_lit, &assumps);
                    kernel.oracle.add_cnf(and_impl).unwrap();
                    Some(and_lit)
                };
                (enc, (0, assump))
            })
            .unzip();
        Self {
            kernel,
            obj_encs,
            fence: Fence { data: fence_data },
            pareto_front: Default::default(),
        }
    }
}

#[oracle_bounds]
impl<PBE, CE, VM, BCG, O> LowerBounding<PBE, CE, VM, BCG, O>
where
    PBE: pb::BoundUpperIncremental,
    CE: card::BoundUpperIncremental,
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental + SolveStats,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> Result<(), Termination> {
        debug_assert_eq!(self.obj_encs.len(), self.kernel.stats.n_objs);
        self.kernel.log_routine_start("lower-bounding")?;
        loop {
            let res = self.kernel.solve_assumps(&self.fence.assumps())?;
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
                        return Ok(());
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

/// Data related to the current fence
pub(crate) struct Fence {
    /// The current bounds and enforcing literals
    pub data: Vec<(usize, Option<Lit>)>,
}

impl Fence {
    pub fn assumps(&self) -> Vec<Lit> {
        self.data
            .iter()
            .filter_map(|(_, ol)| ol.to_owned())
            .collect()
    }

    pub fn bounds(&self) -> Vec<usize> {
        self.data.iter().map(|&(b, _)| b).collect()
    }
}
