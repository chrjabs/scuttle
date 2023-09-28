//! # BiOptSat Algorithm for Bi-Objective Optimization
//!
//! ## References
//!
//! - \[1\] Christoph Jabs and Jeremias Berg and Andreas Niskanen and Matti
//! Järvisalo: _MaxSAT-Based Bi-Objective Boolean Optimization_, SAT 2022.

use rustsat::{
    encodings::{self, card, pb},
    instances::{ManageVars, MultiOptInstance},
    solvers::{SolveIncremental, SolveStats, SolverStats},
    types::{Assignment, Clause, Lit},
};
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{
    types::ParetoFront, EncodingStats, ExtendedSolveStats, KernelFunctions, KernelOptions, Limits,
    Solve, Termination,
};

use super::{default_blocking_clause, ObjEncoding, Objective, SolverKernel};

#[derive(KernelFunctions, Solve)]
#[solve(bounds = "where PBE: pb::BoundUpperIncremental,
        CE: card::BoundUpperIncremental,
        VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental + SolveStats")]
pub struct BiOptSat<PBE, CE, VM, BCG, O> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: (ObjEncoding<PBE, CE>, ObjEncoding<PBE, CE>),
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
}

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
    ) -> Result<Self, Termination> {
        let kernel = SolverKernel::new(inst, O::default(), block_clause_gen, opts)?;
        Ok(Self::init(kernel))
    }
}

impl<PBE, CE, VM, O> BiOptSat<PBE, CE, VM, fn(Assignment) -> Clause, O>
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
    ) -> Result<Self, Termination> {
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
            .zip([&self.obj_encs.0, &self.obj_encs.1].into_iter())
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
                lits.iter().map(|&l| l),
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
                lits.iter().map(|&l| l),
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
    fn alg_main(&mut self) -> Result<(), Termination> {
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
