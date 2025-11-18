//! # LeximaxIST
//!
//! Algorithm proposed in \[1\].
//!
//! ## References
//!
//! - \[1\] Miguel Cabral and Mikolas Janota and Vasco Manquinho: _SAT-Based Leximax Optimisation
//!   Algorithms_, SAT 2022.

use std::io;

use rustsat::{
    solvers::{DefaultInitializer, Initialize, SolveStats, SolverStats},
    types::{Assignment, Clause},
};
use scuttle_proc::KernelFunctions;
use tracing::instrument;

use crate::{
    EncodingStats, ExtendedSolveStats, KernelOptions, Limits,
    MaybeTerminatedError::{self, Done},
    options::EnumOptions,
    types::{ParetoFront, VarManager},
};

use super::{Kernel, Objective};

mod satunsat;
pub use satunsat::SatUnsat;

mod msu3;
pub use msu3::Msu3;

/// The leximaxIST algorithm type
///
/// # Generics
///
/// - `O`: the SAT solver oracle
/// - `Opt`: The optimizer variant to use
/// - `OInit`: the oracle initializer
/// - `BCG`: the blocking clause generator
#[derive(KernelFunctions)]
pub struct LeximaxIst<O, Opt = SatUnsat, OInit = DefaultInitializer, BCG = fn(Assignment) -> Clause>
{
    /// The solver kernel
    kernel: Kernel<O, io::BufWriter<std::fs::File>, OInit, BCG>,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
    /// Starting point for the search
    starting_point: Option<(Vec<usize>, Assignment)>,
    /// The optimization subtype
    opt: Opt,
}

impl<'learn, 'term, Opt, OInit, BCG> super::Solve
    for LeximaxIst<rustsat_cadical::CaDiCaL<'term, 'learn>, Opt, OInit, BCG>
where
    Opt: OptVariant<rustsat_cadical::CaDiCaL<'term, 'learn>, OInit, BCG>,
    BCG: Fn(Assignment) -> Clause,
{
    const LEXIMAX: bool = true;

    #[instrument(name = "leximax", skip(self), fields(limits = %limits))]
    fn solve(&mut self, limits: Limits) -> MaybeTerminatedError {
        self.kernel.start_solving(limits);
        self.opt.alg_main(
            &mut self.kernel,
            &mut self.pareto_front,
            self.starting_point.take(),
        )?;
        Done(())
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
            None,
        )
    }
}

impl<'learn, 'term, Opt, OInit, BCG> super::Init
    for LeximaxIst<rustsat_cadical::CaDiCaL<'learn, 'term>, Opt, OInit, BCG>
where
    Opt: OptVariant<rustsat_cadical::CaDiCaL<'learn, 'term>, OInit, BCG>,
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
        anyhow::ensure!(
            matches!(opts.enumeration, EnumOptions::NoEnum),
            "enumeration is currently not implemented for leximaxIST"
        );
        let mut kernel = Kernel::new(clauses, objs, var_manager, block_clause_gen, opts)?;
        let opt = Opt::init(&mut kernel);
        Ok(Self {
            kernel,
            pareto_front: Default::default(),
            starting_point: None,
            opt,
        })
    }
}

impl<O, Opt, OInit, BCG> ExtendedSolveStats for LeximaxIst<O, Opt, OInit, BCG>
where
    Opt: OptVariant<O, OInit, BCG>,
    O: SolveStats,
{
    fn oracle_stats(&self) -> SolverStats {
        self.kernel.oracle.stats()
    }

    fn encoding_stats(&self) -> Vec<EncodingStats> {
        self.opt.encoding_stats(&self.kernel.objs)
    }
}

trait OptVariant<O, OInit, BCG> {
    fn encoding_stats(&self, objectives: &[Objective]) -> Vec<EncodingStats>;
    fn init(kernel: &mut Kernel<O, io::BufWriter<std::fs::File>, OInit, BCG>) -> Self;
    fn alg_main(
        &mut self,
        kernel: &mut Kernel<O, io::BufWriter<std::fs::File>, OInit, BCG>,
        pareto_front: &mut ParetoFront,
        starting_point: Option<(Vec<usize>, Assignment)>,
    ) -> MaybeTerminatedError;
}
