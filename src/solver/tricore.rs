//! # Core-Guided Multi-Objective Prototype for (up to) 3 Objectives

use rustsat::{
    encodings::card::dbtotalizer::TotDb,
    instances::{ManageVars, MultiOptInstance},
    solvers::{SolveIncremental, SolverResult},
    types::{Assignment, Clause},
};
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{KernelFunctions, Limits, Options, Solve, Termination};

use super::{coreguided::OllReformulation, default_blocking_clause, SolverKernel};

#[derive(KernelFunctions, Solve)]
#[solve(bounds = "where VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental")]
pub struct TriCore<VM, O, BCG> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// The objective reformulations
    reforms: [Option<OllReformulation>; 3],
    /// The ideal point of the current working instance
    ideal: [usize; 3],
    /// The nadir point of the current working instance
    nadir: [usize; 3],
    /// The totalizer database
    tot_db: TotDb,
}

impl<VM, O> TriCore<VM, O, fn(Assignment) -> Clause>
where
    VM: ManageVars,
    O: SolveIncremental,
{
    pub fn new_default_blocking(
        inst: MultiOptInstance<VM>,
        oracle: O,
        opts: Options,
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

impl<VM, O> TriCore<VM, O, fn(Assignment) -> Clause>
where
    VM: ManageVars,
    O: SolveIncremental + Default,
{
    pub fn new_defaults(inst: MultiOptInstance<VM>, opts: Options) -> Result<Self, Termination> {
        let kernel = SolverKernel::<_, _, fn(Assignment) -> Clause>::new(
            inst,
            O::default(),
            default_blocking_clause,
            opts,
        )?;
        Ok(Self::init(kernel))
    }
}

impl<VM, O, BCG> TriCore<VM, O, BCG>
where
    VM: ManageVars,
{
    /// Initializes the solver
    fn init(kernel: SolverKernel<VM, O, BCG>) -> Self {
        debug_assert!(kernel.stats.n_objs <= 3);
        let mut solver = Self {
            kernel,
            reforms: [None, None, None],
            ideal: [0; 3],
            nadir: [0; 3],
            tot_db: Default::default(),
        };
        // Initialize objective reformulations
        for (idx, obj) in solver.kernel.objs.iter().enumerate() {
            solver.reforms[idx] = Some(obj.into());
            // nadir point is initialized with zeroes first to make comparison
            // for the termination criterion easier
            solver.nadir[idx] = usize::MAX;
        }
        solver
    }
}

#[oracle_bounds]
impl<VM, O, BCG> TriCore<VM, O, BCG>
where
    VM: ManageVars,
    BCG: FnMut(Assignment) -> Clause,
    O: SolveIncremental,
{
    /// The solving algorithm main routine.
    fn alg_main(&mut self) -> Result<(), Termination> {
        let res = self.kernel.solve()?;
        if SolverResult::Unsat == res {
            return Ok(());
        }
        loop {
            self.find_ideal()?;
            if self.ideal == self.nadir {
                break;
            }
            self.find_nadir()?;
            self.cut_nadir()?;
            if self.ideal == self.nadir {
                break;
            }
            self.block_remaining()?;
        }
        Ok(())
    }

    /// Finds the ideal point of the working instance by executing OLL
    /// single-objective optimization. Returns false if the entire pareto front
    /// was found.
    fn find_ideal(&mut self) -> Result<(), Termination> {
        self.kernel.log_routine_start("find_ideal")?;
        for obj_idx in 0..self.kernel.stats.n_objs {
            let obj_ref = self.reforms[obj_idx].take().unwrap();
            let (_, obj_ref) = self.kernel.oll(obj_ref, &mut self.tot_db)?;
            // TODO: maybe make use of solution?
            self.ideal[obj_idx] = obj_ref.offset;
            self.reforms[obj_idx] = Some(obj_ref)
        }
        self.kernel.log_routine_end()?;
        Ok(())
    }

    /// Find the nadir point of the working instance by solving all permutations
    /// of lexicographic optimization with LSU
    fn find_nadir(&mut self) -> Result<(), Termination> {
        todo!()
    }

    /// Introduces the nadir point cut
    fn cut_nadir(&mut self) -> Result<(), Termination> {
        todo!()
    }

    /// Blocks all solutions that are not cut by the nadir cut with a P-Minimal
    /// clause
    fn block_remaining(&mut self) -> Result<(), Termination> {
        todo!()
    }
}
