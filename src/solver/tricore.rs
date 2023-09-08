//! # Core-Guided Multi-Objective Prototype for (up to) 3 Objectives

use rustsat::{
    encodings::card::dbtotalizer::TotDb,
    instances::ManageVars,
    solvers::{SolveIncremental, SolverResult},
    types::{Assignment, Clause},
};
use scuttle_proc::{oracle_bounds, KernelFunctions, Solve};

use crate::{KernelFunctions, Limits, Solve, Termination};

use super::SolverKernel;

#[derive(KernelFunctions, Solve)]
#[solve(bounds = "where VM: ManageVars,
        BCG: FnMut(Assignment) -> Clause,
        O: SolveIncremental")]
pub struct TriCore<VM, O, BCG> {
    /// The solver kernel
    kernel: SolverKernel<VM, O, BCG>,
    /// The ideal point of the current working instance
    ideal: [Option<usize>; 3],
    /// The nadir point of the current working instance
    nadir: [Option<usize>; 3],
    /// The totalizer database
    tot_db: TotDb,
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
        loop {
            self.find_ideal()?;
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
    fn find_ideal(&mut self) -> Result<bool, Termination> {
        todo!()
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
