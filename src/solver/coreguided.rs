//! # Core-Guided Search Functionality

use rustsat::{
    encodings::card::dbtotalizer::TotDb,
    instances::ManageVars,
    solvers::{SolveIncremental, SolverResult},
    types::Assignment,
};

use crate::Termination;

use super::{Objective, SolverKernel};

impl<VM, O, BCG> SolverKernel<VM, O, BCG>
where
    VM: ManageVars,
    O: SolveIncremental,
{
    /// OLL core-guided search over an objective. The implementation includes the following
    /// refinements:
    /// - Weight-aware core extraction
    /// - Core exhaustion
    pub fn oll(
        &mut self,
        objective: Objective,
        tot_db: &mut TotDb,
    ) -> Result<(Assignment, Objective), Termination> {
        let (mut obj, offset, unit_weight) = match objective {
            Objective::Weighted { offset, lits } => (lits, offset, None),
            Objective::Unweighted {
                offset,
                unit_weight,
                lits,
            } => (
                lits.into_iter().map(|l| (l, unit_weight)).collect(),
                offset,
                Some(unit_weight),
            ),
            Objective::Constant { .. } => panic!(),
        };
        // Build assumptions sorted by weight
        let mut assumps: Vec<_> = obj.iter().map(|(&l, _)| !l).collect();
        assumps.sort_unstable_by_key(|&l| -(obj[&!l] as isize));

        loop {
            match self.solve_assumps(&assumps)? {
                SolverResult::Sat => {
                    let sol = self.oracle.solution(self.var_manager.max_var().unwrap())?;
                    obj.retain(|_, w| *w > 0);
                    let obj = if let Some(unit_weight) = unit_weight {
                        Objective::Unweighted {
                            offset,
                            unit_weight,
                            lits: obj.keys().copied().collect(),
                        }
                    } else {
                        Objective::Weighted { offset, lits: obj }
                    };
                    return Ok((sol, obj));
                }
                SolverResult::Unsat => {
                    let core = self.oracle.core()?;
                    let core_weight = core
                        .iter()
                        .fold(usize::MAX, |cw, l| std::cmp::min(cw, obj[l]));
                    // Extend tot if output in core
                    for &olit in &core {
                        
                    }
                    // Reformulate core
                }
                SolverResult::Interrupted => panic!(),
            }
        }
    }
}
