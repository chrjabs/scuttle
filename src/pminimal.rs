//! # The $P$-Minimal Algorithm for Multi-Objective Optimization
//!
//! This the main module of the solver containing the implementation of the algorithm.

use std::collections::HashMap;

use crate::{
    EncodingStats, ExtendedSolveStats, Options, OracleStats, ParetoFront, Solve, Stats, Termination,
};
use rustsat::{
    encodings,
    encodings::{card, pb},
    instances::{ManageVars, MultiOptInstance, Objective, CNF},
    solvers,
    types::{Clause, Lit},
};

/// The solver type. Generics the pseudo-boolean encoding to use for weighted
/// objectives, the cardinality encoding to use for unweighted objectives, the
/// variable manager to use and the SAT backend.
pub struct PMinimal<PBE, CE, VM, O>
where
    PBE: pb::IncUBPB,
    CE: card::IncUBCard,
    VM: ManageVars,
    O: solvers::IncrementalSolve,
{
    /// The SAT solver backend
    oracle: O,
    /// The variable manager keeping track of variables
    var_manager: VM,
    /// A cardinality or pseudo-boolean encoding for each objective
    obj_encs: Vec<ObjEncoding<PBE, CE>>,
    /// All clauses that contain objective literals. Only populated when using
    /// model tightening. If blocking literals were added by the solver, the
    /// blocking literal is _not_ in the clause kept here.
    obj_clauses: Vec<Clause>,
    /// Maps soft clauses to blocking literals
    blits: HashMap<Clause, Lit>,
    /// Objective literal data
    obj_lit_data: HashMap<Lit, ObjLitData>,
    /// The Pareto front discovered so far
    pareto_front: ParetoFront,
    /// Configuration options
    opts: Options,
    /// Running statistics
    stats: Stats,
}

impl<PBE, CE, VM, O> Solve<VM> for PMinimal<PBE, CE, VM, O>
where
    PBE: pb::IncUBPB,
    CE: card::IncUBCard,
    VM: ManageVars,
    O: solvers::IncrementalSolve,
{
    fn init_with_options(inst: MultiOptInstance<VM>, opts: Options) -> Self {
        let (constr, objs) = inst.decompose();
        let (mut cnf, var_manager) = constr.as_cnf();
        let mut solver = PMinimal {
            oracle: O::new(),
            var_manager: var_manager,
            obj_encs: vec![],
            obj_clauses: vec![],
            blits: HashMap::new(),
            obj_lit_data: HashMap::new(),
            pareto_front: ParetoFront::new(),
            opts,
            stats: Stats::init(),
        };
        solver.stats.n_objs = objs.len();
        solver.obj_encs.reserve_exact(objs.len());
        // Add objectives to solver
        objs.into_iter()
            .for_each(|obj| cnf.extend(solver.add_objective(obj)));
        // Add hard clauses and relaxed soft clauses to oracle
        solver.oracle.add_cnf(cnf);
        solver
    }

    fn solve(
        &mut self,
        max_pps: Option<usize>,
        max_sols: Option<usize>,
        max_candidates: Option<usize>,
        max_oracle_calls: Option<usize>,
    ) -> Termination {
        todo!()
    }

    fn pareto_front(&self) -> ParetoFront {
        self.pareto_front.clone()
    }

    fn stats(&self) -> Stats {
        self.stats.clone()
    }
}

impl<PBE, CE, VM, O> ExtendedSolveStats for PMinimal<PBE, CE, VM, O>
where
    PBE: pb::IncUBPB + encodings::EncodeStats,
    CE: card::IncUBCard + encodings::EncodeStats,
    VM: ManageVars,
    O: solvers::IncrementalSolve + solvers::SolveStats,
{
    fn oracle_stats(&self) -> OracleStats {
        OracleStats {
            n_sat_solves: self.oracle.n_sat_solves(),
            n_unsat_solves: self.oracle.n_unsat_solves(),
            n_clauses: self.oracle.n_clauses(),
            n_vars: self.oracle.n_vars(),
            avg_clause_len: self.oracle.avg_clause_len(),
            cpu_solve_time: self.oracle.cpu_solve_time(),
        }
    }

    fn encoding_stats(&self) -> Vec<EncodingStats> {
        self.obj_encs
            .iter()
            .map(|obj_enc| match obj_enc {
                ObjEncoding::Weighted { encoding, offset } => EncodingStats {
                    n_clauses: encoding.n_clauses(),
                    n_vars: encoding.n_vars(),
                    offset: *offset,
                    unit_weight: None,
                },
                ObjEncoding::Unweighted {
                    encoding,
                    offset,
                    unit_weight,
                } => EncodingStats {
                    n_clauses: encoding.n_clauses(),
                    n_vars: encoding.n_vars(),
                    offset: *offset,
                    unit_weight: Some(*unit_weight),
                },
            })
            .collect()
    }
}

impl<PBE, CE, VM, O> PMinimal<PBE, CE, VM, O>
where
    PBE: pb::IncUBPB,
    CE: card::IncUBCard,
    VM: ManageVars,
    O: solvers::IncrementalSolve,
{
    /// Adds a new objective to the solver. This shall only be called during
    /// initialization.
    fn add_objective(&mut self, obj: Objective) -> CNF {
        let mut cnf = CNF::new();
        if obj.weighted() {
            // Add weighted objective
            let (soft_cl, offset) = obj.as_soft_cls();
            let lits: HashMap<Lit, usize> = soft_cl
                .into_iter()
                .map(|(cl, w)| {
                    let (olit, opt_cls_info) = self.add_soft_clause(cl);
                    // Track the objective index for the objective literal
                    match self.obj_lit_data.get_mut(&olit) {
                        Some(data) => data.objs.push(self.obj_encs.len()),
                        None => {
                            self.obj_lit_data.insert(
                                olit,
                                ObjLitData {
                                    objs: vec![self.obj_encs.len()],
                                    clauses: vec![],
                                },
                            );
                        }
                    };
                    // Add hard clause to CNF and track olit appearance
                    match opt_cls_info {
                        Some((cls_idx, hard_cl)) => {
                            cnf.add_clause(hard_cl);
                            if self.opts.model_tightening {
                                self.obj_lit_data
                                    .get_mut(&olit)
                                    .unwrap()
                                    .clauses
                                    .push(cls_idx);
                            }
                        }
                        None => (),
                    };
                    (olit, w)
                })
                .collect();
            // Initialize encoder for objective
            self.obj_encs.push(ObjEncoding::new_weighted(lits, offset));
        } else {
            // Add unweighted objective
            let (soft_cl, unit_weight, offset) = obj.as_unweighted_soft_cls();
            let lits: Vec<Lit> = soft_cl
                .into_iter()
                .map(|cl| {
                    let (olit, opt_cls_info) = self.add_soft_clause(cl);
                    // Track the objective index for the objective literal
                    match self.obj_lit_data.get_mut(&olit) {
                        Some(data) => data.objs.push(self.obj_encs.len()),
                        None => {
                            self.obj_lit_data.insert(
                                olit,
                                ObjLitData {
                                    objs: vec![self.obj_encs.len()],
                                    clauses: vec![],
                                },
                            );
                        }
                    };
                    // Add hard clause to CNF and track olit appearance
                    match opt_cls_info {
                        Some((cls_idx, hard_cl)) => {
                            cnf.add_clause(hard_cl);
                            if self.opts.model_tightening {
                                self.obj_lit_data
                                    .get_mut(&olit)
                                    .unwrap()
                                    .clauses
                                    .push(cls_idx);
                            }
                        }
                        None => (),
                    };
                    olit
                })
                .collect();
            // Initialize encoder for objective
            self.obj_encs
                .push(ObjEncoding::new_unweighted(lits, offset, unit_weight));
        }
        cnf
    }

    /// Adds a soft clause to the solver, returns an objective literal. If the
    /// clause has been newly relaxed, also returns the index of the clause in
    /// [`PMinimal::obj_clauses`] as well as the relaxed clause to be added to
    /// the oracle.
    fn add_soft_clause(&mut self, mut cls: Clause) -> (Lit, Option<(usize, Clause)>) {
        if cls.len() == 1 {
            // No blit needed
            return (cls[0], None);
        }
        if self.blits.contains_key(&cls) {
            // Reuse clause with blit that was already added
            let blit = self.blits[&cls];
            return (blit, None);
        }
        // Get new blit
        let blit = self.var_manager.next_free().pos_lit();
        // Save blit in case same soft clause reappears
        // TODO: find way to not have to clone the clause here
        self.blits.insert(cls.clone(), blit);
        if self.opts.model_tightening {
            // Add clause to the saved objective clauses
            self.obj_clauses.push(cls.clone());
        }
        // Relax clause and return so that it is added to the oracle
        cls.add(blit);
        (blit, Some((self.obj_clauses.len() - 1, cls)))
    }
}

/// Data regarding an objective literal
struct ObjLitData {
    /// Objectives that the literal appears in
    objs: Vec<usize>,
    /// Clauses that the literal appears in. The entries are indices in
    /// [`PMinimal::obj_clauses`]. Only populated when using model tightening.
    clauses: Vec<usize>,
}

/// Internal data associated with an objective
enum ObjEncoding<PBE, CE>
where
    PBE: pb::IncUBPB,
    CE: card::IncUBCard,
{
    Weighted {
        offset: isize,
        encoding: PBE,
    },
    Unweighted {
        offset: isize,
        unit_weight: usize,
        encoding: CE,
    },
}

impl<PBE, CE> ObjEncoding<PBE, CE>
where
    PBE: pb::IncUBPB,
    CE: card::IncUBCard,
{
    /// Initializes a new objective encoding for a weighted objective
    fn new_weighted(lits: HashMap<Lit, usize>, offset: isize) -> Self {
        ObjEncoding::Weighted {
            offset,
            encoding: PBE::new_from_lits(lits.into_iter()),
        }
    }

    /// Initializes a new objective encoding for a weighted objective
    fn new_unweighted(lits: Vec<Lit>, offset: isize, unit_weight: usize) -> Self {
        ObjEncoding::Unweighted {
            offset,
            unit_weight,
            encoding: CE::new_from_lits(lits.into_iter()),
        }
    }
}
