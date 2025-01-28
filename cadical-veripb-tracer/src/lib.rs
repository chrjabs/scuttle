//! # VeriPB Proof Tracer For CaDiCaL Through RustSAT

use std::io;

use pigeons::{AbsConstraintId, Conclusion, ConstraintId, OutputGuarantee, Proof};
use rustsat::{
    encodings::{CollectCertClauses, CollectClauses},
    solvers::SolverResult,
    types::{Clause, Lit, RsHashSet, Var},
};
use rustsat_cadical::{CaDiCaL, CaDiCaLClause, ClauseId, ProofTracerHandle, TraceProof};

#[derive(Debug)]
pub struct CadicalTracer<ProofW: io::Write> {
    /// The proof to be passed back and forth between the tracer and the kernel
    proof: Option<Proof<ProofW>>,
    /// The constraint ID mapper
    cmap: ConstraintMapper,
    /// The [`AbsConstraintId`] of the last found core
    core_id: Option<AbsConstraintId>,
    /// The set of weakened clauses
    weakened_clauses: RsHashSet<ClauseId>,
    assumptions: Vec<Lit>,
}

impl<ProofW: io::Write> CadicalTracer<ProofW> {
    pub fn new(proof: Proof<ProofW>) -> Self {
        CadicalTracer {
            proof: Some(proof),
            cmap: ConstraintMapper::default(),
            core_id: None,
            weakened_clauses: RsHashSet::default(),
            assumptions: vec![],
        }
    }

    pub fn proof_mut(&mut self) -> &mut Proof<ProofW> {
        self.proof.as_mut().expect("expected proof")
    }

    pub fn take_proof(&mut self) -> Proof<ProofW> {
        let Some(proof) = self.proof.take() else {
            panic!("expected proof")
        };
        proof
    }

    pub fn replace_proof(&mut self, proof: Proof<ProofW>) -> Option<Proof<ProofW>> {
        self.proof.replace(proof)
    }

    pub fn core_id(&self) -> Option<AbsConstraintId> {
        self.core_id
    }
}

impl<ProofW: io::Write> CadicalTracer<ProofW>
where
    ProofW: io::Write,
{
    fn add_derived(
        &mut self,
        id: ClauseId,
        redundant: bool,
        clause: &CaDiCaLClause,
        antecedents: &[ClauseId],
    ) -> AbsConstraintId {
        debug_assert!(!antecedents.is_empty());
        let proof = self.proof.as_mut().expect("expected proof");
        let veripb_id = write_derived(
            proof,
            clause,
            antecedents.iter().map(|id| self.cmap.map(*id)),
        );
        self.cmap.add_clause_checked(veripb_id, id);
        #[cfg(feature = "verbose")]
        proof
            .equals(clause, Some(pigeons::ConstraintId::last(1)))
            .expect("failed to write proof");
        if !redundant {
            proof
                .move_ids_to_core([pigeons::ConstraintId::from(veripb_id)])
                .expect("failed to write proof");
        }
        veripb_id
    }
}

impl<ProofW: io::Write> TraceProof for CadicalTracer<ProofW>
where
    ProofW: io::Write,
{
    fn add_original_clause(
        &mut self,
        id: ClauseId,
        _redundant: bool,
        _clause: &CaDiCaLClause,
        restored: bool,
    ) {
        if restored {
            return;
        }
        debug_assert_eq!(usize::try_from(id.0).unwrap(), self.cmap.map.len());
        let proof = self.proof.as_mut().expect("expected proof");
        #[cfg(feature = "verbose")]
        {
            proof
                .equals(_clause, Some(self.cmap.map(id).into()))
                .expect("failed to write proof");
        }
        let veripb_id = self.cmap.map(id);
        if veripb_id >= proof.first_proof_id() {
            proof
                .move_ids_to_core([veripb_id.into()])
                .expect("failed to write proof");
        }
    }

    fn add_derived_clause(
        &mut self,
        id: ClauseId,
        redundant: bool,
        clause: &CaDiCaLClause,
        antecedents: &[ClauseId],
    ) {
        self.add_derived(id, redundant, clause, antecedents);
    }

    fn delete_clause(&mut self, id: ClauseId, redundant: bool, _clause: &CaDiCaLClause) {
        if !redundant {
            // don't delete clauses that are not redundant
            // NOTE: in cadicals proof tracer itself, this is `!redundant &&
            // self.weakened_clauses.contains(&id)`, but that might delete clauses in the proof
            // that scuttle thinks are still there
            return;
        }
        let id = self.cmap.map(id);
        let proof = self.proof.as_mut().expect("expected proof");
        proof
            .delete_ids::<Var, CaDiCaLClause, _, _>([id.into()], None)
            .expect("failed to write proof")
    }

    fn strengthen(&mut self, id: ClauseId) {
        self.proof
            .as_mut()
            .expect("expected proof")
            .move_ids_to_core([self.cmap.map(id).into()])
            .expect("failed to write proof");
    }

    fn weaken_minus(&mut self, id: ClauseId, _clause: &CaDiCaLClause) {
        self.weakened_clauses.insert(id);
    }

    fn report_status(&mut self, status: SolverResult, id: ClauseId) {
        let id = if id.0 > 0 {
            Some(self.cmap.map(id))
        } else {
            None
        };
        #[cfg(feature = "verbose")]
        self.proof
            .as_mut()
            .expect("expected proof")
            .comment(&format_args!(
                "CaDiCaL: finished solving: {status}, id: {id:?}",
            ))
            .expect("failed to write proof");
        if let Some(id) = id {
            debug_assert_eq!(status, SolverResult::Unsat);
            self.proof
                .as_mut()
                .expect("expected proof")
                .update_default_conclusion::<Var>(
                    OutputGuarantee::None,
                    &Conclusion::Unsat(Some(ConstraintId::from(id))),
                );
            #[cfg(feature = "verbose")]
            self.proof
                .as_mut()
                .expect("expected proof")
                .equals(&rustsat::clause![], Some(ConstraintId::from(id)))
                .expect("failed to write proof");
        }
    }

    fn solve_query(&mut self) {
        #[cfg(feature = "verbose")]
        {
            use itertools::Itertools;
            let proof = self.proof.as_mut().expect("expected proof");
            proof
                .comment(&"CaDiCaL: start solving with the following assumptions")
                .expect("failed to write proof");
            proof
                .comment(&format_args!(
                    "[{}]",
                    self.assumptions
                        .iter()
                        .map(|l| pigeons::Axiom::from(*l))
                        .format(", ")
                ))
                .expect("failed to write proof");
        }
    }

    fn add_assumption(&mut self, assumption: Lit) {
        self.assumptions.push(assumption)
    }

    fn reset_assumptions(&mut self) {
        self.assumptions.clear()
    }

    fn add_assumption_clause(
        &mut self,
        id: ClauseId,
        clause: &CaDiCaLClause,
        antecedents: &[ClauseId],
    ) {
        //#[cfg(feature = "verbose")]
        //{
        //    let proof = self.proof.as_mut().expect("expected proof");
        //    proof
        //        .comment(&"the next constraint is a core found by CaDiCaL")
        //        .expect("failed to write proof");
        //}
        let id = self.add_derived(id, true, clause, antecedents);
        self.core_id = Some(id);
    }
}

fn write_derived<ProofW, I>(
    proof: &mut Proof<ProofW>,
    _clause: &CaDiCaLClause,
    antecedents: I,
) -> AbsConstraintId
where
    ProofW: io::Write,
    I: IntoIterator<Item = AbsConstraintId, IntoIter: DoubleEndedIterator>,
{
    cfg_if::cfg_if! {
        if #[cfg(feature = "rup-hints")] {
            use pigeons::ConstraintId;
            proof.reverse_unit_prop(_clause, antecedents.into_iter().map(ConstraintId::from))
                .expect("failed to write proof")
        } else {
            use pigeons::{OperationLike, OperationSequence};
            let mut antecedents = antecedents.into_iter().rev();
            let Some(first) = antecedents.next() else {
                panic!("need antecedents for derived clause")
            };
            let derivation = antecedents.fold(OperationSequence::<rustsat::types::Var>::from(first), |der, id| {
                (der + id).saturate()
            });
            proof.operations(&derivation).expect("failed to write proof")
        }
    }
}

#[derive(Default, Debug)]
struct ConstraintMapper {
    map: Vec<AbsConstraintId>,
}

impl ConstraintMapper {
    pub fn add_clause(&mut self, id: AbsConstraintId) {
        self.map.push(id);
    }

    pub fn add_clause_checked(&mut self, id: AbsConstraintId, clause_id: ClauseId) {
        self.map.push(id);
        assert_eq!(u64::try_from(self.map.len()).unwrap(), clause_id.0);
    }

    pub fn map(&self, id: ClauseId) -> AbsConstraintId {
        self.map[usize::try_from(id.0 - 1).expect("`ClauseId` does not fit in `usize`")]
    }
}

pub struct CadicalCertCollector<'cadical, 'term, 'learn, ProofW: io::Write> {
    cadical: &'cadical mut CaDiCaL<'term, 'learn>,
    pt_handle: &'cadical ProofTracerHandle<CadicalTracer<ProofW>>,
}

impl<'cadical, 'term, 'learn, ProofW: io::Write>
    CadicalCertCollector<'cadical, 'term, 'learn, ProofW>
{
    pub fn new(
        cadical: &'cadical mut CaDiCaL<'term, 'learn>,
        pt_handle: &'cadical ProofTracerHandle<CadicalTracer<ProofW>>,
    ) -> Self {
        Self { cadical, pt_handle }
    }
}

impl<ProofW: io::Write + 'static> CollectCertClauses for CadicalCertCollector<'_, '_, '_, ProofW>
where
    ProofW: io::Write,
{
    fn extend_cert_clauses<T>(&mut self, cl_iter: T) -> Result<(), rustsat::OutOfMemory>
    where
        T: IntoIterator<Item = (Clause, AbsConstraintId)>,
    {
        for (cl, id) in cl_iter.into_iter() {
            self.add_cert_clause(cl, id)?;
        }
        Ok(())
    }

    fn add_cert_clause(
        &mut self,
        cl: Clause,
        id: AbsConstraintId,
    ) -> Result<(), rustsat::OutOfMemory> {
        let tracer = self.cadical.proof_tracer_mut(self.pt_handle);
        tracer.cmap.add_clause(id);
        self.cadical.add_clause(cl)
    }
}

// Passthrough
impl<ProofW: io::Write> CollectClauses for CadicalCertCollector<'_, '_, '_, ProofW> {
    fn n_clauses(&self) -> usize {
        self.cadical.n_clauses()
    }

    fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), rustsat::OutOfMemory>
    where
        T: IntoIterator<Item = Clause>,
    {
        self.cadical.extend_clauses(cl_iter)
    }

    fn add_clause(&mut self, cl: Clause) -> Result<(), rustsat::OutOfMemory> {
        self.cadical.add_clause(cl)
    }
}
