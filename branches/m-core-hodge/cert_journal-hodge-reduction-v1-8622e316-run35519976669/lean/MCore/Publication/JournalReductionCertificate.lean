import MCore.BackwardAudit.R2FiberAlgebraicityBoundary
import MCore.BackwardAudit.R3SpecializationBoundary
import MCore.K20

namespace MCore.Publication

open MCore.BackwardAudit

/-!
# Publication-grade conditional reduction certificate

This module states the strongest theorem currently exportable from the
R1d/R2/R3 chain without claiming the rational Hodge conjecture itself.

The hypothesis preserves the full dependency order:
  forall X, p, alpha, hX, hAlpha,
  there exists a spread S,
  there exists a Qbar Hodge-point witness D,
  R2 fiber algebraicity holds at D,
  and the R3 specialization payload holds for S.

No candidate is moved outside these quantifiers.
-/

/-- Exact pointwise geometric payload still required by the current reduction. -/
def JournalPointwiseGeometricPayload
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety)
    (p : Nat)
    (α : G.CohomologyQ X (2 * p))
    (hX : G.isSmoothProjective X)
    (hα : G.isTypePP p α),
    ∃ S : SpreadData G X p α hX hα,
      ∃ D : R1DescentPointContract S,
        R2FiberAlgebraicityTarget M D ∧
        R3SpecializationPayload M S

/-- Main publishable reduction theorem:
    the explicit R1d/R2/R3 geometric payload implies the exact concrete
    algebraicity endpoint.  The proof uses no choice extraction and no
    conjectural axiom. -/
theorem journal_geometric_payload_implies_concrete_algebraicity
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : JournalPointwiseGeometricPayload G M) :
    ConcreteAlgebraicityPayload M := by
  intro X p α hX hα
  rcases H X p α hX hα with ⟨S, D, hR2, hR3⟩
  have nR2 : Nonempty (R2PointProductionContract M S D) :=
    r2_nonempty_of_fiber_algebraicity D hR2
  have nR3 : Nonempty (R3TransportContract M S) :=
    r3_payload_closes_transport hR3
  rcases nR2 with ⟨R2⟩
  rcases nR3 with ⟨R3⟩
  exact r1d_r2_r3_yields_concrete_witness D R2 R3

/-- At a supplied certification boundary, the same geometric payload implies
    the graded rational Hodge statement.  This is a conditional reduction,
    not an unconditional proof of Hodge. -/
theorem journal_geometric_payload_implies_hodge
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (H : JournalPointwiseGeometricPayload G M) :
    GradedRationalHodgeConjecture G :=
  boundary_and_payload_imply_hodge B
    (journal_geometric_payload_implies_concrete_algebraicity H)

/-- The exact local theorem at one endpoint input. -/
theorem journal_local_r1d_r2_r3_closure
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S)
    (hR2 : R2FiberAlgebraicityTarget M D)
    (hR3 : R3SpecializationPayload M S) :
    InConcreteCycleSpan M α := by
  have nR2 := r2_nonempty_of_fiber_algebraicity D hR2
  have nR3 := r3_payload_closes_transport hR3
  rcases nR2 with ⟨R2⟩
  rcases nR3 with ⟨R3⟩
  exact r1d_r2_r3_yields_concrete_witness D R2 R3

inductive JournalCertificateStatus where
  | provedReduction
  | openMathematics
  deriving Repr, DecidableEq

structure JournalCertificateFrontier where
  localReduction : JournalCertificateStatus
  universalReduction : JournalCertificateStatus
  r1dQbarPoint : JournalCertificateStatus
  r2FiberAlgebraicity : JournalCertificateStatus
  r3SpecializationCompatibility : JournalCertificateStatus
  hodge : SignatureStatus
  mayExportReductionTheorem : Bool
  mayExportHodgeProof : Bool

def journalCertificateFrontier : JournalCertificateFrontier :=
  {
    localReduction := .provedReduction
    universalReduction := .provedReduction
    r1dQbarPoint := .openMathematics
    r2FiberAlgebraicity := .openMathematics
    r3SpecializationCompatibility := .openMathematics
    hodge := .openBridge
    mayExportReductionTheorem := true
    mayExportHodgeProof := false
  }

theorem journal_reduction_exportable :
    journalCertificateFrontier.mayExportReductionTheorem = true := rfl

theorem journal_hodge_not_exportable :
    journalCertificateFrontier.mayExportHodgeProof = false := rfl

theorem journal_hodge_still_open :
    journalCertificateFrontier.hodge = .openBridge := rfl

#print axioms MCore.Publication.journal_geometric_payload_implies_concrete_algebraicity
#print axioms MCore.Publication.journal_geometric_payload_implies_hodge
#print axioms MCore.Publication.journal_local_r1d_r2_r3_closure
#print axioms MCore.Publication.journal_reduction_exportable
#print axioms MCore.Publication.journal_hodge_not_exportable
#print axioms MCore.Publication.journal_hodge_still_open

end MCore.Publication
