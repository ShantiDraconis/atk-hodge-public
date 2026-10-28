import MCore.K13
import MCore.Frontier.CandidateBridge

namespace HodgeBackwardAuditR1

open MCore
open MCore.Frontier

/-
R1 audit target.

Important quantifier distinction:

  Pointwise/V2.1:
    ∀ X p α, ∃ family, spread α family

  Strong uniform:
    ∀ X p, ∃ family, ∀ α, spread α family

The first still permits the chosen family to depend on α.  The second does not.
No existence theorem is asserted in this file.
-/

/-- Abstract algebraic spread family attached to one variety X.
    The proposition fields are obligations; this structure does not manufacture
    proofs of them. -/
structure AlgebraicSpreadFamily
    (G : GradedRationalHodgeData) (X : G.Variety) where
  Base : Type
  TotalSpace : Type
  s0 : Base
  definedOverQbar : Prop
  fiberAtBaseIdentifiedWithX : Prop
  smoothProjectiveFamily : Prop

/-- Cohomological spread data for one class α in a fixed family.
    We deliberately distinguish a flat/local-system extension from an
    algebraic-cycle witness.  No algebraicity of α is a field. -/
structure ClassSpreadData
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    (F : AlgebraicSpreadFamily G X)
    (p : Nat)
    (α : G.CohomologyQ X (2 * p)) where
  SectionCarrier : Type
  flatSection : SectionCarrier
  isFlatSection : Prop
  restrictsAtBaseToAlpha : Prop
  hodgeLocusControlled : Prop

/-- The exact quantifier order written in the proposed V2.1.
    Despite the name "uniform spread", this remains pointwise in α:
    F occurs after α and may therefore depend on α. -/
def R1_PointwiseV21 (G : GradedRationalHodgeData) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)),
    G.isSmoothProjective X →
    G.isTypePP p α →
    ∃ (F : AlgebraicSpreadFamily G X),
      F.definedOverQbar ∧
      F.fiberAtBaseIdentifiedWithX ∧
      F.smoothProjectiveFamily ∧
      ∃ (A : ClassSpreadData F p α),
        A.isFlatSection ∧
        A.restrictsAtBaseToAlpha ∧
        A.hodgeLocusControlled

/-- Strong uniformity in α: for fixed X and p, choose the algebraic family
    before seeing α.  Individual flat sections may still depend on α. -/
def R1_UniformFamily (G : GradedRationalHodgeData) : Prop :=
  ∀ (X : G.Variety) (p : Nat),
    G.isSmoothProjective X →
    ∃ (F : AlgebraicSpreadFamily G X),
      F.definedOverQbar ∧
      F.fiberAtBaseIdentifiedWithX ∧
      F.smoothProjectiveFamily ∧
      ∀ (α : G.CohomologyQ X (2 * p)),
        G.isTypePP p α →
        ∃ (A : ClassSpreadData F p α),
          A.isFlatSection ∧
          A.restrictsAtBaseToAlpha ∧
          A.hodgeLocusControlled

/-- Strong uniformity implies the pointwise V2.1 shape by reusing the same
    family.  This is pure quantifier wiring. -/
theorem uniformFamily_implies_pointwiseV21
    {G : GradedRationalHodgeData}
    (h : R1_UniformFamily G) :
    R1_PointwiseV21 G := by
  intro X p α hX hpp
  obtain ⟨F, hQ, hFiber, hFam, hAll⟩ := h X p hX
  obtain ⟨A, hFlat, hBase, hLocus⟩ := hAll α hpp
  exact ⟨F, hQ, hFiber, hFam, A, hFlat, hBase, hLocus⟩

/-- Minimal semantic adapter from a concrete R1 witness to the old abstract
    CandidateBridge spread proposition.  Supplying this adapter is external
    geometry/formalization work; it is not proved here. -/
structure R1ToCandidateAdapter
    (G : GradedRationalHodgeData)
    (V : AlgebraicityCandidateVocabulary) where
  pointwiseToCandidate : R1_PointwiseV21 G → C_Spread V

theorem r1_feeds_candidate_given_adapter
    {G : GradedRationalHodgeData}
    {V : AlgebraicityCandidateVocabulary}
    (A : R1ToCandidateAdapter G V)
    (hR1 : R1_PointwiseV21 G) :
    C_Spread V :=
  A.pointwiseToCandidate hR1

/-- Fail-closed audit metadata.  The source contains only the specification and
    quantifier wiring; it does not assert R1. -/
inductive R1AuditStatus where
  | specificationOnly
  | externalClassicalPartial
  | openResidue
  | proved
  deriving Repr, DecidableEq

def r1PointwiseStatus : R1AuditStatus := .openResidue
def r1UniformFamilyStatus : R1AuditStatus := .openResidue

theorem r1_pointwise_not_promoted :
    r1PointwiseStatus = .openResidue := by
  rfl

theorem r1_uniform_not_promoted :
    r1UniformFamilyStatus = .openResidue := by
  rfl

#print axioms HodgeBackwardAuditR1.uniformFamily_implies_pointwiseV21
#print axioms HodgeBackwardAuditR1.r1_feeds_candidate_given_adapter
#print axioms HodgeBackwardAuditR1.r1_pointwise_not_promoted
#print axioms HodgeBackwardAuditR1.r1_uniform_not_promoted

end HodgeBackwardAuditR1
