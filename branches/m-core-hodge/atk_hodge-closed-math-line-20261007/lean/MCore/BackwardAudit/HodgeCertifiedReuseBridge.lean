import MCore.BackwardAudit.H01MinimalForwardPayload
import MCore.BackwardAudit.HodgeCodimTrisection

namespace MCore.BackwardAudit

/-!
# Certified historical reuse bridge

This module connects the already-certified H01 forward chain
(R1 descent point + R2 point production + R3 variational algebraicity)
to the currently isolated higher-codimension terminal.

Historical certified provenance consumed by H01 includes the R1d/R2/R3 family.
This file does not manufacture any missing mathematical witness.
-/

/-- Exact higher-codimension H01 producer.  This is the only new mathematical
input required by the historical forward route once p=0 and p=1 are handled. -/
def HigherCodimH01ForwardPayload
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) : Type 1 :=
  ∀ (X : G.Variety) (p : Nat) (alpha : G.CohomologyQ X (2 * p)),
    2 ≤ p →
    H01MinimalForwardPayload G M X p alpha

/-- Reuse theorem: every higher-codimension H01 payload is transported through
the certified R1/R2/R3 chain to the concrete higher-codimension endpoint. -/
theorem higherCodim_of_h01_forward
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (H : HigherCodimH01ForwardPayload G M) :
    HigherCodimensionAlgebraicityPayload M := by
  intro X p alpha hp hX hAlpha
  have hSemantic :
      GradedAlgebraicityAt G X p alpha :=
    h01_minimal_forward_payload_closes_pointwise A (H X p alpha hp)
  exact (A.span_iff alpha).1 (hSemantic hX hAlpha)

/-- Full endpoint activation through the certified historical chain.
All remaining assumptions are explicit in the type. -/
theorem hodge_of_certified_h01_reuse
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (A : CycleSpanAdapter G M)
    (h0 : CodimensionZeroAlgebraicityPayload M)
    (h1 : MCore.CodimensionOneAlgebraicityPayload M)
    (H : HigherCodimH01ForwardPayload G M) :
    GradedRationalHodgeConjecture G := by
  exact (hodge_iff_higher_given_boundary_low_codim B h0 h1).2
    (higherCodim_of_h01_forward A H)

/-- Exact characterization of what the certified historical route still lacks:
the endpoint is equivalent to the higher-codimension H01 producer only when the
reverse implication is independently supplied.  We deliberately do not assert
that reverse implication here. -/
theorem certified_h01_forward_is_sufficient
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (A : CycleSpanAdapter G M)
    (h0 : CodimensionZeroAlgebraicityPayload M)
    (h1 : MCore.CodimensionOneAlgebraicityPayload M) :
    HigherCodimH01ForwardPayload G M →
      GradedRationalHodgeConjecture G := by
  intro H
  exact hodge_of_certified_h01_reuse B A h0 h1 H

#print axioms MCore.BackwardAudit.higherCodim_of_h01_forward
#print axioms MCore.BackwardAudit.hodge_of_certified_h01_reuse
#print axioms MCore.BackwardAudit.certified_h01_forward_is_sufficient

end MCore.BackwardAudit
