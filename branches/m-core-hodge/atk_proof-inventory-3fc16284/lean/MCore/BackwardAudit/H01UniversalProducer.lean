import MCore.BackwardAudit.H01MinimalForwardPayload

namespace MCore.BackwardAudit

/-- Exact universal producer left after the pointwise H01 reduction. -/
structure H01UniversalForwardPayload
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  run :
    ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)),
      H01MinimalForwardPayload G M X p α

/-- A universal minimal-forward payload discharges every pointwise
algebraicity obligation through the already-certified H01 reduction. -/
theorem h01_universal_forward_payload_closes_all
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (P : H01UniversalForwardPayload G M) :
    ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)),
      GradedAlgebraicityAt G X p α := by
  intro X p α
  exact h01_minimal_forward_payload_closes_pointwise A (P.run X p α)

#print axioms MCore.BackwardAudit.h01_universal_forward_payload_closes_all

end MCore.BackwardAudit
