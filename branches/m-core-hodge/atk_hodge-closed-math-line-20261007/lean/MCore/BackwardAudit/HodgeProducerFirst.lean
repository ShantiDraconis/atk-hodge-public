import MCore.BackwardAudit.H01MinimalForwardPayload
import MCore.BackwardAudit.HodgeHabitant

namespace MCore.BackwardAudit

/-!
# Producer-first extraction for the Hodge inhabitant

No new mathematical hypothesis is introduced here.  The purpose of this file
is to expose the exact producer already implicit in the certified R1/R2/R3
pipeline: once descent, fiber-cycle production, and back-transport are genuine
inputs, a concrete cycle combination is computed by extracting the witness of
the existing kernel theorem.

The remaining OPEN_MATH is therefore not another wrapper around the endpoint.
It is the production of the required R1/R2/R3 data for every admissible input,
with R2 carrying the first actual algebraic-cycle witness.
-/

/-- Exact local producer type. -/
abbrev HodgeExactLocalProducer
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hAlpha : G.isTypePP p alpha}
    (S : SpreadData G X p alpha hX hAlpha)
    (D : R1DescentPointContract S) :=
  R2PointProductionContract M S D →
  R3TransportContract M S →
  CycleCombination G M X p

/-- Minimal exact producer: extract the concrete cycle combination from the
already-certified R1d+R2+R3 witness theorem. -/
noncomputable def hodgeExactLocalProducer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hAlpha : G.isTypePP p alpha}
    {S : SpreadData G X p alpha hX hAlpha}
    (D : R1DescentPointContract S)
    (R2 : R2PointProductionContract M S D)
    (R3 : R3TransportContract M S) :
    CycleCombination G M X p :=
  Classical.choose (r1d_r2_r3_yields_concrete_witness D R2 R3)

/-- Verifier for the exact producer. -/
theorem hodgeExactLocalProducer_verified
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hAlpha : G.isTypePP p alpha}
    {S : SpreadData G X p alpha hX hAlpha}
    (D : R1DescentPointContract S)
    (R2 : R2PointProductionContract M S D)
    (R3 : R3TransportContract M S) :
    (hodgeExactLocalProducer D R2 R3).eval M = alpha :=
  Classical.choose_spec (r1d_r2_r3_yields_concrete_witness D R2 R3)

/-- A pointwise H01 payload yields an actual cycle combination, not merely a
status or semantic proposition. -/
noncomputable def hodgeCycleOfMinimalForwardPayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    (P : H01MinimalForwardPayload G M X p alpha)
    (hX : G.isSmoothProjective X)
    (hAlpha : G.isTypePP p alpha) :
    CycleCombination G M X p := by
  rcases P.run hX hAlpha with ⟨S, D, W⟩
  have hR3 : Nonempty (R3TransportContract M S) :=
    (r3_contract_iff_variational_algebraicity).2 W.r3
  exact hodgeExactLocalProducer D W.r2 (Classical.choice hR3)

/-- The extracted cycle verifies the target class exactly. -/
theorem hodgeCycleOfMinimalForwardPayload_verified
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    (P : H01MinimalForwardPayload G M X p alpha)
    (hX : G.isSmoothProjective X)
    (hAlpha : G.isTypePP p alpha) :
    (hodgeCycleOfMinimalForwardPayload P hX hAlpha).eval M = alpha := by
  simp only [hodgeCycleOfMinimalForwardPayload]
  rcases P.run hX hAlpha with ⟨S, D, W⟩
  have hR3 : Nonempty (R3TransportContract M S) :=
    (r3_contract_iff_variational_algebraicity).2 W.r3
  exact hodgeExactLocalProducer_verified D W.r2 (Classical.choice hR3)

/-- Universal H01 data directly inhabits HodgeHabitant by the exact producer. -/
noncomputable def hodgeHabitantOfUniversalForward
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : ∀ (X : G.Variety) (p : Nat)
      (alpha : G.CohomologyQ X (2 * p)),
      H01MinimalForwardPayload G M X p alpha) :
    HodgeHabitant M :=
  {
    realize := by
      intro X p alpha hX hAlpha
      let Z := hodgeCycleOfMinimalForwardPayload (P X p alpha) hX hAlpha
      exact ⟨Z, hodgeCycleOfMinimalForwardPayload_verified
        (P X p alpha) hX hAlpha⟩
  }

#print axioms MCore.BackwardAudit.hodgeExactLocalProducer
#print axioms MCore.BackwardAudit.hodgeExactLocalProducer_verified
#print axioms MCore.BackwardAudit.hodgeCycleOfMinimalForwardPayload
#print axioms MCore.BackwardAudit.hodgeCycleOfMinimalForwardPayload_verified
#print axioms MCore.BackwardAudit.hodgeHabitantOfUniversalForward

end MCore.BackwardAudit
