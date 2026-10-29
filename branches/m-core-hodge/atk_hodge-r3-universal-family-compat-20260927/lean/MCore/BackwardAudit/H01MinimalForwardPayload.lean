import MCore.BackwardAudit.R2AfterR3
import MCore.BackwardAudit.R2FiberAlgebraicityBoundary
import MCore.BackwardAudit.R3CombinationMinimal

namespace MCore.BackwardAudit

/-- Local payload after a spread and descent point have been chosen. -/
structure H01LocalForwardPayload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (D : R1DescentPointContract S) where
  r2 : R2PointProductionContract M S D
  r3 : R3VariationalAlgebraicityPayload M S


/-- Exact local composition: concrete algebraicity at the selected R2 fiber,
together with a concrete pathwise specialization backend, supplies both fields
of H01LocalForwardPayload.  No extra variational hypothesis is introduced. -/
theorem h01_local_nonempty_of_fiber_and_atomic
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
    (A : DirectPathwiseSpecializationData M S) :
    Nonempty (H01LocalForwardPayload M S D) := by
  rcases r2_nonempty_of_fiber_algebraicity D hR2 with ⟨R2⟩
  exact ⟨{
    r2 := R2
    r3 := variational_payload_of_atomic_specialization A
  }⟩

/-- Forward-only H01 payload after the quantifier firewall:
for each input class we need only a spread/descent point, a cycle-production
witness at that point, and the exact variational algebraicity implication.
No atomwise specialization backend is required. -/
structure H01MinimalForwardPayload
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G)
    (X : G.Variety)
    (p : Nat)
    (α : G.CohomologyQ X (2 * p)) where
  run :
    ∀ (hX : G.isSmoothProjective X) (hα : G.isTypePP p α),
      Σ S : SpreadData G X p α hX hα,
        Σ D : R1DescentPointContract S,
          H01LocalForwardPayload M S D

/-- The compressed forward payload is sufficient for the concrete pointwise
Hodge endpoint. -/
theorem h01_minimal_forward_payload_closes_pointwise
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    (P : H01MinimalForwardPayload G M X p α) :
    GradedAlgebraicityAt G X p α := by
  intro hX hα
  rcases P.run hX hα with ⟨S, D, W⟩
  have hR3 : Nonempty (R3TransportContract M S) :=
    (r3_contract_iff_variational_algebraicity).2 W.r3
  rcases hR3 with ⟨R3⟩
  exact (A.span_iff α).2
    (r1d_r2_r3_yields_concrete_witness D W.r2 R3)

/-- Existing typed pipeline data maps into the minimal payload, so the new
frontier never asks for more than the old one. -/
def pointwisePipeline_to_minimal
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    (P : PointwiseTypedPipeline G M X p α) :
    H01MinimalForwardPayload G M X p α :=
  {
    run := by
      intro hX hα
      rcases P.run hX hα with ⟨S, D, W⟩
      refine ⟨S, D, ?_⟩
      exact {
        r2 := W.r2
        r3 := combination_payload_iff_variational_algebraicity.mp
          (r3_contract_implies_combination_payload W.r3)
      }
  }

#print axioms MCore.BackwardAudit.h01_local_nonempty_of_fiber_and_atomic
#print axioms MCore.BackwardAudit.h01_minimal_forward_payload_closes_pointwise

end MCore.BackwardAudit
