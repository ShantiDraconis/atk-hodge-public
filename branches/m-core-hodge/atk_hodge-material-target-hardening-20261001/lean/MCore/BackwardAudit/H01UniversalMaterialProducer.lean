import MCore.BackwardAudit.ConcreteHodgeMaterialTarget
import MCore.BackwardAudit.H01MinimalForwardPayload

namespace MCore.BackwardAudit

/--
Universal material producer for the compressed H01 route.

For every concrete endpoint input X,p,alpha it supplies exactly the already
audited minimal forward payload.  Nonempty geometry and the span adapter are
kept explicit so the result cannot close vacuously.
-/
structure H01UniversalMaterialProducer
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  nonemptyVariety : Nonempty G.Variety
  spanAdapter : CycleSpanAdapter G M
  pointwise :
    ∀ (X : G.Variety) (p : Nat)
      (alpha : G.CohomologyQ X (2 * p)),
      H01MinimalForwardPayload G M X p alpha

/-- The universal H01 producer yields the literal concrete algebraicity payload. -/
theorem h01UniversalMaterialProducer_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : H01UniversalMaterialProducer G M) :
    ConcreteAlgebraicityPayload M := by
  intro X p alpha hX hAlpha
  have hSemantic : G.inCycleClassSpan p alpha := by
    exact
      h01_minimal_forward_payload_closes_pointwise
        P.spanAdapter (P.pointwise X p alpha) hX hAlpha
  exact (P.spanAdapter.span_iff alpha).mp hSemantic

/-- No remaining adapter gap: the universal H01 producer builds the hardened
material target on the same G and M. -/
def H01UniversalMaterialProducer.toMaterialTarget
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : H01UniversalMaterialProducer G M) :
    ConcreteHodgeMaterialTarget G M where
  nonemptyVariety := P.nonemptyVariety
  spanAdapter := P.spanAdapter
  algebraicity := h01UniversalMaterialProducer_payload P

/-- Therefore the universal H01 producer closes the same graded Hodge endpoint. -/
theorem h01UniversalMaterialProducer_closes
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : H01UniversalMaterialProducer G M) :
    GradedRationalHodgeConjecture G :=
  concreteHodgeMaterialTarget_closes P.toMaterialTarget

#print axioms MCore.BackwardAudit.h01UniversalMaterialProducer_payload
#print axioms MCore.BackwardAudit.H01UniversalMaterialProducer.toMaterialTarget
#print axioms MCore.BackwardAudit.h01UniversalMaterialProducer_closes

end MCore.BackwardAudit
