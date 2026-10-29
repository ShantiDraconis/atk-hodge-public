import MCore.Hodge
import MCore.HodgeReduction

namespace MCore

/-
Material audit:
HodgeBridge stores the entire RationalHodgeConjecture as a field.
Thus bridge_implies_hodge is a projection/transport theorem, not a material producer.
-/
theorem hodgeBridge_is_endpoint_projection
    {D : HodgeSemanticData}
    (h : HodgeBridge D) :
    RationalHodgeConjecture D :=
  h.surjective_on_hodge_classes

/-
The pointwise reduction is a definitional equivalence. It narrows the endpoint,
but does not construct an algebraic cycle or prove rationalSpanOfCycles.
-/
theorem pointwise_reduction_is_transport
    {D : HodgeSemanticData}
    (h : PointwiseHodgeAlgebraicity D) :
    RationalHodgeConjecture D :=
  pointwise_closes_hodge h

#print axioms MCore.hodgeBridge_is_endpoint_projection
#print axioms MCore.pointwise_reduction_is_transport

end MCore
