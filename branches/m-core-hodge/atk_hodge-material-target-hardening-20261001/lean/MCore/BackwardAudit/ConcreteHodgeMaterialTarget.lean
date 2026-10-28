import MCore.K18

namespace MCore

/--
Fail-closed material target for the Hodge lane.

The bare ConcreteAlgebraicityPayload can be vacuously inhabited when the
abstract graded model has no varieties.  This hardened target requires:
1. a nonempty geometric carrier;
2. the concrete cycle-span adapter;
3. the concrete algebraicity payload itself.

It still does not manufacture genuine algebraic geometry; it only removes the
empty-model and missing-adapter loopholes from the terminal proposition.
-/
structure ConcreteHodgeMaterialTarget
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  nonemptyVariety : Nonempty G.Variety
  spanAdapter : CycleSpanAdapter G M
  algebraicity : ConcreteAlgebraicityPayload M

/-- A hardened Hodge material target closes the semantic graded Hodge endpoint
for the same G and M. -/
theorem concreteHodgeMaterialTarget_closes
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (T : ConcreteHodgeMaterialTarget G M) :
    GradedRationalHodgeConjecture G :=
  (hodge_iff_concretePayload T.spanAdapter).2 T.algebraicity

/-- Projection to the previously isolated algebraicity payload. -/
theorem concreteHodgeMaterialTarget_implies_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (T : ConcreteHodgeMaterialTarget G M) :
    ConcreteAlgebraicityPayload M :=
  T.algebraicity

/-- The nonempty carrier is an explicit projection of every hardened target,
so an empty-variety model cannot satisfy the target. -/
theorem concreteHodgeMaterialTarget_has_variety
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (T : ConcreteHodgeMaterialTarget G M) :
    Nonempty G.Variety :=
  T.nonemptyVariety

#print axioms MCore.concreteHodgeMaterialTarget_closes
#print axioms MCore.concreteHodgeMaterialTarget_implies_payload
#print axioms MCore.concreteHodgeMaterialTarget_has_variety

end MCore
