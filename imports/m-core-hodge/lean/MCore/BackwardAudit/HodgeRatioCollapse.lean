import MCore.BackwardAudit.HodgeThreeWayCore

namespace MCore.BackwardAudit

/--
Terminal ratio states requested by the user:
0/1 and 0/2 are boundary presentations; 1/1 and 2/2 are their normalized
terminal images.  This is a symbolic transition system only; it introduces no
new Hodge hypothesis.
-/
inductive HodgeRatioState where
  | zeroOverOne
  | oneOverOne
  | zeroOverTwo
  | twoOverTwo

def HodgeRatioSemantics
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeRatioState → Prop
  | .zeroOverOne => HodgeTriStateSemantics M 0
  | .oneOverOne => HodgeTriStateSemantics M 1
  | .zeroOverTwo => HodgeTriStateSemantics M 0
  | .twoOverTwo => HodgeTriStateSemantics M 2

/-- 0/1 tends to 1/1 at the level of terminal logical content. -/
theorem zero_over_one_to_one_over_one
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeRatioSemantics M .zeroOverOne ↔
      HodgeRatioSemantics M .oneOverOne := by
  exact (tristate_zero_iff_endpoint M).trans
    (tristate_one_iff_endpoint M).symm

/-- 0/2 tends to 2/2 at the level of terminal logical content. -/
theorem zero_over_two_to_two_over_two
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeRatioSemantics M .zeroOverTwo ↔
      HodgeRatioSemantics M .twoOverTwo := by
  exact (tristate_zero_iff_endpoint M).trans
    (tristate_two_iff_endpoint M).symm

/-- Both normalized terminal images are endpoint-equivalent. -/
theorem normalized_ratio_images_hit_endpoint
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    (HodgeRatioSemantics M .oneOverOne ↔ ConcreteAlgebraicityPayload M) ∧
    (HodgeRatioSemantics M .twoOverTwo ↔ ConcreteAlgebraicityPayload M) :=
  ⟨tristate_one_iff_endpoint M, tristate_two_iff_endpoint M⟩

/--
If either normalized image is inhabited, the endpoint is closed.
-/
theorem normalized_ratio_inhabitant_closes
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (h :
      HodgeRatioSemantics M .oneOverOne ∨
      HodgeRatioSemantics M .twoOverTwo) :
    ConcreteAlgebraicityPayload M := by
  cases h with
  | inl h1 => exact (tristate_one_iff_endpoint M).1 h1
  | inr h2 => exact (tristate_two_iff_endpoint M).1 h2

/--
Fail-closed test: the two ratio-normalization laws can both hold in the
certified countermodel while the endpoint is false. Hence normalization laws
alone do not inhabit the endpoint.
-/
theorem ratio_normalization_does_not_imply_endpoint :
    ¬ (
      ((HodgeRatioSemantics codimZeroCounterexampleM .zeroOverOne ↔
          HodgeRatioSemantics codimZeroCounterexampleM .oneOverOne) ∧
       (HodgeRatioSemantics codimZeroCounterexampleM .zeroOverTwo ↔
          HodgeRatioSemantics codimZeroCounterexampleM .twoOverTwo))
      →
      ConcreteAlgebraicityPayload codimZeroCounterexampleM
    ) := by
  intro h
  exact countermodel_endpoint_false
    (h ⟨zero_over_one_to_one_over_one codimZeroCounterexampleM,
        zero_over_two_to_two_over_two codimZeroCounterexampleM⟩)

#print axioms MCore.BackwardAudit.zero_over_one_to_one_over_one
#print axioms MCore.BackwardAudit.zero_over_two_to_two_over_two
#print axioms MCore.BackwardAudit.normalized_ratio_inhabitant_closes
#print axioms MCore.BackwardAudit.ratio_normalization_does_not_imply_endpoint

end MCore.BackwardAudit
