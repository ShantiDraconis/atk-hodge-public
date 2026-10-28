import MCore.BackwardAudit.HodgeRatioCollapse

namespace MCore.BackwardAudit

/--
Terminal open/closed/opposed presentations of the same Hodge endpoint.
These are existing certified presentations, not new mathematical assumptions.
-/
def HodgeOpenMath
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  HodgeLastBit M

def HodgeClosedMath
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ConcreteAlgebraicityPayload M

def HodgeNegativeOpenMath
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  HodgeOppositionPayload M

theorem open_math_iff_closed_math
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeOpenMath M ↔ HodgeClosedMath M :=
  hodge_last_bit_iff_concrete_payload M

theorem closed_math_iff_negative_open_math
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeClosedMath M ↔ HodgeNegativeOpenMath M :=
  (hodge_opposition_payload_iff_concrete_payload M).symm

theorem negative_open_math_iff_open_math
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeNegativeOpenMath M ↔ HodgeOpenMath M := by
  exact (hodge_opposition_payload_iff_concrete_payload M).trans
    (hodge_last_bit_iff_concrete_payload M).symm

/--
Certified terminal duality wheel:
OPEN_MATH ↔ CLOSED_MATH ↔ (-OPEN_MATH) ↔ OPEN_MATH.
-/
theorem hodge_open_closed_duality_cycle
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    (HodgeOpenMath M ↔ HodgeClosedMath M) ∧
    (HodgeClosedMath M ↔ HodgeNegativeOpenMath M) ∧
    (HodgeNegativeOpenMath M ↔ HodgeOpenMath M) :=
  ⟨open_math_iff_closed_math M,
   closed_math_iff_negative_open_math M,
   negative_open_math_iff_open_math M⟩

/--
Any inhabited presentation in the open/closed/opposed wheel closes the endpoint.
-/
theorem any_open_closed_duality_inhabitant_closes
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (h : HodgeOpenMath M ∨ HodgeClosedMath M ∨ HodgeNegativeOpenMath M) :
    ConcreteAlgebraicityPayload M := by
  rcases h with hO | hC | hN
  · exact (open_math_iff_closed_math M).1 hO
  · exact hC
  · exact (hodge_opposition_payload_iff_concrete_payload M).1 hN

/--
Decisive fail-closed test:
the duality cycle itself can hold in the certified countermodel while CLOSED_MATH
is false.  Therefore equality/equivalence of the terminal presentations does not
by itself manufacture an inhabitant.
-/
theorem open_closed_duality_does_not_imply_closed :
    ¬ (
      ((HodgeOpenMath codimZeroCounterexampleM ↔
          HodgeClosedMath codimZeroCounterexampleM) ∧
       (HodgeClosedMath codimZeroCounterexampleM ↔
          HodgeNegativeOpenMath codimZeroCounterexampleM) ∧
       (HodgeNegativeOpenMath codimZeroCounterexampleM ↔
          HodgeOpenMath codimZeroCounterexampleM))
      →
      HodgeClosedMath codimZeroCounterexampleM
    ) := by
  intro h
  exact countermodel_endpoint_false
    (h (hodge_open_closed_duality_cycle codimZeroCounterexampleM))

#print axioms MCore.BackwardAudit.hodge_open_closed_duality_cycle
#print axioms MCore.BackwardAudit.any_open_closed_duality_inhabitant_closes
#print axioms MCore.BackwardAudit.open_closed_duality_does_not_imply_closed

end MCore.BackwardAudit
