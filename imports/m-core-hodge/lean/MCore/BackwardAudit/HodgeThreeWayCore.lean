import Mathlib.Tactic
import MCore.BackwardAudit.HodgeTerminalCycleCountermodel

namespace MCore.BackwardAudit

/--
Three-way terminal code:
0 = Gap, 1 = Habitant, 2 = Inhabitant.
All three are existing terminal presentations; no new mathematical parameter
or geometric hypothesis is introduced.
-/
def HodgeTriStateSemantics
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    Fin 3 → Prop
  | ⟨0, _⟩ => HodgeTerminalSemantics M .gap
  | ⟨1, _⟩ => HodgeTerminalSemantics M .habitant
  | ⟨2, _⟩ => HodgeTerminalSemantics M .inhabitant
  | ⟨n+3, h⟩ => False.elim (Nat.not_lt_zero _ (Nat.lt_of_add_lt_add_right h))

theorem tristate_zero_iff_endpoint
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeTriStateSemantics M 0 ↔ ConcreteAlgebraicityPayload M :=
  hodge_last_bit_iff_concrete_payload M

theorem tristate_one_iff_endpoint
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeTriStateSemantics M 1 ↔ ConcreteAlgebraicityPayload M :=
  hodge_opposition_payload_iff_concrete_payload M

theorem tristate_two_iff_endpoint
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeTriStateSemantics M 2 ↔ ConcreteAlgebraicityPayload M :=
  hodge_last_bit_iff_concrete_payload M

/--
All three terminal directions converge propositionally to the same core.
-/
theorem hodge_three_way_core_convergence
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    (HodgeTriStateSemantics M 0 ↔ ConcreteAlgebraicityPayload M) ∧
    (HodgeTriStateSemantics M 1 ↔ ConcreteAlgebraicityPayload M) ∧
    (HodgeTriStateSemantics M 2 ↔ ConcreteAlgebraicityPayload M) :=
  ⟨tristate_zero_iff_endpoint M,
   tristate_one_iff_endpoint M,
   tristate_two_iff_endpoint M⟩

/--
Any inhabited one of the three terminal states closes the endpoint.
-/
theorem hodge_three_way_any_inhabited_closes
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (i : Fin 3)
    (h : HodgeTriStateSemantics M i) :
    ConcreteAlgebraicityPayload M := by
  fin_cases i
  · exact (tristate_zero_iff_endpoint M).1 h
  · exact (tristate_one_iff_endpoint M).1 h
  · exact (tristate_two_iff_endpoint M).1 h

/--
Decisive firewall: the three-way convergence law itself does not produce the
core.  The certified countermodel has the full convergence pattern while its
endpoint is false.
-/
theorem hodge_three_way_convergence_does_not_imply_endpoint :
    ¬ (
      ((HodgeTriStateSemantics codimZeroCounterexampleM 0 ↔
          ConcreteAlgebraicityPayload codimZeroCounterexampleM) ∧
       (HodgeTriStateSemantics codimZeroCounterexampleM 1 ↔
          ConcreteAlgebraicityPayload codimZeroCounterexampleM) ∧
       (HodgeTriStateSemantics codimZeroCounterexampleM 2 ↔
          ConcreteAlgebraicityPayload codimZeroCounterexampleM))
      →
      ConcreteAlgebraicityPayload codimZeroCounterexampleM
    ) := by
  intro h
  exact countermodel_endpoint_false
    (h (hodge_three_way_core_convergence codimZeroCounterexampleM))

#print axioms MCore.BackwardAudit.hodge_three_way_core_convergence
#print axioms MCore.BackwardAudit.hodge_three_way_any_inhabited_closes
#print axioms MCore.BackwardAudit.hodge_three_way_convergence_does_not_imply_endpoint

end MCore.BackwardAudit
