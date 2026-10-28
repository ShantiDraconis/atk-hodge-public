import MCore.BackwardAudit.HodgeOpenClosedDuality

namespace MCore.BackwardAudit

/--
Distinct occurrences of the terminal states in the reduction cycle.
The labels are intentionally different even when their semantic propositions
are equivalent.
-/
inductive HodgeTerminalPhase where
  | openBefore
  | closedCenter
  | negativeOpen
  | openAfter
deriving DecidableEq, Repr

def HodgePhaseSemantics
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeTerminalPhase → Prop
  | .openBefore => HodgeOpenMath M
  | .closedCenter => HodgeClosedMath M
  | .negativeOpen => HodgeNegativeOpenMath M
  | .openAfter => HodgeOpenMath M

theorem open_phases_are_distinct_labels :
    HodgeTerminalPhase.openBefore ≠ HodgeTerminalPhase.openAfter := by
  decide

theorem open_phases_same_semantics
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgePhaseSemantics M .openBefore ↔
      HodgePhaseSemantics M .openAfter :=
  Iff.rfl

theorem closed_phase_reflexive
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgePhaseSemantics M .closedCenter ↔
      HodgePhaseSemantics M .closedCenter :=
  Iff.rfl

/--
Literal self-inequality of a proposition is impossible.
This separates phase-distinctness from semantic self-inequality.
-/
theorem open_math_not_self_unequal
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    ¬ (HodgeOpenMath M ≠ HodgeOpenMath M) := by
  intro h
  exact h rfl

theorem closed_math_not_self_unequal
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    ¬ (HodgeClosedMath M ≠ HodgeClosedMath M) := by
  intro h
  exact h rfl

/--
Distinct cycle positions can carry equivalent endpoint semantics.
-/
theorem phase_distinctness_with_terminal_equivalence
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeTerminalPhase.openBefore ≠ HodgeTerminalPhase.openAfter ∧
    (HodgePhaseSemantics M .openBefore ↔ HodgeClosedMath M) ∧
    (HodgeClosedMath M ↔ HodgePhaseSemantics M .negativeOpen) ∧
    (HodgePhaseSemantics M .negativeOpen ↔ HodgePhaseSemantics M .openAfter) :=
  ⟨open_phases_are_distinct_labels,
   open_math_iff_closed_math M,
   closed_math_iff_negative_open_math M,
   negative_open_math_iff_open_math M⟩

/--
Even phase-distinctness plus the complete terminal equivalence cycle does not
manufacture endpoint truth in the certified countermodel.
-/
theorem phase_distinct_cycle_does_not_imply_closed :
    ¬ (
      (HodgeTerminalPhase.openBefore ≠ HodgeTerminalPhase.openAfter ∧
       (HodgePhaseSemantics codimZeroCounterexampleM .openBefore ↔
          HodgeClosedMath codimZeroCounterexampleM) ∧
       (HodgeClosedMath codimZeroCounterexampleM ↔
          HodgePhaseSemantics codimZeroCounterexampleM .negativeOpen) ∧
       (HodgePhaseSemantics codimZeroCounterexampleM .negativeOpen ↔
          HodgePhaseSemantics codimZeroCounterexampleM .openAfter))
      →
      HodgeClosedMath codimZeroCounterexampleM
    ) := by
  intro h
  exact countermodel_endpoint_false
    (h (phase_distinctness_with_terminal_equivalence codimZeroCounterexampleM))

#print axioms MCore.BackwardAudit.open_phases_are_distinct_labels
#print axioms MCore.BackwardAudit.open_math_not_self_unequal
#print axioms MCore.BackwardAudit.closed_math_not_self_unequal
#print axioms MCore.BackwardAudit.phase_distinctness_with_terminal_equivalence
#print axioms MCore.BackwardAudit.phase_distinct_cycle_does_not_imply_closed

end MCore.BackwardAudit
