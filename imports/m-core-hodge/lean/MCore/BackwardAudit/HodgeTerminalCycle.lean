import MCore.BackwardAudit.HodgeGapSignature

namespace MCore.BackwardAudit

/--
Terminal-cycle presentation names.  These are not assumed equal by definition;
their equivalence is proved from the existing certified terminal reductions.
-/
inductive HodgeTerminalNode where
  | endpoint
  | gap
  | habitant
  | inhabitant

def HodgeTerminalSemantics
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeTerminalNode → Prop
  | .endpoint => ConcreteAlgebraicityPayload M
  | .gap => HodgeLastBit M
  | .habitant => HodgeOppositionPayload M
  | .inhabitant => normalizeHodgePresentation M .lastBit

theorem terminal_endpoint_gap
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeTerminalSemantics M .endpoint ↔
      HodgeTerminalSemantics M .gap :=
  (hodge_last_bit_iff_concrete_payload M).symm

theorem terminal_gap_habitant
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeTerminalSemantics M .gap ↔
      HodgeTerminalSemantics M .habitant := by
  exact (hodge_last_bit_iff_concrete_payload M).trans
    (hodge_opposition_payload_iff_concrete_payload M).symm

theorem terminal_habitant_inhabitant
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeTerminalSemantics M .habitant ↔
      HodgeTerminalSemantics M .inhabitant := by
  exact (hodge_opposition_payload_iff_concrete_payload M).trans
    (hodge_last_bit_iff_concrete_payload M).symm

theorem terminal_inhabitant_endpoint
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeTerminalSemantics M .inhabitant ↔
      HodgeTerminalSemantics M .endpoint :=
  hodge_last_bit_iff_concrete_payload M

/-- Full certified terminal wheel. -/
theorem hodge_terminal_cycle
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    (HodgeTerminalSemantics M .endpoint ↔ HodgeTerminalSemantics M .gap) ∧
    (HodgeTerminalSemantics M .gap ↔ HodgeTerminalSemantics M .habitant) ∧
    (HodgeTerminalSemantics M .habitant ↔ HodgeTerminalSemantics M .inhabitant) ∧
    (HodgeTerminalSemantics M .inhabitant ↔ HodgeTerminalSemantics M .endpoint) :=
  ⟨terminal_endpoint_gap M,
   terminal_gap_habitant M,
   terminal_habitant_inhabitant M,
   terminal_inhabitant_endpoint M⟩

/--
A recurrence proof that merely transports truth around the terminal wheel
cannot create truth from nothing.  If Endpoint is false, all wheel nodes are
false as well.
-/
theorem terminal_cycle_preserves_uninhabited
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (h : ¬ HodgeTerminalSemantics M .endpoint) :
    (¬ HodgeTerminalSemantics M .gap) ∧
    (¬ HodgeTerminalSemantics M .habitant) ∧
    (¬ HodgeTerminalSemantics M .inhabitant) := by
  constructor
  · intro hg
    exact h ((terminal_endpoint_gap M).2 hg)
  constructor
  · intro hh
    exact h ((hodge_opposition_payload_iff_concrete_payload M).1 hh)
  · intro hi
    exact h ((terminal_inhabitant_endpoint M).1 hi)

/--
Conversely, any independently produced inhabitant at any node closes Endpoint.
This is the exact formal meaning of the user's terminal-wheel intuition.
-/
theorem any_terminal_inhabitant_closes_endpoint
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (n : HodgeTerminalNode)
    (h : HodgeTerminalSemantics M n) :
    ConcreteAlgebraicityPayload M := by
  cases n with
  | endpoint => exact h
  | gap => exact (hodge_last_bit_iff_concrete_payload M).1 h
  | habitant => exact (hodge_opposition_payload_iff_concrete_payload M).1 h
  | inhabitant => exact (hodge_last_bit_iff_concrete_payload M).1 h

#print axioms MCore.BackwardAudit.hodge_terminal_cycle
#print axioms MCore.BackwardAudit.terminal_cycle_preserves_uninhabited
#print axioms MCore.BackwardAudit.any_terminal_inhabitant_closes_endpoint

end MCore.BackwardAudit
