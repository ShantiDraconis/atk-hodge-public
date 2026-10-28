import MCore.BackwardAudit.HodgeOppositionMincut

namespace MCore.BackwardAudit

/--
Meta-level normal form for the Hodge reduction architecture.

The normalizer forgets presentation and returns the unique terminal
mathematical proposition. Re-normalizing is definitionally idempotent.
-/
inductive HodgePresentation where
  | lastBit
  | concretePayload
  | oppositionPayload

def normalizeHodgePresentation
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgePresentation → Prop
  | .lastBit => HodgeLastBit M
  | .concretePayload => ConcreteAlgebraicityPayload M
  | .oppositionPayload => HodgeOppositionPayload M

theorem normalized_lastBit_eq_endpoint
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    normalizeHodgePresentation M .lastBit ↔
      ConcreteAlgebraicityPayload M :=
  hodge_last_bit_iff_concrete_payload M

theorem normalized_opposition_eq_endpoint
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    normalizeHodgePresentation M .oppositionPayload ↔
      ConcreteAlgebraicityPayload M :=
  hodge_opposition_payload_iff_concrete_payload M

/--
Every currently admitted terminal presentation is propositionally equivalent
to the same mathematical endpoint.
-/
theorem all_terminal_presentations_same_endpoint
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (p : HodgePresentation) :
    normalizeHodgePresentation M p ↔ ConcreteAlgebraicityPayload M := by
  cases p with
  | lastBit =>
      exact hodge_last_bit_iff_concrete_payload M
  | concretePayload =>
      rfl
  | oppositionPayload =>
      exact hodge_opposition_payload_iff_concrete_payload M

/--
No-reopen fixed point: once reduced to the endpoint, selecting any of the
certified terminal presentations and reducing again yields the same endpoint.
This certifies architectural termination/normalization, not an inhabitant of
the endpoint proposition itself.
-/
theorem hodge_terminal_normal_form_fixed_point
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (p q : HodgePresentation) :
    normalizeHodgePresentation M p ↔ normalizeHodgePresentation M q := by
  exact (all_terminal_presentations_same_endpoint M p).trans
    (all_terminal_presentations_same_endpoint M q).symm

#print axioms MCore.BackwardAudit.all_terminal_presentations_same_endpoint
#print axioms MCore.BackwardAudit.hodge_terminal_normal_form_fixed_point

end MCore.BackwardAudit
