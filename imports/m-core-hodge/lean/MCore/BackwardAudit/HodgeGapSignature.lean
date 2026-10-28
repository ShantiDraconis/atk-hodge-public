import MCore.BackwardAudit.HodgeTerminalNormalForm

namespace MCore.BackwardAudit

/--
Certified signature of the terminal Hodge gap.

The gap is not a new proposition beyond the endpoint. It is the stable
normal-form behavior that every admitted terminal presentation reduces to the
same endpoint and reopening among those presentations yields no new logical
content.
-/
structure HodgeGapSignature
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop where
  endpoint_unique :
    ∀ p : HodgePresentation,
      normalizeHodgePresentation M p ↔ ConcreteAlgebraicityPayload M
  reopen_fixed_point :
    ∀ p q : HodgePresentation,
      normalizeHodgePresentation M p ↔ normalizeHodgePresentation M q

def hodgeGapSignature
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeGapSignature M :=
  {
    endpoint_unique := all_terminal_presentations_same_endpoint M
    reopen_fixed_point := hodge_terminal_normal_form_fixed_point M
  }

/--
The terminal gap signature and the terminal endpoint have the same normal form.
This is a closure theorem for the reduction architecture.
-/
theorem hodge_gap_signature_closed_normal_form
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    Nonempty (HodgeGapSignature M) :=
  ⟨hodgeGapSignature M⟩

/--
No further certified terminal presentation can improve the cut merely by
re-expression: last-bit, concrete-payload and opposition-payload are already
identified at the normal form.
-/
theorem hodge_gap_is_terminal_normal_form
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    normalizeHodgePresentation M .lastBit ↔
    normalizeHodgePresentation M .oppositionPayload :=
  hodge_terminal_normal_form_fixed_point M .lastBit .oppositionPayload

#print axioms MCore.BackwardAudit.hodgeGapSignature
#print axioms MCore.BackwardAudit.hodge_gap_signature_closed_normal_form
#print axioms MCore.BackwardAudit.hodge_gap_is_terminal_normal_form

end MCore.BackwardAudit
