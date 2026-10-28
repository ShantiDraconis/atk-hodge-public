import MCore.BackwardAudit.HodgeUnifiedTerminalProducer

namespace MCore.BackwardAudit

/-!
# Unconditional Hodge terminal certificate

This file isolates the exact claim object required for an unconditional
positive endpoint.  No reduction-only certificate can inhabit it.

An inhabitant must contain:
1. the certified semantic/concrete boundary for the selected model;
2. the universal concrete algebraicity payload itself.

Once such an inhabitant exists, the Hodge theorem follows with no additional
mathematical premise.
-/

structure UnconditionalHodgeCertificate
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) : Prop where
  boundary : HodgeCertificationBoundary G M
  algebraicity : MCore.ConcreteAlgebraicityPayload M

/-- Exact unconditional positive claim.  The certificate contains the whole
remaining mathematical content, so theorem creation introduces no new premise. -/
theorem unconditional_hodge_claim
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (C : UnconditionalHodgeCertificate G M) :
    GradedRationalHodgeConjecture G :=
  (MCore.k26_minimal_cut C.boundary).2 C.algebraicity

/-- Any already-unified positive terminal producer can create the exact
unconditional certificate once the certified boundary is supplied. -/
def unconditionalCertificateOfPositiveProducer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (P : HodgePositiveTerminalProducer M) :
    UnconditionalHodgeCertificate G M :=
  {
    boundary := B
    algebraicity := P.payload
  }

/-- The terminal certificate is equivalent to the concrete payload once the
boundary is fixed. This makes the remaining OPEN_MATH explicit and prevents
metadata-only certificates from being promoted. -/
theorem unconditionalCertificate_iff_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M) :
    UnconditionalHodgeCertificate G M ↔
      MCore.ConcreteAlgebraicityPayload M := by
  constructor
  · intro C
    exact C.algebraicity
  · intro h
    exact ⟨B, h⟩

/-- Direct theorem-enabling API: if the exact terminal certificate exists,
the theorem is enabled immediately. -/
def enableUnconditionalHodgeTheorem
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (C : UnconditionalHodgeCertificate G M) :
    GradedRationalHodgeConjecture G :=
  unconditional_hodge_claim C

#print axioms MCore.BackwardAudit.unconditional_hodge_claim
#print axioms MCore.BackwardAudit.unconditionalCertificateOfPositiveProducer
#print axioms MCore.BackwardAudit.unconditionalCertificate_iff_payload
#print axioms MCore.BackwardAudit.enableUnconditionalHodgeTheorem

end MCore.BackwardAudit
