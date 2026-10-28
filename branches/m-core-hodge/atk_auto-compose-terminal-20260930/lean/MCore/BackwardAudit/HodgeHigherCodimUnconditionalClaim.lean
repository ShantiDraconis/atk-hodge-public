import MCore.BackwardAudit.HodgeUnconditionalCertificate
import MCore.BackwardAudit.HodgeCodimTrisection

namespace MCore.BackwardAudit

/-!
# Exact unconditional higher-codimension claim

This is the minimal positive mathematical certificate after the reusable
low-codimension slices are supplied.  It is intentionally not a wrapper around
another open proposition: its sole mathematical field is exactly
HigherCodimensionAlgebraicityPayload.
-/

structure HigherCodimensionUnconditionalCertificate
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop where
  proof : HigherCodimensionAlgebraicityPayload M

/-- The exact higher-codimension certificate closes the universal concrete
payload once the reusable p=0 and p=1 slices are supplied. -/
theorem higher_certificate_closes_concrete_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h0 : CodimensionZeroAlgebraicityPayload M)
    (h1 : MCore.CodimensionOneAlgebraicityPayload M)
    (C : HigherCodimensionUnconditionalCertificate M) :
    MCore.ConcreteAlgebraicityPayload M :=
  concretePayload_of_trisection h0 h1 C.proof

/-- Exact unconditional theorem activation from the higher-codimension
certificate and the already-reusable low-codimension slices. -/
theorem higher_certificate_enables_hodge
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (h0 : CodimensionZeroAlgebraicityPayload M)
    (h1 : MCore.CodimensionOneAlgebraicityPayload M)
    (C : HigherCodimensionUnconditionalCertificate M) :
    GradedRationalHodgeConjecture G :=
  (MCore.k26_minimal_cut B).2
    (higher_certificate_closes_concrete_payload h0 h1 C)

/-- Build the full unconditional terminal certificate from exactly the
higher-codimension mathematical certificate. -/
def unconditionalCertificateOfHigher
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (h0 : CodimensionZeroAlgebraicityPayload M)
    (h1 : MCore.CodimensionOneAlgebraicityPayload M)
    (C : HigherCodimensionUnconditionalCertificate M) :
    UnconditionalHodgeCertificate G M :=
  {
    boundary := B
    algebraicity := higher_certificate_closes_concrete_payload h0 h1 C
  }

/-- Fail-closed exactness: the higher certificate contains no information
beyond the higher-codimension payload itself. -/
theorem higher_certificate_iff_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G} :
    HigherCodimensionUnconditionalCertificate M ↔
      HigherCodimensionAlgebraicityPayload M := by
  constructor
  · intro C
    exact C.proof
  · intro h
    exact ⟨h⟩

#print axioms MCore.BackwardAudit.higher_certificate_closes_concrete_payload
#print axioms MCore.BackwardAudit.higher_certificate_enables_hodge
#print axioms MCore.BackwardAudit.unconditionalCertificateOfHigher
#print axioms MCore.BackwardAudit.higher_certificate_iff_payload

end MCore.BackwardAudit
