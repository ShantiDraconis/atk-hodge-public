import MCore.BackwardAudit.HodgeLastBitFrontier

namespace MCore

open BackwardAudit

/--
FINAL_ROOT / GLOBAL_EXTERNAL certificate.

This certificate closes the formal architecture: all structural reductions,
firewalls, and no-reopen obligations are kernel checked. It deliberately does
not inhabit HodgeLastBit; that proposition is the remaining mathematical
endpoint.
-/
structure HodgeFinalGlobalExternalCertificate
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) : Prop where
  noReopen : HodgeNoReopenCertificate M
  lastBitExact :
    HodgeLastBit M ↔ ConcreteAlgebraicityPayload M
  firewall :
    ∀ (P : R2StructuralCandidate),
      P codimZeroCounterexampleM →
      ¬ ForcesFastR2 P

def hodgeFinalGlobalExternalCertificate
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeFinalGlobalExternalCertificate G M :=
  {
    noReopen := hodgeNoReopenCertificate M
    lastBitExact := hodge_terminal_truncation_exact M
    firewall := by
      intro P hP
      exact candidate_holding_on_counterexample_cannot_force_fast_r2 P hP
  }

theorem hodge_final_root_structural_certified
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    Nonempty (HodgeFinalGlobalExternalCertificate G M) :=
  ⟨hodgeFinalGlobalExternalCertificate M⟩

/-- Publication boundary: the final mathematical theorem follows exactly from
an inhabitant of the last bit, and from nothing weaker in this certificate. -/
theorem hodge_final_root_of_last_bit
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h : HodgeLastBit M) :
    ConcreteAlgebraicityPayload M :=
  hodge_last_bit_closes_terminal h

#print axioms MCore.hodgeFinalGlobalExternalCertificate
#print axioms MCore.hodge_final_root_structural_certified
#print axioms MCore.hodge_final_root_of_last_bit

end MCore
