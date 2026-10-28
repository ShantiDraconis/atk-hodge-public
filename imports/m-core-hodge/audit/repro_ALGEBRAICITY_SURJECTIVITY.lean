import MCore.K26
import MCore.Frontier.CandidateBridge

namespace HodgeBackwardAuditRepro

open MCore
open MCore.Frontier

/-- Literal public endpoint used for reproduction. -/
def PUBLIC_LITERAL_ENDPOINT (G : GradedRationalHodgeData) : Prop :=
  ∀ (X : G.Variety), G.isSmoothProjective X →
    ∀ (p : Nat) (alpha : G.CohomologyQ X (2 * p)),
      G.isTypePP p alpha → G.inCycleClassSpan p alpha

theorem literal_endpoint_matches_frozen_statement
    (G : GradedRationalHodgeData) :
    PUBLIC_LITERAL_ENDPOINT G ↔ GradedRationalHodgeConjecture G := by
  rfl

/-- Frozen K26 reproduction: the endpoint follows exactly when the certified
    boundary and the still-open concrete algebraicity payload are supplied. -/
theorem repro_from_k26_payload
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (payload : ConcreteAlgebraicityPayload M) :
    PUBLIC_LITERAL_ENDPOINT G := by
  exact (literal_endpoint_matches_frozen_statement G).2
    ((k26_minimal_cut B).2 payload)

/-- Dense reproduction of the current Spread/Variational route. Every
    unresolved mathematical arrow remains an explicit argument. -/
theorem repro_variational_spread_given_residues
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    {V : AlgebraicityCandidateVocabulary}
    (hodgeLocusAlgebraic : V.hodgeLocusAlgebraic)
    (spread : C_Spread V)
    (spreadProducesPoint :
      C_Spread V → V.hasAlgebraicPointOnHodgeLocus)
    (specialization :
      V.hasAlgebraicPointOnHodgeLocus → ConcreteAlgebraicityPayload M) :
    PUBLIC_LITERAL_ENDPOINT G := by
  have payload : ConcreteAlgebraicityPayload M :=
    spread_to_payload_given_geometric_inputs
      (M := M) hodgeLocusAlgebraic spreadProducesPoint specialization spread
  exact repro_from_k26_payload B payload

/-- Reproduction verdict metadata. No target certificate is emitted by this
    audit because the residue-bearing arguments above have not been discharged. -/
def TARGET_CERTIFICATE_AVAILABLE : Bool := false

theorem target_certificate_not_emitted :
    TARGET_CERTIFICATE_AVAILABLE = false := by
  rfl

#print axioms HodgeBackwardAuditRepro.literal_endpoint_matches_frozen_statement
#print axioms HodgeBackwardAuditRepro.repro_from_k26_payload
#print axioms HodgeBackwardAuditRepro.repro_variational_spread_given_residues
#print axioms HodgeBackwardAuditRepro.target_certificate_not_emitted

end HodgeBackwardAuditRepro
