import MCore.BackwardAudit.R3CombinationMinimal

namespace MCore.BackwardAudit

/-!
# R3 circularity firewall

The exact variational R3 payload can always be discharged if algebraicity of
the original class alpha is already known.  Therefore a claimed proof of R3 is
only informative when its provenance is independent of the target
InConcreteCycleSpan M alpha.

This module records that circularity mechanically.
-/

theorem base_algebraicity_implies_r3_variational
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (hAlg : InConcreteCycleSpan M α) :
    R3VariationalAlgebraicityPayload M S := by
  intro y γ hy hq hTransportedAlg
  exact hAlg

theorem base_algebraicity_implies_r3_combination
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (hAlg : InConcreteCycleSpan M α) :
    R3CombinationPayload M S :=
  combination_payload_iff_variational_algebraicity.mpr
    (base_algebraicity_implies_r3_variational hAlg)

theorem base_algebraicity_implies_r3_contract
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (hAlg : InConcreteCycleSpan M α) :
    Nonempty (R3TransportContract M S) :=
  (r3_contract_iff_variational_algebraicity).2
    (base_algebraicity_implies_r3_variational hAlg)

inductive R3ProvenanceStatus where
  | targetCanDischargeR3
  | independentGeometryRequiredForProgress
  | noIndependentR3ProofPresent
  deriving Repr, DecidableEq

structure R3ProvenanceFrontier where
  circularDischarge : R3ProvenanceStatus
  progressCriterion : R3ProvenanceStatus
  currentIndependentProof : R3ProvenanceStatus

def r3ProvenanceFrontier : R3ProvenanceFrontier :=
  {
    circularDischarge := .targetCanDischargeR3
    progressCriterion := .independentGeometryRequiredForProgress
    currentIndependentProof := .noIndependentR3ProofPresent
  }

theorem r3_target_can_discharge_r3 :
    r3ProvenanceFrontier.circularDischarge =
      .targetCanDischargeR3 := rfl

theorem r3_independent_geometry_required_for_progress :
    r3ProvenanceFrontier.progressCriterion =
      .independentGeometryRequiredForProgress := rfl

theorem r3_no_independent_proof_present :
    r3ProvenanceFrontier.currentIndependentProof =
      .noIndependentR3ProofPresent := rfl

#print axioms MCore.BackwardAudit.base_algebraicity_implies_r3_variational
#print axioms MCore.BackwardAudit.base_algebraicity_implies_r3_combination
#print axioms MCore.BackwardAudit.base_algebraicity_implies_r3_contract
#print axioms MCore.BackwardAudit.r3_target_can_discharge_r3
#print axioms MCore.BackwardAudit.r3_independent_geometry_required_for_progress
#print axioms MCore.BackwardAudit.r3_no_independent_proof_present

end MCore.BackwardAudit
