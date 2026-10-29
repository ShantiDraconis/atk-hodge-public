import MCore.K26

namespace MCore

/-- Non-promoting registry metadata for one candidate condition.  Proof objects
    are never stored as optional values: every mathematical implication is
    supplied explicitly to the theorems below. -/
structure FinalAttackCandidate where
  name : String
  qToAlgebraicitySupplied : Bool := false
  algebraicityToQSupplied : Bool := false
  qToHodgeSupplied : Bool := false
  hodgeToQSupplied : Bool := false
  independentProofSupplied : Bool := false
  counterexampleSupplied : Bool := false

inductive FinalAttackStatus where
  | provedReduction
  | counterexample
  | redundant
  | circular
  | externalTheoremRequired
  | openMathematics
  | crossRepoIncompatible
  deriving Repr, DecidableEq

theorem fa_q_to_algebraicity_implies_q_to_hodge
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M) (Q : Prop)
    (hQA : Q → ConcreteAlgebraicityPayload M) :
    Q → GradedRationalHodgeConjecture G := by
  intro hQ
  exact (k26_minimal_cut B).2 (hQA hQ)

theorem fa_hodge_to_algebraicity
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M) :
    GradedRationalHodgeConjecture G → ConcreteAlgebraicityPayload M :=
  (k26_minimal_cut B).1

theorem fa_equivalent_payload_is_circular
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M) (Q : Prop)
    (hQA : Q → ConcreteAlgebraicityPayload M)
    (hAQ : ConcreteAlgebraicityPayload M → Q) :
    Q ↔ GradedRationalHodgeConjecture G := by
  constructor
  · exact fa_q_to_algebraicity_implies_q_to_hodge B Q hQA
  · intro hH
    exact hAQ ((k26_minimal_cut B).1 hH)

theorem fa_hodge_to_q_and_q_to_payload_is_equivalent
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M) (Q : Prop)
    (hHQ : GradedRationalHodgeConjecture G → Q)
    (hQA : Q → ConcreteAlgebraicityPayload M) :
    Q ↔ GradedRationalHodgeConjecture G := by
  constructor
  · exact fa_q_to_algebraicity_implies_q_to_hodge B Q hQA
  · exact hHQ

structure FinalAttackCounterexample
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (Q : Prop) : Prop where
  qWitness : Q
  algebraicityFails : ¬ ConcreteAlgebraicityPayload M

theorem fa_counterexample_refutes_q_to_algebraicity
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    {Q : Prop} (C : FinalAttackCounterexample (G := G) (M := M) Q) :
    ¬ (Q → ConcreteAlgebraicityPayload M) := by
  intro h
  exact C.algebraicityFails (h C.qWitness)

inductive CrossRepoImportMode where
  | exact
  | adapted
  | analogyOnly
  deriving Repr, DecidableEq

structure CrossRepoProvenance where
  sourceRepository : String
  sourceSHA : String
  frozenRef : String
  certificate : String
  sourceCreatedAt : String
  certifiedAt : String
  sourceGate : String
  sourceTheorem : String
  sourceClassification : String
  targetRepository : String
  targetGate : String
  targetGap : String
  importMode : CrossRepoImportMode
  hypothesesMatch : Bool
  semanticMatch : Bool
  dependencyHash : String
  sourceBlobSHA : String
  targetAdapterTheorem : String
  assumptionsAdded : List String
  assumptionsDischarged : List String
  closureDistanceBefore : Nat
  closureDistanceAfter : Nat
  verificationStatus : String

structure FinalAttackFrontier where
  exactAlgebraicityCut : FinalAttackStatus
  equivalentReformulations : FinalAttackStatus
  coefficientModelDescendants : FinalAttackStatus
  uncertifiedCrossRepoMaterial : FinalAttackStatus
  finalProof : SignatureStatus

def finalAttackFrontier : FinalAttackFrontier :=
  { exactAlgebraicityCut := .openMathematics
    equivalentReformulations := .circular
    coefficientModelDescendants := .redundant
    uncertifiedCrossRepoMaterial := .externalTheoremRequired
    finalProof := .openBridge }

theorem fa_algebraicity_open :
    finalAttackFrontier.exactAlgebraicityCut = .openMathematics := rfl

theorem fa_equivalent_reformulations_circular :
    finalAttackFrontier.equivalentReformulations = .circular := rfl

theorem fa_coefficient_model_redundant :
    finalAttackFrontier.coefficientModelDescendants = .redundant := rfl

theorem fa_uncertified_cross_repo_external :
    finalAttackFrontier.uncertifiedCrossRepoMaterial = .externalTheoremRequired := rfl

theorem fa_final_proof_open : finalAttackFrontier.finalProof = .openBridge := rfl

def finalAttackReductionStatus : SignatureStatus := .provedProperty

#print axioms fa_q_to_algebraicity_implies_q_to_hodge
#print axioms fa_hodge_to_algebraicity
#print axioms fa_equivalent_payload_is_circular
#print axioms fa_hodge_to_q_and_q_to_payload_is_equivalent
#print axioms fa_counterexample_refutes_q_to_algebraicity
#print axioms fa_algebraicity_open
#print axioms fa_equivalent_reformulations_circular
#print axioms fa_coefficient_model_redundant
#print axioms fa_uncertified_cross_repo_external
#print axioms fa_final_proof_open

end MCore
