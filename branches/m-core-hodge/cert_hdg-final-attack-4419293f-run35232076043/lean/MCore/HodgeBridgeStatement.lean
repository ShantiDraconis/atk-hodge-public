import MCore.FinalAttack

namespace MCore

/-- Arithmetic/geometric/operator data for a candidate bridge.  This is an
    interface only: no field has type `inCycleClassSpan` and no algebraic-cycle
    witness is stored here. -/
structure HodgeBridgeData
    (G : GradedRationalHodgeData)
    (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)) where
  ArithmeticModel : Type
  AdicCohomology : Type
  deRhamCohomology : Type
  ChowModel : Type
  arithmeticModel : ArithmeticModel
  ell : Nat
  alphaAdic : AdicCohomology
  frobenius : AdicCohomology → AdicCohomology
  frobeniusFixed : frobenius alphaAdic = alphaAdic
  alphaDeRham : deRhamCohomology
  periodCompatible : Prop
  hodgeFiltrationCompatible : Prop
  gaussManinCompatible : Prop
  monodromyCompatible : Prop
  regulatorCompatible : Prop
  comparisonCompatible : Prop
  operatorDomain : Type
  operator : operatorDomain → G.CohomologyQ X (2 * p)
  operatorEquation : Prop

/-- The candidate bridge condition deliberately contains only arithmetic,
    comparison and operator constraints.  It does not contain the conclusion
    `G.inCycleClassSpan p α`. -/
def AlgebraicityBridge
    (G : GradedRationalHodgeData)
    (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)) : Prop :=
  ∃ B : HodgeBridgeData G X p α,
    B.periodCompatible ∧
    B.hodgeFiltrationCompatible ∧
    B.gaussManinCompatible ∧
    B.monodromyCompatible ∧
    B.regulatorCompatible ∧
    B.comparisonCompatible ∧
    B.operatorEquation

/-- Exact open implication whose proof would turn the bridge condition into
    pointwise algebraicity.  This is a proposition, not an axiom/theorem. -/
def BridgeImpliesAlgebraicity (G : GradedRationalHodgeData) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)),
    G.isSmoothProjective X → G.isTypePP p α →
    AlgebraicityBridge G X p α → G.inCycleClassSpan p α

/-- Exact open existence/universality side of the bridge. -/
def BridgeHolds (G : GradedRationalHodgeData) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)),
    G.isSmoothProjective X → G.isTypePP p α → AlgebraicityBridge G X p α

/-- Safe transport theorem.  It proves only that the two explicit bridge
    obligations, if independently supplied, imply the rational Hodge statement. -/
theorem hodge_of_open_bridge
    (G : GradedRationalHodgeData)
    (hBridge : BridgeHolds G)
    (hImplies : BridgeImpliesAlgebraicity G) :
    GradedRationalHodgeConjecture G := by
  intro X hsp p α hpp
  exact hImplies X p α hsp hpp (hBridge X p α hsp hpp)

def bridgeStatementStatus : SignatureStatus := .definitionInterface
def bridgeProofStatus : FinalAttackStatus := .openMathematics
def bridgeHodgeExportStatus : SignatureStatus := .openBridge

theorem bridge_statement_well_formed : bridgeStatementStatus = .definitionInterface := rfl
theorem bridge_proof_open : bridgeProofStatus = .openMathematics := rfl
theorem bridge_hodge_export_open : bridgeHodgeExportStatus = .openBridge := rfl

#print axioms hodge_of_open_bridge
#print axioms bridge_statement_well_formed
#print axioms bridge_proof_open
#print axioms bridge_hodge_export_open

end MCore
