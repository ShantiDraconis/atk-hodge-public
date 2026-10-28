import MCore.BackwardAudit.HodgeCertifiedReuseBridge
import MCore.BackwardAudit.HodgeTensionClosure

namespace MCore.BackwardAudit

/-!
# Unified Hodge terminal producer

All currently legitimate terminal-producing forms are unified here.
Reduction-only certificates are consumed through their proved transport theorems;
they are not promoted by title or status.
-/

inductive HodgeTerminalProducer
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Type 1
  | directPositive
      (proof : MCore.ConcreteAlgebraicityPayload M)
  | codimSplitPositive
      (codimZero : CodimensionZeroAlgebraicityPayload M)
      (codimOne : MCore.CodimensionOneAlgebraicityPayload M)
      (higher : HigherCodimensionAlgebraicityPayload M)
  | certifiedH01Positive
      (adapter : CycleSpanAdapter G M)
      (codimZero : CodimensionZeroAlgebraicityPayload M)
      (codimOne : MCore.CodimensionOneAlgebraicityPayload M)
      (higherH01 : HigherCodimH01ForwardPayload G M)
  | concreteNegative
      (counterexample : ConcreteAlgebraicityCounterexample M)

/-- Every legitimate producer creates a genuine terminal outcome. -/
def HodgeTerminalProducer.outcome
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : HodgeTerminalProducer M) :
    HodgeClosedOutcome M :=
  match P with
  | .directPositive h =>
      .trueCase h
  | .codimSplitPositive h0 h1 h2 =>
      .trueCase (concretePayload_of_trisection h0 h1 h2)
  | .certifiedH01Positive A h0 h1 H =>
      .trueCase
        (concretePayload_of_trisection
          h0 h1 (higherCodim_of_h01_forward A H))
  | .concreteNegative C =>
      .falseCase (counterexample_to_negative C).closes

/-- Unified theorem activation: a real terminal producer yields Hodge or its
negation at the certified boundary. -/
def HodgeTerminalProducer.enableTheorem
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (P : HodgeTerminalProducer M) :
    GradedRationalHodgeConjecture G ∨
      ¬ GradedRationalHodgeConjecture G :=
  match P.outcome with
  | .trueCase h =>
      Or.inl ((MCore.k26_minimal_cut B).2 h)
  | .falseCase h =>
      Or.inr (by
        intro hHodge
        exact h ((MCore.k26_minimal_cut B).1 hHodge))

/-- Data-valued result of attempting positive theorem creation. -/
inductive HodgePositiveCreationResult
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Type
  | created (proof : MCore.ConcreteAlgebraicityPayload M)
  | negativeRoute

/-- Positive construction endpoint: every positive producer creates the
universal concrete payload; a negative producer is reported distinctly. -/
def HodgeTerminalProducer.createPositivePayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : HodgeTerminalProducer M) :
    HodgePositiveCreationResult M :=
  match P with
  | .directPositive h => .created h
  | .codimSplitPositive h0 h1 h2 =>
      .created (concretePayload_of_trisection h0 h1 h2)
  | .certifiedH01Positive A h0 h1 H =>
      .created (concretePayload_of_trisection
        h0 h1 (higherCodim_of_h01_forward A H))
  | .concreteNegative _ => .negativeRoute


/-- Positive-only terminal producers.  This API is the theorem-creation path:
every constructor carries enough evidence to build the concrete universal
payload, hence Hodge at a certified boundary. -/
inductive HodgePositiveTerminalProducer
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Type 1
  | direct
      (proof : MCore.ConcreteAlgebraicityPayload M)
  | codimSplit
      (codimZero : CodimensionZeroAlgebraicityPayload M)
      (codimOne : MCore.CodimensionOneAlgebraicityPayload M)
      (higher : HigherCodimensionAlgebraicityPayload M)
  | certifiedH01
      (adapter : CycleSpanAdapter G M)
      (codimZero : CodimensionZeroAlgebraicityPayload M)
      (codimOne : MCore.CodimensionOneAlgebraicityPayload M)
      (higherH01 : HigherCodimH01ForwardPayload G M)

def HodgePositiveTerminalProducer.payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : HodgePositiveTerminalProducer M) :
    MCore.ConcreteAlgebraicityPayload M :=
  match P with
  | .direct h => h
  | .codimSplit h0 h1 h2 =>
      concretePayload_of_trisection h0 h1 h2
  | .certifiedH01 A h0 h1 H =>
      concretePayload_of_trisection
        h0 h1 (higherCodim_of_h01_forward A H)

/-- Final theorem creation from any legitimate positive producer. -/
theorem HodgePositiveTerminalProducer.createTheorem
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (P : HodgePositiveTerminalProducer M) :
    GradedRationalHodgeConjecture G :=
  (MCore.k26_minimal_cut B).2 P.payload

/-- Final refutation creation from a faithful concrete counterexample. -/
theorem createHodgeRefutation
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (C : ConcreteAlgebraicityCounterexample M) :
    ¬ GradedRationalHodgeConjecture G := by
  intro h
  exact (counterexample_to_negative C).closes
    ((MCore.k26_minimal_cut B).1 h)

#print axioms MCore.BackwardAudit.HodgeTerminalProducer.outcome
#print axioms MCore.BackwardAudit.HodgeTerminalProducer.enableTheorem
#print axioms MCore.BackwardAudit.HodgeTerminalProducer.createPositivePayload
#print axioms MCore.BackwardAudit.HodgePositiveTerminalProducer.payload
#print axioms MCore.BackwardAudit.HodgePositiveTerminalProducer.createTheorem
#print axioms MCore.BackwardAudit.createHodgeRefutation

end MCore.BackwardAudit
