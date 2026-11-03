import MCore.BackwardAudit.HodgeResidualCodimSplit

namespace MCore.BackwardAudit

/-!
# Hodge codimension trisection

Exact partition of the concrete algebraicity payload into:
- codimension 0,
- codimension 1,
- higher codimension p >= 2.

This is a logical decomposition only. No classical theorem is manufactured.
-/

def CodimensionZeroAlgebraicityPayload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (alpha : G.CohomologyQ X (2 * 0)),
    G.isSmoothProjective X →
    G.isTypePP 0 alpha →
    InConcreteCycleSpan M alpha

def HigherCodimensionAlgebraicityPayload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (alpha : G.CohomologyQ X (2 * p)),
    2 ≤ p →
    G.isSmoothProjective X →
    G.isTypePP p alpha →
    InConcreteCycleSpan M alpha

theorem concretePayload_implies_codimZero
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h : MCore.ConcreteAlgebraicityPayload M) :
    CodimensionZeroAlgebraicityPayload M := by
  intro X alpha hX hAlpha
  exact h X 0 alpha hX hAlpha

theorem concretePayload_implies_higherCodim
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h : MCore.ConcreteAlgebraicityPayload M) :
    HigherCodimensionAlgebraicityPayload M := by
  intro X p alpha hp hX hAlpha
  exact h X p alpha hX hAlpha

theorem concretePayload_of_trisection
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h0 : CodimensionZeroAlgebraicityPayload M)
    (h1 : MCore.CodimensionOneAlgebraicityPayload M)
    (h2 : HigherCodimensionAlgebraicityPayload M) :
    MCore.ConcreteAlgebraicityPayload M := by
  intro X p alpha hX hAlpha
  cases p with
  | zero =>
      simpa using h0 X alpha hX hAlpha
  | succ p =>
      cases p with
      | zero =>
          simpa using h1 X alpha hX hAlpha
      | succ q =>
          have hp : 2 ≤ Nat.succ (Nat.succ q) := by omega
          exact h2 X (Nat.succ (Nat.succ q)) alpha hp hX hAlpha

theorem concretePayload_iff_trisection
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G} :
    MCore.ConcreteAlgebraicityPayload M ↔
      CodimensionZeroAlgebraicityPayload M ∧
      MCore.CodimensionOneAlgebraicityPayload M ∧
      HigherCodimensionAlgebraicityPayload M := by
  constructor
  · intro h
    exact ⟨concretePayload_implies_codimZero h,
      MCore.concretePayload_implies_codimensionOne h,
      concretePayload_implies_higherCodim h⟩
  · rintro ⟨h0, h1, h2⟩
    exact concretePayload_of_trisection h0 h1 h2

theorem hodge_iff_higher_given_boundary_low_codim
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (h0 : CodimensionZeroAlgebraicityPayload M)
    (h1 : MCore.CodimensionOneAlgebraicityPayload M) :
    GradedRationalHodgeConjecture G ↔
      HigherCodimensionAlgebraicityPayload M := by
  constructor
  · intro h
    exact concretePayload_implies_higherCodim ((MCore.k26_minimal_cut B).1 h)
  · intro h2
    exact (MCore.k26_minimal_cut B).2
      (concretePayload_of_trisection h0 h1 h2)

#print axioms MCore.BackwardAudit.concretePayload_implies_codimZero
#print axioms MCore.BackwardAudit.concretePayload_implies_higherCodim
#print axioms MCore.BackwardAudit.concretePayload_of_trisection
#print axioms MCore.BackwardAudit.concretePayload_iff_trisection
#print axioms MCore.BackwardAudit.hodge_iff_higher_given_boundary_low_codim

end MCore.BackwardAudit
