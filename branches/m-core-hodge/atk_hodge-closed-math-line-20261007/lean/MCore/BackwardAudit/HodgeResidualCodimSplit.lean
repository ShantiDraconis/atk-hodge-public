import MCore.K26
import MCore.BackwardAudit.CodimOneAdapterFirewall

namespace MCore.BackwardAudit

/-!
# Hodge residual codimension split

This file isolates the exact residual after codimension one.

No classical theorem is manufactured here.  Given a genuine codimension-one
certificate, the universal concrete algebraicity payload is equivalent to the
same payload restricted to p != 1.
-/

def NonCodimOneAlgebraicityPayload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (alpha : G.CohomologyQ X (2 * p)),
    p ≠ 1 →
    G.isSmoothProjective X →
    G.isTypePP p alpha →
    InConcreteCycleSpan M alpha

theorem concretePayload_implies_nonCodimOne
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h : MCore.ConcreteAlgebraicityPayload M) :
    NonCodimOneAlgebraicityPayload M := by
  intro X p alpha hp hX hAlpha
  exact h X p alpha hX hAlpha

theorem concretePayload_of_codimOne_and_residual
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h1 : MCore.CodimensionOneAlgebraicityPayload M)
    (hR : NonCodimOneAlgebraicityPayload M) :
    MCore.ConcreteAlgebraicityPayload M := by
  intro X p alpha hX hAlpha
  by_cases hp : p = 1
  · subst hp
    exact h1 X alpha hX hAlpha
  · exact hR X p alpha hp hX hAlpha

theorem concretePayload_iff_codimOne_and_residual
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G} :
    MCore.ConcreteAlgebraicityPayload M ↔
      MCore.CodimensionOneAlgebraicityPayload M ∧
      NonCodimOneAlgebraicityPayload M := by
  constructor
  · intro h
    exact ⟨MCore.concretePayload_implies_codimensionOne h,
      concretePayload_implies_nonCodimOne h⟩
  · rintro ⟨h1, hR⟩
    exact concretePayload_of_codimOne_and_residual h1 hR

theorem concretePayload_iff_residual_given_codimOne
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h1 : MCore.CodimensionOneAlgebraicityPayload M) :
    MCore.ConcreteAlgebraicityPayload M ↔
      NonCodimOneAlgebraicityPayload M := by
  constructor
  · exact concretePayload_implies_nonCodimOne
  · intro hR
    exact concretePayload_of_codimOne_and_residual h1 hR

theorem hodge_iff_residual_given_boundary_and_codimOne
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (h1 : MCore.CodimensionOneAlgebraicityPayload M) :
    GradedRationalHodgeConjecture G ↔
      NonCodimOneAlgebraicityPayload M := by
  exact (MCore.k26_minimal_cut B).trans
    (concretePayload_iff_residual_given_codimOne h1)

#print axioms MCore.BackwardAudit.concretePayload_implies_nonCodimOne
#print axioms MCore.BackwardAudit.concretePayload_of_codimOne_and_residual
#print axioms MCore.BackwardAudit.concretePayload_iff_codimOne_and_residual
#print axioms MCore.BackwardAudit.concretePayload_iff_residual_given_codimOne
#print axioms MCore.BackwardAudit.hodge_iff_residual_given_boundary_and_codimOne

end MCore.BackwardAudit
