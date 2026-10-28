import MCore.HodgeExactRemaining

namespace MCore

/-!
# Canonical semantic Hodge model

The early ungraded HodgeSemanticData API can be instantiated canonically from
the graded model plus concrete cycle-span mechanics.  A semantic class stores
its codimension together with its degree-2p rational cohomology class.

This removes the old semantic adapter from the canonical terminal route.
-/

abbrev PackagedHodgeClass
    (G : GradedRationalHodgeData)
    (X : G.Variety) :=
  Sigma fun p : Nat => G.CohomologyQ X (2 * p)

abbrev PackagedAlgebraicCycle
    (G : GradedRationalHodgeData)
    (X : G.Variety) :=
  Sigma fun p : Nat => G.CycleQ X p

def canonicalHodgeSemanticData
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) :
    HodgeSemanticData :=
  {
    Variety := G.Variety
    Class := PackagedHodgeClass G
    AlgebraicCycle := PackagedAlgebraicCycle G
    isSmoothProjective := G.isSmoothProjective
    isRationalHodgeClass := by
      intro X c
      exact G.isTypePP c.1 c.2
    cycleClass := by
      intro X z
      exact ⟨z.1, M.cycleClass z.1 z.2⟩
    rationalSpanOfCycles := by
      intro X c
      exact InConcreteCycleSpan M c.2
  }

theorem canonicalRationalHodge_iff_concretePayload
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) :
    RationalHodgeConjecture (canonicalHodgeSemanticData G M) ↔
      ConcreteAlgebraicityPayload M := by
  constructor
  · intro h X p α hX hα
    exact h X hX ⟨p, α⟩ hα
  · intro h X hX c hc
    rcases c with ⟨p, α⟩
    exact h X p α hX hc

theorem canonicalTerminal_iff_concretePayload
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) :
    HodgeTerminalCertifies (canonicalHodgeSemanticData G M) ↔
      ConcreteAlgebraicityPayload M := by
  exact canonicalRationalHodge_iff_concretePayload G M

theorem HodgeConstructiveMaterial.certifiesCanonicalTerminal
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : HodgeConstructiveMaterial G M) :
    HodgeTerminalCertifies (canonicalHodgeSemanticData G M) :=
  (canonicalTerminal_iff_concretePayload G M).2 H.toConcretePayload

#print axioms MCore.canonicalRationalHodge_iff_concretePayload
#print axioms MCore.canonicalTerminal_iff_concretePayload
#print axioms MCore.HodgeConstructiveMaterial.certifiesCanonicalTerminal

end MCore
