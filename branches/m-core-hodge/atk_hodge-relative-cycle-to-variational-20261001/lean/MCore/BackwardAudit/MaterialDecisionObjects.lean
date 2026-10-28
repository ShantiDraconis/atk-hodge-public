import MCore.K15

namespace MCore

/--
Official negative-side object for the graded rational Hodge statement.

It contains a concrete variety, codimension and rational Hodge class together
with a proof that the official cycle-span predicate fails at that class.
No negated conjecture is accepted as an input.
-/
structure GradedHodgeCounterexample (G : GradedRationalHodgeData) where
  X : G.Variety
  p : Nat
  alpha : G.CohomologyQ X (2 * p)

  smoothProjective : G.isSmoothProjective X
  typePP : G.isTypePP p alpha
  outsideOfficialCycleSpan : ¬ G.inCycleClassSpan p alpha

/--
A concrete graded Hodge counterexample directly refutes the graded conjecture.
-/
theorem GradedHodgeCounterexample.refutes
    {G : GradedRationalHodgeData}
    (C : GradedHodgeCounterexample G) :
    ¬ GradedRationalHodgeConjecture G := by
  intro h
  exact C.outsideOfficialCycleSpan
    (h C.X C.smoothProjective C.p C.alpha C.typePP)

/--
More concrete cycle-level negative object.

This records failure of the finite cycle-combination span in the explicit
CycleSpanMechanics carrier.  It is intentionally NOT promoted to a refutation
of the official graded statement unless an exact semantic identification of
the official and concrete span predicates has separately been established.
-/
structure ConcreteCycleSpanCounterexample
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  X : G.Variety
  p : Nat
  alpha : G.CohomologyQ X (2 * p)

  smoothProjective : G.isSmoothProjective X
  typePP : G.isTypePP p alpha
  outsideConcreteCycleSpan : ¬ InConcreteCycleSpan M alpha

/--
Finite-combination expansion of the negative concrete condition.
Every explicit finite cycle combination evaluates to something different from
the proposed Hodge class.
-/
theorem ConcreteCycleSpanCounterexample.no_combination_represents
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (C : ConcreteCycleSpanCounterexample G M) :
    ∀ z : CycleCombination G M C.X C.p,
      z.eval M ≠ C.alpha := by
  intro z hz
  exact C.outsideConcreteCycleSpan ⟨z, hz⟩

/--
A positive concrete cycle combination and a negative concrete counterexample
for the same class are incompatible.
-/
theorem concrete_cycle_positive_negative_incompatible
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    (z : CycleCombination G M X p)
    (hz : z.eval M = alpha)
    (hneg : ¬ InConcreteCycleSpan M alpha) :
    False :=
  hneg ⟨z, hz⟩

#print axioms MCore.GradedHodgeCounterexample.refutes
#print axioms MCore.ConcreteCycleSpanCounterexample.no_combination_represents
#print axioms MCore.concrete_cycle_positive_negative_incompatible

end MCore
