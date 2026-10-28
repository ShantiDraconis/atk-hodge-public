import MCore.K18
import MCore.BackwardAudit.H01MinimalForwardPayload
import MCore.BackwardAudit.CodimOneLefschetz11

namespace MCore

/-!
# Hodge material frontier

Forward-only decomposition of the concrete algebraicity payload.

This module does not assert any missing Hodge theorem.  It splits the exact
K18 payload into codimension zero, codimension one, and codimension >= 2,
reuses the existing Lefschetz (1,1) reduction for codimension one, and exposes
H01MinimalForwardPayload as a sufficient producer for the remaining pieces.
-/

def CodimZeroConcretePayload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (α : G.CohomologyQ X (2 * 0)),
    G.isSmoothProjective X →
    G.isTypePP 0 α →
    InConcreteCycleSpan M α

def CodimOneConcretePayload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (α : G.CohomologyQ X (2 * 1)),
    G.isSmoothProjective X →
    G.isTypePP 1 α →
    InConcreteCycleSpan M α

def HigherCodimConcretePayload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)),
    2 ≤ p →
    G.isSmoothProjective X →
    G.isTypePP p α →
    InConcreteCycleSpan M α

/-- Exact partition of the K18 frontier.  No mathematical content is added:
every natural codimension is either 0, 1, or at least 2. -/
theorem concretePayload_iff_materialSplit
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    ConcreteAlgebraicityPayload M ↔
      CodimZeroConcretePayload M ∧
      CodimOneConcretePayload M ∧
      HigherCodimConcretePayload M := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro X α hX hα
      exact h X 0 α hX hα
    · intro X α hX hα
      exact h X 1 α hX hα
    · intro X p α hp hX hα
      exact h X p α hX hα
  · rintro ⟨h0, h1, h2⟩ X p α hX hα
    cases p with
    | zero =>
        exact h0 X α hX hα
    | succ q =>
        cases q with
        | zero =>
            exact h1 X α hX hα
        | succ r =>
            have hp : 2 ≤ Nat.succ (Nat.succ r) :=
              Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le r))
            exact h2 X (Nat.succ (Nat.succ r)) α hp hX hα

/-- Existing codimension-one reduction.  A genuine complex-geometry adapter
supplying Lefschetz11ConcreteLaw discharges the complete p=1 slice. -/
theorem codimOnePayload_of_lefschetz11
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (L : BackwardAudit.Lefschetz11ConcreteLaw M) :
    CodimOneConcretePayload M := by
  intro X α hX hα
  exact L.algebraic X α hX hα

/-- Minimal H01 producer for codimension zero. -/
structure CodimZeroH01Producer
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  run :
    ∀ (X : G.Variety) (α : G.CohomologyQ X (2 * 0)),
      BackwardAudit.H01MinimalForwardPayload G M X 0 α

/-- Minimal H01 producer for all genuinely higher codimensions. -/
structure HigherH01Producer
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  run :
    ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)),
      2 ≤ p →
      BackwardAudit.H01MinimalForwardPayload G M X p α

theorem codimZeroPayload_of_h01
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (P : CodimZeroH01Producer G M) :
    CodimZeroConcretePayload M := by
  intro X α hX hα
  exact (A.span_iff α).1
    ((BackwardAudit.h01_minimal_forward_payload_closes_pointwise
      A (P.run X α)) hX hα)

theorem higherPayload_of_h01
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (P : HigherH01Producer G M) :
    HigherCodimConcretePayload M := by
  intro X p α hp hX hα
  exact (A.span_iff α).1
    ((BackwardAudit.h01_minimal_forward_payload_closes_pointwise
      A (P.run X p α hp)) hX hα)

/-- Forward-only assembly.  The theorem consumes three independent material
producers; it does not synthesize any of them. -/
theorem concretePayload_of_materialProducers
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h0 : CodimZeroConcretePayload M)
    (L : BackwardAudit.Lefschetz11ConcreteLaw M)
    (hHigher : HigherCodimConcretePayload M) :
    ConcreteAlgebraicityPayload M := by
  exact
    (concretePayload_iff_materialSplit M).2
      ⟨h0, codimOnePayload_of_lefschetz11 L, hHigher⟩

/-- H01-based assembly.  What remains external is visible in the arguments:
the cycle-span adapter, the p=0 H01 producer, the concrete Lefschetz law,
and the p>=2 H01 producer. -/
theorem concretePayload_of_h01_split
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (P0 : CodimZeroH01Producer G M)
    (L : BackwardAudit.Lefschetz11ConcreteLaw M)
    (P2 : HigherH01Producer G M) :
    ConcreteAlgebraicityPayload M := by
  exact concretePayload_of_materialProducers
    (codimZeroPayload_of_h01 A P0)
    L
    (higherPayload_of_h01 A P2)

#print axioms MCore.concretePayload_iff_materialSplit
#print axioms MCore.codimOnePayload_of_lefschetz11
#print axioms MCore.codimZeroPayload_of_h01
#print axioms MCore.higherPayload_of_h01
#print axioms MCore.concretePayload_of_materialProducers
#print axioms MCore.concretePayload_of_h01_split

end MCore
