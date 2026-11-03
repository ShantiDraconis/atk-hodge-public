import MCore.K15

namespace HodgeR2Lefschetz11DirectAudit

open MCore

/-- Direct semantic adapter for the ORIGINAL K13 fiber X in codimension one.
    This route deliberately bypasses R1d/R3: Lefschetz (1,1) applies directly
    to a rational degree-two Hodge class on X. -/
structure DirectLefschetz11Adapter
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (X : G.Variety)
    (α : G.CohomologyQ X (2 * 1)) where
  ClassicalH2Q : Type
  ClassicalDivisor : Type

  toClassicalH2Q :
    G.CohomologyQ X (2 * 1) → ClassicalH2Q

  fromClassicalH2Q :
    ClassicalH2Q → G.CohomologyQ X (2 * 1)

  from_to :
    ∀ β : G.CohomologyQ X (2 * 1),
      fromClassicalH2Q (toClassicalH2Q β) = β

  to_from :
    ∀ β : ClassicalH2Q,
      toClassicalH2Q (fromClassicalH2Q β) = β

  isClassicalH11 : ClassicalH2Q → Prop

  typePP_iff_classicalH11 :
    ∀ β : G.CohomologyQ X (2 * 1),
      G.isTypePP 1 β ↔
        isClassicalH11 (toClassicalH2Q β)

  divisorClass : ClassicalDivisor → ClassicalH2Q

  divisorToCombination :
    ClassicalDivisor → CycleCombination G M X 1

  divisorCycleClassCompatibility :
    ∀ D : ClassicalDivisor,
      (divisorToCombination D).eval M =
        fromClassicalH2Q (divisorClass D)

/-- External classical Lefschetz (1,1) theorem, still supplied as an explicit
    theorem argument rather than an axiom declaration. -/
def DirectLefschetz11ClassicalStatement
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    (A : DirectLefschetz11Adapter M X α) : Prop :=
  ∀ β : A.ClassicalH2Q,
    A.isClassicalH11 β →
    ∃ D : A.ClassicalDivisor, A.divisorClass D = β

/-- Direct p=1 closure on the original fiber. No Qbar point, spread, path,
    or cycle specialization occurs in the statement or proof. -/
theorem direct_lefschetz11_closes_concrete_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    (A : DirectLefschetz11Adapter M X α)
    (hα : G.isTypePP 1 α)
    (hL11 : DirectLefschetz11ClassicalStatement A) :
    InConcreteCycleSpan M α := by
  have h11 :
      A.isClassicalH11 (A.toClassicalH2Q α) :=
    (A.typePP_iff_classicalH11 α).1 hα
  rcases hL11 (A.toClassicalH2Q α) h11 with ⟨D, hD⟩
  refine ⟨A.divisorToCombination D, ?_⟩
  calc
    (A.divisorToCombination D).eval M =
        A.fromClassicalH2Q (A.divisorClass D) :=
      A.divisorCycleClassCompatibility D
    _ = A.fromClassicalH2Q (A.toClassicalH2Q α) := by
      rw [hD]
    _ = α := A.from_to α

/-- Existing K15 wiring immediately transports the direct classical result to
    the semantic span predicate used by K13. -/
theorem direct_lefschetz11_closes_semantic_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (Span : CycleSpanAdapter G M)
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    (A : DirectLefschetz11Adapter M X α)
    (hα : G.isTypePP 1 α)
    (hL11 : DirectLefschetz11ClassicalStatement A) :
    G.inCycleClassSpan 1 α := by
  exact (Span.span_iff α).2
    (direct_lefschetz11_closes_concrete_span A hα hL11)

/-- Direct p=1 route classification. The only non-wiring obligations are a
    genuine classical carrier/divisor adapter and the external theorem. -/
inductive DirectP1Status where
  | provedInternal
  | semanticAdapterResidue
  | externalClassical
  deriving Repr, DecidableEq

structure DirectP1Requirement where
  name : String
  status : DirectP1Status
  note : String
  deriving Repr

def directP1Requirements : List DirectP1Requirement :=
  [
    ⟨"DIRECT_H2_H11_DIVISOR_ADAPTER", .semanticAdapterResidue,
      "Must identify frozen CohomologyQ/isTypePP/CycleQ mechanics with classical H^2_Q, H^(1,1), and divisors on the original X."⟩,
    ⟨"LEFSCHETZ_1_1", .externalClassical,
      "Supplied explicitly as DirectLefschetz11ClassicalStatement."⟩,
    ⟨"DIRECT_P1_TO_CONCRETE_SPAN", .provedInternal,
      "No R1d, Qbar descent, selected fiber, or R3 specialization is needed in codimension one."⟩
  ]

#print axioms HodgeR2Lefschetz11DirectAudit.direct_lefschetz11_closes_concrete_span
#print axioms HodgeR2Lefschetz11DirectAudit.direct_lefschetz11_closes_semantic_span

end HodgeR2Lefschetz11DirectAudit
