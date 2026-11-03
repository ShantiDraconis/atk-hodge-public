import MCore.BackwardAudit.R1DescentBoundary

namespace HodgeR2Lefschetz11Audit

open MCore
open MCore.BackwardAudit

/-- Independent comparison between the frozen rational degree-two carrier
    and a classical H^2(Q) carrier, including the exact (1,1) predicate match. -/
structure DegreeTwoHodgeComparison
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    (S : SpreadData G X 1 α hX hα)
    (Q : QbarHodgePointData S) where
  ClassicalH2Q : Type

  toClassicalH2Q :
    G.CohomologyQ (S.Family Q.y) (2 * 1) →
    ClassicalH2Q

  fromClassicalH2Q :
    ClassicalH2Q →
    G.CohomologyQ (S.Family Q.y) (2 * 1)

  from_to :
    ∀ β : G.CohomologyQ (S.Family Q.y) (2 * 1),
      fromClassicalH2Q (toClassicalH2Q β) = β

  to_from :
    ∀ β : ClassicalH2Q,
      toClassicalH2Q (fromClassicalH2Q β) = β

  isClassicalH11 : ClassicalH2Q → Prop

  typePP_iff_classicalH11 :
    ∀ β : G.CohomologyQ (S.Family Q.y) (2 * 1),
      G.isTypePP 1 β ↔
        isClassicalH11 (toClassicalH2Q β)

/-- Independent realization of classical divisors as the frozen finite cycle
    combinations, with exact cycle-class compatibility. -/
structure DivisorCycleRealization
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    (S : SpreadData G X 1 α hX hα)
    (Q : QbarHodgePointData S)
    (C : DegreeTwoHodgeComparison S Q) where
  ClassicalDivisor : Type

  divisorClass : ClassicalDivisor → C.ClassicalH2Q

  divisorToCombination :
    ClassicalDivisor →
    CycleCombination G M (S.Family Q.y) 1

  divisorCycleClassCompatibility :
    ∀ D : ClassicalDivisor,
      (divisorToCombination D).eval M =
        C.fromClassicalH2Q (divisorClass D)

/-- Typed bridge between the frozen abstract degree-two carrier and a
    classical rational H^(1,1) carrier.  This is data: no classical theorem is
    declared here. -/
structure Lefschetz11CarrierAdapter
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    (S : SpreadData G X 1 α hX hα)
    (Q : QbarHodgePointData S) where
  ClassicalH2Q : Type
  ClassicalDivisor : Type

  toClassicalH2Q :
    G.CohomologyQ (S.Family Q.y) (2 * 1) →
    ClassicalH2Q

  fromClassicalH2Q :
    ClassicalH2Q →
    G.CohomologyQ (S.Family Q.y) (2 * 1)

  from_to :
    ∀ β : G.CohomologyQ (S.Family Q.y) (2 * 1),
      fromClassicalH2Q (toClassicalH2Q β) = β

  to_from :
    ∀ β : ClassicalH2Q,
      toClassicalH2Q (fromClassicalH2Q β) = β

  isClassicalH11 : ClassicalH2Q → Prop

  typePP_iff_classicalH11 :
    ∀ β : G.CohomologyQ (S.Family Q.y) (2 * 1),
      G.isTypePP 1 β ↔
        isClassicalH11 (toClassicalH2Q β)

  divisorClass : ClassicalDivisor → ClassicalH2Q

  divisorToCombination :
    ClassicalDivisor →
    CycleCombination G M (S.Family Q.y) 1

  divisorCycleClassCompatibility :
    ∀ D : ClassicalDivisor,
      (divisorToCombination D).eval M =
        fromClassicalH2Q (divisorClass D)

/-- The split comparison and divisor-realization pieces reconstruct the
    monolithic carrier adapter mechanically. -/
def lefschetz11AdapterOfPieces
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    {S : SpreadData G X 1 α hX hα}
    {Q : QbarHodgePointData S}
    (C : DegreeTwoHodgeComparison S Q)
    (D : DivisorCycleRealization M S Q C) :
    Lefschetz11CarrierAdapter M S Q :=
  {
    ClassicalH2Q := C.ClassicalH2Q
    ClassicalDivisor := D.ClassicalDivisor
    toClassicalH2Q := C.toClassicalH2Q
    fromClassicalH2Q := C.fromClassicalH2Q
    from_to := C.from_to
    to_from := C.to_from
    isClassicalH11 := C.isClassicalH11
    typePP_iff_classicalH11 := C.typePP_iff_classicalH11
    divisorClass := D.divisorClass
    divisorToCombination := D.divisorToCombination
    divisorCycleClassCompatibility := D.divisorCycleClassCompatibility
  }

/-- Exact external theorem interface for Lefschetz (1,1).
    It remains an explicit theorem hypothesis and is never declared as an
    axiom. -/
def Lefschetz11ClassicalStatement
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    {S : SpreadData G X 1 α hX hα}
    {Q : QbarHodgePointData S}
    (A : Lefschetz11CarrierAdapter M S Q) : Prop :=
  ∀ β : A.ClassicalH2Q,
    A.isClassicalH11 β →
    ∃ D : A.ClassicalDivisor,
      A.divisorClass D = β

/-- With a real carrier match plus the external classical theorem, the p=1
    R2 witness is constructed. -/
theorem lefschetz11_adapter_closes_r2
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    {S : SpreadData G X 1 α hX hα}
    {Q : QbarHodgePointData S}
    (A : Lefschetz11CarrierAdapter M S Q)
    (hL11 : Lefschetz11ClassicalStatement A) :
    Nonempty (R2FiberCycleData M S Q) := by
  have h11 :
      A.isClassicalH11
        (A.toClassicalH2Q (S.transportedAlpha Q.path)) :=
    (A.typePP_iff_classicalH11
      (S.transportedAlpha Q.path)).1 Q.y_is_hodge
  rcases hL11
      (A.toClassicalH2Q (S.transportedAlpha Q.path)) h11 with
    ⟨D, hD⟩
  refine ⟨{
    combination := A.divisorToCombination D
    combination_class := ?_
  }⟩
  calc
    (A.divisorToCombination D).eval M =
        A.fromClassicalH2Q (A.divisorClass D) :=
      A.divisorCycleClassCompatibility D
    _ = A.fromClassicalH2Q
        (A.toClassicalH2Q (S.transportedAlpha Q.path)) := by
      rw [hD]
    _ = S.transportedAlpha Q.path :=
      A.from_to (S.transportedAlpha Q.path)

/-- Audit object witnessing that the frozen carrier has actually been matched
    to the classical degree-two/H^(1,1)/divisor package.  Existence of this
    object is the semantic-adapter obligation. -/
structure Lefschetz11CarrierSemanticMatch
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    (S : SpreadData G X 1 α hX hα)
    (Q : QbarHodgePointData S) where
  comparison : DegreeTwoHodgeComparison S Q
  divisorRealization : DivisorCycleRealization M S Q comparison
  smoothProjectiveHypothesisMatched : G.isSmoothProjective (S.Family Q.y)

/-- The exact carrier adapter extracted from a semantic-match witness. -/
def Lefschetz11CarrierSemanticMatch.adapter
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    {S : SpreadData G X 1 α hX hα}
    {Q : QbarHodgePointData S}
    (SM : Lefschetz11CarrierSemanticMatch M S Q) :
    Lefschetz11CarrierAdapter M S Q :=
  lefschetz11AdapterOfPieces SM.comparison SM.divisorRealization

/-- The exact current semantic-match proposition: an inhabitant must be
    constructed; no Bool is allowed to manufacture a GREEN state. -/
def Lefschetz11CarrierSemanticMatchComplete
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    (S : SpreadData G X 1 α hX hα)
    (Q : QbarHodgePointData S) : Prop :=
  Nonempty (Lefschetz11CarrierSemanticMatch M S Q)

/-- A completed semantic match plus the still-external classical theorem
    closes R2 for p=1. -/
theorem semantic_match_modulo_classical_closes_r2
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    {S : SpreadData G X 1 α hX hα}
    {Q : QbarHodgePointData S}
    (SM : Lefschetz11CarrierSemanticMatch M S Q)
    (hL11 : Lefschetz11ClassicalStatement SM.adapter) :
    Nonempty (R2FiberCycleData M S Q) :=
  lefschetz11_adapter_closes_r2 SM.adapter hL11

/-- The theorem itself remains externally supplied even after carrier matching. -/
def lefschetz11ClassicalTheoremInternal : Bool := false

theorem lefschetz11_remains_external :
    lefschetz11ClassicalTheoremInternal = false := by
  rfl

#print axioms HodgeR2Lefschetz11Audit.lefschetz11AdapterOfPieces
#print axioms HodgeR2Lefschetz11Audit.Lefschetz11CarrierSemanticMatch.adapter
#print axioms HodgeR2Lefschetz11Audit.lefschetz11_adapter_closes_r2
#print axioms HodgeR2Lefschetz11Audit.semantic_match_modulo_classical_closes_r2
#print axioms HodgeR2Lefschetz11Audit.lefschetz11_remains_external

end HodgeR2Lefschetz11Audit
