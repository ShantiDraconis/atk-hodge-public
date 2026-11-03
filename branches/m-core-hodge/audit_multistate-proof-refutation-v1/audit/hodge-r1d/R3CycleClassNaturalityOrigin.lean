import MCore.BackwardAudit.R1DescentBoundary

namespace HodgeR3NaturalityOriginAudit

open MCore
open MCore.BackwardAudit

/-- Cohomological return map used by the relative-cycle-class square. -/
structure CohomologyReturnOrigin
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S) where
  returnCohomology :
    G.CohomologyQ (S.Family Q.y) (2 * p) →
    G.CohomologyQ X (2 * p)

/-- A relative-cycle object whose two fiber realizations are actual frozen
    CycleCombination values. No final algebraicity predicate occurs here. -/
structure RelativeCycleClassOrigin
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S)
    (R : CohomologyReturnOrigin S Q) where

  RelativeCycle : Type

  liftFromSelectedFiber :
    CycleCombination G M (S.Family Q.y) p →
    RelativeCycle

  specializeToOriginalFiber :
    RelativeCycle →
    CycleCombination G M X p

  relativeClassAtSelectedFiber :
    RelativeCycle →
    G.CohomologyQ (S.Family Q.y) (2 * p)

  relativeClassAtOriginalFiber :
    RelativeCycle →
    G.CohomologyQ X (2 * p)

  liftClassCompatibility :
    ∀ c : CycleCombination G M (S.Family Q.y) p,
      relativeClassAtSelectedFiber (liftFromSelectedFiber c) =
        c.eval M

  specializationClassCompatibility :
    ∀ z : RelativeCycle,
      (specializeToOriginalFiber z).eval M =
        relativeClassAtOriginalFiber z

  relativeClassNaturality :
    ∀ z : RelativeCycle,
      relativeClassAtOriginalFiber z =
        R.returnCohomology (relativeClassAtSelectedFiber z)

/-- Minimal abstract backend for the missing relative Chow/Hilbert geometry.
    Properness and flatness are predicates ON CONCRETE MORPHISMS, never loose
    propositions.  The backend is still only an audit interface: constructing
    an inhabitant from genuine algebraic geometry remains open. -/
structure RelativeChowHilbertBackend
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S) where

  GeometricObject : Type
  Morphism : GeometricObject → GeometricObject → Type

  IsProper :
    {A B : GeometricObject} →
    Morphism A B → Prop

  IsFlat :
    {A B : GeometricObject} →
    Morphism A B → Prop

  baseObject : GeometricObject
  relativeParameterObject : GeometricObject
  universalCycleObject : GeometricObject

  parameterProjection :
    Morphism relativeParameterObject baseObject

  universalCycleProjection :
    Morphism universalCycleObject relativeParameterObject

  parameterProjection_isProper :
    IsProper parameterProjection

  universalCycleProjection_isFlat :
    IsFlat universalCycleProjection

  RelativeCycle : Type

  liftFromSelectedFiber :
    CycleCombination G M (S.Family Q.y) p →
    RelativeCycle

  specializeToOriginalFiber :
    RelativeCycle →
    CycleCombination G M X p

/-- Relative cycle-class map attached to a concrete Chow/Hilbert backend. -/
structure HasRelativeCycleClassMap
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    {R : CohomologyReturnOrigin S Q}
    (B : RelativeChowHilbertBackend M S Q) where

  classAtSelectedFiber :
    B.RelativeCycle →
    G.CohomologyQ (S.Family Q.y) (2 * p)

  classAtOriginalFiber :
    B.RelativeCycle →
    G.CohomologyQ X (2 * p)

  liftClassCompatibility :
    ∀ c : CycleCombination G M (S.Family Q.y) p,
      classAtSelectedFiber (B.liftFromSelectedFiber c) =
        c.eval M

  specializationClassCompatibility :
    ∀ z : B.RelativeCycle,
      (B.specializeToOriginalFiber z).eval M =
        classAtOriginalFiber z

  specialization_commutes :
    ∀ z : B.RelativeCycle,
      classAtOriginalFiber z =
        R.returnCohomology (classAtSelectedFiber z)

/-- Chow/Hilbert backend plus relative cycle-class map constructs the exact
    RelativeCycleClassOrigin required by the non-circular G4 factorization. -/
def relativeOriginOfChowHilbert
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    {R : CohomologyReturnOrigin S Q}
    (B : RelativeChowHilbertBackend M S Q)
    (C : HasRelativeCycleClassMap (R := R) B) :
    RelativeCycleClassOrigin M S Q R :=
  {
    RelativeCycle := B.RelativeCycle
    liftFromSelectedFiber := B.liftFromSelectedFiber
    specializeToOriginalFiber := B.specializeToOriginalFiber
    relativeClassAtSelectedFiber := C.classAtSelectedFiber
    relativeClassAtOriginalFiber := C.classAtOriginalFiber
    liftClassCompatibility := C.liftClassCompatibility
    specializationClassCompatibility := C.specializationClassCompatibility
    relativeClassNaturality := C.specialization_commutes
  }

/-- The relative-cycle-class square induces exactly the naturality equation
    required by factorized G4. -/
theorem relative_origin_yields_cycle_class_naturality
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    {R : CohomologyReturnOrigin S Q}
    (O : RelativeCycleClassOrigin M S Q R)
    (c : CycleCombination G M (S.Family Q.y) p) :
    (O.specializeToOriginalFiber
      (O.liftFromSelectedFiber c)).eval M =
      R.returnCohomology (c.eval M) := by
  calc
    (O.specializeToOriginalFiber
      (O.liftFromSelectedFiber c)).eval M =
        O.relativeClassAtOriginalFiber
          (O.liftFromSelectedFiber c) :=
      O.specializationClassCompatibility
        (O.liftFromSelectedFiber c)
    _ =
        R.returnCohomology
          (O.relativeClassAtSelectedFiber
            (O.liftFromSelectedFiber c)) :=
      O.relativeClassNaturality
        (O.liftFromSelectedFiber c)
    _ = R.returnCohomology (c.eval M) := by
      rw [O.liftClassCompatibility c]

/-- The same naturality theorem specialized to a Chow/Hilbert origin. -/
theorem chow_hilbert_origin_yields_cycle_class_naturality
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    {R : CohomologyReturnOrigin S Q}
    (B : RelativeChowHilbertBackend M S Q)
    (C : HasRelativeCycleClassMap (R := R) B)
    (c : CycleCombination G M (S.Family Q.y) p) :
    (B.specializeToOriginalFiber
      (B.liftFromSelectedFiber c)).eval M =
      R.returnCohomology (c.eval M) :=
  relative_origin_yields_cycle_class_naturality
    (relativeOriginOfChowHilbert (R := R) B C) c

/-- Construction of a real Chow/Hilbert backend is the remaining semantic
    geometry obligation. -/
def relativeChowHilbertSemanticMatchComplete : Bool := false

theorem relative_chow_hilbert_semantic_match_still_open :
    relativeChowHilbertSemanticMatchComplete = false := by
  rfl

#print axioms HodgeR3NaturalityOriginAudit.relativeOriginOfChowHilbert
#print axioms HodgeR3NaturalityOriginAudit.relative_origin_yields_cycle_class_naturality
#print axioms HodgeR3NaturalityOriginAudit.chow_hilbert_origin_yields_cycle_class_naturality
#print axioms HodgeR3NaturalityOriginAudit.relative_chow_hilbert_semantic_match_still_open

end HodgeR3NaturalityOriginAudit
