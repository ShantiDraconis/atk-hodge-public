import MCore.BackwardAudit.R3aSemanticRelativeCycle
import MCore.BackwardAudit.R3SpecializationBoundary

namespace MCore.BackwardAudit

/-!
# R3a valuative relative-cycle cut

A standard relative-cycle criterion is valuative: a family of cycles on fibres
must be compatible with specialization after every DVR test.  This module does
not claim the algebraic geometry needed to construct such a family.  It only
types the exact obligations and proves that satisfying them yields the stronger
semantic R3a interface.

This keeps the core fail-closed: endpoint data alone is insufficient, and even
a path-matched family must still satisfy all valuative specialization tests.
-/

/-- A dependent family of codimension-p cycles over every fibre of S. -/
def CycleFamilyOnFibres
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Type :=
  ∀ b : S.Base, G.CycleQ (S.Family b) p

/-- Abstract DVR-test system for the spread.

A concrete backend should interpret Test as morphisms Spec(R) -> S from DVRs,
with genericPoint and specialPoint their images in the base.  Specializes is
the actual specialization relation/map on cycles for that DVR pullback.
-/
structure DVRTestSystem
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  Test : Type
  genericPoint : Test → S.Base
  specialPoint : Test → S.Base
  Specializes :
    ∀ t : Test,
      G.CycleQ (S.Family (genericPoint t)) p →
      G.CycleQ (S.Family (specialPoint t)) p →
      Prop

def IsDVRCompatible
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (V : DVRTestSystem S)
    (F : CycleFamilyOnFibres S) : Prop :=
  ∀ t : V.Test,
    V.Specializes t
      (F (V.genericPoint t))
      (F (V.specialPoint t))

/-- Additional path/cohomology semantics required by R3.  They remain
external obligations; the valuative criterion only addresses the relative
cycle part. -/
structure ValuativePathSemantics
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {R : ReverseTransportLaws S}
    {y : S.Base}
    (γ : S.Path S.basepoint y)
    (V : DVRTestSystem S) where
  IsPathMatched :
    CycleFamilyOnFibres S → Prop
  IsCycleClassCompatible :
    CycleFamilyOnFibres S → Prop

/-- The valuative model: its relative objects are actual cycle families on all
fibres, and geometric validity is exactly DVR compatibility. -/
def genuineModelOfValuativeSemantics
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {R : ReverseTransportLaws S}
    {y : S.Base}
    (γ : S.Path S.basepoint y)
    (V : DVRTestSystem S)
    (P : ValuativePathSemantics (M := M) (R := R) γ V) :
    GenuineRelativeCycleModel (M := M) (R := R) γ :=
  {
    RelativeObject := CycleFamilyOnFibres S
    sourceRestriction := fun F => F y
    targetRestriction := fun F =>
      castCycle G S.fiberAtBasepoint (F S.basepoint)
    IsGeometricRelativeCycle := IsDVRCompatible V
    IsPathMatched := P.IsPathMatched
    IsSpecializationCompatible := P.IsCycleClassCompatible
  }

/-- Exact valuative R3a existence obligation for one source fibre/path. -/
structure ValuativeRelativeCycleExtension
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {R : ReverseTransportLaws S}
    {y : S.Base}
    (γ : S.Path S.basepoint y)
    (V : DVRTestSystem S)
    (P : ValuativePathSemantics (M := M) (R := R) γ V) where
  familyFor :
    G.CycleQ (S.Family y) p → CycleFamilyOnFibres S
  sourceFiber :
    ∀ Z : G.CycleQ (S.Family y) p,
      familyFor Z y = Z
  dvrCompatible :
    ∀ Z : G.CycleQ (S.Family y) p,
      IsDVRCompatible V (familyFor Z)
  pathMatched :
    ∀ Z : G.CycleQ (S.Family y) p,
      P.IsPathMatched (familyFor Z)
  cycleClassCompatible :
    ∀ Z : G.CycleQ (S.Family y) p,
      P.IsCycleClassCompatible (familyFor Z)

/-- Valuative extension data safely constructs the stronger genuine semantic
extension. -/
def genuineExtensionOfValuativeExtension
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {R : ReverseTransportLaws S}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    {V : DVRTestSystem S}
    {P : ValuativePathSemantics (M := M) (R := R) γ V}
    (E : ValuativeRelativeCycleExtension
      (M := M) (R := R) γ V P) :
    GenuineRelativeCycleExtension
      (genuineModelOfValuativeSemantics
        (M := M) (R := R) γ V P) :=
  {
    extendCycle := E.familyFor
    source_extend := E.sourceFiber
    geometric := E.dvrCompatible
    pathMatched := E.pathMatched
    specializationCompatible := E.cycleClassCompatible
  }

/-- Therefore a valuative extension also yields the old legacy R3a carrier,
but only through the stronger semantic boundary. -/
def legacyExtensionOfValuativeExtension
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {R : ReverseTransportLaws S}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    {V : DVRTestSystem S}
    {P : ValuativePathSemantics (M := M) (R := R) γ V}
    (E : ValuativeRelativeCycleExtension
      (M := M) (R := R) γ V P) :
    RelativeCycleExtension
      (legacyEndpointDataOfGenuineModel
        (genuineModelOfValuativeSemantics
          (M := M) (R := R) γ V P)) :=
  legacyExtensionOfGenuineExtension
    (genuineExtensionOfValuativeExtension E)

/-- Negative-control DVR system: one test whose specialization relation is
always false. -/
def impossibleDVRTestSystem
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (y : S.Base) :
    DVRTestSystem S :=
  {
    Test := Unit
    genericPoint := fun _ => y
    specialPoint := fun _ => S.basepoint
    Specializes := fun _ _ _ => False
  }

/-- Endpoint values alone cannot imply DVR compatibility: with the impossible
test system no family can pass the single specialization test. -/
theorem endpoint_family_does_not_imply_dvr_compatibility
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (y : S.Base)
    (F : CycleFamilyOnFibres S) :
    ¬ IsDVRCompatible (impossibleDVRTestSystem y) F := by
  intro h
  exact h ()

inductive R3aValuativeStatus where
  | provedReduction
  | rejectedEndpointOnly
  | openDVRSystemSemantics
  | openValuativeExtension
  | openPathCompatibility
  deriving Repr, DecidableEq

structure R3aValuativeFrontier where
  valuativeToGenuine : R3aValuativeStatus
  endpointOnlyPromotion : R3aValuativeStatus
  dvrSystemSemantics : R3aValuativeStatus
  valuativeExtensionExistence : R3aValuativeStatus
  pathAndClassCompatibility : R3aValuativeStatus

def r3aValuativeFrontier : R3aValuativeFrontier :=
  {
    valuativeToGenuine := .provedReduction
    endpointOnlyPromotion := .rejectedEndpointOnly
    dvrSystemSemantics := .openDVRSystemSemantics
    valuativeExtensionExistence := .openValuativeExtension
    pathAndClassCompatibility := .openPathCompatibility
  }

theorem r3a_valuative_to_genuine_proved :
    r3aValuativeFrontier.valuativeToGenuine = .provedReduction := rfl

theorem r3a_endpoint_only_promotion_rejected :
    r3aValuativeFrontier.endpointOnlyPromotion = .rejectedEndpointOnly := rfl

theorem r3a_dvr_semantics_open :
    r3aValuativeFrontier.dvrSystemSemantics =
      .openDVRSystemSemantics := rfl

theorem r3a_valuative_extension_open :
    r3aValuativeFrontier.valuativeExtensionExistence =
      .openValuativeExtension := rfl

#print axioms MCore.BackwardAudit.genuineModelOfValuativeSemantics
#print axioms MCore.BackwardAudit.genuineExtensionOfValuativeExtension
#print axioms MCore.BackwardAudit.legacyExtensionOfValuativeExtension
#print axioms MCore.BackwardAudit.endpoint_family_does_not_imply_dvr_compatibility
#print axioms MCore.BackwardAudit.r3a_valuative_to_genuine_proved
#print axioms MCore.BackwardAudit.r3a_endpoint_only_promotion_rejected
#print axioms MCore.BackwardAudit.r3a_dvr_semantics_open
#print axioms MCore.BackwardAudit.r3a_valuative_extension_open

end MCore.BackwardAudit
