import MCore.BackwardAudit.R3aPathMatchedBridge

namespace MCore.BackwardAudit

/-!
# R3a semantic relative-cycle firewall

The legacy RelativeCycleEndpointData interface stores only a carrier together
with source and target maps.  It does not itself encode flatness, a universal
family, specialization compatibility, or any other geometric condition.

This module proves that weakness explicitly and introduces a stronger external
semantic boundary.  No geometric existence theorem is asserted.
-/

/-- Given only one source cycle and one target cycle, the legacy endpoint type
    is trivially inhabitable.  This demonstrates that the old carrier is not a
    semantic definition of a relative algebraic cycle. -/
def legacyEndpointDataFromTwoCycles
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
    (Zy : G.CycleQ (S.Family y) p)
    (Z0 : G.CycleQ X p) :
    RelativeCycleEndpointData (M := M) (S := S) (R := R) γ :=
  {
    RelativeCycle := Unit
    sourceCycle := fun _ => Zy
    targetCycle := fun _ => Z0
  }

/-- Consequently, a Hilbert endpoint witness alone can manufacture the legacy
    universal-family adapter, with no actual universal family.  This theorem is
    a NEGATIVE CONTROL, not a geometric construction. -/
def legacyHilbertAdapterFromEndpointsOnly
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {R : ReverseTransportLaws S}
    {H : RelativeHilbertChowComponent S}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    {Z : G.CycleQ (S.Family y) p}
    (W : HilbertChowEndpointWitness H Z) :
    HilbertUniversalFamilyAdapter
      (M := M) (R := R) (γ := γ) H Z W :=
  {
    endpointData :=
      legacyEndpointDataFromTwoCycles
        (M := M) (R := R) γ Z W.targetCycleInOriginal
    relativeCycle := ()
    source_is_Z := rfl
    target_is_hilbert_member := rfl
  }

/-- Even the quantified legacy R3a extension is mechanically obtainable from
    an arbitrary target-cycle choice function.  Therefore the legacy extension
    interface cannot by itself certify geometric extension. -/
def legacyEndpointDataFromTargetChoice
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
    (target : G.CycleQ (S.Family y) p → G.CycleQ X p) :
    RelativeCycleEndpointData (M := M) (S := S) (R := R) γ :=
  {
    RelativeCycle := G.CycleQ (S.Family y) p
    sourceCycle := fun Z => Z
    targetCycle := target
  }

def legacyExtensionFromTargetChoice
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
    (target : G.CycleQ (S.Family y) p → G.CycleQ X p) :
    RelativeCycleExtension
      (legacyEndpointDataFromTargetChoice
        (M := M) (R := R) γ target) :=
  {
    extendCycle := fun Z => Z
    source_extend := by
      intro Z
      rfl
  }

/-- Concrete semantic model expected from a genuine algebraic-geometric
    backend.  The predicates are intentionally external obligations: the core
    does not pretend to know what flat/proper relative-cycle geometry means.

A real backend should instantiate these fields with actual scheme/Hilbert/Chow
objects and prove the laws from the relevant geometric library or literature.
-/
structure GenuineRelativeCycleModel
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
    (γ : S.Path S.basepoint y) where
  RelativeObject : Type
  sourceRestriction :
    RelativeObject → G.CycleQ (S.Family y) p
  targetRestriction :
    RelativeObject → G.CycleQ X p
  IsGeometricRelativeCycle : RelativeObject → Prop
  IsPathMatched : RelativeObject → Prop
  IsSpecializationCompatible : RelativeObject → Prop

/-- Strong R3a extension: every source cycle has a genuine relative object,
    with explicit semantic certificates. -/
structure GenuineRelativeCycleExtension
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
    (C : GenuineRelativeCycleModel (M := M) (R := R) γ) where
  extendCycle :
    G.CycleQ (S.Family y) p → C.RelativeObject
  source_extend :
    ∀ Z : G.CycleQ (S.Family y) p,
      C.sourceRestriction (extendCycle Z) = Z
  geometric :
    ∀ Z : G.CycleQ (S.Family y) p,
      C.IsGeometricRelativeCycle (extendCycle Z)
  pathMatched :
    ∀ Z : G.CycleQ (S.Family y) p,
      C.IsPathMatched (extendCycle Z)
  specializationCompatible :
    ∀ Z : G.CycleQ (S.Family y) p,
      C.IsSpecializationCompatible (extendCycle Z)

/-- Forgetting semantics recovers the legacy endpoint carrier.  This direction
    is safe; the reverse direction is intentionally absent. -/
def legacyEndpointDataOfGenuineModel
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
    (C : GenuineRelativeCycleModel (M := M) (R := R) γ) :
    RelativeCycleEndpointData (M := M) (S := S) (R := R) γ :=
  {
    RelativeCycle := C.RelativeObject
    sourceCycle := C.sourceRestriction
    targetCycle := C.targetRestriction
  }

/-- Genuine semantic extension safely implies the legacy quantified extension. -/
def legacyExtensionOfGenuineExtension
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
    {C : GenuineRelativeCycleModel (M := M) (R := R) γ}
    (E : GenuineRelativeCycleExtension C) :
    RelativeCycleExtension (legacyEndpointDataOfGenuineModel C) :=
  {
    extendCycle := E.extendCycle
    source_extend := E.source_extend
  }

inductive R3aSemanticStatus where
  | provedFirewall
  | legacyInterfaceRejected
  | openConcreteSemanticModel
  | openGenuineExtension
  deriving Repr, DecidableEq

structure R3aSemanticFrontier where
  legacyAdapterCanBeTrivial : R3aSemanticStatus
  legacyPromotion : R3aSemanticStatus
  concreteSemanticModel : R3aSemanticStatus
  genuineRelativeExtension : R3aSemanticStatus
  genuineToLegacyForgetfulMap : R3aSemanticStatus

def r3aSemanticFrontier : R3aSemanticFrontier :=
  {
    legacyAdapterCanBeTrivial := .provedFirewall
    legacyPromotion := .legacyInterfaceRejected
    concreteSemanticModel := .openConcreteSemanticModel
    genuineRelativeExtension := .openGenuineExtension
    genuineToLegacyForgetfulMap := .provedFirewall
  }

theorem r3a_legacy_interface_rejected :
    r3aSemanticFrontier.legacyPromotion = .legacyInterfaceRejected := rfl

theorem r3a_concrete_semantic_model_open :
    r3aSemanticFrontier.concreteSemanticModel =
      .openConcreteSemanticModel := rfl

theorem r3a_genuine_extension_open :
    r3aSemanticFrontier.genuineRelativeExtension =
      .openGenuineExtension := rfl

#print axioms MCore.BackwardAudit.legacyEndpointDataFromTwoCycles
#print axioms MCore.BackwardAudit.legacyHilbertAdapterFromEndpointsOnly
#print axioms MCore.BackwardAudit.legacyEndpointDataFromTargetChoice
#print axioms MCore.BackwardAudit.legacyExtensionFromTargetChoice
#print axioms MCore.BackwardAudit.legacyEndpointDataOfGenuineModel
#print axioms MCore.BackwardAudit.legacyExtensionOfGenuineExtension
#print axioms MCore.BackwardAudit.r3a_legacy_interface_rejected
#print axioms MCore.BackwardAudit.r3a_concrete_semantic_model_open
#print axioms MCore.BackwardAudit.r3a_genuine_extension_open

end MCore.BackwardAudit
