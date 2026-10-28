import MCore.BackwardAudit.R3aValuativeRelativeCycle
import MCore.BackwardAudit.R3SpecializationBoundary

namespace MCore.BackwardAudit

/-!
# R3a minimal bridge-valuative cut

This module removes two over-strong requirements from the previous semantic
boundary:

1. A relative cycle need only live over a bridge base C -> S joining y to the
   distinguished basepoint, not over every point of S.
2. R3a contains only existence of a genuine path-matched relative cycle.
   Cycle-class compatibility belongs to R3b and is NOT part of this interface.

The bridge carries its own DVR test system.  A concrete algebraic-geometric
backend should instantiate it with a curve/trait-chain or other parameter base
mapping to S and prove the valuative specialization laws there.
-/

/-- A bridge base C -> S tied to the exact path gamma used by R3. -/
structure RelativeCycleBridgeBase
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    {y : S.Base}
    (γ : S.Path S.basepoint y) where
  Base : Type
  source : Base
  target : Base
  mapToS : Base → S.Base
  source_maps_to_y : mapToS source = y
  target_maps_to_basepoint : mapToS target = S.basepoint
  ProjectsToExactPath : Prop
  projection_certified : ProjectsToExactPath

/-- A cycle family only over the bridge base C. -/
def BridgeCycleFamily
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    (C : RelativeCycleBridgeBase S γ) : Type :=
  ∀ c : C.Base, G.CycleQ (S.Family (C.mapToS c)) p

def BridgeCycleFamily.sourceRestriction
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    {C : RelativeCycleBridgeBase S γ}
    (F : BridgeCycleFamily C) :
    G.CycleQ (S.Family y) p :=
  castCycle G
    (congrArg S.Family C.source_maps_to_y)
    (F C.source)

def BridgeCycleFamily.targetRestriction
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    {C : RelativeCycleBridgeBase S γ}
    (F : BridgeCycleFamily C) :
    G.CycleQ X p :=
  castCycle G
    ((congrArg S.Family C.target_maps_to_basepoint).trans
      S.fiberAtBasepoint)
    (F C.target)

/-- DVR tests internal to the bridge base C. -/
structure BridgeDVRTestSystem
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    (C : RelativeCycleBridgeBase S γ) where
  Test : Type
  genericPoint : Test → C.Base
  specialPoint : Test → C.Base
  Specializes :
    ∀ t : Test,
      G.CycleQ (S.Family (C.mapToS (genericPoint t))) p →
      G.CycleQ (S.Family (C.mapToS (specialPoint t))) p →
      Prop

def IsBridgeDVRCompatible
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    {C : RelativeCycleBridgeBase S γ}
    (V : BridgeDVRTestSystem C)
    (F : BridgeCycleFamily C) : Prop :=
  ∀ t : V.Test,
    V.Specializes t
      (F (V.genericPoint t))
      (F (V.specialPoint t))

/-- R3a-only semantic model.  There is deliberately NO cycle-class
compatibility field here; that is R3b. -/
structure GenuineR3aRelativeCycleModel
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

structure GenuineR3aExtension
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
    (C : GenuineR3aRelativeCycleModel (M := M) (R := R) γ) where
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

/-- The bridge-valuative model.  Geometric validity is exactly DVR
compatibility on C; path matching comes from the certified projection C -> S.
-/
def genuineR3aModelOfBridgeValuative
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
    (C : RelativeCycleBridgeBase S γ)
    (V : BridgeDVRTestSystem C) :
    GenuineR3aRelativeCycleModel (M := M) (R := R) γ :=
  {
    RelativeObject := BridgeCycleFamily C
    sourceRestriction := BridgeCycleFamily.sourceRestriction
    targetRestriction := BridgeCycleFamily.targetRestriction
    IsGeometricRelativeCycle := IsBridgeDVRCompatible V
    IsPathMatched := fun _ => C.ProjectsToExactPath
  }

/-- Minimal R3a existence payload: for every source cycle, construct a cycle
family on the bridge satisfying every DVR test. -/
structure BridgeValuativeR3aExtension
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
    (C : RelativeCycleBridgeBase S γ)
    (V : BridgeDVRTestSystem C) where
  familyFor :
    G.CycleQ (S.Family y) p → BridgeCycleFamily C
  sourceFiber :
    ∀ Z : G.CycleQ (S.Family y) p,
      (familyFor Z).sourceRestriction = Z
  dvrCompatible :
    ∀ Z : G.CycleQ (S.Family y) p,
      IsBridgeDVRCompatible V (familyFor Z)

/-- Bridge-valuative R3a data constructs the exact stronger R3a semantic
extension; path matching is discharged by the bridge certificate itself. -/
def genuineR3aExtensionOfBridgeValuative
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
    {C : RelativeCycleBridgeBase S γ}
    {V : BridgeDVRTestSystem C}
    (E : BridgeValuativeR3aExtension (M := M) (R := R) γ C V) :
    GenuineR3aExtension
      (genuineR3aModelOfBridgeValuative
        (M := M) (R := R) γ C V) :=
  {
    extendCycle := E.familyFor
    source_extend := E.sourceFiber
    geometric := E.dvrCompatible
    pathMatched := by
      intro Z
      exact C.projection_certified
  }

/-- Forgetting only R3a semantics yields the legacy endpoint/extension carrier.
This direction is safe and makes no cycle-class claim. -/
def legacyEndpointDataOfGenuineR3aModel
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
    (C : GenuineR3aRelativeCycleModel (M := M) (R := R) γ) :
    RelativeCycleEndpointData (M := M) (S := S) (R := R) γ :=
  {
    RelativeCycle := C.RelativeObject
    sourceCycle := C.sourceRestriction
    targetCycle := C.targetRestriction
  }

def legacyExtensionOfGenuineR3aExtension
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
    {C : GenuineR3aRelativeCycleModel (M := M) (R := R) γ}
    (E : GenuineR3aExtension C) :
    RelativeCycleExtension (legacyEndpointDataOfGenuineR3aModel C) :=
  {
    extendCycle := E.extendCycle
    source_extend := E.source_extend
  }

/-- Negative control: a bridge with correct endpoints/path projection still
does not imply valuative compatibility. -/
def impossibleBridgeDVRTestSystem
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    (C : RelativeCycleBridgeBase S γ) :
    BridgeDVRTestSystem C :=
  {
    Test := Unit
    genericPoint := fun _ => C.source
    specialPoint := fun _ => C.target
    Specializes := fun _ _ _ => False
  }

theorem path_matched_bridge_does_not_imply_valuative_cycle
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    (C : RelativeCycleBridgeBase S γ)
    (F : BridgeCycleFamily C) :
    ¬ IsBridgeDVRCompatible (impossibleBridgeDVRTestSystem C) F := by
  intro h
  exact h ()

inductive R3aMinimalStatus where
  | provedMinimalReduction
  | rejectedBridgeOnlyShortcut
  | openBridgeExistence
  | openDVRSpecializationSemantics
  | openRelativeCycleExistence
  deriving Repr, DecidableEq

structure R3aMinimalFrontier where
  bridgeValuativeToR3a : R3aMinimalStatus
  bridgeOnlyPromotion : R3aMinimalStatus
  bridgeExistence : R3aMinimalStatus
  dvrSpecializationSemantics : R3aMinimalStatus
  relativeCycleExistence : R3aMinimalStatus

def r3aMinimalFrontier : R3aMinimalFrontier :=
  {
    bridgeValuativeToR3a := .provedMinimalReduction
    bridgeOnlyPromotion := .rejectedBridgeOnlyShortcut
    bridgeExistence := .openBridgeExistence
    dvrSpecializationSemantics := .openDVRSpecializationSemantics
    relativeCycleExistence := .openRelativeCycleExistence
  }

theorem r3a_minimal_reduction_proved :
    r3aMinimalFrontier.bridgeValuativeToR3a =
      .provedMinimalReduction := rfl

theorem r3a_bridge_only_promotion_rejected :
    r3aMinimalFrontier.bridgeOnlyPromotion =
      .rejectedBridgeOnlyShortcut := rfl

theorem r3a_minimal_bridge_open :
    r3aMinimalFrontier.bridgeExistence =
      .openBridgeExistence := rfl

theorem r3a_minimal_dvr_semantics_open :
    r3aMinimalFrontier.dvrSpecializationSemantics =
      .openDVRSpecializationSemantics := rfl

theorem r3a_minimal_relative_cycle_open :
    r3aMinimalFrontier.relativeCycleExistence =
      .openRelativeCycleExistence := rfl

#print axioms MCore.BackwardAudit.BridgeCycleFamily.sourceRestriction
#print axioms MCore.BackwardAudit.BridgeCycleFamily.targetRestriction
#print axioms MCore.BackwardAudit.genuineR3aModelOfBridgeValuative
#print axioms MCore.BackwardAudit.genuineR3aExtensionOfBridgeValuative
#print axioms MCore.BackwardAudit.legacyExtensionOfGenuineR3aExtension
#print axioms MCore.BackwardAudit.path_matched_bridge_does_not_imply_valuative_cycle
#print axioms MCore.BackwardAudit.r3a_minimal_reduction_proved
#print axioms MCore.BackwardAudit.r3a_bridge_only_promotion_rejected
#print axioms MCore.BackwardAudit.r3a_minimal_bridge_open
#print axioms MCore.BackwardAudit.r3a_minimal_dvr_semantics_open
#print axioms MCore.BackwardAudit.r3a_minimal_relative_cycle_open

end MCore.BackwardAudit
