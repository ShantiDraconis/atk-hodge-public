import MCore.BackwardAudit.R3RelativeCycleCut
import MCore.BackwardAudit.R3SpecializationBoundary

namespace MCore.BackwardAudit

/-!
# R3a Hilbert/Chow properness cut

This is a typed stub for the exact geometric route needed by R3a.

The key logical point is deliberately fail-closed:

* properness / universal closedness gives CLOSED IMAGE;
* dominance gives DENSE IMAGE;
* closed + dense gives SURJECTIVITY onto the base;
* only then can one obtain a point of the same Hilbert/Chow component over the
  distinguished basepoint.

No theorem below asserts that the required Hilbert/Chow component exists for an
arbitrary source cycle, nor that it is proper or dominant. Those remain the
geometric inputs to be supplied by a concrete algebraic-geometric backend.
-/

structure ClosureInterface (B : Type) where
  closure : (B → Prop) → B → Prop
  subset_closure :
    ∀ (A : B → Prop) (b : B), A b → closure A b

def ClosureInterface.IsClosed
    {B : Type} (T : ClosureInterface B) (A : B → Prop) : Prop :=
  ∀ b : B, T.closure A b → A b

def ClosureInterface.IsDense
    {B : Type} (T : ClosureInterface B) (A : B → Prop) : Prop :=
  ∀ b : B, T.closure A b

theorem closed_dense_is_all
    {B : Type}
    (T : ClosureInterface B)
    (A : B → Prop)
    (hClosed : T.IsClosed A)
    (hDense : T.IsDense A) :
    ∀ b : B, A b := by
  intro b
  exact hClosed b (hDense b)


/-- Negative control: closed image alone does not imply surjectivity. -/
def discreteBoolClosure : ClosureInterface Bool :=
  {
    closure := fun A => A
    subset_closure := by
      intro A b hb
      exact hb
  }

def singletonTrueImage : Bool → Prop :=
  fun b => b = true

theorem singletonTrueImage_closed :
    discreteBoolClosure.IsClosed singletonTrueImage := by
  intro b hb
  exact hb

theorem closed_image_alone_not_surjective :
    ¬ (∀ b : Bool, singletonTrueImage b) := by
  intro h
  have hf : false = true := h false
  cases hf

structure RelativeHilbertChowComponent
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  PointAt : S.Base → Type
  cycleAt :
    ∀ (b : S.Base), PointAt b → G.CycleQ (S.Family b) p

def hilbertChowImage
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H : RelativeHilbertChowComponent S) :
    S.Base → Prop :=
  fun b => Nonempty (H.PointAt b)

structure ProperDominantComponentLaws
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (T : ClosureInterface S.Base)
    (H : RelativeHilbertChowComponent S) : Prop where
  imageClosed :
    T.IsClosed (hilbertChowImage H)
  imageDense :
    T.IsDense (hilbertChowImage H)

theorem proper_dominant_component_reaches
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (T : ClosureInterface S.Base)
    (H : RelativeHilbertChowComponent S)
    (L : ProperDominantComponentLaws T H)
    (b : S.Base) :
    Nonempty (H.PointAt b) :=
  closed_dense_is_all T (hilbertChowImage H)
    L.imageClosed L.imageDense b

theorem proper_dominant_component_reaches_basepoint
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (T : ClosureInterface S.Base)
    (H : RelativeHilbertChowComponent S)
    (L : ProperDominantComponentLaws T H) :
    Nonempty (H.PointAt S.basepoint) :=
  proper_dominant_component_reaches T H L S.basepoint

structure HilbertChowSourceWitness
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H : RelativeHilbertChowComponent S)
    {y : S.Base}
    (Z : G.CycleQ (S.Family y) p) where
  point : H.PointAt y
  represents :
    H.cycleAt y point = Z

structure HilbertChowEndpointWitness
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H : RelativeHilbertChowComponent S)
    {y : S.Base}
    (Z : G.CycleQ (S.Family y) p) where
  source : H.PointAt y
  sourceRepresents :
    H.cycleAt y source = Z
  target : H.PointAt S.basepoint

theorem hilbert_chow_endpoint_of_proper_dominant
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (T : ClosureInterface S.Base)
    (H : RelativeHilbertChowComponent S)
    (L : ProperDominantComponentLaws T H)
    {y : S.Base}
    {Z : G.CycleQ (S.Family y) p}
    (Src : HilbertChowSourceWitness H Z) :
    Nonempty (HilbertChowEndpointWitness H Z) := by
  rcases proper_dominant_component_reaches_basepoint T H L with ⟨q0⟩
  exact ⟨{
    source := Src.point
    sourceRepresents := Src.represents
    target := q0
  }⟩

def HilbertChowEndpointWitness.targetCycleInOriginal
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H : RelativeHilbertChowComponent S}
    {y : S.Base}
    {Z : G.CycleQ (S.Family y) p}
    (W : HilbertChowEndpointWitness H Z) :
    G.CycleQ X p :=
  castCycle G S.fiberAtBasepoint
    (H.cycleAt S.basepoint W.target)

structure HilbertUniversalFamilyAdapter
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
    (H : RelativeHilbertChowComponent S)
    (Z : G.CycleQ (S.Family y) p)
    (W : HilbertChowEndpointWitness H Z) where
  endpointData :
    RelativeCycleEndpointData (M := M) (S := S) (R := R) γ
  relativeCycle :
    endpointData.RelativeCycle
  source_is_Z :
    endpointData.sourceCycle relativeCycle = Z
  target_is_hilbert_member :
    endpointData.targetCycle relativeCycle =
      W.targetCycleInOriginal

inductive R3aHilbertStatus where
  | provedInternal
  | classicalGeometryInput
  | openUniversalFamilyAdapter
  deriving Repr, DecidableEq

structure R3aHilbertFrontier where
  properDenseToReachability : R3aHilbertStatus
  sourceHilbertPoint : R3aHilbertStatus
  propernessClosedImage : R3aHilbertStatus
  dominanceDenseImage : R3aHilbertStatus
  universalFamilyEndpointAdapter : R3aHilbertStatus

def r3aHilbertFrontier : R3aHilbertFrontier :=
  {
    properDenseToReachability := .provedInternal
    sourceHilbertPoint := .classicalGeometryInput
    propernessClosedImage := .classicalGeometryInput
    dominanceDenseImage := .classicalGeometryInput
    universalFamilyEndpointAdapter := .openUniversalFamilyAdapter
  }

theorem r3a_proper_dense_reachability_proved :
    r3aHilbertFrontier.properDenseToReachability = .provedInternal := rfl

theorem r3a_universal_family_adapter_open :
    r3aHilbertFrontier.universalFamilyEndpointAdapter =
      .openUniversalFamilyAdapter := rfl

#print axioms MCore.BackwardAudit.closed_dense_is_all
#print axioms MCore.BackwardAudit.singletonTrueImage_closed
#print axioms MCore.BackwardAudit.closed_image_alone_not_surjective
#print axioms MCore.BackwardAudit.proper_dominant_component_reaches
#print axioms MCore.BackwardAudit.proper_dominant_component_reaches_basepoint
#print axioms MCore.BackwardAudit.hilbert_chow_endpoint_of_proper_dominant
#print axioms MCore.BackwardAudit.HilbertChowEndpointWitness.targetCycleInOriginal
#print axioms MCore.BackwardAudit.r3a_proper_dense_reachability_proved
#print axioms MCore.BackwardAudit.r3a_universal_family_adapter_open

end MCore.BackwardAudit
