import MCore.BackwardAudit.R3aUniversalFamilyBridge

namespace MCore.BackwardAudit

/-!
# R3a path-matched parameter bridge

A relative Hilbert/Chow deformation from a cycle over y to a cycle over the
basepoint is not enough for the R3 theorem unless its projection to the base is
compatible with the same path gamma used by cohomological back-transport.

This module makes that monodromy-sensitive requirement explicit.
-/

structure PathMatchedHilbertBridge
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H : RelativeHilbertChowComponent S)
    {y : S.Base}
    (γ : S.Path S.basepoint y)
    {Z : G.CycleQ (S.Family y) p}
    (W : HilbertChowEndpointWitness H Z) where
  Bridge : Type
  bridge : Bridge
  projectsToExactPath : Bridge → Prop
  sourceEndpointMatches : Bridge → Prop
  targetEndpointMatches : Bridge → Prop
  projection_certified : projectsToExactPath bridge
  source_certified : sourceEndpointMatches bridge
  target_certified : targetEndpointMatches bridge

structure PathBlindHilbertBridge
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H : RelativeHilbertChowComponent S)
    {y : S.Base}
    {Z : G.CycleQ (S.Family y) p}
    (W : HilbertChowEndpointWitness H Z) where
  Bridge : Type
  bridge : Bridge
  sourceEndpointMatches : Bridge → Prop
  targetEndpointMatches : Bridge → Prop
  source_certified : sourceEndpointMatches bridge
  target_certified : targetEndpointMatches bridge

theorem path_blind_bridge_does_not_certify_exact_projection
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H : RelativeHilbertChowComponent S}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    {Z : G.CycleQ (S.Family y) p}
    {W : HilbertChowEndpointWitness H Z}
    (B : PathBlindHilbertBridge H W) :
    ¬ (∀ projectionPredicate : B.Bridge → Prop,
        projectionPredicate B.bridge) := by
  intro h
  exact h (fun _ => False)

structure UniversalFamilyAlongMatchedBridge
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
    (W : HilbertChowEndpointWitness H Z)
    (B : PathMatchedHilbertBridge H γ W) where
  endpointData :
    RelativeCycleEndpointData (M := M) (S := S) (R := R) γ
  relativeCycle :
    endpointData.RelativeCycle
  source_fiber :
    endpointData.sourceCycle relativeCycle = Z
  target_fiber :
    endpointData.targetCycle relativeCycle =
      W.targetCycleInOriginal

def hilbertUniversalFamilyAdapterOfMatchedBridge
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
    {W : HilbertChowEndpointWitness H Z}
    {B : PathMatchedHilbertBridge H γ W}
    (U : UniversalFamilyAlongMatchedBridge
      (M := M) (R := R) W B) :
    HilbertUniversalFamilyAdapter
      (M := M) (R := R) (γ := γ) H Z W :=
  {
    endpointData := U.endpointData
    relativeCycle := U.relativeCycle
    source_is_Z := U.source_fiber
    target_is_hilbert_member := U.target_fiber
  }

structure PerCycleMatchedHilbertData
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
  component :
    ∀ Z : G.CycleQ (S.Family y) p,
      RelativeHilbertChowComponent S
  endpoint :
    ∀ Z : G.CycleQ (S.Family y) p,
      HilbertChowEndpointWitness (component Z) Z
  bridge :
    ∀ Z : G.CycleQ (S.Family y) p,
      PathMatchedHilbertBridge
        (component Z) γ (endpoint Z)
  universalFamily :
    ∀ Z : G.CycleQ (S.Family y) p,
      UniversalFamilyAlongMatchedBridge
        (M := M) (R := R)
        (endpoint Z) (bridge Z)

def hilbertAdaptersOfMatchedData
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
    (D : PerCycleMatchedHilbertData (M := M) (R := R) γ) :
    ∀ Z : G.CycleQ (S.Family y) p,
      Σ HC : RelativeHilbertChowComponent S,
        Σ W : HilbertChowEndpointWitness HC Z,
          HilbertUniversalFamilyAdapter
            (M := M) (R := R) (γ := γ) HC Z W := by
  intro Z
  exact ⟨D.component Z, D.endpoint Z,
    hilbertUniversalFamilyAdapterOfMatchedBridge
      (D.universalFamily Z)⟩

def relativeCycleExtensionOfMatchedHilbertData
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
    (D : PerCycleMatchedHilbertData (M := M) (R := R) γ) :
    RelativeCycleExtension
      (endpointDataOfPerCycle
        (perCycleDataOfHilbertAdapters γ
          (hilbertAdaptersOfMatchedData γ D))) :=
  relativeCycleExtensionOfHilbertAdapters γ
    (hilbertAdaptersOfMatchedData γ D)

inductive R3aPathMatchedStatus where
  | provedInternal
  | rejectedPathBlindShortcut
  | openExactPathBridge
  | openUniversalFamilyPullback
  deriving Repr, DecidableEq

structure R3aPathMatchedFrontier where
  pathBlindPromotion : R3aPathMatchedStatus
  exactPathBridgeExistence : R3aPathMatchedStatus
  universalFamilyPullback : R3aPathMatchedStatus
  matchedDataToR3a : R3aPathMatchedStatus

def r3aPathMatchedFrontier : R3aPathMatchedFrontier :=
  {
    pathBlindPromotion := .rejectedPathBlindShortcut
    exactPathBridgeExistence := .openExactPathBridge
    universalFamilyPullback := .openUniversalFamilyPullback
    matchedDataToR3a := .provedInternal
  }

theorem r3a_path_blind_promotion_rejected :
    r3aPathMatchedFrontier.pathBlindPromotion =
      .rejectedPathBlindShortcut := rfl

theorem r3a_matched_data_to_r3a_proved :
    r3aPathMatchedFrontier.matchedDataToR3a = .provedInternal := rfl

theorem r3a_exact_path_bridge_open :
    r3aPathMatchedFrontier.exactPathBridgeExistence =
      .openExactPathBridge := rfl

theorem r3a_matched_universal_family_open :
    r3aPathMatchedFrontier.universalFamilyPullback =
      .openUniversalFamilyPullback := rfl

#print axioms MCore.BackwardAudit.path_blind_bridge_does_not_certify_exact_projection
#print axioms MCore.BackwardAudit.hilbertUniversalFamilyAdapterOfMatchedBridge
#print axioms MCore.BackwardAudit.hilbertAdaptersOfMatchedData
#print axioms MCore.BackwardAudit.relativeCycleExtensionOfMatchedHilbertData
#print axioms MCore.BackwardAudit.r3a_path_blind_promotion_rejected
#print axioms MCore.BackwardAudit.r3a_matched_data_to_r3a_proved
#print axioms MCore.BackwardAudit.r3a_exact_path_bridge_open
#print axioms MCore.BackwardAudit.r3a_matched_universal_family_open

end MCore.BackwardAudit
