import MCore.BackwardAudit.R3aHilbertProperness

namespace MCore.BackwardAudit

/-!
# R3a universal-family bridge cut

This module separates the remaining R3a universal-family residue into:

1. parameter-bridge existence between the source Hilbert/Chow point and a
   point over the distinguished base fiber;
2. pullback/evaluation of the universal family along that bridge;
3. aggregation of per-cycle relative objects into the single
   RelativeCycleExtension interface required by R3.

Endpoint reachability alone does NOT imply bridge existence.  This is enforced
by a negative control.
-/

/-- Geometry of "being connected by an admissible parameter bridge" inside a
    chosen relative Hilbert/Chow parameter space.  This may later be realized
    by an algebraic curve, trait-chain, or other concrete parameter object. -/
structure HilbertParameterBridgeGeometry
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H : RelativeHilbertChowComponent S) where
  Connected :
    ∀ {b0 b1 : S.Base},
      H.PointAt b0 → H.PointAt b1 → Prop

/-- The deliberately empty bridge relation, used as a fail-closed negative
    control. -/
def noHilbertBridges
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H : RelativeHilbertChowComponent S) :
    HilbertParameterBridgeGeometry H :=
  {
    Connected := fun _ _ => False
  }

/-- Merely possessing source and target points does not logically manufacture
    an admissible bridge between them. -/
theorem endpoint_points_do_not_imply_bridge
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
    ¬ (∀ P : HilbertParameterBridgeGeometry H,
        P.Connected W.source W.target) := by
  intro h
  exact h (noHilbertBridges H)

/-- Universal-family data pulled back along one admissible bridge.

This is the exact semantic content needed from representability/universal
family machinery: one relative object has the source and target fibre cycles
as its endpoint restrictions.
-/
structure UniversalFamilyAlongBridge
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
    (P : HilbertParameterBridgeGeometry H)
    (hBridge : P.Connected W.source W.target) where
  endpointData :
    RelativeCycleEndpointData (M := M) (S := S) (R := R) γ
  relativeCycle :
    endpointData.RelativeCycle
  source_fiber :
    endpointData.sourceCycle relativeCycle = Z
  target_fiber :
    endpointData.targetCycle relativeCycle =
      W.targetCycleInOriginal

/-- Once the pulled-back universal family is supplied, the older per-cycle
    adapter is purely mechanical. -/
def hilbertUniversalFamilyAdapterOfBridge
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
    {P : HilbertParameterBridgeGeometry H}
    {hBridge : P.Connected W.source W.target}
    (U : UniversalFamilyAlongBridge
      (M := M) (R := R) (γ := γ) W P hBridge) :
    HilbertUniversalFamilyAdapter
      (M := M) (R := R) (γ := γ) H Z W :=
  {
    endpointData := U.endpointData
    relativeCycle := U.relativeCycle
    source_is_Z := U.source_fiber
    target_is_hilbert_member := U.target_fiber
  }

/-- Generic per-cycle relative extension data.  The endpoint carrier is allowed
    to depend on Z; the theorem below aggregates these into the single carrier
    required by RelativeCycleExtension. -/
structure PerCycleRelativeExtensionData
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
  endpointFor :
    ∀ Z : G.CycleQ (S.Family y) p,
      RelativeCycleEndpointData (M := M) (S := S) (R := R) γ
  relativeFor :
    ∀ Z : G.CycleQ (S.Family y) p,
      (endpointFor Z).RelativeCycle
  sourceFor :
    ∀ Z : G.CycleQ (S.Family y) p,
      (endpointFor Z).sourceCycle (relativeFor Z) = Z

/-- Aggregate all per-cycle endpoint carriers by a sigma type. -/
def endpointDataOfPerCycle
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
    (D : PerCycleRelativeExtensionData (M := M) (R := R) γ) :
    RelativeCycleEndpointData (M := M) (S := S) (R := R) γ :=
  {
    RelativeCycle :=
      Σ Z : G.CycleQ (S.Family y) p,
        (D.endpointFor Z).RelativeCycle
    sourceCycle := fun T =>
      (D.endpointFor T.1).sourceCycle T.2
    targetCycle := fun T =>
      (D.endpointFor T.1).targetCycle T.2
  }

/-- The per-cycle adapters really are sufficient for the quantified R3a
    extension interface; no uniform endpoint carrier has to be assumed. -/
def relativeCycleExtensionOfPerCycle
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
    (D : PerCycleRelativeExtensionData (M := M) (R := R) γ) :
    RelativeCycleExtension (endpointDataOfPerCycle D) :=
  {
    extendCycle := fun Z => ⟨Z, D.relativeFor Z⟩
    source_extend := by
      intro Z
      exact D.sourceFor Z
  }

/-- A family of per-cycle Hilbert universal adapters can be converted into the
    generic per-cycle data expected by the sigma aggregation. -/
def perCycleDataOfHilbertAdapters
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
    (H :
      ∀ Z : G.CycleQ (S.Family y) p,
        Σ HC : RelativeHilbertChowComponent S,
          Σ W : HilbertChowEndpointWitness HC Z,
            HilbertUniversalFamilyAdapter
              (M := M) (R := R) (γ := γ) HC Z W) :
    PerCycleRelativeExtensionData (M := M) (R := R) γ :=
  {
    endpointFor := fun Z => (H Z).2.2.endpointData
    relativeFor := fun Z => (H Z).2.2.relativeCycle
    sourceFor := by
      intro Z
      exact (H Z).2.2.source_is_Z
  }

/-- Therefore per-cycle Hilbert universal-family adapters close the R3a
    extension quantifier mechanically. -/
def relativeCycleExtensionOfHilbertAdapters
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
    (H :
      ∀ Z : G.CycleQ (S.Family y) p,
        Σ HC : RelativeHilbertChowComponent S,
          Σ W : HilbertChowEndpointWitness HC Z,
            HilbertUniversalFamilyAdapter
              (M := M) (R := R) (γ := γ) HC Z W) :
    RelativeCycleExtension
      (endpointDataOfPerCycle (perCycleDataOfHilbertAdapters γ H)) :=
  relativeCycleExtensionOfPerCycle
    (perCycleDataOfHilbertAdapters γ H)

inductive R3aUniversalFamilyStatus where
  | provedInternal
  | rejectedShortcut
  | openBridgeExistence
  | openUniversalFamilyPullback
  deriving Repr, DecidableEq

structure R3aUniversalFamilyFrontier where
  endpointImpliesBridge : R3aUniversalFamilyStatus
  bridgeExistence : R3aUniversalFamilyStatus
  universalFamilyPullback : R3aUniversalFamilyStatus
  perCycleAggregation : R3aUniversalFamilyStatus

def r3aUniversalFamilyFrontier : R3aUniversalFamilyFrontier :=
  {
    endpointImpliesBridge := .rejectedShortcut
    bridgeExistence := .openBridgeExistence
    universalFamilyPullback := .openUniversalFamilyPullback
    perCycleAggregation := .provedInternal
  }

theorem r3a_endpoint_does_not_imply_bridge :
    r3aUniversalFamilyFrontier.endpointImpliesBridge = .rejectedShortcut := rfl

theorem r3a_per_cycle_aggregation_proved :
    r3aUniversalFamilyFrontier.perCycleAggregation = .provedInternal := rfl

theorem r3a_bridge_existence_open :
    r3aUniversalFamilyFrontier.bridgeExistence = .openBridgeExistence := rfl

theorem r3a_universal_family_pullback_open :
    r3aUniversalFamilyFrontier.universalFamilyPullback =
      .openUniversalFamilyPullback := rfl

#print axioms MCore.BackwardAudit.endpoint_points_do_not_imply_bridge
#print axioms MCore.BackwardAudit.hilbertUniversalFamilyAdapterOfBridge
#print axioms MCore.BackwardAudit.endpointDataOfPerCycle
#print axioms MCore.BackwardAudit.relativeCycleExtensionOfPerCycle
#print axioms MCore.BackwardAudit.perCycleDataOfHilbertAdapters
#print axioms MCore.BackwardAudit.relativeCycleExtensionOfHilbertAdapters
#print axioms MCore.BackwardAudit.r3a_endpoint_does_not_imply_bridge
#print axioms MCore.BackwardAudit.r3a_per_cycle_aggregation_proved
#print axioms MCore.BackwardAudit.r3a_bridge_existence_open
#print axioms MCore.BackwardAudit.r3a_universal_family_pullback_open

end MCore.BackwardAudit
