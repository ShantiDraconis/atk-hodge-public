import P05.Hodge.MathlibGeometryBridgeProbe

namespace P05.Hodge

open MCore
open AlgebraicGeometry

/-!
# Cycle-carrier compatibility shell

The legacy name is kept for repository continuity.  Under the pinned Mathlib
v4.19.0, the concrete `AlgebraicCycle` carrier is not available, so the
carrier itself is an explicit field of the bridge.  Thus this file types the
adapter but does not inhabit the missing backend.
-/

structure MathlibCycleClassBridge
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  schemeOf : G.Variety → Scheme
  CycleCarrier : G.Variety → Nat → Type
  cycleToExternal :
    ∀ (X : G.Variety) (p : Nat),
      G.CycleQ X p → CycleCarrier X p
  externalToCycle :
    ∀ (X : G.Variety) (p : Nat),
      CycleCarrier X p → G.CycleQ X p
  cycle_roundtrip :
    ∀ (X : G.Variety) (p : Nat) (z : G.CycleQ X p),
      externalToCycle X p (cycleToExternal X p z) = z

def MathlibCycleClassBridge.realizeCycle
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : MathlibCycleClassBridge G M)
    {X : G.Variety}
    {p : Nat}
    (z : G.CycleQ X p) :
    B.CycleCarrier X p :=
  B.cycleToExternal X p z

theorem MathlibCycleClassBridge.realize_roundtrip
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : MathlibCycleClassBridge G M)
    {X : G.Variety}
    {p : Nat}
    (z : G.CycleQ X p) :
    B.externalToCycle X p (B.realizeCycle z) = z :=
  B.cycle_roundtrip X p z

def mathlibBridgeFieldCount : Nat := 5

theorem mathlibBridgeFieldCount_eq_five :
    mathlibBridgeFieldCount = 5 := rfl

#print axioms P05.Hodge.MathlibCycleClassBridge.realize_roundtrip
#print axioms P05.Hodge.mathlibBridgeFieldCount_eq_five

end P05.Hodge
