import P05.Hodge.MathlibCohomologyCycleClassAdapter
import P05.Hodge.HodgeInfrastructureComplete

namespace P05.Hodge

open MCore

/-!
# Full formal realization shell

All formal interfaces needed to connect the repository's abstract Hodge model
to a concrete scheme/algebraic-cycle/cohomology realization are now collected
in one type.  Inhabiting this type still requires genuine mathematical
realization data; the shell itself is only infrastructure.
-/

structure HodgeFormalRealization
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  cycles : MathlibCycleClassBridge G M
  cohomology :
    MathlibCohomologyCycleClassAdapter G M cycles

def HodgeFormalRealization.toInfrastructureComplete
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (R : HodgeFormalRealization G M) :
    HodgeInfrastructureComplete G M :=
  { mathlibCycleBridge := R.cycles }

/-- Formal scaffolding inventory.  These are interface definitions, not
mathematical inhabitants. -/
inductive FormalScaffoldStatus
  | typed
  | inhabitantOpen
  deriving DecidableEq, Repr

structure HodgeFormalScaffoldLedger where
  schemeRealizationType : FormalScaffoldStatus
  algebraicCycleCarrierType : FormalScaffoldStatus
  cycleRoundtripType : FormalScaffoldStatus
  cohomologyCarrierType : FormalScaffoldStatus
  cohomologyRoundtripType : FormalScaffoldStatus
  cycleClassMapType : FormalScaffoldStatus
  cycleClassCompatibilityType : FormalScaffoldStatus
  concreteRealizationInhabitant : FormalScaffoldStatus
  materialMincutInhabitant : FormalScaffoldStatus
  deriving Repr

def formalScaffoldLedger : HodgeFormalScaffoldLedger :=
  {
    schemeRealizationType := .typed
    algebraicCycleCarrierType := .typed
    cycleRoundtripType := .typed
    cohomologyCarrierType := .typed
    cohomologyRoundtripType := .typed
    cycleClassMapType := .typed
    cycleClassCompatibilityType := .typed
    concreteRealizationInhabitant := .inhabitantOpen
    materialMincutInhabitant := .inhabitantOpen
  }

def typedScaffoldCount : Nat :=
  [ formalScaffoldLedger.schemeRealizationType
  , formalScaffoldLedger.algebraicCycleCarrierType
  , formalScaffoldLedger.cycleRoundtripType
  , formalScaffoldLedger.cohomologyCarrierType
  , formalScaffoldLedger.cohomologyRoundtripType
  , formalScaffoldLedger.cycleClassMapType
  , formalScaffoldLedger.cycleClassCompatibilityType
  ].foldl (fun n s => if s = .typed then n + 1 else n) 0

theorem typedScaffoldCount_eq_seven :
    typedScaffoldCount = 7 := by decide

/-- Once both genuine inhabitants are supplied, the terminal concrete payload
is obtained mechanically. -/
theorem formalRealization_plus_material_closes
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (R : HodgeFormalRealization G M)
    (H : HodgeMaterialMincut G M) :
    ConcreteAlgebraicityPayload M :=
  infrastructure_plus_material_closes
    R.toInfrastructureComplete H

#print axioms P05.Hodge.HodgeFormalRealization.toInfrastructureComplete
#print axioms P05.Hodge.typedScaffoldCount_eq_seven
#print axioms P05.Hodge.formalRealization_plus_material_closes

end P05.Hodge
