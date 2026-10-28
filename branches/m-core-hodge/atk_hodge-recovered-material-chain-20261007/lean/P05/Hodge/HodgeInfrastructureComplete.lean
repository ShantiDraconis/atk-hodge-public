import P05.Hodge.MathlibCycleClassBridge
import P05.Hodge.HodgeMaterialLeafLedger
import MCore.BackwardAudit.CodimOneAdapterFirewall
import MCore.BackwardAudit.R1dQbarPointBoundary
import MCore.BackwardAudit.R2FiberAlgebraicityBoundary
import MCore.BackwardAudit.R3AtomicSpecialization
import MCore.BackwardAudit.R3aHilbertProperness

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/-!
# Hodge infrastructure completion package

This file aggregates the already-typed infrastructure surrounding the six
material leaves.  It intentionally does not inhabit the open mathematical
producers.  Its purpose is to prove that the remaining frontier is mathematical,
not scaffolding.
-/

inductive InfraStatus
  | closedInternal
  | openFormalizationAdapter
  | openExternalMathematics
  deriving DecidableEq, Repr

structure HodgeInfrastructureLedger where
  endpointQuantifierTyping : InfraStatus
  finiteCycleCombination : InfraStatus
  materialSplit : InfraStatus
  mathlibCycleCarrier : InfraStatus
  cycleRealizationBridge : InfraStatus
  codimOneAdapterFirewall : InfraStatus
  spreadDependentTyping : InfraStatus
  qbarPointBoundary : InfraStatus
  r2ExactBoundary : InfraStatus
  r3FiniteCombinationLift : InfraStatus
  hilbertChowReachabilityLogic : InfraStatus
  deriving Repr

def hodgeInfrastructureLedger : HodgeInfrastructureLedger :=
  {
    endpointQuantifierTyping := .closedInternal
    finiteCycleCombination := .closedInternal
    materialSplit := .closedInternal
    mathlibCycleCarrier := .openFormalizationAdapter
    cycleRealizationBridge := .openFormalizationAdapter
    codimOneAdapterFirewall := .closedInternal
    spreadDependentTyping := .closedInternal
    qbarPointBoundary := .closedInternal
    r2ExactBoundary := .closedInternal
    r3FiniteCombinationLift := .closedInternal
    hilbertChowReachabilityLogic := .closedInternal
  }

def closedInfrastructureCount : Nat :=
  [ hodgeInfrastructureLedger.endpointQuantifierTyping
  , hodgeInfrastructureLedger.finiteCycleCombination
  , hodgeInfrastructureLedger.materialSplit
  , hodgeInfrastructureLedger.mathlibCycleCarrier
  , hodgeInfrastructureLedger.cycleRealizationBridge
  , hodgeInfrastructureLedger.codimOneAdapterFirewall
  , hodgeInfrastructureLedger.spreadDependentTyping
  , hodgeInfrastructureLedger.qbarPointBoundary
  , hodgeInfrastructureLedger.r2ExactBoundary
  , hodgeInfrastructureLedger.r3FiniteCombinationLift
  , hodgeInfrastructureLedger.hilbertChowReachabilityLogic
  ].foldl (fun n s => if s = .closedInternal then n + 1 else n) 0

def openFormalAdapterCount : Nat :=
  [ hodgeInfrastructureLedger.endpointQuantifierTyping
  , hodgeInfrastructureLedger.finiteCycleCombination
  , hodgeInfrastructureLedger.materialSplit
  , hodgeInfrastructureLedger.mathlibCycleCarrier
  , hodgeInfrastructureLedger.cycleRealizationBridge
  , hodgeInfrastructureLedger.codimOneAdapterFirewall
  , hodgeInfrastructureLedger.spreadDependentTyping
  , hodgeInfrastructureLedger.qbarPointBoundary
  , hodgeInfrastructureLedger.r2ExactBoundary
  , hodgeInfrastructureLedger.r3FiniteCombinationLift
  , hodgeInfrastructureLedger.hilbertChowReachabilityLogic
  ].foldl (fun n s => if s = .openFormalizationAdapter then n + 1 else n) 0

theorem closedInfrastructureCount_eq_nine :
    closedInfrastructureCount = 9 := by decide

theorem openFormalAdapterCount_eq_two :
    openFormalAdapterCount = 2 := by decide

/-- Once the concrete cycle realization adapter exists, infrastructure no longer
blocks the six material producers.  The actual Hodge payload still requires a
term of HodgeMaterialMincut. -/
structure HodgeInfrastructureComplete
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  mathlibCycleBridge : MathlibCycleClassBridge G M

theorem infrastructure_plus_material_closes
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (_I : HodgeInfrastructureComplete G M)
    (H : HodgeMaterialMincut G M) :
    ConcreteAlgebraicityPayload M :=
  material_mincut_closes_payload H

/-- The complete infrastructure package still does not manufacture any of the
six mathematical producer fields. -/
def remainingMaterialLeafCount : Nat := 6

theorem remainingMaterialLeafCount_eq_six :
    remainingMaterialLeafCount = 6 := rfl

#print axioms P05.Hodge.closedInfrastructureCount_eq_nine
#print axioms P05.Hodge.openFormalAdapterCount_eq_two
#print axioms P05.Hodge.infrastructure_plus_material_closes
#print axioms P05.Hodge.remainingMaterialLeafCount_eq_six

end P05.Hodge
