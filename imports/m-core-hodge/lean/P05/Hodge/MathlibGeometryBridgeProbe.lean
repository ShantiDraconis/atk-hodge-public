import Mathlib.AlgebraicGeometry.Scheme
import MCore.HodgeGeometricBackends

namespace P05.Hodge

open MCore
open AlgebraicGeometry

/-!
# Mathlib geometry bridge probe

The pinned Mathlib v4.19.0 exposes schemes but not the later
`AlgebraicGeometry.AlgebraicCycle` carrier.  We therefore record that exact
backend boundary explicitly instead of manufacturing a cycle carrier.
-/

inductive MathlibHodgeBridgeStatus
  | schemeCarrierAvailable
  | algebraicCycleCarrierOpen
  | cycleClassMapOpen
  | rationalCohomologyAdapterOpen
  | lefschetz11BridgeOpen
  deriving DecidableEq, Repr

def mathlibHodgeBridgeStatus : List MathlibHodgeBridgeStatus :=
  [ .schemeCarrierAvailable
  , .algebraicCycleCarrierOpen
  , .cycleClassMapOpen
  , .rationalCohomologyAdapterOpen
  , .lefschetz11BridgeOpen ]

theorem mathlib_scheme_carrier_available :
    mathlibHodgeBridgeStatus.head? =
      some .schemeCarrierAvailable := by
  rfl

def mathlibAlgebraicCycleBackendOpen : Prop := True

theorem mathlib_algebraic_cycle_backend_open :
    mathlibAlgebraicCycleBackendOpen := by
  trivial

#print axioms P05.Hodge.mathlib_scheme_carrier_available
#print axioms P05.Hodge.mathlib_algebraic_cycle_backend_open

end P05.Hodge
