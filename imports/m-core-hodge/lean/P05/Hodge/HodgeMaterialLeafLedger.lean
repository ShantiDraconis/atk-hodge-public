import P05.Hodge.HodgeMaterialMincut

namespace P05.Hodge

open MCore

inductive MaterialLeafState
  | openMath
  | produced
  deriving DecidableEq, Repr

structure HodgeMaterialLeafLedger where
  codimZero : MaterialLeafState
  codimOne : MaterialLeafState
  higherSpread : MaterialLeafState
  higherQbar : MaterialLeafState
  higherFiber : MaterialLeafState
  higherTransport : MaterialLeafState
  deriving Repr

/--
Fail-closed current material ledger.
This record is status metadata only; it does not assert nonexistence in
mathematics.  It records that the repository currently has no checked
inhabitant wired for any of the six constructive producer fields.
-/
def currentMaterialLeafLedger : HodgeMaterialLeafLedger :=
  {
    codimZero := .openMath
    codimOne := .openMath
    higherSpread := .openMath
    higherQbar := .openMath
    higherFiber := .openMath
    higherTransport := .openMath
  }

def producedLeafCount : Nat :=
  [ currentMaterialLeafLedger.codimZero
  , currentMaterialLeafLedger.codimOne
  , currentMaterialLeafLedger.higherSpread
  , currentMaterialLeafLedger.higherQbar
  , currentMaterialLeafLedger.higherFiber
  , currentMaterialLeafLedger.higherTransport
  ].foldl (fun n s => if s = .produced then n + 1 else n) 0

def openLeafCount : Nat :=
  [ currentMaterialLeafLedger.codimZero
  , currentMaterialLeafLedger.codimOne
  , currentMaterialLeafLedger.higherSpread
  , currentMaterialLeafLedger.higherQbar
  , currentMaterialLeafLedger.higherFiber
  , currentMaterialLeafLedger.higherTransport
  ].foldl (fun n s => if s = .openMath then n + 1 else n) 0

theorem producedLeafCount_eq_zero : producedLeafCount = 0 := by
  decide

theorem openLeafCount_eq_six : openLeafCount = 6 := by
  decide

/-- Promotion rule: a material payload requires an actual six-field mincut term. -/
theorem six_fields_required_for_current_route
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : HodgeMaterialMincut G M) :
    ConcreteAlgebraicityPayload M :=
  material_mincut_closes_payload H

#print axioms P05.Hodge.producedLeafCount_eq_zero
#print axioms P05.Hodge.openLeafCount_eq_six
#print axioms P05.Hodge.six_fields_required_for_current_route

end P05.Hodge
