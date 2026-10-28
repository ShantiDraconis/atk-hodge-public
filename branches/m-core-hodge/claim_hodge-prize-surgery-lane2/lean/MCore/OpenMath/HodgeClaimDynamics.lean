import MCore.Hodge
import MCore.HodgeReduction
import MCore.OpenMath.HodgeFinalCertificateChain

namespace MCore

inductive HodgeClaimPole where
  | truth
  | falsehood
  deriving DecidableEq, Repr

structure HodgeClaimTension where
  towardTruth : Prop
  towardFalsehood : Prop

def TruthContraction (D : ClayHodgeData) : Prop :=
  ClayHodgeStatement D

def FalsehoodContraction (D : ClayHodgeData) : Prop :=
  ClayHodgeCounterexample D

theorem truth_falsehood_repulsion {D : ClayHodgeData}
    (ht : TruthContraction D)
    (hf : FalsehoodContraction D) : False := by
  exact (clay_refutation_exact (D := D)).mpr hf ht

structure HodgeContractionRepulsionState (D : ClayHodgeData) where
  truthPressure : Prop
  falsehoodPressure : Prop
  truthClosed : Bool := false
  falsehoodClosed : Bool := false

theorem falsehood_closure_to_open_math {D : ClayHodgeData}
    (h : FalsehoodContraction D) :
    HODGE_RESOLUTION_OPEN_MATH D :=
  ⟨h⟩

theorem falsehood_closure_to_final_root {D : ClayHodgeData}
    (h : FalsehoodContraction D) :
    HodgeFinalRoot D :=
  clay_refutation_to_final_root (falsehood_closure_to_open_math h)

def ACTIVE_HODGE_POLE : HodgeClaimPole := .falsehood

end MCore
