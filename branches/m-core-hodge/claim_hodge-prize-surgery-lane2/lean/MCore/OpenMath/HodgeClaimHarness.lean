import MCore.OpenMath.HodgeDualLaneFinalFail

namespace MCore

/-- Claim-test result over the common scientific frontier. -/
inductive HodgeClaimTestState where
  | proofOnly
  | refutationOnly
  | neither
  | contradiction
  deriving Repr, DecidableEq

def classifyClaimTest
    (proofInhabited refutationInhabited : Bool) : HodgeClaimTestState :=
  match proofInhabited, refutationInhabited with
  | true, false => .proofOnly
  | false, true => .refutationOnly
  | false, false => .neither
  | true, true => .contradiction

theorem classify_neither :
    classifyClaimTest false false = .neither := rfl

theorem classify_proof_only :
    classifyClaimTest true false = .proofOnly := rfl

theorem classify_refutation_only :
    classifyClaimTest false true = .refutationOnly := rfl

theorem classify_contradiction :
    classifyClaimTest true true = .contradiction := rfl

/-- A simultaneous mathematical inhabitant is impossible for the same D. -/
theorem claim_test_no_simultaneous_survivors
    {D : ClayHodgeData}
    (P : HodgeProofLane D)
    (R : HodgeRefutationLane D) : False :=
  both_true_impossible P R

/-- Either scientific survivor is sufficient to build FINAL_FAIL. -/
def finalFailFromProof
    {D : ClayHodgeData}
    (P : HodgeProofLane D) : HodgeFinalFail D :=
  .proofSurvives P

def finalFailFromRefutation
    {D : ClayHodgeData}
    (R : HodgeRefutationLane D) : HodgeFinalFail D :=
  .refutationSurvives R

end MCore
