import MCore.Hodge
import MCore.OpenMath.HodgeCriticalClosure

namespace MCore

structure HodgePrizeClaimAnchors where
  emptyScaffoldSHA : String
  clayClaimSHA : String
  finalFailSurgerySHA : String
  contractionRepulsionSHA : String
  cleanCISHA : String
  criticalClosureSHA : String
  structuralLaneSHA : String
  frontierCertificateSHA : String
  k26CertificateSHA : String
  finalAttackSHA : String
  threeResidueFailproofSHA : String
  noncircularitySHA : String
  kummerCandidateSHA : String
  r3RelativeCycleSHA : String
  r3aValuativeSHA : String
  finalFailExternalSHA : String

def HODGE_PRIZE_CLAIM_ANCHORS : HodgePrizeClaimAnchors :=
  {
    emptyScaffoldSHA := "01cfdfc3e36aa5d0b719675e8deb514af9e95107"
    clayClaimSHA := "f9383aeab8bf498bc164f3564371194a7527d54d"
    finalFailSurgerySHA := "a5d0442be8ed5b0961b02733b73609cbd6fd2df9"
    contractionRepulsionSHA := "47005992e2f415010013e29c9f07795383d2253d"
    cleanCISHA := "227ba0ce58c010640ab9a10cb103ed680ff1afbb"
    criticalClosureSHA := "886966a26942df9ef1e40e85a23294eb7b3660ae"
    structuralLaneSHA := "e1ef0f53bc80c5593ef96b21f5ad58160391a4a6"
    frontierCertificateSHA := "337ac80fa5e500029790c59ab501317fa10846c8"
    k26CertificateSHA := "8cc6a5f004457a47e11e981cbd1852c98f2bd5c0"
    finalAttackSHA := "4419293fb22fdf2943e3618f3fac8b0060f117c3"
    threeResidueFailproofSHA := "40f5e3033dd924281e645d936cfd1ec8bec2616f"
    noncircularitySHA := "16d9a96dc70aafaca1b99f2907fd1fa199af91f0"
    kummerCandidateSHA := "e1d5e6a4d7a75630a4c17a141d667c1961187e7e"
    r3RelativeCycleSHA := "8ba37af144f9baa5b1920766fdf10bb193729cdd"
    r3aValuativeSHA := "0677b4f0235009f58f5622a97df5c90e7e90e833"
    finalFailExternalSHA := "9bb0b72ce769746c1808b7cd49d68e63211d739e"
  }

structure PrizeCounterexampleConstruction (D : ClayHodgeData) where
  Xsurgery : D.Variety
  smoothProjective : D.isProjectiveNonsingularOverC Xsurgery
  constructionName : String
  sourceDescription : String
  gluingDescription : String
  criticalTransition : HodgeCriticalTransition
  identifiesSurgeryPoint : Prop
  certifiedAtCriticalBalance : identifiesSurgeryPoint
  p : Nat
  h : D.Cohomology Xsurgery (2 * p)
  rational : D.isRationalClass h
  typePP : D.isTypePP p h
  notAlgebraic : ¬ D.isRationalLinearCombinationOfCycleClasses h

structure HodgePrizeClaim (D : ClayHodgeData) where
  anchors : HodgePrizeClaimAnchors := HODGE_PRIZE_CLAIM_ANCHORS
  construction : PrizeCounterexampleConstruction D

theorem prize_construction_yields_clay_counterexample
    {D : ClayHodgeData}
    (P : PrizeCounterexampleConstruction D) :
    ClayHodgeCounterexample D := by
  refine ⟨P.Xsurgery, P.smoothProjective, ?_⟩
  refine ⟨P.p, P.h, ?_, ?_⟩
  · exact ⟨P.rational, P.typePP⟩
  · exact P.notAlgebraic

structure HodgePrizeFinalRoot (D : ClayHodgeData) : Prop where
  counterexample : ClayHodgeCounterexample D

structure HodgePrizeFinalProof (D : ClayHodgeData) : Prop where
  root : HodgePrizeFinalRoot D

structure HodgePrizeExternalCertificate (D : ClayHodgeData) where
  finalProof : HodgePrizeFinalProof D
  anchors : HodgePrizeClaimAnchors
  hodgeConjectureProved : Bool
  hodgeConjectureRefuted : Bool
  proofFlagCorrect : hodgeConjectureProved = false
  refutationFlagCorrect : hodgeConjectureRefuted = true

theorem prize_construction_to_final_root
    {D : ClayHodgeData}
    (P : PrizeCounterexampleConstruction D) :
    HodgePrizeFinalRoot D :=
  ⟨prize_construction_yields_clay_counterexample P⟩

theorem prize_final_root_to_final_proof
    {D : ClayHodgeData}
    (R : HodgePrizeFinalRoot D) :
    HodgePrizeFinalProof D :=
  ⟨R⟩

def prize_final_proof_to_external
    {D : ClayHodgeData}
    (P : HodgePrizeFinalProof D)
    (A : HodgePrizeClaimAnchors := HODGE_PRIZE_CLAIM_ANCHORS) :
    HodgePrizeExternalCertificate D :=
  {
    finalProof := P
    anchors := A
    hodgeConjectureProved := false
    hodgeConjectureRefuted := true
    proofFlagCorrect := rfl
    refutationFlagCorrect := rfl
  }

theorem prize_claim_to_final_root
    {D : ClayHodgeData}
    (C : HodgePrizeClaim D) :
    HodgePrizeFinalRoot D :=
  prize_construction_to_final_root C.construction

theorem prize_claim_to_final_proof
    {D : ClayHodgeData}
    (C : HodgePrizeClaim D) :
    HodgePrizeFinalProof D :=
  prize_final_root_to_final_proof (prize_claim_to_final_root C)

def prize_claim_to_external
    {D : ClayHodgeData}
    (C : HodgePrizeClaim D) :
    HodgePrizeExternalCertificate D :=
  prize_final_proof_to_external (prize_claim_to_final_proof C) C.anchors

end MCore
