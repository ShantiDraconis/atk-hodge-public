import MCore.OpenMath.HodgeStructuralFinalCertificate
import MCore.OpenMath.HodgePrizeSurgeryLane2
import MCore.OpenMath.HodgePrizePayloadDecomposition

namespace MCore

/-- Common certified frontier at which proof and refutation lanes meet. -/
structure HodgeMiddleFrontier where
  transition : HodgeCriticalTransition
  minimalCut : HodgeStructuralMinimalCut

def canonicalHodgeMiddleFrontier : HodgeMiddleFrontier :=
  {
    transition := canonicalCriticalTransition
    minimalCut := critical_transition_reaches_minimal_cut canonicalCriticalTransition
  }

/-- Proof lane: a genuine kernel term proving the Clay Hodge statement. -/
structure HodgeProofLane (D : ClayHodgeData) : Prop where
  statement : ClayHodgeStatement D

/-- Refutation lane: the dense concrete counterexample construction. -/
structure HodgeRefutationLane (D : ClayHodgeData) where
  construction : PrizeCounterexampleConstruction D

theorem refutation_lane_counterexample
    {D : ClayHodgeData}
    (R : HodgeRefutationLane D) :
    ClayHodgeCounterexample D :=
  prize_construction_yields_clay_counterexample R.construction

theorem refutation_lane_excludes_proof
    {D : ClayHodgeData}
    (R : HodgeRefutationLane D) :
    ¬ ClayHodgeStatement D := by
  exact (clay_refutation_exact (D := D)).mpr
    (refutation_lane_counterexample R)

theorem proof_lane_excludes_refutation
    {D : ClayHodgeData}
    (P : HodgeProofLane D) :
    ¬ Nonempty (HodgeRefutationLane D) := by
  intro hR
  rcases hR with ⟨R⟩
  exact (refutation_lane_excludes_proof R) P.statement

/-- Terminal scientific outcome. It can only be inhabited by an actual
surviving mathematical lane; the opposite lane is then excluded by theorem. -/
inductive HodgeFinalFail (D : ClayHodgeData) where
  | proofSurvives (proof : HodgeProofLane D)
  | refutationSurvives (refutation : HodgeRefutationLane D)

/-- Minimal scientific payload. No metadata, no certificate fields. -/
inductive HodgeScientificPayload (D : ClayHodgeData) where
  | proof (statement : ClayHodgeStatement D)
  | refutation (construction : PrizeCounterexampleConstruction D)

def scientificPayloadToFinalFail
    {D : ClayHodgeData}
    (P : HodgeScientificPayload D) :
    HodgeFinalFail D :=
  match P with
  | .proof h => .proofSurvives ⟨h⟩
  | .refutation h => .refutationSurvives ⟨h⟩

def finalFailToScientificPayload
    {D : ClayHodgeData}
    (F : HodgeFinalFail D) :
    HodgeScientificPayload D :=
  match F with
  | .proofSurvives P => .proof P.statement
  | .refutationSurvives R => .refutation R.construction

inductive HodgeScientificOutcome where
  | proved
  | refuted
  deriving Repr, DecidableEq

/-- Fail-closed terminal payload: unlike mere Nonempty HodgeScientificPayload,
this records which side is claimed and carries that side's actual witness. -/
inductive HodgeTerminalScientificPayload (D : ClayHodgeData) where
  | proved (statement : ClayHodgeStatement D)
  | refuted (construction : PrizeCounterexampleConstruction D)

def refutationPayloadsToTerminal
    {D : ClayHodgeData}
    (G : HodgePrizeGeometryPayload D)
    (C : HodgePrizeClassPayload D G)
    (S : HodgePrizeSeparationPayload D G C) :
    HodgeTerminalScientificPayload D :=
  .refuted (assemblePrizeCounterexample G C S)

def terminalPayloadToFinalFail
    {D : ClayHodgeData}
    (P : HodgeTerminalScientificPayload D) :
    HodgeFinalFail D :=
  match P with
  | .proved h => .proofSurvives ⟨h⟩
  | .refuted h => .refutationSurvives ⟨h⟩

def terminalPayloadOutcome
    {D : ClayHodgeData} :
    HodgeTerminalScientificPayload D → HodgeScientificOutcome
  | .proved _ => .proved
  | .refuted _ => .refuted

theorem terminal_payload_excludes_opposite
    {D : ClayHodgeData}
    (P : HodgeTerminalScientificPayload D) :
    match P with
    | .proved _ => ¬ Nonempty (HodgeRefutationLane D)
    | .refuted _ => ¬ HodgeProofLane D := by
  cases P with
  | proved h =>
      exact proof_lane_excludes_refutation ⟨h⟩
  | refuted h =>
      intro P
      exact (refutation_lane_excludes_proof ⟨h⟩) P.statement

theorem scientific_payload_final_fail_roundtrip
    {D : ClayHodgeData}
    (P : HodgeScientificPayload D) :
    finalFailToScientificPayload (scientificPayloadToFinalFail P) = P := by
  cases P <;> rfl

theorem final_fail_proof_excludes_refutation
    {D : ClayHodgeData}
    (P : HodgeProofLane D) :
    ¬ Nonempty (HodgeRefutationLane D) :=
  proof_lane_excludes_refutation P

theorem final_fail_refutation_excludes_proof
    {D : ClayHodgeData}
    (R : HodgeRefutationLane D) :
    ¬ HodgeProofLane D := by
  intro P
  exact (refutation_lane_excludes_proof R) P.statement

/-- Dense readiness target: both routes are wired to the same frontier,
but no scientific outcome is claimed until one lane is inhabited. -/
structure HodgeDualLaneReady where
  frontier : HodgeMiddleFrontier := canonicalHodgeMiddleFrontier
  proofLaneWired : Bool := true
  refutationLaneWired : Bool := true

def HODGE_DUAL_LANE_READY : HodgeDualLaneReady := {}

inductive HodgeFourWayState where
  | proofTrueRefutationFalse
  | proofFalseRefutationTrue
  | bothFalse
  | bothTrue
  deriving Repr, DecidableEq

def HodgeFourWayState.isOpenMath : HodgeFourWayState → Bool
  | .bothFalse => true
  | _ => false

def HodgeFourWayState.isTerminalScientific : HodgeFourWayState → Bool
  | .proofTrueRefutationFalse => true
  | .proofFalseRefutationTrue => true
  | .bothFalse => false
  | .bothTrue => false

theorem both_true_impossible
    {D : ClayHodgeData}
    (P : HodgeProofLane D)
    (R : HodgeRefutationLane D) : False := by
  exact (refutation_lane_excludes_proof R) P.statement

theorem both_false_is_open_math :
    HodgeFourWayState.bothFalse.isOpenMath = true := rfl

theorem proof_true_refutation_false_is_terminal :
    HodgeFourWayState.proofTrueRefutationFalse.isTerminalScientific = true := rfl

theorem proof_false_refutation_true_is_terminal :
    HodgeFourWayState.proofFalseRefutationTrue.isTerminalScientific = true := rfl


/-- Both lanes are closed around the same middle frontier:
one side is inhabited and the opposite side is formally noninhabited. -/
inductive HodgeClosedPair (D : ClayHodgeData) where
  | proofSide
      (proof : HodgeProofLane D)
      (refutationClosed : ¬ Nonempty (HodgeRefutationLane D))
  | refutationSide
      (refutation : HodgeRefutationLane D)
      (proofClosed : ¬ HodgeProofLane D)

def close_pair_from_final_fail
    {D : ClayHodgeData}
    (F : HodgeFinalFail D) :
    HodgeClosedPair D :=
  match F with
  | .proofSurvives P =>
      .proofSide P (proof_lane_excludes_refutation P)
  | .refutationSurvives R =>
      .refutationSide R (final_fail_refutation_excludes_proof R)

structure HodgeDualLaneFinalCertificate (D : ClayHodgeData) where
  frontier : HodgeMiddleFrontier
  closedPair : HodgeClosedPair D
  finalFail : HodgeFinalFail D

def dual_lane_final_certificate
    {D : ClayHodgeData}
    (F : HodgeFinalFail D) :
    HodgeDualLaneFinalCertificate D :=
  {
    frontier := canonicalHodgeMiddleFrontier
    closedPair := close_pair_from_final_fail F
    finalFail := F
  }

/-- Final scientific root exists exactly when a scientific lane survives. -/
abbrev HodgeDualLaneFinalRoot (D : ClayHodgeData) :=
  HodgeDualLaneFinalCertificate D

structure HodgeScientificFinalRoot (D : ClayHodgeData) where
  frontier : HodgeMiddleFrontier
  closedPair : HodgeClosedPair D
  outcome : HodgeScientificOutcome

def scientific_final_root
    {D : ClayHodgeData}
    (F : HodgeFinalFail D) :
    HodgeScientificFinalRoot D :=
  match F with
  | .proofSurvives P =>
      {
        frontier := canonicalHodgeMiddleFrontier
        closedPair := .proofSide P (proof_lane_excludes_refutation P)
        outcome := .proved
      }
  | .refutationSurvives R =>
      {
        frontier := canonicalHodgeMiddleFrontier
        closedPair := .refutationSide R (final_fail_refutation_excludes_proof R)
        outcome := .refuted
      }

structure HodgeScientificFinalProof (D : ClayHodgeData) where
  root : HodgeScientificFinalRoot D
  finalFail : HodgeFinalFail D

def scientific_final_proof
    {D : ClayHodgeData}
    (F : HodgeFinalFail D) :
    HodgeScientificFinalProof D :=
  {
    root := scientific_final_root F
    finalFail := F
  }

structure HodgeScientificExternalCertificate (D : ClayHodgeData) where
  finalProof : HodgeScientificFinalProof D
  anchors : HodgePrizeClaimAnchors
  outcome : HodgeScientificOutcome
  proofLaneClosed : Bool
  refutationLaneClosed : Bool
  bothTrueRejected : Bool
  bothFalseRejected : Bool

def scientific_external_certificate
    {D : ClayHodgeData}
    (F : HodgeFinalFail D)
    (A : HodgePrizeClaimAnchors := HODGE_PRIZE_CLAIM_ANCHORS) :
    HodgeScientificExternalCertificate D :=
  match F with
  | .proofSurvives P =>
      {
        finalProof := scientific_final_proof (.proofSurvives P)
        anchors := A
        outcome := .proved
        proofLaneClosed := true
        refutationLaneClosed := true
        bothTrueRejected := true
        bothFalseRejected := true
      }
  | .refutationSurvives R =>
      {
        finalProof := scientific_final_proof (.refutationSurvives R)
        anchors := A
        outcome := .refuted
        proofLaneClosed := true
        refutationLaneClosed := true
        bothTrueRejected := true
        bothFalseRejected := true
      }

theorem scientific_final_proof_reaches_root
    {D : ClayHodgeData}
    (F : HodgeFinalFail D) :
    (scientific_final_proof F).root = scientific_final_root F := rfl

theorem scientific_external_rejects_both_false
    {D : ClayHodgeData}
    (F : HodgeFinalFail D) :
    (scientific_external_certificate F).bothFalseRejected = true := by
  cases F <;> rfl

end MCore
