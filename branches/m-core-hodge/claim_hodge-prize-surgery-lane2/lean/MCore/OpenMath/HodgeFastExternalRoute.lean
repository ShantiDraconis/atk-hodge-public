import MCore.OpenMath.HodgePrizePayloadDecomposition
import MCore.OpenMath.HodgeDualLaneFinalFail

namespace MCore

/-- Fast fail-closed terminal bundle. This structure does not create any
mathematics: every scientific inhabitant remains an explicit field. It only
removes repetitive assembly steps once the concrete p>1 payload exists. -/
structure HodgeConcreteRefutationBundle (D : ClayHodgeData) where
  G : HodgePrizeGeometryCore D
  C : HodgePrizeClassCore D G
  p_gt_one : 1 < C.p
  O : HodgeRationalCohomologyOperations D G C
  complete : HodgeFiniteSpanCompleteness O
  separator : HodgeFiniteWitnessSeparator O

def concreteBundleSeparationCore
    {D : ClayHodgeData}
    (B : HodgeConcreteRefutationBundle D) :
    HodgePrizeSeparationCore D B.G B.C :=
  {
    notAlgebraic :=
      finiteWitnessSeparator_proves_notAlgebraic
        B.O B.complete B.separator
  }

def concreteBundlePrizeConstruction
    {D : ClayHodgeData}
    (B : HodgeConcreteRefutationBundle D) :
    PrizeCounterexampleConstruction D :=
  assemblePrizeCounterexample
    (geometryPayloadFromCore B.G)
    (classPayloadFromCore B.G B.C)
    (separationPayloadFromCore B.G B.C
      (concreteBundleSeparationCore B))

def concreteBundleTerminal
    {D : ClayHodgeData}
    (B : HodgeConcreteRefutationBundle D) :
    HodgeTerminalScientificPayload D :=
  .refuted (concreteBundlePrizeConstruction B)

def concreteBundleFinalFail
    {D : ClayHodgeData}
    (B : HodgeConcreteRefutationBundle D) :
    HodgeFinalFail D :=
  terminalPayloadToFinalFail (concreteBundleTerminal B)

def concreteBundleScientificExternal
    {D : ClayHodgeData}
    (B : HodgeConcreteRefutationBundle D) :
    HodgeScientificExternalCertificate D :=
  scientific_external_certificate (concreteBundleFinalFail B)

theorem concreteBundleExternalOutcomeRefuted
    {D : ClayHodgeData}
    (B : HodgeConcreteRefutationBundle D) :
    (concreteBundleScientificExternal B).outcome = .refuted := rfl

theorem concreteBundleExternalRejectsBothFalse
    {D : ClayHodgeData}
    (B : HodgeConcreteRefutationBundle D) :
    (concreteBundleScientificExternal B).bothFalseRejected = true := rfl


/-- Single inhabited object required by the canonical ATK fast path.
It packages the faithful Clay model together with the already-audited concrete
refutation bundle; it introduces no new mathematical assumption. -/
structure HodgeConcreteExternalInput where
  D : ClayHodgeData
  bundle : HodgeConcreteRefutationBundle D

def concreteInputPrizeConstruction
    (I : HodgeConcreteExternalInput) :
    PrizeCounterexampleConstruction I.D :=
  concreteBundlePrizeConstruction I.bundle

def concreteInputScientificExternal
    (I : HodgeConcreteExternalInput) :
    HodgeScientificExternalCertificate I.D :=
  concreteBundleScientificExternal I.bundle

theorem concreteInputExternalOutcomeRefuted
    (I : HodgeConcreteExternalInput) :
    (concreteInputScientificExternal I).outcome = .refuted := rfl

end MCore
