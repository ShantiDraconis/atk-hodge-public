import MCore.K26
import MCore.BackwardAudit.R2HardCore

namespace MCore.BackwardAudit

/-!
# H01 direct-core compression

The previously explored variational route R1d -> R2 -> R3 is sufficient, but
R2HardCore already proves that on the constant-Qbar regression family, R2 is
exactly the original concrete algebraicity endpoint.

Therefore R1d and R3 are not logically mandatory gates for the terminal Hodge
frontier.  The exact irreducible producer is ConcreteAlgebraicityPayload.
This is a compression theorem, not a proof of that payload.
-/

abbrev H01DirectResearchCore
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ConcreteAlgebraicityPayload M

theorem direct_core_iff_constant_qbar_r2
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    H01DirectResearchCore M ↔ TrivialQbarR2Payload M :=
  (trivial_qbar_r2_payload_iff_concrete_payload M).symm

theorem direct_core_iff_hodge
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M) :
    H01DirectResearchCore M ↔ GradedRationalHodgeConjecture G :=
  (k26_minimal_cut B).symm

inductive DirectCoreGateStatus where
  | optionalRoute
  | terminalOpenResearch
  deriving Repr, DecidableEq

structure DirectCoreFrontier where
  r1dQbarDescent : DirectCoreGateStatus
  r2FiberAlgebraicity : DirectCoreGateStatus
  r3VariationalAlgebraicity : DirectCoreGateStatus
  directAlgebraicityCore : DirectCoreGateStatus

def directCoreFrontier : DirectCoreFrontier :=
  {
    r1dQbarDescent := .optionalRoute
    r2FiberAlgebraicity := .optionalRoute
    r3VariationalAlgebraicity := .optionalRoute
    directAlgebraicityCore := .terminalOpenResearch
  }

theorem direct_core_is_single_terminal_gate :
    directCoreFrontier.directAlgebraicityCore = .terminalOpenResearch := rfl

theorem r1d_no_longer_mandatory_gate :
    directCoreFrontier.r1dQbarDescent = .optionalRoute := rfl

theorem r3_no_longer_mandatory_gate :
    directCoreFrontier.r3VariationalAlgebraicity = .optionalRoute := rfl

#print axioms MCore.BackwardAudit.direct_core_iff_constant_qbar_r2
#print axioms MCore.BackwardAudit.direct_core_iff_hodge
#print axioms MCore.BackwardAudit.direct_core_is_single_terminal_gate
#print axioms MCore.BackwardAudit.r1d_no_longer_mandatory_gate
#print axioms MCore.BackwardAudit.r3_no_longer_mandatory_gate

end MCore.BackwardAudit
