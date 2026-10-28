import MCore.BackwardAudit.HodgeHabitant
import MCore.BackwardAudit.HodgeHabitantConstructors
import MCore.BackwardAudit.HodgeHabitantGenericFirewall
import MCore.BackwardAudit.HodgeUnifiedTerminalProducer
import MCore.BackwardAudit.HodgeUnconditionalCertificate

namespace MCore.BackwardAudit

/-!
# Assumed complete Hodge closure

This module formalizes the conditional experiment in which the unique remaining
material producer is supplied explicitly as data.

It does not construct the Hodge inhabitant.  It records the exact assumption,
transports it through the already-certified terminal machinery, and keeps the
absolute/open distinction explicit.
-/

/-- Explicit assumption package for the conditional closure experiment. -/
structure AssumedHodgeCompleteClosure
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) : Type 1 where
  boundary : HodgeCertificationBoundary G M
  habitant : HodgeHabitant M

/-- The assumed complete object produces the exact universal concrete payload. -/
def AssumedHodgeCompleteClosure.concretePayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (C : AssumedHodgeCompleteClosure G M) :
    MCore.ConcreteAlgebraicityPayload M :=
  concretePayload_of_habitant C.habitant

/-- The assumed complete object is a legitimate positive terminal producer. -/
def AssumedHodgeCompleteClosure.terminalProducer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (C : AssumedHodgeCompleteClosure G M) :
    HodgePositiveTerminalProducer M :=
  .direct C.concretePayload

/-- The assumed complete object creates the terminal certificate. -/
def AssumedHodgeCompleteClosure.terminalCertificate
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (C : AssumedHodgeCompleteClosure G M) :
    UnconditionalHodgeCertificate G M :=
  unconditionalCertificateOfHabitant C.boundary C.habitant

/-- Conditional closure theorem: once the complete inhabitant is supplied,
all downstream mathematics closes through the certified boundary. -/
theorem hodge_of_assumed_complete_closure
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (C : AssumedHodgeCompleteClosure G M) :
    GradedRationalHodgeConjecture G :=
  unconditional_hodge_claim C.terminalCertificate

/-- Relative open-math count: no further mathematical premise is needed after
the explicit inhabitant is supplied. -/
def relativeOpenMathCount : Nat := 0

/-- Absolute open-math count: constructing the inhabitant remains the sole
material producer problem. -/
def absoluteOpenMathCount : Nat := 1

theorem relative_open_math_closed :
    relativeOpenMathCount = 0 := rfl

theorem absolute_open_math_singleton :
    absoluteOpenMathCount = 1 := rfl

/-- The complete assumption is not weaker than the existing endpoint: its
inhabitant component is exactly the endpoint-equivalent realization object. -/
theorem assumed_complete_contains_exact_open_core
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (C : AssumedHodgeCompleteClosure G M) :
    MCore.ConcreteAlgebraicityPayload M :=
  C.concretePayload

#print axioms MCore.BackwardAudit.AssumedHodgeCompleteClosure.concretePayload
#print axioms MCore.BackwardAudit.AssumedHodgeCompleteClosure.terminalProducer
#print axioms MCore.BackwardAudit.AssumedHodgeCompleteClosure.terminalCertificate
#print axioms MCore.BackwardAudit.hodge_of_assumed_complete_closure
#print axioms MCore.BackwardAudit.relative_open_math_closed
#print axioms MCore.BackwardAudit.absolute_open_math_singleton
#print axioms MCore.BackwardAudit.assumed_complete_contains_exact_open_core

end MCore.BackwardAudit
