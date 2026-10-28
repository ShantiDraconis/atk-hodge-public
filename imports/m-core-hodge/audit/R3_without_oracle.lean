import MCore.BackwardAudit.R3Contract

namespace MCore.BackwardAuditR3Repro

open MCore
open MCore.BackwardAudit

#check R3ConcreteTarget
#check R3TransportContract
#check r3_contract_yields_concrete_span
#check r3_contract_yields_span

example : r3CandidateQuantifierMatch = true :=
  r3_quantifier_match

example : r3TransportClosed = false :=
  r3_transport_still_open

#print axioms MCore.BackwardAudit.r3_contract_yields_concrete_span
#print axioms MCore.BackwardAudit.r3_contract_yields_span
#print axioms MCore.BackwardAudit.r3_quantifier_match
#print axioms MCore.BackwardAudit.r3_transport_still_open

end MCore.BackwardAuditR3Repro
