# m-core-hodge — branch `atk/auto-compose-terminal-20260930`

Lean sources from the branch `atk/auto-compose-terminal-20260930` of the private repository `ShantiDraconis/m-core-hodge`, commit `5e6a20f4b0c5d08a93446274ec61b10ad1812f8b` (2026-10-01T01:45:53+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 67 — closed 63, conditional 0, open 1, proof error 3, not reached 0, no result 0.
* History: 98 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `56a80e5c47e28fc1930883a957fe0b3a1328fc995ddea6dfdc914a77b48a4146`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-hodge/atk_auto-compose-terminal-20260930/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.AutoCompose.extract` | `lean/MCore/AutoCompose.lean`:24 | fechado |
| `MCore.BackwardAudit.Final.FINAL_ROOT_of_minimal_concrete_inputs` | `lean/MCore/BackwardAudit/ExactFinalProducer.lean`:60 | fechado |
| `MCore.BackwardAudit.Final.codimOnePayload_of_concrete_lefschetz` | `lean/MCore/BackwardAudit/ExactFinalProducer.lean`:7 | fechado |
| `MCore.BackwardAudit.Final.finalExternal_to_FINAL_ROOT` | `lean/MCore/BackwardAudit/FinalExternal.lean`:14 | fechado |
| `MCore.BackwardAudit.Final.higherCodimConcrete_of_h01` | `lean/MCore/BackwardAudit/ExactFinalProducer.lean`:16 | fechado |
| `MCore.BackwardAudit.HodgePositiveTerminalProducer.createTheorem` | `lean/MCore/BackwardAudit/HodgeUnifiedTerminalProducer.lean`:120 | fechado |
| `MCore.BackwardAudit.absolute_open_math_singleton` | `lean/MCore/BackwardAudit/HodgeAssumedCompleteClosure.lean`:70 | fechado |
| `MCore.BackwardAudit.any_positive_producer_closes` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:145 | fechado |
| `MCore.BackwardAudit.assumed_complete_contains_exact_open_core` | `lean/MCore/BackwardAudit/HodgeAssumedCompleteClosure.lean`:73 | fechado |
| `MCore.BackwardAudit.both_is_invalid` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:220 | fechado |
| `MCore.BackwardAudit.boundary_does_not_force_unconditional_certificate` | `lean/MCore/BackwardAudit/HodgeUnconditionalNoShortcut.lean`:100 | aberto-sorry |
| `MCore.BackwardAudit.certified_h01_forward_is_sufficient` | `lean/MCore/BackwardAudit/HodgeCertifiedReuseBridge.lean`:53 | fechado |
| `MCore.BackwardAudit.concretePayload_iff_codimOne_and_residual` | `lean/MCore/BackwardAudit/HodgeResidualCodimSplit.lean`:44 | fechado |
| `MCore.BackwardAudit.concretePayload_iff_residual_given_codimOne` | `lean/MCore/BackwardAudit/HodgeResidualCodimSplit.lean`:57 | fechado |
| `MCore.BackwardAudit.concretePayload_iff_trisection` | `lean/MCore/BackwardAudit/HodgeCodimTrisection.lean`:67 | fechado |
| `MCore.BackwardAudit.concretePayload_implies_codimZero` | `lean/MCore/BackwardAudit/HodgeCodimTrisection.lean`:32 | fechado |
| `MCore.BackwardAudit.concretePayload_implies_higherCodim` | `lean/MCore/BackwardAudit/HodgeCodimTrisection.lean`:40 | fechado |
| `MCore.BackwardAudit.concretePayload_implies_nonCodimOne` | `lean/MCore/BackwardAudit/HodgeResidualCodimSplit.lean`:24 | fechado |
| `MCore.BackwardAudit.concretePayload_of_codimOne_and_residual` | `lean/MCore/BackwardAudit/HodgeResidualCodimSplit.lean`:32 | fechado |
| `MCore.BackwardAudit.concretePayload_of_habitant` | `lean/MCore/BackwardAudit/HodgeHabitant.lean`:30 | fechado |
| `MCore.BackwardAudit.concretePayload_of_trisection` | `lean/MCore/BackwardAudit/HodgeCodimTrisection.lean`:48 | fechado |
| `MCore.BackwardAudit.createHodgeRefutation` | `lean/MCore/BackwardAudit/HodgeUnifiedTerminalProducer.lean`:129 | fechado |
| `MCore.BackwardAudit.current_open_math_is_50` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:304 | fechado |
| `MCore.BackwardAudit.direct_core_iff_constant_qbar_r2` | `lean/MCore/BackwardAudit/H01DirectCoreCompression.lean`:22 | fechado |
| `MCore.BackwardAudit.direct_core_iff_hodge` | `lean/MCore/BackwardAudit/H01DirectCoreCompression.lean`:28 | fechado |
| `MCore.BackwardAudit.direct_core_is_single_terminal_gate` | `lean/MCore/BackwardAudit/H01DirectCoreCompression.lean`:54 | fechado |
| `MCore.BackwardAudit.false_closed_state_is_0` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:63 | fechado |
| `MCore.BackwardAudit.higherCodim_of_h01_forward` | `lean/MCore/BackwardAudit/HodgeCertifiedReuseBridge.lean`:25 | fechado |
| `MCore.BackwardAudit.higher_certificate_closes_concrete_payload` | `lean/MCore/BackwardAudit/HodgeHigherCodimUnconditionalClaim.lean`:19 | fechado |
| `MCore.BackwardAudit.higher_certificate_enables_hodge` | `lean/MCore/BackwardAudit/HodgeHigherCodimUnconditionalClaim.lean`:30 | fechado |
| `MCore.BackwardAudit.higher_certificate_iff_payload` | `lean/MCore/BackwardAudit/HodgeHigherCodimUnconditionalClaim.lean`:58 | fechado |
| `MCore.BackwardAudit.hodgeCycleOfMinimalForwardPayload_verified` | `lean/MCore/BackwardAudit/HodgeProducerFirst.lean`:84 | fechado |
| `MCore.BackwardAudit.hodgeExactLocalProducer_verified` | `lean/MCore/BackwardAudit/HodgeProducerFirst.lean`:51 | fechado |
| `MCore.BackwardAudit.hodge_iff_higher_given_boundary_low_codim` | `lean/MCore/BackwardAudit/HodgeCodimTrisection.lean`:82 | fechado |
| `MCore.BackwardAudit.hodge_iff_residual_given_boundary_and_codimOne` | `lean/MCore/BackwardAudit/HodgeResidualCodimSplit.lean`:68 | fechado |
| `MCore.BackwardAudit.hodge_of_assumed_complete_closure` | `lean/MCore/BackwardAudit/HodgeAssumedCompleteClosure.lean`:50 | fechado |
| `MCore.BackwardAudit.hodge_of_certified_h01_reuse` | `lean/MCore/BackwardAudit/HodgeCertifiedReuseBridge.lean`:39 | fechado |
| `MCore.BackwardAudit.hodge_of_habitant` | `lean/MCore/BackwardAudit/HodgeHabitant.lean`:79 | fechado |
| `MCore.BackwardAudit.negative_certificate_refutes_core` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:87 | fechado |
| `MCore.BackwardAudit.negative_certificate_refutes_hodge` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:161 | fechado |
| `MCore.BackwardAudit.negative_only_is_closed_false` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:210 | fechado |
| `MCore.BackwardAudit.neither_is_not_closed` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:215 | fechado |
| `MCore.BackwardAudit.no_generic_hodgeHabitant` | `lean/MCore/BackwardAudit/HodgeHabitantGenericFirewall.lean`:30 | fechado |
| `MCore.BackwardAudit.no_hodgeHabitant_on_counterexample` | `lean/MCore/BackwardAudit/HodgeHabitantGenericFirewall.lean`:5 | fechado |
| `MCore.BackwardAudit.nonempty_hodgeHabitant_iff_concretePayload` | `lean/MCore/BackwardAudit/HodgeHabitant.lean`:53 | fechado |
| `MCore.BackwardAudit.open_state_is_50` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:57 | fechado |
| `MCore.BackwardAudit.positive_certificate_closes_core` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:80 | fechado |
| `MCore.BackwardAudit.positive_certificate_closes_hodge` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:152 | fechado |
| `MCore.BackwardAudit.positive_negative_incompatible` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:94 | fechado |
| `MCore.BackwardAudit.positive_only_is_closed_true` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:205 | fechado |
| `MCore.BackwardAudit.public_reuse_plus_H01_payload_closes_pointwise` | `lean/MCore/BackwardAudit/H01PublicReuseCompression.lean`:76 | fechado |
| `MCore.BackwardAudit.r1d_no_longer_mandatory_gate` | `lean/MCore/BackwardAudit/H01DirectCoreCompression.lean`:57 | fechado |
| `MCore.BackwardAudit.r3_no_longer_mandatory_gate` | `lean/MCore/BackwardAudit/H01DirectCoreCompression.lean`:60 | fechado |
| `MCore.BackwardAudit.realize_hodgeClass_eq_smul_cycleClass` | `lean/MCore/BackwardAudit/HodgeHabitantConstructors.lean`:54 | fechado |
| `MCore.BackwardAudit.realize_hodgeClass_eq_zero` | `lean/MCore/BackwardAudit/HodgeHabitantConstructors.lean`:40 | fechado |
| `MCore.BackwardAudit.realize_smul_cycleClass` | `lean/MCore/BackwardAudit/HodgeHabitantConstructors.lean`:25 | fechado |
| `MCore.BackwardAudit.realize_zeroClass` | `lean/MCore/BackwardAudit/HodgeHabitantConstructors.lean`:5 | fechado |
| `MCore.BackwardAudit.relative_open_math_closed` | `lean/MCore/BackwardAudit/HodgeAssumedCompleteClosure.lean`:67 | fechado |
| `MCore.BackwardAudit.remainingResearchSubgates_count` | `lean/MCore/BackwardAudit/H01PublicReuseCompression.lean`:72 | fechado |
| `MCore.BackwardAudit.remainingResearchSubgates_exact` | `lean/MCore/BackwardAudit/H01PublicReuseCompression.lean`:63 | fechado |
| `MCore.BackwardAudit.true_closed_state_is_0` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:60 | fechado |
| `MCore.BackwardAudit.twist_involutive` | `lean/MCore/BackwardAudit/HodgeTensionClosure.lean`:27 | fechado |
| `MCore.BackwardAudit.unconditionalCertificate_iff_payload` | `lean/MCore/BackwardAudit/HodgeUnconditionalCertificate.lean`:46 | fechado |
| `MCore.BackwardAudit.unconditional_counterexample_payload_false` | `lean/MCore/BackwardAudit/HodgeUnconditionalNoShortcut.lean`:94 | erro |
| `MCore.BackwardAudit.unconditional_false_in_concrete_span` | `lean/MCore/BackwardAudit/HodgeUnconditionalNoShortcut.lean`:36 | erro |
| `MCore.BackwardAudit.unconditional_hodge_claim` | `lean/MCore/BackwardAudit/HodgeUnconditionalCertificate.lean`:24 | fechado |
| `MCore.BackwardAudit.unconditional_true_not_in_concrete_span` | `lean/MCore/BackwardAudit/HodgeUnconditionalNoShortcut.lean`:42 | erro |
