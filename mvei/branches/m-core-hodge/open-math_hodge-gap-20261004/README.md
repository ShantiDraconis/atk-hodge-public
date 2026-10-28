# m-core-hodge — branch `open-math/hodge-gap-20261004`

Lean sources from the branch `open-math/hodge-gap-20261004` of the private repository `ShantiDraconis/m-core-hodge`, commit `59f3ab6bdf3a1b60ec43550660228c2860f639ad` (2026-10-04T22:56:59+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 77 — closed 68, conditional 0, open 3, proof error 6, not reached 0, no result 0.
* History: 62 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `12e2d94aa4cf8a25a448451d35f9981d435dc498acbd9127ff284514834284a9`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-hodge/open-math_hodge-gap-20261004/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `P05.Hodge.ACandidate.accept_sound` | `lean/MCore/P05/Hodge/ConcreteSearchEngine.lean`:74 | fechado |
| `P05.Hodge.B_is_mechanical` | `lean/MCore/P05/Hodge/CompressedFiveQuestions.lean`:41 | fechado |
| `P05.Hodge.C_still_material` | `lean/MCore/P05/Hodge/MaterialSearchFrontier.lean`:98 | fechado |
| `P05.Hodge.CohomologyCoordinates.equal_complete` | `lean/MCore/P05/Hodge/SearchArchitecture.lean`:106 | fechado |
| `P05.Hodge.CohomologyCoordinates.equal_sound` | `lean/MCore/P05/Hodge/SearchArchitecture.lean`:96 | fechado |
| `P05.Hodge.D_is_mechanical` | `lean/MCore/P05/Hodge/CompressedFiveQuestions.lean`:55 | fechado |
| `P05.Hodge.E_still_material` | `lean/MCore/P05/Hodge/MaterialSearchFrontier.lean`:101 | fechado |
| `P05.Hodge.OpenMath.H2H3HilbertProducer.closesR2` | `open_math/Hodge_H2_H3_Forcing.lean`:346 | fechado |
| `P05.Hodge.OpenMath.correspondence_actionEval_eq_cycleEval` | `open_math/Hodge_H2_H3_Forcing.lean`:950 | erro |
| `P05.Hodge.OpenMath.decomposition_implies_R2` | `open_math/Hodge_H2_H3_Forcing.lean`:150 | fechado |
| `P05.Hodge.OpenMath.decomposition_implies_R2_nonempty` | `open_math/Hodge_H2_H3_Forcing.lean`:185 | fechado |
| `P05.Hodge.OpenMath.decomposition_implies_concrete_span` | `open_math/Hodge_H2_H3_Forcing.lean`:131 | fechado |
| `P05.Hodge.OpenMath.divisorSource_class_algebraic` | `open_math/Hodge_H2_H3_Forcing.lean`:1412 | aberto-sorry |
| `P05.Hodge.OpenMath.h2a_h2b_do_not_force_h2c` | `open_math/Hodge_H2_H3_Forcing.lean`:539 | aberto-sorry |
| `P05.Hodge.OpenMath.h2cCounterCombination_eval_false` | `open_math/Hodge_H2_H3_Forcing.lean`:527 | erro |
| `P05.Hodge.OpenMath.h2c_correspondence_action_tail_mechanical` | `open_math/Hodge_H2_H3_Forcing.lean`:1081 | fechado |
| `P05.Hodge.OpenMath.h2c_correspondence_route_tail_mechanical` | `open_math/Hodge_H2_H3_Forcing.lean`:883 | fechado |
| `P05.Hodge.OpenMath.h2c_divisor_correspondence_tail_mechanical` | `open_math/Hodge_H2_H3_Forcing.lean`:1506 | fechado |
| `P05.Hodge.OpenMath.h2c_divisor_route_tail_mechanical` | `open_math/Hodge_H2_H3_Forcing.lean`:719 | fechado |
| `P05.Hodge.OpenMath.h2c_generation_still_open` | `open_math/Hodge_H2_H3_Forcing.lean`:395 | fechado |
| `P05.Hodge.OpenMath.h2c_lowerCodim_route_tail_mechanical` | `open_math/Hodge_H2_H3_Forcing.lean`:1286 | erro |
| `P05.Hodge.OpenMath.h2h3_mechanical_tail_closed` | `open_math/Hodge_H2_H3_Forcing.lean`:392 | fechado |
| `P05.Hodge.OpenMath.h2h3_then_r3_yields_original_span` | `open_math/Hodge_H2_H3_Forcing.lean`:404 | erro |
| `P05.Hodge.OpenMath.identityCorrespondenceBackend_realize` | `open_math/Hodge_H2_H3_Forcing.lean`:1111 | fechado |
| `P05.Hodge.OpenMath.lowerCodim_pushEval_eq_cycleEval` | `open_math/Hodge_H2_H3_Forcing.lean`:1178 | erro |
| `P05.Hodge.OpenMath.nonempty_usefulFiber_iff_nonCircularQbarIntersection` | `open_math/Hodge_H2_H3_Forcing.lean`:41 | fechado |
| `P05.Hodge.Q5_not_forced_by_spread` | `lean/MCore/P05/Hodge/OpenWitnesses.lean`:60 | fechado |
| `P05.Hodge.Q7_Q8_do_not_force_Q9` | `lean/MCore/P05/Hodge/OpenWitnesses.lean`:72 | fechado |
| `P05.Hodge.Q9_to_exact_R2` | `lean/MCore/P05/Hodge/OpenWitnesses.lean`:82 | fechado |
| `P05.Hodge.R3CombinationSpecialization.closes_span` | `lean/MCore/P05/Hodge/R3CombinationMincut.lean`:52 | fechado |
| `P05.Hodge.R3_still_material` | `lean/MCore/P05/Hodge/MaterialSearchFrontier.lean`:104 | fechado |
| `P05.Hodge.answerE_iff_Q3` | `lean/MCore/P05/Hodge/ExactFiveQuestions.lean`:133 | fechado |
| `P05.Hodge.answer_Q10_proved` | `lean/MCore/P05/Hodge/KernelQuestionMatrix.lean`:113 | fechado |
| `P05.Hodge.answer_Q15_open` | `lean/MCore/P05/Hodge/KernelQuestionMatrix.lean`:116 | fechado |
| `P05.Hodge.answer_Q6_refuted` | `lean/MCore/P05/Hodge/KernelQuestionMatrix.lean`:106 | fechado |
| `P05.Hodge.answer_Q9_open` | `lean/MCore/P05/Hodge/KernelQuestionMatrix.lean`:110 | fechado |
| `P05.Hodge.answersABCDE_close_R2` | `lean/MCore/P05/Hodge/ExactFiveQuestions.lean`:150 | fechado |
| `P05.Hodge.basepointA_search_hits` | `lean/MCore/P05/Hodge/MaterialSearchFrontier.lean`:49 | fechado |
| `P05.Hodge.basepointR3_closes_span` | `lean/MCore/P05/Hodge/BasepointR3FastPath.lean`:87 | aberto-sorry |
| `P05.Hodge.basepointRouteGaps_count` | `lean/MCore/P05/Hodge/BasepointR3FastPath.lean`:162 | fechado |
| `P05.Hodge.basepoint_fast_path_green` | `lean/MCore/P05/Hodge/MaterialSearchFrontier.lean`:95 | fechado |
| `P05.Hodge.castCohomology_cancel` | `lean/MCore/P05/Hodge/BasepointR3FastPath.lean`:35 | fechado |
| `P05.Hodge.castCombination_eval` | `lean/MCore/P05/Hodge/BasepointR3FastPath.lean`:46 | erro |
| `P05.Hodge.certified_search_answers_close_R2` | `lean/MCore/P05/Hodge/SearchArchitecture.lean`:216 | fechado |
| `P05.Hodge.compressedOpenAnswers_count` | `lean/MCore/P05/Hodge/CompressedFiveQuestions.lean`:83 | fechado |
| `P05.Hodge.counterA_search_hits` | `lean/MCore/P05/Hodge/ExecutableSearchSmokeTest.lean`:25 | fechado |
| `P05.Hodge.counterC_search_hits` | `lean/MCore/P05/Hodge/ExecutableSearchSmokeTest.lean`:56 | fechado |
| `P05.Hodge.counterE_search_rejects` | `lean/MCore/P05/Hodge/ExecutableSearchSmokeTest.lean`:86 | fechado |
| `P05.Hodge.counterE_verifier_rejects` | `lean/MCore/P05/Hodge/ExecutableSearchSmokeTest.lean`:82 | fechado |
| `P05.Hodge.divisorCorrespondenceKernelProducer_closes_R2_target` | `lean/MCore/P05/Hodge/DivisorCorrespondenceKernelPressure.lean`:50 | fechado |
| `P05.Hodge.divisorCorrespondenceKernelProducer_q1_lt_p` | `lean/MCore/P05/Hodge/DivisorCorrespondenceKernelPressure.lean`:101 | fechado |
| `P05.Hodge.divisorCorrespondenceKernelProducer_source_algebraic` | `lean/MCore/P05/Hodge/DivisorCorrespondenceKernelPressure.lean`:116 | fechado |
| `P05.Hodge.exact_R2_can_be_endpoint` | `lean/MCore/P05/Hodge/OpenWitnesses.lean`:98 | fechado |
| `P05.Hodge.executable_search_fail_closed` | `lean/MCore/P05/Hodge/ExecutableSearchSmokeTest.lean`:90 | fechado |
| `P05.Hodge.findAccepted_sound` | `lean/MCore/P05/Hodge/ConcreteSearchEngine.lean`:14 | fechado |
| `P05.Hodge.five_answer_search_sound` | `lean/MCore/P05/Hodge/SearchArchitecture.lean`:271 | fechado |
| `P05.Hodge.five_answer_tail_closed` | `lean/MCore/P05/Hodge/ExactFiveQuestions.lean`:204 | fechado |
| `P05.Hodge.hodgeKernelQ3_closes_R2` | `lean/MCore/P05/Hodge/KernelQuestions.lean`:93 | fechado |
| `P05.Hodge.kernelQCounter_Q1_inhabited` | `lean/MCore/P05/Hodge/KernelQuestions.lean`:189 | fechado |
| `P05.Hodge.kernelQCounter_Q2_inhabited` | `lean/MCore/P05/Hodge/KernelQuestions.lean`:193 | fechado |
| `P05.Hodge.kernelQCounter_Q3_impossible` | `lean/MCore/P05/Hodge/KernelQuestions.lean`:197 | fechado |
| `P05.Hodge.materialSearchGaps_count` | `lean/MCore/P05/Hodge/MaterialSearchFrontier.lean`:76 | fechado |
| `P05.Hodge.material_head_is_open` | `lean/MCore/P05/Hodge/KernelQuestionMatrix.lean`:140 | fechado |
| `P05.Hodge.material_tail_is_closed` | `lean/MCore/P05/Hodge/KernelQuestionMatrix.lean`:135 | fechado |
| `P05.Hodge.matrix_has_15_questions` | `lean/MCore/P05/Hodge/KernelQuestionMatrix.lean`:52 | fechado |
| `P05.Hodge.q1_q2_not_enough` | `lean/MCore/P05/Hodge/KernelQuestionMatrix.lean`:55 | fechado |
| `P05.Hodge.q3_is_sufficient_for_R2` | `lean/MCore/P05/Hodge/KernelQuestionMatrix.lean`:63 | fechado |
| `P05.Hodge.r1d_gate_is_exact` | `lean/MCore/P05/Hodge/KernelQuestionMatrix.lean`:78 | fechado |
| `P05.Hodge.r2_gate_is_exact` | `lean/MCore/P05/Hodge/KernelQuestionMatrix.lean`:91 | fechado |
| `P05.Hodge.r3MinimalQuestions_count` | `lean/MCore/P05/Hodge/R3CombinationMincut.lean`:134 | fechado |
| `P05.Hodge.r3Questions_count` | `lean/MCore/P05/Hodge/R3SpecializationMincut.lean`:194 | fechado |
| `P05.Hodge.r3_action_closes_original_span` | `lean/MCore/P05/Hodge/R3SpecializationMincut.lean`:118 | fechado |
| `P05.Hodge.remainingWitnessKinds_count` | `lean/MCore/P05/Hodge/OpenWitnesses.lean`:128 | fechado |
| `P05.Hodge.searchE_sound` | `lean/MCore/P05/Hodge/ConcreteSearchEngine.lean`:231 | fechado |
| `P05.Hodge.specializeCombination_eval` | `lean/MCore/P05/Hodge/R3SpecializationMincut.lean`:61 | fechado |
| `P05.Hodge.verifyAnswerE_complete` | `lean/MCore/P05/Hodge/SearchArchitecture.lean`:153 | fechado |
| `P05.Hodge.verifyAnswerE_sound` | `lean/MCore/P05/Hodge/SearchArchitecture.lean`:134 | fechado |
