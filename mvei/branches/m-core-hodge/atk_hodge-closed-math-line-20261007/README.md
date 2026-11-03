# m-core-hodge — branch `atk/hodge-closed-math-line-20261007`

Lean sources from the branch `atk/hodge-closed-math-line-20261007` of the private repository `ShantiDraconis/m-core-hodge`, commit `4de000498ca24fb6cd3f15bb26b2bf6115db64bf` (2026-10-07T20:07:57+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 25 — closed 23, conditional 0, open 1, proof error 1, not reached 0, no result 0.
* History: 39 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `5572797082a52e027e78bda8fd5a8ad4d2e7cf1c2191ccf00fb0c9356bb68d77`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-hodge/atk_hodge-closed-math-line-20261007/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.BackwardAudit.recovered_universalForward_closes_concrete` | `lean/MCore/BackwardAudit/HodgeRecoveredMaterialBridge.lean`:9 | fechado |
| `MCore.BackwardAudit.recovered_universalForward_closes_terminal` | `lean/MCore/BackwardAudit/HodgeRecoveredMaterialBridge.lean`:28 | fechado |
| `MCore.BackwardAudit.recovered_zero_constructor` | `lean/MCore/BackwardAudit/HodgeRecoveredMaterialBridge.lean`:39 | fechado |
| `MCore.HodgeR2MaterialProducer.toCanonicalTerminal` | `lean/MCore/HodgeClosedMathLine.lean`:208 | fechado |
| `MCore.HodgeR2MaterialProducer.toConcretePayload` | `lean/MCore/HodgeClosedMathLine.lean`:198 | fechado |
| `MCore.closed_canonical_terminal_iff_payload` | `lean/MCore/HodgeClosedMathLine.lean`:117 | fechado |
| `MCore.closed_constructive_material_to_payload` | `lean/MCore/HodgeClosedMathLine.lean`:67 | fechado |
| `MCore.closed_exact_r1d_cut` | `lean/MCore/HodgeClosedMathLine.lean`:75 | fechado |
| `MCore.closed_exact_r2_cut` | `lean/MCore/HodgeClosedMathLine.lean`:88 | fechado |
| `MCore.closed_exact_r3_cut` | `lean/MCore/HodgeClosedMathLine.lean`:103 | fechado |
| `MCore.closed_higher_run_to_span` | `lean/MCore/HodgeClosedMathLine.lean`:42 | fechado |
| `MCore.closed_material_producers_to_payload` | `lean/MCore/HodgeClosedMathLine.lean`:56 | fechado |
| `MCore.closed_material_split` | `lean/MCore/HodgeClosedMathLine.lean`:11 | fechado |
| `MCore.closed_universalForward_to_payload` | `lean/MCore/HodgeClosedMathLine.lean`:151 | fechado |
| `MCore.closed_zero_cycle_constructor` | `lean/MCore/HodgeClosedMathLine.lean`:125 | fechado |
| `MCore.cycleCombination_eval_append` | `lean/MCore/HodgeClosedMathLine.lean`:406 | erro |
| `MCore.directCycle_add_witness` | `lean/MCore/HodgeClosedMathLine.lean`:426 | aberto-sorry |
| `MCore.directCycle_of_eq_single` | `lean/MCore/HodgeClosedMathLine.lean`:385 | fechado |
| `MCore.directCycle_of_eq_zero` | `lean/MCore/HodgeClosedMathLine.lean`:374 | fechado |
| `MCore.directCycle_single_witness` | `lean/MCore/HodgeClosedMathLine.lean`:360 | fechado |
| `MCore.directCycle_zero_witness` | `lean/MCore/HodgeClosedMathLine.lean`:350 | fechado |
| `MCore.nonempty_directCycleProducer_iff_r2Producer` | `lean/MCore/HodgeClosedMathLine.lean`:330 | fechado |
| `MCore.nonempty_hodgeR2MaterialProducer_iff_habitant` | `lean/MCore/HodgeClosedMathLine.lean`:258 | fechado |
| `MCore.nonempty_hodgeR2MaterialProducer_iff_payload` | `lean/MCore/HodgeClosedMathLine.lean`:218 | fechado |
| `MCore.nonempty_hodgeR2MaterialProducer_iff_terminal` | `lean/MCore/HodgeClosedMathLine.lean`:245 | fechado |
