# m-core-hodge — branch `atk/hodge-material-target-hardening-20261001`

Lean sources from the branch `atk/hodge-material-target-hardening-20261001` of the private repository `ShantiDraconis/m-core-hodge`, commit `7e834bb99add47f2eea8af582cdd1e3f0b8f9e30` (2026-10-01T17:32:24+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 6 — closed 4, conditional 0, open 0, proof error 0, not reached 2, no result 0.
* History: 5 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `b1def4a41aae1f45c4e4cf42576ac5ba9a058a06584c4ff7bdb0fdf1165dcf2e`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-hodge/atk_hodge-material-target-hardening-20261001/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.BackwardAudit.h01UniversalMaterialProducer_closes` | `lean/MCore/BackwardAudit/H01UniversalMaterialProducer.lean`:46 | nao_alcancado |
| `MCore.BackwardAudit.h01UniversalMaterialProducer_payload` | `lean/MCore/BackwardAudit/H01UniversalMaterialProducer.lean`:22 | nao_alcancado |
| `MCore.concreteHodgeMaterialTarget_closes` | `lean/MCore/BackwardAudit/ConcreteHodgeMaterialTarget.lean`:23 | fechado |
| `MCore.concreteHodgeMaterialTarget_has_variety` | `lean/MCore/BackwardAudit/ConcreteHodgeMaterialTarget.lean`:40 | fechado |
| `MCore.concreteHodgeMaterialTarget_implies_payload` | `lean/MCore/BackwardAudit/ConcreteHodgeMaterialTarget.lean`:32 | fechado |
| `MCore.concretePayload_vacuous_on_empty_model` | `audit/ATK_CONCRETE_PAYLOAD_MODEL_BINDING_COUNTERAUDIT.lean`:27 | fechado |
