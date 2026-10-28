# m-core-hodge — branch `research/pure-math-final-proof-v1`

Lean sources from the branch `research/pure-math-final-proof-v1` of the private repository `ShantiDraconis/m-core-hodge`, commit `d80bb0f1228d68b0b229d5f1b29e134b2fef177a` (2026-09-20T08:41:56+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 5 — closed 5, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 14 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `5fc2339607af7782a232604af69aeb5f0d92b5cdac652617a422629c07bb06eb`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-hodge/research_pure-math-final-proof-v1/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.BackwardAudit.constructor_implies_rational_hodge` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:19 | fechado |
| `MCore.BackwardAudit.hodge_constructor_iff_endpoint` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:32 | fechado |
| `MCore.BackwardAudit.hodge_witness_constructor_still_open` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:42 | fechado |
| `MCore.BackwardAudit.rational_hodge_implies_constructor` | `lean/MCore/BackwardAudit/WitnessKernel.lean`:26 | fechado |
| `MCore.Research.return_to_primary` | `lean/MCore/Research/ParallelClosure.lean`:10 | fechado |
