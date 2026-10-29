# m-core-hodge — branch `audit/multistate-proof-refutation-v1`

Lean sources from the branch `audit/multistate-proof-refutation-v1` of the private repository `ShantiDraconis/m-core-hodge`, commit `867f54bac28328c0200aeb292747c032b662deb4` (2026-09-19T09:47:12+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 54 — closed 8, conditional 0, open 0, proof error 0, not reached 46, no result 0.
* History: 72 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `81f12b58f1573014e707ae9d000c6ebe8f7269e19bb59463b439a69e0d137c73`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-hodge/audit_multistate-proof-refutation-v1/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `HodgeR1dAudit.basepoint_is_hodge` | `audit/hodge-r1d/R1dBasepointAttack.lean`:58 | nao_alcancado |
| `HodgeR1dAudit.basepoint_qbar_closes_r1d` | `audit/hodge-r1d/R1dBasepointAttack.lean`:96 | nao_alcancado |
| `HodgeR1dAudit.basepoint_residue_suffices` | `audit/hodge-r1d/R1dBasepointAttack.lean`:141 | nao_alcancado |
| `HodgeR1dAudit.isTypePP_castCohomology` | `audit/hodge-r1d/R1dBasepointAttack.lean`:46 | nao_alcancado |
| `HodgeR1dAudit.r1d_contract_iff_exact_residue` | `audit/hodge-r1d/R1dBasepointAttack.lean`:21 | nao_alcancado |
| `HodgeR1dAudit.trivial_spread_blocks_unconditional_r1d` | `audit/hodge-r1d/R1dBasepointAttack.lean`:110 | nao_alcancado |
| `HodgeR1dComponentSketchAudit.component_construction_not_attempted` | `audit/hodge-r1d/R1dComponentModelSketch.lean`:46 | nao_alcancado |
| `HodgeR1dComponentSketchAudit.component_model_still_open` | `audit/hodge-r1d/R1dComponentModelSketch.lean`:50 | nao_alcancado |
| `HodgeR1dFieldBridgeAudit.component_model_gives_qbar_hodge_point` | `audit/hodge-r1d/R1dFieldOfDefinitionBridge.lean`:68 | nao_alcancado |
| `HodgeR1dFieldBridgeAudit.field_of_definition_bridge_closes_r1d` | `audit/hodge-r1d/R1dFieldOfDefinitionBridge.lean`:87 | nao_alcancado |
| `HodgeR1dFieldBridgeAudit.field_of_definition_semantic_match_still_open` | `audit/hodge-r1d/R1dFieldOfDefinitionBridge.lean`:119 | nao_alcancado |
| `HodgeR1dVoisinAudit.has_qbar_point_on_locus_implies_r1d` | `audit/hodge-r1d/R1dVoisinBoundary.lean`:23 | nao_alcancado |
| `HodgeR1dVoisinAudit.r1d_iff_has_qbar_point_on_locus` | `audit/hodge-r1d/R1dVoisinBoundary.lean`:61 | nao_alcancado |
| `HodgeR1dVoisinAudit.r1d_implies_has_qbar_point_on_locus` | `audit/hodge-r1d/R1dVoisinBoundary.lean`:45 | nao_alcancado |
| `HodgeR1dVoisinAudit.r1d_voisin_general_case_still_open` | `audit/hodge-r1d/R1dVoisinBoundary.lean`:122 | nao_alcancado |
| `HodgeR1dVoisinAudit.voisin_semantic_match_still_open` | `audit/hodge-r1d/R1dVoisinBoundary.lean`:118 | nao_alcancado |
| `HodgeR2Audit.r1d_supplies_hodge_not_cycle_span` | `audit/hodge-r1d/R2ExactCut.lean`:49 | nao_alcancado |
| `HodgeR2Audit.r2_contract_is_exact_residue` | `audit/hodge-r1d/R2ExactCut.lean`:78 | nao_alcancado |
| `HodgeR2Audit.r2_data_iff_concrete_span` | `audit/hodge-r1d/R2ExactCut.lean`:7 | nao_alcancado |
| `HodgeR2Audit.r2_data_iff_semantic_span` | `audit/hodge-r1d/R2ExactCut.lean`:30 | nao_alcancado |
| `HodgeR2KnownRegimesAudit.divisor_regime_semantic_match_still_open` | `audit/hodge-r1d/R2KnownRegimes.lean`:71 | nao_alcancado |
| `HodgeR2KnownRegimesAudit.known_regime_certificate_closes_r2` | `audit/hodge-r1d/R2KnownRegimes.lean`:53 | nao_alcancado |
| `HodgeR2Lefschetz11Audit.lefschetz11_adapter_closes_r2` | `audit/hodge-r1d/R2Lefschetz11Adapter.lean`:162 | nao_alcancado |
| `HodgeR2Lefschetz11Audit.lefschetz11_remains_external` | `audit/hodge-r1d/R2Lefschetz11Adapter.lean`:260 | nao_alcancado |
| `HodgeR2Lefschetz11Audit.semantic_match_modulo_classical_closes_r2` | `audit/hodge-r1d/R2Lefschetz11Adapter.lean`:241 | nao_alcancado |
| `HodgeR2Lefschetz11DirectAudit.direct_lefschetz11_closes_concrete_span` | `audit/hodge-r1d/R2Lefschetz11Direct.lean`:60 | nao_alcancado |
| `HodgeR2Lefschetz11DirectAudit.direct_lefschetz11_closes_semantic_span` | `audit/hodge-r1d/R2Lefschetz11Direct.lean`:84 | nao_alcancado |
| `HodgeR3Audit.original_target_implies_r3` | `audit/hodge-r1d/R3ExactCut.lean`:35 | nao_alcancado |
| `HodgeR3Audit.r3_contract_iff_exact_residue` | `audit/hodge-r1d/R3ExactCut.lean`:19 | nao_alcancado |
| `HodgeR3Audit.r3_iff_original_target_given_point` | `audit/hodge-r1d/R3ExactCut.lean`:51 | nao_alcancado |
| `HodgeR3Audit.r3_iff_semantic_span_given_point` | `audit/hodge-r1d/R3ExactCut.lean`:70 | nao_alcancado |
| `HodgeR3FactorizationAudit.castCohomology_addClass` | `audit/hodge-r1d/R3GeometricFactorization.lean`:238 | nao_alcancado |
| `HodgeR3FactorizationAudit.castCohomology_smul` | `audit/hodge-r1d/R3GeometricFactorization.lean`:253 | nao_alcancado |
| `HodgeR3FactorizationAudit.castCohomology_zeroClass` | `audit/hodge-r1d/R3GeometricFactorization.lean`:224 | nao_alcancado |
| `HodgeR3FactorizationAudit.decomposed_specialization_has_original_class` | `audit/hodge-r1d/R3GeometricFactorization.lean`:503 | nao_alcancado |
| `HodgeR3FactorizationAudit.eval_specializeCombinationByGenerators` | `audit/hodge-r1d/R3GeometricFactorization.lean`:128 | nao_alcancado |
| `HodgeR3FactorizationAudit.factor_castCohomology_roundtrip` | `audit/hodge-r1d/R3GeometricFactorization.lean`:282 | nao_alcancado |
| `HodgeR3FactorizationAudit.r3_factor_semantic_match_still_open` | `audit/hodge-r1d/R3GeometricFactorization.lean`:561 | nao_alcancado |
| `HodgeR3GeometricAudit.geometric_r3_semantic_match_still_open` | `audit/hodge-r1d/R3GeometricSpecializationInterface.lean`:102 | nao_alcancado |
| `HodgeR3GeometricAudit.specialized_combination_has_original_class` | `audit/hodge-r1d/R3GeometricSpecializationInterface.lean`:45 | nao_alcancado |
| `HodgeR3NaturalityOriginAudit.chow_hilbert_origin_yields_cycle_class_naturality` | `audit/hodge-r1d/R3CycleClassNaturalityOrigin.lean`:218 | nao_alcancado |
| `HodgeR3NaturalityOriginAudit.relative_chow_hilbert_semantic_match_still_open` | `audit/hodge-r1d/R3CycleClassNaturalityOrigin.lean`:243 | nao_alcancado |
| `HodgeR3NaturalityOriginAudit.relative_origin_yields_cycle_class_naturality` | `audit/hodge-r1d/R3CycleClassNaturalityOrigin.lean`:184 | nao_alcancado |
| `HodgeR3TransportReturnAudit.castCohomology_roundtrip` | `audit/hodge-r1d/R3TransportReturnOrigin.lean`:24 | nao_alcancado |
| `HodgeR3TransportReturnAudit.reverse_path_returns_transported_alpha` | `audit/hodge-r1d/R3TransportReturnOrigin.lean`:90 | nao_alcancado |
| `MCore.Audit8x5.A_axis_pending` | `lean/MCore/Audit8x5.lean`:65 | fechado |
| `MCore.Audit8x5.HC_axis_blocking` | `lean/MCore/Audit8x5.lean`:60 | fechado |
| `MCore.Audit8x5.K_axis_pending` | `lean/MCore/Audit8x5.lean`:64 | fechado |
| `MCore.Audit8x5.Q_axis_matched` | `lean/MCore/Audit8x5.lean`:62 | fechado |
| `MCore.Audit8x5.S_axis_pending` | `lean/MCore/Audit8x5.lean`:63 | fechado |
| `MCore.Audit8x5.endpoint_iff_pointwise` | `lean/MCore/Audit8x5.lean`:25 | fechado |
| `MCore.Audit8x5.pointwise_payload_remains_open` | `lean/MCore/Audit8x5.lean`:42 | fechado |
| `MCore.Audit8x5.quantifier_match` | `lean/MCore/Audit8x5.lean`:38 | fechado |
| `MultistateAudit.Hodge.Gates.fullyAudited_elim` | `audit/20_BACKWARD_ELIMINATION/MassiveGateArchitecture.lean`:34 | nao_alcancado |
