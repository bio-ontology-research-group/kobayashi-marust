# v1.6.0 ALC Reference Procedure in `km-el-reference` and Orchestrator Stage

## Branch

- Branch: `v160/alc-binary` (base commit `7a1fb406`)

## Summary

This change wires `KMConcreteWorkerAdapters.alcReferenceExecution` into the `km-el-reference` executable and the Rust orchestrator reference stage (`orchestrate::try_reference_stage`) so the shipped pipeline matches the stage order of `KMSupervisorInstance.kmSupervisor_complete_on_EL_or_ALC`.

## Deliverables

1. **Lean executable `km-el-reference` (`lean/KMELReferenceCheck.lean`)**:
   - Added `--procedure el|alc|el-then-alc` (default `el-then-alc`) alongside `--recognize-only`, preserving the binary name `km-el-reference`, input JSON document format, symbol interning, and `List FCL` mapping.
   - In `el-then-alc` mode, `elReferenceExecution.run` runs first; if it declines, the ALC reference stage runs next.
   - Before evaluating `alcReferenceExecution.run`, the ALC stage checks the recognised signature count against `KM_ALC_REFERENCE_MAX_CONCEPTS` (default `16`). When `recognized.conceptCount` exceeds the limit, the binary exits with code `3` and stderr reason `alc budget: N concept names`. The module docstring notes that this budget is a runtime resource bound outside the Lean completeness proof.
   - Rechecks `requestedExactAccept` on every `.publish` outcome before printing the output taxonomy JSON.

2. **Rust orchestrator and integration tests (`engine/src/orchestrate/mod.rs`, `engine/tests/reference_stage.rs`, `engine/tests/fixtures/reference_stage/`)**:
   - `try_reference_stage` invokes `km-el-reference` once with `--procedure el-then-alc`, logging `KM_REFERENCE_STAGE declined: not recognised: ...` or `KM_REFERENCE_STAGE declined: alc budget: ...` on decline.
   - Added `reference_stage_alc_disjunction_matches_unforced` (`alc_disjunction.ofn`: `:A ⊑ :B ⊔ :C`, `:B ⊑ :D`, `:C ⊑ :D`, forcing `:A ⊑ :D` outside EL) verifying that the forced reference-stage taxonomy equals the unforced answer.
   - Added `reference_stage_alc_budget_declines_without_publishing` (`alc_budget.ofn`: 17 declared classes plus 1 disjunction definer and 2 consistency probes = 20 concept names) verifying that the stage declines with `alc budget: 20 concept names`.
   - Updated `non_el_disjunction.ofn` with `SubObjectPropertyOf(:r :s)` so it lies outside both EL and ALC (ALCH) and declines with `not recognised: role_inclusion_or_inverse_clause`.

3. **Routing certification gate (`lean/run-routing-certification-gate.sh`, `lean/testdata/alc-reference-valid.json`)**:
   - Added `ContextCalculus.ALCCommonSourceRecognizer` and `ContextCalculus.ALCReferenceSaturation` to the gate build targets.
   - Added axiom-audit checks for `KMSupervisorInstance.kmSupervisor_complete_on_ALC`, `KMSupervisorInstance.kmSupervisor_sound_and_complete_on_ALC`, `KMSupervisorInstance.kmSupervisor_complete_on_EL_or_ALC`, `KMConcreteWorkerAdapters.alcReferenceExecution_completeAt`, `KMConcreteWorkerAdapters.alcReferenceAccept_sound`, `ALCReference.alcBit_exact`, and `ALCCommonSourceRecognizer.recognizeALC_entails_iff`.
   - Added execution checks for `km-el-reference --procedure el-then-alc` on `lean/testdata/el-reference-valid.json` and `km-el-reference --procedure alc` on `lean/testdata/alc-reference-valid.json`.

## Verification

- `LEAN_NUM_THREADS=2 nice lake build km-el-reference`: passed (7018 jobs).
- `cargo test --release --test reference_stage` (with `KM_EL_TEST_REFERENCE_CHECKER`): 6 passed, 0 failed (`reference_stage_el_existentials_matches_unforced`, `reference_stage_el_role_chain_matches_unforced`, `reference_stage_el_unsat_class_matches_unforced`, `reference_stage_alc_disjunction_matches_unforced`, `reference_stage_alc_budget_declines_without_publishing`, `reference_stage_non_el_declines_without_publishing`).
- `lean/run-routing-certification-gate.sh`: passed (`routing certification gate passed`, 0 `sorryAx`).
- `cargo test --release --lib -- --test-threads=1`: 3121 passed, 21 failed (exact match to the 21 baseline failures in `.work/worktrees/fix-bridge-defers/results/agents/2026-11-01/bridge-defers/data/lib-failures.txt`).
