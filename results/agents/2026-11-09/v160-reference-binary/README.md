# v1.6.0 EL Reference Binary, Orchestrator Stage, and P2 Suite Measurement

## Branch

- Branch: `v160/reference-binary` (base commit `6d7a02f107ffdf59ebaa219ac54df140b44e701e`)

## Summary

This change implements the executable Lean EL reference binary (`km-el-reference`), wires the orchestrator reference fallback stage into `km classify`, adds integration tests in `engine/tests/reference_stage.rs`, updates `lean/run-routing-certification-gate.sh` with the v1.6.0 P1 completeness theorems and `km-el-reference` checks, and measures `ELCommonSourceRecognizer.recognizeEL` across all 593 `elc`-routed inputs of the checkers-on suite (acceptance clause P2).

## Deliverables

1. **Lean executable `km-el-reference`** (`lean/KMELReferenceCheck.lean`, `lean/lakefile.toml`):
   - Parses `{"clauses":[...],"named":[...],"rules":[]}` (with optional `named` and `rules` defaulting to `[]`, plus optional `iri_map`: `[[id, iri], ...]`).
   - Rejects non-empty `rules` or duplicate `named` with exit code `3`.
   - Supports `--recognize-only`: exits `0` with `recognised` on stdout when `ELCommonSourceRecognizer.recognizeEL` returns `some`, or exits `3` with `not recognised: <reason>` on stderr when `recognizeEL` returns `none`.
   - In full mode, runs `KMConcreteWorkerAdapters.elReferenceExecution.run`, verifies `KMConcreteWorkerAdapters.requestedExactAccept`, and prints JSON `{"consistent": bool, "unsatisfiable": [...], "subsumptions": [[sub, [sup, ...]], ...]}` (or IRI-mapped JSON when `iri_map` is supplied).

2. **Rust orchestrator reference stage** (`engine/src/orchestrate/mod.rs`, `engine/src/orchestrate/frontend_run.rs`):
   - Added `KM_KEEP_CLAUSES=<dir>` support in `frontend_run.rs` and `run_ofn_for_reference` to materialise raw common-source clauses (`OfnClausesOnly`) plus metadata.
   - Added `KM_REFERENCE_FORCE=1` support in `orchestrate/mod.rs` so production routes (`run_atomic_mechanism`, portfolio `None` arm, `flat_nf1`, `mirror`) decline and hand control to the reference stage.
   - Added `try_reference_stage` at the end of `classify_with_evidence_mode` when `depth == 0`, `forced_route.is_none()`, `result.is_err()`, and `KM_REFERENCE_STAGE != "0"`.
   - Resolves `km-el-reference` from `KM_EL_REFERENCE_CHECKER`, `KM_EL_TEST_REFERENCE_CHECKER`, or a sibling `km-el-reference` next to the current executable.

3. **Integration tests** (`engine/tests/reference_stage.rs` and `engine/tests/fixtures/reference_stage/`):
   - `el_existentials_publishes_via_reference_stage_and_matches_production`
   - `el_role_chain_publishes_via_reference_stage_and_matches_production`
   - `el_unsat_class_publishes_via_reference_stage_and_matches_production`
   - `non_el_disjunction_declines_cleanly_under_reference_force`

4. **Routing certification gate** (`lean/run-routing-certification-gate.sh`):
   - Builds `ContextCalculus.ELCommonSourceRecognizer`, `ContextCalculus.ELReferenceSaturation`, `ContextCalculus.KMSupervisorInstance`, and `km-el-reference`.
   - Audits `#print axioms` for all seven P1 theorems from `docs/V1.6.0-ACCEPTANCE.md`:
     - `KMSupervisorInstance.kmSupervisor_sound`
     - `KMSupervisorInstance.kmSupervisor_complete_on_EL`
     - `KMSupervisorInstance.kmSupervisor_sound_and_complete_on_EL`
     - `KMConcreteWorkerAdapters.elReferenceExecution_completeAt`
     - `KMConcreteWorkerAdapters.elReferenceAccept_sound`
     - `ELReference.referenceBit_exact`
     - `ELCommonSourceRecognizer.recognizeEL_entails_iff`
   - Verifies `km-el-reference` on `lean/testdata/el-reference-valid.json` and rejects `lean/testdata/el-reference-malformed.json`.
   - Runs `cargo test --release --test reference_stage` with `KM_EL_TEST_REFERENCE_CHECKER`.

## P2 Recognition Measurement (593 `elc`-routed inputs)

Per-input data is recorded in `results/agents/2026-11-09/v160-reference-binary/p2-recognition.tsv`.

| Outcome / Rejection Reason | Count | Share (%) | Example Input | Notes |
| --- | ---: | ---: | --- | --- |
| **Accepted (`recognised`)** | 475 | 80.10% | `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_10004.owl` | `ELCommonSourceRecognizer.recognizeEL` returns `some` (exit 0) |
| **Rejected (total)** | 118 | 19.90% | | |
| `not recognised: nary_concept_conjunction` | 114 | 19.22% | `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_10008.owl` | Clause body has 3+ concept atoms `C1(x) /\ C2(x) /\ C3(x) -> D(x)` from n-ary `ObjectIntersectionOf`; `parseClause` only matches binary NF2 |
| `exit 124` (300 s timeout) | 3 | 0.51% | `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_11395.owl` | Giant ORE ontologies (`ore_ont_11395.owl`, `ore_ont_14042.owl`, `ore_ont_1559.owl`) where Lean JSON parsing + list traversal exceeds 300 s |
| `not recognised: individual_or_constant_term` | 1 | 0.17% | `engine/tests/fixtures/finite_rule_taxonomy.ofn` | Initial `ofn` pass emits grounded DL-safe rule clauses with individual constants before `finite_rule_class_projection` rewrites to a TBox-only ontology for `elc` |
| **Total `elc`-routed inputs** | **593** | **100.00%** | | |

## `reference_stage` Test Output

```text
running 4 tests
test el_existentials_publishes_via_reference_stage_and_matches_production ... ok
test el_role_chain_publishes_via_reference_stage_and_matches_production ... ok
test el_unsat_class_publishes_via_reference_stage_and_matches_production ... ok
test non_el_disjunction_declines_cleanly_under_reference_force ... ok

test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.10s
```

## Routing Certification Gate Output

```text
ℹ [3609/3624] Replayed ContextCalculus.ELCommonSourceRecognizer
info: ContextCalculus/ELCommonSourceRecognizer.lean:1258:0: 'ContextCalculus.ELCommonSourceRecognizer.recognizeEL_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELCommonSourceRecognizer.lean:1259:0: 'ContextCalculus.ELCommonSourceRecognizer.recognizeEL_unsat_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
ℹ [3610/3624] Replayed ContextCalculus.ELReferenceSaturation
info: ContextCalculus/ELReferenceSaturation.lean:793:0: 'ContextCalculus.ELReference.referenceBit_exact' depends on axioms: [propext, Quot.sound]
ℹ [3611/3624] Replayed ContextCalculus.KMSupervisorInstance
info: ContextCalculus/KMSupervisorInstance.lean:84:0: 'ContextCalculus.KMSupervisorInstance.kmSupervisor_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/KMSupervisorInstance.lean:85:0: 'ContextCalculus.KMSupervisorInstance.kmSupervisor_coversAt_of_EL' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/KMSupervisorInstance.lean:86:0: 'ContextCalculus.KMSupervisorInstance.kmSupervisor_complete_on_EL' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/KMSupervisorInstance.lean:87:0: 'ContextCalculus.KMSupervisorInstance.kmSupervisor_sound_and_complete_on_EL' depends on axioms: [propext, Classical.choice, Quot.sound]
...
routing certification gate passed
```
