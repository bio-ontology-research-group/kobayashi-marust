# v1.6.0 Force-Decline Guards and Reference-Stage Spawn Hardening

Date: 2026-11-10
Branch: `v160/force-guards`
Worktree: `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v160-reference-binary`

## 1. Summary

This change closes every remaining production publication path under `KM_REFERENCE_FORCE=1` so that forced runs always decline production classification with `OrchestrateError::OutOfFragment("KM_REFERENCE_FORCE=1".into())` and enter `try_reference_stage`. It also hardens `try_reference_stage` to invoke `km-el-reference` through `crate::lean_checkers::CheckerCommand` under a dedicated wall-clock budget `KM_REFERENCE_BUDGET_S` (default 300 s), logs `procedure=<el|alc>` when the reference output JSON supplies `"procedure"`, and rejects `meta.profile.positive_el_abox_materializable` sources at the reference stage because their role assertions live in `nominal_abox` rather than the clause stream.

## 2. Guarded Production Publication Paths

Every production publication path in `classify_with_evidence_inner` and its helpers now checks `reference_force_enabled()` (`KM_REFERENCE_FORCE=1`):

| # | Path / Helper | File & Line(s) | Unforced Publication Line(s) | Notes |
|---|---|---|---|---|
| 1 | `run_atomic_mechanism` | `engine/src/orchestrate/mod.rs:909` | `mod.rs:3751` | Existing guard; declines non-portfolio atomic leaves (`Elc`, `Cb`, `Ht`, `Tableau`). |
| 2 | Ground-rule source / data-ABox projection (`KM_GROUND_RULE_SOURCE` / `KM_DATA_ABOX_PROJECT`) | `engine/src/orchestrate/mod.rs:1977` | `mod.rs:2029` | Previously published 3 inputs in P3 via `data_source::automatic_candidate` + `KM_DATA_ABOX_PROJECT`. |
| 3 | Automatic data-source candidate (`data_source::automatic_candidate`) | `engine/src/orchestrate/mod.rs:2037` | `mod.rs:2058` | Skips speculative data-source rewrite probes under force. |
| 4 | Explicit symbolic source bridge (`KM_SYMBOLIC_SOURCE_BRIDGE`) | `engine/src/orchestrate/mod.rs:2072` | `mod.rs:2075` | Returns `OutOfFragment("KM_REFERENCE_FORCE=1")` under force. |
| 5 | Automatic symbolic source bridge (`symbolic_source::automatic_candidate` / `symbolic_source::classify_text`) | `engine/src/orchestrate/mod.rs:2078`, `engine/src/orchestrate/symbolic_source.rs:39` | `mod.rs:2087`, `symbolic_source.rs:67` | Previously published 1 input (`ore_ont_5107.owl`) in P3 by calling `run_bridge_producer_input_typed` directly. |
| 6 | Positive ABox quotient (`positive_abox_quotient::try_build`) | `engine/src/orchestrate/mod.rs:2113` | `mod.rs:2131` | Skips positive ABox quotient rewrite under force. |
| 7 | Disjoint-union ABox quotient (`abox_quotient::try_build`) | `engine/src/orchestrate/mod.rs:2151` | `mod.rs:2227`, `2271`, `2317` | Skips disjoint-union ABox quotient rewrite and its three publication returns under force. |
| 8 | Flat NF1 fast path (`flat_nf1::try_classify`) | `engine/src/orchestrate/mod.rs:2341` | `mod.rs:2362` | Existing guard. |
| 9 | Mirror fast path (`mirror::try_classify`) | `engine/src/orchestrate/mod.rs:2368` | `mod.rs:2384` | Existing guard. |
| 10 | Finite-rule class projection (`meta.profile.finite_rule_class_projection` / `checked_finite_rule_taxonomy`) | `engine/src/orchestrate/mod.rs:2422`, `4305` | `mod.rs:2431`, `2445`, `4313` | Previously published 2 inputs (`fr213.ofn`, `fr301.ofn`) in P3. |
| 11 | Bounded bridge-first probe (`bounded_bridge_first_candidate`) | `engine/src/orchestrate/mod.rs:2480` | `mod.rs:2566` | Skips speculative bridge-first probes under force. |
| 12 | Compact typed / functional-data ABox bridge probe (`compact_typed_bridge_first_candidate`, `functional_data_abox_bridge_candidate`) | `engine/src/orchestrate/mod.rs:2607` | `mod.rs:2626`, `2649` | Skips compact typed bridge probes under force. |
| 13 | Uncertified nominal general-HT probe (`KM_NOMINAL_GENERAL_HT_PROBE_UNCERTIFIED`) | `engine/src/orchestrate/mod.rs:2690` | `mod.rs:2718` | Skips nominal general-HT probe under force. |
| 14 | Certified nominal production probe (`certified_nominal_production_probe_candidate`) | `engine/src/orchestrate/mod.rs:2746` | `mod.rs:2772` | Skips certified nominal production probe under force. |
| 15 | Disjoint-union global consistency probe (`KM_ABOX_DISJOINT_UNION_CHECK` / `disjoint_union_global_consistency`) | `engine/src/orchestrate/mod.rs:2797`, `4259` | `mod.rs:2809` | Guards both the caller branch and `disjoint_union_global_consistency`. |
| 16 | ABox-inconsistency fast path (`meta.abox_inconsistent`) | `engine/src/orchestrate/mod.rs:3107` | `mod.rs:3110` | Previously published 24 ABox-inconsistent inputs in P3; `try_reference_stage` continues to decline `meta.abox_inconsistent` sources (`mod.rs:4094`). |
| 17 | Positive-EL ABox materialization (`meta.profile.positive_el_abox_materializable` / `KM_EL_ABOX_CHECK` / `certified_el_out`) | `engine/src/orchestrate/mod.rs:3136`, `3414` | `mod.rs:3173`, `3751` | Previously published `realization/inconsistent.ofn` in P3; `try_reference_stage` also declines `meta.profile.positive_el_abox_materializable` (`mod.rs:4095`) because its role assertions reside in `nominal_abox` outside the clause stream. |
| 18 | DL-safe rules consistency and rule-aware taxonomy (`cfg.ht_rules` / `rules_consistency` / `complete_rule_taxonomy`) | `engine/src/orchestrate/mod.rs:3232`, `4377`, `4548` | `mod.rs:3305`, `3330`, `3732` | Previously published 86 rule ontologies and timed out on 4 `ht_rules` ontologies in P3. |
| 19 | Portfolio fallback (`Mechanism::Portfolio`) | `engine/src/orchestrate/mod.rs:3484` | `mod.rs:3751` | Existing guard. |
| 20 | Final `map_engine_out_to_evidence` tail in `classify_with_evidence_inner` | `engine/src/orchestrate/mod.rs:3750` | `mod.rs:3751` | Defense-in-depth guard before output mapping in `classify_with_evidence_inner`. |

## 3. Reference-Stage Spawn Hardening and Procedure Logging

1. **`CheckerCommand` with per-stage deadline (`engine/src/lean_checkers.rs:582-765`)**:
   - Added `CheckerCommand::time_limit(&mut self, limit: Option<Duration>)` and `CheckerCommand::output_timed(&mut self) -> io::Result<(Output, bool)>`.
   - `try_reference_stage` (`engine/src/orchestrate/mod.rs:4144-4161`) now spawns `km-el-reference` via `CheckerCommand`, inheriting `LEAN_STACK_SIZE_KB=262144`, `PR_SET_PDEATHSIG=SIGKILL`, and the thread-creation retry loop, under the stage budget `KM_REFERENCE_BUDGET_S` (default `300.0` s via `reference_stage_budget()` at `mod.rs:4021-4028`).
   - When the deadline expires (`timed_out == true`), `try_reference_stage` logs `KM_TIMING KM_REFERENCE_STAGE declined: budget` and returns `None`.
2. **Procedure logging (`engine/src/orchestrate/mod.rs:4011-4017`, `4181-4186`, `4218-4226`)**:
   - `ReferenceStageOutput` deserializes an optional `procedure: Option<String>` field (`#[serde(default)]`).
   - When present and non-empty, `try_reference_stage` logs `KM_TIMING KM_REFERENCE_STAGE published procedure=<el|alc>` (lowercased); when absent, it logs `KM_TIMING KM_REFERENCE_STAGE published`.

## 4. Verification

1. **Integration tests (`engine/tests/reference_stage.rs`)**:
   - Added fixtures `engine/tests/fixtures/reference_stage/rules_taxonomy.ofn` and `engine/tests/fixtures/reference_stage/abox_inconsistent.ofn`.
   - Added `reference_stage_rules_declines_under_force`, `reference_stage_abox_inconsistent_declines_under_force` (testing both `abox_inconsistent.ofn` and `realization/inconsistent.ofn`), and `reference_stage_budget_timeout_declines_with_budget_reason` (`KM_REFERENCE_BUDGET_S=0`).
   - All 9 tests in `engine/tests/reference_stage.rs` pass (`9 passed; 0 failed` in 3.22 s).
2. **P3 unguarded and timeout set (120 inputs)**:
   - Re-ran all 116 `production_unguarded` inputs and all 4 `ht_rules` timeout inputs from `results/agents/2026-11-10/v160-p3-suite/data/p3-results.tsv` under `KM_REFERENCE_FORCE=1`: all 120 inputs now decline at `KM_REFERENCE_STAGE` (`exit 3`, empty stdout, `0` unguarded publications, `0` timeouts).
3. **Library unit test suite (`cargo test --release --lib -- --test-threads=1`)**:
   - Ran in a clean environment (`env -i PATH=$PATH HOME=$HOME KM_THREADS=1`): `3121 passed; 21 failed; 10 ignored`.
   - The 21 failures match `.work/worktrees/fix-bridge-defers/results/agents/2026-11-01/bridge-defers/data/lib-failures.txt` line for line.
