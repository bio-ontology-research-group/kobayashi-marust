# v1.6.0 Acceptance Clause P3: Forced Reference-Stage Suite Evaluation (2026-11-10)

## 1. Scope and Setup

This directory records the acceptance clause P3 evaluation (`docs/V1.6.0-ACCEPTANCE.md` section P3) on the fixed 1,781-input checkers-on suite (`results/agents/2026-10-30/checkers-on-suite/per-input.tsv`: 186 fixtures, 501 seed-family ontologies across bridge/cardinality/data/nominal/rule, and 1,094 ORE 2015 ontologies).

- **Branch / commit**: `v160/p3-suite` at `d0476260` (incorporating `v160/recognizer-perf` `243b8c04` and `v160/alc-binary` `3ce25ff2`).
- **Binaries**:
  - `engine/target/release/km`: SHA-256 `cec6aa8f0a4be59bb1d70227de44a1ce357ca98f3c94fb5120167e379a61c730`
  - `lean/.lake/build/bin/km-el-reference`: SHA-256 `c63be66cad334af924812f977fc93c0e5edc0a0e0123377e839d26cf7b1f9bb9`
- **Execution parameters**:
  - Unforced (production): `KM_THREADS=1 KM_TIMING=1 KM_REFERENCE_STAGE=0 km classify <ont> --lines`
  - Forced (reference stage): `KM_THREADS=1 KM_TIMING=1 KM_REFERENCE_FORCE=1 KM_EL_REFERENCE_CHECKER=lean/.lake/build/bin/km-el-reference LEAN_STACK_SIZE_KB=262144 km classify <ont> --lines`
  - Timeout: `300 s` per run (`start_new_session=True` with process-group `SIGKILL` on timeout), at most 4 concurrent runs (`--jobs 4`).
- **Artifacts**:
  - Per-input table (1,781 rows): `results/agents/2026-11-10/v160-p3-suite/data/p3-results.tsv`
  - Runner and summarizer script: `results/agents/2026-11-10/v160-p3-suite/tools/run_p3_suite.py`

## 2. Four Acceptance Checks

| Check | Requirement | Result | Status |
|---|---|---|---|
| **Check 1** | Every input that P2 counts as recognised (`p2-recognition.tsv`, 592 `accepted` inputs out of 593 `elc`-routed inputs) publishes under force, and its forced answer digest equals the unforced one. | **6 / 592** publish via `KM_REFERENCE_STAGE published` (procedure `EL`) with matching answer digests (`6 / 6`). **1 / 592** (`realization/inconsistent.ofn`) publishes via the unguarded `meta.abox_inconsistent` fast path with a matching digest (`1 / 1`). **585 / 592** (all 585 ORE `elc` inputs) time out at `300 s` inside `km-el-reference` (`elReferenceAccept`). | **FAIL (6 reference-published, 1 unguarded-published, 585 timeout; 0 digest mismatches)** |
| **Check 2** | Every other forced publication (ALC reference, or EL on inputs outside the 593) equals the unforced answer where the unforced run published. | **2 / 2** reference-stage ALC publications (`clause_or_definer_fallback.ofn`, `clause_top_conjunction_inconsistent.ofn`) match the unforced digest. **115 / 115** additional unguarded production-path publications outside the 592 also match the unforced digest (**117 / 117** total outside P2's 592). | **PASS (117 / 117 match; 2 / 2 via ALC reference stage)** |
| **Check 3** | No forced answer differs from an unforced answer anywhere. | **0 mismatches** across all **124** inputs that published an answer under `KM_REFERENCE_FORCE=1` (8 via `KM_REFERENCE_STAGE published` + 116 via unguarded production paths). | **PASS (0 mismatches)** |
| **Check 4** | Inputs where the unforced run itself published nothing (timeouts, declines) are listed separately with the forced outcome. | **17 inputs** published nothing in the unforced `300 s` run (8 timeouts, 4 `exit1`, 2 `exit-6`, 1 `exit3`, 1 `exit124`, 1 `exit2`). None published under force (11 declined, 5 timed out, 1 exited 2). Listed in Section 5. | **RECORDED (17 inputs)** |

### All 8 Reference-Stage Publications (`KM_TIMING KM_REFERENCE_STAGE published`)

| Family | Input | P2 Status | Unforced Route | Procedure | Unforced Digest | Forced Digest | Unforced Wall (s) | Forced Wall (s) |
|---|---|---|---|---|---|---|---:|---:|
| `fixture` | `fixtures/automatic_el_fallback.ofn` | `accepted` | `elc` | `EL` | `6c89984bf842b86c` | `6c89984bf842b86c` | 0.004 | 0.080 |
| `fixture` | `bridge_generator/clause_top_conjunction.ofn` | `accepted` | `elc` | `EL` | `ebae021fd69153f8` | `ebae021fd69153f8` | 0.006 | 0.088 |
| `fixture` | `fixtures/lean_el_v3_mixed.ofn` | `accepted` | `elc` | `EL` | `4bb8d50501af56b0` | `4bb8d50501af56b0` | 0.006 | 0.168 |
| `fixture` | `realization/sameas.ofn` | `accepted` | `elc` | `EL` | `3d39c1dcd9928711` | `3d39c1dcd9928711` | 0.003 | 0.077 |
| `fixture` | `fixtures/utf8_non_ascii.ofn` | `accepted` | `elc` | `EL` | `a78270c291c4bdca` | `a78270c291c4bdca` | 0.005 | 0.077 |
| `fixture` | `fixtures/utf8_non_ascii.ttl` | `accepted` | `elc` | `EL` | `a78270c291c4bdca` | `a78270c291c4bdca` | 0.006 | 0.078 |
| `fixture` | `bridge_generator/clause_or_definer_fallback.ofn` | `-` | `production_all` | `ALC` | `b2747f03587bfee3` | `b2747f03587bfee3` | 0.011 | 1.010 |
| `fixture` | `bridge_generator/clause_top_conjunction_inconsistent.ofn` | `-` | `production_all` | `ALC` | `78dc764240e471d6` | `78dc764240e471d6` | 0.010 | 3.832 |

The single P2-rejected `elc` input (`engine/tests/fixtures/finite_rule_taxonomy.ofn`) declines under force at `0.012 s` with `KM_TIMING KM_REFERENCE_STAGE declined: not recognised: not in pure EL/ALC clause-stream fragment`.

## 3. Per-Route Table of Forced Outcomes (All 1,781 Inputs)

| Unforced Route | Total | Ref Published (`EL`) | Ref Published (`ALC`) | Unguarded Prod Published | Declined: Meta Fragment Guard | Declined: Checker Not Recognised | Declined: ALC Budget | Declined: Frontend Failed | Declined: Lean OOM | Forced Timeout (`300 s`) | Error (`exit2`) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `elc` | 594 | 6 | 0 | 1 | 1 | 0 | 0 | 0 | 1 | 585 | 0 |
| `production_all` | 546 | 0 | 2 | 1 | 312 | 155 | 14 | 2 | 2 | 58 | 0 |
| `ht_bridge` | 237 | 0 | 0 | 18 | 177 | 0 | 0 | 42 | 0 | 0 | 0 |
| `certified_nominals` | 203 | 0 | 0 | 2 | 141 | 4 | 0 | 56 | 0 | 0 | 0 |
| `ht_rules` | 105 | 0 | 0 | 88 | 1 | 0 | 0 | 12 | 0 | 4 | 0 |
| `manual` | 89 | 0 | 0 | 3 | 23 | 0 | 0 | 63 | 0 | 0 | 0 |
| `-` | 4 | 0 | 0 | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| `mirror_private` | 1 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| `certified_card_proxy_abox` | 1 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| `certified_card_nominals` | 1 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| **Total** | **1,781** | **6** | **2** | **116** | **658** | **159** | **14** | **175** | **3** | **647** | **1** |

Notes on route counts vs the 60-second `checkers-on-suite` baseline:
- Under the 300-second timeout on `d0476260`, `ore_ont_15059.owl` (previously `-` due to 60 s timeout) completes `elc` in `100.195 s`, bringing `elc` to 594 inputs (the 593 inputs in `p2-recognition.tsv` plus `ore_ont_15059.owl`). Under force, `ore_ont_15059.owl`, `ore_ont_16744.owl`, and `ore_ont_8737.owl` decline in `102.4 s`--`146.4 s` with `KM_TIMING KM_REFERENCE_STAGE declined: INTERNAL PANIC: out of memory`.
- The 647 forced timeouts consist of:
  - **585** `elc` ORE inputs (all P2-recognised `EL`, timing out in `elReferenceAccept`);
  - **44** `production_all` ORE inputs that are pure EL clause streams recognised by `recognizeEL` (routed to `production_all` in unforced mode because the in-process exact-EL screen declines inputs above its byte threshold) and time out in `elReferenceAccept`;
  - **10** `production_all` ORE inputs rejected by `recognizeEL` (`disjunctive_head`) that time out in `recognizeALC` / `source.named.Nodup` before the ALC concept budget check;
  - **4** `production_all` non-ORE inputs (`g633.ofn`, `min_atleast0_gci.ofn`, `min_copy_successor_insufficient.ofn`, `datatype_union_cover.ofn`, with 9--12 total concepts) that pass the `<= 16` ALC concept budget and time out in `alcReferenceAccept`;
  - **4** `ht_rules` seed inputs (`fr133.ofn`, `fr61.ofn`, `fr65.ofn`, `fr97.ofn`) that time out in the unguarded `rules-consistency` worker before reaching `try_reference_stage`.

## 4. Timing Summary

| Subset | Count | Unforced Total (s) | Unforced Median (s) | Unforced Max (s) | Forced Total (s) | Forced Median (s) | Forced Max (s) |
|---|---:|---:|---:|---:|---:|---:|---:|
| **All inputs** | 1,781 | 9,079.0 | 0.109 | 300.190 | 195,679.1 | 0.137 | 300.188 |
| **Reference-published (`EL`)** | 6 | 0.030 | 0.006 | 0.006 | 0.568 | 0.080 | 0.168 |
| **Reference-published (`ALC`)** | 2 | 0.021 | 0.011 | 0.011 | 4.842 | 3.832 | 3.832 |
| **Unguarded production published** | 116 | 36.0 | 0.018 | 7.474 | 38.2 | 0.018 | 7.649 |
| **Declined at reference stage** | 1,009 | 5,269.6 | 0.070 | 300.190 | 1,533.4 | 0.024 | 146.393 |
| **Forced timeouts (`300 s`)** | 647 | 3,773.3 | 0.415 | 300.102 | 194,102.1 | 300.000 | 300.188 |

## 5. Check 4: Inputs Where the Unforced Run Published Nothing (17 Inputs)

| Family | Input | Unforced Route | Unforced Status | Unforced Wall (s) | Forced Outcome | Forced Wall (s) |
|---|---|---|---|---:|---|---:|
| `data` | `fresh3/m7056.ofn` | `certified_nominals` | `timeout` | 300.106 | `declined: not recognised: not in pure EL/ALC clause-stream fragment` | 0.008 |
| `fixture` | `fixtures/multi_object_constant_data_rules.ofn` | `-` | `exit2` | 0.002 | `error (exit2)` | 0.003 |
| `nominal` | `fresh2/m2296.ofn` | `certified_nominals` | `timeout` | 300.138 | `declined: not recognised: not in pure EL/ALC clause-stream fragment` | 0.010 |
| `ore` | `files/ore_ont_15203.owl` | `production_all` | `exit1` | 97.876 | `declined: not recognised: not in pure EL/ALC clause-stream fragment` | 64.920 |
| `ore` | `files/ore_ont_15803.owl` | `certified_nominals` | `exit1` | 164.640 | `declined: not recognised: not in pure EL/ALC clause-stream fragment` | 29.958 |
| `ore` | `files/ore_ont_16462.owl` | `certified_nominals` | `exit1` | 68.572 | `declined: not recognised: not in pure EL/ALC clause-stream fragment` | 12.593 |
| `ore` | `files/ore_ont_16744.owl` | `production_all` | `exit-6` | 78.065 | `declined: INTERNAL PANIC: out of memory` | 102.409 |
| `ore` | `files/ore_ont_7729.owl` | `certified_nominals` | `exit3` | 74.223 | `declined: not recognised: not in pure EL/ALC clause-stream fragment` | 13.192 |
| `ore` | `files/ore_ont_8737.owl` | `production_all` | `exit1` | 111.000 | `declined: INTERNAL PANIC: out of memory` | 117.201 |
| `ore` | `files/ore_ont_9674.owl` | `elc` | `exit-6` | 97.524 | `timeout` | 300.000 |
| `ore` | `files/ore_ont_9791.owl` | `production_all` | `timeout` | 300.190 | `declined: not recognised: not in pure EL/ALC clause-stream fragment` | 8.399 |
| `rule` | `ofn/fr133.ofn` | `ht_rules` | `timeout` | 300.102 | `timeout` | 300.100 |
| `rule` | `ofn/fr253.ofn` | `ht_rules` | `exit124` | 235.166 | `declined: not recognised: not in pure EL/ALC clause-stream fragment` | 0.012 |
| `rule` | `ofn/fr57.ofn` | `ht_rules` | `timeout` | 300.082 | `declined: out of fragment: frontend failed for reference stage` | 65.967 |
| `rule` | `ofn/fr61.ofn` | `ht_rules` | `timeout` | 300.099 | `timeout` | 300.110 |
| `rule` | `ofn/fr65.ofn` | `ht_rules` | `timeout` | 300.008 | `timeout` | 300.009 |
| `rule` | `ofn/fr97.ofn` | `ht_rules` | `timeout` | 300.079 | `timeout` | 300.066 |

## 6. Bottlenecks and Missing Switches Found

Per the task brief ("No source changes are expected; if the runner needs a switch that does not exist, report it instead of adding it"), no Rust or Lean source files were modified. The suite evaluation identified five concrete defects and bottlenecks explaining why Check 1 only publishes 6 of 592 P2-recognised inputs within `300 s`:

### 6.1 Per-Cell Recomputation of `ELReference.closure` (`2 * (|named| + 2)^2` Blowup) and Unindexed Saturation Step
- **Location**: `lean/ContextCalculus/ELReferenceSaturation.lean:752-755` (`referenceBit`) and `lean/ContextCalculus/KMConcreteWorkerAdapters.lean:1146-1168` (`referenceAnswer`, `elReferenceAccept`).
- **Root cause**: `referenceBit` binds `let c := closure top bottom named O` *inside* the function after `(sub sup : Nat)`. `matrixAnswer` calls `referenceBit` for every `(sub, sup)` pair in `named x named`, and `requestedExactAccept` (`elReferenceAccept`) calls `referenceAnswer` a second time to verify the published answer against the computed matrix. This recomputes `ELReference.closure` from scratch **`2 * (|named| + 2)^2` times** per ontology instead of once.
- **Empirical measurement**: On `ore_ont_8937.owl` (94 concepts, 262 clauses), `named=1` (`2` closure calls) takes `4.670 s`, `named=2` (`8` closure calls) takes `18.529 s` (`3.97x`), and full `named=94` (`18,432` closure calls) requires `~43,000 s`. Even on the smallest ORE `elc` ontology (`ore_ont_10309.owl`, 59 concepts, 203 clauses), one closure takes `0.086 s`, so `2 * 61^2 = 7,442` closure calls require `~640 s > 300 s`.
- **Secondary saturation cost**: On larger ORE ontologies (e.g. `ore_ont_258.owl`, 275 concepts, 271 clauses), even a single `ELReference.closure` call exceeds `30 s` because `ELReferenceSaturation.step` (`lean/ContextCalculus/ELReferenceSaturation.lean:155-205`) scans `U.flatMap` x `O.flatMap` with linear `List.mem` (`s.hasSub`, `s.hasRole`) and quadratic `List.dedup` on every round.

### 6.2 Per-Cell Recomputation and Unconditional $2^{|C|}$-Step Iteration in `ALCReferenceSaturation` plus Pre-Budget Quadratic Checks in `recognizeALC`
- **Location**: `lean/ContextCalculus/ALCReferenceSaturation.lean:146-177` (`saturateC`, `alcBit`), `lean/ContextCalculus/ALCCommonSourceRecognizer.lean:694-736` (`recognizeALC`), and `lean/KMELReferenceCheck.lean:480-517` (`runAlcStage`, `runFile`).
- **Root cause**:
  1. `alcBit` recomputes `saturateC O` for every `(A, B)` cell (`2 * |named|^2` times), and `saturateC O = (stepC O)^[(candC O).card] (candC O)` runs `(candC O).card` iterations unconditionally (up to $2^{|C|}$ steps without a fixpoint early exit), where each `stepC` is $O(|G|^2 \cdot |O|)$. Consequently, ALC inputs with 5--6 concepts finish in `1.0 s`--`3.8 s`, whereas the 4 ALC fixtures/seeds with 9--12 concepts (`min_atleast0_gci.ofn`, `datatype_union_cover.ofn`, `g633.ofn`, `min_copy_successor_insufficient.ofn`) exceed `300 s`.
  2. `KMELReferenceCheck.lean:515` checks `if !source.named.Nodup` using `List.Nodup` ($O(|\text{named}|^2)$), and `runAlcStage` checks `recognized.conceptCount > maxConcepts` (default 16) *after* `recognizeALC` runs `ALCOntologyVariant` ($2 \times |O|^2$ pairwise clause equivalence checks). On 10 large non-EL ORE ontologies whose clauses all match ALC shapes, `recognizeALC` times out at `300 s` before reaching the `maxConcepts = 16` budget check.

### 6.3 Incomplete `KM_REFERENCE_FORCE=1` Guards in `classify_with_evidence_inner`
- **Location**: `engine/src/orchestrate/mod.rs:2067-3455`.
- **Root cause**: `reference_force_enabled()` only guards `run_atomic_mechanism` (line 909), the `None` portfolio branch of `atomic_out` (line 3455), `flat_nf1::try_classify` (line 2326), and `mirror::try_classify` (line 2353). It does not guard:
  1. `cfg.ht_rules` / `rules_consistency` (lines 3203--3309): **88 inputs** publish and **4 inputs** time out here under `KM_REFERENCE_FORCE=1` without reaching `try_reference_stage`.
  2. `meta.abox_inconsistent` (line 3083): **25 inputs** (including `engine/tests/fixtures/realization/inconsistent.ofn`, one of the 592 P2-recognised inputs) publish `CONSISTENT 0` here without reaching `try_reference_stage`. In addition, if `realization/inconsistent.ofn` reached `try_reference_stage`, line 4049 (`if meta.abox_inconsistent`) would decline it because its inconsistency comes from `meta.abox_inconsistent` rather than the TBox clause stream.
  3. `meta.profile.finite_rule_class_projection` (lines 2405--2428): **2 inputs** (`fr213.ofn`, `fr301.ofn`) publish here.
  4. `symbolic_source::automatic_candidate` / `positive_abox_quotient::try_build` (lines 2067--2128): **1 input** (`ore_ont_5107.owl`) publishes here.
  5. `meta.profile.positive_el_abox_materializable` (lines 3107--3182, feeding `certified_el_out` at line 3386 before `run_atomic_mechanism`).

### 6.4 Missing Procedure Name (`EL` vs `ALC`) on `KM_TIMING KM_REFERENCE_STAGE published`
- **Location**: `engine/src/orchestrate/mod.rs:4169` and `lean/KMELReferenceCheck.lean:402-417`.
- **Root cause**: `km-el-reference` emits only `{"named": [...], "cells": [...]}` on stdout without a `"procedure": "EL" | "ALC"` field, and `try_reference_stage` logs `eprintln!("KM_TIMING KM_REFERENCE_STAGE published")` without indicating which procedure (`EL` or `ALC`) produced the publication. Our runner (`tools/run_p3_suite.py`) determines `EL` vs `ALC` on published runs via `km-el-reference --recognize-only --procedure el` and `--procedure alc`.

### 6.5 Direct `std::process::Command` Spawn in `try_reference_stage` Instead of `CheckerCommand`
- **Location**: `engine/src/orchestrate/mod.rs:4096-4100`.
- **Root cause**: Unlike all other Lean checker call sites in `engine/` (which use `crate::lean_checkers::CheckerCommand`), `try_reference_stage` spawns `km-el-reference` directly via `std::process::Command::new(&checker_path)`. Consequently, it omits `PR_SET_PDEATHSIG = SIGKILL` (leaving orphaned `km-el-reference` processes if `km classify` is killed by an external non-group timeout), omits `LEAN_STACK_SIZE_KB=262144` (risking either `failed to create thread` under strict overcommit when default 1 GiB stacks are reserved or stack overflow if a smaller stack is used), and omits the `startup_thread_failure` retry loop.
