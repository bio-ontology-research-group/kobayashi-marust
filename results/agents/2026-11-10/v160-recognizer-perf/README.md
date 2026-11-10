# v1.6.0 Near-Linear `nf3` Pairing in `ELCommonSourceRecognizer`

## Overview

In the prior P2 measurement (`results/agents/2026-11-10/v160-nary-conjunction/p2-recognition.tsv`), `km-el-reference --recognize-only` timed out at 300 s (`exit 124`) on three ORE 2015 inputs (`ore_ont_11395.owl`, `ore_ont_14042.owl`, `ore_ont_1559.owl`: 1.33M to 2.93M clauses, 150,890 to 225,283 `nf3` role and filler halves) and took 139.76 s on `ore_ont_13224.owl` (439,500 clauses, 82,828 `nf3` role and filler halves). The bottleneck was `ELCommonSourceRecognizer.buildNF3Clauses`, which used $O(M^2)$ list operations (`List.Nodup` on `roles.map Prod.fst` and `fillers.map Prod.fst`, `roles.all (halfMatches fillers)`, `fillers.all (halfMatches roles)`, and `roles.filterMap` with linear `lookupHalf`).

We replaced the quadratic pairing in `buildNF3Clauses` (commit `eada9c82`) with an executable $O(M \log M)$ bottom-up merge sort on function identifiers (`sortHalves`) followed by a single $O(M)$ tail-recursive validation pass (`validSortedHalves`) and linear zip (`zipSortedHalves`). All public theorem statements (`recognizeEL_entails_iff`, `recognizeEL_unsat_iff`, `kmSupervisor_complete_on_EL_or_ALC`) and the specification lemmas (`buildNF3Clauses_role_mem`, `buildNF3Clauses_filler_mem`, `buildNF3Clauses_clause_mem`) remain unchanged.

## Formalisation Details

- **Bottom-up merge sort (`sortHalves`)**: `mergeHalvesFuel`, `mergeHalves`, `mergePairs`, `mergeAllRuns`, and `sortHalves` sort `List (Nat × Nat × Nat)` by function identifier `Prod.fst` using structural recursion on fuel. `sortHalves_perm` proves `(sortHalves xs).Perm xs`.
- **Single-pass validation and pairing (`validSortedHalves`, `zipSortedHalves`)**: `validSortedHalves prevF sRoles sFillers` verifies in one pass that `sRoles` and `sFillers` have the same length, strictly increasing function identifiers (`prevF < f`), and matching `(f, a)` pairs at every position. `zipSortedHalves` pairs matching `(f, a, r)` and `(f, a, b)` entries into `.nf3 a r b` clauses in $O(M)$ time.
- **Preserved interface lemmas**: Using `sortHalves_perm` together with `validSortedHalves_roles_nodup`, `validSortedHalves_fillers_nodup`, `validSortedHalves_role_mem`, `validSortedHalves_filler_mem`, and `validSortedHalves_clause_mem`, the existing specification theorems `buildNF3Clauses_role_mem`, `buildNF3Clauses_filler_mem`, and `buildNF3Clauses_clause_mem` keep their exact statements, leaving all downstream proofs in `ELCommonSourceRecognizer.lean` untouched.

## Exact Theorem Statements

Unchanged public recogniser and supervisor theorems:

```lean
theorem recognizeEL_entails_iff (named : List Nat) (source : List FCL)
    (recognized : RecognizedEL)
    (hrecognized : recognizeEL named source = some recognized)
    {sub sup : Nat} (hsub : sub ∈ named) (hsup : sup ∈ named) :
    Entails source sub sup ↔
      ELCompletion.EntailsSub (top := recognized.top) (bottom := recognized.bottom)
        recognized.ontology sub sup

theorem recognizeEL_unsat_iff (named : List Nat) (source : List FCL)
    (recognized : RecognizedEL)
    (hrecognized : recognizeEL named source = some recognized) :
    (∀ (Domain : Type) [Nonempty Domain] (model : TModel Domain),
        (∀ clause ∈ source, valid model clause) → False) ↔
      ELCompletion.Unsatisfiable (top := recognized.top)
        (bottom := recognized.bottom) recognized.ontology

theorem kmSupervisor_complete_on_EL_or_ALC
    (rust : Route → KMRequestedExecution) (decide : RoutingSource → Decision) :
    CompleteOn RequestedCorrect (fun source => ELFragment source ∨ ALCFragment source)
      (kmSupervisor rust decide).run
```

Unchanged `buildNF3Clauses` specification lemmas and new merge-sort helper theorems in `lean/ContextCalculus/ELCommonSourceRecognizer.lean`:

```lean
theorem sortHalves_perm (xs : List (Nat × Nat × Nat)) :
    (sortHalves xs).Perm xs

theorem validSortedHalves_roles_nodup {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true) :
    (rs.map Prod.fst).Nodup

theorem validSortedHalves_fillers_nodup {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true) :
    (fs.map Prod.fst).Nodup

theorem validSortedHalves_role_mem {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true)
    {f a r : Nat} (hmem : (f, a, r) ∈ rs) :
    ∃ b, (f, a, b) ∈ fs ∧ .nf3 a r b ∈ zipSortedHalves rs fs

theorem validSortedHalves_filler_mem {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true)
    {f a b : Nat} (hmem : (f, a, b) ∈ fs) :
    ∃ r, (f, a, r) ∈ rs ∧ .nf3 a r b ∈ zipSortedHalves rs fs

theorem validSortedHalves_clause_mem {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true)
    {cl : ELCompletion.Clause Nat Nat} (hcl : cl ∈ zipSortedHalves rs fs) :
    ∃ f a r b, cl = .nf3 a r b ∧ (f, a, r) ∈ rs ∧ (f, a, b) ∈ fs

theorem buildNF3Clauses_role_mem {roles fillers : List (Nat × Nat × Nat)}
    {nf3Clauses : List (ELCompletion.Clause Nat Nat)}
    (hbuild : buildNF3Clauses roles fillers = some nf3Clauses)
    {f a r : Nat} (hmem : (f, a, r) ∈ roles) :
    lookupHalf f roles = some (a, r) ∧
      ∃ b, lookupHalf f fillers = some (a, b) ∧ .nf3 a r b ∈ nf3Clauses

theorem buildNF3Clauses_filler_mem {roles fillers : List (Nat × Nat × Nat)}
    {nf3Clauses : List (ELCompletion.Clause Nat Nat)}
    (hbuild : buildNF3Clauses roles fillers = some nf3Clauses)
    {f a b : Nat} (hmem : (f, a, b) ∈ fillers) :
    lookupHalf f fillers = some (a, b) ∧
      ∃ r, lookupHalf f roles = some (a, r) ∧ .nf3 a r b ∈ nf3Clauses

theorem buildNF3Clauses_clause_mem {roles fillers : List (Nat × Nat × Nat)}
    {nf3Clauses : List (ELCompletion.Clause Nat Nat)}
    (hbuild : buildNF3Clauses roles fillers = some nf3Clauses)
    {cl : ELCompletion.Clause Nat Nat} (hcl : cl ∈ nf3Clauses) :
    ∃ f a r b, cl = .nf3 a r b ∧ (f, a, r) ∈ roles ∧ (f, a, b) ∈ fillers
```

## Build Command and Axiom Verification

Command:
```bash
LEAN_NUM_THREADS=2 nice lake build \
  ContextCalculus.KMSupervisorInstance \
  ContextCalculus.ELCommonSourceRecognizerTests \
  km-el-reference
```

Copied `#print axioms` lines from the build log:
```text
info: ContextCalculus/ELCommonSourceRecognizer.lean:2164:0: 'ContextCalculus.ELCommonSourceRecognizer.recognizeEL_entails_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: ContextCalculus/ELCommonSourceRecognizer.lean:2165:0: 'ContextCalculus.ELCommonSourceRecognizer.recognizeEL_unsat_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: ContextCalculus/KMSupervisorInstance.lean:136:0: 'ContextCalculus.KMSupervisorInstance.kmSupervisor_complete_on_EL_or_ALC' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All executable unit tests in `ContextCalculus.ELCommonSourceRecognizerTests` pass during the build.

## Before/After Wall-Clock Times on the Four Saved Dumps

Timed with `/usr/bin/time -v timeout 300 taskset -c 0,1 ./lean/.lake/build/bin/km-el-reference --recognize-only <clauses.json>` on the four saved dumps in `.work/agent-scratch/v160-recognizer-perf/dumps/`:

| Input | `clauses.json` Size | Total Clauses | `nf3` Role/Filler Pairs | Before (`--recognize-only`) | After (`--recognize-only` standalone) | After (User / Sys / Max RSS) | After (in P2 sweep: `dump_s` / `rec_s` / `wall_s`) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `ore_ont_13224.owl` | 93.50 MB | 439,500 | 82,828 | 139.76 s (`recognised`) | **5.42 s** (`recognised`) | 4.03 s / 1.11 s / 1.38 GB | 7.53 s / **4.97 s** / 12.49 s |
| `ore_ont_11395.owl` | 282.95 MB | 1,331,669 | 150,890 | > 300.16 s (`exit 124` timeout) | **18.06 s** (`recognised`) | 12.68 s / 4.00 s / 3.96 GB | 39.96 s / **16.20 s** / 56.17 s |
| `ore_ont_14042.owl` | 282.95 MB | 1,331,669 | 150,890 | > 300.07 s (`exit 124` timeout) | **16.53 s** (`recognised`) | 12.60 s / 3.20 s / 3.96 GB | 39.52 s / **16.82 s** / 56.34 s |
| `ore_ont_1559.owl` | 536.76 MB | 2,925,744 | 225,283 | > 300.15 s (`exit 124` timeout) | **31.46 s** (`recognised`) | 23.66 s / 6.22 s / 7.68 GB | 78.99 s / **32.22 s** / 111.21 s |

### Remaining Cost Analysis

`km-el-reference` (`lean/KMELReferenceCheck.lean`) accepts only `<clauses.json>` and `--recognize-only <clauses.json>`; it does not provide a separate `--parse-only` CLI flag. After replacing the quadratic `nf3` pairing pass with `sortHalves` and `validSortedHalves`, total `--recognize-only` wall time scales linearly with the input JSON file size at 58 to 64 ms per MB across all four large dumps (5.42 s for 93.50 MB, 18.06 s and 16.53 s for 282.95 MB, and 31.46 s for 536.76 MB) and max RSS scales at roughly 14.3 to 14.8 MB per MB of JSON text. This linear cost and resident memory footprint come from `IO.FS.readFile`, `Lean.Json.parse`, and `KMELReferenceCheck.parseSource` (which constructs the `Lean.Json` AST and interns terms/atoms into `FCL` clauses before calling `recognizeEL`). Because all inputs now finish well under the 300 s limit (maximum `rec_s` is 32.22 s across the entire 593-input suite), we left `KMELReferenceCheck.lean` unchanged as instructed.

## Updated P2 Recognition Table (593 `elc`-routed inputs)

Per-input results are recorded in `results/agents/2026-11-10/v160-recognizer-perf/p2-recognition.tsv`.

| Outcome / Rejection Reason | Initial Count (v160-reference-binary) | Prior Count (v160-nary-conjunction) | New Count | New Share (%) | Example Input | Notes |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| **Accepted (`recognised`)** | 475 | 589 | **592** | **99.83%** | `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_1559.owl` | `ELCommonSourceRecognizer.recognizeEL` returns `some` (`exit 0`); all 3 prior timeouts now pass in 16.2–32.2 s |
| **Rejected (total)** | 118 | 4 | **1** | **0.17%** | | |
| `not recognised: nary_concept_conjunction` | 114 | 0 | **0** | **0.00%** | `-` | Eliminated in `v160-nary-conjunction` |
| `exit 124` (300 s recogniser timeout) | 3 | 3 | **0** | **0.00%** | `-` | Eliminated (`11395`: 16.20 s, `14042`: 16.82 s, `1559`: 32.22 s) |
| `not recognised: individual_or_constant_term` | 1 | 1 | **1** | **0.17%** | `engine/tests/fixtures/finite_rule_taxonomy.ofn` | Clause 11 has grounded DL-safe rule constants before `finite_rule_class_projection` rewrites to a TBox-only ontology for `elc` |
| **Total `elc`-routed inputs** | **593** | **593** | **593** | **100.00%** | | |

### Breakdown by Family and Timing Summary

- **ORE 2015 (`ore`, 585 inputs)**: **585 accepted (100.00%)**, 0 rejected.
- **Fixtures (`fixture`, 8 inputs)**: **7 accepted (87.50%)**, 1 rejected (`finite_rule_taxonomy.ofn`, `individual_or_constant_term`).
- **Cumulative recogniser time (`rec_s`) across all 593 inputs**: reduced from **1,949.29 s** to **479.87 s** (median `rec_s` 0.166 s, maximum `rec_s` 32.219 s on `ore_ont_1559.owl`).

## What Remains Open

- None for `ELCommonSourceRecognizer` performance on ORE 2015: all 585 ORE `elc`-routed inputs are now recognised within 33 s (`rec_s`).
- The single remaining rejected `elc`-routed input in the 593-input suite is the synthetic fixture `engine/tests/fixtures/finite_rule_taxonomy.ofn` (`not recognised: individual_or_constant_term`), where `clauses.json` is dumped before `finite_rule_class_projection`.
