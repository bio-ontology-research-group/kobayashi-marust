# v161-stack: no stack overflow in the reference stage on large inputs

Branch `v161/stack` (worktree `/mnt/data1/leechuck/km-work/wt/v161-stack`), from
`development/v1.6.1` (50fa0e31, with the v161-sparse answer).

## What changed

- **Lean, `ContextCalculus/ELCommonSourceRecognizer.lean`.** Eight list functions on the
  recognition path recursed once per clause or item without a tail call. Each got a
  tail-recursive twin and an `@[csimp]` equation placed right after it (before its first
  caller, so the compiled `recognizeItems`/`recognizeEL` use the twin):

  | function | twin | how |
  |---|---|---|
  | `parseSource` | `parseSourceTR` | `Array` accumulator, early `none` |
  | `maxNatList` | `maxNatListTR` | `foldl max 0` |
  | `compileDirect` | `compileDirectTR` | per-item `compileItem` (clauses + new `seenTop`), `Array` accumulator |
  | `collectRoleHalves` | `collectRoleHalvesTR` | `filterMap roleHalfOf` (core `filterMapTR`) |
  | `collectFillerHalves` | `collectFillerHalvesTR` | `filterMap fillerHalfOf` |
  | `mergeHalvesFuel` | `mergeHalvesFuelTR` | `Array` accumulator (used by `sortHalves`) |
  | `mergePairs` | `mergePairsTR` | `Array` accumulator (used by `sortHalves`) |
  | `zipSortedHalves` | `zipSortedHalvesTR` | `Array` accumulator |

- **Lean, `ContextCalculus/ALCCommonSourceRecognizer.lean`.** Same treatment for `listMax`
  (`foldl`), `buildIndexedClauses` (per-item `indexItem`, `Array` accumulator) and
  `assignFnNames` (`Array` accumulator). The ALC recogniser stays quadratic in the clause count
  (`decide` of `List.Nodup` on the Skolem halves and of `ALCOntologyVariant`), so on large
  sources it is bound by time, not stack; the binary's 16-concept budget also stops large ALC
  inputs before `recognizeALC`.
- No existing definition or theorem statement changed; every fix is a `@[csimp]` twin (none
  needed a direct rewrite). Both module docstrings say so.
- **Binary `lean/KMELReferenceCheck.lean`.** `KM_REFERENCE_TIMING=1` prints
  `KM_REFERENCE_TIMING phase=<name> ms=<ms>` to stderr per phase: `read`, `json`, `source`,
  `recognise`, `closure`, `readout`, `output`, `total` (ALC: `alc-precheck`, `alc-recognise`,
  `alc-reference`). The EL stage runs as `runElPhases`: `recognizeEL`, then
  `ELReference.closure`, then `sparseAnswerOfClosure` (the body of
  `SparseTaxonomy.sparseReferenceAnswer` with the closure passed in;
  `sparseAnswerOfClosure_closure` is `rfl`), each evaluated through a `@[noinline]` `evalNow`
  that returns the value with its defining equation. The proof `sparseElReference source = some t`
  is rebuilt from those equations and passed to `sparseElReference_correct`, so `publishSparse`
  still takes `RequestedCorrect source t.dense`. Output bytes are unchanged (checked below).
- **Rust `engine/src/orchestrate/mod.rs`.** With `KM_TIMING` set, `try_reference_stage` repeats
  the checker's `KM_REFERENCE_TIMING` lines as `KM_TIMING KM_REFERENCE_TIMING ...` (also after a
  budget kill, since the partial stderr is collected).
- **`lean/run-routing-certification-gate.sh`.** The axiom audit lists the eleven csimp theorems.
- Stack size: KM starts every checker through `lean_checkers::CheckerCommand`, which sets
  `LEAN_STACK_SIZE_KB=262144` (256 MiB) unless the caller set it. All runs below use 262144.

## Theorems (all `@[csimp]`, statements `@foo = @fooTR`)

```lean
theorem ELCommonSourceRecognizer.parseSource_eq_parseSourceTR : @parseSource = @parseSourceTR
theorem ELCommonSourceRecognizer.maxNatList_eq_maxNatListTR : @maxNatList = @maxNatListTR
theorem ELCommonSourceRecognizer.compileDirect_eq_compileDirectTR : @compileDirect = @compileDirectTR
theorem ELCommonSourceRecognizer.collectRoleHalves_eq_collectRoleHalvesTR : @collectRoleHalves = @collectRoleHalvesTR
theorem ELCommonSourceRecognizer.collectFillerHalves_eq_collectFillerHalvesTR : @collectFillerHalves = @collectFillerHalvesTR
theorem ELCommonSourceRecognizer.mergeHalvesFuel_eq_mergeHalvesFuelTR : @mergeHalvesFuel = @mergeHalvesFuelTR
theorem ELCommonSourceRecognizer.mergePairs_eq_mergePairsTR : @mergePairs = @mergePairsTR
theorem ELCommonSourceRecognizer.zipSortedHalves_eq_zipSortedHalvesTR : @zipSortedHalves = @zipSortedHalvesTR
theorem ALCCommonSourceRecognizer.listMax_eq_listMaxTR : @listMax = @listMaxTR
theorem ALCCommonSourceRecognizer.buildIndexedClauses_eq_buildIndexedClausesTR : @buildIndexedClauses = @buildIndexedClausesTR
theorem ALCCommonSourceRecognizer.assignFnNames_eq_assignFnNamesTR : @assignFnNames = @assignFnNamesTR
```

Binary-local: `KMELReferenceCheck.sparseAnswerOfClosure_closure` (`rfl`).

`#print axioms` (from the build log):

```
'ContextCalculus.ELCommonSourceRecognizer.parseSource_eq_parseSourceTR' depends on axioms: [propext, Quot.sound]
'ContextCalculus.ELCommonSourceRecognizer.maxNatList_eq_maxNatListTR' depends on axioms: [propext, Quot.sound]
'ContextCalculus.ELCommonSourceRecognizer.compileDirect_eq_compileDirectTR' depends on axioms: [propext, Quot.sound]
'ContextCalculus.ELCommonSourceRecognizer.collectRoleHalves_eq_collectRoleHalvesTR' depends on axioms: [propext, Quot.sound]
'ContextCalculus.ELCommonSourceRecognizer.collectFillerHalves_eq_collectFillerHalvesTR' depends on axioms: [propext, Quot.sound]
'ContextCalculus.ELCommonSourceRecognizer.mergeHalvesFuel_eq_mergeHalvesFuelTR' depends on axioms: [propext, Quot.sound]
'ContextCalculus.ELCommonSourceRecognizer.mergePairs_eq_mergePairsTR' depends on axioms: [propext, Quot.sound]
'ContextCalculus.ELCommonSourceRecognizer.zipSortedHalves_eq_zipSortedHalvesTR' depends on axioms: [propext, Quot.sound]
'ContextCalculus.ALCCommonSourceRecognizer.listMax_eq_listMaxTR' depends on axioms: [propext, Quot.sound]
'ContextCalculus.ALCCommonSourceRecognizer.buildIndexedClauses_eq_buildIndexedClausesTR' depends on axioms: [propext, Quot.sound]
'ContextCalculus.ALCCommonSourceRecognizer.assignFnNames_eq_assignFnNamesTR' depends on axioms: [propext, Quot.sound]
```

Whole build log: 1963 `depends on axioms` lists, union `{propext, Classical.choice, Quot.sound}`,
0 `sorryAx`; the v1.6.0 capstone `kmSupervisor_complete_on_EL_or_ALC` and the v161-sparse
theorems report the same axioms as before. No `sorry`, `native_decide`, new axiom or option change.

## Build and test

| command | result |
|---|---|
| `cd lean && LEAN_NUM_THREADS=2 nice lake build ContextCalculus ContextCalculus.KMSupervisorInstance ContextCalculus.SparseTaxonomy km-el-reference` | Build completed successfully (12186 jobs), 0 `sorryAx` |
| `cd engine && CARGO_TARGET_DIR=$PWD/target CARGO_BUILD_JOBS=2 cargo build --release --bin km` | ok |
| `KM_EL_TEST_REFERENCE_CHECKER=../lean/.lake/build/bin/km-el-reference cargo test --release --test reference_stage -- --test-threads=1` | 17 passed, 0 failed |

## Stack checks (256 MiB, `LEAN_STACK_SIZE_KB=262144`)

Diagnostic executable `tools/KMStackDiag.lean` (built from a temporary lakefile entry, not
committed), each function on synthetic lists of 10 M items, v161-sparse code (baseline) against
this branch (data: `data/baseline-10M.txt`, `data/fixed-10M.txt`, `data/pipeline-10M.txt`):

| function (10 M items) | baseline | this branch |
|---|---|---|
| `maxNatList`, `parseSource`, `compileDirect`, `sortHalves`, `mergeHalves`, `zipSortedHalves`, `buildNF3Clauses` | stack overflow | ok |
| `collectRoleHalves`/`collectFillerHalves` (all items matching) | overflow 3 to 4 M (v161-sparse) | ok |
| `itemsConcepts` (`flatMap`, core csimp) | ok | ok |
| ALC `listMax`, `assignFnNames`, `buildIndexedClauses` | stack overflow | ok |
| ALC `classifyClause` via `mapM`, `sourceConcepts` | ok | ok |
| `recognizeEL` on a 10 M-clause synthetic `List FCL` (every EL shape) | stack overflow | ok (11 M NF clauses, 10.6 s) |

Synthetic clause stream through the binary (`tools/gen_synth_clauses.py`, every recognised EL
shape in a ten-cycle, concepts modulo k blocks):

| input | binary | outcome |
|---|---|---|
| 10 M clauses (2.27 GB JSON), `--recognize-only --procedure el` | v161-sparse | `Stack overflow detected`, 130.6 s |
| same | this branch | `recognised`, 124.0 s, 33.3 GB peak RSS (read 7.9 s, JSON 52.8 s, source 52.7 s, recognise 8.1 s) |
| same, full `--procedure el-then-alc` | this branch | past recognition (8.2 s), killed by `timeout 300` in the closure, no overflow |
| 1.8 M clauses, k = 20 000, full | v161-sparse and this branch | identical output (md5 `10610c2d…`); closure 73.9 s of 92.3 s |
| 4 M clauses, k = 40 000, full | this branch | past recognition, `timeout 300` in the closure |

## Measurement: the three inputs that overflowed in v161-sparse

`tools/measure.py` (v161-sparse's driver plus `KM_REFERENCE_TIMING=1`), `KM_REFERENCE_FORCE=1
KM_THREADS=1 KM_TIMING=1 timeout 300`, this branch's `km` and `km-el-reference`, 256 MiB stack,
two at a time. Digest against the unforced digest of the v1.6.0 P3 rerun (production routes are
unchanged). Data: `data/forced-256mib.tsv`, `data/r16744-budget200.txt`.

| input | MB | status | wall s | peak RSS GB | published | digest | v161-sparse (256 MiB) |
|---|---|---|---|---|---|---|---|
| ore_ont_16744.owl | 576 | timeout | 300.2 | 4.9 | no | - (unforced timed out too) | stack overflow |
| ore_ont_15059.owl | 576 | ok | 249.3 | 9.2 | yes | match | stack overflow |
| ore_ont_1559.owl | 393 | ok | 251.0 | 7.9 | yes | match | stack overflow |

ore_ont_16744 under the outer 300 s kills `km` before the checker reports. With
`KM_REFERENCE_BUDGET_S=200` (one extra run): frontend 38.8 s, checker read 4.1 s, JSON 27.4 s,
source 25.8 s, recognise 5.0 s, then the closure runs past the 200 s budget (`declined: budget`),
298.9 s total, 16.7 GB peak. No overflow; it is closure-bound.

### Phase timing of the checker on ore_ont_1559 (forced run above)

| phase | ms | share of checker |
|---|---|---|
| read | 1,901 | 1.2 % |
| JSON parse | 11,482 | 7.4 % |
| source parse (JSON to `FCL`) | 8,946 | 5.7 % |
| recognition | 1,825 | 1.2 % |
| closure | 125,764 | 80.6 % |
| sparse readout | 4,899 | 3.1 % |
| output | 602 | 0.4 % |
| total | 156,075 | |

KM spends 27.0 s before the stage (frontend), the checker 156.1 s, the rest of the 251 s is the
stage's JSON write and KM's own work around it. ore_ont_15059: closure 100.7 s of 133.0 s
(76 %). The closure dominates the checker on all three large inputs, so inputs that hit the
300 s budget are most likely closure-bound; the full 116-input split needs the forced suite
rerun with `KM_REFERENCE_TIMING=1` (Ibex).

## Open

- ore_ont_16744 still does not publish within 300 s (closure).
- The closure itself was not optimised (out of scope). On the synthetic streams it grows faster
  than linearly with duplicated clauses (1.8 M clauses: 74 s; 4 M: over 270 s).
- The ALC recogniser is quadratic; the stack fixes there matter only for inputs that pass the
  16-concept budget.
- Full routing gate script and the 116-input suite rerun were not run (Ibex).
