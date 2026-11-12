# v161-sparse: sparse answer type for the reference stage

Branch `v161/sparse` (worktree `/mnt/data1/leechuck/km-work/wt/v161-sparse`), from
`development/v1.6.1` (e8a35491).

## What changed

- **Lean, new module `lean/ContextCalculus/SparseTaxonomy.lean`.** `SparseRow`,
  `SparseTaxonomy`, `SparseRow.bit`, `SparseTaxonomy.dense`, `ofMatrix`,
  `sparseReferenceAnswer`, `sparseElReference`, `sparseAlcReference` with the names and
  shapes of the brief. Helpers: `superIndexStep`/`superIndex` (one `foldl` over the closure's
  `subs` into a `Std.TreeMap Nat (List Nat)` keyed by subject, keeping only requested
  superclasses, tested with a `TreeSet` of the requested names: `O((|subs| + |named|) log)`),
  and `sparseRowOf` (`unsat := c.hasSub sub bottom`; unsatisfiable rows carry `sups := []`).
  `ofMatrix` rows have `unsat := false` and `sups := named.filter (f sub)` (ALC; the Rust caller
  reads unsatisfiability from the bottom-probe bit). Registered in `lean/ContextCalculus.lean`
  and in `lean/run-routing-certification-gate.sh` (build list and `#print axioms` audit next to
  the v1.6.0 reference theorems). No v1.6.0 file changed except the import list; the capstone
  `KMSupervisorInstance` builds unchanged. `closure_wf` is private in `ELReferenceSaturation`, so
  instead of making it public the key lemma derives the needed membership facts from the public
  `referenceBit_exact_of_named`, `closure_closedOn`, `closure_sound` and
  `ELCompletion.entails_iff_materialized_on` (saturation file untouched).
- **Binary `lean/KMELReferenceCheck.lean`.** `--procedure el|alc|el-then-alc` run
  `sparseElReference`/`sparseAlcReference` (same order, ALC precheck and budget, exit codes 0/3)
  and stream `{"format":"sparse-v1","named":[...],"procedure":"el","rows":[{"sub":..,"unsat":..,"sups":[..]},...]}`
  in chunks of 4096 items; no dense list, no whole output string. `publishSparse` takes
  `RequestedCorrect source t.dense` (from `sparseElReference_correct`/`sparseAlcReference_correct`).
  The module docstring says why the v1.6.0 `requestedExactAccept` recheck is gone. Error
  reporting: only the input read prints `failed to read <path>: ...` (exit 2); JSON/input errors
  keep exit 2 with their own messages; any later IO error prints `io error: <err>` and exits 4
  (checked: `> /dev/full` gives `io error: resource exhausted ... no space left on device`, exit 4).
  `--recognize-only` unchanged.
- **Rust `engine/src/orchestrate/mod.rs`.** `interpret_reference_stage_output` accepts only
  `format == "sparse-v1"` (a v1.6.0 dense answer fails to parse: fail closed), checks
  `named == request`, `rows.len() == named.len()`, `rows[i].sub == named[i]`, every `sup`
  requested; builds one `HashSet<usize>` per row; `inconsistent = bit(probe_a, probe_b)`;
  `u` unsatisfiable iff `bit(u, probe_b)` (published as `owl:Nothing` only); satisfiable rows
  get every `sup != sub`, not a probe, in request order (as v1.6.0). No N x N structure.
  `reference_checker_failure_reason`: first non-empty stderr line, else stdout's, cut to 200
  characters, plus the exit status.
- **Tests.** `engine/tests/reference_stage.rs` 12 -> 17 tests: TBox-inconsistent fixture
  (`el_tbox_inconsistent.ofn`, new) against the unforced answer; fake-checker tests (POSIX sh
  scripts written to `CARGO_TARGET_TMPDIR`) for rows out of order, an unknown `sup`, a v1.6.0
  dense answer, and a non-zero exit with both stdout and stderr (the stderr line is reported).
  Lib unit tests `orchestrate::reference_stage_tests` (8): the v1.6.0 dense derivation kept as an
  oracle and compared with the sparse derivation on satisfiable, unsatisfiable-class and
  inconsistent answers; format, shape, named and unknown-sup rejections; the failure reason.
  The ontology fixtures are OWL files and needed no format change.

Finding while testing: on an inconsistent TBox the production routes list every class as
unsatisfiable, while the reference stage (v1.6.0 dense and v1.6.1 sparse alike; the unit oracle
shows the derivations agree) prints none. The suite digest already maps every inconsistent answer
to `[false,[],[]]`; the integration test's `normalised` now does the same.

## Theorems (all in `ContextCalculus.SparseTaxonomy`, statements as in the brief)

```lean
theorem sparseReferenceAnswer_dense
    (recognized : ELCommonSourceRecognizer.RecognizedEL) (named : List Nat) :
    (sparseReferenceAnswer recognized named).dense =
      referenceAnswer recognized named
theorem ofMatrix_dense (named : List Nat) (f : Nat → Nat → Bool) :
    (ofMatrix named f).dense = matrixAnswer named f
theorem sparseElReference_agrees (source : RequestedTaxonomySource)
    (t : SparseTaxonomy) (h : sparseElReference source = some t) :
    elReferenceExecution.run source =
      .publish { source, answer := t.dense, evidence := .elReference ⟨1⟩ }
theorem sparseAlcReference_agrees (source : RequestedTaxonomySource)
    (t : SparseTaxonomy) (h : sparseAlcReference source = some t) :
    ∃ evidence, alcReferenceExecution.run source =
      .publish { source, answer := t.dense, evidence }
theorem sparseElReference_correct (source : RequestedTaxonomySource)
    (t : SparseTaxonomy) (h : sparseElReference source = some t) :
    RequestedCorrect source t.dense
theorem sparseAlcReference_correct (source : RequestedTaxonomySource)
    (t : SparseTaxonomy) (h : sparseAlcReference source = some t) :
    RequestedCorrect source t.dense
theorem sparseElReference_complete (source : RequestedTaxonomySource)
    (hrecognized : (ELCommonSourceRecognizer.recognizeEL source.named
      source.ontology).isSome = true)
    (hnodup : source.named.Nodup) :
    (sparseElReference source).isSome = true
```

Extra: `sparseAlcReference_agrees_exact` (evidence is `.alcReference ⟨1⟩`),
`sparseAlcReference_complete` (ALC totality, same shape as the EL one), `mem_superIndex`,
`sparseRowOf_bit`. No `sorry`, no `native_decide`, no new axioms, no option changes except
`set_option linter.dupNamespace false` (the brief fixes both the namespace and the structure name
`SparseTaxonomy`; documented in the file).

`#print axioms` (from `lake build`, log line by line):

```
'ContextCalculus.SparseTaxonomy.ofMatrix_dense' depends on axioms: [propext, Quot.sound]
'ContextCalculus.SparseTaxonomy.mem_superIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.SparseTaxonomy.sparseRowOf_bit' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.SparseTaxonomy.sparseReferenceAnswer_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.SparseTaxonomy.sparseElReference_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.SparseTaxonomy.sparseAlcReference_agrees_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.SparseTaxonomy.sparseAlcReference_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.SparseTaxonomy.sparseElReference_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.SparseTaxonomy.sparseAlcReference_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.SparseTaxonomy.sparseElReference_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.SparseTaxonomy.sparseAlcReference_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build and test

| command (from the worktree) | result |
|---|---|
| `cd lean && LEAN_NUM_THREADS=2 nice lake build ContextCalculus ContextCalculus.KMSupervisorInstance ContextCalculus.SparseTaxonomy km-el-reference` | Build completed successfully (12186 jobs), 0 `sorryAx` |
| `cd engine && CARGO_TARGET_DIR=$PWD/target CARGO_BUILD_JOBS=2 cargo build --release --bin km` | ok (bin name is `km`) |
| `KM_EL_TEST_REFERENCE_CHECKER=../lean/.lake/build/bin/km-el-reference cargo test --release --test reference_stage -- --test-threads=1` | 17 passed, 0 failed |
| `cargo test --release --lib orchestrate -- --test-threads=1` | 328 passed, 0 failed, 1 ignored |
| dense (v1.6.0 binary) vs sparse bit-by-bit, `tools/cmp_dense_sparse.py`, `lean/testdata/{el,alc}-reference-valid.json` x `--procedure el-then-alc|alc` | 4/4 equal |

The full routing gate script was not run (it builds and tests far more than this task; Ibex runs
it).

## Measurement (Part D)

Inputs: the 155 rows of `results/agents/2026-11-10/v160-p3-rerun/data/p3-results.tsv` whose forced
outcome is `INTERNAL PANIC: out of memory` (135) or `alc budget` (20), sorted by file size, the
20 largest run (all 20 are ORE OOM rows; the `alc budget` rows are small ALC inputs whose
concept budget this task does not change). `km classify <input> --lines` with
`KM_REFERENCE_FORCE=1 KM_THREADS=1 KM_TIMING=1 timeout 300`, this branch's `km` and
`km-el-reference`, the P3 runner's environment (`LEAN_STACK_SIZE_KB=262144`), two at a time,
`/usr/bin/time -v` peak RSS (km plus the checker). Digest: the runner's `parse_answer_digest` against
the v1.6.0 unforced digest in the TSV (production routes are unchanged on this branch). Data:
`data/forced-256mib.tsv`, `data/forced-1gib-top3.tsv`; driver `tools/measure.py`.

| input | MB | status | wall s | peak RSS GB | published | digest | v1.6.0 unforced wall s |
|---|---|---|---|---|---|---|---|
| ore_ont_16744.owl | 576 | exit3 | 161.2 | 15.9 | no | - | 300.874 |
| ore_ont_15059.owl | 576 | exit3 | 146.6 | 8.8 | no | - | 51.855 |
| ore_ont_1559.owl | 393 | exit3 | 113.9 | 7.7 | no | - | 87.088 |
| ore_ont_15703.owl | 274 | ok | 64.9 | 3.9 | yes | match | 59.837 |
| ore_ont_13482.owl | 178 | ok | 50.9 | 2.9 | yes | match | 29.749 |
| ore_ont_9674.owl | 178 | ok | 194.4 | 5.8 | yes | match | 111.327 |
| ore_ont_15280.owl | 167 | ok | 46.0 | 2.7 | yes | match | 29.646 |
| ore_ont_1012.owl | 146 | ok | 46.6 | 2.4 | yes | match | 30.189 |
| ore_ont_10750.owl | 138 | ok | 42.3 | 2.3 | yes | match | 34.877 |
| ore_ont_11739.owl | 128 | ok | 169.1 | 3.1 | yes | match | 33.660 |
| ore_ont_10161.owl | 126 | ok | 62.6 | 1.8 | yes | match | 14.219 |
| ore_ont_9794.owl | 126 | ok | 40.3 | 1.8 | yes | match | 17.239 |
| ore_ont_1306.owl | 102 | ok | 34.1 | 1.7 | yes | match | 22.584 |
| ore_ont_6233.owl | 101 | ok | 30.3 | 1.7 | yes | match | 23.125 |
| ore_ont_10445.owl | 83 | ok | 21.6 | 1.2 | yes | match | 12.341 |
| ore_ont_13355.owl | 67 | ok | 47.9 | 1.4 | yes | match | 28.938 |
| ore_ont_5760.owl | 50 | ok | 13.6 | 0.9 | yes | match | 10.413 |
| ore_ont_12387.owl | 50 | ok | 49.9 | 0.7 | yes | match | 10.090 |
| ore_ont_12528.owl | 50 | ok | 42.2 | 1.2 | yes | match | 19.751 |
| ore_ont_7993.owl | 47 | ok | 13.1 | 0.8 | yes | match | 8.997 |

17 of 20 publish with a matching digest (all 20 died with `out of memory` in v1.6.0). The three
largest decline with `Stack overflow detected. Aborting.` (SIGABRT) in the checker. With a 1 GiB
Lean main stack (`LEAN_STACK_SIZE_KB=1048576`, the Lean default; KM's `CheckerCommand` lowers it
to 256 MiB): ore_ont_15059 publishes (236.7 s, 8.8 GB, digest match), ore_ont_1559 publishes
(248.4 s, 7.7 GB, digest match), ore_ont_16744 times out at 300 s (its unforced run timed out too).

ore_ont_1559 in detail (264,024 requested names, 2,925,744 clauses, stage input 540 MB): the
checker alone needs 24 s to parse and recognise and 160 s in total at 8.0 GB RSS (1 GiB stack); the
sparse output is 40.8 MB (1,997,807 sups, 0 unsat rows) where the dense one would have
7.0 x 10^10 cells. The time after recognition (about 136 s) is the closure plus the sparse readout
and print; the closure is not instrumented separately, but the readout is one pass over `c.subs`
and the output is 40 MB, so the closure dominates there.

### Stack overflow (ore_ont_1559, ore_ont_15059, ore_ont_16744): in the recogniser

- `--recognize-only --procedure el` alone overflows at 128 and 256 MiB and passes at 512 MiB and
  1 GiB, so the overflow happens before the closure, the sparse readout or the output.
- `--recognize-only --procedure alc` on the same input (JSON parse, `parseSource` of the binary,
  ALC `classifyClause` over all clauses) passes at 256 MiB: the JSON and input parsing are fine.
- Truncated inputs pass at 256 MiB up to 2,400,000 clauses; the full 2,925,744 overflow.
- A diagnostic executable (`tools/SparseStackDiag.lean`, built temporarily, not committed) ran
  each list function of `ELCommonSourceRecognizer` on synthetic lists at 256 MiB:
  `compileDirect` overflows between 2.0 M and 2.5 M items (passes at 2.0 M); `collectRoleHalves`
  and `zipSortedHalves` between 3 M and 4 M; `parseSource` between 4 M and 5 M; `maxNatList`,
  `itemsConcepts` and `sortHalves` pass at 6 M; `recognizeEL` on 3 M nf1 clauses overflows at
  256 MiB and passes at 1 GiB. All are structural non-tail recursions (`x :: f rest`), about
  110 to 130 bytes of stack per element for `compileDirect`.

So the first non-tail recursion to overflow is `ELCommonSourceRecognizer.compileDirect` (then
`collectRoleHalves`, `zipSortedHalves`, `parseSource`), all in the recogniser, which this task
must not change. Two remedies for the lead: tail-recursive (`@[csimp]`-backed) implementations of
those functions in the recogniser, or a larger `LEAN_STACK_SIZE_KB` for the reference stage only
(1 GiB publishes two of the three; it costs commit charge on ws, see `lean_checkers.rs`).

## Open

- The stack overflow above (recogniser; not changed here).
- ore_ont_16744 times out at 300 s even with 1 GiB of stack.
- The full suite rerun is for Ibex.
