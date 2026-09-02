# Peak memory and startup on the small exact HT / nominal band

Diagnostic and patch rationale for the v1.4 strict residuals whose executed
mechanism is the exact general hypertableau (`ht_general`, reached directly or
through the certified-nominal general-HT probe) or the exact nominal CB route
(`nominals`). Written 2026-09-02 against the uncommitted `development/v1.4`
working state; nothing in this document was built, run, or measured by its
author. Every number below is either copied from the retained sweep artefacts
or is an explicitly labelled estimate.

## 1. Targets

Sweep `v14-event-race-sweep-job51191347` (Xeon Gold 6248, 16 CPUs per task,
`KM_ROUTE=auto`) against the adjudicated per-ontology baseline ledger
`results/benchmarks/2026-08-31-v1.4-baseline/v13-per-ontology-targets.tsv`:

| ORE | source | frontend label | executed | KM wall / target | KM peak / target | shape |
| --- | --- | --- | --- | --- | --- | --- |
| 10908 | 180 KB, 1,110 axioms, 692 classes, 18 individuals, 1,674 clauses | `nominals` | `ht_general` (probe) | 0.187 s / 0.167 s | 66.5 / 46.7 MiB | SROIQ, 25 disjunctive clauses |
| 9635 | 32 KB, 171 axioms, 96 classes, 435 clauses | `certified_nominals` | `ht_general` (probe) | 0.043 s / 0.104 s | 30.3 / 14.4 MiB | SHIN(D), 16 disjunctive clauses |
| 13113 | 413 KB, 2,171 axioms, 1,269 classes, 210 individuals, 2,807 clauses | `nominals` | `nominals` (CB worker) | 0.106 s / 0.125 s | 45.0 / 39.0 MiB | SHOI |
| 13383 | 166 KB, 864 axioms, 368 classes, 103 individuals, 815 clauses | `nominals` | `nominals` (CB worker) | 0.073 s / 0.101 s | 41.3 / 21.1 MiB | SHOIF(D) |
| 960 | 1.24 MB, 6,412 axioms, 2,998 classes, 1,155 individuals, 6,479 clauses | `ht_general` | `ht_general` | 0.329 s / 0.300 s | 122.7 / 88.4 MiB | SHOIN(D) |
| 9668 | 1.25 MB, 6,443 axioms, 2,993 classes, 1,174 individuals, 6,473 clauses | `ht_general` | `ht_general` | 0.300 s / 0.282 s | 123.2 / 85.0 MiB | SHOIN(D) |

A later candidate build with the in-process typed HT handoff
(`frontend_run::ht_typed_handoff_candidate`, sources below 2 MiB) measured
ORE 10908 at about 0.145 s and 59-61 MiB against a 56.99 MiB target. That
build is the state this patch is written for: all six targets except 13113 and
13383 now classify inside the `km classify` process, with no worker
subprocess.

## 2. What the harness measures

`full_panel_run_one.py` reports `peak_mb = max(tree_sample_peak, direct_maxrss)`:

- `tree_watchdog.monitor` sums `/proc/<pid>/stat` RSS over the process tree
  and process group every 20 ms (`sample_interval=0.02`).
- `/usr/bin/time -v` contributes the kernel high-water mark (`ru_maxrss`) of
  the direct child, i.e. of `km classify` itself.

Consequences that separate genuine process-tree RSS from artefacts:

1. **In-process runs are measured exactly, not sampled.** For 10908, 9635, 960
   and 9668 the reported peak is the `km classify` VmHWM. Run-to-run spread
   (59-61 MiB on 10908) is allocator and scheduling variance, not sampling.
2. **Worker routes are sampled sums.** For `nominals` (13113, 13383) the peak
   is the 20 ms sample that saw the largest `supervisor + km engine` sum. The
   supervisor's share is constant during the wait, so anything it retains is
   added to every sample of the worker's own peak.
3. **The binary image is counted once per process.** `km` is an 11 MiB LTO
   binary; its touched text, rodata and relro pages appear in each process's
   RSS although they are physically shared. A two-process route pays that
   twice. The in-process handoff removed one copy for the HT band; the
   `nominals` CB route still pays two.
4. **Sub-50 ms runs are barely sampled.** 9635 finishes in 43 ms, so the tree
   sampler sees one or two points and the direct maxrss dominates. Its 30 MiB
   is therefore the process high-water mark, not a coincidence of timing.
5. **Retention, not live data, is what RSS tracks.** glibc keeps freed chunks
   resident: the main arena shrinks only when its top chunk exceeds the trim
   threshold, and that threshold doubles once a large buffer has been freed,
   which the frontend does early (the source text alone is above the default
   mmap threshold). Each classify worker thread owns an arena that keeps the
   largest model that thread ever built. A phase's garbage therefore sits
   inside the measured peak of the next phase.

## 3. Where the bytes are

### 3.1 In-process `ht_general` (10908, 9635 via the probe; 960, 9668 direct)

Sequence in one process: `flat_nf1` and `mirror` screens (auto only) ->
frontend pass 1 (parse, profile, normalise, write clause JSON for the nominal
fallback) -> for the probe members, a recursive `classify_with_evidence_mode`
under `KM_ROUTE=ht_general`, which repeats the frontend and retains the typed
`JInput` -> `run_ht_general_in_process` (`native_nominal_bridge_clauses`,
`cb_to_ht::convert`) -> `run_producer_input_typed` -> `run_tinput_inner`
(`clauses_of_tinput`, `Ht::new`, global consistency model,
`classify_parallel` with `KM_HT_PAR = avail_cpus() = 16`: phase 1 and phase 2
each build one `Ht` per worker thread) -> transitive closure and naming ->
`tableau_to_out` -> public-output mapping -> serialisation.

At the parallel-phase instant the process holds, in the main arena: the two
frontend passes' garbage (parse trees, normalisation intermediates, the
serialised nominal-view JSON stream) as retained free chunks; the live
`Meta` of both frames (IRI map, named list, profile); the frontend-owned side
data (`rbox`, `cardinalities`, `definers`, `source_axioms`, `nominal_abox`,
`rules`) that the converter consumed by reference but that stayed owned by
the runner; the typed `TInput`; two `Vec<Clause>` views (the original and the
clone moved into the HT thread); the main `Ht` with the global consistency
model; and the 16 clause templates cloned for the workers. In 16 worker
arenas: each worker's `Ht` (records with sorted body copies, trigger indexes)
plus the largest `Ext` model it built. After the phases the worker arenas keep
those maxima while output mapping allocates the public taxonomy on top.

Estimated shares (not measured): for 960/9668 a worker `Ht` over 6,479 clauses
is roughly 2 MB and a per-test model over a 1,150-individual clause-only ABox
view is a few MB, so 16 workers account for most of the 35 MiB gap to
Konclude; the retained frontend garbage of a 1.2 MB source is of the order of
10 MiB; the dead copies listed above are about 1 MB each. For 10908 the same
items are 5-10 times smaller, and the 3-4 MiB gap is within the retained
frontend garbage plus the dead copies.

### 3.2 `nominals` (13113, 13383)

`Mechanism::Cb` always spawns `km engine` through `engine_run::run_engine`.
The supervisor keeps its frontend garbage (a 413 KB source parses to several
MB of AST and normalisation state) resident beside the worker for the whole
saturation, and both processes carry the binary image. The worker already
releases its input buffers before saturation (`cli::run_engine`).

### 3.3 Subprocess HT (sources of 2 MiB and more, and `KM_NO_INPROC_HT`)

`spawn_ht` serialises the `TInput` into `bytes` and writes it from a feeder
thread; `run_ht_only` trims the supervisor right after the spawn, usually
before the feeder has finished, so the serialised document survived the trim.
`km tableau` read stdin into a `String` that `run_json(&buf)` kept alive for
the entire classification, and `run_tinput_inner` kept a second clause view
beside the one it moved into the HT thread.

## 4. The patch

Commit on branch `agent/v14-ht-memory`, on top of a snapshot of the inherited
working state. Every item is output-identical; the argument is given with it.

1. **`crate::mem::release_transient_heap`** (new `engine/src/mem.rs`). One
   shared `malloc_trim(0)` helper with a `KM_NO_HEAP_TRIM=1` opt-out, replacing
   the private copy in `race.rs`. `malloc_trim` releases free pages of every
   arena and shrinks heap tops; it cannot touch a live allocation, so no
   reasoner state changes. It is a no-op outside glibc.
2. **Trim while a worker runs.** `engine_run::run_engine` (every engine/elc
   spawn, hence the `nominals` route), the isolated frontend spawn in
   `run_ofn_split_cached`, `run_ht_only_bounded`, `run_tableau_only`, and
   `rules_consistency` (which now also drops the parsed clause file, the
   converted input and its wire bytes before waiting). The `spawn_ht` feeder
   thread drops and trims after the pipe drains, as `spawn_tableau` already
   did. Effect: the supervisor's share of every tree sample becomes its live
   data plus image, not its frontend high-water mark.
3. **Trim at the two in-process HT phase boundaries** in `run_tinput_inner`:
   before the HT thread starts (frontend and conversion garbage leaves the
   main arena before the workers allocate) and after it joins (the 16 worker
   arenas' retained maxima leave before output mapping allocates). The typed
   bridge path gets the same two boundaries. Both the in-process handoff and
   the `km tableau` worker go through this function.
4. **Release consumed inputs before classifying.** The three in-process
   runners drop `rbox`, `cardinalities`, `definers`, `source_axioms`,
   `nominal_abox` and `rules` after `convert` (the `TInput` owns what the
   classifier reads). `run_tinput_inner` moves the complete clause view into
   the HT thread instead of cloning it; the legacy-tableau fall-through
   rebuilds the view with `clauses_of_tinput`, which is exact because the only
   clauses that function omits are native-ABox negative-edge clauses, and a
   native ABox returns its defer before that fall-through. `Ht::classify`
   drops the global consistency model (`release_model_state`) before the
   parallel fan-out; `classify_parallel` never reads it, each worker builds
   its own `Ht`, and `consistent` rebuilds `Ext` on entry, preserving only the
   certified-address flag exactly as the rebuild inside `consistent` does.
5. **Worker wire text.** `tableau::run_json_owned` parses the owned stdin
   document and drops it unless `KM_HT_BRIDGE` is set (the bridge re-parses
   the producer input from the same bytes, so that route keeps it).
   `cli::run_tableau` uses it. `run_json(&str)` is unchanged for library and
   test callers.
6. **Output ownership.** Public-output mapping consumes the worker-side
   `subsumptions` map by value, so each row's strings are freed as its public
   row is built. The asserted-unsatisfiable check that used to borrow subject
   names until the end is decided at the same instant a subject first enters
   the unsatisfiable set, which is exactly when the old code recorded that
   subject. The compact-output branch is untouched apart from that check.

### Semantic and fixpoint preservation

No inference rule, clause set, ordering, blocking mode, fan-out count, or
publication gate changes. Items 1-3 only change which freed pages are
resident. Item 4 removes copies that had no reader on the executed path and
reconstructs the one copy that a non-executed path needs from the same typed
input. Item 5 keeps the bytes the bridge route re-parses. Item 6 replaces a
deferred set membership test by the same test evaluated eagerly at the single
point where the set was populated. The Lean-certified boundaries are not
touched: `source_decision_clauses` is still retained whenever a certificate is
requested, `new_certified` addresses are preserved, and the certificate
document builders receive the same clause views as before.

### Expected effect per target

- 10908: the parallel-phase high-water mark loses the retained frontend
  garbage of two passes and the dead copies; the output phase no longer sits
  on the worker arenas' maxima. The 3-4 MiB gap is within that range, but this
  is an estimate. Wall changes by three `malloc_trim` calls over a small heap
  (sub-millisecond each) plus page re-faults for the phase after each trim.
- 9635: same mechanism; the remaining floor is the image plus 16 worker
  arenas and stacks for 96 queries, which only a fan-out policy can reduce
  (see section 5).
- 13113, 13383: the supervisor's frontend garbage leaves every tree sample of
  the CB worker's peak. 13113 (gap about 5 MiB) is the likely flip; 13383's
  best baseline arm (21 MiB) is below the two-process floor.
- 960, 9668: the retained frontend garbage of a 1.2 MB source and the dead
  copies leave the parallel-phase peak (estimate: 10-15 MiB). The remaining
  gap is 16 concurrent worker models, which is genuine live memory under the
  current fan-out; these two stay memory failures unless the fan-out or the
  per-test model is changed.

## 5. Not done here, and why

- **Fan-out policy.** The sibling review in
  `.work/agents/fable-v14-ht-tail/` proposes a per-worker query floor
  (`KM_HT_PAR_MIN_QUERIES`, default 32) that shrinks 9635 to 3 workers but
  leaves 10908, 960 and 9668 at 16. Phase 1 on 960/9668 is about 3,000 SAT
  tests that each re-seed a 1,150-individual clause-only ABox; with 16
  threads the measured wall is already 0.30-0.33 s against a 0.28-0.30 s
  target, so halving the workers would trade a memory pass for a wall
  failure. Any change needs the same-node paired panel first.
- **Double frontend on the nominal probe.** `classify_with_evidence_mode`
  re-enters itself under `KM_ROUTE=ht_general` and re-parses the source;
  only the normalisation legitimately differs. Sharing the parse needs a
  route-explicit re-normalisation entry in `frontend/mod.rs`
  (`ofn_to_clauses_requested` is the seam) and is a frontend-API change, not a
  lifetime fix; it is worth about one parse plus profile per probe member.
- **Sharing the immutable clause index across workers.** `Ht` owns its
  records, trigger maps and `Rc`-backed model; each worker rebuilds all of it
  in both phases. Moving the read-only part behind an `Arc` would remove most
  of the per-worker footprint without changing fan-out, but it is a
  structural refactor of `hypertableau.rs` that must be compiled and
  exercised, not proposed blind.
- **Allocator thresholds.** Fixing `M_MMAP_THRESHOLD` or `M_ARENA_MAX` makes
  RSS follow live data more closely but adds `mmap`/`munmap` and cross-thread
  TLB shootdown cost to every mid-size allocation in a 17-thread process; the
  earlier 1194 experiments with `MALLOC_ARENA_MAX=1` and fixed thresholds were
  not adopted. Phase-boundary trims are the bounded form of the same idea.
- **Transparent huge pages on worker stacks.** Each classify worker requests
  a 512 MiB stack and the HT thread a 4 GiB stack. On a node with
  `transparent_hugepage/enabled = always` and a kernel that does not mark
  `MAP_STACK` mappings `VM_NOHUGEPAGE`, the first touch of each stack can fault
  a 2 MiB huge page: 17 threads would cost about 34 MiB of resident memory
  that is not useful. This would be genuine RSS but not genuine data, and it
  would explain part of the floor on 9635. Check `AnonHugePages` in
  `/proc/<pid>/smaps_rollup` of a running worker on the sweep nodes before
  deciding whether `prctl(PR_SET_THP_DISABLE)` or smaller stacks are worth it.

## 6. What Codex should run

Build with an isolated `CARGO_TARGET_DIR` (see the shared-target note in the
project memory), then:

```
cargo test --release --lib mem::tests
cargo test --release --lib tableau::tests::owned_wire_entry_matches_the_borrowed_worker_contract
cargo test --release --lib tableau::tests::typed_producer_handoff_matches_the_json_worker_contract
cargo test --release --lib hypertableau::tests::release_model_state_drops_the_model_and_keeps_certified_addresses
cargo test --release --lib hypertableau::tests::parallel_classify_after_model_release_matches_sequential
cargo test --release --lib hypertableau::tests::parallel_workers_retain_native_abox
cargo test --release --lib orchestrate::
cargo test --release --lib tableau::tests
cargo test --release --lib hypertableau::tests
cargo test --release --test rules_route
cargo test --release --test ht_taxonomy_certificate
cargo test --release --test incremental_ht_reasoning
cargo test --release
```

Then the same-node paired panel over the six targets plus the four passing
`ht_general` controls (13762, 6226, 9654, 9881), alternating three arms:

- A: the current v1.4 candidate binary;
- B: this branch;
- B0: this branch with `KM_NO_HEAP_TRIM=1` (isolates the trims from the
  ownership changes).

Record for every run: the canonical signature SHA (must equal A), the harness
`peak_mb` and `wall_s`, `/usr/bin/time -v` maximum resident set size, and
`KM_TIMING=1 KM_HT_STATS=1` stderr. Accept when every signature matches, no
control leaves `both`, and the six targets' memory falls without a wall loss
beyond the run-to-run spread. If 960/9668 do not move, the remaining gap is
the 16 concurrent worker models and the next lever is section 5.
