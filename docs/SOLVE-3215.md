# Closing ORE ontology 3215 by matching Konclude's classification phases

Date: 2026-07-13, restored 2026-07-30 (see "Restoring the budget" below)

## Result

`ore_ont_3215.owl` is gold-exact in the direct completion-bridge run on `ws`:

| Measurement | Result |
|---|---:|
| KM subsumption pairs | 3,923,171 |
| Konclude-gold pairs | 3,923,171 |
| Missing pairs | 0 |
| Extra pairs | 0 |
| KM / gold unsatisfiable classes | 0 / 0 |
| Consistency equal | yes |
| Wall time with verbose progress tracing | 202.79 s |
| Peak RSS | 5,388,716 KB |

The final production `km classify` binary matches on IBEX in 129 seconds at
5,351,252 KB with the normal `KM_THREADS=16` configuration. Its task in the
complete 592-ontology sweep matches again in 120 seconds at 5,357,524 KB. The
production binary SHA-256 is
`87ee76f1713e498fa7367832b00090663d0f8d3e02e7d296e275d7d1323c37c4`.
The complete evidence is in
`results/benchmarks/2026-07-13-3215-closure/`.

## Why 3215 was hard

3215 is a large, regular terminology. Its taxonomy contains 54,974 active
classification items and 3.9 million proper subsumption pairs. A superficially
reasonable port can derive the right saturation labels and still time out by
scheduling a huge number of unnecessary tableau subsumption tests.

The first exact structural divergence appeared before pair testing. KM attached
18,323 generated implications to the common named condition `C047449`; its
saturation label grew to roughly 18,000 concepts. Konclude's corresponding
label contained 3 concepts. After correcting the terminology representation,
KM saturation completed in about 31 seconds at about 5.1 GB. The saturation
labels already contained the complete positive taxonomy, but the classifier
still attempted redundant work for 18,323 residue subjects.

The remaining defect was not a slow tableau rule. It was a missing global
classification phase.

## The decisive Konclude comparison

We instrumented the matching Konclude source and ran the same ontology. The
classification trace reported:

| Konclude event | Count |
|---|---:|
| Saturation/classification items | 54,974 |
| Satisfiability results derived directly | 36,651 |
| Completion satisfiability jobs | 18,323 |
| Completion callbacks | 18,323 |
| Calculated possible-subsumption tests | 0 |

Konclude spent about 10.3 seconds dispatching and collecting the 18,323
satisfiability jobs on 56 workers. Its class phase completed in about 12.6
seconds. Most importantly, it did not run a single pairwise subsumption job.

The relevant control flow is in
`COptimizedKPSetClassSubsumptionClassifierThread.cpp`, method
`createNextSubsumtionTest`, around source lines 866–1059:

1. Konclude waits until every class satisfiability job and its classification
   messages have completed.
2. It sorts satisfiable class items by known-subsumer count.
3. It builds a sparse upward/downward propagation graph rooted at the
   `owl:Thing` classifier item.
4. It compares each completed child possible-subsumer map with its parent maps.
   A parent candidate absent from the child map is invalidated and recursively
   pruned.
5. Only after this global barrier can Konclude schedule a possible-subsumption
   calculation.

KM had ported the per-message analyzers and local pruning handlers, but the
synchronous bridge interleaved one subject model with that subject's pair
tests. Its propagation parent/child sets were still empty. It therefore crossed
the pair-testing boundary before the information needed for Konclude's main
KPSet pruning step existed.

## The targeted port

### 1. Reproduce Konclude's terminology shape

The bridge now follows the corresponding Konclude preprocessing choices:

- It creates classifier and saturation items only for active OWL classes.
  Frontend `Q_` and definer concepts remain anonymous structural concepts.
- In normalized source-TBox mode it does not also materialize the clausifier's
  duplicate definer DAG.
- Trigger absorption ports `getUpdatedTriggerComplexities`,
  `findAndReplaceImplicationFromTriggers`, and
  `getImplicationTriggeredConceptForTriggers`: over-used trigger penalties,
  cached pair reuse, decreasing complexity/address order, and the reusable
  left-deep binary implication chain.
- Disjunctive trigger complexity uses Konclude's rounded-average arithmetic.
  The final conclusion unfolds from the combined trigger, rather than attaching
  thousands of reverse definitions to one common named condition.
- Common-disjunct extraction uses reusable dense signed-concept sets with
  branch rollback. This has the same set/cache semantics as Konclude's
  implicitly shared Qt sets without repeated large Rust `HashSet` clones.

These changes remove the first label-shape divergence. They do not discard an
axiom or approximate a class expression.

### 2. Match Konclude's saturation data structures closely enough to finish

The saturation port retains the same rule fixpoint and changes only storage or
duplicate handling:

- concept-tag label maps use a small integer hasher, matching Konclude's direct
  integer-key hashing design;
- an exact signed duplicate is checked before allocating a forced-insertion
  descriptor; the opposite polarity still enters the ordinary clash path;
- the remaining-process-linker pool is an O(1) LIFO free list implemented by
  `Vec::push`/`Vec::pop`, matching Konclude's intrusive prepend/take-head order;
- diagnostic environment gates are cached once instead of calling `getenv` in
  the roughly 187 million label-insertion attempts made by 3215.

The duplicate branch has no rule or callback side effect in Konclude or KM, so
the precheck removes only an unused allocation. The storage changes preserve
the same saturation fixpoint.

### 3. Port the missing all-satisfiability-jobs barrier

`finish_synchronous_satisfiable_phase` in
`engine/src/konclude_ht/classifier/mod.rs` is the synchronous form of the C++
phase above. It:

- creates and initializes the explicit `owl:Thing` KPSet sentinel that the
  bridge's named vector intentionally excludes;
- orders active satisfiable items by known-subsumer count;
- constructs Konclude's sparse propagation parent/child graph;
- globally compares completed possible maps; and
- calls the existing recursive invalidation/pruning bookkeeping for candidates
  absent from a child map.

`bridged_classify_opts` in `engine/src/konclude_ht/bridge.rs` now has two
strict phases:

1. **Prepare:** run every residue satisfiability model and deliver its
   deterministic-subsumer, possible-subsumer, and pseudo-model messages. Run no
   pair tests.
2. **Verify:** cross the global KPSet barrier once, then inspect only candidates
   still unknown. Successful prepare jobs are marked derived, so their models
   are not rerun.

On 3215 the barrier marks 202,002 candidates false by propagation. Zero
`BRIDGE-PAIR-START` events remain. The known saturation labels provide the
positive taxonomy; completed child models eliminate the false candidates.

### 4. Prevent the speculative CB racer from starving the serial bridge

The first portable binary made the bridge logically exact, but the normal
production race still timed out. A controlled IBEX comparison isolated the
cause:

| Ambient threads | Production result | Wall | Peak RSS |
|---:|---|---:|---:|
| 16 | timeout | 240 s | 3,543,944 KB |
| 2 | exact match | 137 s | 5,348,648 KB |

The 16-thread process used about 12 cores because the speculative CB fallback
occupied the other 15 engine slots while the bridge executed its 18,323 KPSet
model jobs synchronously. Both arms were sound and complete, but the CB arm
starved the serial bridge on memory bandwidth. This was an orchestrator issue,
not a classifier result difference.

`engine/src/orchestrate/race.rs` now returns the faithful bridge's active-class
count to the race supervisor. At 50,000 or more active classes, it gives the
speculative CB fallback one thread until the bridge answers or defers. Below
that structural threshold, the existing reservation is unchanged. The bridge,
CB engine, fallback behavior, and CB-preference winner rule are unchanged.

The final binary was invoked with the standard `KM_THREADS=16`; it applied the
cap internally and matched in 129 seconds. The independent full-sweep task
matched in 120 seconds. The scheduler regression test covers the threshold and
the unchanged smaller/non-bridge cases.

## Why the fix is targeted

The final classifier change is not a new heuristic. It restores the ordering
and global map-propagation phase used by Konclude before its first pair test.
The supporting bridge changes reproduce Konclude's active-class and trigger
representations. The saturation changes alter storage and scheduling costs, not
which calculus consequences reach the fixpoint.

No Lean re-certification is required. This patch does not change the CB
calculus rules, ordering, redundancy criterion, or derived clause set. It
changes completion-bridge preprocessing, exact KPSet classifier bookkeeping,
and fixpoint-preserving data structures outside the Lean-certified CB core.

## Verification

The focused tests cover:

- pruning a parent candidate absent from a child's completed map at the KPSet
  barrier;
- excluding structural markers from active class and saturation items;
- Konclude trigger ordering and rounded-average complexity;
- common-disjunct cache reuse;
- exact-duplicate suppression without suppressing an opposite-polarity clash;
- LIFO free-list reuse.

The complete `ws` release suite passes: 1,468 passed, 0 failed, 7 ignored. The
direct and production 3215 results are exactly equal to Konclude gold,
including consistency and the unsatisfiable-class block.

IBEX full-sweep job 48790295 attempted all 592 ontologies at 240 seconds and 20
GB each. It reports 574 ok / 18 timeout and 508 exact gold matches, compared
with 569 / 23 and 499 matches in the immediately preceding feature sweep.
There are zero gold-match regressions. In addition to 3215, eight ontologies
become exact matches; six prior false-positive cases and one prior incomplete
case are corrected by the same active-class and KPSet bookkeeping fixes. The
machine-readable aggregate and reproduction scripts are in the benchmark
artifact directory linked above.

Controlled A/B job 48790909 reran the nine changed correctness cases with the
preceding and final binaries under identical flags. All nine pairs completed:
eight exact-match improvements including 3215, one smaller remaining
both-disagree signature, and zero exact-match regressions. This separates the
correctness improvements from the timing recoveries seen in the full sweep.

## Restoring the budget (2026-07-30)

### What the 2026-07-27 sweep showed

The 2026-07-27 full sweep
(`results/benchmarks/2026-07-27-solving-routes-full-sweep/`) reports
`ore_ont_3215.owl` as a timeout on all 44 current-main KM arms, including the
`km_solution_kpset_barrier` arm that replays the environment recorded above.
The source-bound historical supplement is the same story: exclusive job
49522590 reran the 2026-07-13 closure binary identity alone on a
`cpu_intel_gold_6248` node and it also timed out, at 240.03 s and 8,398 MB.
Konclude answers the same ontology in 64.5 s at 9,702 MB.

So the regression hypothesis was wrong. The closure was not undone by a later
commit.

### The measurement that settles it

Rebuilding `91db9fb` (the closure) and current main from source and running
both on one host, with the documented environment, gives:

| Binary | HT worker | Total | Peak RSS | Signature |
|---|---:|---:|---:|---|
| `91db9fb` (closure) | 397.7 s | 411.7 s | 5,353,720 KB | exact, 3,923,171 pairs |
| current main | 385.8 s | 385.8 s | 5,536,200 KB | exact, 3,923,171 pairs |

Current main is not slower than the closure, and both are still exactly equal
to Konclude gold. The peak RSS of the historical build reproduces the recorded
5,351,252 KB to within 0.05%, which confirms the rebuild is the same work. The
KPSet design, the all-satisfiability-jobs barrier, and the saturation labels
are all intact. What the ontology no longer had was margin: on the hardware
that measures the 240-second contract today, both binaries need about 400 s.

### Where the time goes

`KM_BRIDGE_PROGRESS` now prints a per-phase breakdown. On current main:

| Phase | Time |
|---|---:|
| Frontend + clause hand-off | 6.6 s |
| Bridge environment (trigger absorption) | 1.1 s |
| Saturation seeds + loop + extraction | 34.4 s |
| Satisfiability phase (18,323 completion jobs) | ~340 s |
| KPSet barrier | 0.8 s |
| Verification (0 pairwise subsumption tests) | 12.7 s |

The saturation phase still answers 36,650 subjects directly and hands the
completion path the same 18,323-subject residue the Konclude trace reports.
The barrier still eliminates every pairwise test. The whole cost is the
satisfiability phase, and it is Konclude's own job count, run one at a time.

### The defect: `getenv` in the completion rule bodies

Stack sampling of the satisfiability phase puts more than a third of it inside
`getenv`. The completion rule bodies consult their CLI-only diagnostics inline,
once per concept addition:

- `insert_concepts_to_individual_concept_set` and
  `add_concept_to_individual{,_skip_and_processing}` read `KM_BRIDGE_WATCH_TAG`,
  `KM_BRIDGE_WATCH_NEGTAG` and `KM_BRIDGE_WATCH_NODE`;
- `create_successor_individual`, the OR/clash sites, and the at-most and merge
  paths read `KM_BRIDGE_SEARCH_LOG`, `KM_BRIDGE_DUMP_CLASH`,
  `KM_SAT_ABSORB_DEBUG`, `KM_HT_OR_TRACE` and their siblings;
- `ProcessContext::ht_check_dangling_satellites` reads `KM_BRIDGE_SEARCH_LOG`
  on every `pop_branch_epoch`.

`std::env::var` takes the process-wide environment lock and allocates a
`String` on each call, so a disabled diagnostic costs more than the rule it
guards. Section 2 above removed exactly this cost from the saturation hot path
in 2026-07-13, for exactly this ontology and this reason. The completion layer
never received the same treatment, and the completion work that landed after
the closure multiplied the number of those call sites a single job crosses.

### The fix

`engine/src/konclude_ht/completion/mod.rs` now owns cached accessors for each
of these settings, built from the `OnceLock` pattern
`engine/src/konclude_ht/saturation/mod.rs` already uses, and all 50 inline
reads route through them. Every accessor returns exactly what the inline call
returned: the environment is immutable for the life of a worker, and no route
bundle, orchestrator path, or test sets any of these variables. Every
diagnostic keeps working.

No rule fires differently and no derived set moves, so no Lean
re-certification is required. This is the removal of an observation cost, not a
calculus change.

### Result

IBEX job 49624875, exclusive `cpu_intel_gold_6248` node, 240 s and 20 GiB:

| Route | Wall | Peak RSS | Signature |
|---|---:|---:|---|
| `ht_bridge` | 162.2 s | 5,560,592 KB | exact, 3,923,171 pairs |
| `auto` (production) | 161.9 s | 5,500,480 KB | exact, 3,923,171 pairs |

Zero missing, zero extra, no unsatisfiable-class difference, same consistency
result. On the workstation the isolated route drops from 385.8 s to 215.4 s.

`engine/tests/completion_hot_path_env.rs` fails the build if an inline
`std::env::var` returns to a completion rule body or to the process-context
epoch check, and a unit test pins every cached gate to its unconfigured
default.
