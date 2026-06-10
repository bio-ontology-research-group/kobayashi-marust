# Changelog

All notable changes to the kobayashi-marust reasoner. Newest first.

## [unreleased] — CB engine scaling (ORE 2015 coverage push)

Goal: close the remaining ORE 2015 coverage gap to Konclude (was 551/590 ok;
40 failures = 21 timeout + 19 memout). Diagnosis, fixes, and benchmark deltas
tracked here.

### Frontend (`ofn`): streaming parse + compact clause set (giant ontologies)

The three 3M-axiom giants (ore_ont_8737, 15059, 16744; 450–580 MB OFN) memouted
**in the frontend** at ~20 GB before the reasoner ever started. Three changes,
all output-preserving (byte-identical clause+meta JSON to the old frontend on the
full ORE corpus and on all three giants), cut the frontend peak ~5.5x:

- **Zero-copy tokeniser / parser** (`sexpr.rs`): tokens are now `&str` slices into
  the source produced by a lazy iterator, instead of a `Vec<String>` with a heap
  allocation per token. The parse tree (`Node`) borrows those slices. The
  whole-document token vector and its per-token strings are never materialised.
- **Streaming document walk** (`parse.rs` `for_each_ontology_child` /
  `parse_axioms`): each `Ontology(...)` child is parsed, turned into SROIQ
  axioms, and dropped, so the whole-document AST is never resident. The RBox /
  declared-class side scans re-stream the (cheap, zero-copy) parse instead of
  retaining and **deep-cloning** the AST across `normalise`/`augment` (the old
  `onto_nodes = args.clone()` was itself an O(document) copy). `reg.short` call
  order is preserved, so assigned internal names are identical.
- **Compact `DLClause`** (`clauses.rs`): `body`/`head` are sorted-deduped
  `Vec<Atom>` (canonicalised in the constructors) instead of `BTreeSet<Atom>`.
  A `BTreeSet` node over-allocates even for a 1–2 atom clause; on 3M clauses that
  dominated memory. `Ontology` also stores axioms behind `Rc` so the dedup set
  shares the allocation instead of cloning every axiom.

Measured on ore_ont_8737 (472 MB): frontend peak **19.2 GB → 3.6 GB**, wall
45 s → 20 s (per-stage `VmHWM` via `KM_OFN_TIMING`: normalise 9.4→2.6 GB,
augment 18.6→3.5 GB). Result: **ore_ont_15059 recovered** (was memout; now ok in
70 s / 5 GB, signature identical to the Konclude gold — consistent, empty
#UNSAT). 8737 and 16744 now reach the reasoner (frontend no longer the wall) but
are **not** EL-safe (inverse roles), so they route to the context engine and
remain time-bound there — the engine-scaling residual, not the frontend.

### Result (ORE 2015, 240 s / 20 GB, gold = Konclude 587 ok)

| build | ok | timeout | memout | vs baseline |
|---|---|---|---|---|
| baseline (16-thread, pre-fixes) | 551 | 21 | 19 | — |
| + Hyper join + adaptive retry | 553 | 33 | 5 | +2, 0 regressions |
| + message batching | 554 | 31 | 6 | +3, 0 regressions |
| **+ streaming frontend (final)** | **555** | 32 | 4 | **+4, 0 regressions** |

Recovered: 2397 (fully correct), 9944, 9724 (sound but CB-incomplete on
number/inverse), and 15059 (the giant — see the frontend section; agrees with the
Konclude gold). Soundness preserved: vs gold the correctness profile is unchanged
(530 agree, 17 incomplete, 8 unsound — the pre-existing CB nominal/number
under-detected-unsat cases — both-disagree = 0); the one newly-classified
ontology (15059) agrees with gold, and no previously-agreeing ontology regressed.
All landed changes (Hyper join, batching, streaming frontend) are
output-preserving, so they change *whether* an ontology finishes in budget, never
*what* it derives. km has the lowest median peak memory of the five reasoners
(45.9 MB; Konclude 65, Sequoia 536).

Residual is genuinely hard for the CB engine: live-`∀+⊔` disjunction
(message-traffic explosion — Sequoia, the same calculus, solves these via more
mature redundancy/ordering), the two remaining giants (8737, 16744 — frontend now
fits, but they are not EL-safe so they route to the context engine and time out
there), four CB-engine ~20 GB memouts (10781, 15491, 16444, 6682), and role-chain
propagation volume. The hypertableau (`tableau_cli`) is NOT a fallback: it errors
or hangs on real ORE ontologies (validated only on small synthetic + kinship).

### Hyper rule: backtracking join instead of full cartesian product
- `engine/src/engine.rs` `hyper()` / new `hyper_join()`: the Hyper rule used to
  build a candidate list per body position and iterate the **full cartesian
  product**, attempting unification per combination and discarding the ones that
  fail cross-position variable consistency. On number restrictions
  (`R(x,y1) ∧ C(y1) ∧ R(x,y2) ∧ C(y2) → …`) that is `(#successors)^k`
  combinations, almost all immediately discarded.
  Measured on ore_ont_13912: **738171 enumerated, only 2462 unifiable (99.7 %
  waste)**.
  Replaced with a backtracking join that extends the central substitution one
  body position at a time and only descends into candidates consistent with the
  bindings already made (shared neighbour variables bound earliest). Yields the
  **identical resolvent set** — the skipped combinations were exactly the ones
  that fail `unify` — at a fraction of the enumeration. Same ont: 738171 → 59410
  combinations (12×). All `cargo test` pass (incl. `factor_number_restriction_clash`,
  `existential_subsumption`). No change to soundness/completeness; pure
  enumeration optimisation.
- Added env-gated `KM_PROF` diagnostics (per-query seeding + message-loop
  progress, per-rule saturate counters). Off by default, no hot-path cost.

### Message loop: batched propagation
- `engine.rs` `run_for`: the inter-context message fixpoint used to `saturate`
  *and* `propagate` the target after **every** message. On disjunction/role-chain
  ontologies that re-scans each context's predecessor-edge and Succ/Pred pools
  thousands of times (ore_ont_5303: ~86 k propagate calls). Applying a message
  never enqueues new messages (only `propagate` does), so the loop now **drains
  the whole pending batch**, saturates each target, records the touched contexts,
  and propagates each **once** per round. `apply_succ`/`apply_pred` return the
  touched context instead of propagating inline. Fixpoint unchanged (saturation
  is monotone and confluent — the schedule does not affect the derived set);
  ~1.5× faster message throughput. Recovers ore_ont_9724; all `cargo test` pass;
  vs gold no new unsound/incomplete.

### Threading: adaptive parallel-then-single-threaded-retry (memory-aware)
- Root cause: `reasoner.rs` `saturate()` splits the named queries into
  `available_parallelism` chunks, each a full `Engine` that **re-derives the
  shared successor contexts**. On existential-heavy ontologies this multiplies
  the dominant cost by the thread count. Measured on ore_ont_2397 (ALCH): 1
  thread = 9 GB / 138 s **SUCCESS**, 8 = 40 GB, 16 = 84 GB, 64 = 20 GB **MEMOUT
  @ 9 s**.
- A *blanket* `KM_THREADS=1` is **net-negative**: it recovers the memory-bound
  onts but regresses the speed-bound ones (measured: −12 onts that needed
  parallelism for speed now time out, vs +1..4 memout recoveries). Parallelism
  is genuinely valuable for throughput; it is only harmful (memory) on the
  existential-blow-up onts.
- Fix (`owl_classify.py` `_run_engine_adaptive`): run the **default parallel**
  attempt under an RSS watchdog (`KM_PAR_MEM_GB`, default 18 GiB, just under the
  20 GiB benchmark memcap) that kills *only the engine child*; on overflow,
  **retry single-threaded** (one engine, successor contexts shared, far lower
  memory). Keeps parallel speed for the speed-bound onts (no regression) and
  recovers the memory-bound onts via the fallback. RSS (not virtual address
  space) is monitored so legitimate large parallel runs are not falsely tripped.
  An explicit `KM_THREADS` bypasses the adaptive logic.
