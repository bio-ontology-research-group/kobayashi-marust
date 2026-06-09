# Changelog

All notable changes to the kobayashi-marust reasoner. Newest first.

## [unreleased] — CB engine scaling (ORE 2015 coverage push)

Goal: close the remaining ORE 2015 coverage gap to Konclude (was 551/590 ok;
40 failures = 21 timeout + 19 memout). Diagnosis, fixes, and benchmark deltas
tracked here.

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

### Threading: parallelise across ontologies, not within
- Root cause: `reasoner.rs` `saturate()` splits the named queries into
  `available_parallelism` chunks, each a full `Engine` that **re-derives the
  shared successor contexts**. On existential-heavy ontologies this multiplies
  the dominant cost by the thread count. Measured on ore_ont_2397 (ALCH): 1
  thread = 9 GB / 138 s **SUCCESS**, 8 = 40 GB, 16 = 84 GB, 64 = 20 GB **MEMOUT
  @ 9 s**.
  The Slurm harness already runs ontologies independently, so within-ontology
  parallelism is redundant under a per-ontology memory cap. Running the CB engine
  with `KM_THREADS=1` recovers the memory-bound onts (confirmed: +4 on the 40 =
  2397, 541, 9944, 11311) and cuts memory across the board.
