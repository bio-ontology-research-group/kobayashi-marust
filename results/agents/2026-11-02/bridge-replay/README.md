# bridge-replay: reuse of the consistency model with a reuse branch point

Agent `bridge-replay`, branch `fix/v155-bridge-replay` (base
`development/v1.5.5` at 80ba3173). Design and exactness argument:
docs/HYBRID-CB-HT.md section 16.

## What changed

On a base that resumes the first fork of a nondeterministic consistency
completion, every class job used to re-decide the pending ABox
disjunctions (§15). Now the first class job builds the LEAF: the
consistency continuation from that base, run once to a clash-free fixpoint
with no class root. Its open decisions stay below every class job (their
epochs stay open; they are not on the job's branch stack). Each subject
read-off, pair probe and batch refutation first runs on the leaf
(alternative 0 of a reuse branch point) and is accepted only when

- it is satisfiable (a clash-free fixpoint: a model of the input), never
  authoritative; or
- it is unsatisfiable through a root cancellation (u29 traced the clash to
  branching level 0, with witnessed sibling refutations), i.e. it depends on
  no decision of the job or of the leaf.

Every other outcome takes alternative 1: the leaf is dropped and the job
reruns on the resuming base exactly as before; the leaf is rebuilt lazily.
The dependency spine (track points, dependency nodes and links, clash and
concept descriptors, branch nodes) is epoch-exempt, so leaf jobs run inside
a journaled spine epoch (`ProcessContext::push_spine_journal_epoch`) popped
per job: DDB marks on the leaf's track points never reach the next job.
Leaf jobs write no satisfiability-expansion cache entries.

The same leaf serves the per-job reset path (no retained base, e.g. when
the saturation refuses `SELF`: 6132, 9899): there the leaf is the
consistency completion of the freshly initialized ABox and alternative 1 is
the per-job reset.

How this relates to Konclude: Konclude's class tasks start from the
deterministic consistency task with cleared queues and consult the cached
nondeterministic model (`CCompletionGraphCacheHandler`), reactivating
individuals the task contradicts. The port does not have that handler
(u21 `W6-DEFER`). The leaf reaches the same effect (class jobs reuse the
decided model and touch only what they reach) with a smaller argument: the
job is a continuation of the consistency search, its verdict is accepted
only when it cannot depend on a leaf decision, and everything else falls
back to the unchanged path.

Code: `engine/src/konclude_ht/bridge.rs` (block "Retained consistency leaf":
`RetainedConsistencyLeaf`, `build_/restore_/drop_retained_consistency_leaf`,
`retained_leaf_verdict_accepted`, and the `leaf_*` state and three attempt
sites in the classification driver), `engine/src/konclude_ht/process/context.rs`
(spine journal, and a unit test). `KM_BRIDGE_NO_LEAF_REUSE=1` restores the
old path; `KM_BRIDGE_LEAF_STATS=1` (with `KM_HT_STATS=1` on the orchestrated
route) prints the counters. No routing, budget, CB or frontend change.

Commits: 7710a52a (leaf on the resuming base), 69b3affe (per-job reset path,
shared replay map, design section 16), 57c893a3 (spine journal unit test),
plus the results commit.

## The eight inputs (automatic route, ws)

Release flags, `--lines`, `timeout 240`, `/usr/bin/time -v`, two runs at a
time (`tools/eight.sh`). Before = `km-base`, `cargo build --release` of
80ba3173 (NO PGO; the release candidate is PGO and 10 to 15 percent
faster). After = `km-v3`, release build of 69b3affe (no PGO; 57c893a3 adds
only a test). The host was shared with other agents' work.

| input | Konclude | before (s / peak RSS) | after (s / peak RSS) | reference (after) |
|---|---|---|---|---|
| ore_ont_3917 | 1.1 s | 72.5 / 347 MiB | **5.8** / 269 MiB | Konclude: agreement |
| ore_ont_11378 | 1.3 s | 139.8 / 560 MiB | **7.6** / 325 MiB | Konclude: agreement |
| ore_ont_12191 | 1.6 s | 140.1 / 566 MiB | **7.9** / 329 MiB | Konclude: agreement |
| ore_ont_9151 | 6 s | timeout / 452 MiB | **61.4** / 657 MiB | Konclude: agreement |
| ore_ont_9577 | 7 s | timeout / 479 MiB | **86.4** / 702 MiB | Konclude: agreement |
| ore_ont_6132 | 0.9 s | timeout / 1.21 GiB | **12.8** / 1.03 GiB | Konclude: agreement |
| ore_ont_9899 | 1.4 s | timeout / 1.23 GiB | timeout / 1.24 GiB | no answer |
| ore_ont_12128 | 22 s | timeout / 2.19 GiB | timeout / 2.19 GiB | no answer |

Peak RSS grows on 9151 and 9577 (the leaf keeps the decided consistency
model and its journals); on the other inputs it falls.

Every answer agrees with the pinned Konclude reference (`tools/diff_ref.py`,
`data/eight-after-refs.jsonl`); on 3917, 11378, 12191, 9151 and 9577 the
pinned JFact reference reports a different consistency verdict (contested,
as before). No reference disagreement before or after.

Reuse branch point counts per input (`data/leaf-counts-inputs.txt`):
3917 6,325 leaf jobs, 6,015 accepted satisfiable, 310 root cancellations,
0 fallbacks; 11378 and 12191 the same shape (0 fallbacks); 9151 2 fallbacks
of 7,705; 9577 46 fallbacks of 7,919; 6132 and 9899 0 fallbacks of 859 / 952.

Remaining cost:
- 9151, 9577: the bridge part is now 10 to 20 s per classification; the
  rest of the wall time is the orchestration (an ABox-quotient run, a
  certified-nominals run on the quotient, a TBox sandwich check that
  disagrees and declines the quotient, then the full input).
- 6132, 9899: the forced `ht_bridge` route answers in 11.8 s and 11.4 s
  with the Konclude answer (was a timeout). On the automatic route only
  the 8 s speculative bridge-first attempt can answer them (the
  certified-nominals bridge declines at the datatype gate), and they need
  about 8 s there: 6132 was accepted at 8.44 s in the final run and declined
  in two earlier runs; 9899 declined at 8.71 s. Per subject the leaf job
  spends about 4.7 ms in completion, almost all in the blocking-candidate
  scan (`get_anywhere_blocking_individual_node_canidate_hashed` under
  `detect_individual_node_blocked_status`, `data/6132-gdb-hot-functions.txt`),
  the scan `fix/v155-bridge-abox-probes` works on. No budget was changed.
- 12128: not this mechanism. The route is `production_all` without native
  nominals; the saturation refuses the terminology (`SELF`), so every one
  of the 187,518 classes needs a completion job (about 1.6 ms each); the
  bridge reached subject 178,817 at 300 s (`data/12128-profile.txt`). The
  fix is Konclude's SELF handling in the approximation saturation; not done.

## Differential runs (HermiT gold)

Seed pools left by earlier agents plus the new family, both routes
(`ht_bridge`, automatic), 60 s cap, release flags, two runs at a time
(`tools/seeds.sh`, `tools/diff_run.py`, `tools/seed_compare.py`). r3 ran on
its first 2,000 seeds (4,000 runs) in both columns to bound the run time.

| pool | runs | before ok / ERR / TIMEOUT | after ok / ERR / TIMEOUT | WRONG | transitions |
|---|---|---|---|---|---|
| bridge-replay (new) | 2,000 | 1,996 / 3 / 1 | 1,996 / 3 / 1 | 0 | none |
| bridge-defers | 600 | 447 / 153 / 0 | 447 / 153 / 0 | 0 | none |
| bridge-nominal-merge | 4,000 | 3,993 / 7 / 0 | 3,993 / 7 / 0 | 0 | none |
| nominal-coverage | 800 | 501 / 287 / 12 | 501 / 287 / 12 | 0 | none |
| sameindividual-bridge | 3,892 | 3,881 / 11 / 0 | 3,881 / 11 / 0 | 0 | none |
| r3-unannounced (first 2,000) | 4,000 | 3,596 / 323 / 81 | 3,596 / 323 / 81 | 0 | none |

15,292 runs, 0 verdict transitions, 0 disagreements with HermiT. `ERR`
means the harness parsed no answer; the same rows are ERR in both columns
(the bridge-speed agent's pools show the same pattern, e.g. 192 ERR on
bridge-defers), so they are not related to this change.

New family (`tools/gen_replay.py`, 1,000 seeds `p0..p999`, gold by HermiT
through `tools/gold.sh`): nondeterministic ABoxes (disjunctive and
nominal-disjunctive class assertions, at-most restrictions that force
merges), TBox consequences of each disjunct propagated through roles, and
query classes defined by ObjectHasValue and ObjectHasValue chains. On the
forced route the leaf was built in 763 seeds; the reuse branch point fell
back in 204 seeds (301 fallbacks: unsatisfiable verdicts not root-cancelled;
84 root cancellations and 8,371 satisfiable verdicts accepted), all answers
equal to HermiT. Seeds and gold: `.work/agent-scratch/bridge-replay/pool/`.

## Tests

`tools/itests.sh` at 57c893a3, `KM_THREADS=1`, `--test-threads=1`
(`data/tests-summary.txt`, `data/lib-failures.txt`):

- `cargo test --release --lib`: 3,110 passed, 21 failed, 10 ignored. The 21
  failures are exactly the baseline set (20 checker-bound `tableau::` tests
  and `cli::cb_derivation_candidate_tests::source_exact_taxonomy_uses_real_production_traces_and_models`);
  the extra passing test is the new spine journal test. No new failure.
- All 86 integration targets pass (including `completion_hot_path_env`: the
  new switches are read in `bridge.rs`, outside the completion hot path,
  and `bridge_conditional_full_replay`).

## Tools

- `tools/run.sh BIN ONT OUT`: one release-flag run with peak RSS.
- `tools/eight.sh BIN LABEL`: the eight inputs, two at a time, with the
  reference comparison (`tools/diff_ref.py`).
- `tools/seeds.sh BIN LABEL [ROUTES] [POOLS]`: the gold-backed pools
  (`R3_FIRST=N` limits r3); `tools/seed_compare.py BASE FINAL`.
- `tools/gen_replay.py SEED OUT.ofn`, `tools/gold.sh SEEDS GOLD`: the new
  family and its HermiT gold.
- `tools/itests.sh OUT`: the library and every integration target.
- `tools/pmp*.sh`: gdb stack sampling.

Binaries and raw logs: `.work/agent-scratch/bridge-replay/` (`bin/km-base`,
`bin/km-v3` with sha256 files, `data/`).
