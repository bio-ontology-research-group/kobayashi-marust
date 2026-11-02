# bridge-speed: native Konclude bridge on nine held-out ORE inputs

Agent `bridge-speed`, branch `fix/v155-bridge-speed` (base
`development/v1.5.5` at 1427ce55). Design and exactness arguments:
docs/HYBRID-CB-HT.md sections 13 and 14.

## Binaries

- `km-v1.5.5-rc-pgo`: the release-candidate binary
  (`.work/pgo-v155/km-v1.5.5-rc-pgo`), the "before" column. Its runs on the
  automatic route are the coordinator's runs of 2026-11-01
  (`.work/v155-heldout-gap/auto/`).
- `km-base`: `cargo build --release --bin km` at 1427ce55 (no PGO), used for
  the seed-pool baseline and the profiles.
- `km-final`: the release `km` binary of the branch head e5f402b6 (no PGO,
  sha256 `5b67ff69eb8c77c8…`); the seed pools ran on the identical build of
  75d91db4 (`km-final3`, sha256 `1f678b2f…`), which differs only in how the
  diagnostic `KM_BRIDGE_DDB_TRACE` is read.

Binaries and raw logs stay in `.work/agent-scratch/bridge-speed/` (`bin/`,
`data/`). Every measurement uses the release flags
(`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`),
`--lines`, `timeout 240` (`tools/run.sh`). The host was shared with other
agents and with this agent's own builds and test runs, so single wall times
carry noise of the order of 20 to 40 percent on the long runs.

## Results on the nine inputs (automatic route, ws)

| input | Konclude | before: RC (PGO) | after: `km-final` (HEAD, no PGO) | answer vs references (after) |
|---|---|---|---|---|
| ore_ont_4796 | 0.3 s | 240 s timeout | **23.3 s** (21 to 23 s in five runs of this branch) | Konclude, OpenLLet, JFact: agreement |
| ore_ont_6132 | 0.9 s | 240 s timeout | 240 s timeout | no answer |
| ore_ont_9899 | 1.4 s | 240 s timeout | 240 s timeout | no answer |
| ore_ont_3917 | 1.1 s | 71.1 s | 108.2 s (`km-base` 102.3 s in the same hour) | Konclude: agreement |
| ore_ont_11378 | 1.3 s | 148.3 s | 182.7 s (120 to 183 s over three runs) | Konclude: agreement |
| ore_ont_12191 | 1.6 s | 205.1 s | 191.6 s (133 to 213 s over three runs) | Konclude: agreement |
| ore_ont_9151 | 6 s | 240 s timeout (192 s in another run) | 240 s timeout | no answer |
| ore_ont_9577 | 7 s | 240 s timeout | 240 s timeout | no answer |
| ore_ont_12128 | 22 s | 240 s timeout | 240 s timeout | no answer |

The head build changes the automatic route only through the witness of
section 13; the cleared-queue screen of section 14 is off by default. On
3917, 11378 and 12191 the witness never fires, so their after-times are the
base algorithm without PGO under heavier host load (`km-base`, the same
source without this branch, took 102 s on 3917 in the same hour). The single
input that this branch moves inside the protocol is 4796: from a timeout to
23 s, with all three references agreeing (`data/nine-after-*`,
`data/nine-before-rc-summary.txt`).

References: `tools/diff_ref.py` converts `--lines` to the km-json shape,
canonicalises it with the pinned `.work/v152-correctness-1920/canonicalize.py`
against the reference `signature.tsv` and compares it with each pinned
validated reference through `compare_taxonomies.py`. Every answer KM gave,
before and after, agrees with the Konclude reference. On 3917, 11378 and
12191 the pinned JFact reference reports a different consistency verdict
(a contested reference, the same before and after) and there is no OpenLLet
reference; on 4796 all three references agree with KM.

## Defect 1: withheld root cancellation (ore_ont_4796)

Profile (`data/4796-rc-progress-excerpt.txt`, `data/4796-rc-gdb-samples.txt`,
`KM_BRIDGE_PROGRESS`, forced `--route ht_bridge`): 197 of 199 subjects take
20 to 90 ms; `system-as-artifact` and `physical-plurality` each run their
30 s read-off budget (400,000 drives, 600,000 backtracks, a 300-deep branch
stack, 9 million saturation expansions), so the bridge defers the whole
input and the race falls through to slower stacks. Konclude reports both
classes unsatisfiable in 0.3 s.

`KM_BRIDGE_DDB_TRACE` (new, `data/4796-ddb-walk-*.txt`) shows the walk: 28
percent of the clashes end in a chronological fallback, every one right
after the topmost decision, a four-way disjunction on one node, had all four
alternatives refuted. `KM_BRIDGE_DUMP_CLASH` (`data/4796-withheld-root-cancel.txt`)
shows the collected closure at branching level 0 and the root cancellation
withheld, because two siblings stored an EMPTY refutation. The clashes of
those siblings are `particular, ¬particular` on a successor that the
alternative `∃r142.¬particular` creates (`data/4796-concepts.txt`): the
operand is unsatisfiable on its own, so the empty set is correct and
Konclude cancels. The port's witness test (§11 of the design document)
cannot tell such a set from a lossy reconstruction and withholds.

Fix (section 13): an empty stored set counts once a separate probe of the
operand in a fresh bridge environment (disjunctions parked, chronological
copy-on-write search, no DDB) proves the operand unsatisfiable. The two
probes take 15 to 25 ms (`data/4796-witness-probes.txt`).

## Defect 2: every class job re-decides the ABox (ObjectHasValue family)

Profile (`data/3917-forced-resume-subject-opens.txt`,
`data/3917-base-gdb-samples.txt`): on 3917 all 5,383 class jobs open the
same 173 branch points (93 on nominal nodes) and make 3,000 to 4,400
insertions with zero backtracks, 16 ms per job; that is 87 s of the 117 s
prepare phase. The retained base resumes the first fork of the
nondeterministic consistency completion, so each job redoes the pending ABox
disjunctions. Konclude starts each class task from its deterministic
consistency task with cleared processing queues. With
`KM_BRIDGE_FORK_DRAIN=konclude` (the cleared-queue job already in the port)
3917 runs in 12 to 18 s with the reference answer
(`data/3917-forced-konclude-drain-subject-opens.txt`: 4,607 of 5,383 jobs
open no branch point), but that mode is not exact by itself.

Fix attempt (section 14, opt-in `KM_BRIDGE_CLEARED_QUEUE_SCREEN=1`): each
read-off first runs as a screen on the same retained graph with cleared
queues and is accepted only when the job stayed isolated from the retained
graph; otherwise the subject reruns as before. Effect: the
forced bridge on 3917 drops from 100 to 146 s to 52 s (2,514 of 5,383
screens accepted, `data/3917-phases.txt`). On the automatic route the bridge
runs on the `certified_nominals` input, where every job reaches a retained
individual: 0 of the first 512 screens are accepted
(`data/3917-auto-screen-rerun-reasons.txt`) and the driver stops screening,
so the automatic route gains nothing on this family (3917 automatic: 77.5 s
without, 90.5 s with the screen, same binary and hour). The screen is
therefore off by default.

The first version of the isolation test missed jobs that change a
LOCALIZED copy of a retained individual. The seed pools caught it (249 wrong
answers per route on `bridge-nominal-merge`, and the `cw_min4051` case of
`engine/tests/bridge_conditional_full_replay.rs`); commit 1edfbc5c adds the
id, merge and edge tests. The numbers in this README are for the corrected
binary.

## Not fixed

- 6132, 9899 (data-property assertions, `SELF` in the terminology): the
  saturation refuses the terminology, so the bridge uses the
  completion-only nominal schedule with no retained consistency base. Every
  class job rebuilds the whole ABox model: 617,000 insertions, 8,000 new
  nodes and 890 nominal branch points per job, 0.8 s of completion plus
  0.23 s of reset per subject, 849 subjects (`data/6132-forced-subject-stats.txt`).
  The fix is a retained base for the completion-only schedule; not done.
- 9151, 9577 and the remaining cost on 3917, 11378, 12191: on the automatic
  route every class job reaches the ABox (ObjectHasValue), so the screen
  cannot accept, and the jobs still resume the pending ABox disjunctions.
  Konclude avoids this with its backend cache of the consistency model
  (lazy reuse of individual labels with a reuse branch point); the port's
  equivalent, the precomputation replay, is disabled whenever the
  consistency completion is nondeterministic (`BRIDGE-REPLAY disabled`).
  Enabling it for nondeterministic completions is the next step.
- 12128 (96 MB): not profiled beyond the coordinator's trace (the bridge
  does not finish its 180 s HT-first phase).

## Differential runs

HermiT-gold seed pools left by other agents (`.work/agent-scratch/<pool>/seeds`
with `gold/`), both routes (`ht_bridge` and automatic), 60 s cap, release
flags, one run at a time (`tools/seeds.sh`, `tools/seed_compare.py`,
`data/seeds-base/`, `data/seeds-final/`, `data/seeds-base-vs-final.txt`).
Before = `km-base` (1427ce55), after = `km-final3` (75d91db4, screen off).

| pool | runs | WRONG before | WRONG after | verdict transitions |
|---|---|---|---|---|
| bridge-defers | 600 | 0 | 0 | none |
| bridge-nominal-merge | 4,000 | 0 | 0 | none |
| nominal-coverage | 800 | 0 | 0 | 2 TIMEOUT to ok |
| sameindividual-bridge | 3,892 | 11 | 11 | none (the same 11 consistency mismatches on the automatic route in both, s1032 and others with `FunctionalDataProperty`; not bridge related) |
| r3-unannounced | 8,000 | 0 | 0 | none |

17,292 runs, 0 answer differences between before and after, and no new
disagreement with HermiT. The r3 pool ran in three disjoint slices of its
file list at the end (one process each, at most two at a time) and was
merged in order (`data/seeds-final/r3-unannounced.tsv`).

With the screen on (`km-final2`, 1edfbc5c, `data/seeds-screen-on/`) the
first four pools also give 0 differences; the pre-fix screen (f987b90e)
gave 249 incomplete answers per route on `bridge-nominal-merge`.

## Tests

At the branch head (e5f402b6), `KM_THREADS=1`, `--test-threads=1`
(`tools/itests.sh`, `data/tests-summary.txt`):

- `cargo test --release --lib`: 3,100 passed, 21 failed, 10 ignored. The 21
  failures (`data/lib-failures.txt`) are exactly the baseline set: 20
  checker-bound `tableau::` tests and
  `cli::cb_derivation_candidate_tests::source_exact_taxonomy_uses_real_production_traces_and_models`.
  No new failure.
- All 86 integration targets pass.

Two failures seen on intermediate commits and fixed before the head:
`bridge_conditional_full_replay` (cw_min4051, the localization gap of the
first screen, fixed in 1edfbc5c) and `completion_hot_path_env` (an inline
`getenv` of the new diagnostic, fixed in e5f402b6).

## Tools

- `tools/run.sh BIN ONT OUTPREFIX [args]`: one release-flag run with
  `KM_TIMING=1`.
- `tools/nine.sh BIN LABEL`: the nine inputs, automatic route, sequential,
  with the reference comparison.
- `tools/diff_ref.py ONT LINES WORKDIR`: reference agreement of one output.
- `tools/seeds.sh BIN LABEL ROUTES`: the gold-backed seed pools through
  `tools/diff_run.py` (copied from `nominal-coverage`), one KM run at a time.
- `tools/seed_compare.py DIR_A DIR_B`: verdict transitions between two
  seed runs.
- `tools/pmp.sh`, `tools/pmp-child.sh`, `tools/pmp-sum.sh`: gdb stack
  sampling (no `perf` on ws).
- `tools/itests.sh`: the library and every integration target, one by one.
