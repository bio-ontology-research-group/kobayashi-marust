# Rule checker follow-ups (2026-10-30)

Branch `fix/v155-rules-route-followups` from `development/v1.5.5` (7807ba92).
These are the three findings of the inert-sort exactness review
(`.work/agent-scratch/review-inert-sorts/`). The docs are in
docs/NOMINALS-CB.md section 6, under "Rule checker follow-ups (2026-10-30)".

Commits:

- bfef7536 worker: grow deep search stacks on demand instead of reserving them
- dea343ac incremental: release inert object sorts in the rule adapter's probe
- 2650c432 hypertableau: retry worker-pool spawns that fail for lack of memory
- e9cbed22 frontend: reuse the positive-ABox closure in the second classifier pass
- plus the commit carrying this README, the docs, a test-only environment-lock
  fix in `tableau.rs` and the address-space test fixture.

Binaries are all plain `cargo build --release --features mimalloc --bin km`.
They live in `.work/agent-scratch/rules-route-followups/`:

| name | source | md5 |
|---|---|---|
| `km-base` | 62e7a33d (= `rules-worker-cost/km-fix`; its engine is identical to 7807ba92 apart from the version string) | 9666cafa6856 |
| `km-review` | the reviewer's build of the same code (`review-inert-sorts/km-review`) | 2031b2882fb0 |
| `km-i12` | bfef7536 + dea343ac (items 1 and 2) | a215cf35e7db |
| `km-final` | e9cbed22 (all items; the later commit changes only tests and docs) | 7852ef714a10 |
| `km-v153-pgo` | v1.5.3 release PGO asset (`subset-blocking-cost/`) | 285f555f3c96 |

Host conditions: `ws`, 56 cores. The load average during the runs ranged
from 45 to 125 because other agents were running. `vm.overcommit_memory = 2`,
CommitLimit 264 GiB, and Committed_AS 186 to 274 GiB over the session.
Wall times are therefore noisy. The timing tables also report user CPU time.

## Item 1: worker failures that depended on machine load

**Cause.** `km tableau` started a 2 GiB thread (`cli::run_tableau`). Inside
it, the rule checker started a 4 GiB thread (`rules_consistency_with_sorts`).
Under strict overcommit each stack is charged in full against the commit
limit when the thread starts. When other processes held most of the limit,
`pthread_create` returned `EAGAIN`, the worker printed `tableau error:
Resource temporarily unavailable (os error 11)` and exited 1. The
orchestrator had sent that stderr to `/dev/null` and reported `worker tableau
exited 1:`.

**Reproduction** (`data/worker-failures-old-binary.txt`):

- Natural failures: `km-review` on the 1,757 review seeds at 24 parallel jobs
  (`data/p24.tsv`; the run was cut short at 836 seeds when `xargs` itself hit
  ENOMEM). Two worker exits (b8_1071, b8_1074), both with the message above.
  Committed_AS peaked at 262.5 of 264 GiB.
- Deterministic failures: `ulimit -v 5000000` gives the same message with
  exit 1. `ulimit -v 3000000` gives exit 134, from a panic at the 2 GiB
  spawn.
- `ulimit -v` itself was unlimited, and `vm.overcommit_memory` was 2.

**Fix.** `engine/src/bigstack.rs`:

- `ensure_main_stack` raises the worker's soft `RLIMIT_STACK` to 4 GiB plus
  128 MiB and re-executes it once. `execve` then reserves the gap below the
  main stack as address space only, and the kernel charges stack pages as
  the stack grows.
- `run` runs deep work inline when the current thread has the stack it asks
  for. Otherwise it spawns a thread with the stack it needs and retries a
  failed spawn for about 5 s. If the spawn still fails, the error names the
  thread, the stack size and the OS reason.
- All six `stack_size(4 << 30)` sites in tableau.rs and the incremental probe
  now go through `run`.
- The seven HT worker pools (64 to 512 MiB stacks) retry their spawns with
  `spawn_scoped_retrying`. They run in parallel, so they cannot share a stack.
- `rules_consistency` keeps the worker's stderr and puts its last 4 KiB in the
  error.

I chose the main-thread strategy because it is the only option that removes
the up-front charge. Retrying alone still fails under sustained pressure.
`MAP_NORESERVE` is ignored when `vm.overcommit_memory` is 2. Sizing the stack
to the input has no sound bound.

A running worker on 7278 showed `Max stack size 4429185024`, one thread, and
a `VmStk` of 132 kB. The old worker's VSZ was 7 to 8 GB; the new one's is
1 GB.

**Verification** (review protocol: `scripts/onoff2.sh` = `onoff.sh` plus
capture of the worker's stderr and exit code, 1,757 seeds, 12 parallel jobs,
60 s cap):

| binary | pairs | same | DIFF | worker exits | released seeds |
|---|---:|---:|---:|---:|---:|
| km-review (review run) | 1,757 | 1,742 | 15 | 97 seeds had rc 1 on at least one side | 191 |
| km-i12 (`data/oo-fix12.tsv`) | 1,757 | 1,757 | 0 | 0 | 191 |
| km-final (`data/oo-final12.tsv`) | 1,757 | 1,753 | 4 | 0 | 191 |

The 4 km-final DIFFs are b11_1074, b8_1074, b9_11_1074 and b9_1074. Each
takes about 50 s, and in each pair exactly one side hit the 60 s cap (rc
124 with empty output, against rc 0 on the other side). They are timeouts,
not answer differences: in the km-i12 run all four answered on both sides
with equal output. Of the 97 seeds the review binary answered with rc 1,
km-final answers 86 and 11 hit the cap. No worker exited with an error in
either fixed run: there were no `.rc` files under `cap-*`, and no `worker
tableau exited` lines. Peak Committed_AS was 245 GiB for km-i12 and 239 GiB
for km-final (`data/commit-*.txt`).

Integration test `rule_checker_worker_runs_without_reserving_its_deep_stack`
runs b11_1134 under `RLIMIT_AS` = 3 GiB. The old binary fails there with
`worker tableau terminated by signal 6`. The fixed binary's output is
byte-identical to the unlimited run.

Residual risks:

- The orchestrator's in-process CB thread (`orchestrate/mod.rs`, 256 MiB,
  "inproc-cb") still spawns without retry. On failure it returns a Spawn
  error.
- Rayon's global pool panics if it cannot start its threads. I saw this
  only under `RLIMIT_AS`, whose limit counts mimalloc's virtual reservations.
  I did not touch either.

## Item 2: inert-sort release on the incremental route

`incremental_rules::rules_consistent` now applies the same release. It calls
`inert_sorts::release_inert_object_sorts_in`, the parts-based form of the
batch function, with the same source-name test and the same
`KM_RULES_KEEP_INERT_SORTS` switch. Both `KM_TIMING` lines list the released
definers. Test `incremental_and_batch_rule_checkers_release_the_same_definers`
uses seed fr69 plus one added class assertion. The batch route, the batch
route with the conversion, and the incremental adapter all release Q_6, Q_7
and Q_9. The switch turns the pass off on both routes and keeps the verdict.

Measurement on ore_ont_7278 (`scripts/incr7278.py`: a legacy session
(`KM_SOURCE_SESSION=legacy`), then a revision adding
`ObjectPropertyAssertion(isPartOf III_2004 _2005)`; one core):

- **Default settings.** The adapter is never reached. The session frontend
  reports the 81 data assertions as uncarried, `retained_backend_allowed`
  fails, and every revision is an `exact_rebuild` through the batch
  classifier. That classifier already releases the sorts (init 21 to 31 s,
  revision 26 to 51 s, all of it batch).
- **With `KM_DATA_ASSERTION_AS_CLASS=1`.** The adapter is used
  (`ht_delta`), but the probe does not finish within these limits:
  - km-base (no release): stopped after 28 min wall, 17 min CPU.
  - km-i12 (release, 11 definers): stopped after 21 min wall, 13 min CPU.
- **Cause of the slow probe.** The batch checker runs 7278 in source-model
  mode with `KM_RULE_JOIN_ORDER=1`; the incremental probe runs without it. On
  the batch checker's captured worker input, `km tableau` takes 8 s with
  `KM_RULE_JOIN_ORDER=1` and more than 100 s (killed) without it. The release
  is applied but does not, by itself, make the incremental probe fast.
  Setting the selective join order in the probe changes the clause matcher's
  schedule, and I did not make that change.

## Item 3: the second frontend pass

**Where the time goes.** The finite-rule grounding (`lower_finite_rules`)
takes 0.1 to 0.2 s. The rule-assertion closure
`rule_assertions::materialize`, which runs after it, takes 2.8 s on a quiet
machine and 4.4 to 7.4 s here. Stack samples (`scripts/pmp.sh`) and the new
`KM_TIMING frontend ... grounding/closure` lines show this. The README of
`rules-worker-cost` attributed the cost to the grounding.

**Audit of a conditional skip.** The second pass differs from the first in
the parse-time conversion of positive data assertions. Every consumer
between parsing and the grounding sees the converted assertions:
`abox_consistency`, `data_abox`, the ABox probes, the literal cap and
abstraction block, `nominal_abox`, and the uncarried count. On 7278 the two
passes already differ in `nominal_abox`. A skip conditioned on the first
pass would change that meta, so I did not skip the pass.

**Fix.** `frontend/pass_cache.rs` memoizes the closure across the two passes
of `run_ofn_split_cached`. The memo is keyed on set-equality of the closure
input: concept facts, role facts, inclusions and rules. The exactness
argument is in `rule_assertions::ClosureInput` and docs/NOMINALS-CB.md:
equal inputs give equal closures. `KM_NO_FRONTEND_PASS_CACHE=1` disables the
memo.

**Verification.** `scripts/ab3.sh` compares three configurations: km-final,
km-final with the memo off, and km-i12 (without item 3). Each run uses
`KM_THREADS=3` and a 60 s cap. The inputs are the 400 fr seeds and the 1,757
review seeds (`data/ab-seeds.tsv`):

- 2,156 of 2,157 rows are equal in rc and md5 across all three
  configurations. Of these, 1,079 answered in all three, 990 are the same
  refusal (rc 3), and 88 hit the cap on all sides.
- The memo hit on 1,028 inputs: 346 fr and 682 review seeds.
- The single DIFF, fr136, is a 60 s cap hit in the memo-on run, where the
  memo did not fire. Three reruns of km-final gave the common md5.
- 7278 and 3726 give md5 1be6b3438106 in all 24 timing runs.

Timing (`scripts/timing.sh`, `data/timing-table.tsv`): three interleaved
rounds, previous agent's run1 environment, one core, wall / user seconds:

| input | km-base | km-i12 | km-final, memo off | km-final |
|---|---|---|---|---|
| 7278 wall | 24.4 18.7 27.0 | 18.6 18.0 19.1 | 16.3 25.4 28.9 | 14.0 16.9 16.2 |
| 7278 user | 18.4 16.7 17.3 | 17.9 17.0 16.8 | 15.6 17.3 17.6 | 12.4 12.4 12.5 |
| 3726 wall | 20.3 31.1 23.6 | 21.5 27.9 24.2 | 17.5 26.6 30.5 | 14.9 16.0 20.3 |
| 3726 user | 16.7 17.2 17.3 | 17.0 17.3 17.6 | 16.7 17.3 17.6 | 12.4 12.5 12.7 |

Under this load the memo saves about 4.8 s of CPU per run, a ratio of 0.72
to the base. The second pass drops from 4.6 to 7.7 s to 0.24 to 0.34 s. The
same ratio applied to the brief's quiet-machine figure of 9.3 s gives about
6.7 s, against 6.9 s for v1.5.3. In two direct interleaved pairs under load,
`km-v153-pgo` took 17.9 and 8.1 s wall (11.8 and 8.1 s user), and km-final
took 8.3 and 11.9 s wall (8.2 and 11.8 s user). A quiet-machine table remains
to be done.

## Tests (release, `--features mimalloc`)

Run with `scripts/run_tests.sh` and `run_tests2.sh`. Logs are
`.work/agent-scratch/rules-route-followups/tests-final*.log`.

- **Targeted lib tests** (`orchestrate::inert_sorts frontend::rule_assertions
  bigstack::`): 17 passed, 0 failed.
- **`--lib orchestrate::`**: 292 passed, 0 failed, 1 ignored.
- **Integration, 19 suites** (the 18 rule suites of `rules-worker-cost` plus
  `rules_inert_sorts_routes`), first full pass:
  - 17 suites passed.
  - `data_assertions_carried`: one test hit its 60 s bound on route
    `nominals`.
  - `empty_and_universal_data_ranges`: one test hit its 180 s bound on
    `cb_absorb8`.
  - `rules_inert_sorts_routes`: 2 of 3 passed. I then fixed the third test
    (see the rerun line below).
  - Both timeouts are load. The two inputs take the same time with km-base
    and km-final (23.6 / 25.1 s and 41.9 / 43.8 s wall), with identical
    output.
- **Rerun at 2 test threads** (`tests-final2.log`): `rules_inert_sorts_routes`
  3/3, `data_assertions_carried` 9/9, `empty_and_universal_data_ranges` 10/10.
  - The fix to the third test: its first version ran the whole
    classification under `RLIMIT_AS`, and the CB engine's rayon pool failed
    there. It now uses a fixture that ends at the rule checker.
- **`--lib tableau:: frontend::`** (after the lock fix): 635 passed, 20
  failed, stable over 4 runs. The 20 are exactly the pre-existing names of
  results/agents/2026-10-30/rules-worker-cost/tests/ (they need the
  `KM_HT_LEAN_*` checkers; `data/lib-tableau-frontend-failed.txt`). Before
  the lock fix, 3 runs gave 21 or 22 failures: the same 20, plus
  `tableau::tests::compact_bridge_entry_matches_the_legacy_json_worker`,
  plus once
  `frontend::symbolic_frontend_tests::full_symbolic_frontend_retains_data_and_large_bound_evidence`
  (not seen again in 4 later runs). The compact-bridge test passes alone and
  with `--test-threads=1`: two sibling tests changed `KM_HT_BRIDGE` without
  the module's environment lock, a race that predates this branch. The final
  commit takes the lock in those two tests.

## Not done

- The incremental probe's join order (item 2, above).
- A quiet-machine timing table and a PGO build.
- Spawn retry for the orchestrator's in-process CB thread and rayon pools.
- No Lean work. None of the changes alters a calculus, an encoding or a
  worker input. The obligations stated in docs/NOMINALS-CB.md section 6 are
  unchanged and not mechanised.
