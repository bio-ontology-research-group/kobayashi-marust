# Cost of checked subset blocking (2026-10-30)

Branch `fix/v155-subset-blocking-cost` from v1.5.4 (80c8f82a). Commits
8565b673 (incremental checked blocking) and 5c7d0bf5 (unit test). Argument:
docs/HYBRID-CB-HT.md section 9, "Cost".

Binaries: `km-v153-pgo`, `km-v154-pgo` (release PGO assets), `km-v154-rel`
(plain `cargo build --release` of the v1.5.4 tag), `km-fix` (plain release
build of 8565b673). Environment of every timing run: `run1.sh` (one core
via `taskset`, the env list of the task, `KM_ROUTE=auto`,
`KM_ROUTING_POLICY=v153`, `KM_TIMING=1`).

## Profile (`profile/`)

`KM_HT_STATS=1` on 7499 (card arm, mode 5), worker time:

| build | steps | blocking passes | block_ms | prop_ms | worker s |
|---|---:|---:|---:|---:|---:|
| v1.5.3 PGO | 654,415 | - | 25,119 | 19,509 | 48.4 |
| v1.5.4 PGO | 1,037,056 | - | 144,858 | 25,039 | 176.4 |
| v1.5.4 + counters (`profile-counters.patch`) | 1,037,056 | 1,025,014 | 175,544 | 29,434 | 212.8 |
| fix | 1,037,056 | 1,025,014 | 30,263 | 28,642 | 66.6 |

Counters on v1.5.4 (7499): 117.7M nodes searched, 117.6M candidates,
112.0M label supersets passing B2a, 112.0M `admits` calls (18.6M false)
taking 94.6 s of the 169 s in `compute_blocked`. So the cost was (a) the
per-pair relevance check (0.85 µs, rebuilding the relevant-set list and
probing every literal of the blocker), times every node on every pass,
since mode 5 has no incremental path. Candidate lists stayed short (about
one candidate per node), so (b) a larger candidate search is not the
cause. Indirect blocking (c) is a linear pass. (d) does not apply to mode
5, which never had an incremental path; for mode 1 the checked path
bypassed `KM_HT_INCRBLOCK2`, which the fix restores in checked form. The
step count (1.04M against 0.65M) is the larger search that the checked
pairs require; it is identical in all post-fix builds, as are the blocking
pass counts. 205 gives the same picture (`prof-205`).

Incremental steps on 7499 (worker s): suffix recompute 118.1, plus
successor-edge refinement and `admits` split 83.9, plus posting log and
cached relevant literals 73.1, plus cached B2a operands 66.6.
`profile-counters-incremental.patch` and `prof2-7499` split the 84 s
build: 47.4M nodes searched, 47.3M `admits` (20.7 s), recompute 55.6 s.

7278 and 3726 are not subset blocking: their time is in the
rules-consistency worker (`tableau.rs` `Tableau`, no `hypertableau.rs`
blocking). v1.5.4 carries 81 data-property assertions as `DataHasValue`
(5a9eaa77), so the worker input grows from 8,074 to 8,552 clauses, and the
frontend runs twice. The v1.5.3 worker on the v1.5.4 input
(`KM_TAB_BIN=tab153.sh`) takes 26.9 s (7278) and 25.4 s (3726), as long as
the v1.5.4 worker (`v154-tab153-*`).

## Exactness checks

- `KM_HT_INCRBLOCK2_CHECK=1` compares every incremental pass with the full
  `compute_blocked` and aborts on a difference: 205 and 7499 ran to the end
  with it (about 1.0M passes each, mode 5) at every step of the change;
  the 700-seed `ht_general` run with it (mode 1) aborted on none.
- Outputs of 205 and 7499 identical to v1.5.4 for every build; the timing
  outputs below are identical across all four binaries (md5).
- Tests (`integration-tests.log`): ht_subset_blocking 4 passed,
  empty_and_universal_data_ranges 10, bridge_generator_soundness 3,
  data_assertions_carried 9, forced_route_fail_closed 5,
  cb_route_completeness 8, universal_role_and_top_data_range 13 passed.
  `--lib cb_to_ht:: tableau::` (`lib-tests-result.txt`): 288 passed, 20
  failed, the same 20 names as at 75dd4d46 (they need the `KM_HT_LEAN_*`
  checkers). New `checked_subset_blocking_incremental_matches_full_scan`
  passes (`lib-newtest.txt`).

## Seed differential (`seeds-*.txt`)

`rerun.py` (copied from results/agents/2026-10-29/ht-card-complement),
700 ALCHIQ seeds, HermiT gold, `KM_ROUTE=ht_general`, 60 s cap.

| run | ok | WRONG | declined | no answer | hermit-error |
|---|---:|---:|---:|---:|---:|
| previous agent, post-fix (75dd4d46, 4 workers, heavy load) | 325 | 0 | 232 | 141 | 2 |
| `km-v154-rel` (2 workers) | 326 | 0 | 235 | 137 | 2 |
| `km-fix` (4 workers) | 326 | 0 | 235 | 137 | 2 |
| `km-fix` + `KM_HT_INCRBLOCK2_CHECK=1` (2 workers) | 326 | 0 | 235 | 137 | 2 |
| intermediate build + check (`seeds-inc2-check.txt`) | 326 | 0 | 235 | 137 | 2 |

Per seed, `km-fix` and `km-v154-rel` agree on all 700. The 137 no-answer
seeds are timeouts on both, as before mostly inverse-role inputs that the
route declines after the worker has run.

## Timing (`timing/table.tsv`, one at a time, one core, wall s)

| input | v1.5.3 PGO | v1.5.4 PGO | v1.5.4 release | fix release | fix / v1.5.4 release |
|---|---:|---:|---:|---:|---:|
| ore_ont_205 | 48.29 | 178.68 | 200.26 | 71.32 | 0.36 |
| ore_ont_7499 | 44.75 | 160.62 | 174.12 | 61.10 | 0.35 |
| ore_ont_7278 | 6.94 | 31.43 | 32.68 | 32.56 | 1.00 |
| ore_ont_3726 | 6.86 | 31.49 | 33.29 | 33.17 | 1.00 |
| ore_ont_10019 | 0.05 | 0.04 | 0.05 | 0.04 | - |
| ore_ont_12107 | 0.04 | 0.04 | 0.04 | 0.04 | - |
| ore_ont_5303 | 0.13 | 0.12 | 0.14 | 0.13 | - |

A PGO build of the fix should land near 0.9 of the release time (v1.5.4:
PGO/release 0.89 and 0.92 on 205 and 7499); that is inferred, not
measured.
