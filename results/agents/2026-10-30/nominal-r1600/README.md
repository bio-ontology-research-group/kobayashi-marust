# nominal-r1600: merge hypotheses, the nominal-label cache, a ranked R2

Two items of the v1.5.5 brief (agent `nominal-r1600`, branch
`fix/v155-nominal-r1600`). Design and exactness arguments:
docs/NOMINALS-CB.md section 10 (item 1), docs/PER-CONTEXT-ORDERING.md
section 9 (item 2), Lean `lean/ContextCalculus/ExchangeEquality.lean`
(sections `Ranked`, `MaxRanked`).

## Binaries

- `km.v4`: `engine/target/release/km` (`cargo build --release`, non-PGO) at
  merge commit 72b16fb4 (the item fixes on top of `development/v1.5.5` at
  3ae4185d), sha256 `18a8f997b10fe669…`. The committed tree adds only the
  cost-attribution diagnostics `KM_DIAG_EQEQ_OPEN`, `KM_DIAG_EQATOM_OPEN`
  (default off) and comments; `km.diag` is that tree.
- `km.final2`: the tree of 7c238e52 with `KM_CONTEXT_NO_GUARD`, sha256
  `c91bbe3ceab89ccf…` (`.work/agent-scratch/r3-unannounced/km.final2`).
- v1.5.4: `.work/pgo-v154/km-pgo-use`, sha256 `ac15b82272bd22ad…` (PGO).
- Oracle: HermiT 1.4.3.456 through `.work/agent-scratch/r3-unannounced/oracle`
  (cached answers in `.../r3-unannounced/gold`).

Binaries and inputs stay in `.work/agent-scratch/nominal-r1600/` (not
committed). The workstation ran at load 40 to 70 with other agents.

## Scripts

- `runset.sh BIN OUT TIMEOUT THREADS LIST [DIFF_KEEP]`: `diff_run.py` of
  `results/agents/2026-10-30/r3-unannounced/` (route `nominals`) in chunks
  of 100 files (one long argument list hit E2BIG).
- `chk.sh BIN FILE...`: the three nominal routes against the HermiT answer.
- `tc.sh BIN FILE ROUTE CAP ENV...`, `tm.sh BIN JSON CAP ENV...`: wall time
  per diagnostic setting (classify, engine).
- `set60.sh BIN TAG LIST`: forced `nominals`, 60 s, one file at a time.
- `cmp.py NAME TSV ...`: verdict counts and paired times on common seeds.
- `hist.py DUMP`: body/head histogram of a context dump (debug builds only).
- `min/m1.ofn` to `min/m4.ofn`: the minimisation of r1600 (`m4` is the
  fixture `merge_r1600_min.ofn`), with HermiT answers.

## Data (`data/`)

- `diff-v4-rand.tsv`: 4,000 `gen_r3.py` seeds, 10 s, 2 threads (5 worker
  errors rerun, merged). `diff-v4-tpl.tsv`, `diff-v4-tpl2.tsv`: motif sets,
  20 s, 1 thread.
- `diff-v4pair-rand1k.tsv`: seeds r0 to r999 with `KM_CONTEXT_PAIR_R2=1`
  (section-8 R2 and guard, same binary), 1 thread, run beside `diff-v4-rand`.
- `diff-final2-rand-partial.tsv` (724 seeds), `diff-v154-rand-partial.tsv`
  (768 seeds): same-load reruns of km.final2 and v1.5.4, 1 thread each,
  stopped to free threads. The full v1.5.4 and km.final rows are the
  r3-unannounced campaign's (`../r3-unannounced/diff-v154-rand.tsv`,
  `diff-final-rand.tsv`, 8 threads, load 75 to 100).
- `set60-v4.tsv`, `set60-final2.tsv`: the 36 seeds the v1.5.4 rules answered
  and 7c238e52 did not (`../r3-unannounced/pair-slow.tsv`), r673, r3351,
  r129, fr248, at 60 s.
- `times-v4.tsv`, `times-final2.tsv`: the 112 ORE inputs of the paired
  design (`../r3-unannounced/ore-design-nominal.txt`), automatic route,
  300 s, `ore_time.sh`, two streams side by side.
- `timings-*.txt`, `attribution-*.txt`: per-seed timings and the
  diagnostic splits of PER-CONTEXT-ORDERING.md section 11.1.
- `open-seeds-v4.txt`: the four open seeds and the minimised one on three
  routes, 300 s.

## Reproduce

    S=.work/agent-scratch/nominal-r1600
    ./runset.sh $S/km.v4 v4-rand.tsv 10 2 list-rand.txt
    ./runset.sh $S/km.v4 v4pair.tsv 10 1 list-rand1k.txt KM_CONTEXT_PAIR_R2=1
    ../r3-unannounced/ore_time.sh $S/km.v4 ../r3-unannounced/ore-design-nominal.txt ore v4
    python3 -I ../r3-unannounced/ore_cmp.py ore final2 v4

## Results in brief

Verdicts per item are in the hand-back report; the measured numbers:

| set | v1.5.4 | km.final(2) | this branch (km.v4) |
|---|---|---|---|
| open seeds r1600/r1646/r3403/r3602, `nominals` | 4 wrong | 4 wrong | r3403, r3602 ok; r1600, r1646 time out at 300 s |
| open seeds, automatic and `certified_nominals` | r1600 wrong | r1600 wrong | all ok |
| `gen_r3.py` 4,000, 10 s | 2,217 ok, 4 wrong (campaign of r3-unannounced) | 2,205 ok, 4 wrong, 1,761 TO, 30 err (same) | 2,191 ok, 0 wrong, 1,809 TO |
| same-load rerun, first 724 seeds | 416 ok of 768 (1 wrong, r673) | 401 ok | 382 ok |
| motifs m1-m5 (2,000, 20 s) | 1,520 ok, 480 wrong | 1,999 ok, 1 TO | 1,999 ok, 1 TO |
| motifs m6, m7 (1,000, 20 s) | 842 ok, 155 wrong | 997 ok, 3 TO | 997 ok, 3 TO |
| 36 seeds + r673, r3351, r129, fr248, 60 s | | 5 of 36; r129 26 s; others TO | 10 of 36; r129, r673, r3351, fr248 TO |
| ORE paired design, 112, auto, 300 s | | 106 + 0 | 106 identical + 2 (3077, 699) |

Ranked R2 against section-8 R2 in the same binary, seeds r0-r999, 10 s:
531 against 534 ok, both-answered total 190 s against 232 s.

Tests (`data/tests-full-summary.txt`, `--release`, `--test-threads=2`):
3,399 passed, 24 failed, 13 ignored. The 21 lib failures are HT and CB
certificate tests that need the real Lean checkers (`KM_HT_LEAN_*`,
"requires the real Lean checker"); `completion_hot_path_env` (a getenv in
`konclude_ht/completion/u02.rs`) and `source_module_reuse::common_data_core_prefers_plain_module_before_full_common_path`
are in code this branch does not touch; `universal_role_and_top_data_range::data_value_singleton_next_to_nominal_successors`
exceeds its 10 s bound on the "object value" case (`data/dv_obj.ofn`):
v1.5.4 takes 24 s and km.final2 28 s on it at the current load, this
branch 31 s without and more than 60 s with the merge hypotheses.

## After merging development/v1.5.5 at a2e98d95 (2026-10-31)

`km.v6` (sha256 `701b703f68c155c8…`), the branch head merged with
a2e98d95 (data-values-2, lean-rules-route, nominal-seeds):

- Seeds r0-r999, 10 s, 2 threads (`data/diff-v6-rand1k.tsv`): 530 ok, 0
  wrong, 470 timeouts (km.v4: 531 ok, 0 wrong).
- Open seeds: r3403 correct on all routes; r1600 correct on the automatic
  route (22 s); r1646, r3602 correct on the automatic route. On forced
  `nominals`, r3602 now times out at 60 s also with the merge hypotheses
  and the ranked R2 switched off, and so does the nominal-coverage binary
  `km.fixm4` that development merged: a regression of the merged base, not
  of this branch.
- Targeted tests (`data/tests-v6-targeted.txt`): merge_hypotheses 4 of 4
  (after moving r3602's forced route to the ignored test),
  r3_disjunctive_equality 4/4, nominal_seq_order 6/6;
  universal_role_and_top_data_range 11 passed, 2 failed on its 10 s bound:
  the "object value" case (`data/dv_obj.ofn`, v1.5.4 24 s, km.final2 28 s)
  and the hub with data values on `certified_nominals`
  (`data/hub_with_data_values.ofn`: 10 s without, 30 s with the merge
  hypotheses).
- The five seeds the nominal-seeds agent found wrong on the automatic route
  (r1536, r1866, r2408, r2564, r3777; `data/five-auto-seeds.txt`): all five
  are answered correctly by the forced `nominals` route of km.final2; the
  wrong answers come from the HT worker of the typed-nominal bridge, which
  answers first on the automatic route (`route=ht_bridge`) and in the race
  of `certified_nominals` (r2408 is a functional-role merge, `a = d`). This
  is the bridge merging defect of `nominal-seeds/bridge_merge_min.ofn`, not
  the cause of r1600, and this branch does not fix it (r2408 becomes correct
  on `certified_nominals` only). With the merge hypotheses, r1536 and r3777
  time out at 60 s on forced `nominals` (0.3 s and 0.06 s on km.final2).
