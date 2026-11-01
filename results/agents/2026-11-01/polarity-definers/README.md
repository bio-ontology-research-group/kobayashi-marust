# polarity-definers: Plaisted-Greenbaum encoding of complement definers

Agent `polarity-definers`, branch `fix/v155-polarity-definers` from
`development/v1.5.5` at 775223bf. Design, exactness argument and Lean
statement: docs/NOMINALS-CB.md section 11; note in docs/DATATYPES.md
("Negated value fillers"); Lean `lean/ContextCalculus/PolarityDefiners.lean`.

## Binaries

- `km.base`: `engine/target/release/km` at 775223bf (`cargo build --release
  -j 12 --bin km`), sha256 `e282dfead74f869e…`.
- `km.new`: the same at 2ad4f806 (the frontend pass; later commits change
  tests, docs and results only), sha256 `ba491e86aa0ba034…`.

Both are in `.work/agent-scratch/polarity-definers/` (`$S`). Every KM run is
pinned to one CPU (`tools/pin`: `taskset` on CPUs 24 to 29 claimed by lock
files) with `KM_THREADS=1`, at most three runs at a time.

## The test case

`data/objvalue.ofn` is the "object value instead of data value" case of
`data_value_singleton_next_to_nominal_successors`, and `data/datavalue.ofn` is
its data-value twin. Wall time, one CPU:

| case | route | base | new |
|---|---|---:|---:|
| object value | `nominals` | over 60 s | 0.04 s |
| object value | `certified_card_proxy_abox` | over 60 s | 0.03 s |
| object value | `nominal_ni_abox` | 20.1 s | 0.03 s |
| object value | auto, `certified_nominals` | 0.02 s | 0.02 to 0.03 s |
| data value | all five | 0.02 s | 0.02 s |

All runs answer consistent, with no unsatisfiable class and no subsumption,
which is the hand-derived answer.

## Tests (`--release`, `KM_THREADS=1`)

- `data/tests-integration.txt` (`--test-threads=3`): universal_role_and_top_data_range
  13 passed (was 12 passed, 1 failed on the base), native_data_values 30,
  top_nominal_data_successors 16, merge_hypotheses 6 passed 1 ignored,
  nominal_seq_order 6, cb_route_completeness 8, rule_taxonomy_nominal 9,
  source_module_reuse 38, incremental_ht_reasoning 6. No failures.
- `data/lib-frontend.txt`: `frontend::` 428 passed (424 plus the four new
  `polarity_definer_tests`); `data/lib-engine.txt`: `engine::` 67 passed,
  1 ignored.
- No test fails on this branch that passes on the base.

## Frontend differential (`tools/fe_one.sh`, `data/fe-ore.tsv`)

`km ofn` with both binaries on the 1,094 ORE design-half inputs of the
checkers-on suite (`results/agents/2026-10-30/checkers-on-suite/inputs/ore.tsv`),
under three settings. Columns: input, setting, clause sha (base, new), meta
sha (base, new), bytes (base, new), seconds (base, new).

| setting | inputs | clause file changed | meta changed |
|---|---:|---:|---:|
| default | 1,094 | 79 | 0 |
| `KM_NOMINALS=1` | 1,094 | 79 | 0 |
| `KM_ABSORB=1` | 1,094 | 23 | 0 |

The 23 changed under absorption are a subset of the 79. On the 25 smallest
changed inputs, `tools/fe_struct.py` shows that the new clause set is the
old one minus excluded middles (1 to 8 per input) and with complement
constraints rewritten (0 to 5 per input), with no other difference.

Answers (`tools/ore_cls.sh`, `data/ore-cls.tsv`): the 79 changed inputs,
automatic route, `KM_THREADS=1`, 240 s, one CPU, both binaries. All 79 are
answered by both, with identical sorted `SUB`/`UNSAT`/`CONSISTENT`/`DROPPED`
lines. Total 889.4 s base, 766.1 s new.

## Seeds against HermiT

Forced `nominals` and auto: `tools/runset.sh` (the `diff_run.py` of
`.work/agent-scratch/r3-unannounced/tools`, cached HermiT answers in
`r3-unannounced/gold`). Data-value pools: `tools/dataset.sh` (the pools of
`forced-nominal-data-misses`, `results/agents/2026-10-30/data-values-3/scripts/diff_run.py`).

| set | route | cap | new | previous table |
|---|---|---|---|---|
| `gen_r3` r0-r999 | `nominals` | 60 s | 639 ok, 0 WRONG, 361 TIMEOUT | 636 ok (km.x3) |
| `gen_r3` 4,000 | `nominals` | 10 s | 2,521 ok, 0 WRONG, 1,479 TIMEOUT | 2,521 ok (km.x3) |
| `gen_r3` 4,000 | auto | 10 s | 3,795 ok, 0 WRONG, 205 TIMEOUT | |
| data probes (38) | auto, certified_nominals, nominals | 60 s | 103 ok, 11 TIMEOUT, 0 WRONG | 103 ok, 11 TIMEOUT |
| reduction fixtures (14) | same three | 60 s | 42 ok | 42 ok |
| top-nominal-data seeds (87) | same three | 60 s | 226 ok, 35 TIMEOUT, 0 WRONG | 224 ok, 37 TIMEOUT |
| m2000-m2399 | nominals, certified_nominals | 30 s | 552 ok, 248 TIMEOUT, 0 WRONG | 535 ok, 265 TIMEOUT |
| m2000-m2399 | auto | 60 s | 385 ok, 15 TIMEOUT, 0 WRONG | 380 ok, 20 TIMEOUT |
| r3-unannounced seeds with data (300) | auto | 30 s | 284 ok, 16 TIMEOUT, 0 WRONG | 281 ok, 19 TIMEOUT |
| nominal-r1600 seeds with data (400) | auto | 30 s | 380 ok, 20 TIMEOUT, 0 WRONG | 380 ok, 20 TIMEOUT |

How many inputs the pass changes (`km ofn` under `KM_NOMINALS=1`, base
against new): none of the 4,000 `gen_r3` seeds; 0 of 38 probes, 2 of 14
fixtures, 127 of 400 m-seeds, 82 of 300 r3 data seeds, 87 of 400 r1600 data
seeds. The `gen_r3` seed runs therefore re-measure an unchanged engine input.

## Named seeds on forced `nominals` (`tools/timing.sh`, `data/timing-*.tsv`)

r163, r219, r461, r481, r575 and r696 (60 s), r1536 and r3777 (300 s): no
answer with either binary (60 s each; r1536 and r3777 stop at 235 s with
exit 124 under both). Their frontend output is byte-identical between the
binaries, so the pass cannot affect them; their cost is the merge
hypotheses of docs/NOMINALS-CB.md section 10.4.

## Reproduce

    S=.work/agent-scratch/polarity-definers
    # build km at 775223bf and at the branch head, copy to $S/km.base, $S/km.new
    xargs -P 3 -n 1 tools/fe_one.sh < ore-list.txt > fe-ore.tsv
    tools/master.sh     # tests, ORE answers, timings, seeds (tools/master2.sh: the order used)
