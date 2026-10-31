# nominal-exchange: the exchange cut, its proof, and its validation

Agent `nominal-exchange`, branch `fix/v155-nominal-exchange`. Design and
exactness argument: docs/PER-CONTEXT-ORDERING.md section 13; Lean
`lean/ContextCalculus/ExchangeCut.lean`; docs/NOMINALS-CB.md section 10.5.

## Binaries

- `km.x3`: `engine/target/release/km` (`cargo build --release`, LTO, non-PGO)
  at b411722e (the branch merged with development/v1.5.5 at aacd11cb),
  sha256 `987ea9000538b52c…`. All final runs below use it.
- `km.x1`: the branch before the merges (cff365ef), sha256 `a0cf8e7f04d6c512…`
  (`data/x1-rand1k-60.tsv` only).
- `km.v6`: `.work/agent-scratch/nominal-r1600/km.v6` (r1600 branch head, merge
  hypotheses without the cut), `km.final2`:
  `.work/agent-scratch/r3-unannounced/km.final2` (7c238e52 tree, no merge
  hypotheses).
- Fast prototypes `km.cut1` to `km.cut4` (no LTO, `tools/qbuild.sh`) were used
  for the attribution in `data/ct-*.tsv`, `data/lost-cut*.tsv`.
- Oracle: HermiT 1.4.3.456, cached answers in
  `.work/agent-scratch/r3-unannounced/gold`.

Binaries and engine inputs stay in `.work/agent-scratch/nominal-exchange/`.

## Protocol

Every KM run is pinned to one CPU (`tools/one-x3`: `taskset` on CPUs 50 to 55
claimed by lock files, so `available_parallelism` is 1 and the route's
`KM_THREADS=16` is capped to 1), at most three runs at a time
(`tools/drive3.sh`). Forced `nominals` route through `diff_run.py` of
`results/agents/2026-10-30/r3-unannounced/` (`tools/runset.sh`). Host load
varied from 5 to 140 during the day.

## Results (km.x3)

| set | cap | result |
|---|---|---|
| `gen_r3.py` r0-r999 | 60 s | 636 ok, 0 wrong, 364 timeouts |
| of those 364, km.v6 | 60 s | 2 ok (r567 33 s, r696 53 s), 362 timeouts |
| of those 364, km.final2 | 60 s | 18 ok, 346 timeouts |
| `gen_r3.py` 4,000 | 10 s | 2,521 ok, 0 wrong, 1,479 timeouts (km.v4 in the nominal-r1600 campaign, multi-threaded engine: 2,191 ok) |
| motifs m1-m5 (2,000) | 20 s | 2,000 ok |
| motifs m6, m7 (1,000) | 20 s | 1,000 ok |
| open seeds, 3 routes | 300 s | `data/open-x3.tsv`: all ok except r1536, r3777 on forced `nominals` (timeout) |
| ALCHIQ g621, g1014, g1022, auto | 60 s | ok (km.x1 before the merge: missed inconsistency, the defect fixed on development) |
| ORE paired design, 112 nominal inputs, auto, 300 s, one CPU each | | 108 answered by both with identical SUB/UNSAT/CONSISTENT lines, the same 3 timeouts and 1 exit 3 in both; 772 s against 794 s for km.v6, mean ratio x3/v6 1.019, median 1.013 |

The 22 seeds that km.final2 answered and km.v6 lost at 10 s
(`list-lost.txt` of nominal-r1600): 16 answer at 60 s, 6 still time out
(r163, r219, r461, r481, r575, r696; km.final2 answers them in under 2 s).

Attribution seeds, forced `nominals`, 30 s (`data/ct-*.tsv`, before the
merges): r5 30 s+ → 0.2 s, r129 30 s+ → 0.3 s, r1646 30 s+ → 0.8 s, fr248
30 s+ → 14 s, r10 30 s+ → 12 s; r163, r3602, r1600, r1536, r3777, r3351, r673
stayed above 30 s then. After the merges r3602 answers in 0.5 s and r1600 in
224 s (open seeds at 300 s). m2197 (`top_nominal_data_successors`): more than
60 s without the cut, 2.1 s with it.

Tests (`data/tests-targeted.txt`, `--release`): cb_route_completeness 8/8,
merge_hypotheses 6 passed 1 ignored, nominal_seq_order 6/6,
r3_disjunctive_equality 4/4, top_nominal_data_successors 16/16,
universal_role_and_top_data_range 12 passed, 1 failed
(`data_value_singleton_next_to_nominal_successors`, the object-value case on
`nominals`: more than 60 s with and without the cut, 0.4 s without merge
hypotheses; its cost is the ground context's exchange with its own
successor contexts under the merge-hypothesis labels, which the cut does not
touch).

## Reproduce

    N=.work/agent-scratch/nominal-exchange
    tools/build.sh x3          # release build, copies km.x3
    tools/drive3.sh            # seed sets, open seeds, ORE (writes $N/runs, $N/ore)
    python3 -I ../../2026-10-30/r3-unannounced/ore_cmp.py $N/ore v6 x3
