# objvalue-cost: Pred premises on composite edges, least-key subsumption postings

Agent `objvalue-cost`, branch `fix/v155-objvalue-cost` (base bb3fb9a0).
Design, exactness arguments and the remaining root cause:
docs/PER-CONTEXT-ORDERING.md section 15; Lean
`lean/ContextCalculus/CBPredResolving.lean`.

## Binaries

- `km.base`: `cargo build --release` at bb3fb9a0 (development/v1.5.5 after
  the nominal-exchange merge), sha256 `bf211f4cbe44d32d…`.
- `km.f2`: the same build at f6b3fe6a (the two exact changes, 15.2 and 15.3;
  the unit-bridge restriction of 15.4 reverted), sha256 `a13b58aa907d86f1…`.
- Oracle: HermiT 1.4.3.456, cached answers in
  `.work/agent-scratch/r3-unannounced/gold`.

Binaries, profiles and intermediate engine inputs stay in
`.work/agent-scratch/objvalue-cost/`.

## Protocol

Every KM run is pinned to one CPU (`tools/one-f2`: `taskset` on CPUs 44 to 46
claimed by lock files, so `available_parallelism` is 1), at most three runs at
a time, `KM_THREADS=1`. Differential runs go through `diff_run.py` of
`results/agents/2026-10-30/r3-unannounced/` (`tools/runset.sh`, `tools/drive.sh`)
over the seed lists of `results/agents/2026-10-31/nominal-exchange/`. The host
was shared with the v1.5.5 preview PGO build and benchmark reproductions, so
times of the 10 s sets carry noise; the baseline rows are the `km.x3` runs of
the nominal-exchange agent (same lists, same caps, CPUs 50 to 55).

## Results (km.f2)

| set | route | cap | km.f2 | baseline (km.x3) |
|---|---|---|---|---|
| `gen_r3.py` r0-r999 (`data/f2-rand1k-60.tsv`) | nominals | 60 s | 679 ok, 0 wrong, 321 timeouts | 636 ok, 0 wrong, 364 timeouts |
| `list-rand.txt`, 4,000 seeds (`data/f2-rand-10.tsv`) | nominals | 10 s | 2,615 ok, 0 wrong, 1,385 timeouts | 2,521 ok, 0 wrong, 1,479 timeouts |
| `list-rand.txt`, 4,000 seeds (`data/f2-rand-auto-10.tsv`) | auto | 10 s | 3,810 ok, 0 wrong, 190 timeouts | not run |

Transitions against the baseline: at 60 s, 44 timeouts become ok and one ok
(r621, 47.4 s) becomes a timeout; at 10 s, 133 timeouts become ok and 39 ok
become timeouts (their baseline times: 3.2 to 10.0 s, median 6.6 s, six under
5 s). Summed time over the inputs both binaries answer: 0.72 of the baseline
at 60 s (635 inputs), 1.16 at 10 s (2,482 inputs, mostly sub-second runs
taken under heavier host load). No wrong answer in any set.

## The test case and the eight seeds

`data/ov.ofn` is the object-value case of
`data_value_singleton_next_to_nominal_successors`; the seeds are the eight
inputs of docs/PER-CONTEXT-ORDERING.md section 14.5 that the nominal-exchange
agent left open. `tools/ctime.sh`, forced `nominals` route, one pinned CPU
(`data/before-*.tsv`, `data/after-*.tsv`):

| input | km.base | km.f2 |
|---|---|---|
| ov | 60 s timeout | 60 s timeout |
| r163, r461, r481, r575, r696 | 60 s timeout | 60 s timeout |
| r219 | 60 s timeout | 2.15 s ok |
| r1536 | 235 s timeout | 235 s timeout |
| r3777 | 235 s timeout | 0.05 s ok |

The case itself stays open: its cost is the excluded middle of the `¬{e}`
definer (section 15.4), which the frontend polarity encoding of agent
`polarity-definers` removes.

## Tests

- `engine::tests::composite_edge_pred_resolves_premises_and_copies_labels`
  (15.2) and `engine::tests::forward_subsumption_postings_match_a_full_scan`
  (15.3, 3,000 random insertions and removals against a full scan).
- Lean: `lake build ContextCalculus.CBPredResolving`; axioms of
  `providerPlanResolving_sub`: `propext`; of
  `providerPlanResolving_none_of_premise`: `propext`, `Quot.sound`.
