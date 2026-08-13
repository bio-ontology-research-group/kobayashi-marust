# Sequential completion bridge for a large disjunctive SHI terminology

This experiment evaluates a scheduling-only change for very large,
source-certified, disjunctive SHI terminologies. The automatic
`production_all` portfolio runs its complete-answer-or-defer completion bridge
before allocating the unchanged exact CB fallback. Bridge rejection, worker
failure, or explicit defer starts that fallback. No inference rule, frontend
normalization, bridge certificate, CB mechanism, or output mapping changes.

Applying the source predicate to all 592 v0.2.12 profiles selects exactly
`ore_ont_3215.owl`.

## Source-bound candidate

- Source archive SHA-256:
  `6c5fcd4bd17d65b296b725ea1cb1e6362852ea68a1ab1c1fe37ebecbdf4acebd`
- IBEX binary SHA-256:
  `31ecdbc74174e371f1f55805af8de382f517b0ab1960ed81553f6fa249c4bea5`
- Build job: `50440791`
- CPU gate: Intel Xeon Gold 6248
- Limits: 240 seconds, 20 GiB, 16 workers

## ORE3215 paired gate

Job `50440878` ran three alternating v0.2.12/candidate pairs on one node.
Every run matched the frozen Konclude full-IRI signature
`2e629f329a33aae3af87893afb850e383d3aece4e19f6785157d4d8756234f6b`.

| Metric | v0.2.12 baseline | Candidate | Change |
|---|---:|---:|---:|
| Mean wall time | 162.0549 s | 157.3747 s | -2.89% |
| Mean peak memory | 8,499.09 MiB | 6,330.62 MiB | -25.51% |

The gate required all six runs to be checkpointed exact matches, all
signatures to agree, and both candidate mean wall and mean memory to improve.

## Corpus gate

Strict sweep job `50441548` produced exactly 592 results, profiles, and
checkpoints with no temporary files. The binary and CPU identities are uniform.
It reports 591 successful classifications, ORE1194 as the sole fail-closed
error, and zero status, consistency, signature, or coverage regression relative
to v0.2.12.

| Metric | v0.2.12 sweep | Candidate sweep | Change |
|---|---:|---:|---:|
| Mean wall time | 4.5441 s | 4.5871 s | +0.95% |
| Median wall time | 0.2461 s | 0.2491 s | +1.22% |
| Mean peak memory | 503.74 MiB | 499.60 MiB | -0.82% |
| Median peak memory | 42.78 MiB | 41.45 MiB | -3.11% |

The independently scheduled corpus sweep improves both memory aggregates but
contains adverse wall movement. The same-node six-run gate isolates the only
changed ontology and measures a repeatable 2.89% wall reduction together with
the 25.51% memory reduction. Both measurements are retained without
adjustment.

## Reproduction

- `ibex_build_candidate.sbatch`: source-bound IBEX build.
- `ibex_candidate_gate.sbatch`: three-pair same-node gate.
- `ibex_full_sweep.sbatch`: resumable strict 592-ontology sweep.
- `aggregate_strict.py`: validates every result, profile, checkpoint, binary,
  CPU model, and route trace before computing aggregate metrics.
- `compare_release.py`: requires behavior identity with the release sweep.
- `automatic-results.tsv`: all 592 audited automatic-route rows.
- `summary.json`, `strict-audit.out`, and `release-comparison.json`: aggregate
  results and the exact v0.2.12 behavior comparison.
