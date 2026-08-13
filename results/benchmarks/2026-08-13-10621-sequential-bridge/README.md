# Sequential certified bridge for large typed ABoxes

This experiment evaluates a scheduling-only change to the automatic
`certified_nominals` portfolio. For source-certified typed object ABoxes with
at least 30,000 logical axioms and 100,000 concept expressions, KM runs the
complete-answer-or-defer Konclude completion bridge before allocating the exact
nominal-aware CB fallback. A bridge rejection, worker failure, or explicit
defer starts the unchanged CB procedure. Smaller typed-ABox ontologies retain
the concurrent portfolio.

Applying this predicate to all 592 source profiles from both the v0.2.11 sweep
and its preceding source-profile sweep selects exactly `ore_ont_10621.owl`.

No inference rule, frontend normalization, bridge certificate, CB fallback, or
output mapping changes.

## Source-bound candidate

- Source archive SHA-256:
  `7a8d4307524e80b704cb5da35b03d6e71a27022d096181681d6df0a44e7f8f84`
- IBEX binary SHA-256:
  `21263bc18a61fddf15c4a2b0c71f9e2a06051b1c916227e15efd246534b677ee`
- Build job: `50438393`
- CPU gate: Intel Xeon Gold 6248
- Limits: 240 seconds, 20 GiB, 16 workers

The first attempted deployment used the workstation binary and failed before
classification because IBEX lacks glibc 2.39. The harness recorded that failed
attempt under `failed-workstation-abi/`; it is not a benchmark observation.
The candidate was then rebuilt from the hashed source archive by Slurm on an
IBEX compute node.

## ORE 10621 paired gate

Job `50438534` ran three alternating baseline/candidate pairs on one node. Every
run matched the Konclude full-IRI signature
`cb490ae3d086535d4ef467ed5277e5f497e221d84a79a70fb0dc87afb8a45ccf`.

| Metric | v0.2.11 baseline | Candidate | Change |
|---|---:|---:|---:|
| Mean wall time | 87.1031 s | 86.6274 s | -0.55% |
| Mean peak memory | 9,368.57 MiB | 1,256.15 MiB | -86.59% |

The gate required all six runs to be gold-exact, all signatures to agree,
candidate wall time to remain within 3% of baseline, and candidate memory to
fall below 25% of baseline.

## Corpus gate

The resumable strict sweep used jobs `50438700`, `50439574`, and `50439604`.
It produced exactly 592 results, profiles, and checkpoints, no temporary
outputs, and the expected binary and CPU identities. The result is 591
successful classifications, with ORE1194 the sole fail-closed error. Exact
comparison with v0.2.11 found zero status, consistency, signature, or coverage
regressions.

| Metric | v0.2.11 sweep | Candidate sweep | Change |
|---|---:|---:|---:|
| Mean wall time | 4.5079 s | 4.5441 s | +0.80% |
| Median wall time | 0.2475 s | 0.2461 s | -0.57% |
| Mean peak memory | 517.05 MiB | 503.74 MiB | -2.57% |
| Median peak memory | 42.27 MiB | 42.78 MiB | +1.21% |

The independently scheduled corpus sweep therefore confirms the large mean
memory reduction but contains adverse mean-wall and median-memory movement.
The same-node six-run gate isolates the only changed ontology and measures a
0.55% wall reduction together with the 86.59% memory reduction. Both sets of
measurements are retained without adjustment.

## Reproduction

- `ibex_build_candidate.sbatch`: source-bound IBEX build.
- `ibex_route_panel.sbatch`: released-route discovery panel.
- `ibex_candidate_gate.sbatch`: three-pair same-node gate.
- `ibex_full_sweep.sbatch`: resumable strict 592-ontology sweep.
- `aggregate_strict.py`: validates every row, checkpoint, profile, binary hash,
  CPU model, and route trace before producing aggregate metrics.
- `automatic-results.tsv`: all 592 audited automatic-route rows.
- `summary.json`, `strict-audit.out`, and `release-comparison.json`: aggregate
  results and the exact v0.2.11 behavior comparison.
