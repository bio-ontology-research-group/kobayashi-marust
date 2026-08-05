# v0.2.5 source-bound ORE baseline

This directory records the fixed-hardware baseline used for performance work
after the v0.2.5 nominal-enumeration soundness release.

## Provenance

- Release: `v0.2.5`
- Source revision: `408dee4`
- Source archive SHA-256:
  `e96598abe3dbf73cd8831b1cc1b5b227d53c93bc4ef7c6cb6a4618f114833a80`
- Source-bound build job: `50071949`
- Binary SHA-256:
  `4812d656144b4b822523acf97d6500238391aff5912078868535604f1aef22b1`
- Complete automatic-route sweep: job `50072086`
- Hardware: Intel Xeon Gold 6248, 16 workers, 240-second timeout, 20 GiB
  reasoner memory cap

The sweep script binds every result to the ontology index and binary hash,
requires a terminal checkpoint and production route trace, and resumes only
from a result/profile pair that passes those checks. The strict aggregator also
requires exactly 592 unique results, profiles, and checkpoints, indices 0–591,
one binary and CPU model, and no temporary output.

## Results

The audit accepted all 592 rows. KM completed 591 classifications. The verdicts
are 588 Konclude-signature matches, the two known consistency adjudications,
one ontology without a Konclude gold signature, and ORE1194 failing closed.

| Metric | v0.2.5 |
|---|---:|
| Mean wall time | 5.7632 s |
| Median wall time | 0.2489 s |
| Mean peak RSS | 780.74 MiB |
| Median peak RSS | 42.76 MiB |

[`automatic-results.tsv`](automatic-results.tsv) contains the 592 per-ontology
rows and has SHA-256
`9cf68ebe61e00709c8d30678f572378dfee8b2f8ebc982f8b688ec55c768c7e2`.
[`summary.json`](summary.json) contains the machine-readable aggregate.
