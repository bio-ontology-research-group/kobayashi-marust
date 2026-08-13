# EL bottom/disjointness routing candidate

Candidate `2a32741` extends the source-certified ELC route to OWL EL class
bottom and named-class disjointness. The normalized cert-off ELC screen remains
the authoritative worker gate; bottom roles remain excluded.

The candidate builds from the source archive whose SHA-256 is
`2e335345b7a6ea17edda2c13e1f91da9e767c359e7654b3ef902ea8b53c15bc8`.
IBEX build job `50085854` produced binary SHA-256
`d8fd398d79e044e1daada75dff9812960de72bf2dca94399bf4836a1c0bab7b6`.

Local release-target checks before the IBEX build:

- 27 routing tests passed.
- Issue #3 `nominal_enumeration_equality_reports_inconsistent` passed.
- The complete locked release suite passed: 1,959 tests passed, eight were
  intentionally ignored, and none failed.

Profile job `50086049` completed with 592 profiles, 592 checkpoints, and no
temporary files. Relative to `e9cb3d1`, exactly 60 ontologies changed from
`production_all` to `elc`; `route-delta.tsv` records the source-level reason
for each. Relative to v0.2.6, `route-delta-v026.tsv` records exactly 98 such
changes, including the 38 positive-EL ABox candidates.

Paired Gold-6248 job `50087236` classified all 60 newly changed ontologies with
both binaries, reversing arm order by array parity. Its strict aggregate found
60 semantically identical pairs, 120 terminal checkpoints, no temporary files,
and no failures:

| Metric | e9cb3d1 | 2a32741 |
|---|---:|---:|
| Mean wall time | 6.9095 s | 4.3882 s |
| Median wall time | 3.1589 s | 1.6223 s |
| Mean peak RSS | 1,099.38 MiB | 422.95 MiB |
| Median peak RSS | 670.12 MiB | 149.39 MiB |

`paired-results.tsv` and `panel-summary.json` retain the accepted paired
evidence.

Strict 592-ontology fixed-hardware sweep `50087884`, with final debug-partition
task `50091562`, completed on Intel Xeon Gold 6248 CPUs. The aggregate contains
592 result/checkpoint pairs, no temporary files, 591 successful
classifications, and ORE1194 as the sole fail-closed error. The exact v0.2.6
comparison found zero coverage regressions, zero semantic regressions, and all
98 expected `production_all` to `elc` route changes.

| Metric | v0.2.6 | 2a32741 | Change |
|---|---:|---:|---:|
| Mean wall time | 5.1787 s | 4.9971 s | -3.51% |
| Median wall time | 0.2467 s | 0.2736 s | +10.90% |
| Mean peak RSS | 720.08 MiB | 597.87 MiB | -16.97% |
| Median peak RSS | 42.02 MiB | 42.14 MiB | +0.29% |

The candidate therefore passes every correctness and coverage gate and makes
large mean-memory progress, but this sweep does not pass the four-metric
release gate because both measured medians increased. The independent strict
fixed-hardware sweep is still running to determine whether the median movement
is repeatable. `automatic-results.tsv`, `summary.json`, and
`comparison-v026.json` preserve the completed authoritative evidence. No
release claim is made from this run.
