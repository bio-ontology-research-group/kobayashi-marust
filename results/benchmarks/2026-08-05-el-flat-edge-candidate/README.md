# Rejected sorted-flat EL edge storage

Candidate `2624799` replaced each EL completion state's outgoing-edge hash set
with a sorted flat vector. Binary-search insertion, lookup, and removal retained
exact set semantics, but the representation did not improve ORE resource use.
The change was reverted and was not released.

## Provenance

- Candidate source revision: `2624799`
- Source archive SHA-256:
  `66d9c33b3720f1bd6be3cdde465a2a8db3852282c2d98476a4847770c0d5b796`
- Source-bound build job: `50072830`
- Candidate binary SHA-256:
  `8f4a8ca4617be1039614b85de9a2ebb2c11e49cc14e7f9d9a444c250f88a315a`
- Baseline release: `v0.2.5`, revision `408dee4`
- Baseline binary SHA-256:
  `4812d656144b4b822523acf97d6500238391aff5912078868535604f1aef22b1`
- Same-node Gold-6248 panel: job `50073304`

The first submission, job `50073208`, identified a missing route-capture option
in the panel harness and produced no accepted pair. Job `50073304` used the
corrected harness. It alternated binary order and required identical status,
verdict, consistency, signature, subsumption count, and unsatisfiable-class
count before accepting a pair.

## Result

Seven pairs completed with identical semantics, including ORE8486 through the
exact `elc` route and ORE1194 as the failure-mode control. The candidate was
slower while its memory change was negligible:

| Metric over six successful pairs | v0.2.5 | Candidate | Change |
|---|---:|---:|---:|
| Mean wall time | 100.2998 s | 101.5121 s | +1.21% |
| Median wall time | 109.9128 s | 112.1416 s | +2.03% |
| Mean peak RSS | 7412.45 MiB | 7404.55 MiB | −0.11% |
| Median peak RSS | 9149.67 MiB | 9122.60 MiB | −0.30% |

On the directly affected ORE8486 `elc` route, wall time increased from 34.2312
to 34.8570 seconds while peak RSS changed from 1532.70 to 1532.66 MiB. The
remaining panel tasks were cancelled after this decisive negative result.

[`paired-results.tsv`](paired-results.tsv) contains the accepted pairs,
[`summary.json`](summary.json) contains the aggregate, and [`raw/`](raw/)
contains both source rows for every accepted pair.
