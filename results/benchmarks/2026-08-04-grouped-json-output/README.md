# Grouped JSON taxonomy output

Commit `115b09b` keeps full-IRI taxonomy rows grouped through the normal JSON
CLI and serializes each row directly. The public `Classification` API,
explanation path, mirror reconstruction, and `--lines` output retain their
existing flat representation. The change does not affect calculus rules,
saturation, routing, or the derived taxonomy.

The complete workstation release suite passed with 1,950 library tests, eight
ignored tests, and every integration and documentation suite passing. A unit
regression proves byte identity between grouped and flat serialization,
including duplicate pairs. End-to-end JSON and `--lines` output on
`rule_consistent.ofn` were byte-identical to the `c3c3d24` binary.

The exact source archive has SHA-256
`9302f5010bac0c63a87cfc7442183bfe1893fe4c8a12c6fa0d2e82700729b2ca`.
IBEX build job `50031508` produced candidate binary SHA-256
`cf51bffdae6cef6bea40e66ad0893abe677bf3785a81e512e4c551d888abe9c3`.

## Dense-output A/B

Job `50031609` alternated the source-bound candidate with the exact
`c3c3d24` production binary on ORE9674. Each run wrote the complete JSON to a
node-local file before hashing it.

| repetition | `c3c3d24` wall | candidate wall | `c3c3d24` peak KiB | candidate peak KiB |
|---:|---:|---:|---:|---:|
| 1 | 42.74 s | 42.35 s | 4,016,476 | 2,883,160 |
| 2 | 42.97 s | 42.37 s | 4,016,048 | 2,882,436 |
| 3 | 42.74 s | 42.36 s | 4,016,644 | 2,881,572 |
| **mean** | **42.817 s** | **42.360 s** | **4,016,389** | **2,882,389** |

Mean wall improved by 1.07%. Mean peak RSS fell by 1,134,000 KiB, or
1.081 GiB (28.23%). All six complete outputs had SHA-256
`152cdf0863750e3c94ac3faeb1764fe31a52935db73069bb48a5a8b6d2cd9184`.

## Full automatic-route sweep

Source-bound production arrays `50033013` and `50033014` completed all 592
ontology indices with resumable per-ontology checkpoints. The strict audit
verified 592 unique terminals, checkpoints, profiles, and completion logs;
exact ontology and array-index coverage; the pinned binary on every row; route
traces; expected failure captures; no temporary artifacts; and the
collision-sensitive full-IRI fingerprints for ORE3524, 13503, 4669, and 15703.

Coverage remained 591/592: 591 `ok` rows and the existing ORE1194 error. The
verdicts are 588 matches, the two established consistency disagreements on
ORE2669 and ORE15516, one no-gold row (ORE10860), and ORE1194's error. Every
semantic field and selected route is identical to the accepted `c3c3d24`
sweep.

Across the 591 paired successes, mean peak RSS fell from 830.96 to 823.95 MiB
(0.84%) and median peak fell from 43.07 to 41.79 MiB (2.97%). Mean wall moved
from 5.8301 to 5.8558 seconds (+0.44%) and median wall from 0.2526 to 0.2523
seconds (-0.12%); these corpus timings are scheduler-noisy, so the alternating
ORE9674 pair above is the source-isolated speed evidence. The complete result
table is [`automatic-results.tsv`](automatic-results.tsv).
