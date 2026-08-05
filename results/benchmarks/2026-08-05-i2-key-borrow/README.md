# Borrow blocking keys without a temporary vector

Commit `5bd9489` splits the immutable node-concept borrow from the mutable
incremental-blocking posting-list borrows. The registration loop can therefore
iterate concept keys directly instead of allocating and copying one temporary
`Vec<CLit>` for every unblocked node. It inserts the same keys in the same
iteration order and changes neither blocking nor reasoning.

The complete release suite passed: 1,952 library tests passed, eight were
ignored, and all binary, integration, and documentation tests passed. The
focused hypertableau filter passed 90 tests. This allocation optimization does
not change calculus rules or scheduling and requires no Lean re-certification.

The source archive has SHA-256
`91f2e84a36637e65755333412aabdf7b1938677e168a6eac4ac3dc7c97c8a4fc`.
IBEX build job `50050792` produced candidate binary SHA-256
`a16f97f899854c5153ff20ef0f318a813a3be159d269efb13e16d9594dcf62d2`.
Alternating ORE6934 pair job `50050793` compared it with the source-bound
`07b8526` baseline binary, SHA-256
`631af3586f0aac6ec5f4025ea70e9b818f2e8cba64e1417ad69fbdafa74d5439`,
on one exclusive Intel Xeon Gold 6248 node.

| Arm | Wall seconds | Peak KiB |
|---|---:|---:|
| Baseline 1 | 114.85 | 3,347,396 |
| Candidate 1 | 113.24 | 3,348,456 |
| Baseline 2 | 115.34 | 3,347,204 |
| Candidate 2 | 111.24 | 3,330,688 |
| Baseline 3 | 116.54 | 3,345,140 |
| Candidate 3 | 113.56 | 3,349,512 |
| **Baseline mean** | **115.577** | **3,346,580** |
| **Candidate mean** | **112.680** | **3,342,885** |

Mean wall improved by 2.897 seconds, or 2.51%, and mean peak RSS fell by
3,695 KiB (0.11%). All six outputs had SHA-256
`9d58abe4db62956241a0de0b0cf6bad39d48fc36c1afc07a07bcf8b19981e0a2`.
The strict audit checked both binary identities, all six timing receipts and
zero exit codes, and all six output digests.

Sanity job `50051037` and source-bound production arrays `50051038` and
`50051039` use [`ibex_sweep_5bd9489.sbatch`](ibex_sweep_5bd9489.sbatch).
They completed at
`/ibex/scratch/hohndor/km/release-5bd9489-auto-20260805`. The strict audit
verified all 592 terminal rows, checkpoints, profiles, production route traces,
task-to-ontology identities, exact binary hashes, completion logs, and
collision-sensitive full-IRI fingerprints, with no temporary artifacts. Every
route and semantic result matched the `07b8526` sweep.

Coverage remained 591/592: 591 successful rows and the existing ORE1194 error.
Verdicts remained 588 matches, the established consistency disagreements on
ORE2669 and ORE15516, one no-gold row (ORE10860), and ORE1194's error. Across
the 591 paired successes, mean wall moved from 5.7865 to 5.7993 seconds
(+0.22%) and mean peak RSS fell from 819.58 to 818.65 MiB (0.11%). Median wall
moved from 0.2516 to 0.2536 seconds (+0.79%), and median peak moved from 42.12
to 43.33 MiB (+2.87%). These independently scheduled sweeps are noisier than
the alternating source-isolated pair and do not establish a corpus-wide speed
change. The complete result table is
[`automatic-results.tsv`](automatic-results.tsv).

[`ibex_build_5bd9489.sbatch`](ibex_build_5bd9489.sbatch) and
[`ibex_6934_pair.sbatch`](ibex_6934_pair.sbatch) reproduce the build and pair.
