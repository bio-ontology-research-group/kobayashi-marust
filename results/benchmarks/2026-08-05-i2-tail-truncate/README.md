# Blocking posting-list tail truncation

Commit `07b8526` replaces a full `retain` scan of every touched incremental
subset-blocking posting list with `partition_point` plus `truncate`. Nodes enter
each posting list in increasing ID order, so entries invalidated by suffix
recomputation form one contiguous tail. This changes neither the retained
entries nor the blocking result.

The complete release suite passed: 1,952 library tests passed, eight were
ignored, and all binary, integration, and documentation tests passed. A debug
focused run also exercised the posting-list sortedness assertion. This is a
data-structure operation improvement, not a calculus or scheduling change, so
it does not require Lean re-certification.

## Alternating ORE6934 pair

IBEX build job `50047977` produced candidate binary SHA-256
`631af3586f0aac6ec5f4025ea70e9b818f2e8cba64e1417ad69fbdafa74d5439`.
Pair job `50047978` ran three alternating repetitions against the source-bound
`02e6200` baseline binary, SHA-256
`3acef3c43d46b69a6ce9cd9b7d4f6ef4508ed74d8b8f1e92c31eac7ce04e9219`,
on one exclusive Intel Xeon Gold 6248 node.

| Arm | Wall seconds | Peak KiB |
|---|---:|---:|
| Baseline 1 | 120.76 | 3,348,932 |
| Candidate 1 | 116.16 | 3,348,864 |
| Baseline 2 | 125.45 | 3,346,236 |
| Candidate 2 | 114.74 | 3,345,536 |
| Baseline 3 | 127.66 | 3,347,656 |
| Candidate 3 | 115.44 | 3,351,004 |
| **Baseline mean** | **124.623** | **3,347,608** |
| **Candidate mean** | **115.447** | **3,348,468** |

Mean wall improved by 9.177 seconds, or 7.36%. Mean peak RSS changed by
+860 KiB (+0.026%), which is measurement-neutral. All six outputs had SHA-256
`9d58abe4db62956241a0de0b0cf6bad39d48fc36c1afc07a07bcf8b19981e0a2`.
The strict audit checked both binary identities, all six timing receipts and
zero exit codes, and all six output digests.

The candidate source archive has SHA-256
`02f6eca1ebc7289dcd0fabe14a09fccd5a07be7d1901e89570b721cc5114b087`.
[`ibex_build_07b8526.sbatch`](ibex_build_07b8526.sbatch) and
[`ibex_6934_pair.sbatch`](ibex_6934_pair.sbatch) reproduce the build and pair.
Sanity job `50049899` and source-bound production arrays `50049893` and
`50049894` use [`ibex_sweep_07b8526.sbatch`](ibex_sweep_07b8526.sbatch).
They completed at
`/ibex/scratch/hohndor/km/release-07b8526-auto-20260805`. The strict audit
verified all 592 terminal rows, checkpoints, profiles, production route traces,
task-to-ontology identities, exact binary hashes, completion logs, and
collision-sensitive full-IRI fingerprints, with no temporary artifacts. Every
route and semantic result matched the `02e6200` sweep.

Coverage remained 591/592: 591 successful rows and the existing ORE1194 error.
Verdicts remained 588 matches, the established consistency disagreements on
ORE2669 and ORE15516, one no-gold row (ORE10860), and ORE1194's error. Across
the 591 paired successes, mean wall fell from 5.8006 to 5.7865 seconds (0.24%)
and median wall from 0.2538 to 0.2516 seconds (0.87%). Mean peak RSS fell from
819.95 to 819.58 MiB (0.05%), and median peak fell from 42.77 to 42.12 MiB
(1.52%). The complete result table is
[`automatic-results.tsv`](automatic-results.tsv).
