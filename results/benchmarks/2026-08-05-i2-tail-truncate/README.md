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
The arrays are dependency-queued behind the `02e6200` corpus sweep. A complete
strictly audited 592-ontology result remains required before release.
