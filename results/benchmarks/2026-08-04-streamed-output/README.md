# Stream final classification JSON

## Change

`km classify` previously called `Classification::to_json()`, which serialized
the complete final taxonomy into a second `Vec<u8>` before copying it to
stdout. Dense outputs therefore kept the owned classification and a whole JSON
copy alive together.

The CLI now serializes with the same Python-compatible `PyFmt` formatter
directly into the locked stdout stream. The allocation-returning `to_json()`
API remains available and delegates to the new streaming method. This changes
neither classification contents nor ordering, and it does not touch the
calculus or saturation fixpoint. No Lean re-certification is required.

## Focused validation

A regression test checks byte identity between the streaming and allocating
APIs. The complete release suite passed with 1,949 library tests, eight ignored
library tests, and every integration and documentation suite passing. The
source-bound archive had SHA-256
`e836eb66541155b42d74a84bcf51f5bdab4c9beaedb41b0b0a9d20b5ed06d0e8`.
IBEX build job `50026984` produced binary SHA-256
`3b78da472c1037964378b0a448af04c26c0765e84800937e86c142106f4f5f78`.
Paired job `50026985` ran on an Intel Xeon Gold 6248 node and streamed each
complete classification into SHA-256.

| repetition | `6600efe` wall | candidate wall | `6600efe` peak KiB | candidate peak KiB |
|---:|---:|---:|---:|---:|
| 1 | 46.64 s | 44.64 s | 5,480,268 | 4,016,092 |
| 2 | 46.47 s | 44.77 s | 5,479,956 | 4,016,324 |
| 3 | 46.36 s | 44.79 s | 5,479,572 | 4,017,068 |
| **mean** | **46.490 s** | **44.733 s** | **5,479,932** | **4,016,495** |

Mean wall improved by 3.78%. Mean peak RSS fell by 1,463,437 KiB (26.7%), or
1.396 GiB. All six outputs had SHA-256
`152cdf0863750e3c94ac3faeb1764fe31a52935db73069bb48a5a8b6d2cd9184`.

## Buffered file-backed validation

The CLI wraps the locked stdout stream in a bounded `BufWriter`, preventing
serde's small writes from reaching a file or pipe individually. A second
source-bound build used archive SHA-256
`b4c7127c472784d6be731c2c21ecfe5bf0037581f8dca972b8eb04ede98830f6`.
Build job `50029770` produced binary SHA-256
`a0400ac6678755c08d2478daddcf1c2e7341eae82e5a39ff7d6e0da9ab15c736`.
Job `50029868` wrote each complete output to a node-local file before hashing
it, matching the production redirection shape more closely.

| repetition | `6600efe` wall | buffered candidate wall | `6600efe` peak KiB | buffered candidate peak KiB |
|---:|---:|---:|---:|---:|
| 1 | 44.07 s | 44.59 s | 5,479,896 | 4,016,824 |
| 2 | 44.32 s | 43.03 s | 5,480,504 | 4,015,680 |
| 3 | 44.25 s | 43.16 s | 5,479,892 | 4,015,904 |
| **mean** | **44.213 s** | **43.593 s** | **5,480,097** | **4,016,136** |

Mean wall improved by 1.40%, while mean peak RSS again fell by 1.396 GiB
(26.7%). All outputs retained the same SHA-256 as the pipe-backed experiment.

## Complete production sweep

Commit `c3c3d24` was archived with SHA-256
`b01764d009aac6301a108a2e175438e87a00f8528a314fedde2c72dae3e6ebed`.
IBEX build job `50029950` produced binary SHA-256
`a0400ac6678755c08d2478daddcf1c2e7341eae82e5a39ff7d6e0da9ab15c736`.
Sanity job `50029951` completed ORE10860, and exclusive arrays `50029952` and
`50029953` completed all 592 indices with resumable per-ontology checkpoints.

The strict audit verified exact ontology and index coverage; 592 matching
terminal rows, checkpoints, profiles, and logs; the pinned binary on every row;
valid production route traces; no temporary artifacts; the expected diagnostic
artifact set; and collision-safe full-IRI fingerprints for ORE3524, 13503,
4669, and 15703. Comparison with the complete `6600efe` sweep found zero
differences in status, verdict, signature, consistency, answer counts, route,
incompleteness, or gold-difference counts.

The sweep retained 591 `ok` rows and the sole expected ORE1194 error. Verdicts
were 588 exact matches, two established consistency mismatches, one no-gold
case, and one error. Across the 591 paired successful rows:

| measure | `6600efe` | `c3c3d24` |
|---|---:|---:|
| mean wall | 5.9744 s | 5.8301 s |
| median wall | 0.2703 s | 0.2526 s |
| mean peak | 845.61 MiB | 830.96 MiB |
| median peak | 45.00 MiB | 43.07 MiB |

Mean wall improved by 2.42%, and mean peak RSS fell by 1.73%. The 5%-trimmed
paired wall delta was minus 0.0570 seconds. ORE9674 completed in 43.6561 seconds
at 3,923.45 MiB with the same signature, compared with 48.1639 seconds and
5,352.88 MiB in the preceding sweep.

The authoritative per-ontology table is
[`automatic-results.tsv`](automatic-results.tsv), SHA-256
`f1b388ab25bf8479534b77ae0d3615eac47d6998bd75948fae57b7d9e7b7aef3`.

Reproduction files:

- [`ibex_build_candidate.sbatch`](ibex_build_candidate.sbatch)
- [`ibex_9674_pair.sbatch`](ibex_9674_pair.sbatch)
- [`ibex_build_buffered_candidate.sbatch`](ibex_build_buffered_candidate.sbatch)
- [`ibex_9674_buffered_file_pair.sbatch`](ibex_9674_buffered_file_pair.sbatch)
- [`ibex_build_c3c3d24.sbatch`](ibex_build_c3c3d24.sbatch)
- [`ibex_sanity_c3c3d24.sbatch`](ibex_sanity_c3c3d24.sbatch)
- [`ibex_sweep_c3c3d24.sbatch`](ibex_sweep_c3c3d24.sbatch)
