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

An initial production sweep was conservatively cancelled after 116 unique
terminals because scheduler elapsed for ORE 9674 exceeded three minutes. Its
completed row showed the reasoner itself took 45.2206 seconds at 3,923.18 MiB
with the correct signature; the remaining task time was canonicalisation of
14,809,043 pairs, not reasoner serialization. No result from the cancelled
partial sweep is used as a corpus-wide claim.

Reproduction files:

- [`ibex_build_candidate.sbatch`](ibex_build_candidate.sbatch)
- [`ibex_9674_pair.sbatch`](ibex_9674_pair.sbatch)
- [`ibex_build_buffered_candidate.sbatch`](ibex_build_buffered_candidate.sbatch)
- [`ibex_9674_buffered_file_pair.sbatch`](ibex_9674_buffered_file_pair.sbatch)

The complete 592-ontology production sweep remains the acceptance gate.
