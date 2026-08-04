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

Reproduction files:

- [`ibex_build_candidate.sbatch`](ibex_build_candidate.sbatch)
- [`ibex_9674_pair.sbatch`](ibex_9674_pair.sbatch)

The complete 592-ontology production sweep remains the acceptance gate.
