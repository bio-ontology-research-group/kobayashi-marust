# Grouped final-taxonomy ordering

## Change

The automatic classifier previously mapped every worker subsumption to a
`[full_subject_iri, full_superclass_iri]` pair and globally sorted the complete
pair vector. Dense taxonomies therefore compared the same potentially long
subject IRI millions of times.

The candidate groups mapped superclass IRIs by mapped full subject IRI, sorts
each superclass row, iterates subjects in `BTreeMap` order, and then flattens
the rows. This produces exactly the same lexicographic pair sequence as the
global sort. Aliased local subjects are merged only after full-IRI mapping, and
duplicate pairs are retained. Unsatisfiable-class ordering and first-alias
consistency behavior remain unchanged. The transformation affects only final
answer representation; it does not change the calculus or saturation fixpoint
and requires no Lean re-certification.

## Validation

The complete workstation release suite passed with 1,948 library tests, eight
ignored library tests, and every integration and documentation suite passing.
The focused regression constructs unsorted rows, duplicate pairs, and mapped
subject aliases, then checks equality with the previous global pair sort.

The source-bound IBEX build used archive SHA-256
`7240de2d3fdb6acfd6c122ed4a03d394db501ce4d612f5d9a61b52f7f3b58325`.
Build job `50024140` produced cluster-native binary SHA-256
`537779a49e730941651736da7a55bfa2b97022b441011808528db76ca7e28863`.
Paired benchmark job `50024141` ran on an Intel Xeon Gold 6248 node. Each
classification streamed directly into SHA-256, and the job rejected nonzero
exits, malformed receipts, changing hashes, or baseline/candidate disagreement.

ORE 9674 emits 14,809,043 subsumption pairs and exercises the dense final-sort
path:

| repetition | baseline wall | candidate wall | baseline peak KiB | candidate peak KiB |
|---:|---:|---:|---:|---:|
| 1 | 51.71 s | 46.74 s | 5,454,736 | 5,480,220 |
| 2 | 51.76 s | 46.65 s | 5,454,188 | 5,480,812 |
| 3 | 51.62 s | 46.41 s | 5,454,388 | 5,480,844 |
| **mean** | **51.697 s** | **46.600 s** | **5,454,437** | **5,480,625** |

Mean wall improved by 9.86%. Mean peak RSS increased by 26,188 KiB (0.48%).
All six output streams had SHA-256
`152cdf0863750e3c94ac3faeb1764fe31a52935db73069bb48a5a8b6d2cd9184`.

The initial workstation-built candidate was also deliberately attempted as a
deployment sanity check and rejected before measurement because IBEX lacked
its required GLIBC 2.39. No result from that failed attempt is included above.

## Reproduction

- [`ibex_build_candidate.sbatch`](ibex_build_candidate.sbatch) builds the
  pinned source archive on an IBEX compute node.
- [`ibex_9674_pair.sbatch`](ibex_9674_pair.sbatch) runs the alternating paired
  benchmark and validates output identity.

## Complete production sweep

Commit `6600efe` was archived with SHA-256
`aefde41c675d7b1d9159fdb19db56f34152ea423cfa2a4410192abed749007ef`.
IBEX build job `50024711` reproduced binary SHA-256 `537779a49e73…`.
Sanity job `50024712` completed ORE 10860 and wrote a resumable checkpoint;
exclusive array `50024713` then completed all 592 indices.

The strict terminal audit verified 592 unique result rows, profiles,
checkpoints, and full-array logs; exact ontology and index coverage; the pinned
binary on every row; valid terminal or resume markers; no temporary or partial
artifacts; and the expected retained diagnostic-artifact set. Collision-safe
full-IRI fingerprints passed for ORE 3524, 13503, 4669, and 15703. Comparison
with the complete `df5bb5b` sweep found zero differences in status, verdict,
signature, consistency, answer counts, route, incompleteness, or gold-difference
counts.

The sweep retained 591 `ok` rows and the sole expected ORE 1194 error. Verdicts
were 588 exact matches, two established consistency mismatches, one no-gold
case, and one error. Across the 591 paired successful rows:

| measure | `df5bb5b` | `6600efe` |
|---|---:|---:|
| mean wall | 6.1991 s | 5.9744 s |
| median wall | 0.2766 s | 0.2703 s |
| mean peak | 844.44 MB | 845.61 MB |
| median peak | 45.23 MB | 45.00 MB |

The observed corpus mean wall improved by 3.63%, while mean peak increased by
0.14%. The 5%-trimmed paired mean improved by 0.0822 seconds. Because unrelated
routes also moved between arrays, the alternating ORE 9674 experiment above is
the source-isolated evidence for the optimization itself: 9.86% faster at a
0.48% peak-RSS cost. In the production sweep, ORE 9674 improved from 54.9113 to
48.1639 seconds with the same signature.

The authoritative per-ontology table is
[`automatic-results.tsv`](automatic-results.tsv), SHA-256
`1d9d4e3eed6d79b0a708aebbacab652d8449098ddbf5f0b92d12924501b628cd`.
The production build and arrays are reproduced by
[`ibex_build_6600efe.sbatch`](ibex_build_6600efe.sbatch),
[`ibex_sanity_6600efe.sbatch`](ibex_sanity_6600efe.sbatch), and
[`ibex_sweep_6600efe.sbatch`](ibex_sweep_6600efe.sbatch).
