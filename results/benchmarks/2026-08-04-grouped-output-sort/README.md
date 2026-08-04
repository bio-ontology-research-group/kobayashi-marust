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

The complete 592-ontology production sweep is the acceptance gate for landing
the optimization in the released automatic route.
