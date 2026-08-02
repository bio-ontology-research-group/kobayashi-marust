# Automatic ORE 2015 sweep at `1ef8ee1`

This directory records the source-bound production sweep of the default
`km classify` route over all 592 ORE 2015 ontologies. The benchmark contract
was 240 seconds, 20 GiB, and 16 cores per ontology.

## Provenance

- Source commit: `1ef8ee1`
- Remote root: `/ibex/scratch/hohndor/km/release-1ef8ee1-auto-20260802`
- Source archive SHA-256: `a477f7ea8cb7ca2f04de5367828a74eeafe66d4770e0fa14882f87a661205766`
- Cluster-native build job: `49835146`
- Built `km` SHA-256: `bdb436541eaebe4d0c2af86e4cf35d0fca4332244752f8975610a8f8712a1b90`
- End-to-end gate array: `49835472` (indices 33 and 401)
- Full resumable array: `49835534`
- Result-table SHA-256: `3c326e7c00524085fe8543c0c0de22bd8350d9d8917cc4350ab8f4bb9dd3ae18`

The terminal audit found 592 task logs, each ending in `TASK_COMPLETE` or
`ALREADY_COMPLETE`, and exactly 592 unique ontology and array-index records.
Every result matched its checkpoint, all 592 rows reported the same binary
hash, all 592 profiles recorded a selected route, and no temporary output
remained.

## Result

| measure | value |
|---|---:|
| Ontologies | 592 |
| `status=ok` | **591** |
| `status=error` | 1 (`ore_ont_1194.owl`) |
| Exact retained-gold matches | 588 |
| Independently adjudicated consistency mismatches | 2 |
| Independently adjudicated no-gold result | 1 |
| Mean wall time over successful rows | 6.3539 s |
| Median wall time over successful rows | 0.2738 s |
| Mean peak RSS over successful rows | 844.18 MiB |
| Median peak RSS over successful rows | 45.23 MiB |

All semantic comparison fields are identical to the certified `e05b35c`
sweep: status, verdict, solved and consistency flags, signature and full-IRI
taxonomy digests, discrepancy counts including unsatisfiability, and selected
route trace. The exact Hyper candidate narrowing, dense subsumption screens,
and staged local Pred join therefore introduced no observed semantic change.

In paired successful rows, mean wall time decreased by 0.3315 seconds and the
median decreased from 0.2758 to 0.2738 seconds. Mean peak RSS increased by
6.17 MiB and median peak RSS was effectively unchanged. Coverage remains
591/592; `ore_ont_1194.owl` is still the sole automatic-route failure.

[`automatic-results.tsv`](automatic-results.tsv) is the complete per-ontology
result table.
