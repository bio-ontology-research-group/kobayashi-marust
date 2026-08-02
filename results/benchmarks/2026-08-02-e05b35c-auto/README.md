# Automatic ORE 2015 sweep at `e05b35c`

This directory records the source-bound production sweep of the default
`km classify` route over all 592 ORE 2015 ontologies. The benchmark contract
was 240 seconds, 20 GiB, and 16 cores per ontology.

## Provenance

- Source commit: `e05b35c`
- Remote root: `/ibex/scratch/hohndor/km/release-e05b35c-auto-20260802`
- Source archive SHA-256: `060167b95d20080c93c3473466d7bdfd23a2ea8acae1040366587d068655602f`
- Cluster-native build job: `49826807`
- Built `km` SHA-256: `ffbd9afd129533e7fa67c1c86f726496d4e269dfc38418375c16aa033e32dd9b`
- End-to-end gate array: `49826957` (indices 33 and 401)
- Full resumable array: `49826971`
- Result-table SHA-256: `e4798b461064d69e19657280e11c56ea6c1243ebd04697c2ef6a66e784a53cdb`

The terminal audit found 590 `TASK_COMPLETE` markers and two
`ALREADY_COMPLETE` markers for the gate rows, covering all 592 indices. Every
result row matched its checkpoint, all rows reported the same binary hash, and
no temporary output remained.

## Result

| measure | value |
|---|---:|
| Ontologies | 592 |
| `status=ok` | **591** |
| `status=error` | 1 (`ore_ont_1194.owl`) |
| Exact retained-gold matches | 588 |
| Independently adjudicated consistency mismatches | 2 |
| Independently adjudicated no-gold result | 1 |
| Mean wall time over successful rows | 6.6854 s |
| Median wall time over successful rows | 0.2758 s |
| Mean peak RSS over successful rows | 838.01 MiB |
| Median peak RSS over successful rows | 45.22 MiB |

The status, verdict, solved flag, output digests, consistency result, taxonomy
and unsatisfiable counts, discrepancy fields, and selected route trace are
identical to the preceding complete sweep. The index-reuse change therefore
introduced no observed semantic change. It lets the 1194 certificate repair
complete six conflict restarts instead of three in the same focused gate, but
1194 still reaches the benchmark limit without publishing a result.

[`automatic-results.tsv`](automatic-results.tsv) is the complete per-ontology
result table.
