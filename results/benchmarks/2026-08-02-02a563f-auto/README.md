# Automatic ORE 2015 sweep at `02a563f`

This directory records the source-bound production sweep of the default
`km classify` route over all 592 ORE 2015 ontologies after introducing a
shared immutable CB seed layer with per-context deltas. The benchmark contract
was 240 seconds, 20 GiB, and 16 cores per ontology.

## Provenance

- Source commit: `02a563f40286dcc42b3e1c7df3fa29d4a7c5eaaa`
- Remote root: `/ibex/scratch/hohndor/km/release-02a563f-auto-20260802`
- Source archive SHA-256: `a42ab9e1a43c1436e5af9c7fb553f22075ad455e07651c043d45d33dbc3f8a68`
- Cluster-native build job: `49841036`
- Built `km` SHA-256: `1011b397da7782301d7d78f451591889f3eaeadcef47f4a1a7a5352b2c123666`
- Ontology 1194 gate array: `49841342` (index 33)
- Full resumable array: `49841416`
- Result-table SHA-256: `b64308ce4fcfd12aff71e819aa147180d41933ae56c0196fb68ff373c7659ecb`

The terminal audit found 592 full-sweep task logs, each ending in
`TASK_COMPLETE` or `ALREADY_COMPLETE`, and exactly 592 unique ontology and
array-index records covering indices 0 through 591. Every result was identical
to its checkpoint, all rows reported the same binary hash, all 592 profiles
recorded a selected route, and no temporary output remained. Slurm stopped
exposing new children briefly after index 327; changing only the array throttle
from 10 to 9 forced a scheduler reevaluation and the same resumable array then
completed without resubmission or lost artifacts.

## Result

| measure | value |
|---|---:|
| Ontologies | 592 |
| `status=ok` | **591** |
| `status=error` | 1 (`ore_ont_1194.owl`) |
| Exact retained-gold matches | 588 |
| Independently adjudicated consistency mismatches | 2 |
| Independently adjudicated no-gold result | 1 |
| Mean wall time over successful rows | 6.2836 s |
| Median wall time over successful rows | 0.2776 s |
| Mean peak RSS over successful rows | 833.61 MiB |
| Median peak RSS over successful rows | 45.55 MiB |

All semantic comparison fields are identical to the certified `1ef8ee1`
sweep: status, verdict, solved and consistency flags, signature and full-IRI
taxonomy digests, discrepancy counts including unsatisfiability, and selected
route trace. Coverage therefore remains 591/592 with no observed correctness
change.

Across the 591 paired successful rows, mean wall time decreased by 0.0703
seconds and median wall time decreased by 0.0006 seconds. Mean peak RSS
decreased by 10.57 MiB and median peak RSS was unchanged. The largest measured
memory reductions were 2,200.09 MiB on `ore_ont_14817.owl`, 1,898.87 MiB on
`ore_ont_10621.owl`, and 749.60 MiB on `ore_ont_7246.owl`. The largest measured
increase was 148.93 MiB on `ore_ont_9768.owl`.

The production 1194 gate remained an error. Its measured peak decreased from
18,611.55 MiB to 18,558.06 MiB, while wall time increased from 27.6815 seconds
to 32.0151 seconds. The worker still crossed the route's internal memory
watchdog, so this optimization does not close the final ontology.

[`automatic-results.tsv`](automatic-results.tsv) is the complete per-ontology
result table.
