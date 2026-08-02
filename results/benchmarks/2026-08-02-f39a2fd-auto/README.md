# Automatic ORE 2015 sweep at `f39a2fd`

This directory records the source-bound production sweep of the default
`km classify` route over all 592 ORE 2015 ontologies after enabling batched NF4
propagation and exact edge membership in the QO/KPSet specialist. The benchmark
contract was 240 seconds, 20 GiB, and 16 cores per ontology.

## Provenance

- Source commit: `f39a2fd`
- Remote root: `/ibex/scratch/hohndor/km/release-f39a2fd-auto-20260802`
- Source archive SHA-256: `b3cbf0ee144ba85fa3325f029f74236f184c6a73caadc4bbd2068f329c6f68d3`
- Cluster-native build job: `49886489`
- Built `km` SHA-256: `4051f903dc2d3b63f9d08c7d8d36ad731612c251d4ca9b119b010e05bcc759b4`
- Full resumable array: `49886711`
- Audit receipt: `audit-49886711.out` in the remote root
- Result-table SHA-256: `61be1cf5f35f822e80df812e8b62035c523db1181febdc94b3cd874741336620`

The audit verified exactly 592 ontology/index pairs, final/checkpoint identity,
592 valid profiles and production route traces, one binary hash, 592 terminal
log markers, and no temporary artifacts. Slurm twice stopped exposing children
with a stale `JobArrayTaskLimit`; changing only the array throttle forced
reevaluation, and the same resumable job completed without duplicate or lost
results.

## Result

| measure | value |
|---|---:|
| Ontologies | 592 |
| `status=ok` | **591** |
| `status=error` | 1 (`ore_ont_1194.owl`) |
| Exact retained-gold matches | 588 |
| Independently adjudicated consistency mismatches | 2 |
| Independently adjudicated no-gold result | 1 |
| Mean wall time over successful rows | 6.3106 s |
| Median wall time over successful rows | 0.2791 s |
| Mean peak RSS over successful rows | 835.76 MiB |
| Median peak RSS over successful rows | 45.23 MiB |

Every semantic comparison field is identical to the certified `02a563f`
sweep: status, verdict, solved and consistency flags, signature and full-IRI
taxonomy digests, discrepancy counts, and selected production route. Coverage
therefore remains 591/592 with zero observed semantic regressions.

Across the 591 paired successful rows, mean wall time changed by +0.0270
seconds, median wall time by +0.0006 seconds, mean peak RSS by +2.15 MiB, and
median peak RSS by 0.00 MiB. These single-run aggregate differences are small
relative to cluster noise. The controlled same-binary sentinel gate showed
7581 improving from 21.1071 to 20.2926 seconds while retaining its exact
1,246,911-subsumption signature; 15098 remained effectively unchanged.

The production row for 1194 remains a fail-closed `error` after 31.9179 seconds
at 18,510.10 MiB and emits no taxonomy. A forced QO/KPSet diagnostic now reaches
its deterministic shared-filler precompute fixpoint in about 185 seconds, but
all 70,231 concepts remain affected by non-filler cardinality deferrals and
parked disjunctions. `CARDMERGE` performs zero merges in that model. Combining
separate fillers with `CARDMERGE` still times out with millions of literal and
edge events queued and 1,117,473 parked disjunctions. Closing 1194 therefore
requires predecessor-sensitive inverse/cardinality handling, not another
existing route switch.

[`automatic-results.tsv`](automatic-results.tsv) is the complete per-ontology
result table.
