# Parallel certified-bridge subject evidence

Release candidate `d9c251a` partitions independent classification subjects
for the narrowly selected large typed-ABox bridge profile. The candidate
binary is
`d289f0e4c8c18551cbce5f3a1a476ae036a27d2259b0fa3439983ba0d1ac1a6f`.
The v0.2.34 baseline binary is
`cc04717a29ca85be6441b668167493254600c53661ccdf66fb688b924ad2bdb0`.

## Correctness contract

Each worker classifies a disjoint subset of named subjects against the same
complete ontology and superclass universe. The merged output is sorted and
deduplicated. If any partition declines, the bridge publishes no answer and
the unchanged exact fallback runs. This is a scheduling change and does not
alter the bridge calculus.

The direct release-mode unit test compares one-worker and two-worker results
for consistency, unsatisfiable classes, and subsumptions. The complete release
suite passes 2,006 library tests with eight ignored tests and every integration
test, including `issue_3_soundness`.

## Focused ORE10621 gate

Same-node Slurm job `50552259` ran three alternating automatic-route pairs.
All six runs selected `certified_nominals`, matched the Konclude full-IRI
signature
`cb490ae3d086535d4ef467ed5277e5f497e221d84a79a70fb0dc87afb8a45ccf`,
and produced identical consistency and answer counts.

| arm | wall samples s | wall median s | RSS median MiB |
|---|---|---:|---:|
| v0.2.34 baseline | 83.4969, 83.2582, 83.2711 | 83.2711 | 1,273.03 |
| candidate | 38.9416, 39.0450, 38.8790 | 38.9416 | 1,555.85 |

## Full ORE pair

Order-balanced job `50552285` ran both binaries on all 592 ontologies on
exclusive Intel Xeon Gold 6248 nodes. It contains exactly 1,184 terminal JSON
records, 1,184 matching checkpoints, 592 pair-completion markers, and no
temporary outputs. Each arm has 591 successful classifications and the
expected fail-closed ORE1194 result. Comparisons cover status, verdict,
consistency, selected route, solved state, answer counts, missing and extra
counts, and collision-sensitive full-IRI signatures. Every comparison count
is zero.

| arm | wall mean s | wall median s | peak mean MiB | peak median MiB | wall sum s | RSS sum MiB |
|---|---:|---:|---:|---:|---:|---:|
| v0.2.34 baseline | 3.419858 | 0.1625 | 416.3415 | 35.14 | 2,021.1362 | 246,057.84 |
| candidate | 3.330214 | 0.1621 | 417.0383 | 35.02 | 1,968.1566 | 246,469.63 |

ORE10621 falls from 83.3822 seconds and 1,272.22 MiB to 38.8773 seconds
and 1,555.30 MiB in the full pair. The corpus saves 52.9796 wall seconds.
