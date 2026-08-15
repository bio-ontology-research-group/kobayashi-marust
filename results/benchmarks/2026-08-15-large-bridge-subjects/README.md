# Large production-bridge subject-partition evidence

Release candidate `6851533` assigns bounded subject workers to two narrowly
selected large `production_all` bridge profiles. The candidate binary is
`bbef8d7efbc6a6b8aefa3c44e55f40fb90916f1974d6c8086eb77bb7ac1d074f`.
The v0.2.35 baseline binary is
`d289f0e4c8c18551cbce5f3a1a476ae036a27d2259b0fa3439983ba0d1ac1a6f`.

## Correctness contract

Each worker classifies a disjoint subset of named subjects against the same
complete ontology and superclass universe. The merged output is sorted and
deduplicated. If any partition declines, the bridge publishes no answer and
the unchanged exact fallback runs. This is a scheduling change and does not
alter the bridge calculus.

The complete serial release suite passes 2,006 library tests with eight
ignored tests and every integration test, including `issue_3_soundness`.

## Focused gates

Same-node Slurm jobs `50554126` and `50554127` ran three alternating
automatic-route pairs per ontology. All runs selected `production_all`,
matched their Konclude full-IRI signatures, and produced identical consistency
and answer counts.

| ontology | arm | wall samples s | wall median s | RSS median MiB |
|---|---|---|---:|---:|
| ORE14817 | v0.2.35 baseline | 91.8347, 92.7472, 91.6673 | 91.8347 | 2,799.62 |
| ORE14817 | candidate | 75.0825, 75.5803, 74.9235 | 75.0825 | 5,963.04 |
| ORE3215 | v0.2.35 baseline | 125.9276, 125.1896, 125.5704 | 125.5704 | 6,278.98 |
| ORE3215 | candidate | 88.5683, 89.1692, 89.9747 | 89.1692 | 9,643.82 |

## Full ORE pair

Order-balanced job `50554161` ran both binaries on all 592 ontologies on
exclusive Intel Xeon Gold 6248 nodes. It contains exactly 1,184 terminal JSON
records, 1,184 matching checkpoints, 592 pair-completion markers, and no
temporary outputs. Each arm has 591 successful classifications and the
expected fail-closed ORE1194 result. Comparisons cover status, verdict,
consistency, selected route, solved state, answer counts, missing and extra
counts, and collision-sensitive full-IRI signatures. Every comparison count
is zero.

| arm | wall mean s | wall median s | peak mean MiB | peak median MiB | wall sum s | RSS sum MiB |
|---|---:|---:|---:|---:|---:|---:|
| v0.2.35 baseline | 3.323273 | 0.1621 | 416.5434 | 34.43 | 1,964.0546 | 246,177.16 |
| candidate | 3.238253 | 0.1628 | 427.8782 | 35.39 | 1,913.8077 | 252,875.99 |

ORE14817 falls from 91.7122 seconds and 2,815.84 MiB to 74.4746 seconds and
5,956.86 MiB in the full pair. ORE3215 falls from 124.3401 seconds and
6,278.20 MiB to 88.7951 seconds and 9,695.84 MiB. The corpus saves 50.2469
wall seconds. The candidate's four corpus metrics are below the frozen
Konclude measurements: 3.2657 seconds mean wall, 0.2813 seconds median wall,
558.09 MiB mean peak RSS, and 76.53 MiB median peak RSS.
