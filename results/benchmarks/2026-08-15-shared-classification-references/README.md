# Shared classification-reference evidence

Release candidate `ce8b606` replaces one owned concept-reference hash table per
KPSet classification message adapter with an immutable shared `Arc`. Adapter
mutation uses `Arc::make_mut`, preserving the established isolated mutable
contract. The candidate binary is
`c28ece45471c273c651921ab2752604281a2b83e04db5408abdc56772965b692`;
the v0.2.30 baseline binary is
`1da5c66a96425cba2fe87cd208c1f58b1cc363fc85c9a69253f79190d3d632a1`.

## Focused mechanism gate

Same-node opposite-order job `50537191` classified ORE3215 twice per arm. Both
candidate outputs are byte-identical to their baseline output, including the
complete 367-MiB JSON taxonomy.

| arm | wall runs s | wall mean s | peak runs KiB |
|---|---|---:|---|
| v0.2.30 baseline | 127.22, 129.02 | 128.120 | 5,503,892; 5,506,616 |
| candidate | 124.01, 124.98 | 124.495 | 5,510,604; 5,506,332 |

## Three full ORE pairs

Jobs `50537280`, `50538368`, and `50539369` each ran both binaries in balanced
order over all 592 ontologies. Each job contains exactly 1,184 terminal JSON
rows, 592 ontologies, 591 successful classifications per arm, and the expected
fail-closed ORE1194 result. Comparisons cover status, verdict, consistency,
consistency mismatch, selected route, solved state, missing/extra counts,
unsatisfiable counts, and full-IRI signature. All comparison counts are zero.

| job | arm | wall mean s | wall median s | peak mean MiB | peak median MiB |
|---|---|---:|---:|---:|---:|
| 50537280 | baseline | 3.528027 | 0.16090 | 453.8111 | 35.600 |
| 50537280 | candidate | 3.513883 | 0.16075 | 454.1747 | 35.480 |
| 50538368 | baseline | 3.517573 | 0.16360 | 454.9469 | 35.315 |
| 50538368 | candidate | 3.504773 | 0.15995 | 454.7270 | 34.840 |
| 50539369 | baseline | 3.514595 | 0.16245 | 453.9793 | 34.240 |
| 50539369 | candidate | 3.504917 | 0.16175 | 454.1386 | 34.525 |
| **pooled** | **baseline** | **3.520065** | **0.16145** | **454.2458** | **35.125** |
| **pooled** | **candidate** | **3.507857** | **0.16075** | **454.3468** | **34.965** |

The candidate lowers mean wall in all three replications and saves 21.6812
seconds across the pooled 1,776 pairs. Mean peak RSS changes by 0.101 MiB
(0.022%) in the pool and changes direction between runs; it is treated as flat,
not as a memory improvement. Median peak RSS improves in the pool.

## Release tests

`CARGO_TARGET_DIR=/tmp/km-v031-target cargo test --release --locked` passes
1,995 library tests with eight ignored tests and every integration test. The
dedicated `issue_3_soundness` test passes and confirms that nominal enumeration
plus explicit difference reports the pigeonhole ontology inconsistent.
