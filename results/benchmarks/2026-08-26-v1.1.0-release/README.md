# KM v1.1.0 release sweep

This directory records the exact-artifact release gate for KM v1.1.0.

- Final binary SHA-256:
  `fd9d7f1a1f4365a3262aeb37be8095631489257ea1e030e400a647d382b6a88a`
- Native build job: `50883680`, completed in 4 minutes 29 seconds
- Cargo package version: 1.1.0
- Source-capsule SHA-256:
  `ab00cb88cfa0464907f399cecbbc0d4f177dfbc2ed467afa9e90bd1373f0f0ba`
- Final IBEX root: `/ibex/scratch/hohndor/km/v1.1.0-final-20260826`
- Contract: automatic `km classify`, 592 ORE 2015 ontologies, 240 seconds,
  20 GiB process-tree RSS, 16 CPUs, exclusive Intel Xeon Gold 6248 nodes

The sweep starts from an empty results directory. Every task checks the binary
hash and records a terminal result, profile, and checkpoint. The strict release
auditor must preserve every v1.0 status/signature or an independently retained
recovery, produce 591 successful classifications plus the established
fail-closed ORE1194 error, and beat the frozen correct-completion aggregates of
ELK, HermiT, Konclude, and strict Sequoia on mean and median wall time and peak
RSS. No release claim is valid until all checks pass for this exact binary.

## Rejected workstation artifact

Workstation binary
`71770cdbfcb0f57a833e23b729330fbf929d148de966f491171ab13811e4c3eb`
was submitted as array `50883551`. The first seven profile checks all failed
before reasoning because the binary required glibc 2.39, unavailable on the
IBEX compute nodes. Monitoring detected the common error and cancelled the
array immediately. None of its rows are admissible release evidence. The final
artifact is built from the hash-pinned capsule on an IBEX compute node.

## Final sweep scheduling

Batch array `50883938` started with indices 0–591. After it completed index 40,
the untouched range 300–591 was cancelled from that array; its remaining
ownership is 41–299. Debug array `50884031` owns exactly 300–591 with a
single-task throttle on `gpu510-32`. Both arrays use the same Gold 6248 CPU,
hash-pinned binary, harness, output directory, and checkpoint contract. Their
ranges are disjoint, so no ontology can be concurrently published by both.

While the batch prefix remained priority-limited at index 79, untouched indices
190–299 were cancelled from `50883938`. Debug array `50884855` owns that exact
range and queues behind `50884031` on the same node. Final ownership is
`50883938`: 0–189, `50884855`: 190–299, and `50884031`: 300–591.

After both debug ranges completed and batch indices 98–189 remained pending,
indices 140–189 were cancelled from `50883938` and assigned to debug array
`50885983`. Final ownership is `50883938`: 0–139, `50885983`: 140–189,
`50884855`: 190–299, and `50884031`: 300–591.

After the three debug ranges completed, batch indices 118–139 were still
untouched and resource-pending. They were cancelled from `50883938` and moved
as final closeout array `50886461` to the now-free debug node. Final ownership
is `50883938`: 0–117, `50886461`: 118–139, `50885983`: 140–189,
`50884855`: 190–299, and `50884031`: 300–591.

## Completed release gate

All arrays left the queue with 592 profiles, 592 terminal results, 592
byte-identical checkpoint records, no temporary files, and no harness failure
markers. The strict v1.0 preservation audit found 591 successful
classifications, the same fail-closed ORE1194 error, and no behavioral
difference over all 592 ontologies. The five intended route changes are 12528,
15803, 5519, 6223, and 6477.

| Metric over 591 correct completions | v1.0 preservation baseline | v1.1.0 |
|---|---:|---:|
| Mean wall (s) | 1.562004 | 1.399664 |
| Median wall (s) | 0.1348 | 0.1303 |
| Mean peak RSS (MiB) | 231.032 | 225.696 |
| Median peak RSS (MiB) | 26.65 | 27.02 |

[`release-gate-v1.1.0.txt`](release-gate-v1.1.0.txt) passes mean and median
wall/RSS strictly against ELK 0.6.0, HermiT 1.4.6.519-SNAPSHOT, Konclude
v0.7.0-1138 (`0002e8063540`), and Sequoia 0.6.1-alpha (`c5248ec7be30`).
[`strict-audit-v110-v20.json`](strict-audit-v110-v20.json) records preservation
and [`per-ontology-gate-v1.1.0.json`](per-ontology-gate-v1.1.0.json) records the
separate v1.2 status: 442 both-metric wins, 59 memory-only, 9 wall-only, 79
neither, and three unadjudicated ontologies.
