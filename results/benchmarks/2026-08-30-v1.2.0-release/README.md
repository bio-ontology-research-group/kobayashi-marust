# KM v1.2.0 release sweep

This directory records the exact-artifact release gate for KM v1.2.0.

- Final benchmark binary SHA-256:
  `4d04cc8491597f67c9c0f4c57a5fe6422d46144643fbe74efbb8d64646ebfb91`
- Authoritative Slurm owner job: `50996021`
- Cargo package version: 1.2.0
- Final IBEX root:
  `/ibex/scratch/hohndor/km/v1.2.0-final-20260829/full-sweep`
- Contract: automatic `km classify`, 592 ORE 2015 ontologies, 12-minute task
  limit, Gold-6248 nodes, array throttle 40, and one non-competing writer

Indices 1–13 existed as durable validated results before the final owner job.
Job 50996021 exclusively owned indices 0 and 14–591. It completed normally
with 592 profiles, results, and byte-identical checkpoint records. Every record
identifies the expected ontology, array index, task identity, binary hash, CPU
model, selected route, and terminal result.

## Completed release gate

The strict semantic gate reports 591 successful classifications and the
established fail-closed ORE1194 parse error. Of the 592 verdicts, 588 match the
retained gold, ORE2669 and ORE15516 are the documented consistency mismatches
where the gold is wrong, and ORE10860 has no gold result.

| Metric over 591 correct completions | v1.2.0 |
|---|---:|
| Mean wall (s) | 1.464575 |
| Median wall (s) | 0.1559 |
| Mean peak RSS (MiB) | 226.307 |
| Median peak RSS (MiB) | 26.98 |

All four aggregate metrics are strictly below the retained correct-completion
arms for ELK 0.6.0, HermiT 1.4.6.519-SNAPSHOT, Konclude v0.7.0-1138
(`0002e8063540`), and Sequoia 0.6.1-alpha (`c5248ec7be30`).

[`release-gate-summary.json`](release-gate-summary.json) is the durable summary
written by the fail-closed remote release audit. Its SHA-256 is
`e7cd87c8288629a67633a29d9a55458076f214eaf2f26d905ef4070f126ad844`.
