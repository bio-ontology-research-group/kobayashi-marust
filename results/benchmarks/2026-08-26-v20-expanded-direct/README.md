# v20 expanded direct-route sweep

Candidate v20 expands the source-certified direct taxonomy route to large
sparse sources with pairwise `DisjointClasses` axioms and reflexive role
declarations.  These constructs are accepted only under the existing
common-descendant and taxonomy-edge-elision checks.

- Source capsule SHA-256: `3f603f60cd88115de2d074920dc322c359bb395f10e84c160d445ded1bfd03e1`
- IBEX binary SHA-256: `33b536962de62789387d98479d9d4f5d28edc142eb9e7260e9805eb7d79b2c97`
- Full sweep: Slurm array `50876507`
- Hardware: exclusive Intel Xeon Gold 6248 nodes, 16 allocated CPUs
- Contract: 592 ORE ontologies, 240 seconds, 20 GiB process-tree RSS
- Baseline: accepted v19 binary `760ffd875e5ac72f0aa0f205a46add71250410280725f5042a375c01cb67bd10`

The strict audit records 591 successful classifications and the established
fail-closed ORE1194 error in both arms.  It finds zero status, signature,
verdict, consistency, or solved-state differences.  Only ORE3560 and ORE7246
change selected route.

| Metric | v19 | v20 | Change |
|---|---:|---:|---:|
| Mean wall (s) | 1.643307 | 1.562004 | -0.081303 |
| Median wall (s) | 0.1575 | 0.1348 | -0.0227 |
| Mean peak RSS (MiB) | 235.741 | 231.032 | -4.709 |
| Median peak RSS (MiB) | 27.31 | 26.65 | -0.66 |

The authoritative audit is
`/ibex/scratch/hohndor/km/v20-expanded-direct-20260826/full-sweep/strict-audit-v20-v19.json`.
The fail-closed release gate is recorded beside it as `release-gate-v20.txt`.
Every comparison against Konclude, HermiT, Sequoia, and ELK passes except ELK
mean wall: v20 records 1.562004 seconds against the strict 1.520774-second
target.  This single remaining failure means the evidence does not authorize a
v1.1.0 release.
