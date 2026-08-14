# Parallel NF4 frontier batching

This directory records the v0.2.24 automatic-route candidate evidence.

- Candidate binary SHA-256:
  `b51af8f49e59f4c74515bb2677e68706a585a2d851ae838275046a81b77fe965`
- Strict IBEX sweep: Slurm job `50496853`
- Hardware: Intel Xeon Gold 6248
- Contract: 240-second timeout and 20-GiB memory cap
- Integrity: 592 terminal results with per-task binary, ontology-index, route,
  checkpoint, and collision-safe fingerprint checks
- Automatic-results SHA-256:
  `61eb241df0b972a7c25b5365beb4464d1aaa60d572582385bf4aa4234bc23984`

The automatic route reports 591 successful classifications and ORE1194 as
the sole fail-closed error. Comparison with v0.2.23 finds zero differences in
status, verdict, consistency, selected route, or output signature.

| metric | v0.2.23 | candidate | change |
|---|---:|---:|---:|
| mean wall, seconds | 3.783516 | 3.779906 | -0.095% |
| median wall, seconds | 0.1885 | 0.1887 | +0.106% |
| mean peak RSS, MiB | 441.4595 | 441.5357 | +0.017% |
| median peak RSS, MiB | 36.47 | 36.17 | -0.823% |

The optimization groups dense edge-side NF4 frontiers by parent, computes
missing propagation conclusions in parallel, and inserts those conclusions in
deterministic order. Sparse frontiers retain the serial join. The production
source-profile gate matches one ontology in the 592-ontology profile table:
ORE8737. Three alternating automatic-route pairs reduced its mean wall time
from 85.174 to 78.256 seconds, an 8.1% reduction. All six outputs matched gold;
mean process-tree peak RSS changed from 4915.98 to 4916.95 MiB.

`automatic-results.tsv` contains every terminal row, `summary.json` contains
the strict aggregate, and `comparison-v0.2.23.json` records the behavioral and
resource comparison. `focused-repeats/` retains the controlled ORE8737 rows.
The first full-sweep submission, job `50496754`, found a missing remote template
before classification and produced zero result rows. It was canceled and is
excluded. Job `50496853` is the accepted sweep.

No Lean re-certification is needed. Batching emits only conclusions attempted
by the existing NF4 edge join and changes the scheduling and deduplication of a
finite monotone EL Horn closure, not its rules or derived fixpoint.
