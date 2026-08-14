# Bulk-sorted frontend IRI metadata

This directory records the v0.2.25 automatic-route candidate evidence.

- Candidate binary SHA-256:
  `7c090417f169d5ee60992f5203e2fe62aee4e8244b50e1aadf7a03b08bf1a71a`
- Strict IBEX sweep: Slurm job `50499428`
- Frontend byte-identity sweep: Slurm job `50498616`
- Hardware: Intel Xeon Gold 6248
- Contract: 240-second timeout and 20-GiB memory cap
- Integrity: 592 terminal results with per-task binary, ontology-index, route,
  checkpoint, and collision-safe fingerprint checks
- Automatic-results SHA-256:
  `d1d3e5919efc2f1404093aaaf31c966cac2505f74961eb165dc8ccc619d69a65`

The automatic route reports 591 successful classifications and ORE1194 as
the sole fail-closed error. Comparison with v0.2.24 finds zero differences in
status, verdict, consistency, selected route, or output signature.

| metric | v0.2.24 | candidate | change |
|---|---:|---:|---:|
| mean wall, seconds | 3.779906 | 3.722682 | -1.514% |
| median wall, seconds | 0.1887 | 0.1860 | -1.431% |
| mean peak RSS, MiB | 441.5357 | 440.8062 | -0.165% |
| median peak RSS, MiB | 36.17 | 36.04 | -0.359% |

The frontend now sorts owned IRI metadata once, derives the named-class vector
from that ordering, and bulk-constructs the `BTreeMap` from its sorted iterator.
The independent frontend sweep compared both the clause stream and metadata
file for every ontology and found 592/592 byte-identical pairs.

Two order-reversed focused panels produced 34 exact baseline/candidate pairs.
The candidate reduced their combined wall time by 17.78 seconds, about 1.8%.
One exploratory ORE3524 task in each panel exceeded memory because that early
panel used the ordinary local-name canonicalizer; the accepted strict sweep
used the collision-safe runner and completed ORE3524 correctly.

`automatic-results.tsv` contains every terminal row, `summary.json` contains
the strict aggregate, and `comparison-v0.2.24.json` records the behavioral and
resource comparison. The included Slurm scripts reproduce the build, focused
reverse panel, frontend identity sweep, and strict classification sweep.

No Lean re-certification is needed. The change only constructs the same sorted
frontend metadata through a different standard-library insertion path. It does
not alter clauses, routing, reasoning rules, or derived results.
