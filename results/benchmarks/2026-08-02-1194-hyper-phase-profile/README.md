# ORE 1194 Hyper phase profile

This diagnostic splits the CB engine's aggregate Hyper time into ontology
candidate lookup, premise-candidate construction, exact semijoin reduction,
and recursive join plus resolvent construction. It runs on detached revision
`f106554`, based on the exact linked worked-off candidate `4a34d3c`. The
instrumentation is not included in `main` and does not change reasoning.

## Provenance

- Source revision: `f1065542d4b6caf7f700f4bc63bfb70b9b346caf`
- Source archive SHA-256:
  `48ed118f9d47283e32e6cbd7d1b0d5760908b131d2ea4454c36dae739776c96e`
- IBEX build job: `49865575`, with `BUILD_COMPLETE`
- Binary SHA-256:
  `432d9a1a6cca658ecc38b61d28941c6b11ea0b184ea7d37022b95f4375d53e4c`
- Profile job: `49865577`, with checkpoint and `TASK_COMPLETE`
- Immutable remote root:
  `/ibex/scratch/hohndor/km/profile-f106554-hyper-phases-20260802`

The run used the exact manual two-thread CB route, a 225-second central cap,
and the production 240-second / 20-GiB outer contract. It failed closed after
234.2933 seconds at 14,879.62 MB and emitted no taxonomy.

## Result

The largest aggregate Hyper checkpoint was:

| Hyper phase | Cumulative time (ms) | Share of aggregate Hyper |
|---|---:|---:|
| ontology candidate lookup | 1,625.8 | 10.1% |
| premise candidate construction and unification | 6,409.8 | 39.8% |
| exact semijoin reduction | 234.7 | 1.5% |
| recursive join and resolvent construction | 1,986.8 | 12.3% |
| uninstrumented Hyper overhead and early exits | 5,846.0 | 36.3% |
| **aggregate Hyper** | **16,103.0** | **100%** |

At the final message-loop checkpoint, the engine had 149,264 contexts and had
processed 6,759,999 successor messages while the ground context held 663,369
worked-off clauses. The measured Hyper phases therefore do not dominate the
remaining wall time. Even eliminating candidate construction completely would
save only 6.4 seconds in this run and would not address the context/message
explosion.

## Decision

Do not pursue another isolated Hyper micro-optimization as the closure route
for ontology 1194. The next closure attempt should avoid the CB context graph,
using the certified-EL residual path and addressing its model-scale role-bridge
closure directly. Hyper performance work can still be useful for general KM
throughput, but this evidence does not support it as the path from 591 to 592.

Raw checkpoint, result, stderr profile, resource report, and submitted Slurm
script are retained under `evidence/`.
