# Exit-notified workers and focused one-worker scheduling

This directory records the v0.2.22 automatic-route release sweep.

- Implementation commit: `144f92d`
- Candidate binary SHA-256:
  `4379bd61e853869c81148633365740d058e1f768b3320c69334f64e3cf88127f`
- Strict IBEX sweep: Slurm job `50492209`
- Hardware: Intel Xeon Gold 6248
- Contract: 240-second timeout and 20-GiB memory cap
- Result integrity: 592 result rows, 592 profiles, and 592 checkpoints
- Automatic-results SHA-256:
  `026d13755a14359f754670cd5bb6adacba99d87ec1299832b501a8a605071ce7`

The sweep reports 591 successful classifications and ORE1194 as the sole
fail-closed error. Against v0.2.21 it has zero status, verdict, signature,
consistency, or coverage regressions.

| metric | v0.2.21 | v0.2.22 candidate | change |
|---|---:|---:|---:|
| mean wall, seconds | 3.897291 | 3.846692 | -1.298% |
| median wall, seconds | 0.1897 | 0.1885 | -0.633% |
| mean peak RSS, MiB | 443.2223 | 441.1139 | -0.476% |
| median peak RSS, MiB | 35.94 | 35.73 | -0.584% |

`automatic-results.tsv` contains every per-ontology terminal row. `summary.json`
contains the strict aggregate and route counts. An 85-run, five-repeat
alternating panel (`50491928`) compared the panic-build baseline with the pidfd
candidate and produced byte-identical output for every pair. Focused watchdog
tests cover successful child exit, timeout termination, and RSS-cap
termination.

No Lean re-certification is needed. The changes affect operating-system wait
notification, release panic code generation, and the worker count for an
unchanged complete route portfolio. They do not alter calculus rules,
ordering, redundancy, or the derived fixpoint.
