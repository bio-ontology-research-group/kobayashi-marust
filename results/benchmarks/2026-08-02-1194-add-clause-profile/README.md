# ORE 1194 exact `add_clause` phase profile

This run separates the exact active-clause insertion path into arena lookup,
forward subsumption, backward subsumption, and index maintenance. It is an
instrumentation-only build: detached commit `1fd4285`, source archive SHA-256
`ec391457add7238a16bf7ad85154a9caba12a12a826f714294829e70dbdb77c8`, and
binary SHA-256
`3335a5efece165a7a935d1272ed9d64d4dd3e25adee1b039e8ca4995aaf6f40f`.

IBEX build job `49851481` emitted `BUILD_COMPLETE`. Exclusive-node profile job
`49851840` emitted `TASK_COMPLETE`, a checkpointed row, the expected
`nominals` automatic-route trace, and the exact binary fingerprint. The run
failed closed at the central time cap after 234.3947 seconds and peaked at
12,902.94 MiB.

## Decisive context

At 600,000 iterations in context 59,483, the engine had accepted 688,894
clauses, retained 10,314 worked-off clauses, and generated 10,008,068 Hyper
conclusions. Cumulative timed phases were:

| phase | milliseconds |
|---|---:|
| `add_clause` total | 130,681.9 |
| backward subsumption | 75,410.6 |
| forward subsumption | 47,838.2 |
| arena lookup | 3,896.0 |
| active/index maintenance | 1,470.4 |
| Hyper generation | 25,241.4 |
| work-off subsumption | 12,564.1 |

Backward subsumption grew from 17.58 seconds at 200,000 iterations to 50.92
seconds at 400,000 and 75.41 seconds at 600,000. The corresponding forward
subsumption totals were 8.97, 33.95, and 47.84 seconds. This makes exact
cross-call active-clause subset/superset indexing the next measured target;
generation, arena lookup, and ordinary index insertion are secondary.

Immutable artifacts remain under
`/ibex/scratch/hohndor/km/probe-1fd4285-add-phases-20260802`, including the
source archive, build log, binary, checkpoint, result row, and full stderr
profile.
