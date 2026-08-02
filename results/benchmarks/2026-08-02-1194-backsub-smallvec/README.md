# Rejected allocation-free backward-subsumption candidate

Candidate `3339f41` iterates the selected rarest active-head posting directly
and keeps the usually tiny exact removal set in `SmallVec<[u32; 8]>`. It removes
the per-call candidate `Vec` and removal `HashSet` allocations without changing
the dense screen, exact strengthening predicate, candidate order, or final
active clause set.

The focused engine suite passed 52 tests with one benchmark-only test ignored.
The complete release suite passed 1,946 tests with eight intentionally ignored
and zero failures, including randomized linear-oracle and shared-base
backward-subsumption differentials.

## Provenance

- Candidate commit: `3339f41f4c182db49c5e86ad039106501132dae6`
- Source archive SHA-256:
  `38f4558d22e99b334a581f83ebfebcbd123fe4ae70835b4987de81058f9da818`
- IBEX build job `49855340`, with `BUILD_COMPLETE`
- Binary SHA-256:
  `713decface1ce5e43b4e191806af26f3dba49a3f98323bfb208104a5af4e791f`
- Four-task gate array `49856028`; every task emitted a checkpoint, selected
  route trace, finalized JSON result, and `TASK_COMPLETE`
- Immutable root:
  `/ibex/scratch/hohndor/km/gate-3339f41-backsub-smallvec-20260802`

| ontology/configuration | status | verdict | wall s | peak MiB | baseline wall s |
|---|---|---|---:|---:|---:|
| 1194 automatic | error | error | 31.8489 | 18,546.68 | 32.0151 |
| 1194 exact CB, 2 threads, 225-second cap | error | error | 234.5986 | 12,941.85 | 234.58–234.74 |
| 8480 automatic | ok | exact match | 22.7446 | 5,449.95 | 19.9043 |
| 15846 automatic | ok | exact match | 196.2804 | 18,969.13 | 197.8516 |

The candidate preserves both sentinels but does not materially advance 1194.
The millions of tiny temporary allocations are not the limiting cost despite
their frequency. The candidate is rejected and not integrated. A full
592-ontology sweep is not warranted after this failed 1194 gate.
