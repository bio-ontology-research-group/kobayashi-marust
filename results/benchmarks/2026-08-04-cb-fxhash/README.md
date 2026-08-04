# CB fast-hash local gate

This gate replaces `std::collections`' default SipHash state inside the CB
engine with the deterministic FxHash-style hasher already used by KM's EL
completion engine. The keys are trusted, internally generated interned ids,
predicates, terms, and small tuples. Exact map/set equality, rule firing,
subsumption, redundancy, and output construction are unchanged.

## Correctness gate

- `cargo test --release`: 1,947 passed, 0 failed, 8 ignored.
- Every integration and CLI suite passed.
- The focused 41-test engine suite passed, including differential Hyper,
  local-Pred, forward-subsumption, backward-subsumption, index, and incremental
  reasoning checks.
- `/tmp/4669-base.clauses.json` produced byte-identical 16,886,076-byte JSON;
  both outputs have SHA-256
  `055cb5f2481c778e5ed137dddccd2201e04d45c05a472b42eb54119cdc331ac2`.
- ORE 1194 reached the same 6,000,000-message checkpoint with identical
  contexts, saturation calls, Succ count, Pred count, and empty output under
  both 60-second bounded runs.

## Workstation performance gate

Host: `leechuck-office`. Build: release, LTO, one codegen unit. CB workers used
`KM_THREADS=1`.

| workload | build | wall | peak RSS | result |
|---|---|---:|---:|---|
| 4669 base | `d18f5a7` baseline | 30.99 s | 1,871,776 KiB | complete |
| 4669 base | CB fast hash | 22.27 s | 1,842,588 KiB | complete, byte-identical |
| 1194, 60 s | `d18f5a7` baseline | 60.16 s | 2,148,044 KiB | bounded checkpoint |
| 1194, 60 s | CB fast hash | 60.16 s | 2,150,560 KiB | same bounded checkpoint |

At the matching 1194 checkpoint:

| cumulative phase | baseline | fast hash | change |
|---|---:|---:|---:|
| Pred arrival | 35.685 s | 27.695 s | -22.4% |
| clause insertion | 24.525 s | 18.715 s | -23.7% |
| forward subsumption | 18.269 s | 14.357 s | -21.4% |
| backward subsumption | 0.991 s | 0.429 s | -56.7% |
| index maintenance | 2.285 s | 1.052 s | -54.0% |
| propagation | 1.684 s | 1.176 s | -30.2% |

## Full IBEX sweep

- Source commit: `a4eb829`
- Source archive SHA-256:
  `e2631c0ae792ee16d297b3a92e6306281ddf85d5f7daac5ce82615b6d91addf7`
- Build job: `49995963`
- Sanity array: `49995965` (1194, 4669, and 10860)
- Full resumable array: `49995966`
- Binary SHA-256:
  `2dd549fbf9833bcb8628de19e9a79f77cff9939efd60044c1b06b3b7e39f8f43`
- Result-table SHA-256:
  `42fbd1c6bf02a439e006cad0d215ee3b43469ef87a7e2acfb63100b85ba5c730`

The terminal audit found 592 unique ontology rows, every array index from 0 to
591 exactly once, 592 valid profiles, 592 full-array terminal markers, one
binary hash, no malformed checkpoints, no failure markers, and no temporary
files. All semantic fields matched the `1ef8ee1` source-bound sweep.

| measure | `1ef8ee1` | `a4eb829` |
|---|---:|---:|
| `status=ok` | 591 | 591 |
| exact retained/oracle matches | 588 | 588 |
| adjudicated consistency mismatches | 2 | 2 |
| adjudicated no-gold results | 1 | 1 |
| mean wall, successful rows | 6.3539 s | 6.1310 s |
| median wall, successful rows | 0.2738 s | 0.2794 s |
| mean peak RSS, successful rows | 844.18 MiB | 844.50 MiB |
| median peak RSS, successful rows | 45.23 MiB | 44.19 MiB |

Mean wall improved by 0.2228 seconds per successful ontology. The median wall
increase was 0.0056 seconds, mean RSS increased by 0.32 MiB, and median RSS
decreased by 1.04 MiB. The dominant route families all improved in mean wall:
`production_all` by 0.1381 seconds over 513 rows, `nominals` by 0.3840 seconds
over 49 rows, `certified_nominals` by 1.1021 seconds over ten rows, and
`nominal_ni_abox` by 2.4343 seconds over eight rows.

[`automatic-results.tsv`](automatic-results.tsv) is the complete per-ontology
result table. Coverage remains 591/592; ontology 1194 is still the only
automatic-route failure.
