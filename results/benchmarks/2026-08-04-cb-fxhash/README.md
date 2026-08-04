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

The local gate justifies an IBEX corpus sweep. It does not establish a release
claim or change the documented 591/592 automatic coverage result.
