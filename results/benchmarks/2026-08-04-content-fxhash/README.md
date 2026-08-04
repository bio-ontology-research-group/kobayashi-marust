# Exact-checked content hashing gate

KM uses content hashes to select candidate buckets when interning context cores
and Pred clauses. Every candidate is still compared for exact structural
equality, so the hash is never a semantic decision. This gate replaces the
remaining `DefaultHasher` (SipHash) in that path with the deterministic
FxHash-style hasher already used by the CB saturation maps and sets.

## Workstation gate

Host: `leechuck-office`. Source baseline: `b10d951`. Release builds used LTO,
one codegen unit, and `KM_THREADS=1`. The test workload was
`/tmp/4669-base.clauses.json`, the completing ORE 4669 base workload.

The shared Cargo target cache initially contained a stale executable. It was
discarded. Both binaries below were rebuilt from the checked source immediately
before this gate.

| build | binary SHA-256 |
|---|---|
| `b10d951` baseline | `990dcce92fb6ef93f51d12a0e6813d396a783150e595169633f3824b5e13550c` |
| content FxHash candidate | `0d140493696c2c2bb7452ac34b19a1261ac9582f7257bbf3ef47c3118520bd14` |

Three interleaved pairs produced:

| run | baseline wall | candidate wall | baseline peak RSS | candidate peak RSS |
|---:|---:|---:|---:|---:|
| 1 | 22.97 s | 21.44 s | 1,837,764 KiB | 1,838,604 KiB |
| 2 | 22.23 s | 21.36 s | 1,838,648 KiB | 1,839,944 KiB |
| 3 | 22.19 s | 21.59 s | 1,840,200 KiB | 1,839,400 KiB |
| mean | 22.463 s | 21.463 s | 1,838,871 KiB | 1,839,316 KiB |

Mean wall improved by 1.000 seconds, or 4.45%. Mean peak RSS increased by
445 KiB, below run-to-run variation. All six outputs were byte-identical,
16,886,076-byte JSON with SHA-256
`055cb5f2481c778e5ed137dddccd2201e04d45c05a472b42eb54119cdc331ac2`.

The complete release suite passed with 1,955 library tests, eight ignored
library tests, and every integration suite passing. The focused 41-test release
engine suite also passed. A matched 60-second ORE 1194 check
preserved the bounded result: both builds timed out with zero output. Peak RSS
was 5,459,288 KiB for the baseline and 5,464,924 KiB for the candidate.

The change only alters bucket distribution. Core and Pred-clause equality,
interned ids, rule scheduling after successful interning, and the saturation
fixpoint are unchanged. It therefore does not change the CB calculus and does
not require Lean re-certification.
