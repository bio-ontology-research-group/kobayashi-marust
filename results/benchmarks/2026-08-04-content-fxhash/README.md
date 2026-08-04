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

## Complete IBEX production sweep

The source-bound IBEX build used archive SHA-256
`334e1a092cf9bfc5afca6a9a5ab3999939b9b156442e15dfe96f388dfb2bed63`.
Build job `50014324` recorded `BUILD_COMPLETE revision=df5bb5b`; the deployed
`km` binary SHA-256 was
`546ecedfd926794879e1ddae60cfd74e00896a264b0513324afaef0060161089`.
Sanity job `50015185` preceded exclusive resumable array job `50014326`.

The terminal audit checked all of the following:

- 592 unique ontology rows and all array indices `0..591` exactly once;
- 592 valid route profiles and 592 task logs with terminal markers;
- the expected binary hash, checkpoint flag, and route trace on every row;
- no malformed JSON, temporary artifacts, or runner failure markers;
- collision-safe full-IRI fingerprints for ORE 3524, 13503, 4669, and 15703.

All checks passed. The sweep produced 591 `ok` rows and the expected error for
ORE 1194. Verdicts were 588 `match`, two previously established consistency
discrepancies, one no-gold case, and the ORE 1194 error. Comparison with the
complete `a4eb829` sweep found zero status, verdict, or signature differences.

For the 591 paired successful rows:

| measure | `a4eb829` | `df5bb5b` |
|---|---:|---:|
| mean wall | 6.1310 s | 6.1991 s |
| median wall | 0.2794 s | 0.2766 s |
| mean peak | 844.50 MB | 844.44 MB |
| median peak | 44.19 MB | 45.23 MB |

The corpus-wide 5%-trimmed mean wall delta was +0.0021 seconds, effectively
neutral. The routes that exercise the changed CB interning path improved:
`nominals` mean wall fell from 2.8930 to 2.8114 seconds (2.82%), and
`cb_plain16` from 10.7877 to 10.5138 seconds (2.54%). `production_all`, which
also contains many EL, HT, and very small cases unaffected by this change, was
0.94% slower in one sweep. The local completing CB workload above remains the
source-isolated hot-path measurement.

The authoritative per-ontology table is
[`automatic-results.tsv`](automatic-results.tsv), SHA-256
`38cf911d512f10d28402f581f93095eff9517f362ccad45f17fd81a39901a45d`.
The comparison table for `a4eb829` had SHA-256
`42fbd1c6bf02a439e006cad0d215ee3b43469ef87a7e2acfb63100b85ba5c730`.
