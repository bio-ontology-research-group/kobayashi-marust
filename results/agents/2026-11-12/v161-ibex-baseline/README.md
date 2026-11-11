# v1.6.0 reference stage on Ibex: baseline for v1.6.1

Ibex jobs 55504234 (build `km-el-reference` from the v1.6.0 tag tree; sha256
a54d6fa0..., identical to the ws build) and 55504235 (array, 214 tasks, 1 CPU,
96 GB, 330 s per input). Inputs: the 213 ORE inputs and one fixture that
`km-el-reference --recognize-only` accepts but the forced v1.6.0 stage did not
publish in the ws P3 rerun (`results/agents/2026-11-10/v160-p3-rerun/`).
Binary: the v1.6.0 release km (d1a99d67...), `KM_REFERENCE_FORCE=1
KM_THREADS=1`; the checker ran through a wrapper recording its exit code,
stderr, wall time and peak RSS (`run.sbatch`). Rows: `rows.tsv`.

| outcome | inputs |
|---|---:|
| published | 45 |
| Lean stage finished (dense JSON 17 to 43 GB, peak RSS 20 to 55 GB), km timed out parsing it | 25 |
| stage budget (300 s) | 116 + 12 killed with km |
| Rust guard: not pure EL/ALC clause stream | 14 |
| `Stack overflow detected` (ore_ont_1559, exit 134) | 1 |

Findings:
- The "exit 2 after printing the matrix" of the ws P3 rerun (18 rows there)
  does not reproduce with memory: 12 of those inputs publish here, the others
  run into the time budget. On ws (strict overcommit, about 25 GB commit
  headroom while other jobs ran) the same inputs fail with `failed to create
  thread` or `INTERNAL PANIC: out of memory` at 1.4 to 2.4 GB RSS. The cause
  is host memory exhaustion by the dense answer; the Rust stage reported
  stdout's first line (the matrix) instead of the checker's stderr.
- The dense `named x named` output dominates both memory and time.
