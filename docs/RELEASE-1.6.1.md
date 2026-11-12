# KM 1.6.1 release notes

Draft. Release commit and tag are filled in at release.

## What changes

KM 1.6.1 makes the v1.6.0 reference stage scale to the suite's large
inputs and makes its failures report their cause. No theorem of v1.6.0
changes; the acceptance contract is `docs/V1.6.1-ACCEPTANCE.md`.

- **Sparse answer.** `km-el-reference` publishes one row per requested
  name (an unsatisfiability flag and the named subsumers) in the format
  `sparse-v1` and no longer builds the dense `named × named` list.
  `SparseTaxonomy.lean` defines the rows and their dense denotation
  `SparseTaxonomy.dense` and proves that what the binary prints denotes
  exactly what `elReferenceExecution` and `alcReferenceExecution` publish
  (`sparseElReference_agrees`, `sparseAlcReference_agrees`), so
  `kmSupervisor_sound` and `kmSupervisor_complete_on_EL_or_ALC` cover the
  printed answer. Publication takes the correctness proof as an argument
  (`publishSparse`), which replaces v1.6.0's runtime recheck of the
  answer. The Rust stage checks the row shape and declines on any
  deviation.
- **No stack overflow on large inputs.** Eleven list functions of the EL
  and ALC recognisers recursed once per clause and overflowed the 256 MiB
  stack above about 2 M clauses. Each has a tail-recursive twin registered
  with `@[csimp]` and proved equal to the original, so the compiled code
  changes and every proof keeps reasoning about the original definition.
  The recogniser handles a synthetic stream of 10 M clauses.
- **Failures name their cause.** The Rust stage takes a decline reason from
  the checker's stderr first (v1.6.0 reported the first line of stdout,
  which could be the whole answer); `km-el-reference` reports a write
  failure as `io error` with exit 4; the metadata guard names the condition
  that fired (for example `el_abox`). The v1.6.0 "exit 2 after printing the
  matrix" failures were host memory exhaustion by the dense answer.
- **Phase timing.** `KM_REFERENCE_TIMING=1` makes `km-el-reference` print
  one line per phase (read, JSON, source, recognition, closure, readout,
  output); with `KM_TIMING` set, `km` passes them on.

## What the stage covers now

Forced suite run on Ibex (`KM_REFERENCE_FORCE=1`, all 1,781 checkers-on
inputs, `results/agents/2026-11-12/v161-q2/`):

| | v1.6.0 | v1.6.1 |
|---|---:|---:|
| recognised inputs published (of 592) | 378 | 575 |
| all inputs published | 410 | 628 |
| published in v1.6.0, not now | | 0 |
| forced answer differs from the production answer | 0 | 0 |

The 17 recognised inputs that do not publish: 14 carry ABox assertions,
which the stage's metadata guard refuses (`el_abox`; ABox support is stage
2 of the frontend plan, `docs/V1.6.2-FRONTEND-PLAN.md`), and 3 exceed
km's 300 s budget, as in v1.6.0. The largest published input is
ore_ont_1559 (394 MB, 2.9 M clauses; 202 s in the checker, 291 s in km).
The practical limit is now the closure: it takes 78 percent of the
checker's time over all published inputs, and on the largest inputs 76 to
81 percent. Median checker time on the published inputs is 0.3 s, the
95th percentile 38 s.

## Speed and correctness (Ibex, same day)

(filled at release)

## Certification

(filled at release)

## Records

`docs/V1.6.1-ACCEPTANCE.md`, `results/agents/2026-11-12/` (baseline,
sparse answer, stack fix, Q2 suite run), `docs/V1.6.2-FRONTEND-PLAN.md`
(next release).
