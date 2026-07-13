# Plan: solve ore_ont_7914, 9663, 9724 by porting Konclude's mechanisms

Status: Stage 0 COMPLETE (2026-07-11). Stage 1a next.
Branch: `payg-strategy`. Predecessor checkpoint: `592462b` (KPSet saturation
pipeline + 7914 divergence isolation, see
`results/benchmarks/2026-07-11-kpset-special-reference/README.md`).

## Context

KM sits at 576/584 ORE ok, 0 unsound. Five unsolved: 3215, 7914, 9663, 9724,
14817. Targets, in order: 7914, 9663, 9724. Six weeks of prior attempts failed
on these; the rule for this arc is: investigate first, then make very targeted
changes, PORTED faithfully from Konclude (clone at
`/home/leechuck/Public/software/Konclude`, with our added `KCOMPDBG`/`KSATDBG`
instrumentation), never invented. Test and refine after each port.

Abbreviations:
- `completion cpp` = `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
- `saturation cpp` = `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
- KM paths are under `engine/src/konclude_ht/`.

## Root cause per ontology (established, evidence below)

### 7914 (SRIQ, 68k clauses; Konclude 2.7s; KM 28min/25GB timeout)

Checkpoint `592462b` proved the saturation hand-off byte-identical vs Konclude.
The divergence is entirely in completion O