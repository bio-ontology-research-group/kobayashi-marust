# Serial hypertableau model reuse and pruning

Commit `298dd68` enables two existing sound optimizations in serial
hypertableau workers spawned by the default `km classify` route.

- Witness reuse skips a phase-1 satisfiability test when a named concept already
  occurs in a completed model. That node is already a satisfiability witness, and
  its label supplies a conservative candidate set. Phase 2 still verifies every
  retained candidate.
- Model pruning uses a satisfiable `A ∧ ¬B` model to remove every concept absent
  from the model root from `A`'s remaining candidate set. The same model is a
  counterexample to each removed subsumption.

The parallel hypertableau classifier already performs model-based pruning
internally, so these flags affect serial workers only. The change does not alter
hypertableau rules, blocking, branching, routing, or output construction. It
only avoids redundant independent satisfiability calls, so Lean
re-certification is not required.

## Validation

The complete release test suite passed serially: 1,952 library tests passed,
eight were ignored, and every binary, integration, and documentation test
passed. An earlier parallel library invocation exposed an unrelated
environment-variable test isolation failure; its isolated rerun and the full
serial suite passed.

IBEX array job \`50046596\` tested all 70 ontologies currently known to use a
successful serial-hypertableau-related automatic route. Both arms used the
exact source-bound `9ee269e` binary, SHA-256
`be326fe76e9cbe52d574ad8d5f3c037ae3db9f9fd3d25b498a1f90492534a6dd`;
the candidate arm added only `KM_HT_WITREUSE=1` and
`KM_HT_MODELPRUNE=1`.

The strict audit verified all 70 ontology indices, completion markers, 140
zero exit codes, 280 timing/digest receipts, and 70 exact output-digest pairs.
No output differed.

| Metric | Baseline | Reuse + pruning | Change |
|---|---:|---:|---:|
| Total wall | 675.60 s | 571.84 s | -15.36% |
| Mean wall | 9.6514 s | 8.1691 s | -15.36% |
| Median wall | 0.5750 s | 0.5650 s | -1.74% |
| Mean peak RSS | 1,094,331 KiB | 1,085,540 KiB | -0.80% |
| Median peak RSS | 182,842 KiB | 184,378 KiB | +0.84% |

The material speed gains were ORE7499, 83.81 to 33.75 seconds (-59.73%);
ORE10702, 2.91 to 1.29 seconds (-55.67%); and ORE6934, 168.74 to 116.25
seconds (-31.11%). ORE15846, the 19 GiB tail case, remained effectively neutral
at 205.45 versus 206.50 seconds and reduced peak RSS by 47,116 KiB. ORE7474
moved from 7.53 to 7.93 seconds in one pair; the absolute 0.40-second change is
small relative to scheduler noise and did not change output or memory.

The complete per-ontology measurements and output digests are in
[`panel-results.tsv`](panel-results.tsv). The array script and exact ontology
list in this directory reproduce the panel. A complete source-bound
592-ontology production sweep remains the final promotion gate.
