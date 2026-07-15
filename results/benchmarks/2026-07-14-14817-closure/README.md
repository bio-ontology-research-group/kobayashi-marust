# ORE 14817 closure artifacts

Status: complete. This directory records the Konclude comparison, the exact
cardinality-successor port, the production closure, and the 592-ontology IBEX
regression gate.

## Outcome

The final Rust 1.85 Bullseye binary has SHA-256
`c7c3eefe49ac95a7feaa7c1b70ada2ae65b820097cbe0456b0ab4be82c61ba07`.

| IBEX job | Scope | Result | Wall | Peak RSS |
|---|---|---|---:|---:|
| 48811085 | preceding production binary, full 14817 | timeout | 240 s | within cap |
| 48841110 | cache/task-slice candidate, full 14817 | timeout at 9,217/9,722 residue subjects | 240.03 s | 4,289,560 KB |
| 48849853 | old subject 85031 trace | deferred | 51.27 s | 5,862,880 KB |
| 48849538 | trusted Konclude target trace | target callback in 125 ms | 50.34 s full run | 3,078,512 KB |
| 48852901 | fixed subject 85031 | completed | 14.66 s | 1,727,144 KB |
| 48853037 | fixed full 14817 with counters | exact match | 195.16 s | 4,234,340 KB |
| 48853569 task 518 | fixed full 14817, sweep flags | exact match | 56 s | 3,365,116 KB |

The final taxonomy contains 1,184,692 subsumptions, no unsatisfiable classes,
and the same consistent verdict as Konclude. Gold comparison reports zero extra
and zero missing pairs.

## Root cause and correction

The old production ≥-rule used the reduced
`ht_create_distinct_successors` helper. It created distinct nodes, role links,
and qualifiers but bypassed Konclude's saturation replay and cache setup.
Konclude's `applyATLEASTRule` creates an `ATLEAST` dependency and delegates to
`createDistinctSuccessorIndividuals`, which saturation-expands every new
successor before link installation and qualifier processing.

For target subject 85031 (`UBERON_0014672`), the old KM trace created successors
1001 through 1006 without expanding them and began its nine expansion events at
1007. It then produced 72,670 disjunction replacement events in 51 seconds.
Konclude expanded those first six successors as three cardinality-created
pairs. The corrected Rust call chain now does the same. The successful target
run expands the missing six and records only 300 replacement events over the
complete run.

The source and full causal account are in `../../../docs/SOLVE-14817.md`.

## Full-corpus gate

Array job 48853569 ran all 592 ORE ontologies at 240 seconds and 20 GB per task.
Every result row records the same final binary SHA.

| Metric | 9724 baseline | 14817 closure |
|---|---:|---:|
| completed | 574 | 575 |
| timeout | 18 | 17 |
| exact match | 514 | 515 |
| incomplete | 45 | 45 |
| unsound | 5 | 5 |
| both | 1 | 1 |
| inconsistent | 6 | 6 |
| no gold | 3 | 3 |

The only changed result is `ore_ont_14817.owl`, from timeout to exact match.
No previously exact ontology regressed. `sweep-aggregate.json` is the
machine-readable report.

## Artifact map

- `ibex_14817_konclude_uberon0014672_completion_trace.sbatch` reproduces the
  trusted target trace.
- `ibex_14817_subject_85031_sat_trace.sbatch` and
  `ibex_14817_subject_85031_watch136767.sbatch` reproduce the missing-expansion
  and restored-branch-state diagnoses.
- `ibex_14817_subject_85031_atleast_port.sbatch` proves the isolated fix.
- `ibex_14817_atleast_port_full.sbatch` proves the full ontology with detailed
  counters.
- `ibex_14817_fullsweep.sbatch`, `aggregate_14817_fullsweep.py`, and
  `sweep-aggregate.json` reproduce and summarize the full regression gate.
- The remaining scripts preserve controlled cache, scheduling, ordering, and
  subject-isolation experiments performed before the decisive source
  divergence was found.
