# Positive EL ABox automatic route

This capsule validates the feature-selected exact ABox materialization route
that restores `ore_ont_1579.owl` and `ore_ont_3377.owl`.

## Correctness contract

The source gate accepts positive EL++ TBox/RBox axioms, positive class and
object-property assertions, and explicit equality/inequality between
individuals. It rejects disjunction, complement, cardinality, functionality,
concept nominals, datatypes, negative assertions, rules, imports, and bottom
roles. The normalized consumer independently requires a complete typed ABox
and a pure-EL clause set.

Individuals are unioned under `SameIndividual`. Each resulting equality class
becomes one fresh EL completion node. Class assertions seed its label and
object-property assertions become edges between those nodes.
`DifferentIndividuals` rejects an equality clash. The ontology is consistent
exactly when the EL TBox is consistent and no individual node derives bottom.
Only then may KM publish the nominal-free taxonomy.

## Evidence

The workstation release tests pass serially with 1,826 passed, zero failed,
and eight ignored. Parallel execution is not the acceptance command because
pre-existing tests alter process-wide route environment variables.

IBEX source archive SHA-256:
`05dccc44ba15f52ed7cefd9a56d35c894b289c8146015ac3961ec25eefd4432a`.
Build job 49637596 produced binary SHA-256:
`d4ccde36263f9044fc891787ad39bf543b96ab0f27a153477712fd2dadcd55c7`.

Focused automatic-route job 49637883 completed:

| Ontology | Selected route | Wall (s) | Peak (KiB) | Gold pairs | Missing | Extra | Verdict |
|---|---|---:|---:|---:|---:|---:|---|
| 1579 | `production_all` | 12.33 | 852,504 | 56,782 | 0 | 0 | exact |
| 3377 | `production_all` | 37.03 | 1,971,828 | 4,490,309 | 0 | 0 | exact |

Both consistency verdicts and unsatisfiable-class sets match Konclude.

The first focused submission, job 49637486, was rejected by the dynamic loader
because the workstation executable required glibc 2.39. Job 49637596 therefore
builds from the source-bound archive on an IBEX compute node. Job 49637597
validated 3377 but its 1579 comparator started before `ore_canon.py` was
deployed. Neither infrastructure failure is correctness evidence. Job
49637883 is the complete accepted gate.

## Files

- `ibex_build.sbatch`: verifies and builds the source archive on IBEX.
- `ibex_focused.sbatch`: runs automatic classification and complete canonical
  signature comparison under the production timeout and memory allocation.
