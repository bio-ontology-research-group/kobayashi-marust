# Inert-role ABox probe regression sweep

Commit `dc7ad629be339618fe719da2246d21b376ee41ab` fixes the
automatic `production_all` query schedule for the frontend's private
inert-role ABox consistency probes. The public named-class query set previously
omitted those generated probes, so the route could miss a clash that involved
two asserted classes on one individual. The orchestrator now also queries the
frontend-recorded asserted classes when, and only when, the parsed frontend has
issued the exact `inert_role_abox_probe_candidate` certificate. Private probe
names remain filtered from public output.

This changes query coverage, not any calculus rule, ordering, or redundancy
criterion. The focused `certified_abox_production` integration suite contains
the synthetic joint-class-clash regression and passes all five tests.

## Full ORE regression

IBEX build job `51297215` produced candidate binary SHA-256
`c8688f6b286db2b422f1ec1df0874eadbbce0cc9e2899f35dbe143ccad70639d`
from source archive SHA-256
`12c31bcec650138c938c19f689b1a7e8b4082240e962dd0c4c5f42850e5b58b8`.
Array job `51297216` ran `KM_ROUTE=auto` on all 592 ORE inputs using Intel
Xeon Gold 6248 nodes, 16 CPUs per task, a 480-second timeout, and the 20-GiB
reasoner limit.

The fail-closed audit found:

* 592 parseable results for 592 distinct ontology names;
* 592 byte-identical checkpoints, 592 profiles, and 592 `TASK_COMPLETE`
  markers;
* no temporary files;
* the pinned candidate digest on every row and `status=ok` on every row;
* 588 retained-gold matches, the independently adjudicated inconsistency
  results for ORE 2669 and 15516, and the independently certified no-gold
  results for ORE 10860 and 1194;
* zero semantic-field differences from the accepted positive-ABox quotient
  sweep across status, consistency, signature, taxonomy cardinality,
  unsatisfiable-class cardinality, dropped-clause count, verdict, and all
  missing/extra counters.

No ORE profile activates the new inert-role probe certificate. This means the
fix closes the synthetic soundness regression without perturbing any ORE
classification. The complete 59-MiB result, checkpoint, profile, and Slurm-log
archive is retained under
`.work/artifacts/v14-inert-probe-fix/full-sweep-archive/`.
