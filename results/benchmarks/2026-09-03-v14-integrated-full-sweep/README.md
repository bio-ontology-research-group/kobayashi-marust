# v1.4 integrated automatic-route sweep

IBEX array `51252846` ran commit
`88d3ffd42d9c13aa5b14f050f9180c668c691b72` through all 592 ORE inputs with
only `KM_ROUTE=auto`, a 480-second timeout, a 20-GiB reasoner cap, and 16 CPUs
on Intel Xeon Gold 6248 nodes. Build job `51252616` produced binary SHA-256
`f7ccb74550d04a31fb2c35442d401d62e8105edb072a166474f7d78f971bbffa`.

The run has 592 result files, 592 checkpoints, 592 Slurm outputs, and 592
`TASK_COMPLETE` markers. Every result uses the pinned binary and returns
`status=ok`. Of the retained Konclude signatures, 588 match directly. ORE 2669
and 15516 retain their independently adjudicated inconsistent results; the
stored Konclude outputs are parse-failure artifacts. ORE 10860 and 1194 have no
authoritative full baseline signature and retain their independent
certificates. Thus the automatic route completes all 592 ontologies without a
new correctness discrepancy.

Across the 592 single runs, mean and median wall time are 1.4259 and 0.1177
seconds. Mean and median peak process-tree RSS are 208.77 and 22.07 MiB.
Against the 589 inputs with a correct external baseline completion, this
one-shot sweep is strictly faster on 509, strictly lower-memory on 521, and
wins both measures on 493.

The one-shot strict count is deliberately not substituted for the repeated
candidate panels near a threshold. The preceding bounded-near-EL panel gives
497/589 strict wins on medians. The integrated five-repetition context-parallel
EL panel plus this full sweep confirms five additional disjoint recoveries:
15929, 2828, 4802, 5612, and 795. The five-repetition production-routing panel
confirms eleven more: 10127, 10697, 11207, 15725, 2195, 3164, 3658, 4187,
4827, 7901, and 9958. The evidence-composite strict score is therefore
513/589 at this sweep checkpoint.  A subsequent source-feature extension of
the same context-parallel EL schedule recovered ORE 7567 under the automatic
route. A subsequent compact expressive nominal scheduling gate recovered ORE
5184. A ten-repetition boundary confirmation also established that the
unchanged automatic route for ORE 9096 beats both external targets on its
median. These recoveries raise the current evidence-composite score to
**516/589**, with 73 comparable ontologies remaining. Their repeated
confirmations are recorded in `../2026-09-03-v14-elc-wide-role-routing/`,
`../2026-09-03-v14-compact-nominal-ht-scheduling/`, and
`../2026-09-03-v14-9096-boundary-confirmation/`. The composite uses medians for
every claimed narrow recovery and this full sweep as the coverage and
regression gate.

`per-ontology.tsv` records the complete one-shot comparison against the frozen
v1.4 external target ledger. Raw results and Slurm logs are retained in
`.work/artifacts/v14-production-auto-integration/full-sweep-complete.tar.gz`,
SHA-256
`9a42b03442eaee68212df49a21dbbc6eccbc6a5bb51a70b1c34bb6604f63deeb`.
