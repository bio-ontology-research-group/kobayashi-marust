# v1.4 minimum-head integrated automatic-route sweep

IBEX array `51331621`, with the infrastructure-only retry `51332312` for
array task 266, ran all 592 ORE inputs through `KM_ROUTE=auto`. Each ontology
had a 480-second timeout and 20-GiB reasoner cap on Intel Xeon Gold 6248
nodes. The exact integrated source was commit `677f023` plus the retained
working-tree patch with SHA-256
`3be845bbb0bce711427e49482e0d646b92457413a49dc534dbf690da58a36faf`.
IBEX build job `51331531` produced binary SHA-256
`8cb733feb586287228c8a3894b213d1c9fca130525033465d9fa458516984c04`
from source archive SHA-256
`e6550a9fd0952d29b4680775d8927f49b22c9a8c1464f6bbcdd4b606cdfb8554`.

The completion audit found exactly 592 unique expected results, 592
checkpoints, and 592 task-complete markers, with no missing, extra, or
duplicate ontology. Every result reports `status=ok`, the pinned binary hash,
and a nonempty route trace. Of the retained external signatures, 588 match
directly. ORE 2669 and 15516 retain their independently adjudicated
inconsistent verdicts, while ORE 10860 and 1194 have no authoritative full
external signature. This preserves verified ORE coverage at **592/592**.

The first attempted array, `51331421`, was rejected by its output sanity check:
the workstation-built binary required GLIBC 2.39 on older IBEX nodes and
produced no result records. That array was cancelled and is not benchmark
evidence. Task 266 of the valid array encountered a node-local stale Python
shim before invoking KM. The retry pins `/usr/bin/python3`; no KM output from
the failed infrastructure attempt was retained as a result.

For the 592 valid runs, mean and median wall time are 1.4592 and 0.1197
seconds; mean and median peak process-tree RSS are 209.36 and 24.31 MiB. The
largest peak is 16,714.31 MiB. Against the 589 ontologies with comparable
external targets, this one-shot sweep is strictly faster on 506, strictly
lower-memory on 527, and wins both measures on 493. The authoritative
repeated-evidence composite remains **525/589**, with 64 residuals: this sweep
is a correctness and integration gate, not a replacement of repeated medians
near performance boundaries.

`per-ontology.tsv` contains the complete comparison against the frozen v1.4
target ledger. Raw result JSON, checkpoints, task logs, source receipt, and
build receipt remain under
`/ibex/scratch/hohndor/km/v14-min-head-integrated-full-20260904/` and the local
working artifact mirror `.work/artifacts/v14-min-head-integrated/`.
