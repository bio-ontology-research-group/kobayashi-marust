# EL residual phase profile

This panel profiles eight ORE 2015 EL-route residuals after the shared-symbol
interner change. Slurm array job `51318397` completed all eight tasks on IBEX.
Every task used an Intel Xeon Gold 6248 CPU, exited zero, selected `route=elc`,
and produced a receipt bound to binary SHA-256
`5b3350b718c593dda5854b5f3df9ced72c7eb8ce76ba41e5d26dac0da8a8955e`.

The first submission, job `51317694`, was intentionally rejected by its
fail-closed wrapper: two tasks encountered an over-specific CPU-banner check,
and six successful reasoner executions encountered a stale expected timing-log
label. Job `51318397` relaxed the banner match to the still-recorded Gold 6248
model and asserted the actual `frontend done ... route=elc` marker. The rerun
retains the binary, ontology, output, host, CPU, exit, wall-time, memory, and
phase bindings in the per-ontology receipts under the ignored `.work/` tree.

## Interpretation

Frontend work is the largest measured phase for seven of eight ontologies,
taking 1.29 to 2.24 seconds where detailed frontend timing is available. The
exact-EL screen handles ontology 6722 and reaches the EL route at 0.96 seconds;
for that case compact-output construction is the largest instrumented EL phase
at 0.678 seconds. Saturation dominates the instrumented EL phases only for
7868 and 13224. Consequently, the next general optimization should target
frontend parsing/normalization or compact-output construction before changing
the completion calculus. No calculus rule changed in this profiling work.
