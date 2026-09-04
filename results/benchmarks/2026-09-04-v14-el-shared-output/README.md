# Shared compact-output symbol table

This panel measures the ownership-only change that transfers the EL interner's
`Arc<str>` symbol table into compact output instead of copying every symbol into
a new `String`. The external binary and JSON formats are unchanged. Binary
decoding likewise allocates each validated UTF-8 symbol directly as `Arc<str>`
instead of first constructing a temporary `String`.

IBEX jobs `51318909`, `51318959`, `51318969`, `51318990`, `51319010`,
`51319047`, `51319135`, `51319181`, and `51319222` produced 40 successful
paired trials: eight EL-route residual ontologies, five repetitions each, with
alternating arm order. The repeated submissions work around a Slurm array
throttle bookkeeping fault after the first four tasks. Task 12 was rerun after
two infrastructure-only failures on `cn603-25-l`; all accepted trials exclude
that node. Every accepted task ran on an Intel Xeon Gold 6248, selected
`route=elc`, used the expected compact-output path, compared candidate and
control JSON byte for byte, and wrote a receipt.

The control binary SHA-256 is
`5b3350b718c593dda5854b5f3df9ced72c7eb8ce76ba41e5d26dac0da8a8955e`.
The candidate binary SHA-256 is
`0232bba8f942cef184576832800b393b476c59cad1ce8bcc1d79700c0191aa12`.
The source archive SHA-256 is
`5a16c72030bf16114d55b090da1e0c99e03f312e3754bcaa6a6d4047ee746671`.
The deterministic digest over the sorted receipt checksums is
`475f96775f876e25417ed4b592b472234040413be1f6abfdd07b8dd646b833fb`.

Across all 40 paired trials, candidate/control geomean ratios are 0.994672 for
wall time, 0.999216 for peak RSS, and 0.878242 for compact-output construction.
The corresponding medians of paired ratios are 0.993865, 0.999794, and
0.870197. Thus the intended phase is about 12 percent faster, end-to-end wall
time improves by about 0.5 percent, and peak memory is effectively unchanged.
The small per-ontology wall differences around one cross in both directions,
so this is retained as a general low-risk reduction in output work rather than
as a new strict per-ontology win.

`paired-summary.tsv` gives per-ontology medians and medians of paired ratios.
Raw receipts and outputs remain in the ignored local `.work/` evidence tree and
under `/ibex/scratch/hohndor/km/v14-el-shared-output-20260904`.

Validation on the source tree passed 102 EL-completion unit tests, five compact
EL binary-I/O tests, five rule-route integration tests, and 17 rule conversion
tests. No calculus rule, ordering, routing decision, serialized format, or
derived fact changes, so Lean re-certification is not required.
