# Konclude comparator and pilot

The source-history adapter is `konclude_incremental.py`. It performs a fresh
Konclude process for each revision through OWLlink, with one worker. It does not
claim retained incremental inference. The executable is the retained official
Konclude v0.7.0 binary at `/ibex/scratch/hohndor/km/Konclude-official`, SHA-256
`5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3`.
It needs `LD_LIBRARY_PATH=/home/hohndor/bench/compat` on the selected IBEX nodes.
The library hash and linked-library paths are retained in the run root.

## Interface capability

The [official supported OWLlink commands](https://github.com/konclude/Konclude)
include Tell and LoadOntologies but do not list Retract. The
[OWLlink retraction extension](https://www.w3.org/Submission/owllink-extension-retraction/)
defines deletion as an additional interface capability. Consequently this adapter
reports the deletion/exchange retained arm as unsupported by the available
interface. This does not establish that all Konclude implementations lack any
incremental internal code. Addition-only retained reasoning is not yet measured.

## Canonical output and timing

One request loads the unchanged source snapshot, asks whether owl:Thing is
satisfiable, and requests the full subclass hierarchy. The adapter expands
synset equivalences and computes transitive superclass closure over full IRIs.
It emits the shared `C`, `U`, and `S` format, excluding reflexive, top/bottom,
and unsatisfiable-subject subsumption rows. Frozen declarations remain in the
source sent to Konclude. UnsatisfiableKBError is an explicit inconsistency
answer; other errors or missing responses fail the run. The adapter preserves
the raw XML and stdout/stderr for review. Compressed `.ofn.gz` snapshots are
expanded into a temporary file in the output directory before invocation.

`process_e2e_s` includes executable startup, source parsing, inference and XML
serialization. `extract_write_s` covers canonicalization and signature writing.
`prepare_decompress_request_s` covers decompression and request preparation.
These intervals must not be compared directly with Java inference-only timing.
GNU time files record per-process RSS. The pilot Slurm allocation has a 20 GiB
job cap; it is not evidence of a general external process-tree RSS sampler.

## Pilot evidence

Remote root: `/ibex/scratch/hohndor/km/dynamic-benchmark-20260917`.
The pilot job 51981146 completed successfully. All six chain-control states
and all six ADO states match the fresh HermiT canonical signatures byte for
byte. Per-revision timing, input/binary/signature hashes and reference hashes
are retained in `konclude_pilot_results.json` and remotely under
`results/{chains,ado}/konclude/fresh/`. Median process end-to-end times over
six states were 0.0664 s (chains) and 0.1166 s (ADO). These are pilot figures,
without warmup or replicated measurements, not release benchmark results.

Analytic controls (job 51981158) verify equivalence, superclass closure,
unsatisfiable classes, a named class equivalent to top, isolated declarations,
and global inconsistency. Both signatures match independently specified answers.
The first control run exposed the need to handle UnsatisfiableKBError explicitly;
its failed evidence remains in `konclude-controls/results/`, with corrected
results in `konclude-controls/results-v2/`.

`konclude_oracle.py` accepts the common extractor's one-shot JSON init request
and returns a canonical classification JSON response. It starts a fresh process
for every call. Job 51981172 checked a two-path entailment, one surviving path,
and deletion of both paths; all passed. That job also classified a gzip snapshot
and matched HermiT. The wrapper subsequently stopped detaching the reasoner into
another process group, so the extractor's outer timeout can clean up the child.
No KM reasoner implementation changed.
