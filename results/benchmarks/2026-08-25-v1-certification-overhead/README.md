# v1.0.0 certification/runtime overhead audit

The fresh immutable v1.0.0 sweep showed large regressions relative to the
byte-identical v0.2.36 release baseline on several production routes. ORE4604
rose from 11.5844 seconds to 127.0426 seconds while retaining full-IRI
signature `d07c82fff63f...`. The paired Slurm diagnostic runs the exact pinned
v0.2.36 and v1.0.0 binaries sequentially on one exclusive Gold-6248 node with
`KM_TIMING` and `KM_PROF_TIME`, requires byte-identical JSON, and records
process peak RSS. This is diagnostic evidence only; release measurements still
require the strict full-corpus harness.

The first submission, `50854386`, was cancelled while scheduler-pending before
it consumed an allocation because the script lacked the bridge's internal
phase trace. Its replacement additionally enables `KM_BRIDGE_PHASES`,
`KM_HT_STATS`, and the HT candidate trace.

Replacement `50854395` then failed before invoking either reasoner because
IBEX did not define `SLURM_TMPDIR`. It produced no classification or timing
evidence. The corrected runner uses a job-specific node-local `/tmp` fallback
and removes it on exit.

Job `50854500` completed the corrected same-node pair. Both binaries emitted
JSON with SHA-256 `f0b015d68903...`. The retained v0.2.36 binary converted
344,722 clauses in 0.67 seconds and completed in 10.71 seconds at 932,868 KiB
peak RSS. The pinned v1.0.0 binary spent 124.78 seconds in the same conversion,
completed in 135.94 seconds, and reached 1,624,300 KiB. This localizes the
regression before either reasoning worker runs.

The regression came from stable source-concept deduplication in the optional
bundle-projection proof payload. v1.0.0 searched a growing vector for every
concept occurrence. ORE4604 contains more than 80,000 distinct concepts and
hundreds of thousands of occurrences, making proof-payload construction
quadratic. Candidate `e6d257b3a8a9...` uses first-seen hash deduplication and
does not construct or serialize source-proof payloads during ordinary
classification. Explicit proof-carrying HT runs retain the payload. The
payload is checker evidence and is not consumed by any reasoning rule.

On the workstation, candidate `e6d257b3a8a9...` classified the exact ORE4604
input in 14.43 seconds at 839,428 KiB peak RSS. Its output was byte-identical
to retained v0.2.36. The corresponding local v0.2.36 run took 14.60 seconds at
929,708 KiB. These are diagnostic measurements, not substitutes for the
same-node IBEX gate or the strict full-corpus release sweep. IBEX job
`50855494` was intended to run the pinned v0.2.36, v1.0.0, and candidate
binaries sequentially and require byte-identical output from all three.

The workstation-built candidate could not execute on IBEX because it links
against glibc 2.39, which is newer than the compute-node runtime. Consequently,
job `50855494` contains valid v0.2.36 and v1.0.0 control measurements but no
candidate measurement. Panel job `50855591` likewise completed only its first
v0.2.36 control before failing at candidate process startup. Neither job counts
as a candidate performance or correctness gate. Source snapshot
`1075204f0309...` under
`/ibex/scratch/hohndor/km/v1-cert-overhead-v4-20260825` is instead built by
Slurm job `50855718`, ensuring ABI compatibility before repeating both gates.

The ABI-compatible v4 triple `50856045` passed exact-output comparison on
ORE4604. Candidate wall/RSS were 12.39 seconds/837,988 KiB, versus v0.2.36 at
10.71 seconds/927,356 KiB and v1.0.0 at 138.65 seconds/1,625,216 KiB. The v4
panel `50856046` then exposed a separate routing regression. ORE7581 remained
byte-identical but rose from 23.29 seconds/1,871,892 KiB to 51.70
seconds/11,632,432 KiB; ORE9663 subsequently hit the panel's 300-second cap.
The dependency-held v4 full sweep `50856048` was cancelled before allocation.

Both regressions had one cause. An absent typed-ABox payload uses the serde
default `complete=false` with all ABox collections empty. A fail-closed caller
treated this identity case as a failed ABox installation and suppressed the
otherwise faithful HT/bridge racer. Non-empty incomplete ABoxes must still be
rejected, but an empty ABox has nothing to certify or install. Candidate v5
returns success only for that empty identity case and has a focused unit test.
On the workstation ORE7581 then restored the bridge, retained byte-identical
output, and completed in 21.00 seconds at 1,871,932 KiB, versus the local
v0.2.36 control at 22.14 seconds with the same resource scale. Source snapshot
`06da990a73bc...` built natively as binary `e9f06cda45e0...` in job `50856587`.
Resource-guarded seven-ontology panel `50856926` must pass before dependency-held
full sweep `50856927` can allocate.

Panel `50856926` passed all seven byte-identity and resource guards. Candidate
v5 versus v0.2.36 wall seconds were: ORE7581 16.10/17.21, ORE4604 11.15/10.89,
ORE9663 20.99/22.18, ORE10016 8.29/8.28, ORE5566 6.85/6.99, ORE8982
6.49/6.54, and ORE7127 7.96/8.28. Candidate RSS stayed within the 1.25x guard
on every row, with the largest deltas under one percent. The successful panel
released strict sweep `50856927`; it remains scheduler-pending until Gold-6248
nodes are available.

The first v5 full-array submission `50856927` failed its first allocated tasks
before invoking KM because the new sweep root lacked the immutable harness's
`ore592.txt` and helper scripts. It produced no terminal ontology row and was
cancelled immediately after the Slurm-output sanity check detected the missing
file. The exact eight baseline harness files were copied and byte-compared into
the candidate root. Mandatory single-task gate `50858011` then completed
ORE33 with an exact Konclude match, byte-identical terminal/checkpoint records,
binary `e9f06cda45e0...`, route `production_all`, 0.2714 seconds, and 34.19 MiB.
Only after that gate passed was resumable full array `50858012` released; its
task 0 reused the validated row and subsequent tasks are now running.
