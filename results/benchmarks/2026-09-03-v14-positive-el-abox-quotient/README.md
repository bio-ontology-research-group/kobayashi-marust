# Streaming positive-EL ABox quotient

This targeted experiment measures the streaming positive-ABox quotient on ORE
1579, whose full frontend alone previously exceeded its fastest-baseline wall
target. The candidate source is commit
`18d746bda7d2259211a354261ac28264be62fa69`; the separately committed
`e196f5156b0c057b87b47ab25387a926f67e8b29` adds only a fixed-size source-density
admission gate before this same quotient implementation.

The source archive SHA-256 is
`7e44f2f03fef1a5f8afc46c753716cb54083653857b7f249684794dea45fca07`.
Slurm build job `51267648` passed the deployment check and produced binary
SHA-256 `ada2b03383a17807f46d89a5639202a065695e6ceed9a5dde0b0dba770f4d138`.
Panel job `51269328` ran five interleaved control/candidate repetitions on Intel
Xeon Gold 6248 nodes with four CPUs, 8 GiB, and a 180-second process timeout.

| Arm | Runs | Median wall (s) | Median peak RSS (MiB) |
|---|---:|---:|---:|
| merged-certificate control | 5 | 6.24 | 473.88 |
| streaming quotient | 5 | 2.20 | 219.77 |

All ten tasks emitted `BENCH_COMPLETE`; all 20 raw/normalized JSON files were
present. Every normalized result had SHA-256
`144cf28b50c7a969a29d76e6bf3f59185c42f45b04fd850d8ef0601501ac3323`,
the established accepted result. The candidate emitted the quotient-acceptance
marker in all five runs.

ORE 1579's strict targets are 2.4938 seconds and 596.66 MiB. The candidate
therefore closes both dimensions in this targeted panel. The evidence archive
under `.work/artifacts/v14-positive-abox-quotient/ibex/archive` contains the
source archive, build and benchmark scripts, deployment receipt, scheduler
logs, timings, raw and normalized outputs, and a verified 55-entry manifest.
Its `SHA256SUMS` file has SHA-256
`1351f223aa70423fcc991f974576228c8e1f1a00b083f010492b6f690de6d058`.

An initial panel submission (`51269291`) failed before reasoner execution
because its hard-coded control digest contained a transcription error. The
digest guard rejected every attempted task and no output was accepted. The
corrected job above used the control binary's directly verified digest.
