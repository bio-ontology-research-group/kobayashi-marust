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

## Integrated regression and correction

The first density-gated integrated source, commit `ec70703`, was deliberately
rejected after full sweep `51269428`. It produced 591 `ok` rows and one timeout:
the quotient frontend was expensive before it could reject expressive ORE
15846, and ORE 9654 timed out after the same inappropriate attempt. The retained
rejected-sweep archive records all 592 terminal rows; no result from it is used
as release evidence.

Commit `53ab180` adds a streaming source-contract prepass that rejects unions,
complements, universal restrictions, number restrictions, nominals,
functionality, disjoint/equivalent class constructors, negative assertions,
data constructors, keys, rules, and imports before quotient allocation. Commit
`ea34aad` adds the explicit `KM_NO_POSITIVE_ABOX_QUOTIENT` ablation switch.

Build job `51274343` produced the corrected binary at commit `ea34aad` with
SHA-256
`f5b2c52785c8fe28c0ba2932f8dcd9e05bc0b2b6a53e335c98731a71aa884591`.
Same-binary panel `51274344` ran three repetitions per arm:

| Ontology | Arm | Median wall (s) | Median peak RSS (MiB) | Quotient accepted |
|---|---|---:|---:|---:|
| 1579 | disabled | 5.05 | 473.48 | 0/3 |
| 1579 | enabled | 1.83 | 219.75 | 3/3 |
| 15846 | disabled | 9.66 | 513.61 | 0/3 |
| 15846 | enabled | 9.78 | 514.48 | 0/3 |
| 9654 | disabled | 18.09 | 996.05 | 0/3 |
| 9654 | enabled | 14.28 | 1001.89 | 0/3 |

Each ontology had one normalized hash across both arms. The expressive-source
prepass therefore restores 15846 and 9654 without disabling the 1579 quotient.

Corrected full sweep `51274570` produced 592 results, 592 checkpoints, 592
Slurm logs, 592 `TASK_COMPLETE` markers, and no temporary files. All rows have
`status=ok`, the exact binary digest, and a selected-route trace. The verdict
population is 588 retained-gold matches, two independently adjudicated
consistency mismatches, and two no-gold certified cases. Every semantic field
matches the prior accepted 592/592 sweep. ORE 1579 completed in 1.8762 seconds
at 220.2 MiB.

The corrected sweep's one-shot strict joint count is 490/589. As elsewhere in
the v1.4 evidence, narrow boundary claims use repeated medians rather than
substituting one noisy sweep sample. Adding the repeated 1579 closure to the
preceding evidence composite gives 525/589 strict joint wins and 64 residuals.

The complete corrected build, panel, and full-sweep evidence occupies 138 MiB
under `.work/artifacts/v14-positive-abox-quotient-final2`. Its verified
1,890-entry `SHA256SUMS` file has SHA-256
`0ff8802f8669ed7a4d8d0aded8c74dbb5bb0450897a473af1f2a347cd63a9126`.
