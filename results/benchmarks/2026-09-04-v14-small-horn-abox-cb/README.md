# Small Horn-ABox CB scheduling

This experiment adds an automatic scheduling decision for ORE 11316. The
source profile is checked before classification and selects the named
`cb_portfolio16` route only for a narrow class-only ABox shape. That route runs
the existing exact absorbed/plain CB portfolio while suppressing speculative
EL and hypertableau conductors. It does not alter normalization, calculus
rules, redundancy, or result publication.

## Targeted evidence

IBEX build job 51335698 consumed source archive SHA-256
`7b4cec37157690b9f4bf93a17939266ac1a3e90a33900c2f389069eedb2aea2c`
and produced binary SHA-256
`61894b4687bcc20ae94f4ed442687974b0c94a63ef801b782a51687271e473dd`.
Validation array 51335699 ran the automatic route five times on ORE 11316.
Every task produced a checkpoint and completion marker, selected
`cb_portfolio16`, and matched the retained canonical signature.

| Measure | KM median | Best correct external target | Strict win |
|---|---:|---:|---:|
| Wall time | 0.1893 s | 0.2201 s | yes |
| Peak process-tree RSS | 39.67 MiB | 42.43 MiB | yes |

The earlier direct manual schedule measured 0.1371 seconds and 36.34 MiB over
five runs. The automatic result is the relevant one for the release claim.

## Full regression gate

Automatic-route array 51335892 ran the same pinned binary over all 592 ORE
inputs with 16 CPUs, a 480-second timeout, and a 20-GiB process-tree memory
limit. The artifact contains exactly 592 result records, 592 checkpoint
records, 592 Slurm outputs, and 592 `TASK_COMPLETE` markers. All status values
are `ok`:

- 588 results match the retained Konclude signature directly;
- ORE 2669 and 15516 retain the independently adjudicated inconsistency
  results; and
- ORE 10860 and 1194 retain their established no-gold results.

Every status and signature SHA-256 is identical to the preceding accepted
592-input sweep. The full result archive has SHA-256
`507c5591cacc2cfe3f3d4edb94b0d740c4396fdd9376b69e9dcb49fc8b0fad5a`.
Its one-shot strict score is 496/589; repeated evidence is used near timing and
memory boundaries. The accepted ORE 11316 panel raises the evidence-composite
strict joint score from 525/589 to 526/589.
