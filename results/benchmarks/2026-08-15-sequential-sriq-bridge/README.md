# Sequential large-SRIQ bridge evidence

Release candidate `870fb86` schedules ORE14817's already certified completion
bridge before the exact production fallback. The candidate binary is
`cc04717a29ca85be6441b668167493254600c53661ccdf66fb688b924ad2bdb0`.
The v0.2.33 baseline binary is
`645e79b99626db2fe125bfbc3df003355593d206117ebdb5d0a225bdc910afeb`.

## Focused gate

Same-node Slurm job `50548498` ran three alternating pairs on ORE14817. Every
run selected `production_all`, matched the Konclude full-IRI signature
`3c43822a005baa536d47079eac973ab6247dd54adace4643ac119bc74757445d`,
and produced the same consistency and answer counts.

| arm | wall samples s | wall mean s | RSS samples MiB | RSS mean MiB |
|---|---|---:|---|---:|
| v0.2.33 baseline | 91.7119, 92.5547, 92.0302 | 92.09893 | 5,113.38, 5,103.53, 5,085.51 | 5,100.81 |
| candidate | 91.8608, 92.3676, 92.3874 | 92.20527 | 2,827.38, 2,787.52, 2,786.38 | 2,800.43 |

The 0.12% wall movement is measurement noise. The repeated 2.30-GiB memory
reduction is the intended effect of running one complete arm at a time instead
of overlapping the bridge with the CB fallback.

## Full ORE pair

Order-balanced job `50548596` ran both binaries on all 592 ontologies on
exclusive Intel Xeon Gold 6248 nodes. It contains exactly 1,184 terminal JSON
records, 1,184 matching checkpoints, 592 pair-completion markers, and no
temporary outputs. Each arm has 591 successful classifications and the expected
fail-closed ORE1194 result. Comparisons cover status, verdict, consistency,
selected route, solved state, answer counts, missing and extra counts, and
collision-sensitive full-IRI signatures. Every comparison count is zero.

| arm | wall mean s | wall median s | peak mean MiB | peak median MiB | wall sum s | RSS sum MiB |
|---|---:|---:|---:|---:|---:|---:|
| v0.2.33 baseline | 3.429525 | 0.1655 | 420.3890 | 34.79 | 2,026.8493 | 248,449.87 |
| candidate | 3.434231 | 0.1623 | 416.0649 | 34.75 | 2,029.6303 | 245,894.38 |

ORE14817 itself falls from 93.0595 seconds and 5,112.05 MiB to 92.2462
seconds and 2,791.18 MiB. The aggregate 2.781-second wall movement is dominated
by unrelated route noise and is not claimed as a wall regression or
improvement. Summed peak RSS falls by 2,555.49 MiB, including the deterministic
2,320.87-MiB reduction on ORE14817.

## Release tests

The complete release-mode suite passes 2,005 library tests with eight ignored
tests and every integration test, including `issue_3_soundness`, which confirms
that nominal enumeration plus explicit difference reports the pigeonhole
ontology inconsistent.
