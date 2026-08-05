# Compact central trigger sets

Commit `a0a9a9b` replaces each CB central-context successor trigger
`BTreeSet<Pred>` with a compact sorted `Vec<Pred>`. Binary-search insertion
preserves uniqueness and deterministic order, and every consumer observes the
same ordered predicate sequence. This changes storage only; rule derivation,
context identity, scheduling, and the saturation fixpoint are unchanged.

## Workstation gates

The complete serial release suite passed: 1,953 library tests passed, eight
were ignored, and every binary, integration, and documentation test passed.

Two alternating single-thread ORE4669 pairs produced byte-identical
16,886,076-byte output with SHA-256
`055cb5f2481c778e5ed137dddccd2201e04d45c05a472b42eb54119cdc331ac2`.
Wall was neutral while peak RSS fell reproducibly:

| order | baseline wall / RSS | candidate wall / RSS |
|---|---:|---:|
| baseline then candidate | 21.38 s / 1,841,272 KiB | 21.25 s / 1,775,344 KiB |
| candidate then baseline | 21.64 s / 1,839,916 KiB | 21.34 s / 1,773,740 KiB |

On a 60-second ORE1194 CB diagnostic, both binaries reached exactly the same
query, context, pending-message, saturation-call, and detailed 200,000-iteration
checkpoint. Peak RSS fell from 5,480,896 to 4,710,720 KiB, a 14.1% reduction,
without measurable progress loss.

## IBEX sentinel panel

- Source commit: `a0a9a9b`
- Source archive SHA-256:
  `609880607adf66ff0ad37217ff87358b8866ab386f7bfd8ebc1c0fb6ecc60d50`
- Build job: `50052217`, completed in 4:46
- Binary SHA-256:
  `7d32fa946eb5100dbeb60115ccb2037df79f4ecfa296aeb89657b41c762ba6ba`
- Ten-task panel: `50052224`

The strict audit verified ten unique result rows and profiles, the expected ten
array indices, ten completion logs, one binary identity, valid checkpoints and
terminal statuses, and no temporary files. Nine solved sentinels remained exact
against Konclude. ORE1194 retained its expected fail-closed error. ORE4669 also
matched the collision-safe full-IRI fingerprint
`a482e066a22110df593bf3a4c1fdd0ef4404f7141903b2101b85aae49811cb30`.

Against the latest v0.2.2 source-bound sweep, total wall over the nine successful
sentinels fell from 625.0680 to 614.7679 seconds (1.65%), and mean peak RSS fell
from 8,717.32 to 8,642.82 MiB (0.85%). ORE14817 had the largest memory reduction,
5,956.62 to 5,312.94 MiB (10.81%). ORE7246 was the adverse cross-job outlier at
10,493.37 to 10,834.48 MiB (3.25%); the full sweep below provides the
corpus-wide memory and correctness promotion gate.

[`panel-results.tsv`](panel-results.tsv) contains every paired measurement and
signature comparison. The Slurm scripts in this directory reproduce the build
and panel with source, binary, ontology, CPU, checkpoint, and resume checks.

## Full 592-ontology production sweep

The merged source at `ed81ac6` was archived with SHA-256
`6b853637570ef157519fe8c441f969b969ec5faa4a2c8389f277a4ec74d9d0f5`.
Build job `50052290` completed in 4:47 and reproduced binary SHA-256
`7d32fa946eb5100dbeb60115ccb2037df79f4ecfa296aeb89657b41c762ba6ba`.
Resumable array `50052291` then completed all 592 tasks.

The strict terminal audit verified 592 unique ontology rows, every array index
from 0 through 591, 592 valid profiles, 592 terminal logs, 592 checkpoint
receipts matching their result rows, one binary identity, four expected
collision-sensitive full-IRI fingerprints, and zero temporary files. Coverage
remained 591/592, with ORE1194 the only error. The verdict distribution remained
588 matches, the two established adjudicated consistency mismatches, and one
adjudicated no-gold result. Relative to the v0.2.2 sweep, there were zero status,
verdict, signature, or production-route differences.

Across the 591 paired successes:

| metric | v0.2.2 | compact trigger sets | change |
|---|---:|---:|---:|
| Mean wall | 5.7993 s | 5.7810 s | -0.32% |
| Median wall | 0.2536 s | 0.2530 s | -0.24% |
| Mean peak RSS | 818.65 MiB | 817.18 MiB | -0.18% |
| Median peak RSS | 43.33 MiB | 43.14 MiB | -0.44% |

The 7246 cross-job RSS increase persisted, but the complete corpus aggregate
improved and no ontology lost coverage or correctness. The exact full result
table is [`automatic-results.tsv`](automatic-results.tsv), SHA-256
`08e73a73c539550784a0eb4b9e845f64c40ac3fda717f7985977085ce36d89fb`.
[`ibex_full_build.sbatch`](ibex_full_build.sbatch) and
[`ibex_full_sweep.sbatch`](ibex_full_sweep.sbatch) reproduce the source-bound
build and sweep.
