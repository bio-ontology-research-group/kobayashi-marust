# Allocation-light frontend validation

This candidate changes frontend allocation and source-screen scheduling only.
It does not change OWL normalization, generated clauses, calculus rules, or
accepted results.

## Pinned artifacts

- Candidate source archive SHA-256:
  `5fe10eae2f2164120326ff775843ca3dcb82c8d871521317a0e7b45127c3b0c8`
- Candidate binary SHA-256:
  `bcea1fadc32705e7335fece71f120528c13317f93b3f3dd0b8f6c7f1c10b0620`
- Baseline binary SHA-256:
  `d41ea3768f9eaf579283ed870ae6fc45ae6c0aa6692925acdb35509ee887c3ec`
- Validation evidence archive SHA-256:
  `d05e2803331f7ab191cfb1351cbc9cb5f232fd4d36bb0fac773eb4586aaf1c0e`
- Build job: 51337670
- Accepted identity array: 51338298
- Performance panel: 51338299

The local copy of the validation archive is
`.work/artifacts/frontend-alloc-candidate/frontend-validation-evidence.tgz`.

## Semantic gate

The identity array ran both binaries as `km ofn --meta` over every ORE input.
It required the SHA-256 digest of the clause stream and metadata file to match
independently. The run produced 592 result files and 592 `TASK_COMPLETE`
markers, with 592 clause matches, 592 metadata matches, and no mismatch. ORE
8737, 15059, and 16744 were present and matched explicitly.

An earlier array, 51337671, failed before running the frontend because the batch
environment did not define `SLURM_TMPDIR`. It produced no result files and is
not evidence. The corrected script falls back to a unique directory under the
persistent scratch root and removes it on exit.

## Repeated performance panel

All 40 runs were `ok`, matched retained gold, emitted checkpoints and completion
markers, and selected `elc`.

| ORE ontology | median wall (s) | target wall (s) | median peak (MiB) | target peak (MiB) | joint win |
|---:|---:|---:|---:|---:|:---:|
| 6722 | 3.1596 | 1.8636 | 310.78 | 428.45 | no |
| 7340 | 2.4082 | 2.5354 | 275.68 | 759.47 | yes |
| 7868 | 3.0935 | 2.4669 | 296.89 | 934.22 | no |
| 12087 | 3.5237 | 2.8360 | 358.69 | 849.45 | no |
| 12387 | 2.8338 | 3.2375 | 368.60 | 729.74 | yes |
| 13224 | 3.2944 | 2.0760 | 396.49 | 397.32 | no |
| 15976 | 3.7055 | 2.8331 | 344.25 | 693.33 | no |
| 16596 | 4.0377 | 2.8055 | 360.36 | 877.77 | no |

The accepted repeated-evidence composite is therefore 529/589 strict joint
wins. Sixty comparable ontologies remain above at least one external target.

## Integrated acceptance

The active worktree was archived after combining this frontend work with the
accepted ORE 11316 routing and ORE 14312 certificate changes:

- integrated source archive SHA-256:
  `e20f10f71df0479d36934a5fb823ad60d69e9469fe05ef717e0be6766b386f1c`;
- integrated binary SHA-256:
  `0e419dc5ff30267486707f1cf1915341d5070e151739cb41f6ea3907a0795603`;
- integrated validation archive SHA-256:
  `14b86956ecbf1ab05c0978a8997f96687dc00d0a8acfbaf80f32d45bd42c5efa`;
- build 51340006, repeated retention panel 51340007, full sweep 51340008,
  and same-node ORE 14312 A/B panel 51340156.

The retention panel produced 20/20 exact completions. Its medians were 0.1769
seconds / 36.34 MiB for ORE 11316, 1.5583 seconds / 195.80 MiB for ORE 14312,
2.1908 seconds / 276.11 MiB for ORE 7340, and 3.1987 seconds / 368.34 MiB for
ORE 12387. Because concurrent-node variance put 14312 above its absolute target
in that panel, the paired same-node panel compared the preceding and integrated
binaries sequentially in alternating order. All ten runs matched gold. The
integrated median was 1.4087 seconds / 196.19 MiB versus 1.4633 seconds /
200.53 MiB for the preceding binary, retaining the established strict target.

The integrated automatic sweep produced exactly 592 results, 592 checkpoints,
and 592 completion markers from the pinned binary. All statuses were `ok`: 588
matched retained signatures directly, two retained their independently
adjudicated consistency verdicts, and two had no retained external gold. Every
status and signature hash was identical to the preceding accepted sweep. The
three giant inputs selected `flat_nf1`: ORE 8737 completed in 10.2619 seconds
at 59.61 MiB, ORE 15059 in 3.9179 seconds at 69.80 MiB, and ORE 16744 in
12.0602 seconds at 67.39 MiB.

## Final routing replay

The final source state also pins `KM_NO_HT_RULES=1` in `cb_portfolio16`. This
removes an irrelevant rule precheck from a route whose source-profile fence
already requires zero rule axioms. It changes neither the selected complete CB
workers nor their fixpoint.

- source archive SHA-256:
  `e24a2fafab2569d8fd828a0a30c4cf20a7b23f9a290298da7bd64dcfc1f6af97`;
- binary SHA-256:
  `151bf5dece8b61829dcff7a63f7d0ed9b07c8a9aa030b161a04dc55c9385db4c`;
- validation archive SHA-256:
  `c5fbb15f9e16769eeeb70bc0f49c813fd954d74ae810c74fda623e9ddbbddacd`;
- build 51341044, repeated panel 51341067, and full sweep 51341068.

The panel produced 20/20 exact gold matches with complete checkpoints and
markers. ORE 11316 selected `cb_portfolio16` in all five runs, with medians of
0.1696 seconds and 36.31 MiB. The final sweep produced exactly 592 results,
592 checkpoints, and 592 completion markers from the pinned binary. All 592
statuses were `ok`; 588 matched retained Konclude signatures, two retained
their adjudicated consistency verdicts, and two had no external gold. No status
or signature hash differed from integrated sweep 51340008.
