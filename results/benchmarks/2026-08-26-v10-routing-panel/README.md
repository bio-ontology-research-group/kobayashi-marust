# v10 source-bound routing panel

This candidate combines two feature-selected scheduling changes over the
frozen v5 automatic-route candidate:

- 20 compact nominal ontologies schedule the certified general HT worker;
- ORE7499 schedules that worker through a separate large-cardinality gate.

Both workers remain complete-answer-or-defer routes. A declined conversion or
publication restores the prior exact fallback. The panel compares byte-exact
classification JSON against v5 for every selected ontology and six exclusion
controls. It also verifies the expected automatic route from `KM_TIMING`.

The frozen source archive is `v10-source-20260826.tar.gz`, SHA-256
`d24f3e62267501bca4a1cb1a308ca9f705e5869b971d15b5fea4827d1c6980f5`.
Before freezing it, the release-mode routing suite passed all 45 tests. Slurm
build job `50864403` verifies that source hash before compiling. The binary
SHA-256 is
`a800d74983811ccaee8ea135f0d7989d1b9fdac27397a9163651094478698372`.
The build completed in 4 minutes 16 seconds. A selected compact ontology and
ORE7499 must pass a sanity pair before the complete array.

Sanity job `50864546` passed ORE148 and ORE7499 with byte-identical v5/v10
answers and the expected `ht_general` trace. Full panel job `50864621` passed
the first 26 tasks. Its original `0-25` bound omitted the seventh item after
the 20 compact cases, so the harness was corrected to `0-26`; job `50864773`
then passed the missing ORE9540 unchanged-route control. The final artifact set
contains 27 v5 measures, 27 v10 measures, and 27 v10 traces. All 27 answers are
byte-identical, exactly 21 traces select `ht_general`, and all six controls
retain their prior route.

Across the 27 paired rows, v5 used 104.98 wall-seconds and 23,536.4 MiB of
summed process-tree peak RSS. v10 used 14.48 seconds and 4,898.2 MiB,
respectively. This source-bound panel therefore saves 90.50 seconds and
18,638.2 MiB while preserving every answer. These are focused measurements;
the strict full-corpus sweep remains the release authority.
