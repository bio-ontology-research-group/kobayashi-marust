# v1.5 performance work

The release objectives are not yet achieved.

## Release acceptance

- v1.5.0: lower arithmetic mean runtime, lower median runtime, and strictly
  more verified solved ontologies than each of Konclude, RustDL, and ELK.
- Preserve the full frozen corpus, input admission, independent verification,
  and common 240-second, 20-GiB, one-CPU protocol. Report all failures. Do not
  claim success using only this diagnostic subset or a changed denominator.
- Report successful-subset times alongside coverage and matched-case times.
  Confirm improvements with repeated measurements under identical conditions.
- Maintain Lean certification. Before each release, run every production gate
  from the exact release source and reject sorryAx. Preserve soundness and
  completeness; never restore an unsound shortcut to improve coverage.
- v1.5.1: substantially increase actual reuse during incremental reasoning.
  Measure reuse directly and compare retained versus fresh reasoning for each
  update case, with identical answers and repeated timings. Every case must
  improve, rather than hiding regressions behind an aggregate speedup. Keep
  preparation failures, session failures, and initialization costs visible.

## Initial diagnostic

`paired-selection.json` derives 30 lost completions, two gained completions,
and ten runtime-decile controls from the stored v1.4.4 and v1.4.5 results.
These are operational completion counts, not independently verified answers.

`run_pairs.py` uses the existing classification measurement and watchdog code
unchanged for both pinned release binaries. Each ontology runs three times
per version on the same Slurm worker and CPU affinity; version order alternates.
Raw answers are retained for subsequent semantic audit. This subset diagnoses
regressions; it cannot establish either release's final acceptance.

Initial hypotheses to test, not established causes:

1. Differences in the old and new harness account for part of the latency.
2. Classification now materializes cached disjunctions and defers saturation
   answers with unresolved equivalent classes. These correctness safeguards
   may expose expensive completion work that previously returned early.
3. Correct nominal merge dependencies can change search and backjump behavior.

Do not remove correctness safeguards. Use matched results and phase profiles
to identify the next implementation change.

## First matched observations

The first repetition of job 53294013 reproduces three large operational
regressions: v1.4.4 completes 1997 in 0.844 s, 5303 in 0.861 s, and 2901 in
8.616 s; v1.4.5 reaches the 240-second limit on all three. The small control
10174 takes approximately 0.040 s in either version. Independent answer audits
and the remaining repetitions are pending; these observations do not prove
that the earlier answers are correct. `pilot-initial-observations.json` stores
the partial receipts.

Phase profile job 53294179 uses a separate 60-second diagnostic limit and
enables timing/progress logs; its times must not enter performance summaries.
The remaining 38 pairs are queued as job 53294280, dependent on successful
completion of the pilot audit. Audit jobs 53294117 and 53294283 run after
their corresponding measurement tasks. See `CURRENT-STATE.json` before
resuming, to avoid duplicate submissions.
