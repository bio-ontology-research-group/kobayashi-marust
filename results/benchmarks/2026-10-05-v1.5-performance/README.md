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

## Completion-search diagnosis

Visible worker traces (job 53294360) show that frontend processing is still
about 0.02–0.05 seconds. On 1997, read-off for subject 150 grows from 0.031
seconds to 28.206 seconds; the next subject consumes its 30-second budget.
The v1.4.4 answers for all three diagnostic ontologies agree with both
Konclude and HermiT using the pinned source signatures and canonicalization.

The existing `KM_HT_DDB=1` option (job 53294493) finishes 1997 and 5303 in
1.13 and 1.27 seconds with independent agreement. Its 0.66-second answer on
2901 is wrong: it marks 17 satisfiable classes unsatisfiable. These are
instrumented diagnostic times, not release benchmark figures. Removing atomic
semantic branching (`KM_HT_NO_SEMB=1`, job 53294622) preserves that failure.
Do not promote DDB to a production default on this evidence. Job 53294731
separates mark-driven stack skipping from saturation-cache reading/absorption.

`phase-profiles/` retains raw outputs, timing receipts, worker traces, pinned
reference audits, and independent comparisons. The explicit edge difference
for 2901 excludes the vacuous edges implied by its erroneous UNSAT verdicts;
the UNSAT arrays in that artifact are essential to interpreting the error.

For incremental work, `incremental-route-diagnosis.json` groups existing
v1.4.5 reuse receipts by route. All 348 recorded post-initialization attempts
through nominals, certified_nominals, and ht_bridge rebuild. This is a concrete
adapter/reuse coverage gap to address for v1.5.1, in addition to frontend and
update overhead. The file does not replace the full failure denominator.

## At-most dependency repair

The completed pilot audit confirms all three regressions across three
repetitions. Every v1.4.4 completion is independently verified; all nine
corresponding v1.4.5 runs time out. The control remains verified for both.

Reduction job 53294946 isolated four variable axioms, with HermiT checking
each accepted reduction. A separate small fixture describes four successors
in a disjoint union, three in C and one in D. The pre-fix Rust test accepts
this satisfiable partition with chronological search but incorrectly rejects
it with dependency-directed backjumping.

Both at-most merge-enumeration paths used a boolean mergeability predicate
that discarded dependencies of rejected pairs. The repair uses the existing
descriptor-carrying predicate and retains these premises on the bound clash
or merge decision. This prevents a branch-specific conflict from being
mistaken for an unconditional contradiction. Unsupported predicate state
continues to stop the task.

The regression now passes for both cardinality implementations with
backjumping on and off. The affected engine test group passes 1,466 tests,
with seven ignored. The repaired diagnostic CLI also finishes the original
ORE 2901 case and agrees with both pinned Konclude and HermiT references:
the 17 false UNSAT classifications disappear. See
`atmost-dependency-diagnostic/ore_ont_2901-local/independent-audit.json`.
The local 25.8-second diagnostic used a build without LTO and is not a
release benchmark measurement. An earlier local harness attempt failed
because this container lacks `/usr/bin/time`; its adapter-error record is
retained separately.

Backjumping remains disabled by default. A standard release build and the
HT certification gate are in progress; see `CURRENT-STATE.json` for handles.
`run_atmost_candidate.py` and `atmost-candidate.sbatch` prepare an independently
audited run of the existing 42-case diagnostic selection once the normal
release binary is ready. This selection cannot establish the full release
objectives, which remain unchanged and unmet.
