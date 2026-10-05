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

Backjumping remains disabled by default. The standard release build completed
and was deployed with SHA-256
`4f4f2d9cec9eb83bcb49c2baf51d79b2157354c9808f3b464c5b66a52292f0ab`.
The HT certification gate is in progress; see `CURRENT-STATE.json` for handles.
`run_atmost_candidate.py` and `atmost-candidate.sbatch` prepare an independently
audited run of the existing 42-case diagnostic selection, submitted as job
53296355 with three repetitions. This selection cannot establish the full release
objectives, which remain unchanged and unmet.

## Wider matched audit, partial

The next eight completed case audits change the interpretation of the lost
completion count. On ORE 11477, 1397, 14334, 16481, 2182, 3010, 6272 and 8786,
all three v1.4.4 runs return a consistency verdict that disagrees with every
available independent reference. v1.4.5 times out on those cases. They are
lost output completions, not verified successes lost to a regression. The
three verified pilot regressions remain confirmed. These partial receipts
are in `paired-53294280/` and `paired-partial-audit-summary.json`; the remaining
matched runs and audits are still in progress.

## Incremental invalidation diagnosis

A targeted source-session replay of ORE 9944 confirms that its bridge adapter
is retained, but removing one normalized clause reclassifies every query.
The typed side fingerprint is unchanged (`side_changed=false`); the undirected
dependency closure contains 15,225 concepts for 8,008 public queries. No query
state survives. `incremental-9944-diagnosis.json` records source hashes,
receipts and the trace. Its local timing is diagnostic only. This motivates
finer dependency-supported invalidation, not removal of the typed-state
guards. Prior-state restoration can help the restoration revisions, but
would not satisfy the requirement to improve deletion revisions as well.

## Conjunctive reuse prototype and current partial measurements

The opt-in `KM_INCREMENTAL_CONJUNCTIVE=1` path preserves conjunctions during
query-dependency analysis in a guarded positive Horn fragment. On ORE 9944,
the single-axiom removal/restoration retains 8,004 of 8,008 query rows. All five
revision answers match the retained full-rebuild baseline. Larger edits still
rebuild because normalized definer names and typed fingerprints change.
`conjunctive-diagnostic/` retains the failed initial merge result as well as
the corrected comparison. The bridge merge now replaces only requested
subjects; incidental partial rows must not overwrite complete retained rows.
See `docs/INCREMENTAL-CONJUNCTIVE-REUSE.md` for scope and remaining proof work.
The local timing sequence is not a comparison against fresh processes and
cannot establish the v1.5.1 target.

The snapshots `native-partial-summary-53298536.json` and
`conformance-partial-summary-53300563.json` record 1,170 and 501 inputs,
respectively. Both full 1,920-input Slurm jobs remain active. The first
candidate has eight newly corroborated successes and one historical verified
success not reproduced (1123; the separate ablation does not attribute this
to the candidate flags). The validation-cache candidate's 422 shared verified
KM cases improve from mean 10.985/median 0.671 seconds to 7.084/0.367 seconds.
It still trails Konclude on their shared subset. Input order is not random,
so these snapshots must not be extrapolated to the full corpus. Neither
release objective is established.

The incremental test group passes all 49 tests with the opt-in enabled and
with it absent, including exhaustive small Horn theories and the partial
role-chain taxonomy merge regression. The source-hashed test receipt is in
`conjunctive-diagnostic/test-receipt.json`. Certification of the new reuse
boundary is still pending; the optimization remains disabled by default.

The completed routing diagnostic has 96 verified pairs over 32 selected
inputs. Disabling the preliminary in-process engine has median paired runtime
ratio 0.9988; mean times are 6.526 versus 6.477 seconds. This does not justify
a global routing default change. `routing-probe-completion.json` records all
paired times and chunk hashes.

## Stable-source dependency diagnostic

`probe_source_activation.py` compares typed source-axiom metadata rather than
normalized definer identities. ORE 9944's large edit removes 32 source axioms;
its changed normalized representation need not imply all 8,008 queries change.
The conservative source-expression diagnostic marks 2,180 queries and leaves
5,828 potentially reusable. All 52 actually changed public rows are within
that set. Fresh invocations agree with the stored full-rebuild outputs for
both tested edits. The observed typed domain/range differences disappear when
numeric IDs are resolved to concept names. Evidence is in
`source-activation-{small,large,answer-check,side-check}.json`.
This is not a production fingerprint relaxation or a speedup result. The
source-metadata completeness boundary, handling of every typed field, Lean
proof, and full update-panel comparisons remain necessary.
