# Dense candidate slow-case profiles

Job 53320659 completed all eight instrumented cases under the original 240-second,
20-GiB, one-CPU limits. These traces diagnose work; their outputs have not yet
received independent semantic audits and do not change release solved counts.
Hashes and selected phase lines are in `dense-slow-profile-summary-53320659.json`.

- 14572, 7361 and 9724 repeat whole-ontology saturation for disjoint subject
  shards. For 14572, the two saturation loops take 52.29 and 51.72 seconds,
  each answering its 11,568 subjects without completion probes. The production
  route selects two subject workers, even when the process has one CPU.
- 3726 and 7278 spend 105.65 and 97.40 seconds in the rules-consistency worker.
  The later EL taxonomy classification is negligible. Retain the consistency
  check; optimizing only taxonomy classification cannot resolve these costs.
- 13276 spends 79.14 seconds preparing 24,115 subjects, including 55.77 seconds
  in completion and 19.39 seconds in analysis; verification adds 43.31 seconds.
- 1886 declines the positive-EL ABox certificate and cannot enter the typed HT
  route. Its engine block completes at 136.64 seconds. 4410 selects the nominal
  route and completes its engine block at 160.04 seconds. These traces do not
  yet isolate their internal hot loops.

Job 53321214 compares the existing one-worker override against two workers on
14572, 7361 and 9724. Each case has two repetitions with reversed arm order,
unchanged immutable binary, and unchanged limits. This is a scheduling diagnostic;
exact output audits and a full frozen sweep remain necessary before promotion.

The first six completed outputs (both repetitions of 14572 and the first of
7361, both worker settings) independently agree with the stored full-DL
references. One worker takes 63.07–64.05 seconds versus 118.15–119.37 seconds
for two workers. `single-worker-partial-audit.json` records each comparison and
its hashes. The remaining six measurements were still running when this partial
audit was recorded; no full-corpus result is replaced by these diagnostics.

The final audit verifies all 12 outputs from job 53321214. Across all six pairs,
one worker takes 63.01–64.05 seconds, versus 117.46–119.37 seconds for two.
`single-worker-final-audit.json` supersedes the partial audit. Full frozen-corpus
job 53322070 now tests the override with the same dense-data binary and the
unchanged admission, limits and independent auditing. Production defaults remain
unchanged pending this wider evidence.

The full single-worker sweep 53322070 is complete. Its final summary supersedes
all partial snapshots: 1,620 independently corroborated completions, mean
7.609516 seconds and median 0.389301 seconds. All 1,920 inputs are present;
212 invalid refusals remain, with 27 admitted process errors and 59 timeouts.
Two additional completed answers lack corroboration and do not count as solved.
No audit errors occurred.

Compared with the dense candidate, it gains 9791, 13229, 5162, and 14817 and
loses 12898. The lost case previously took 235.855 seconds and now reaches the
240-second timeout; a repeated comparison is needed to distinguish scheduling
effects from deadline variability. On the 1,616 shared verified cases, mean
runtime decreases from 7.491564 to 7.171215 seconds. These are separate sweeps,
not repeated paired measurements. Production scheduling remains unchanged.

The candidate still fails the v1.5.0 target: Konclude verifies 1,655 cases with
lower mean and median times. KM needs 36 net additional verified cases to exceed
that count. RustDL also retains lower whole-success-subset mean and median
times. The candidate beats ELK on all three required metrics.

Job 53328863 traces the existing SWRL consistency worker for 3726 and 7278.
A wrapper records the exact worker input and otherwise-suppressed stderr, then
executes the pinned certified-source binary. It preserves all consistency and
source-model checks and independently audits completed classifications. Added
diagnostic I/O means these timings cannot establish a performance improvement.
