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
