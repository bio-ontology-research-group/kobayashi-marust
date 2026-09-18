# Justification protocol development

The ISWC 2012 supplementary site was retrieved on 2026-09-17, including
`data/experiments-software.zip` (SHA-256
`e91d056bafcb3d24958f66e1d33fb1d5d72b662694908f4ea2b9bddbe2544a33`).
Its `experiment.properties` sets `entailmentlimit=1000`,
`justificationstimeoutms=600000`, and `shuffle=true`. This supports our
600-second explanation timeout. We use a new frozen OBO panel and stable hash
sampling, so this is a methodology adaptation, not replication of its corpus.
Source: https://web.stanford.edu/~horridge/publications/2012/iswc/justextract/

Panel matches the independent profile/size selection in incremental-panel.tsv:
mmo, hao, vto, mfomd, to, uberon. HermiT and JFact independently classify the
unchanged source; only exactly agreeing full taxonomies admit queries. We take
the first five SHA-256 sorted non-asserted named subsumptions per ontology.
Failures and disagreements remain explicit panel preparation outcomes.
OWLAPI STAR modules are extracted once per query, outside all reasoner arms,
with extraction and serialization cost reported. Full source and module
tracks must not be pooled.

Pilot 51981062 uses three analytic controls and limits 1 and 10. Its timing
includes an extra same-oracle minimality check; this is retained as pilot-only
evidence. Whelk failed on an OWLAPI4/5 createOntology ABI mismatch. The corrected
harness uses createOntology() and applyChange(AddAxiom), with unchanged logic;
rerun 51981088 preserves the initial evidence in a separate directory.
Panel preparation array: 51981087. No KM implementation was changed.

The common extractor uses deterministic deletion minimization and a complete
hitting-set search up to the explicit output limit. Its completeness flag is
true only when the queue exhausts. It does not assume that reaching a requested
limit means all justifications have been found. The measured extraction does
not include independent validation. Each oracle is freshly created, including
KM's one-shot source session. This arm compares shared extraction, separately
from KM's native algorithm and its differing batching/validation costs.

The v2 pilot progressed past ABI construction but found Whelk's documented
`isEntailed` method unsupported. Its named-class subsumption oracle now uses
full superclass/equivalence/unsatisfiability queries when `isEntailed` raises
UnsupportedOperationException. This is an exact query reduction for named
subsumptions, including bottom and inconsistent ontology cases, not unsupported
axiom approximation. EL eligibility remains mandatory for Whelk inputs.

Final analytic pilot 51981178: 48/48 correct by exact known support-family
comparison and independent source-subset, entailment and single-deletion
minimality validation. Arms: native KM; common KM, HermiT, JFact, Openllet,
ELK, Whelk, Konclude. Three controls, two limits. This pilot has no repeated
measurements and is not the release benchmark. Auditing script:
`audit_justification_pilot.py`. Results remain immutable in the remote
`justification-pilot-v4` directory.

Real pilot 51981162 found the MFOMD first module (66 logical axioms) fails in
native KM after 190.11 seconds with `classification oracle: worker engine
exited -1`; peak `time` RSS was 57,228 KiB. The default central strategy cap is
190 seconds, but this attribution requires the separate replay diagnostic.
Job 51981222 captures observed temporary source candidates without modifying
KM, then repeats ordinary classification on the last captured source. Polling
is not a complete oracle trace and cannot establish an exact oracle-call index.
The first captured ontology includes a nine-element nominal enumeration.

Real pilot v2, job 51981216, adds pinned OWLAPI library extraction with HermiT,
JFact and Openllet. Those libraries expose no reliable search-frontier status;
we report enumeration completion as unknown. KM's per-central-worker cap is
set to 240 seconds to match the protocol, explanation limit remains 600 seconds.
Each arm has a separate independent validation process. Main runner additionally
samples summed descendant RSS at 50ms intervals, recording its sampling limit.
Main suite scripts are prepared but not yet submitted.

Before release timing, query selection was revised to avoid unnecessary
full-taxonomy materialization: hash all named class IRIs, select the first 128,
retrieve their nontrivial named superclasses, and take the five smallest
SHA-256 hashes of the resulting nonasserted subclass pairs. HermiT classifies
and proposes candidates; JFact independently confirms consistency and each
selected entailment. The original full-taxonomy preparation continues to its
own terminal state and is retained. The revised protocol never selects on KM
success. Main tasks consume `justification-panel-v2` only.

Access-restored continuation: panel sampling array 51982295 runs under immutable
`justification-driver-v3`; build/task freeze 51982310 depends on its terminal
state. The old real-v2 pilot is terminal: 36 independently verified correct
extractions, 4 KM errors (native and common, MFOMD, bounds 1 and 10). Its ordinary
classification replay also fails with `worker engine exited -1`. Keep this as a
baseline outcome; no calculus or routing change is justified for a minor release.
The durable pilot audit is in the dynamic-baseline results directory.

The main driver now binds Java sources/classes, Python adapters, runtime JARs
and both native binaries with SHA-256, freezes that manifest into every task,
and rejects mutations before execution. It samples total process-tree RSS at
50ms, terminates an arm above 20GiB, and requests 22GiB Slurm allocation to leave
supervisor headroom. A 12-hour task ceiling covers the worst case of all 33
600-second extractions plus independent 600-second validations. Runtime success,
timeout and memory termination behavior was checked locally with small worker
processes. Independent verification remains outside extraction timing.

Each extraction starts a new process. Repetition zero warms filesystem/runtime
caches but is not a retained JVM warmup. Five subsequent repetitions are measured;
arm order rotates deterministically with repetition. Module and full-source
tracks remain separate. The main auditor enumerates every frozen task/arm,
requires a positive source entailment, checks support counts, source membership,
entailment and one-deletion minimality, and distinguishes execution failures from
validation failures. Conditional successful medians must not be compared as if
all arms solved the same query set; use the paired per-query records.

Additional analytic controls (51982346) cover named-class unsatisfiability and
ontology inconsistency at bounds 1, 10 and 100. Both have one known minimal
three-axiom support. Inconsistency uses two class assertions about one individual
and a disjointness axiom, querying owl:Thing subsumption by owl:Nothing. Baseline
KM native/common incorrectly return not-entailed; the pending parent ABox fixes
must rerun all these controls after experimental validation. The three library
arms raise InconsistentOntologyException on that control; this is an explicit
capability failure, not zero-cost successful extraction. Common peers succeed.

Post-run JustificationSupportAudit normalizes each returned support through
OWLAPI logical axiom sets without annotations and hashes sorted axiom renderings.
Report both native source-occurrence counts and normalized distinct support
counts; duplicate occurrences or annotation variants are not additional logical
justifications. This pass stays outside extraction timing and must be run before
the final comparison is accepted.

Main execution started as array 51982389 (0-239, concurrency12), after build
51982310 succeeded. All 20 queries for mmo/hao/vto/mfomd have independent
confirmation and frozen shared modules. This schedules 7,560 extraction arms:
6,300 measured and 1,260 warmups. The first 12 tasks were verified running with
successful extraction and independent verification receipts. Audit 51982402
waits for terminal array state and normalizes logical supports before reporting.
TO and UBERON HermiT preparation hit the 600-second cap and remain explicit
preparation-unavailable rows, not silently discarded successful examples.

A subsequent syntactic eligibility audit found SWRL rules in TO (25) and UBERON
(3), despite the original inventory's OWL 2 DL flags. The parent applies the
same original nearest-log-size selection with an explicit no-rules condition,
obtaining zfa (12,330 logical axioms) and mro (84,613). These form a separate
pure-DL supplement; original DL+rules preparation outcomes remain retained.
Supplement panel 51982414 and build 51982418 use immutable remote
`justification-pure-dl-v1`, unchanged independent query sampling, and a frozen
panel JSON. No KM timing or success determines this eligibility correction.

Logical controls 51982346 are terminal: 45 correct, 9 inconsistent-ontology
library errors, 6 baseline KM incorrect zero-support outputs. The exact candidate
rerun list is native/common KM on both controls at bounds 1/10/100, requiring
independent verification and the unique known three-axiom support, plus the
original two-path/noise/negative controls for regression. No candidate results
have yet been recorded by this benchmark branch.

Pending handoff after first main launch:
- Original main 51982389 is verified live with 12 concurrent tasks; audit51982402
  waits on its terminal state. Do not overwrite driver-v3 sources/manifests.
- Pure-DL panel51982414: zfa completed, mro HermiT still live at3min; build51982418
  remains pending. After build terminates successfully, inspect task-count.txt
  and panel-status.json and submit exactly the resulting task range, then an
  afterany audit, in justification-pure-dl-v1. Never infer termination from an
  observation failure or submit based only on an expected count.
- Candidate-controls script and auditor are prepared locally, not submitted.
  Require CANDIDATE_BIN and CANDIDATE_SHA. Deploy into a new immutable driver
  directory with all Java/Python dependencies, then submit array0-4. The native
  and common KM arms cover unsat, global inconsistency, two-path, noise, negative
  at all three limits, 30 attempts. Root parent supplies experimental candidate
  path/hash; large final KM-only main runs wait for certification and final version.
- All local modifications outside engine are benchmark artifacts, not KM logic.

Experimental candidate controls are now complete: array51982551 and independent
audit51982553 report30/30correct. Local recomputation agrees. Archive9a77671d...
and binaryb5153317... are bound in per-task receipts. Both KM native/common now
recover the unique three-axiom inconsistency support at all limits, correcting
six v1.4.0 outcomes; the other24 controls pass. Durable evidence is in
results/benchmarks/2026-09-17-dynamic-baseline/candidate-justification. This is
pre-certification experimental evidence only; final timed candidate runs remain
pending certification and final binary/version.

Pure-DL supplement execution: build51982418 passed and froze60 ZFA tasks
(five queries, two tracks, six repetitions). Full-source task hashes match
f932a5a15e7571035365768f9164ff49447400354be4d050554483ddcc357dfb from the syntactic
eligibility audit. MRO HermiT preparation reached600s and remains unavailable,
with its source retained in the panel denominator. Actual main51982752 runs
array0-59 at concurrency6; post-run audit51982764 waits for terminal array state.
Together with the original main this schedules9,180 attempts,7,650 measured and
1,530warmups. These are scheduled counts, not successful extraction claims.
Task manifests, binary/runtime/harness manifest, and panel statuses are copied to
results/benchmarks/2026-09-17-dynamic-baseline/justification-main-provenance.

Final v1.4.2 candidate staging (after parent Lean and release-test gates): build
51983793, archive37bb4b1b184033ec249d3044a6a72c3460bbf3e78d443d94d5accfbd8b9631e1,
binary705cac1500018d18018ca4d5482a7451e836091b26648453824afa4b36d16fdb.
All334 archive members retain identical metadata; only KM package versions in
Cargo.toml/lock differ from the1.4.1 archive. All254 Rust members match current
certified source, and689 native-gate source hashes are bound by equivalence.
Task worktree package version remains1.4.1; staging used a private archive.

Public gate51983988 failed before testing because the harness assumed a
`km --version` option. The old log remains retained. Replacement51984225 uses
actual explanation report.reasonerVersion and passes18 public cases with the
same known unsupported manual duplicate-assertion case. Explanation array
51983989 and audit51984004 pass30/30 exact analytic controls. Stage51984100
was dependency-updated to the replacement public gate and succeeded only after
both control gates passed, binding source/proof/runtime receipts.

Final KM-only main arrays51984134(original240tasks, concurrency8) and
51984137(ZFA60tasks, concurrency4) are verified running. They preserve every
frozen query/source/module/track/limit/repetition, exact baseline Java classes,
common extractor and runner. Only KM binary and explicit two-arm selection change.
As that unchanged runner specifies, the two KM arms rotate across repetitions;
this differs from their placement in the original full-comparator rotation.
Peer measurements are retained. Follow-up audits51984145/51984159 wait for the
respective main arrays. Parent separately owns the exact-binary592ORE regression.
Final timing completion, normalization, comparisons and release publication are
still outstanding. Durable controls/proof/version receipts are in
results/benchmarks/2026-09-17-dynamic-baseline/v142-justification.

Comparison renderer51984639 is queued after all four baseline/final audit jobs.
It works from immutable justification-comparison-v1 and expands both frozen
matrices rather than looping only over observed invocations. Local partial
validation proves10,980 expected attempts,9,150 measured, and exact300case
alignment between baseline and final. Only complete five-repetition paired
cases yield ratios; missing or invalid rows remain counted. First final warmup
task completed6/6 independently correct extractions, with native version1.4.2.
This checks launch integrity and is not a completed performance comparison.

Bounded early measured-case review51985085 completed: earliest frozen MMO q000
STAR-module cohort, all six repetitions and all three bounds, selected by order
and readiness rather than performance. Independent audits and OWLAPI support
normalization validate all234 attempts (198 baseline,36 final KM), with one
identical logical support family across arms. All39 five-repetition dispersion
rows and195 compatible paired ratios were recomputed independently from raw
wall records; warmup is excluded. Renderer excludes75 incompatible pairs rather
than creating speed claims from mechanism mixtures or unknown bounded enumeration.
Evidence is saved under justification-early-case-review in the dynamic-baseline
results directory. Its matrix-complete flag is explicitly subset-only; this is
not the final benchmark or an overall performance claim. No live run was changed.
