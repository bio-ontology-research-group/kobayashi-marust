# Incremental reasoning and entailment justification releases

Baseline: published v1.4.0, source c10e22f, IBEX binary SHA-256
`ddc30d2f9013b371b5c4ec19c0623c91ecc1b2dbdc172ded9002fd238903d09a`.
Target releases: v1.4.1 incremental evaluation; v1.4.2 justification evaluation.
Only minor KM fixes are in scope. This document specifies planned experiments;
pilot results must not be described as the completed release evaluation.

## Literature search (2026-09-17, before benchmark implementation)

* Kazakov and Klinov, ISWC 2013, *Incremental Reasoning in OWL EL without
  Bookkeeping*, Section 5.3:
  https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.090/Publikationen/2013/KazKli13Incremental_ISWC.pdf
  Evaluates real GO history and 250 generated versions for GALEN/SNOMED,
  with 1, 10, or 100 additions and deletions per revision. Separates initial
  classification from updates and compares against Pellet. We adopt the
  generated-history method and change sizes, extending evaluation to full DL
  and ABox changes in separately reported tracks. We do not claim to reproduce
  their historical datasets or timings.
* Horridge, Parsia and Sattler, ISWC 2012, *Extracting Justifications from
  BioPortal Ontologies*, pp. 287–299, DOI 10.1007/978-3-642-35173-0_19:
  https://web.stanford.edu/~horridge/publications/2012/iswc/justextract/
  The authors provide flattened ontologies, non-trivial entailments, raw
  justifications, counts, sizes, and extraction times. Adopt this evaluation
  structure with immutable available ontologies. First-justification latency
  and bounded enumeration are separate outcomes; a bound is never evidence
  of complete enumeration. The supplementary experiment software was retrieved
  before benchmark design. Its properties specify 1,000 entailments, shuffled
  ordering and a 600,000ms justification timeout. We adopt the timeout while
  using the independently frozen OBO panel and stable hash sampling; this is
  an adaptation, not a replication of that corpus. Archive hash and details
  are recorded in JUSTIFICATION-NOTES.md.
* Bail, Parsia and Sattler, ISWC 2010, *JustBench: A Framework for OWL
  Benchmarking*: https://iswc2010.semanticweb.org/pdf/PreprintCollectionISWC2010.pdf
  Uses justification-derived reasoning problems. This complements extraction
  evaluation but does not replace timing the extraction of a justification.

## Shared controls

Freeze ontology bytes, imports closure, queries, update traces, seed, runtime
versions, binary/JAR hashes, harness hashes, CPU model and job identifiers.
Use Slurm compute nodes; baseline single CPU, 20 GiB process-tree cap,
240 seconds per classification/update and 600 seconds per explanation.
Run one warmup and five measured repetitions in rotated reasoner order.
Keep JVM startup, parsing, inference and output costs separately where APIs
permit; publish end-to-end costs as well. Record peak process-tree RSS.
Timeout, unsupported, resource failure and incorrect output are distinct.
Never average failures away. Publish per-case rows and paired speedups only
on mutually correct completions, with coverage alongside speed.

Comparators: KM, ELK (validated supported fragment only), HermiT, JFact,
Openllet and Konclude. Inspect each adapter's actual update capability;
label manager/flush sessions as such until retained work is verified. Engines
without an update API receive an explicitly labelled fresh-rebuild arm.
Do not treat accepting unsupported axioms as a valid successful result.

## Incremental benchmark

Use immutable real EL and expressive ORE/biomedical ontologies with a
size/profile-stratified selection frozen before timing. Include synthetic
controls with known taxonomy changes and separate TBox, RBox and ABox tracks.
For generated TBox traces, keep a pool of concept axioms, reserve a seeded
holdout, then exchange n active and n inactive axioms for 250 revisions,
n in {1,10,100}. Also measure addition-only and deletion-only sequences and
round trips. Preserve declarations for the original vocabulary. Small corpora
with insufficient eligible axioms are reported as ineligible at that n.

Compare retained-session updates with a fresh reasoner on every resulting
ontology. Independently compare complete full-IRI taxonomy and consistency
against a second suitable reasoner. Canonical taxonomy contains consistency,
unsatisfiable classes, and all non-reflexive named subsumptions excluding
trivial top/bottom rows. Record KM route, retained backend, update receipts,
and rebuild/migration counts. Validation and signature writing are timed
separately from update inference, and their costs remain visible. KM source
transport includes normalization and result serialization; avoid presenting
that latency as directly equivalent to Java's inference-only interval.

Interpret receipt fields against the bound implementation. In the current KM
source-session path, `invalidated_states` counts facts rederived after retention,
not discarded old facts. Retained counts include internal reflexive/top facts;
neither retention nor a meaningful-update strategy flag establishes a speedup.

## Entailment-justification benchmark

Freeze non-asserted named subsumption queries independently of KM, stratified
by ontology/profile. Hash all named class IRIs, select the first 128, retrieve
nontrivial named superclasses with HermiT, and select the first five hashed
nonasserted subclass pairs. JFact confirms consistency and each selected
entailment. Preserve preparation failures in the six-ontology panel inventory.
Add unsatisfiability,
inconsistency and non-entailment controls. Sample queries by stable hash,
not KM success. Report full-ontology and shared locality-module tracks
separately, retaining module extraction cost. Modules must come from a
reasoner-independent extractor and be identical across arms.

Measure entailment checking, first subset-minimal justification, and bounded
multiple-justification extraction (limits 1, 10, 100) separately. Include a
common deterministic deletion-based black-box extractor across reasoners to
isolate oracle cost and native/library extraction arms to compare actual
user-facing services. Report oracle calls, support size, latency, RSS,
verified supports and whether enumeration exhausted its search.

For every returned J, check J is a subset of input source axioms, independently
verify J entails q, and verify J without each axiom does not entail q.
Different valid minimal supports are not mismatches. Include analytic cases
with known complete support families to test enumeration. Native KM source
occurrences and OWLAPI set semantics need explicit duplicate normalization.
An entailment-only run does not count as a justification benchmark.

## Change and release gates

First reproduce a failure or measure a bottleneck against the unchanged
baseline. Make only a minor fix, demonstrate benefit on held-out cases, then
Lean-certify that exact implementation, as required by the user even for
changes outside CB calculus. Preserve proof/source/runtime bindings; no
post-certification code drift. Run relevant Rust tests, full ORE regression
and independent soundness comparison. Release only after these gates and
complete benchmark evidence, documentation and comparisons are present.

## Initial state

No pre-existing jobs for this objective were live on IBEX at inspection.
Existing v1.3 incremental evidence is a KM-only clause microbenchmark, not
an external source-level comparison. Existing explanation examples are
small correctness demonstrations, not the requested benchmark.

## Frozen main incremental panel and pilot adjustments

`select_incremental_panel.py` chooses the ontology nearest each of 1,000,
10,000 and 100,000 logical axioms on a log scale, separately for OWL 2 EL
and other OWL 2 DL ontologies in the frozen 2026-08-30 OBO inventory.
Require no data properties and at least 200 logical axioms; ties use the ID.
The resulting panel is mmo, hao, vto, mfomd, to and uberon. Exact source hashes
are in `incremental-panel.tsv`. Resource failures stay in the denominator.
ELK and Whelk are included only on the EL main-panel stratum. ADO in the
initial pilot is a harness check, not a supported-fragment performance claim.

Main histories use the same seeded reserve/exchange algorithm as the pilot,
250 updates at each n. Snapshot compression saves space and does not change
axioms. Both Java and KM fresh arms rebuild reasoning state within a persistent
runtime: Java constructs a new reasoner; KM sends `init` each time. This avoids
charging a new KM process against a warm JVM on every revision. The initial
pilot used a new KM process for each fresh state; do not pool its timing with
the main experiment. Each state has a 240-second deadline. A history arm has
a 7,200-second operational cap, reported separately from state timeout.

The initial Whelk failure came from an OWLAPI 4/5 binary interface mismatch
in the harness, not reasoning. Use `applyChange(AddAxiom/RemoveAxiom)` instead
of version-specific collection overloads. Actual IBEX Slurm association is
`pi-hohndor` (verified by sacctmgr); submission under the skill's historical
`c2014` account was rejected. All compute remains in Slurm.

Full-history repetitions store SHA-256 of each complete canonical taxonomy
instead of hundreds of gigabytes of duplicate signatures. Hashing covers all
sorted full-IRI rows, consistency and unsatisfiability, with UTF-8 and one LF
per row; this is not a sampled entailment test. All main arms and repetitions
use this same policy. Pilot runs retain complete compressed taxonomies;
any main digest disagreement requires a targeted full-output rerun for diagnosis.

Each Java measurement now verifies `driver-build.sha256` before launching:
source, entry class and every class in the driver directory must match the
build receipt. Missing, changed or unrecorded classes are rejected. The
measurement retains both the receipt hash and compiled-artifact hashes.
This binds operational results to compiled bytes; it is not a semantic proof.
The revised guard is locally tested but has not yet been deployed to IBEX.

## Incremental execution after restored access

The v3 driver adds Konclude as a fresh process rebuild comparator (the deployed
OWLlink runtime lacks Retract). It records process startup/decompression/request
preparation separately and never claims retained inference. Konclude uses the
same canonical full-taxonomy hash policy, 240-second state deadline, 20 GiB
process-tree cap and 7,200-second history cap. There are 108 case/reasoner jobs:
18 histories times four DL comparators plus Konclude, and three additional
EL histories per size times ELK/Whelk. Each job performs one warmup and five
measured repetitions, with both arms except fresh-only Konclude. A fixed
20260917-seeded permutation distributes reasoners across array submission
order; paired session/fresh arm order alternates across repetitions. Initial array
concurrency was capped at eight; the scheduling amendment below records its
later increase. All workers request the same CPU model.

The v3 gate checks all 13 supported arms on six mmo revisions: full compressed
signatures must agree with HermiT and each corresponding digest-only output.
Build receipts reject modified Java artifacts. Main execution requires a
successful gate. Larger pilot failures remain in the frozen panel: to and
uberon are not replaced because they timed out or errored. The main auditor
checks all three change sizes, every repetition, and the warmup independently.

## Pure DL eligibility correction (before supplemental timing)

The first Konclude TO run rejected a DLSafeRule/ClassAtom input. Source inspection
confirmed SWRL rules in the frozen TO ontology despite the inventory's OWL2DL
flag. OWLAPI profile membership alone therefore does not establish pure SROIQ
eligibility. The original panel and all its results remain published, with
rule-bearing inputs labelled DL+rules extension stress cases, not pure DL.
The corrected pure-DL stratum additionally requires zero SWRL_RULE axioms,
zero remaining imports and zero data properties, plus a fresh OWL2DL profile
check. No axioms are removed from the ontology to achieve eligibility.

Before any supplemental performance measurement, `pure-dl-candidates.tsv`
freezes the ten nearest original eligible DL candidates at each target size,
using the same logarithmic distance and ID tie break. `ProfilePanelCheck.java`
checks their actual ontology objects without invoking a reasoner. The first
syntactically eligible candidate at each size joins the pure-DL panel if not
already present. If all ten fail, expand the same ranking until an eligible
candidate is found; never select using KM success, latency or memory. Publish
all eligibility rows, source hashes and the separate expanded timing results.

The eligibility audit found 25 SWRL rules in TO and 3 in uberon, while all
reported OWL2DL profile checks remained true. The resulting pure-DL choices
are mfomd (998 logical axioms), zfa (12,330), and mro (84,613). The latter two
are the first zero-rule, profile-valid entries in the frozen size rankings;
planp (20 rules), mp (26), and vo (4) were rejected syntactically. The separate
`incremental-pure-dl-supplement.tsv` adds zfa and mro at all three change sizes,
with exactly the same trace generator, runtime hashes, resource limits,
shared passed driver gate, one warmup and five measured repetitions. Existing
mfomd and EL evidence comes from the original main run. TO and uberon remain
extension stress cases. Do not aggregate them into pure-DL coverage or speedups.

## Scheduling amendment during execution

On 2026-09-17 between 04:51:16 and 04:51:36 UTC (IBEX clock), pending
arrays were limited by their task caps while 2,265 matching Gold 6248 CPUs
were idle. The array caps were doubled without changing per-job resources,
deadlines, inputs, repetitions or within-job paired order:

| Array | Purpose | Initial cap | Revised cap |
|---|---|---:|---:|
| 51982318 | Baseline incremental | 8 | 16 |
| 51982375 | Baseline incremental pure-DL supplement | 4 | 8 |
| 51983825 | Final v1.4.1 incremental | 6 | 12 |
| 51982389 | Baseline justification | 12 | 24 |
| 51982752 | Baseline justification pure-DL supplement | 6 | 12 |
| 51984134 | Final v1.4.2 justification | 8 | 16 |
| 51984137 | Final v1.4.2 justification pure-DL supplement | 4 | 8 |

Existing observations remain in the evaluation. Preserve job start times, hosts
and per-repetition ranges: shared-filesystem and memory-bandwidth contention
can affect wall times across scheduling phases. A phase-related timing shift
is not evidence of an engine improvement. The separate ORE regression caps
remain unchanged. Verification is recorded in
`results/benchmarks/2026-09-17-dynamic-baseline/scheduling-amendment.json`.

At 05:23:22 UTC (IBEX clock), a second capacity check found 105 usable matching
nodes, 2,357 unallocated CPUs and 20,423,680 MiB of unreserved memory, enough
for 795 additional jobs at the requested one CPU and 22 GiB allocation. The
seven caps above were doubled again, to 32, 16, 24, 48, 24, 32 and 16 in the
same table order (192 total concurrent jobs at most). No case, resource limit,
repetition, deadline, code or within-job order changed; no job was resubmitted.
The same cross-phase contention caveat applies. Full updates and independently
verified scheduler settings are in
`results/benchmarks/2026-09-17-dynamic-baseline/scheduling-amendment-2.json`.
All scheduling receipts must accompany the final comparison evidence.


At 07:11:46 UTC (IBEX clock), a third capacity check found 174 additional
one-CPU, 22-GiB task slots across matching usable nodes. This check conservatively
used the smaller of unreserved and reported free memory on each node. The
original incremental cap rose from 32 to 64, the original comparator
justification cap from 48 to 128, and the final original-panel justification
cap from 32 to 64. At most 120 additional waiting tasks could start under the
observed queue, leaving capacity headroom. Other array caps were unchanged.
Long comparator attempts were holding slots while later planned tasks waited.

All live array throttle values were independently verified. Updates for two
arrays also reported already-finished elements; those elements were not rerun.
Per-task resources, timeouts, immutable artifacts, repetitions and within-task
arm order remain unchanged. This is another scheduling phase, not a new
experiment or an engine improvement. Preserve its host/start-time provenance
and the shared-resource contention caveat when comparing results. The complete
node-capacity snapshot and update receipts are in
`results/benchmarks/2026-09-17-dynamic-baseline/scheduling-amendment-3.json`.

### Common-driver stream correction (2026-09-17)

The original HAO q002 module runs exposed a benchmark adapter error: Jackson
closed the KM stdout pipe after reading the response object, before the worker
necessarily finished writing its trailing newline. The resulting broken-pipe
exit was reported as an extraction error despite a valid response object. A
standalone regression against the pinned HermiT runtime reproduces the early
close; the corrected adapter drains stdout to EOF before parsing. This changes
the harness, not KM reasoning. Original results and errors remain archived.

The correction reruns the entire KM common-driver arm for both the released
baseline and final candidate, on all original and supplementary tasks, bounds
and repetitions. This is 600 tasks and 1,800 extraction attempts, including
300 warmups. It does not selectively replace failed attempts. All original
source/query hashes, runtime binaries, limits and independent support checks
remain fixed. New manifests bind the changed adapter and compiled classes.
Before measured reruns, positive and negative HAO probes and an independently
verified small MMO extraction must pass for both binaries.

Corrected runs form a separate harness revision. The original arm rotation
is inapplicable when only one arm is rerun; repeated bounds still run in their
frozen order. This and the later scheduling phase can affect cache and shared
resource contention. Preserve the original report and identify corrected
common-driver measurements explicitly when comparing them with unchanged peer
and native arms. Do not pool repetitions across harness revisions or silently
relabel an original failure as success.

The explanation budget is nested: the outer extraction limit is 600 seconds,
while KM central-worker invocations retain the frozen 240-second limit in both
native and common-driver arms. MFOMD q000 module diagnostics varying that
internal limit to 1 and 2 seconds reproduce the generic worker exit -1 at the
corresponding boundary. The atomic CB wrapper does not preserve the internal
timeout flag in its public error. Raw extraction errors remain errors, with
this diagnosed mechanism reported separately; -1 alone does not distinguish
a timeout from another signal. Short-limit diagnostics are excluded from
performance measurements. See v142-justification/mfomd-cap-diagnosis in results.

At 08:25 UTC the corrected common-driver arrays increased from caps 16 each
to 64 for each original panel and 32 for each supplementary panel. The
matching-node check found 175 additional 1-CPU/22-GiB slots using the minimum
of unreserved and reported free memory. The change permits at most 128 extra
tasks, leaving 47 slots of measured headroom. All four live throttle values
were verified. Sources, limits, repetitions and within-task order are unchanged;
no task was restarted. The receipt is justification-stream-v4/scheduling-amendment.json.
Include this correction-phase scheduling change with the three earlier
amendments when interpreting shared-resource contention.

### Konclude common-driver correction extension

The same Java subprocess reader serves the Konclude common-driver wrapper.
The supplementary audit exposed valid JSON followed by a Python broken-pipe
error when that reader closed stdout early. The stream correction therefore
also reruns the complete Konclude common-driver arm across all 300 frozen
tasks and three bounds: 900 attempts, including 150 warmups. It does not
select cases based on success. Positive and negative HAO/ZFA probes and an
independently checked MMO support passed before submission. An initial staging
probe failed because its environment lacked the compatibility-library path;
that failure is retained separately from benchmark outcomes.

The comparison selects corrections by original panel and arm, requires every
original task and repetition, and rejects overlapping replacements or changes
beyond the exact stream patch. Earlier KM-only reports remain intermediate
artifacts. The final combined report must use both KM and Konclude correction
cohorts. Konclude unsupported-input errors remain failures. The two new arrays
use caps of 64 and 16 after observing capacity for 136 additional one-CPU,
22-GiB allocations. Later execution and shared-resource effects remain timing
limitations; per-task limits, inputs, binaries and queries are unchanged.
