# Rendering incremental comparisons

`render_incremental_comparison.py` reads completed or partial audit JSONs. It
never launches benchmarks, edits input evidence, or establishes certification.
Keep the original baseline and pure-DL supplement as separate immutable audits;
they can share a report label because their ontology cases differ:

```bash
python3 render_incremental_comparison.py \
  --audit v1.4.0=baseline-main-audit.json \
  --audit v1.4.0=pure-dl-supplement-audit.json \
  --audit v1.4.1=certified-km-only-audit.json \
  --out incremental-comparison
```

Output includes README.md, attempts.tsv, summary.tsv, paired-speedups.tsv,
paired-speedup-summary.tsv, provenance.tsv and report.json. The output directory
must not exist; this prevents silently replacing an earlier report.

Future KM-only audits use the `audit_incremental.py` schema: each case retains
`expected_states`, `manifest_sha256`, and `repetitions`; each repetition has
`arms` such as `km/session`, containing `complete`, `issues`, `states`,
`measurement`, `timings`, and `km_receipt_summary`. Include every planned attempt,
including missing/error/timeout entries. The renderer borrows fresh HermiT and
JFact references from other supplied audits only when case, manifest SHA and
state count match exactly. All completed fresh reference repetitions must
agree; it does not choose a convenient agreeing pair among conflicting outputs.

For main runs, use five measured repetitions plus warmup (the default).
`--expected-repetitions` exists for another explicitly declared protocol.
`panel-pilot` inputs remain pilot-labelled and never become full main evidence.
Analytic controls, pure OWL2DL, EL, DL+rules stress and unverified profiles remain
separate. The pure-DL list reflects the documented explicit SWRL-rule audit.

Execution completeness differs from correct completion. Final measurement
records with a return code establish a terminal attempt. A stale watchdog
checkpoint, including a timeout checkpoint written before process termination,
does not. Optional scheduler receipts can establish terminal execution:

```bash
python3 render_incremental_comparison.py \
  --audit v1.4.0=baseline-main-audit.json \
  --slurm-receipts slurm-terminal.tsv --out incremental-comparison
```

Receipts accept tab-separated or `sacct -P` columns `JobID` (or `JobIDRaw`),
`State`, `ExitCode`. They are hashed in provenance. If a missing later repetition
has no job metadata, the renderer can infer a unique job from earlier attempts
of the same labelled case/reasoner. An entirely missing job without any such
binding remains unverified; scheduler termination alone cannot prove output
correctness. It does not infer liveness or termination from elapsed time.

Timing medians and observed minimum–maximum ranges use independently correct
complete histories, with sample counts and all planned attempts retained in
coverage denominators. Warmups are excluded. Within-reasoner session/fresh ratios
require both arms independently correct. Whole-process history wall time and
individual API intervals remain separate; Java inference time is never divided
by KM request/response time to claim a cross-interface speedup. Reuse counts
retain exact rebuilds and explicit receipt metrics; retained_backend alone is
not evidence of preserved inference. Konclude's unsupported retained-session
capability remains explicit rather than being counted as a successful update.

For the current KM source-session implementation, `invalidated_states` is the
sum of newly derived subsumptions and edges after retaining unaffected state.
Report it as rederived facts, not as a measured count of discarded old facts.
Retained counts include internal reflexive/top facts, and
`meaningful_incremental_update` is a strategy flag. None of these counters alone
establishes a speedup; compare independently correct paired histories. The
measured MMO example and source-level interpretation are recorded in
`../../results/benchmarks/2026-09-17-dynamic-baseline/MMO-UPDATE-COST.md`.

Validation on the existing v3 controls gives 54/54 terminal attempts but 50/54
independently correct histories and 21 eligible paired whole-history wall ratios.
The four excluded arms are KM ABox fresh/session and JFact RBox/disjunction
session. These are pilot controls, not the release performance comparison.
Seven focused tests also cover reference disagreement, wrong-but-self-consistent
pairs, manifest mismatches, warmup exclusion, planned-repetition denominators,
and the distinction between scheduler termination and correct output.

## Direct failure-cause sidecar

`enrich_incremental_failures.py` writes a new sidecar and never changes raw
supervisor records. Run it after the audit dependencies terminate, supplying
the same labelled audit inputs as the renderer, then pass its JSON via
`--failure-causes failure-causes.json`. The raw operational status remains in
attempts.tsv; a separately recorded failure_kind can distinguish explicit
worker timeouts, unsupported-operation exceptions and OWLlink parser errors.
A parser rejection alone is `parse_error`, not a speculative claim that an
axiom or ontology is unsupported. Missing, stale or contradictory evidence
keeps the generic status. Only direct findings with matching audit and
measurement hashes can refine the report's outcome category.

Evidence reads are capped at 128 KiB per file. Large logs retain hashed first
and last segments with offsets, lengths and file size; these are not presented
as full-file hashes. Konclude state receipts must match revision, reasoner,
arm and binary SHA before they can establish a state timeout. Source XML must
be complete and parseable before an OWLlink parse-error classification is made.
Scheduler termination still does not prove correct reasoning output.

Java extract_s ends after taxonomy extraction. Its subsequent signature
hashing/writing belongs to whole-process wall time, not extract_s. KM
canonicalize_s similarly excludes signature writing. The renderer states
these boundaries explicitly and retains all original interval names.

A bounded early review of eight completed rep-0 histories verified 251 ordered
states, all digest files, matching immutable manifest hashes and the configured
240-second state / 7,200-second history limits. On mmo-n10, final KM session and
fresh outputs matched JFact session/fresh and Konclude fresh at every revision;
preregistered final HermiT/JFact validation still awaits HermiT's main run.
This is neither a full-matrix result nor a five-repetition performance claim.
The 25-hour Slurm limit covers 12 arms at the 2-hour history cap, leaving one
hour for metadata validation, source hashing and teardown. Any later scheduler
truncation remains an explicit incomplete attempt in the final report.

The scheduling amendment at 2026-09-17 04:51:16–04:51:36 UTC doubled array
throttles while preserving per-job limits, inputs, repetitions and CPU model.
Keep scheduling-amendment.json alongside final report provenance. Original
audit measurement objects retain host and start_epoch for phase-aware review.
Shared-filesystem or memory-bandwidth contention can shift wall times across
scheduling phases; do not attribute such shifts to reasoner changes. Retain all
completed rows and per-repetition ranges rather than selecting a timing phase.

Any main digest disagreement requires a separate full-output diagnosis. Replay
session history from revision zero through the first differing revision, and
fresh-classify that exact snapshot; a single fresh run cannot diagnose retained
state errors. Compare full sorted canonical rows and preserve the original
failure result. The bounded eight-history review found no such disagreement.
