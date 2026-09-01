# KM v1.3.0 paper

This directory contains the source and reproducibility material for the KM
v1.3.0 system and methods paper.

The intended first venue is the *Semantic Web Journal* as a full research
paper. `main.tex` remains the single canonical scientific source while results
are still changing. A checked staging converter builds that same content with
the Sage/SWJ class, so publisher compatibility does not depend on maintaining a
second manuscript by hand.

Build with:

```sh
make -C paper
```

Run the complete currently available manuscript and evidence gate with:

```sh
make -C paper checks
```

This includes a venue-facing manuscript contract that enforces a 150--250-word
abstract, 3--7 keywords, the system/evaluation/Methods/related-work structure,
all eight requested baseline families across the two evaluations, required
declarations, and absence of stale running-benchmark markers. The two funding
and competing-interest confirmations remain visible but are counted rather
than silently accepted.

To stage the published-style two-column Sage build, obtain Sage's LaTeX
template from the publisher link in the SWJ author instructions, then run:

```sh
python3 paper/scripts/stage_sage_manuscript.py \
  --template-dir /path/to/directory/containing/sagej.cls \
  --output-dir .work/artifacts/paper-sage-staging
cd .work/artifacts/paper-sage-staging
pdflatex -interaction=nonstopmode -halt-on-error main-swj.tex
bibtex main-swj
pdflatex -interaction=nonstopmode -halt-on-error main-swj.tex
pdflatex -interaction=nonstopmode -halt-on-error main-swj.tex
cd ../../..
python3 paper/scripts/verify_sage_staging.py \
  --staging-dir .work/artifacts/paper-sage-staging
```

The converter copies only generated paper inputs into the disposable build
tree. It does not vendor or modify `sagej.cls`, whose separate Sage rules of
use remain in force. Pass `--class-options Review,sageh,times` for a
single-column review copy.

Regenerate the repository-derived development statistics and verified
milestone table with:

```sh
python3 paper/scripts/extract_history.py
python3 paper/scripts/render_method_milestones.py
```

The milestone renderer verifies full commit identities, dates, chronological
order, and membership in the exact `v1.3.0` ancestry. The full 1,730-commit
timeline remains available as TSV; the manuscript table selects 18 landmarks.

Regenerate the privacy-preserving retained agent-process tables with:

```sh
python3 paper/scripts/extract_agent_sessions.py
python3 paper/scripts/render_agentsview_usage.py
python3 paper/scripts/import_laptop_evidence.py
```

The AgentsView renderer pins the three native reports and tool version by
SHA-256. It checks that daily usage and activity output-token totals agree and
that phase rows conserve all native output tokens and agent-minutes. The
artifact contains no prompts, responses, shell commands, credentials, or tool
results. The laptop importer verifies both source manifests, imports only
privacy-preserving metadata and selected KM memories, records the separately
archived git-bundle digest, and keeps the v0.33.1 laptop counters separate from
the v0.41.1 workstation reports. `scripts/collect_laptop_history.sh` and
`scripts/collect_laptop_agentsview.sh` reproduce the collection paths.

Regenerate the two ORE tables from the tagged release summary, frozen external
panel, baseline manifest, and per-ontology shared-correct ledger with:

```sh
python3 paper/scripts/render_ore_tables.py \
  --baselines paper/benchmark/ore-baselines.tsv \
  --shared paper/generated/shared-correct.json \
  --shared-detail paper/generated/shared-correct.tsv \
  --output paper/generated/ore-results.tex
```

The generator fails if the release tag, KM binary, external-panel digest,
baseline source revisions, completion populations, or recomputed pairwise
statistics differ from the recorded evidence.

Verify and render the exact-v1.3 incremental scale check with:

```sh
python3 paper/benchmark/render_incremental_v13.py
```

This pins the raw ten-repetition EL and CB records, source-bound job receipt,
scheduler log, exact release binary, and runner. Every measured retained
taxonomy was equal to fresh classification of the same union. The paper reports
the lower retained-add latency and the higher retained-session peak memory.

Verify the independently witnessed current-corpus disagreements with:

```sh
python3 paper/benchmark/verify_disagreement_witnesses.py \
  --ledger paper/benchmark/disagreement-evidence.tsv \
  --evidence-root paper/benchmark/generated/disagreement-evidence \
  --output paper/benchmark/generated/disagreement-witness-verification.json
```

The verifier checks source-bound premise hashes and replays the finite DOID and
CVDO derivations. It fails closed if a required premise is removed.

## Contemporary benchmark state

The OBO 2026-08-30 freeze contains 189 acquired inputs and one explicit
source-unavailable registry row. All eight 189-input panels are complete. Job
`51035710` independently revalidated all 1,134 Java records; job `51041442`
produced the inconsistency-normalized strict 1,512-record aggregate with zero
missing or invalid records. The imported final directory contains the
aggregate, disagreement ledger, four manuscript tables, per-record digest
manifest, and final `SHA256SUMS`.

The final renderer rejects missing or invalid records, requires each OWL 2 DL
status row to conserve the independently profiled population, escapes all
machine-generated TeX fields, and labels pairwise KM/external columns
explicitly. See `benchmark/README.md`, `benchmark/execution-jobs.tsv`, and
`benchmark/finalization-jobs.tsv` for the complete protocol and job history.

To verify and atomically import a replacement completed IBEX `final/`
directory from a temporary local directory, run:

```sh
python3 paper/benchmark/import_current_final.py \
  --source .work/artifacts/current-final-from-ibex --replace-existing
```

The importer accepts only the exact 8-by-189 result-record manifest, verifies
the final `SHA256SUMS`, requires status conservation and zero missing or invalid
records, and checks that the generated TeX names the aggregate digest. It then
installs the verified final directory and manuscript table atomically. It
refuses to replace an existing import unless `--replace-existing` is explicit.

After copying the dependency-gated evidence archive and its sidecar, stream
verify every packaged result record against that imported manifest with:

```sh
python3 paper/benchmark/verify_current_evidence_archive.py \
  --archive .work/artifacts/current-obo-evidence-20260830.tar.gz \
  --sha256 .work/artifacts/current-obo-evidence-20260830.tar.gz.sha256 \
  --final paper/benchmark/generated/current-final \
  --output paper/benchmark/generated/current-final/evidence-archive-verification.json
```

This check also requires byte-identical final aggregate files and rejects
unsafe paths, generated taxonomies, full corpus/import paths, runtime archives,
executables, credentials, and conversation-body material.  Small source-bound
diagnostic modules remain visible evidence rather than being removed.

Run the formal-claim, historical-case, tag-evidence, release-log, and citation
audits with:

```sh
python3 paper/scripts/verify_formal_claims.py
python3 paper/scripts/verify_case_study_commits.py
python3 paper/scripts/verify_tagged_evidence.py
python3 paper/scripts/summarize_release_gates.py \
  --logs .work/worktrees/v1.3/.work/logs \
  --output paper/generated/release-gate-summary.json
python3 paper/scripts/verify_citations.py
python3 paper/scripts/render_citation_occurrences.py
python3 paper/scripts/render_route_glossary.py
```

The occurrence renderer binds every individual `\\cite{...}` use to its exact
line, surrounding claim context, audited key, verification source, and status.
This complements the key-level audit and makes reused references reviewable at
each materially different manuscript claim.

The route-glossary renderer reads the public route list and option constants
directly from `engine/src/routing.rs`, expands common settings, applies
route-local overrides, and writes both TSV and TeX supplements. It therefore
fails when a public route lacks a source mapping instead of allowing a prose
glossary to drift from the release catalogue.

The generated files under `paper/generated/` are evidence, not hand-edited
narrative. `claims-ledger.tsv` maps manuscript claims to authoritative
evidence. `goal-completion-audit.tsv` maps each requested paper deliverable to
its evidence and remaining external action. `SUBMISSION.md` is the
submission-readiness checklist, and
`COVER-LETTER.md` is a deliberately incomplete SWJ Full Paper cover-letter
draft whose visible markers prevent premature submission. Claims that
require records from the original laptop are listed in `evidence-needed.md`.
The strict current-corpus aggregate and journal-template conversion are
complete. The paper is not submission-ready until author-confirmed
declarations and the immutable
archival deposit are complete.

Seven isolated Codex subagents reviewed structure, flow, clarity, style,
terminology, related work, and citation support against one immutable
manuscript snapshot. The hash-bound reports are retained under
`paper/reviews/`. Each finding is accepted, rejected, or deferred with a
rationale in `paper/reviews/dispositions.tsv`. The final disposition audit writes
`paper/reviews/disposition-verification.json` bound to the revised manuscript;
a header-only or stale disposition file does not satisfy the packaging audit.

Use TSV columns `review`, `severity`, `finding`, `disposition`, `rationale`, and
`manuscript_action`, then verify the complete set with:

```sh
python3 paper/scripts/verify_review_dispositions.py
```

The verifier derives numbered major and minor findings from the imported
reports, requires exactly one disposition for each, rejects references to
unknown findings, and binds the resulting receipt to both reviewed and current
manuscript hashes.

Run the separate packaging audit with:

```sh
make -C paper submission-audit
```

Stage the redistributable deposit tree, including the exact source tag, both
PDFs, four certification logs, and the independently verified current-OBO
evidence package, with:

```sh
python3 paper/scripts/stage_submission_artifact.py --replace
```

The staging command checks the tag commit and benchmark-archive digest before
copying, excludes LaTeX build by-products and placeholder DOI files, writes a
machine-readable receipt, creates a sorted top-level `SHA256SUMS`, and verifies
the complete manifest. It does not claim immutability or invent a DOI; rerun it
after laptop evidence and review dispositions are imported, then deposit that
frozen tree in Zenodo or an equivalent archive.

This audit is intentionally fail-closed and currently reports pending work. It
does not replace `make -C paper checks`. At final submission, run
`python3 paper/scripts/audit_submission_readiness.py --require-ready` and retain
the generated JSON in the archive.
