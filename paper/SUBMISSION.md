# Submission plan

## Primary target

Submit this manuscript to the **Semantic Web Journal as a Full Paper**.  This
category fits the combined contribution better than a short tool/system report:
KM is the evaluated system outcome, while the human-directed agentic process
and Lean-gated publication architecture are original research results.  The
current evaluation is also designed for the journal's explicit replication
criterion.

The current official author guidance requires one PDF at initial submission,
3--7 keywords, the Sage journal template for accepted manuscripts, links to
evaluation data where possible, and disclosure of inaccessible data in the
cover letter.  The journal publishes submitted manuscripts and reviews through
an open and transparent review process.  Author guidance:
<https://www.semantic-web-journal.net/authors>.

The final artifact must be one immutable, well-organized archive at a stable
URL such as Zenodo, with a top-level README.  It must bind the paper PDF,
source, exact software tag, corpus manifests, result records, validator logs,
AgentsView reports, proof-gate reports, and scripts by digest.  Restricted
SNOMED CT content and credentials must not be included.  SWJ does not permit
manuscript updates during active review, so both the submitted PDF and artifact
must remain frozen until a formal revision decision.

## Fallback target

The **Journal of Automated Reasoning** is the fallback if the paper is revised
to foreground the certified publication relation, regular-model arguments,
and calculus integration.  Its current guidance uses single-blind review,
encourages the Springer Nature LaTeX template, requests editable sources and a
PDF, and requires relevant declarations.  It also specifically requires
substantive LLM use to be documented in Methods, which this manuscript already
does.  Author guidance:
<https://link.springer.com/journal/10817/submission-guidelines>.

## Submission gates

- [x] Full system architecture and supported-interface description.
- [x] Exact v1.3.0 source and formal-evidence binding.
- [x] Historical ORE evaluation framed as regression evidence rather than a
  current corpus.
- [x] Dated OBO freeze, reproducible preparation protocol, and eight pinned
  reasoner baselines.
- [x] Separate hard-case matrix and complete FMA experiment.
- [x] Explicit agent-use account, human responsibility, and Lean trust boundary.
- [x] Complete and strictly validate all 1,512 OBO reasoner/ontology tuples.
- [x] Adjudicate every expressive-reasoner disagreement before promoting any
  current-corpus consensus to a correctness claim.
- [x] Replace provisional current-corpus prose with generated aggregate tables.
- [x] Add and adjudicate the pre-standalone laptop evidence listed in
  `evidence-needed.md`.
- [x] State the absence of the credential-gated BioPortal sample and licensed
  SNOMED CT artifact in the evaluation scope, limitations, and cover letter;
  neither enters an aggregate or redistributable artifact.
- [x] Run seven isolated independent Codex reviews from `review-prompts.md`,
  integrate supported findings, and retain hash-bound reports and dispositions.
- [x] Convert the canonical manuscript through the current Sage template and
  verify a source-bound two-column build with no undefined references,
  layout overflows, or LaTeX/package errors.
- [ ] Freeze a public artifact with immutable source, benchmark manifests,
  result records, validation logs, generated tables, and an archival DOI.
- [x] Draft a cover letter identifying the Full Paper category, inaccessible
  licensed inputs, artifact plan, declarations, and handling-editor expertise.

A complete draft is available in `COVER-LETTER.md`. It states the planned
final GitHub-to-Zenodo synchronization without inventing a DOI. Submission
exclusivity and competing interests still require author confirmation before
the letter is sent; the manuscript and letter contain the confirmed KAUST
funding acknowledgements.

Run `make -C paper submission-audit` for the machine-readable packaging audit.
It reports pending gates without weakening `make -C paper checks`; use
`python3 paper/scripts/audit_submission_readiness.py --require-ready` only when
preparing the actual submission package.

The paper is not submission-ready while any unchecked evidence gate above can
change a central result or the reconstructed development history.
