# KM 1.3 paper artifact

This directory defines the top-level layout and verification procedure for the
immutable artifact accompanying the KM 1.3 paper. The archival DOI and final
`SHA256SUMS` are intentionally absent until the manuscript, laptop-history
evidence, and independent-review dispositions are frozen. Their absence keeps
the submission audit fail-closed.

## Required deposit layout

- `paper/`: the submitted PDF, canonical LaTeX source, generated tables,
  bibliography, claims ledger, citation audit, and review dispositions.
- `source/kobayashi-marust-v1.3.0.tar.gz`: a `git archive` of the annotated
  `v1.3.0` tag. Its peeled commit must be
  `f4738bcdd980a1b2fcc840e4b455d37d447510cb`.
- `benchmarks/ore-2015/`: the 592-row release ledger, route evidence, retained
  reference provenance, and aggregate tables permitted for redistribution.
- `benchmarks/current-obo/current-obo-evidence-20260830.tar.gz`: the verified
  1,512-record evidence package. Its compressed SHA-256 must be
  `98e19518ccfd5a9a9b4321901f85a29e5baf16cdf2319514ef871f55656c5494`.
- `benchmarks/hard-cases/`: acquired named-hard-case records and explicit
  not-acquired receipts for credential-gated or licensed inputs.
- `certification/`: exact-v1.3 source-bound Lean gate summaries and logs.
- `process/`: version-control chronology, privacy-preserving agent-session
  ledger, frozen AgentsView reports, and their digest receipts. It excludes
  prompts, responses, commands, tool results, credentials, and unrelated
  sessions.
- `software/`: exact external baseline manifests and build instructions. Large
  third-party runtime artifacts may be referenced by digest and upstream URL
  when redistribution is not permitted.
- `SHA256SUMS`: a sorted digest manifest for every regular file in the deposit,
  excluding `SHA256SUMS` itself.

Restricted SNOMED CT content, API keys, private conversation bodies, machine
identifiers, build caches, and transient taxonomies must not enter the public
deposit. The BioPortal sample and SNOMED CT hard case were not acquired at the
evaluation cutoff; their absence is part of the reported scope rather than a
missing redistributable payload.

## Verification

From the extracted deposit root, run:

```sh
sha256sum -c SHA256SUMS
python3 paper/scripts/verify_formal_claims.py
python3 paper/scripts/verify_case_study_commits.py
python3 paper/scripts/verify_tagged_evidence.py
python3 paper/scripts/verify_citations.py
python3 paper/benchmark/verify_disagreement_witnesses.py \
  --ledger paper/benchmark/disagreement-evidence.tsv \
  --evidence-root paper/benchmark/generated/disagreement-evidence \
  --output /tmp/disagreement-witness-verification.json
make -C paper checks
```

The current-OBO evidence archive has its own internal `SHA256SUMS` and a
source-bound verification receipt in
`paper/benchmark/generated/current-final/evidence-archive-verification.json`.
The top-level digest manifest binds that nested archive without rewriting it.

## Reproduction boundaries

Rebuilding KM requires Rust and Lean versions pinned by the tagged source.
Re-running the complete benchmarks additionally requires Slurm, the listed
external reasoner artifacts, and the corpus inputs permitted by their
respective licences. The deposited result records and validators support
audit without asserting that every third-party ontology or executable may be
redistributed.
