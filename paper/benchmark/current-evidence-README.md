# Contemporary OBO benchmark evidence

This archive contains the evidence needed to audit the KM paper's frozen
2026-08-30 OBO comparison without redistributing the full corpus ontology payloads or
multi-gigabyte reasoner taxonomies.

Included material:

- the strict final aggregate, disagreement ledger, generated paper tables,
  and the SHA-256 manifest of all 1,512 terminal result records;
- all per-reasoner `*.result.json` records and available fingerprint receipts,
  compact node summaries, named-unsatisfiable lists, stderr, and GNU-time
  records;
- the OBO registry manifest, source/import receipts, independent profile
  reports, and verified Konclude-serialization receipts;
- exact baseline, execution-job, preparation, validation, postprocessing,
  finalization, incremental, and disagreement ledgers;
- small source-bound diagnostic modules and finite disagreement witnesses used
  to adjudicate individual taxonomy splits;
- the pinned benchmark runners, validators, aggregators, table renderers, and
  Slurm scripts; and
- execution, revalidation, finalization, recovery, and disagreement logs.

Excluded material:

- full frozen-corpus ontology payloads and import closures, which are
  identified by retrieval provenance and SHA-256 in the included receipts;
- generated taxonomy payloads, including the 5.4-GiB KM NCBitaxon JSON and
  781-MiB Konclude NCBitaxon OWL/XML files;
- Java runtime archives and native executables, whose exact versions and
  SHA-256 digests are retained in baseline manifests and result records;
- credentials, API keys, licensed SNOMED CT content, and private agent-session
  bodies.

The archive is a benchmark component, not the final single-file SWJ artifact.
The submission artifact additionally contains the exact KM v1.3.0 source,
Lean evidence, paper source/PDF, historical ORE evidence, AgentsView aggregate
telemetry, and this archive. Verify `SHA256SUMS` before inspection.
