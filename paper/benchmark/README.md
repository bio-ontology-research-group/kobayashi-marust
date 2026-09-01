# Expanded paper benchmark

This directory defines the evaluation that supplements the historical ORE 2015
panel in the KM v1.3 paper. No row may enter the manuscript until its corpus
artifact, reasoner artifact, command, limits, output, and correctness status are
recorded by digest.

## Evaluation strata

1. **ORE 2015 continuity.** Retain the 592-ontology experiment because it has
   dense historical route and correctness evidence. Describe it as a controlled
   regression and comparability panel, not as a current ontology sample.
2. **Current biomedical snapshot.** Freeze two independently identifiable
   sources on one date:
   - every active OBO Foundry entry with a resolvable public OWL product and an
     explicit redistribution licence;
   - a stratified BioPortal sample drawn from the latest submission of each
     downloadable public ontology, after content-digest deduplication against
     OBO and exclusion of restricted UMLS-derived artifacts.
3. **Named hard cases.** Report SNOMED CT, GALEN, FMA, NCIt, Uberon, and ChEBI
   separately. These rows remain visible even if a system times out, rejects the
   syntax, or exhausts memory.

The snapshot date is 2026-08-30. The downloaded OBO registry JSON-LD has
SHA-256 `b260d561378a666bc032c1a1e246c9f13a7997250f7e26cdc7aa8f64491407de`;
it contains 266 entries, including 190 marked active. The registry source is
`https://obofoundry.org/registry/ontologies.jsonld`.

## Corpus preparation

- Preserve the original download and HTTP provenance before transformation.
- Record final URL, retrieval time, declared version IRI, media type, byte size,
  SHA-256, licence, and registry identifier.
- Resolve imports into a deterministic merged document for the classification
  experiment. Retain the original unmerged source and a complete import ledger.
- Resolve each import closure once during corpus preparation and give every
  reasoner the same materialized axiom set. Functional Syntax is the canonical
  frozen representation. Konclude receives verified OWL/XML when its OWLAPI
  round trip preserves the logical axiom set, signature, and rule count;
  otherwise it receives the canonical Functional Syntax unchanged. Its tested
  CLI can silently produce an empty taxonomy from some valid Functional Syntax
  inputs, and a semantic pilot showed that it also accepts RDF/XML while
  loading no source classes. RDF/XML is therefore never selected. The format
  choice depends only on round-trip equivalence, not on classification output.
  `ConvertSyntax` records any OWLAPI alpha-renaming of rule variables. Missing
  imports or a failed round trip fail closed. Import retrieval, merge, and
  serialization time are preprocessing costs and are not included in
  classification time.
- Rewrite an inverse object-property expression that occurs inside a property
  chain to a deterministic fresh named role, and add an
  `InverseObjectProperties` definition for that role. This conservative
  extension preserves entailments over the original signature and is applied
  once to the common document supplied to every reasoner. Receipts record the
  normalization version, replacement count, and resulting digest.
- Reject a corpus entry if retrieval returns HTML, an authentication response,
  or a zero-byte placeholder. Redirect success is not download success.
- Deduplicate only by SHA-256 of the original source. Different releases or
  distinct ontologies with overlapping axioms remain distinct.
- Profile each merged ontology before running reasoners, but do not use the
  profile to remove hard inputs.

`runners/owlapi/FreezeImports.java` materialises the common import closure.
`runners/owlapi/ConvertSyntax.java` produces and validates the Konclude input
view; `ibex_convert_verified_xml.sbatch` creates one source-bound receipt per
ontology.
`runners/owlapi/ProfileOntology.java` independently checks OWL~2, DL, EL, QL,
and RL membership and records violation types, signature sizes, and the exact
merged-input digest.  `ibex_profile_obo.sbatch` runs this check only after the
import-freezing array succeeds and resumes a row only when its recorded digest
still matches the frozen input.

The completed OBO freeze contains 189 eligible normalized receipts.  Forty-one
ontologies required inverse-chain normalization, with 124 replaced chain
members in total.  The remaining active registry entry, OGG, is retained as an
explicit `source_unavailable` row because its registered product resolves to a
404 response. Independent profiling places 188 inputs in OWL 2, 160 in OWL 2
DL, 44 in EL, 20 in QL, and 15 in RL; profile sets overlap. The archived
receipts and summaries are under `generated/import-receipts/`,
`generated/profiles/`, `generated/obo-import-summary.json`, and
`generated/obo-profile-summary.json`.

BioPortal requires a user API key for programmatic submission downloads. The
key must be supplied to the acquisition process through an environment variable
and must never be written to a manifest or log. SNOMED CT is licence restricted;
its International Edition OWL/RF2 release must be supplied separately. Missing
credentials or licensed files produce an explicit `not_acquired` corpus row,
not a replacement ontology.

`acquire_bioportal_snapshot.py` implements the dated candidate freeze. It
enumerates submissions released no later than the cutoff, selects the latest
OWL submission, downloads the submission-specific artifact, rejects views,
summary records, restricted UMLS products, authentication payloads, and source
duplicates, and retains every exclusion in the manifest. Licence inclusion is
an explicit human-reviewed TSV decision; missing decisions fail closed. Source
payloads stream to temporary files, and resume requires a terminal receipt
whose submission identifier, endpoint, byte count, and SHA-256 still match.
Run it without exposing the key in process arguments or logs:

```bash
BIOPORTAL_API_KEY="${BIOPORTAL_API_KEY:?}" \
python3 acquire_bioportal_snapshot.py \
  --snapshot-date 2026-08-30 \
  --obo-manifest generated/obo-freeze-20260830.tsv \
  --license-decisions bioportal-license-decisions.tsv \
  --output-root generated/bioportal-snapshot
```

The BioPortal sample is selected before any reasoner run. Its candidate
universe is the latest downloadable public OWL submission for each ontology at
the snapshot timestamp. Ontology views, summary-only entries, restricted
UMLS-derived products, payloads without analysable licence terms, failed
downloads, and source-digest duplicates of the frozen OBO collection are kept
in the manifest with exclusion reasons. Every remaining payload is import
frozen and independently profiled. Candidates are partitioned by the same four
logical-axiom size bins used for RQ5 (`<1k`, `1k--9,999`, `10k--99,999`, and
`>=100k`) and by `OWL 2 EL`, `OWL 2 DL but non-EL`, and `outside OWL 2 DL`.
Each of the resulting 12 cells contributes all candidates when it contains at
most ten, otherwise the ten smallest SHA-256 rankings of the length-framed tuple
`(km-bioportal-20260830-v1, acronym, submission-id, source-sha256)`.
The planned panel therefore contains at most 120 BioPortal inputs, is deterministic,
and cannot be adjusted after observing reasoner performance. GALEN remains a
named hard case even if it is not selected by this panel rule.

## Baselines

[`baselines.tsv`](baselines.tsv) is binding. The required general-purpose
baselines are Konclude, HermiT, JFact, Openllet, and MORe. ELK is the established
OWL EL baseline. Whelk is included as a newer EL+RL system based on ELK's
algorithm, with a published artifact and explicit software version; it is not
treated as a full OWL 2 DL competitor. Each Java reasoner runs in its own
dependency environment so that legacy OWLAPI requirements cannot alter another
baseline.

MORe is retained because modular EL/full-DL routing is directly relevant to KM.
Its final public source depends on OWLAPI 3.4.10, HermiT 1.3.8.4, ELK 0.4.2, and
a bundled JRDFox artifact. The paper will report that historical software stack
and any build or runtime incompatibility. It will not silently substitute a
modern ELK+HermiT portfolio and label it MORe.

## Runtime contract

- Named-class classification and consistency are measured separately.
- Default primary limit: 600 seconds and 32 GiB summed process-tree RSS per
  ontology/reasoner pair. ORE continuity retains its original 240-second,
  20-GiB contract and is reported in a separate table.
- One exclusive Intel Xeon Gold 6248 node allocation, 16 CPUs, one task per
  ontology/reasoner pair. JVM heap limits leave headroom for non-heap and child
  processes inside the process-tree cap.
- Record wall time, CPU time where available, peak process-tree RSS, exit code,
  consistency, taxonomy cardinality, full-IRI signature, stderr digest, runtime
  digest, and exact command.
- A result is successful only when the runner observes reasoner invocation,
  nonempty terminal metadata, complete output parsing, and a checkpoint
  identical to the result record. Resume only absent or invalid indexes.

The isolated Java path is implemented by `runners/run_java_one.py`; KM and
Konclude use `runners/run_native_one.py`.  Both wrap the reasoner with GNU
`time`, monitor the full descendant process tree, publish a result atomically,
and fingerprint output after the timed classification.  The fingerprint stores
both a semantic digest including consistency and a relation-only digest.  The
latter permits a taxonomy comparison with MORe, whose public API does not
implement consistency checking.  `runners/validate_result.py` rejects stale,
partial, zero-memory, wrong-input, wrong-runtime, wrong-runner, and
output/fingerprint-inconsistent records before either resume or aggregation.
Both full-array scripts pin this validator by SHA-256 before reading or writing
a result. This prevents tasks in one array from observing different validator
versions if deployment state changes while the array is active.
For Konclude it additionally requires the returned taxonomy to declare every
named source class. This gate was added after a zero-exit Functional Syntax
load failure produced a syntactically valid but empty taxonomy; such output can
never again satisfy resume or aggregation validation.

The first Java full array began before this validator pin was deployed.  Its
live validator changed while tasks were active; 165 tasks retained successful
terminal validation, while other tasks encountered an incorrect requirement
for a redundant native-only `input_ontology_sha256` field.  The runner
had already atomically checkpointed the complete result and output before this
post-run validation, so the error did not alter measurements or taxonomies.
The corrected validator requires that field only for KM and Konclude while
retaining source, runtime, runner, command, stderr, checkpoint, and output
bindings for Java reasoners.  Read-only job 51033128 revalidated all 378 HermiT
and JFact records with zero errors.  The remaining Java records are subject to
the same revalidation after their original array drains.  Exact hashes and logs
are recorded in `validation-artifacts.tsv`.

Read-only job 51035710 is dependency-gated on completion of Java array
51021831 and applies the fixed validator independently to all 1,134 Java
records.  Finalization job 51036367 runs only if every revalidation task
succeeds.  It executes `ibex_aggregate_current_final.sbatch`, whose digest and
role are recorded in `finalization-jobs.tsv`, without `--allow-incomplete`;
requires exactly 1,512 result records; renders the manuscript tables; and
writes a SHA-256 manifest covering every result record.  Scheduler completion
by itself is therefore insufficient to publish the panel: the log must end in
`CURRENT_FINAL_OK\t1512` and all generated digests must verify.

Evidence-packaging job 51037319 is in turn dependency-gated on successful
finalization. It creates a deterministic compressed archive containing all
1,512 terminal records, fingerprint receipts, corpus profiles and provenance,
diagnostics, exact scripts, and validation logs. It fails if a taxonomy
payload, ontology source, runtime archive, executable, or credential-like
input enters its explicit file list. `current-evidence-README.md` documents
the inclusion and exclusion boundary. This component will be embedded in the
single immutable submission artifact after its own digest is verified.

KM's NCBitaxon run produced a valid 5.4-GiB JSON taxonomy, but the original
whole-document Python fingerprinter exhausted the 36-GiB job allocation after
classification. `runners/fingerprint_km_json_sparse.py` parses that JSON with a
bounded buffer, interns the graph into compact integer arrays, reconstructs SCCs
and sparse transitive closure, and emits the same digest framing. Before use it
matched the legacy fingerprinter's consistency, counts, taxonomy digest, and
relation digest on all 96 current KM outputs for which the legacy path had
completed, including UO, whose published JSON required 23 inferred transitive
pairs. Job 51031093 then fingerprinted NCBitaxon in 248.08 seconds with 2.36 GiB
peak RSS. `recover_km_fingerprint.py` accepted only the unchanged output and
source digests, bound both postprocessors and their Slurm jobs, copied receipts
atomically, and preserved the original 92.09-second, 7.37-GiB classification
measurement (7,373.73 MiB, or 7.20 GiB). The complete provenance is in
`postprocessing-artifacts.tsv`.

Konclude independently completed NCBitaxon in 186.04 seconds with
12,764.51 MiB peak RSS and emitted a 781-MiB OWL/XML taxonomy.  Its legacy
whole-document fingerprint process exceeded the postprocessing allocation.
The sparse implementation was therefore extended with a streaming OWL/XML
frontend and differentially checked against all 160 accepted legacy Konclude
fingerprints; all matched exactly, while 29 non-success rows were explicit
skips.  Job 51032807 reconstructed 55,757,044 subsumptions in 96.65 seconds at
1,845.66 MiB and found no missing source declaration.  Its taxonomy and
relation digests equal KM's NCBitaxon digests.  Job 51032926 preserved the
pre-recovery failure record, atomically attached the sparse receipts, retained
the original Konclude reasoner measurements, and passed strict validation.

`ibex_java_pilot.sbatch` and `ibex_native_pilot.sbatch` exercise two real OBO
ontologies before the full arrays.  `ibex_validate_pilots.sbatch` checks all 16
pilot tuples and requires eight-way relation consensus on ADO.  The full arrays
are dependency-gated on that validation, completion of the independent profile
sweep, and the 189 source-bound serialization receipts required by Konclude.
`aggregate_current.py` reports relation-only taxonomy consensus
across KM, Konclude, HermiT, JFact, Openllet, and MORe, and separately reports
consistency consensus among the five systems whose tested interfaces expose
that service.  It never turns a majority into an undeclared gold answer.
Run `python3 -m unittest discover -s tests -v` from this directory before
aggregation; the regression fixture checks that MORe participates in relation
consensus but cannot silently enter consistency consensus as an `unknown`
answer. Final aggregation fails if any expected tuple is missing or invalid.
It also requires `execution-jobs.tsv`: every record must carry the exact runner
digest and an explicitly allowed owning Slurm array ID. A resumed array is
added to that ledger only when it uses the same corpus and reasoner artifacts;
this prevents an otherwise well-formed stale result from entering the paper.

After archiving the complete result and conversion-receipt trees, regenerate
the current-corpus evidence with:

```bash
python3 summarize_serializations.py \
  --manifest generated/obo-freeze-20260830.tsv \
  --import-receipts generated/import-receipts \
  --serialization-receipts generated/verified-xml-receipts \
  --preparation-artifacts preparation-artifacts.tsv \
  --output generated/serialization-summary.json \
  --output-tex generated/serialization-summary.tex
python3 aggregate_current.py \
  --manifest generated/obo-freeze-20260830.tsv \
  --baselines baselines.tsv \
  --execution-jobs execution-jobs.tsv \
  --preparation-artifacts preparation-artifacts.tsv \
  --receipts generated/import-receipts \
  --serialization-receipts generated/verified-xml-receipts \
  --profiles generated/profiles \
  --results generated/current-results \
  --output-json generated/current-aggregate.json \
  --disagreements-tsv generated/current-disagreements.tsv
python3 render_current_tables.py \
  --aggregate generated/current-aggregate.json \
  --output ../generated/current-results.tex
python3 summarize_terminal_causes.py \
  --results generated/current-results/km \
  --profiles generated/profiles \
  --manifest generated/obo-freeze-20260830.tsv \
  --array-job-id 51028377 \
  --output-tsv generated/km-terminal-causes.tsv \
  --output-json generated/km-terminal-cause-summary.json
```
`--allow-incomplete` exists only for explicitly labelled progress diagnostics.
After a complete aggregate, `render_current_tables.py` generates the own-
completion and pairwise-agreement LaTeX tables directly from the bound JSON.
It additionally reports fixed logical-axiom size strata (`<1k`, `1k--10k`,
`10k--100k`, and `>=100k`) and independent EL, DL-non-EL, and outside-DL
strata. It also emits an explicit NCIt/Uberon/ChEBI hard-case table with every
reasoner's terminal status and the expressive-system relation-consensus
groups. The generated file records the aggregate digest.
`summarize_terminal_causes.py` separately binds every KM terminal category to
the exact stderr digest and independent profile. It fails unless all 189
records belong to the declared array job; `--allow-incomplete` is diagnostic
only and cannot generate final manuscript evidence.

## Exact-v1.3 incremental scale check

`incremental_v13_benchmark.py` benchmarks one addition-only EL transaction and
one ordering-stable CB transaction against fresh classification of the same
union.  The input shapes and sizes were inherited from the release
microbenchmarks rather than selected after observing v1.3 timings.  The driver
uses one warmup and ten measured repetitions, asserts the expected delta
strategy and nonzero fixpoint reuse, and compares every complete taxonomy with
the fresh worker result.  GNU `time` records process peak RSS.  The retained
session peak includes initialization and update; fresh peak covers the new
union worker.

IBEX job `51036603` ran the exact OBO benchmark binary
`cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d`
on one exclusive Intel Xeon Gold 6248 core.  The job and driver hashes are in
`incremental-jobs.tsv`; raw rows, the source-bound receipt, and the terminal
log are under `generated/incremental-v13/`.  Regenerate the manuscript table
and verify all pinned evidence with:

```bash
python3 render_incremental_v13.py
```

Fresh timing includes process startup, JSON parsing, classification, and
serialization, while retained-add timing measures one request in an existing
session.  The ratio is therefore an end-to-end API scale check, not an isolated
saturation speedup or a representative ontology-update workload.

## Correctness

No single baseline is the oracle for the new corpus. For each ontology:

1. compare full-IRI named-class relations from all completing expressive
   reasoners, including MORe;
2. report consensus groups rather than majority truth;
3. use EL reasoners as complete references only when an independent profile
   proves the merged source is in their supported complete fragment;
4. retain non-OWL-2-DL inputs as acceptance and fail-closed-behaviour rows, but
   exclude them from complete-DL correctness claims;
5. adjudicate disagreements with reduced witnesses, satisfiability checks, or
   proof/certificate evidence; and
6. leave unresolved disagreements marked `contested` and exclude them from
   correctness-conditioned speed claims.

`verify_disagreement_witnesses.py` replays the finite DOID, CVDO, and KISAO
source witnesses independently of an OWL reasoner. `compare_taxonomy_tsv.py` performs
a streaming merge difference over sorted full-IRI Java taxonomy rows and
fails on malformed, duplicate, or unsorted input. The source-bound diagnostic
jobs and their dispositions are recorded in `disagreement-jobs.tsv`; these
diagnostics never replace benchmark measurements or promote a majority to
gold.

The headline analysis reports coverage, all-attempt resource distributions,
correct-completion aggregates, pairwise shared-correct comparisons, and the
complete named-hard-case matrix. It reports geometric means or performance
profiles only on explicitly named shared populations.
