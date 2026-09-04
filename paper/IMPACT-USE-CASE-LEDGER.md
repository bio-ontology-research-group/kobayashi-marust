# KM impact-use-case audit and experiment extension

Status date: 2026-09-04. The established evidence states and claim boundary
remain in [`impact/ledger.tsv`](impact/ledger.tsv); this companion audits and
extends that baseline rather than replacing it. It is an experiment plan, not
a novelty claim. The machine-readable, scheduler-facing form is
[`IMPACT-USE-CASE-MANIFEST.tsv`](IMPACT-USE-CASE-MANIFEST.tsv). That TSV is
binding for proposed execution details when a detail here is abbreviated, but
it does not override the established-evidence ledger.

## Claim boundary

OWL 2 EL is a syntactic subset of OWL 2 designed for polynomial-time standard
reasoning tasks on very large class and property vocabularies. It supports
existential restrictions but excludes constructs needed by several tests in
this ledger, including general complement, universal restriction, disjunction,
inverse properties, and cardinality restrictions. These are language facts,
not KM results ([W3C OWL 2 Profiles](https://www.w3.org/TR/owl2-profiles/)).

A terminating complete OWL 2 DL classifier can answer a stronger question than
an EL classifier on an out-of-profile input: what follows from the ontology as
published, rather than from an unreported subset or unsupported execution.
That stronger question enables full-source release gates, full-source merge
checks, and controlled model challenges. It does not make all such workloads
tractable, identify which conflicting axiom is scientifically wrong, or turn an
EL result on an out-of-profile ontology into correctness evidence.

Nothing here claims that consistency checking, incoherence detection, or OWL
DL explanations are new. For example, earlier FMA work used DL reasoners to
find unsatisfiable classes and explicitly described consistency checking as an
advantage of the DL representation
([Golbreich et al.](https://pmc.ncbi.nlm.nih.gov/articles/PMC4349213/)). The
paper may claim only the scale, coverage, resource result, or experiment that
its immutable artifacts directly establish.

The current evidence also does **not** establish a natural-ontology scientific
task that KM alone makes possible among all tested complete reasoners. Konclude
also solves the historical GALEN input; HermiT, Konclude, and MORe share KM's
full relation on frozen NCIt and ChEBI; Konclude, not the tagged v1.3 KM
artifact, is the only expressive completion in the copied FMA sweep; and no
expressive system completed frozen current Uberon's taxonomy in the copied
paper matrix. Guarded KM now directly establishes consistency for that Uberon
input, but no independent complete reasoner result or full taxonomy accompanies
it. What is already demonstrated is the semantic mechanism on controlled cases,
KM's ability to classify one large expressive GALEN artifact, and this separate
consistency-only Uberon result. A claim of new
practical enablement requires a completed natural full-DL task, a same-source
EL differential with a nonzero independently checked effect, and a comparator
failure or material resource boundary. The experiments below are designed to
produce or falsify exactly that evidence.

## Evidence states

- `verified existing` means immutable inputs, commands, outputs, and checks are
  already copied under `paper/impact/evidence/` and pass the fail-closed
  validator.
- `verified consistency only` means a hash-bound direct consistency operation
  completed, while coherence and named-class taxonomy remain unestablished.
- `verified base; proposed differential` means the full ontology result is
  established in the current paper benchmark, but the full-versus-EL
  experiment has not run.
- `proposed` means the hypothesis and acceptance gate are predeclared, with no
  result claimed.
- `verified failure` records a correctly bound non-result. It is not evidence
  that the queried consequence is absent.
- `blocked` means a licence, credential, source, or version gate prevents a
  reproducible run.

The existing compact artifact demonstrates three controlled conflict/control
pairs and the ORE 2015 GALEN classification. It records failed full-Uberon
taxonomy runs and the newer, separate guarded Uberon consistency result. The
detailed boundary is in [`impact/README.md`](impact/README.md) and
[`impact/ledger.tsv`](impact/ledger.tsv). A live taxonomy job does not change a
paper evidence state until its terminal output and receipt are imported and
validated.

## Common full-versus-EL protocol

The natural-ontology experiments use one protocol so that “EL projection” has
an exact meaning.

1. Start from the already import-frozen Functional Syntax document and verify
   its expected SHA-256. Never redownload a moving PURL inside a reasoner job.
2. Run OWLAPI's independent profile checker and retain all violation classes.
3. Run `org.kmbenchmark.MakeELProjection`. It removes each *whole source
   axiom* to which OWLAPI attaches an EL-profile violation, repeats until the
   output passes `OWL2EL=true`, and records input, output, removed-axiom, and
   tool digests. It does not rewrite an unsupported class expression into a
   weaker expression.
4. Classify the full document with the exact KM candidate twice. Classify the
   EL-drop document with KM and ELK 0.6.0. Canonicalize all results as sorted
   full-IRI named-class relations and named-unsatisfiable sets.
5. Require exact KM/ELK agreement on the EL input. If the full ontology is
   consistent, require every projection consequence over the common named
   signature to occur in the full result. A violation of this subset relation
   indicates an implementation, completeness, input, or comparison error, not
   an interesting scientific result.
6. For each reported full-only unsatisfiable class and for a deterministic
   sample of full-only subsumptions, extract a STAR locality module over the
   involved signature and check it with HermiT, JFact, or Konclude. Also retain
   a bounded source-axiom support when KM can produce one. Record failures and
   disagreement; do not promote majority vote to gold.

This generated EL-drop ontology is an axiom-deletion control. It is not the
same object as an ontology project's hand-engineered “basic,” “simple,” “core,”
or “lite” distribution. Uberon, for example, describes `uberon/basic` as a
logic subset that retains only selected relationship types
([Uberon downloads](https://uberon.github.io/downloads.html)); ChEBI's FULL,
CORE, and LITE variants differ in included information
([ChEBI downloads](https://www.ebi.ac.uk/chebi/downloads)). Those official
variants can be secondary comparisons but cannot replace the same-input
projection.

## Ledger summary

| ID | Domain | State | Outcome currently supportable |
|---|---|---|---|
| BIO-UBERON-CONSISTENCY-GUARDED | anatomy | verified consistency only | `consistent=true`, 4.46 s, 157,544 KiB; no taxonomy |
| BIO-UBERON-FULL-EL | anatomy | running externally; not established | Consistency is established separately; full taxonomy and full-versus-EL effect remain unknown |
| BIO-UBERON-FMA-BRIDGE | anatomy integration | proposed, source gate | No merged result |
| BIO-GALEN-ORE-FULL | clinical terminology | verified existing | Two identical KM full classifications; historical Konclude equality |
| BIO-GALEN-FULL-EL | clinical terminology | proposed differential | Full taxonomy exists; EL delta unknown |
| BIO-GALEN-BIOPORTAL | clinical terminology | blocked | Metadata only; payload not acquired |
| BIO-FMA-FULL-EL | anatomy | proposed; v1.3 KM failed | Konclude full result exists; current KM and EL delta unknown |
| BIO-NCIT-FULL-EL | cancer terminology | verified base; proposed differential | Four expressive systems agree on full base; EL delta unknown |
| BIO-NCIT-NEGATION-QC | cancer terminology | proposed, source gate | Official QC-product hypothesis only |
| BIO-CHEBI-FULL-EL | chemistry | verified base; proposed differential | Four expressive systems agree; one-violation null-control hypothesis |
| BIO-SNOMED-SYNTH | clinical terminology design | verified existing | Synthetic full-DL inconsistency distinguished from control |
| BIO-SNOMED-LICENSED | clinical terminology | blocked | No SNOMED CT content acquired or tested |
| BIO-UNMIREOT-2018 | ontology interoperability | blocked exact replication | Published EL results only; no KM corpus rerun |
| BIO-UNMIREOT-2026 | ontology interoperability | proposed new-data study | Frozen inputs exist; merge experiment not run |
| BIO-MERGE-CONTROL | ontology interoperability | verified existing | Synthetic full-DL incoherence distinguished from control |
| NONBIO-ACCESS-CONTROL | access policy | verified existing | Synthetic full-DL policy incoherence distinguished from control |
| NONBIO-PRODUCT-CONFIG | engineering configuration | proposed exact pair | Direct-semantics expectation only |
| NONBIO-FIBO-IDENTITY | finance/data quality | proposed public-ontology pair | Direct-semantics expectation; FIBO closure not frozen here |

## Biomedical cases

### BIO-UBERON-CONSISTENCY-GUARDED: consistency without taxonomy

- **Ontology/version/source:** the same normalized Uberon input described in
  the next row, SHA-256
  `13579e2a9760969bb07beaf4701d019a90c5f63556bd593685ed876c44a8aa93`.
  A hash-bound diagnostic wrapper captured internal TInput SHA-256
  `01dca21c579745be5e8e5eca9d8b752d7811070a69475f73441b9150ae0853c6`.
- **DL features:** inherited from the complete normalized input, which has
  4,247 OWLAPI EL-profile violations. The direct operation consumed KM's
  internal TInput rather than reparsing or projecting the ontology.
- **Question and query:** does the frozen full input have a model under the
  guarded KM consistency procedure? Run `km tableau` with
  `KM_RULES_CONSISTENCY=1`, `KM_TAB_CAREFUL_INC=1`,
  `KM_TAB_CAREFUL_ORDER=1`, and `KM_TAB_CAREFUL_LAZY=1` over the captured
  TInput. The exact command and Slurm script are copied with the evidence.
- **Observed result:** demonstrated. Guarded KM directly returned
  `consistent=true` in 4.46 s at 157,544 KiB peak RSS. The binary SHA-256 is
  `c9be93d3c3c0701a175658c8ba935db0a29df420493e8ed7c1b32f85f5eb2805`.
- **Oracle and limits:** the receipt binds binary, TInput, output, host, and job;
  the capture receipt and scripts bind the TInput to the normalized source.
  There is no independent complete-reasoner agreement for this input. This
  consistency-only execution does not classify named classes. Its empty
  `unsatisfiable` and `subsumptions` arrays are schema fields, not evidence of
  zero unsatisfiable classes or zero relations.
- **Evidence:** `impact/evidence/receipts/uberon-guarded-consistency.receipt.tsv`,
  `impact/evidence/outputs/uberon-guarded-consistency.output.json`, and the
  capture/build receipts and scripts listed in manifest row
  `BIO-UBERON-CONSISTENCY-GUARDED`.

### BIO-UBERON-FULL-EL: full current Uberon versus a same-source EL view

- **Ontology/version/source:** the paper's frozen `uberon.owl`, VersionIRI
  `2026-06-19`, source SHA-256
  `938f51e7c3fc9fcbe5a2863eb346da8033737e568af5836958891c4c6bfb1192`,
  import-frozen and inverse-chain-normalized SHA-256
  `13579e2a9760969bb07beaf4701d019a90c5f63556bd593685ed876c44a8aa93`.
  Uberon publishes versioned releases and distinguishes core, extended,
  taxonomic, system, and logic subsets
  ([official downloads](https://uberon.github.io/downloads.html)).
- **DL features:** the copied OWLAPI profile records 4,247 EL violations: 4,115
  illegal class expressions, 72 illegal axioms, 57 property-chain/range
  restrictions, and three multi-individual nominals.
- **Question:** what named subsumptions, unsatisfiable classes, or consistency
  results depend on the full source rather than the EL-drop axiom subset?
- **Transformation/query:** use the common protocol on the exact normalized
  source. Separately record the official `uberon/basic` relation only as a
  project-defined subset, never as the generated EL projection.
- **Expected observation:** hypothesis. KM and ELK must agree on the generated
  EL ontology. The full taxonomy, if obtained, must contain that taxonomy over
  the common signature. The size of the full-only delta may be zero.
- **Comparators and KM command:** current exact KM twice; ELK on the verified EL
  view; high-resource Konclude on full; module-level HermiT/JFact checks. Exact
  command, limits, and paths are in manifest row `BIO-UBERON-FULL-EL`.
- **Oracle:** repeat identity, EL cross-reasoner identity, monotonic subset
  check, complete-reasoner modules, and source supports. A consistency-only
  precheck is not a classification oracle.
- **Risks/confounders:** the copied post-v1.3 impact evidence has two automatic
  errors and two one-hour route timeouts. Full taxonomy job 51320320 was still
  running at the 2026-09-04 audit and is not yet established. The separate
  guarded consistency result does not change that taxonomy state. Axiom
  deletion can remove much more structure than the official basic subset.

### BIO-UBERON-FMA-BRIDGE: cross-anatomy integration

- **Ontology/version/source:** the two frozen versions above and FMA 5.1.0,
  plus the release-matched official `uberon-bridge-to-fma.owl`. Uberon lists
  the bridge as an official anatomical bridging ontology
  ([official downloads](https://uberon.github.io/downloads.html)).
- **DL features:** inherited full-DL constructs in both ontologies and bridge
  equivalences; exact feature attribution must follow profiling of the union.
- **Question:** does the bridge preserve joint consistency and coherence, and
  which cross-namespace relations disappear under EL axiom deletion?
- **Transformation/query:** freeze all three closures independently, union
  their axioms with `MergeOntologies`, classify, generate the EL-drop control,
  and stratify relation deltas by FMA-to-Uberon, Uberon-to-FMA, and internal
  edges.
- **Expected observation:** no direction is assumed. A contradiction is a
  candidate integration conflict, not evidence that either source is wrong.
- **Comparators/command/oracle:** KM and Konclude on full; KM and ELK on the EL
  view; modules and explanations for every unsatisfiable class. See the
  manifest for the command and acceptance gate.
- **Risks/confounders:** the exact matching bridge is not yet frozen. Many-to-one
  mappings may be intentional, and source-version skew can manufacture a
  conflict. This row must not run before its source gate passes.

### BIO-GALEN-ORE-FULL and BIO-GALEN-FULL-EL

- **Ontology/version/source:** ORE 2015 `ore_ont_9724.owl`, SHA-256
  `00c80e07aa57578c168d15a1755b62fde41c53dd69a2f04cc5d88c888c8baf19`.
  It contains GALEN IRIs and is not the BioPortal submission.
- **DL features:** SHIF, including inverse roles and universal restrictions,
  with functional/cardinality structure outside EL.
- **Question:** can the full historical artifact be classified reproducibly,
  and which of its named consequences need non-EL axioms?
- **Transformation/query:** the full run is identity. The proposed differential
  applies the common EL-drop protocol.
- **Expected/observed:** demonstrated full result: two KM runs report
  consistency, no named-unsatisfiable classes, and 457,090 subsumptions with
  identical semantic digests. Historical KM and Konclude canonical relations
  match. The EL delta is unmeasured.
- **Comparators/command/oracle:** existing exact KM repeats and historical
  Konclude for full; add KM and ELK on projection and enforce the subset gate.
- **Risks/confounders:** no result about a current GALEN release follows. The
  NCBO page describes its only public submission as GALEN 1.1, released
  2007-01-09 and uploaded 2007-01-16
  ([BioPortal GALEN](https://bioportal.bioontology.org/ontologies/GALEN)).

### BIO-GALEN-BIOPORTAL: independently frozen public submission

- **Ontology/version/source:** BioPortal GALEN v1.1 metadata as above; payload,
  checksum, and licence decision remain missing.
- **DL features/question:** independently profile the acquired payload, then ask
  whether its structure and full taxonomy match the ORE file.
- **Transformation/query:** credentialed acquisition by submission identifier,
  import freeze, source/profile receipts, full classification, and a structural
  comparison to `ore_ont_9724`.
- **Expected observation:** unknown. Never substitute the ORE result.
- **Comparators/command/oracle:** full eight-reasoner panel where applicable;
  exact command is predeclared in the manifest.
- **Risk/status:** blocked on API access and licence review. Calling this a
  “current GALEN” test would be misleading because the available submission is
  from 2007.

### BIO-FMA-FULL-EL: expressive anatomy and a strong complete oracle

- **Ontology/version/source:** FMA 5.1.0, source SHA-256
  `beb3dc47979ad5434ef70fd02af4307f147f2023f7d8c2c57103b995191194c3`,
  frozen merge SHA-256
  `aff1dfb7cdcd153ce6fb2f0e4899e29f60a7eec04940a48acbef7e9bd3fb4bb6`.
  The OBO record points to the official FMA OWL and warns that its older
  is-a/part-of/has-part OBO translation is deprecated
  ([OBO FMA](https://obofoundry.org/ontology/fma.html)).
- **DL features:** independently OWL 2 DL and outside EL, QL, and RL. The exact
  violation-class receipt needs copying before feature-level interpretation.
- **Question:** can the current KM candidate classify the full model, and what
  hierarchy or coherence information is absent from the generated EL view?
- **Transformation/query:** full identity plus common EL-drop protocol.
- **Expected/observed:** Konclude already completed in 24.334 seconds at
  5,625.9 MiB and published 371,358 subsumptions under the paper contract. The
  v1.3 KM artifact memout is also verified. Current KM success and EL delta are
  hypotheses.
- **Comparators/command/oracle:** Konclude is the full-output oracle; KM and ELK
  compare on projection. Exact commands and larger current-KM limits are in the
  manifest.
- **Risks/confounders:** old FMA papers, FMA-Lite, and the deprecated OBO
  translation are different inputs. Do not transfer their results to 5.1.0.

### BIO-NCIT-FULL-EL and BIO-NCIT-NEGATION-QC

- **Ontology/version/source:** NCIt OBO Edition VersionIRI `2026-03-19`, source
  SHA-256
  `1f89a02063ff807183dcdc8eac43ef88f65d5eb525cc88709ee8c57fa5f9e780`,
  frozen merge SHA-256
  `2bd711eaf0f0df861ec417fe263aa2d492130f6be3fe05218ab6ff3e712b5ce6`.
- **DL features:** 179 EL violations: 142 illegal class expressions, 19 illegal
  data ranges, and 18 multi-literal data enumerations. The project's separate
  `ncit-negations.owl` product turns excludes properties into logical
  negations and is documented as yielding some unsatisfiable classes
  ([NCIt OBO Edition downloads](https://github-wiki-see.page/m/NCI-Thesaurus/thesaurus-obo-edition/wiki/Downloads)).
- **Question:** do the frozen base's non-EL axioms alter named classification,
  and can the release-matched negation QC product expose additional
  incoherence?
- **Transformation/query:** common full-versus-EL protocol for base. For the QC
  arm, first acquire a negation product from exactly the same release lineage,
  freeze it, and compare new unsatisfiable classes against base and EL view.
- **Expected/observed:** on base, KM, HermiT, Konclude, and MORe already agree
  on consistency and one relation digest. Both differential effects are
  unknown. Project documentation's “some unsatisfiable classes” is not a KM
  result or count.
- **Comparators/command/oracle:** four-way base result, KM/ELK projection,
  and two complete systems plus explanations for each QC unsatisfiability.
- **Risks/confounders:** the public GitHub release assets visible in the source
  audit are older than the frozen 2026-03-19 base. A moving PURL or older
  negation product must not be silently mixed into this experiment.

### BIO-CHEBI-FULL-EL: a required null control

- **Ontology/version/source:** ChEBI VersionIRI 254, source SHA-256
  `4557df5b668394b371e6e75158ec9f7728424852ffdaa2e6a6975cfc31e461ba`,
  frozen merge SHA-256
  `ecac31adf0df48020379d85f7c8f9aefc76eb10981d23b2e0d79c8e8d3dd86d6`.
- **DL features:** one OWLAPI `UseOfIllegalAxiom` EL-profile violation.
- **Question:** does that one axiom change any named consequence?
- **Transformation/query:** common protocol, plus retain the exact removed axiom
  rendering and digest.
- **Expected/observed:** KM, HermiT, Konclude, and MORe already agree on full
  consistency and relation digest. Zero full-only delta is the useful null
  hypothesis; a positive delta must be independently checked.
- **Comparators/command/oracle:** existing four-way full agreement; KM and ELK
  on EL projection; streaming/sparse fingerprints for large outputs.
- **Risks/confounders:** a syntactic profile violation does not imply semantic
  impact. ChEBI FULL is not interchangeable with CORE or LITE. ChEBI documents
  all three as distinct distributions
  ([EMBL-EBI downloads](https://www.ebi.ac.uk/chebi/downloads)).

### BIO-SNOMED-SYNTH and BIO-SNOMED-LICENSED

- **Ontology/version/source:** the verified synthetic pair has no SNOMED CT
  content. The real row requires a user-authorized International Edition OWL
  refset or a pinned RF2-to-OWL conversion. SNOMED International states that
  its OWL reference sets distribute the axioms representing formal concept
  definitions
  ([SNOMED CT OWL Reference Set specification](https://docs.snomed.org/snomed-ct-specifications/snomed-ct-owl-reference-set-specification)).
- **DL features:** the synthetic conflict combines two existential laterality
  fillers, disjointness, maximum cardinality one, and an ABox instance. The
  licensed experiment must pre-register one domain-reviewed non-EL axiom.
- **Question:** can a candidate modeling constraint make a concept incoherent,
  and can instantiating that concept make data inconsistent while EL remains
  blind to the decisive constraint?
- **Transformation/query:** synthetic conflict differs from control only by
  the maximum-cardinality axiom. For licensed data, make immutable base,
  no-op-control, and one-axiom-conflict variants over reviewed live concept IDs.
- **Expected/observed:** demonstrated synthetic result: KM and HermiT report the
  conflict ontology inconsistent and the control consistent; ELK's
  out-of-profile runs do not distinguish them. No real SNOMED outcome is known.
- **Comparators/command/oracle:** exact commands in the manifest; real experiment
  requires domain review, two complete reasoners or independently checked
  modules, and source supports.
- **Risks/confounders:** licence restrictions, concept inactivation, conversion
  semantics, OWL's open-world semantics, and absence of a unique-name
  assumption. Never describe the synthetic example as a SNOMED defect.

### BIO-UNMIREOT-2018 and BIO-UNMIREOT-2026

The 2020 study combined nine OBO Foundry ontologies and reported at least 636
unsatisfiable classes. It then combined a repaired Foundry merge with the wider
2018 OBO collection, reporting 866,494 unsatisfiable occurrences, 312,398
distinct unsatisfiable classes, and 117 removed axioms. Its ELK 0.5.0-SNAPSHOT
oracle lacks negation and universal restriction; the authors explicitly state
that a terminating more expressive reasoner may reveal additional
contradictions. They also explain why repeated satisfiability tests need a fast
oracle ([Slater, Gkoutos, and Hoehndorf 2020](https://link.springer.com/article/10.1186/s12911-020-01336-2)).

- **Question:** how do detection, explanation, and the greedy repair trajectory
  change when each ELK oracle call is replaced by complete OWL 2 DL reasoning?
- **Exact-2018 transformation:** reacquire the exact 132 dated payloads and
  reproduce the published EL arm first. Then run the same merges, most-general
  unsatisfiable-class selection, at-most-25 explanation sample, axiom-frequency
  removal, and reclassification with KM. The source code is pinned at UNMIREOT
  commit `e579133d34b6e579da2b673f9cd0ffe0c8427fec`.
- **2026 transformation:** pre-register a core set from the already frozen
  2026-08-30 OBO snapshot, run full and EL-drop detection arms, freeze those
  results, and only then run a separate repair arm.
- **Expected observation:** all KM deltas are hypotheses. The 2018 numbers are
  reproduction targets only for the exact source payloads; 2026 raw counts are
  a new-data study and cannot be described as a replication of those counts.
- **Comparators/oracle:** reproduce ELK first; use KM full; independently check
  every claimed full-only conflict with a complete reasoner on a locality
  module and retain source supports.
- **Risks/confounders:** exact 2018 ontology files are not in the companion
  repository; permanent links resolve newer content; repair is heuristic and
  potentially order-sensitive; an axiom in a justification is not necessarily
  scientifically wrong. The complete procedural note is
  [`impact/slater-2020.md`](impact/slater-2020.md).

### BIO-MERGE-CONTROL: already executed mechanism check

- **Ontology/features/question:** the checked-in biomedical merge pair combines
  a universal restriction with an existential into a disjoint filler. It asks
  whether `IntegratedFinding` becomes empty while the ontology remains
  consistent.
- **Transformation/observation:** conflict and repaired control differ by one
  existential filler. KM and HermiT distinguish them; ELK's two out-of-profile
  relation digests are identical.
- **Command/oracle/evidence:** manifest row `BIO-MERGE-CONTROL`; existing
  four-axiom subset-minimal KM-oracle support and HermiT agreement.
- **Risk:** synthetic mechanism only, not a corpus-scale merge or a source
  ontology defect.

## Non-biomedical cases

### NONBIO-ACCESS-CONTROL: already executed policy composition

- **Ontology/features/question:** checked-in synthetic access policy; universal
  low-clearance constraint, required high-clearance successor, and disjoint
  clearance classes. It asks whether `PrivilegedContractor` is impossible.
- **Transformation/observation:** a one-axiom repaired pair. KM and HermiT find
  one unsatisfiable named class only in the conflict; ELK's out-of-profile runs
  do not distinguish the pair.
- **Command/oracle/evidence:** manifest row `NONBIO-ACCESS-CONTROL`; existing
  four-axiom support and HermiT agreement.
- **Risk:** this is not an operational policy ontology.

### NONBIO-PRODUCT-CONFIG: engineering cardinality regression

- **Ontology/version/source:** new checked-in controlled pair
  `impact/proposed/product-configuration-{conflict,control}.ofn`, hashes
  `a92e020a...e0fde6` and `baad9238...e0d2f3`.
- **DL features:** qualified maximum cardinality one, two existential payload
  requirements, payload typing, and disjoint camera types.
- **Question:** does a single-payload design rule make a dual-sensor survey
  drone configuration impossible?
- **Transformation/query:** the conflict differs from the control only by
  `ObjectMaxCardinality(1 hasPayload Payload)`. Classify both and explain
  `DualSensorSurveyDrone`; also compare generated EL views.
- **Expected observation:** under OWL Direct Semantics the conflict class is
  unsatisfiable while the control class is satisfiable; both ontologies remain
  consistent. This is a logical expectation, not an executed KM result.
- **Comparators/command/oracle:** KM and HermiT full; KM and ELK projection;
  exact one-axiom diff and independently checked explanation. See manifest.
- **Risks/confounders:** OWL may identify the two fillers because it has no
  unique-name assumption; their disjoint types are what turns identification
  into the intended contradiction. No deployed product line is represented.

### NONBIO-FIBO-IDENTITY: finance ontology plus bad-data injection

- **Ontology/version/source:** FIBO production TBox tag `master_2026Q2`, commit
  `f59157fe156e3d91b1c045222d0a7dc06b7d78a2`, root
  `AboutFIBOProd-TBoxOnly.rdf`. FIBO describes itself as OWL 2 DL and requires
  logical consistency checks with multiple compliant reasoners
  ([FIBO ontology guide](https://github.com/edmcouncil/fibo/blob/master/ONTOLOGY_GUIDE.md)).
- **DL features:** the inspected release axiom constrains an
  `IdentityDocument` to at most one `isEvidenceFor` filler of type
  `PhysicalAddress`. The conflict patch asserts two explicitly different such
  addresses; the control omits `DifferentIndividuals`.
- **Question:** can an identity-document data record point to two known-distinct
  physical addresses under the FIBO constraint?
- **Transformation/query:** clone the exact commit; resolve every import through
  its checked-in `catalog-v001.xml`; freeze the local closure; union the
  conflict or control patch with `MergeOntologies`; classify all three. Patch
  hashes and exact IRIs are in the manifest.
- **Expected observation:** if the inspected axiom survives the pinned closure,
  full DL entails conflict inconsistency and control consistency; EL deletion
  loses the cardinality/distinctness conflict. This has not been run.
- **Comparators/command/oracle:** KM plus HermiT or Konclude, with a source
  support containing the FIBO cardinality axiom and injected ABox facts.
- **Risks/confounders:** FIBO imports OMG Commons and uses version-independent
  IRIs. Resolving imports over the network would mix versions, so a run is
  invalid unless all imports map to the pinned checkout and the expected source
  axiom is present. The injected data is deliberately bad; it is not a FIBO
  defect.

## Highest-value execution order

1. Run the small product-configuration pair first as a syntax, cardinality,
   explanation, and projection smoke gate. It should finish in minutes and
   catches a broken harness before any large allocation.
2. Finish and ingest current Uberon full classification, then run its EL
   projection and differential. Guarded KM has already established consistency,
   but that result contains no named-class taxonomy and cannot answer the
   differential question.
3. Run FMA full plus projection. Konclude's existing successful full result
   makes this the best large-ontology correctness oracle.
4. Run NCIt and ChEBI differentials. Their existing four-way full agreement
   isolates the scientific question from base-classification uncertainty;
   ChEBI is the required null control.
5. Run the GALEN EL differential against the already repeated full taxonomy.
6. Freeze and run FIBO. This supplies a public, non-biomedical, natural-ontology
   data-quality example rather than another standalone toy.
7. Run detection-only UNMIREOT-2026 after its core-set preregistration. Do not
   start the repair loop until detection results are immutable.
8. Defer the Uberon-FMA bridge, exact-2018 UNMIREOT replication, current
   BioPortal GALEN, NCIt negation-product arm, and real SNOMED CT experiment
   until their source/licence/version gates pass.

## Evidence that must still be added before paper claims change

- A successful full current-Uberon taxonomy, in addition to the demonstrated
  guarded consistency verdict, with repeated digest and comparison gates.
- A compiled SHA-bound `MakeELProjection`/`MergeOntologies` runner artifact for
  IBEX. Maven is unavailable on this workstation, but both classes compiled
  with `javac` against the pinned ELK classifier jar. A tiny projection smoke
  removed the one cardinality axiom from the product conflict and emitted an
  independently profile-valid EL document; a tiny merge smoke also completed.
  These local transformation checks did not invoke an ontology reasoner.
- A copied FMA OWLAPI profile receipt with exact violation classes.
- Full and projection output receipts for Uberon, FMA, NCIt, ChEBI, and GALEN.
- Release-matched bridge, GALEN payload, and NCIt negation-product checksums.
- A pinned FIBO import map proving no dependency came from a moving network IRI.
- An authorized SNOMED CT release and domain-reviewed perturbation. No licensed
  content may enter the public artifact.
- Independent module checks and source supports for every consequence promoted
  from “hypothesis” to “demonstrated.”
