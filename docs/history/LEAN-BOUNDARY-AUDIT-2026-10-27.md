# KM v1.5.3 Lean certification audit (read-only)

Source audited: tag v1.5.3 checkout at `$S = /tmp/claude-1000/-home-leechuck--herdr-worktrees-kobayashi-marust-worktree-paper/0285edda-d83d-4be5-8ecb-bb0aeb5575cb/scratchpad/km-v153`.
Every path below is relative to `$S` unless it is absolute. Paper: `/home/leechuck/Documents/papers/km-agents-paper/sections/`.
Nothing was built or run. Statements are from reading source, scripts, and docs.

## 0. Bottom line

* The Lean theorems are **per-document checker theorems**. Each says: *if this executable checker accepts this wire document, the answer in the document is exact (sound and complete) for the clause-level ontology encoded inside the same document.*
* The reference semantics is **first-order semantics of KM's normalised clause language** (`List FCL`, Hypertableau `Clause`, ELC normal forms, CB `SourceOntology` of clauses + chains + role axioms), with concepts and roles as natural-number indices. **No Lean theorem mentions OWL functional syntax, IRIs, or the OWL 2 direct semantics, and none connects the frontend's output clause set to the source ontology.** The only formal hook for that connection, `CertifiedRouting.SourceTranslation.correct_iff`, is never instantiated anywhere in `lean/`.
* **Completeness of the procedures is never proved.** "Complete" in the capstones means "an accepted document's matrix contains every entailed cell of its own clause source". The routing capstone takes the completeness of the selected route and its fallback as **structure fields (hypotheses)**. `ConcreteSupervisor` is never instantiated.
* **No Lean checker runs on the default `km classify` path or in `km incremental-source`.** CB, ELC, and HT checkers run only when specific environment variables are set. The routing checker binary runs only on two fixture files inside the routing gate. Rust code itself says the evidence path is skipped for "ordinary classification and ORE benchmarks".
* Wrong answers (A)–(C) therefore come from components **outside the theorems** (frontend translation, IRI identity, incremental Rust module logic) and from **runtime non-execution**. They do not come from a false Lean theorem. On the statement "if wrong answers occur, the Lean certification is also wrong": the theorems are not refuted. What fails is the paper's description of what the theorems cover.

## 1. What each gate proves

All four gates (`lean/run-{elc,ht,cb,routing}-certification-gate.sh`) follow one pattern:
1. build Lean modules and native checkers;
2. fail on `sorryAx` in the `#print axioms` log;
3. grep for a fixed list of theorem names in that log;
4. run tamper fixtures and Rust tests.

They establish that the listed theorems exist and are axiom-clean. They do not establish anything about a particular production run.

### 1.1 ELC gate (`lean/run-elc-certification-gate.sh`)
* Gate audits: `checkV5_publication_semantics`, `WireCertificate.check_publication_semantics` (lines 44-54), and common-source lemmas including `WireCertificate.check_common_source_sound` (56-67). It then runs Rust tests with `KM_ELC_TEST_LEAN_CHECKER` (74-88).
* Theorem, `lean/ContextCalculus/ELCompletionExecutablePublication.lean:16-19`:
  `theorem WireCertificate.check_publication_semantics (wire : WireCertificate) (hcheck : wire.check = .ok true) : ∃ decoded : DecodedCertificate wire.symbol_count, wire.decode = .ok decoded ∧ PublicationSemantics decoded`
* `PublicationSemantics`, `lean/ContextCalculus/ELCompletionPublication.lean:16-44`, has four fields:
  * `inconsistent_exact : doc.public_inconsistent = true ↔ UnsatisfiableWithResidual doc.ontology doc.sourceResidualTheory`
  * `id_taxonomy_exact` (iff, under side conditions: active subject, not top/bottom, satisfiable subject or sup = bottom)
  * `named_taxonomy_sound`
  * `named_taxonomy_complete`
* Input object: a wire certificate JSON. The semantics is over `doc.ontology` plus `sourceResidualTheory`, i.e. the normalised clause stream inside the certificate.
* Completeness: proved for the accepted document's own source, on the reportable cells given by the side conditions.
* Source-side gaps, stated in the repo:
  * `lean/README.md:125-126`: the source axioms are "reconstructed from normalized frontend Horn clauses".
  * `lean/README.md:158-160`: "Proving the adjacency invariant against the Rust stream and the certificate-wire connection remain open".
  * `lean/README.md:231-232`: the Rust worker invokes the checker only "when `KM_ELC_LEAN_CERT_CHECKER` is set".

### 1.2 HT gate (`lean/run-ht-certification-gate.sh`)
* Gate audits the `HypertableauCertificationSurface` theorems (lines 140-181 of the script) and many support lemmas, then runs Rust tests.
* Representative theorems, `lean/ContextCalculus/HypertableauCertificationSurface.lean`:
  * 144-147: `theorem certifiedHTExecutableTaxonomyPublication (wire : WireExecutableHTTaxonomyPublication) (hcheck : wire.check = true) : wire.SemanticallyValid`
  * 151-154: `theorem certifiedHTDirectCommonTaxonomyPublication (wire : …WireDirectTaxonomyPublication) (hcheck : wire.check = .ok true) : wire.SemanticallyValid`
* `SemanticallyValid`, `lean/ContextCalculus/HTDirectTaxonomyCommonPublication.lean:110-115`: decode succeeds and `decoded.CommonSemantics` holds.
* `CommonSemantics`, same file 44-57: for named concepts, unsatisfiability ↔ `CommonUnsatisfiableConcept (mapOntology decoded.normalization.source)` and subsumption ↔ `CommonEntailsSub (mapOntology decoded.normalization.source) sub sup`.
* Input object: wire JSON whose `normalization.source` is a list of HT clauses.
* Completeness: both directions (iff) for the accepted document's named concepts.
* Fragment: per certified family. The surface docstring is at 36-47. The paper's own table says "inverse roles, nominals, and native ABoxes in the certified constructor" are outside.

### 1.3 CB gate (`lean/run-cb-certification-gate.sh`)
* Gate audits 18 surface theorems (65-90), runs the standalone-context-proof fixtures (92-98), and runs Rust tests.
* In those tests, `KM_CB_TEST_ALLOW_EXTERNAL_SOURCE=1` (line 127) lets fixtures load handcrafted sources.
* Module doc, `lean/ContextCalculus/CBCertificationSurface.lean:34-37`: "It certifies an accepted document, not an unchecked production run. Rust generation and fail-closed invocation are separate integration obligations."
* Capstone, 382-402:
  `theorem certifiedCBProductionExactTaxonomyPublication (wire : WireLiveExactTaxonomyPublication) (hcheck : wire.check = .ok true) : ∃ decoded, wire.decode = .ok decoded ∧ decoded.named.toFinset = (liveNamedConcepts decoded.live).toFinset ∧ … ∧ ∀ index, (decoded.cells.get index).answer = true ↔ SourceExactEntails decoded.live ⟨sub,_⟩ ⟨sup,_⟩`
* `SourceExactEntails`, `lean/ContextCalculus/CBLiveExactTaxonomyPublication.lean:93-101`, quantifies over `Eqv.Interp` models of `CBRoleChainEncoding.models interpretation (productionOf live).source.source`.
* The source is `SourceOntology := {clauses, chains, roleAxioms}` (`CBRoleChainEncoding.lean:45-48`; `models` at 61-66). This is a typed clause source, not OWL.
* At runtime, Rust builds that typed source **from the frontend clause stream**:
  * `engine/src/cli.rs:597-606` calls `crate::cb_source::typed_source_candidate(&input.clauses)`;
  * `engine/src/cb_source.rs:618-648`: `recover_source` reads clauses, and reads chains from chain-shaped clauses.
* Completeness: iff per materialised named coordinate of the accepted document.
* Fragment limits of the evidence families:
  * `docs/CB-CERTIFICATION.md:669-671`: "Functionality, nominals, qualified cardinality, and chains longer than two remain outside this evidence form";
  * `docs/CB-CERTIFICATION.md:761-762`: "General source role axioms remain outside this regular evidence family and therefore fail closed".
* Self-declared open items in `docs/CB-CERTIFICATION.md`:
  * 3-5: "not a claim that the layer is already complete";
  * 496-506: "until then, automatic production routing cannot claim the complete CB boundary";
  * 508-511: "The production Rust worker does not yet emit or invoke every component";
  * 802-803: "frontend-to-worker composition belong[s] to the later routing certification layer".
* `docs/CB-RULE-CERTIFICATION.tsv`, last row: "Blocking/core-growth … Termination and abstract strategy theorems only | Not refined to Rust state".

### 1.4 Routing gate (`lean/run-routing-certification-gate.sh`)
* Gate builds about 50 modules (32-82) and greps 290+ theorem names (90-390).
* It runs `km-automatic-routing-check` on one valid and one forged fixture (392-396). It then runs Rust unit and integration tests, including all incremental tests (398-446). Those incremental results are Rust tests, not Lean.

**(a) Abstract router.** `lean/ContextCalculus/CertifiedRouting.lean:284-292`:
`theorem AutomaticRouter.sound_and_complete (router : AutomaticRouter Profile Source Answer correct) : (∀ source answer, router.run.run source = .publish answer → correct source answer) ∧ (∀ source, ∃ answer, router.run.run source = .publish answer ∧ correct source answer)`
* Completeness is the structure field `coverage : ∀ source, CertifiedProcedure.Covers (select (profile source)) source` (235-240). It is a hypothesis.

**(b) Supervisor.** `lean/ContextCalculus/KMAutomaticSupervisor.lean:110-117`, `CertifiedSupervisor.sound_and_complete`.
* Completeness comes from the fields `selectedComplete` and `fallbackComplete` (44-54).
* The docstring at 37-42 says these "follow" from neither the route name nor termination.

**(c) Concrete supervisor.** `lean/ContextCalculus/KMConcreteAutomaticSupervisor.lean:86-92`:
`theorem ConcreteSupervisor.sound_and_complete (supervisor : ConcreteSupervisor) : (∀ source answer, supervisor.run.run source = .publish answer → RequestedCorrect source answer) ∧ (∀ source, ∃ answer, … ∧ RequestedCorrect source answer)`
* `ConcreteSupervisor` (39-48) has fields `decide`, `execute : Route → KMRequestedExecution`, `selectedComplete`, and `fallbackComplete`. The docstring at 12-17 says operational completeness is "stated as … liveness obligations".
* Each `KMRequestedExecution` must carry `accepted : … requestedExactAccept source answer evidence = true` (`KMConcreteWorkerAdapters.lean:1211-1220`). Soundness is therefore conditional on a Lean checker having accepted.
* `ConcreteSupervisor` is **never instantiated**. grep across `lean/` finds it only in its defining file, and no Rust code references it.

**(d) Common source.**
* `RequestedTaxonomySource := {ontology : List FCL, named : List Nat}` (`KMConcreteWorkerAdapters.lean:1184-1187`).
* `Correct`/`RequestedCorrect` (37-41, 1189-1192) uses `Entails ontology sub sup`, defined at `KMCommonRoutingSource.lean:29-32` as first-order validity over `TModel` models of the clause list.
* `cbAccept` (176-182) takes the ontology **from the decoded certificate** (`ontology = cbPublicationOntology decoded`).

**(e) Executable routing checker.**
* `KMAutomaticRouting.lean:137-143`: `WireSelection.check wire := wire.version == 1 && decide (wire.selected = select wire.decision)`, with `check_sound` giving `wire.selected = select wire.decision`.
* The `Decision` is a record of Booleans supplied by the caller (67-87). The module doc (10-12) says: "Expensive numeric profile predicates are represented by named Boolean decisions here; later executable profile certificates must justify those decisions".
* The wire holds no source and no digest. See `lean/testdata/km-routing-large-horn-valid.json`. grep for digest/sha256 in the routing Lean files finds nothing.
* `coverageBasis` (154-163) is a definitional label. `selected_route_has_coverage_basis` (216-218) is `⟨coverageBasis (select decision), rfl⟩`.
* `CoverageObligations.preprocessingEquivalence` (199-211) is a Bool set to `true` by definition. No proof is attached.

**(f) Frontend hook.**
* `SourceTranslation.correct_iff` (`CertifiedRouting.lean:98-112`) is the obligation that would tie a router source language to the worker clause language. Its docstring says a concrete adapter "must prove it from the frontend normalization theorems".
* There are **zero instances**. grep for `SourceTranslation`/`liftTranslation` outside `CertifiedRouting.lean` finds only a comment in `HTRoutingSource.lean:12`.

**Summary for Q1.** Soundness and completeness are proved for *accepted documents* relative to *their own clause sources*. Routing exactness is proved *given* worker acceptance and *assuming* route completeness. No gate proves any procedure (EL completion, CB, HT) complete, i.e. that it always produces an acceptable document, on any OWL fragment.

## 2. Is the frontend inside the boundary?

No. Evidence:
* Every capstone's semantic object is a clause list or a typed clause source (§1). The Lean semantics has no OWL syntax tree, no IRI type, and no "direct semantics". grep for "direct semantics" in `lean/` returns nothing.
* A separate SROIQ syntax exists only in the incremental locality model (`IncrementalModuleReuse.lean`, `EntailsC` at 1144-1145). No theorem relates it to `FCL`.
* The translation hook `SourceTranslation` is uninstantiated (§1.4f).
* The CB typed source is recovered from the clause stream the frontend produced (`cli.rs:597-606`, `cb_source.rs:618-648`). The ELC source is "reconstructed from normalized frontend Horn clauses" (`lean/README.md:125-126`).
* Normalisation lemmas exist for individual transformations (`ELNormalization`, `ELRawNormalization`, `CBRoleChainCanonicalBinary`, `InverseRoleChainNormalization`, `NativeCardinalityNormalization`, …). They are stand-alone equivalence lemmas. They are not linked to `engine/src/frontend/*` output by any checker, and `lean/README.md:158-160` says the connection remains open.
* Out of scope of every theorem:
  * IRI registry (`engine/src/frontend/iri.rs`);
  * parser (`sexpr.rs`, `parse.rs`);
  * clausifier (`normalise.rs`);
  * augmentation and chain/transitivity encoding (`preprocess.rs:1180-1245`);
  * output mapping from internal names to IRIs (orchestrator; paper `system.tex:697-700`).

## 3. Runtime checking on the default `km classify` route (v1.5.3)

* **CB**: Lean checking only when `KM_CB_LEAN_REQUIRED` is set (`engine/src/cli.rs:652-662`, `verify_cb_lean_publication`, which needs `KM_CB_LEAN_CERT_CHECKER`/… and `KM_CB_CERT_BUNDLE`, `cli.rs:1582-1592`). The certified mode is a different configuration from production:
  * it retains all query roots and disables mutual-unit collapse (`engine/src/reasoner.rs:946-953`);
  * it forces one thread (`reasoner.rs:969-985`).
  * The route named `lean` does **not** set it. Its bundle (`engine/src/routing.rs:2800-2810`) only sets CB single-thread options.
* **ELC**: Lean checking only when `KM_ELC_LEAN_CERT_CHECKER`/`KM_ELC_LEAN_REQUIRED` is set (`engine/src/elcomplete.rs:12459-12468`). Production sets `KM_ELC_CERT=2` (`orchestrate/race.rs:442-450`; `routing.rs:2798`), which is a Rust canonical-model repair certificate (`elcomplete.rs:12008-12022`), not Lean. Under Lean-required mode two production rewrites are disabled because they are outside the Lean theorem:
  * the positive-ABox rewrite declines (`elcomplete.rs:11137-11146`, "source ABox rewrite is outside the ELC Lean boundary");
  * inverse-bridge preparation is skipped (`elcomplete.rs:12470-12479`).
* **HT**: Lean checking only when one of about 50 `KM_HT_LEAN_*` variables is set (`engine/src/tableau.rs:7943-7999`, `ht_lean_certification_requested`). `orchestrate/cb_to_ht.rs:4404-4411` says the evidence computation "is evidence-only, so ordinary classification and ORE benchmarks must not pay for it."
* **Routing**: no Rust code emits a `WireSelection` or invokes `km-automatic-routing-check`. grep of `engine/src` and `engine/tests` finds none. The checker runs only on two fixtures in the gate (`run-routing-certification-gate.sh:392-396`).
* **Konclude-port bridge** (`engine/src/konclude_ht/`): it has no Lean model and emits no Lean evidence. Its "certified" mode (`orchestrate/race.rs:1017-1030`) is a Rust fragment gate. The Lean evidence union `KMExactEvidence` has only `elc | ht | cb` (`KMConcreteWorkerAdapters.lean:1135-1138`).
* `orchestrate/` never sets any `*_LEAN_*` variable. The only read is the HT projection checker in `cb_to_ht.rs:4410`.

What the routing certification proves:
1. the executable selector equals the Lean `select` on a given Boolean decision;
2. every atomic specialist on a fallback-eligible fragment has a fallback whose *label* is not `certifiedFragment` (`automatic_specialist_decline_has_coverage`, `KMAutomaticRouting.lean:184-193`);
3. given accepted worker evidence and given the completeness hypotheses, the supervisor's first-publish sequence is exact (`ConcreteSupervisor.sound_and_complete`).

It does **assume** each procedure is complete on the routed source (`selectedComplete`/`fallbackComplete`). It proves neither that the Rust selector matches the Lean `select` nor that the Boolean profile predicates are true of the source.

## 4. Is incremental-source inside the boundary?

Not at runtime, and only abstractly in Lean.
* `IncrementalRevisionPublication.exact` (`lean/ContextCalculus/KMIncrementalExplanationCertification.lean:24-36`) requires a field `accepted : requestedExactAccept source answer evidence = true`, i.e. Lean-accepted ELC/HT/CB evidence for the post-update **clause** source. The incremental code never produces or checks that.
  * `engine/src/incr_session.rs:1-38` describes the publication rule. It says reuse "never decides an entailment itself" but relies on "the unchanged `km classify` pipeline" (itself unchecked, §3) and on Rust locality/module computation.
* The module-reuse theorems, e.g.
  * `unaffected_query` / `sandwich_query` (`IncrementalModuleReuse.lean:103-116`),
  * `NominalModule` (1532-1537),
  * `nominal_unaffected_query` (1606-1612),
  * `common_nominal_module_named_query` (1654-1659),

  take `IsModule`/`NominalModule` as hypotheses. They are stated over a separate Lean SROIQ syntax. The file says (33-36): "The Rust/Lean binding (parser, formula compiler, DNF weakening, fixpoint propagation) is an executable obligation checked by tests, not by this file."
* The routing gate's incremental coverage is Rust tests (`run-routing-certification-gate.sh:406-427`). `docs/INCREMENTAL-ROUTES.tsv` lists Rust tests as the "evidence" column.
* `common_nominal_subject_reuse` (`engine/src/incr_session.rs:2506-2560`) is plain Rust:
  * `nominal_common_subjects`, `object_common_module`, `classify_rows_with`, `replace_rows_from`;
  * no Lean invocation;
  * when `ht_lean_certification_requested()` is set, some incremental reuse is disabled (`engine/src/source_incremental.rs:1435`, `1496`).
* Explanations: `CertifiedExplanation.support : List CheckerTerm.FCL` (`KMIncrementalExplanationCertification.lean:81-84`). The minimality theorems concern clause supports, not source OWL axioms.

## 5. Why the certification did not catch (A)–(C)

**(A) Chain/transitivity consumers of a super-role (14101).**
* *Outside the boundary* (primary cause):
  * The frontend drops chain and transitivity axioms from the clause stream unless `keep_chains` applies (`preprocess.rs:1205-1206`, filter at `1229-1237`: `keep_chains || !is_chain_axiom(c) || is_canonical_long_chain_axiom(c)`).
  * It replaces them with recognition clauses from `transitivity_clauses_with`/`chain_clauses_with` (`preprocess.rs:1218-1222`). These only fire for consumers whose body role is itself the transitive or chained role (`preprocess.rs:211-226`, check at 225: `if !trans.contains(rrole) …`).
  * The clause set handed to every worker therefore lacks the role axioms needed for `∃R4.W ⊑ D` through `R2 ⊑ R4`.
  * Every theorem's source is that clause set: the CB typed source is recovered from it (`cb_source.rs:618-648`), and ELC/HT certificates encode it.
  * An exact answer for the clause set is a wrong answer for the OWL source. A Lean checker run on it would certify that answer as exact.
  * The v1.5.4 fix is purely in the frontend (commit 09106118, `engine/src/frontend/preprocess.rs` +225 lines, "The clauses are entailed and additive"). That fits a source-translation defect, not a calculus defect.
  * Suggested confirming experiment, not run here: classify the v1.5.3 frontend output for 14101 with `KM_CB_LEAN_REQUIRED` and the source-production checker, and check whether it accepts.
* *Trusted assumption*: the routing capstone assumes route completeness. All four clause routes are labelled `certifiedFallback`/`totalCalculus` (`KMAutomaticRouting.lean:154-163`), but nothing proves this.
* *Unchecked at runtime*: no Lean checker ran (§3).
* The correct v1.5.3 answers came from the Konclude bridge, which has no Lean model at all (§3).

**(B) `<urn:t#u>` vs `:u`.**
* *Outside the boundary*:
  * `IriRegistry::short` (`engine/src/frontend/iri.rs:77-150`) keys its map on the token with angle brackets stripped (79-89). It does not expand prefix names itself, so the two spellings get distinct internal names.
  * Lean concepts and roles are `Nat`/`Fin` indices (`RequestedTaxonomySource.named : List Nat`; ELC `doc.symbols : Fin n → String`). Two indices for one OWL entity are simply two unrelated symbols, and the lost subproperty entailment is correctly not entailed by the clause source.
  * CB requirement 1 rejects "duplicate or aliased public names" (`docs/CB-CERTIFICATION.md:771`). That applies to identical strings, not to different spellings of one IRI.
* *Unchecked at runtime*: also applies.

**(C) `incremental-source` `common_nominal_subject_reuse` missed an unsatisfiable class.**
* *Outside the boundary / trusted assumption*:
  * The Lean theorems are conditional on `NominalModule O M S` and related hypotheses over a separate SROIQ model. Rust discharges these with `nominal_common_subjects`/`object_common_module` (`incr_session.rs:2534-2555`). The Lean file states that this binding is "checked by tests, not by this file" (`IncrementalModuleReuse.lean:33-36`).
* *Unchecked at runtime*:
  * `IncrementalRevisionPublication.exact` needs Lean-accepted evidence, which this path never produces.
  * The module classification runs the unchecked default pipeline (`classify_rows_with`, `incr_session.rs:2555`).
* I did not identify the exact Rust root cause. That needs the failing revision pair.

**(D) `owl:topObjectProperty` hangs.** These are resource and termination failures, outside every theorem by design (paper `certification.tex:36`, `110`).

## 6. Paper claims that overstate the certification, with proposed wording

1. `abstract.tex:11-14`: "Every published taxonomy must pass a route-specific acceptance check, and a Lean 4 development proves that an accepted answer is exact under the OWL 2 direct semantics for the EL, hypertableau, consequence-based, and routing publication boundaries."
   * Problem: there is no OWL direct semantics in Lean (§2). The Lean check is not run per answer (§3).
   * Proposed: "Every published taxonomy passes route-specific Rust checks. A Lean 4 development proves, for each of the EL, hypertableau, and consequence-based procedures, that an evidence document accepted by its Lean checker gives the exact taxonomy of the normalised clause set encoded in that document. It also proves that the router's publication sequence preserves this exactness if the selected procedures are complete. The OWL-to-clause translation, IRI handling, and procedure completeness are not covered, and the Lean checkers are not invoked during ordinary classification."
2. `intro.tex:53-58`: "Every public answer passes a route-specific acceptance check, and the Lean development proves that an accepted answer is exact. … an agent may be wrong in a worker, but a wrong answer cannot reach the output without passing a checker whose theorem the agent did not write alone."
   * Proposed: "Every public answer passes route-specific Rust checks. When a Lean checker is enabled and accepts a worker's evidence document, the Lean development proves the answer exact for the clause set in that document. Errors in the frontend translation or in procedure completeness, and any run without the Lean checker (including the default configuration and our benchmarks), are outside this guarantee."
3. `certification.tex:10-14`: "each public result must satisfy a source-bound, route-specific acceptance relation whose soundness is a theorem … Lean proves that the published answer is exact under the formal semantics."
   * Proposed: "A result can be checked against a route-specific acceptance relation whose soundness is a theorem. If a Lean checker accepts a document binding a normalised clause source, a requested signature, derivation evidence, and an answer, Lean proves that the answer is exact for that clause source under first-order semantics. The 'source' is the frontend's clause output, not the OWL document."
4. `certification.tex:24-26`: "The routing layer checks the source profile, the ordered selector and fallback sequence, exact source identity, the requested signature, and dispatch to one concrete EL, hypertableau, or CB checker."
   * Proposed: "The routing layer's executable checker verifies that a given Boolean profile decision selects the stated route (`WireSelection.check`). The routing theorems prove that, if every published answer carries accepted EL, HT, or CB evidence for the same clause source and requested signature, and if the selected route or its fallback is complete on that source, the supervisor publishes an exact answer. The profile Booleans and the completeness premises are not checked."
5. Table `certification.tex:42-62`, "Outside" column and routing row:
   * EL "the parsers that produced the raw stream" → "the OWL parser, IRI registry, normalisation, and chain/transitivity augmentation that produced the raw stream; that the procedure always emits an acceptable certificate".
   * HT: add "the frontend translation to HT clauses; procedure completeness".
   * CB: add "the frontend clause stream from which the typed source is recovered".
   * Routing "Checked object": replace "source profile … incremental revisions, and explanation minimality" with "selected route equals the Lean selector on a supplied Boolean decision".
   * Routing "Producer obligation": the wire binds no source digest. Replace with "a decision record (unchecked Booleans) and selected route".
   * Routing "Outside": add "profile predicates, completeness of each selected procedure and fallback (theorem premises), the Konclude-port bridge, the incremental module computation".
6. `certification.tex:75-77`: "A run whose evidence is rejected publishes nothing".
   * Proposed: "In Lean-required mode (`KM_CB_LEAN_REQUIRED`), a run whose evidence is rejected publishes nothing. Default runs do not invoke the Lean checker."
7. `certification.tex:79-83`: "let O be the decoded source ontology … O ⊨ A ⊑ B".
   * Proposed: "let O be the decoded normalised clause set (the frontend's output), with ⊨ the first-order semantics of KM's clause language."
8. `certification.tex:90-91`: "Selector and fallback theorems establish that an automatic route has an exact source and a total-calculus or complete-fallback coverage basis."
   * Proposed: "The selector theorems assign each route a coverage label (total calculus, certified fallback, or certified fragment). They prove that every atomic specialist has a fallback not labelled as fragment-dependent. Completeness of the labelled procedures is a premise, not a theorem."
9. `certification.tex:91-93` and `interfaces.tex:38-40`: "Incremental revisions and explanation minimality have their own capstones"; "The routing capstone connects an accepted explanation to source entailment".
   * Proposed: "An incremental revision is exact if it carries accepted EL, HT, or CB evidence for the updated clause set. The incremental implementation does not produce such evidence. Its module-reuse rules are justified by Lean lemmas over a separate SROIQ model, and the Rust code that applies them is validated by tests. Explanation minimality is proved for clause supports with accepted per-deletion evidence."
10. `certification.tex:108-113`: "The trusted computing base includes … the OWL parsers … An execution that bypasses the mandatory checker is outside the theorem. … every published KM taxonomy on the benchmarks below passed the acceptance relation."
    * Proposed: "The trusted computing base includes Lean's kernel and runtime, the Rust compiler, the entire OWL frontend (parsing, IRI identification, normalisation, role-chain and transitivity encoding, augmentation), the output mapping, the Konclude-port bridge, the incremental module logic, the watchdog, and the operating system. The Lean checkers are optional at runtime. No benchmark run invoked them, so the benchmark taxonomies passed the Rust checks of their routes, not the Lean acceptance relation."
11. `system.tex:520-526`: "…after which the supervisor invokes the next semantically complete route."
    * Proposed: "…after which the supervisor invokes a fallback route designed to be complete; this completeness is tested, not proved."
12. `system.tex:625-628`: "Because a predicate only chooses among procedures that answer completely or defer to an exact fallback, a band that generalises poorly costs time and never correctness".
    * Refuted by (A).
    * Proposed: "The predicates are intended to choose only among procedures that answer completely or defer. Because that completeness is not proved, a predicate can change correctness: v1.5.3 answered ORE 14101 correctly only because its routing sent it to the Konclude bridge."
13. `system.tex:671-672` (caption): "Source rewrites and bounded probes publish only certified answers".
    * Proposed: "…publish only answers that pass their Rust certificates".
14. `discussion.tex:32-33`: "Lean obligations ensured that no published answer depended on the corpus the agents had tuned on".
    * Proposed: "Lean obligations constrained the acceptance relations of the procedures, but they did not prevent a frontend or routing error from producing a wrong published answer".
15. `discussion.tex:65-67`: "The Lean development certifies accepted evidence, and the trusted base includes the parsers, the compilers, the watchdog, and the operating system".
    * Proposed: "The Lean development certifies accepted evidence relative to the normalised clause set. The trusted base includes the whole frontend translation, the bridge, the incremental logic, the compilers, the watchdog, and the operating system, and default runs do not invoke the Lean checkers".
16. `discussion.tex:97-101`: "A sound and complete OWL 2 DL reasoner that matches the best existing system … can now be built".
    * Proposed: "An OWL 2 DL reasoner that matched the reference reasoners on every verified ORE 2015 input we measured, with Lean-checked acceptance relations for its procedures, can now be built…". Also report that (A)–(C) were found after release.
17. `development.tex:132-137`: "The Lean proofs cover every input, but only for answers that pass the checker … A corpus-tuned approximation passes the benchmark but cannot produce evidence the checker accepts for an inexact answer".
    * Proposed: "The Lean proofs cover every clause set, but only for answers whose evidence a Lean checker accepted. They say nothing about the frontend translation from OWL into clauses, or about whether the producer emits acceptable evidence. A corpus-tuned approximation inside a procedure cannot produce accepted evidence for an answer that is inexact for its clause input. A frontend error yields accepted evidence for an answer that is wrong for the OWL source."
18. `development.tex:256-258`: "the selected procedures answer completely or defer, so such a band can cost time and cannot change an answer".
    * Proposed: "the selected procedures are designed to answer completely or defer. This is not proved, and ORE 14101 shows that a band can change an answer."
19. `development.tex:270-271`: "Behind all of these, the Lean boundary ensures that a shortcut that produces a wrong taxonomy cannot publish it, whatever the benchmark says."
    * Proposed: "When the Lean checkers are enabled, a shortcut inside an EL, HT, or CB procedure that produces a taxonomy inexact for its clause input cannot pass them. Shortcuts in the frontend, routing, bridge, or incremental code are not covered, and the checkers do not run by default."
20. `lean/README.md:9-10` (repository doc, not paper): "The production proof-carrying boundary is complete for ELC, HT, CB, and their automatic routing composition". It contradicts `docs/CB-CERTIFICATION.md:3-5`, `496-511`.
    * Proposed: "Each of ELC, HT, and CB has a checker theorem for accepted evidence over its clause source, and the routing composition is proved under explicit completeness premises."

Claims that are already accurate and can stay:
* `certification.tex:103-106` ("the benchmark does not invoke it once per ontology").
* `development.tex:132-134` (the proofs "say nothing about whether the producer emits acceptable evidence").
* The EL table entry's mention of parsers (incomplete, but accurate as far as it goes).
