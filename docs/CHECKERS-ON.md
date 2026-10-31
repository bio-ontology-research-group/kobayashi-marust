# Lean checkers on the classification route (v1.5.5)

This file answers the v1.5.5 line of `docs/CERTIFICATION-ROADMAP.md`: run a
test suite with the existing Lean checkers on, and record which published
answers they accept, reject, or cannot check. It has four parts: the
inventory of checkers (what each one checks and what acceptance proves), the
`KM_LEAN_CHECKERS=<dir>` switch, the suite and its results, and the recipe
for the Rust tests that need real checkers.

What acceptance proves is always the same kind of statement, and nothing
more (`docs/history/LEAN-BOUNDARY-AUDIT-2026-10-27.md` §0): if a checker
accepts a document, the answer in that document is exact for the normalised
clause set encoded in the same document. No theorem mentions OWL syntax,
IRIs or the OWL 2 direct semantics; the frontend that produced the clause
set, the IRI mapping, and the completeness of the procedure that produced
the document are outside every theorem.

## 1. Inventory

The 105 executables are the `[[lean_exe]]` targets of `lean/lakefile.toml`.
Each reads one JSON file, decodes it into the named wire structure and runs
its `check`; exit 0 accepts, 1 rejects (including a document that does not
decode), 2 is a usage or I/O error (`lean/CBCertCheck.lean:6-32`). The
theorems are cited as `file:line` under `lean/ContextCalculus/`.

### 1.1 Checkers the engine runs

**ELC** (worker `km elc` and the in-process EL path; `engine/src/elcomplete.rs`).

| executable | variable | document | theorem: acceptance proves | routes |
|---|---|---|---|---|
| `elc-cert-check` | `KM_ELC_LEAN_CERT_CHECKER` (`KM_ELC_LEAN_REQUIRED` makes a missing checker decline; `KM_ELC_LEAN_CERT_OUT` keeps the file) | `WireCertificate` v5 (`ELCompletionExecutablePublication`) | `WireCertificate.check_publication_semantics` (`ELCompletionExecutablePublication.lean:16`): inconsistency exact, id taxonomy exact, named taxonomy sound and complete for the clause stream and residual theory in the document (`ELCompletionPublication.lean:16-44`); `check_common_source_sound` (`ELCommonSourceWire.lean:298`) | `elc`, `elc_cert`, the EL arm of `production_all*` and `default*`, the in-process EL fast path |

A rejection makes the ELC worker decline (exit 3, `cli.rs` `run_elc`), and
the orchestrator then falls back to another route. Before v1.5.5 that
fallback answer was published with no record of the rejection;
`KM_LEAN_CHECKERS` (section 2) closes that gap.

**CB** (worker `km engine`, `cli::run_engine`; checks run only in certified
mode `KM_CB_LEAN_REQUIRED`, which also needs `KM_CB_CERT_BUNDLE` and an
in-band or compiled typed source; `cli.rs` `verify_cb_lean_publication`).
Every variable below except `KM_CB_LEAN_CERT_CHECKER` needs a companion
`*_CANDIDATE` path where the worker writes the document. A rejection exits 5
before stdout is written.

| executable | variable | document | theorem: acceptance proves | set |
|---|---|---|---|---|
| `cb-source-taxonomy-cert-check` | `KM_CB_SOURCE_EXACT_LEAN_CERT_CHECKER` | `WireSourceTaxonomy` | `certifiedCBSourceExactTaxonomyPublication` (`CBCertificationSurface.lean:361`; `CBSourceTaxonomyWire.lean:96`): every named×named cell ↔ entailment by the typed source | publication |
| `cb-source-production-taxonomy-check` | `KM_CB_SOURCE_PRODUCTION_TAXONOMY_CHECKER` | `WireDocument` (`CBSourceProductionTaxonomyWire`) | `certifiedCBSharedProductionTaxonomyPublication` (`CBCertificationSurface.lean:112`; wire `:329`): every cell ↔ typed-source entailment | publication |
| `cb-live-taxonomy-publication-check` | `KM_CB_LEAN_CERT_CHECKER` (the bundle) | `WireLiveTaxonomyPublication` | `check_sound` (`CBLiveTaxonomyPublication.lean:393`): published cells entailed, unsat rows unsatisfiable (soundness only) | none (2026-10-30: declined under `all`, see 5.3) |
| `cb-live-exact-taxonomy-publication-check` | `KM_CB_EXACT_LEAN_CERT_CHECKER` | `WireLiveExactTaxonomyPublication` | `certifiedCBProductionExactTaxonomyPublication` (`CBCertificationSurface.lean:382`) | none (2026-10-30: declined under `all`, see 5.3) |
| `cb-terminal-state-check` | `KM_CB_TERMINAL_STATE_CHECKER` | `WireCBTerminalStateDocument` | `check_sound` (`CBTerminalStateWire.lean:207`): no pending message, no truncation | none (2026-10-30: declined under `all`, see 5.3) |
| `cb-standalone-context-proof-check` | `KM_CB_STANDALONE_CONTEXT_PROOF_CHECKER` | `WireStandaloneDocument` | `certifiedCBStandaloneContextProof` (`CBCertificationSurface.lean:127`) | all |
| `cb-source-live-insertion-derivation-check` | `KM_CB_SOURCE_LIVE_DERIVATION_CHECKER` | `WireSourceLiveInsertionDerivationDocument` | `CBSourceLiveInsertionDerivation.lean:414`: every retained clause valid in every model of the source | all |
| `cb-source-local-closure-check` | `KM_CB_SOURCE_LOCAL_CLOSURE_CHECKER` | local-closure document | `CBSourceLocalClosure.lean:168` | all |
| `cb-source-hyper-closure-check` | `KM_CB_SOURCE_HYPER_CLOSURE_CHECKER` | Hyper closure | `CBSourceHyperClosure.lean:612` | all |
| `cb-source-join3-closure-check` | `KM_CB_SOURCE_JOIN3_CLOSURE_CHECKER` | Join-3 closure | `CBSourceJoin3Closure.lean:143` | all |
| `cb-source-succ-closure-check` | `KM_CB_SOURCE_SUCC_CLOSURE_CHECKER` | Succ closure | `CBSourceSuccClosure.lean:219` | all |
| `cb-source-eq-closure-check` | `KM_CB_SOURCE_EQ_CLOSURE_CHECKER` | Eq closure | `CBSourceEqClosure.lean:438` | all |
| `cb-source-ordinary-pred-closure-check` | `KM_CB_SOURCE_ORDINARY_PRED_CLOSURE_CHECKER` | ordinary Pred closure | `CBSourceOrdinaryPredClosure.lean:174` | all |
| `cb-source-root-pred-closure-check` | `KM_CB_SOURCE_ROOT_PRED_CLOSURE_CHECKER` | root Pred closure | `CBSourceRootPredClosure.lean:160`; `certifiedCBSourceProductionClosure` (`CBCertificationSurface.lean:311`) | all |

Routes: every route whose answer comes from the CB engine worker (`cb_*`,
`lean`, `nominals`, the CB arm of `production_all*` and `default*`, and the
CB fallback of every specialist). The in-process CB fast path for small
inputs (`orchestrate::try_inproc_engine`) has no certificate hook; it
publishes the same bytes as the worker.

"Set" is what `KM_LEAN_CHECKERS` turns on: `publication` checkers conclude
that the published taxonomy is exact; `all` adds the component wires
(`KM_LEAN_CHECKERS_SET=all`).

**HT** (worker `km tableau` with `KM_HT`; `engine/src/tableau.rs`
`run_tinput_inner`, `engine/src/hypertableau.rs`). Any of the 50 names in
`tableau::HT_LEAN_CERTIFICATION_ENV` turns on certified HT. Certified HT also
needs a selected HT route and `KM_HT_GLOBAL`; a preflight returns an error
when a required checker is missing (`tableau.rs:8219-8461`). A rejection
returns an error and the worker exits 1; there is no unchecked fallback inside
the worker. The checks during the search (`hypertableau.rs`
`lean_candidate_passes_with`) reject candidate folds as part of the search;
only UNSAT runs, frontier histories, exhausted blocking histories and run
matrices turn a rejection into an error.

| executable | variable (`KM_HT_LEAN_` + …) | theorem: acceptance proves |
|---|---|---|
| `ht-cert-check` | `CERT_CHECKER` (final verdict, `tableau.rs` verdict check; intermediate candidates) | `WireNormalizedCertificate.check_sound` (`HypertableauNormalizedWire.lean:501`), `WireCertificate.check_sound` (`HypertableauWire.lean:500`) and the equality, cardinality and regular-decision variants: the global SAT/UNSAT verdict is valid for the clause source |
| `ht-taxonomy-cert-check` | `TAXONOMY_CERT_CHECKER` | `unsatisfiable_exact`/`subsumptions_exact` (`HypertableauTaxonomyWire.lean:251/258`, mixed `:435/442`, cardinality `HypertableauCardinalityTaxonomyWire.lean:614/699`): named taxonomy exact |
| `ht-projection-cert-check` | `PROJECTION_CHECKER` | `WireDirectProjection.check_sound` (`HypertableauDirectProjectionWire.lean:137`) and 16 sibling formats: the HT clause projection is model-equivalent to the source |
| `ht-executable-publication-check` | `EXECUTABLE_PUBLICATION_CHECKER` | `HypertableauExecutablePublicationWire.lean:48/99`, surfaces `HypertableauCertificationSurface.lean:133/140`: `SemanticallyValid` |
| `ht-cardinality-common-taxonomy-check` | `CARDINALITY_COMMON_TAXONOMY_CHECKER` | `HTDirectCardinalityTaxonomyCommonPublication.lean:477` (+ mixed, bundle): named unsat and subsumption ↔ common-source entailment |
| `ht-source-bound-{ordinary,cardinality}-{global,taxonomy}-check` | `SOURCE_BOUND_…_CHECKER` | `HypertableauSourceBoundOrdinaryGlobalWire.lean:98`, `…OrdinaryTaxonomyWire.lean:34`, `HypertableauSourceBoundCardinalityWire.lean:40/79`: source, run and payload are bound and the decoded certificate is valid |
| `ht-source-bound-native-abox-{,cardinality-}{global,taxonomy}-check` | `SOURCE_BOUND_NATIVE_ABOX_…_CHECKER` | `HypertableauSourceBoundNativeABoxWire.lean:94/182/262/344` |
| `ht-{ordinary,ordinary-unsat,cardinality,rooted-ordinary,rooted-cardinality}-production-run-check` | `…_PRODUCTION_RUN_CHECKER` | `Hypertableau…ProductionRunWire.lean` (`:221`, `:153`, `:91`, `:113`, `:138`): trace valid from the start state and terminal accepted |
| `ht-{ordinary,cardinality,rooted-ordinary,rooted-cardinality}-taxonomy-production-run-check` | `…_TAXONOMY_PRODUCTION_RUN_CHECKER` | `Hypertableau…TaxonomyProductionRunWire.lean` (`:115`, `:117`, `:129`, `:144`) |
| `ht-{ordinary,cardinality}-taxonomy-run-matrix-check`, `ht-native-abox-{,cardinality-}taxonomy-run-matrix-check` | `…_RUN_MATRIX_CHECKER` | `HypertableauOrdinaryTaxonomyRunMatrixWire.lean:100`, `HypertableauCardinalityTaxonomyRunMatrixWire.lean:107`, native `:67/:73`: a complete taxonomy certificate exists for the terminal |
| `ht-address-refinement-check`, `ht-{,rooted-}cardinality-frontier-check` | `FRONTIER_CHECKER`, `{,ROOTED_}CARDINALITY_FRONTIER_CHECKER` | `HypertableauAddressRefinementWire.lean:111`, `HypertableauCardinalityFrontierStateWire.lean:138/150` |
| `ht-{,cardinality-,rooted-cardinality-}doubling-trace-check` | `…DOUBLING_TRACE_CHECKER` | `HypertableauDoublingTraceWire.lean:127`, `HypertableauCardinalityDoublingTraceWire.lean:100/198` |
| `ht-production-blocking-check`, `ht-production-trace-check`, `ht-equality-production-{blocking,trace,terminal}-check`, `ht-{finite,regular}-production-terminal-check` | matching `…_CHECKER` | `HypertableauProductionBlockingWire.lean:365`, `HypertableauProductionTraceWire.lean:145`, `HypertableauEqualityProductionBlockingWire.lean:969/919`, `HypertableauEqualityProductionTraceWire.lean:183`, `HypertableauFiniteProductionTerminalWire.lean:134`, `HypertableauRegularProductionTerminalWire.lean:87` |
| `ht-native-abox-decision-cert-check`, `ht-native-abox-source-decision-cert-check` | `NATIVE_ABOX_DECISION_CHECKER`, `NATIVE_ABOX_SOURCE_DECISION_CHECKER` | `HypertableauNativeABoxModelWire.lean:181/358`, `HypertableauNativeABoxSourceDecisionWire.lean:108` (+5 formats) |
| `ht-native-abox-taxonomy{,-matrix,-source}-cert-check`, `ht-native-abox-cardinality-taxonomy-{decision,cert,source-cert}-check`, `ht-joint-native-abox-classification-cert-check` | `NATIVE_ABOX_…_CHECKER`, `NATIVE_ABOX_JOINT_SOURCE_CLASSIFICATION_CHECKER` | `HypertableauNativeABoxTaxonomyWire.lean:322`, `…TaxonomyMatrixWire.lean:262`, `…TaxonomySourceWire.lean:385`, `HypertableauNativeABoxCardinalityTaxonomyWire.lean:455/763`, `…CardinalityTaxonomySourceWire.lean:542`, `HypertableauJointSourceClassificationWire.lean:498` |

The exact variable-to-executable map is `lean_checkers::HT_CHECKERS`
(`engine/src/lean_checkers.rs`); it follows the export block of
`lean/run-ht-certification-gate.sh` where the gate exports a variable. A
unit test (`ht_table_covers_every_certification_variable`) fails when a name
is added to `HT_LEAN_CERTIFICATION_ENV` without an executable.

Routes: HT answers come from `ht_general`, `ht_qo`, `ht_shoq`, `ht_card`,
`ht_features`, `ht_full`, the HT arm of `production_all*`, and the
HT-first probe of the race. The Konclude-port bridge (`ht_bridge`,
`ht_full`, `certified_nominals`' bridge attempt) has no Lean model and emits
no certificate (`docs/history/LEAN-BOUNDARY-AUDIT-2026-10-27.md` §3).

### 1.2 Checkers no production code runs

These are built by the gates. Some are run by Rust tests; none is reached
from `km classify`.

| executable | document | theorem | Rust use |
|---|---|---|---|
| `km-automatic-routing-check` | `WireSelection` | `WireSelection.check_sound` (`KMAutomaticRouting.lean:140`): the selected route equals `select decision` for a supplied Boolean decision | gate fixtures only (`run-routing-certification-gate.sh:392-396`); no Rust code emits the wire |
| `cb-cert-check` | `WireCertificate` (`CBSaturationWire`) | `CBSaturationWire.lean:95` | none; the production bundle is the live publication wire, which this checker does not decode |
| `cb-term-cert-check`, `cb-taxonomy-cert-check`, `cb-source-check`, `cb-nominal-allocation-check`, `cb-inter-context-check`, `cb-pred-coverage-check`, `cb-local-{resolution,factor,eq}-closure-check`, `cb-finite-{term,literal}-order-check`, `cb-finite-order-admissibility-check`, `cb-blocked-{carrier,ground-saturation}-check`, `cb-{hyper,join3,succ,rsucc}-closure-wire-check`, `cb-global-{closure,model}-check`, `cb-production-bound-global-model-check`, `cb-live-insertion-derivation-check` | component wires | `CBTermDerivationWire.lean:219`, `CBTaxonomyWire.lean:309`, `CBSourceWire.lean:353`, `CBNominalAllocationWire.lean:213`, `CBInterContextWire.lean:286`, `CBPredCoverageWire.lean:202`, … (one theorem per wire) | none (the last two are embedded in the bundle) |
| `cb-pred-send-coverage-check`, `cb-source-canonical-closure-check`, `cb-{,typed-}regular-arbitrary-chain-countermodel-check` | component wires, countermodels | `CBPredSendCoverageWire.lean:467`, `CBSourceCanonicalClosure.lean:79`, `CBRegularArbitraryChainCountermodelWire.lean:172`, `CBTypedRegularArbitraryChainCountermodelWire.lean:35` | tests only (`KM_CB_TEST_*`) |
| `ht-frontier-check`, `ht-eq-cert-check`, `ht-regular-cardinality-cert-check`, `ht-anchored-premises-check`, `ht-anchored-cardinality-cert-check`, `ht-{direct,mixed}-native-abox-cardinality-taxonomy-cert-check` | HT wires dispatched elsewhere | `HypertableauFrontierWire.lean:239`, `HypertableauEqualityWire.lean:290`, … | none |
| `ht-cardinality-cert-check`, `ht-regular-cert-check`, `ht-regular-decision-cert-check`, `ht-cover-obstruction-check`, `ht-endpoint-role-evidence-check`, `ht-cover-refinement-check`, `ht-anchored-eq-cert-check` | HT wires | `HypertableauCardinalityWire.lean:249`, `HypertableauRegularWire.lean:325`, … | tests only (`KM_HT_TEST_*`, or a sibling path of one) |

## 2. `KM_LEAN_CHECKERS=<dir>`

`KM_LEAN_CHECKERS` names a directory of built checkers. Under it,
`km classify` (also `--lines` and `--realize`):

* turns on, in each worker, the checkers of that worker's procedure that
  exist in the directory and are not already set by the caller: ELC
  (`elc-cert-check`), and the CB publication checkers
  (`cb-source-taxonomy-cert-check`, `cb-source-production-taxonomy-check`);
  `KM_LEAN_CHECKERS_SET=all` adds the CB component wires; `KM_LEAN_CHECKERS_HT=1`
  adds the HT checkers;
* writes every certificate into a private run directory under `TMPDIR`
  (`KM_LEAN_CHECK_KEEP=1` keeps it) and logs every checker event;
* prints one line per event on stderr, for example

  ```text
  KM_LEAN_CHECK accepted family=elc checker=elc-cert-check certificate=elc-publication bytes=2318 worker_pid=81020
  KM_LEAN_CHECK cannot_check family=cb checker=- certificate=cb-publication bytes=0 worker_pid=81034 detail="nominal mode: …"
  KM_LEAN_CHECK summary accepted=1 rejected=0 cannot_check=1 events=2
  ```

* publishes nothing, exits 6 and names the checker when any checker
  rejected any certificate during the run:

  ```text
  KM_LEAN_CHECKERS fail closed: elc-cert-check rejected the elc-publication certificate (ELC certificate rejected: … (exit status: 1)); no answer published
  ```

  This holds even when a fallback route answered after the rejected worker
  declined, which is the case that published silently before.

`KM_LEAN_CHECK_MAX_BYTES` caps the certificate size; a larger certificate is
`cannot_check` and the checker does not run.

### 2.1 Exactness argument

The switch changes which answers are published, never what an answer is.

* ELC: with a checker set, the ELC worker skips the inverse-bridge
  preparation (a residual-shrinking rewrite outside the Lean source theorem)
  and declines whenever the certificate cannot be built or is not accepted.
  A decline sends the input to the exact fallback route, as an ordinary ELC
  decline does. The ELC answer itself is computed by the same completion.
* CB: certified mode keeps every query root, disables the mutual-unit
  collapse and runs one thread. These are schedule and query-set changes of
  the same monotone saturation; the derived set for the published subjects
  is unchanged (`tests/cb_live_state.rs`
  `provenance_schedule_preserves_the_uncertified_answer`). Certified mode
  also forces the unordered literal regime (`calc::set_seq_order_auto`). In
  nominal mode that regime is incomplete (`docs/PER-CONTEXT-ORDERING.md`
  section 4: `p1`, `p2`), so `KM_LEAN_CHECKERS` does not certify a CB worker
  that runs with `KM_NOMINALS`; it reports `cannot_check` and the worker runs
  in its ordinary regime. When the typed source does not compile or the
  certificate cannot be produced, the worker publishes the answer it computed
  and reports `cannot_check`. The in-process CB fast path is turned off
  (`KM_NO_INPROC_ENGINE=1`) so that small inputs reach the worker; the fast
  path publishes the same bytes as the worker.
* HT: certified HT is a different publication mode (global decision plus
  checked runs). On the automatic route most HT workers then decline, and the
  exact fallback answers. That keeps answers but changes routes and costs
  time, so HT checking is opt-in (`KM_LEAN_CHECKERS_HT=1`); by default an HT
  worker records `cannot_check`.
* A rejected certificate means the worker's answer or its certificate is
  wrong. Publishing the fallback's answer would hide that, so the run fails
  closed.

Lean obligation created: none new. The switch only invokes existing checkers
on documents the workers already emit; acceptance proves what section 1
lists. What remains unproved is unchanged: the frontend, the IRI mapping,
and completeness of each procedure.

### 2.2 Why it is not on by default

The suite (section 3) shows that the checkers reject or cannot check most
published answers today: with the switch on, `km classify` fails closed on
231 of 1,781 inputs (ELC rejections, mostly E1) and
loses 380 more to certificate cost, while no answer changes. The default
stays off until the defects of section 3.3 are fixed.

## 3. The suite

`tools/checkers-on-suite.sh` runs `tools/checkers_on_suite.py` on the fixed
input set: every ontology under `engine/tests/fixtures/`, a deterministic
sample of the generated seed families of 2026-10-28 to 2026-10-30, and the
ORE design-half inputs of `results/benchmarks/2026-10-26-v154-routing/` that
v1.5.3 answered within 60 s. Each input runs in mode `off` (no checker), `on`
(`KM_LEAN_CHECKERS`) and `ht` (`on` plus `KM_LEAN_CHECKERS_HT=1`), four runs
at a time, one thread each, 60 s each. Per input it records the route, the
answer digest, the gold verdict where a cached HermiT answer exists, every
checker event, and the wall time.

Results: `results/agents/2026-10-30/checkers-on-suite/` (README and
`summary.md`). On 1,781 inputs:

| mode | accepted | rejected | cannot check | over budget | no answer | answers changed | wall ratio |
|---|---:|---:|---:|---:|---:|---:|---|
| `on` | 34 | 231 | 1,014 | 380 | 122 | 0 | 1.16 |
| `ht` | 34 | 365 | 662 | 595 | 125 | 0 | 1.81 |

### 3.1 What the checkers cover today

* Only 34 of the 1,657 answers the unchecked run publishes are covered by an
  accepted publication certificate, all of them ELC certificates of
  existential-free inputs.
* CB: the publication checkers accept CB certificates of plain clause sets
  (88 acceptances in mode `ht`), but on the automatic route the CB worker
  rarely publishes first, nominal-mode CB is not certified (the certified
  regime is incomplete there), and the typed source declines several
  constructors.
* HT: no HT certificate is produced on the automatic route even with
  `KM_LEAN_CHECKERS_HT=1`. The Konclude-port bridge, which answers most HT
  inputs, has no Lean model, and certified HT requires the global decision
  route.
* 380 inputs that answer within 60 s without checkers do not finish with
  them: ELC certificates reach 90 MB and the checker needs minutes.

### 3.2 Rejections

Every rejection is listed with its minimal input in the results README.
None hides a wrong answer: each minimal input agrees with HermiT, and every
cached HermiT answer agrees with every published answer. They are defects
of the certificate producers or of the wire contracts:

* E1, ELC, every input with an existential restriction:
  `checkNormalizationV5` accepts no Skolem half outside a canonical-witness
  record, and the producer writes witness records only for residual
  compilations.
* E2, ELC on `production_all`, disjointness: the normal form `A ⊓ B ⊑ ⊥`
  mentions ⊥, which `checkSignatureClosed` requires to be active and
  `checkActiveConcepts` requires to be inactive.
* C1, CB with a functional property: the typed source compiles but the
  decoded ontology differs from the checker's encoding.
* C2, C3, CB production taxonomy: a standalone trace that omits its claimed
  result, and a production-trace justification that does not decode.
* H1, HT verdict certificate: `ht-cert-check` cannot decode the global
  decision document (`node_count`); no gate runs this checker.

### 3.3 Before the checkers can be on by default

E1 and E2 must be fixed (producer or checker; each fix changes a Lean
checker's input contract or the checker itself and needs the ELC gate), C1
must decline instead of emitting a mismatched document, and the ELC
certificate needs a size or time budget that falls back to the unchecked
route instead of timing out.

## 4. Rust tests that need real checkers

`lean/checker-env.sh DIR` exports every checker variable the gates use
(production and test names), plus the HT test variables no gate exports, for
a directory of built checkers. `lean/run-checker-tests.sh DIR` runs the 22
tests of the CI skip list (`.github/workflows/ci.yml`; 21 match `tableau::`,
one is `cli::cb_derivation_candidate_tests`), the three integration tests
the CI skips, and `tests/lean_checkers_dir.rs` against them, without
rebuilding Lean. With the v1.5.4 checkers all 22 pass when run one at a
time. Run them serially: in parallel the checkers can fail to start threads
on a host near its memory commit limit, and the hypertableau search counts
such a failure as a rejected candidate. The whole lib suite under the full
checker environment is not a valid configuration: eight production-path
tests assume no certified mode.

## 5. Certificate defect fixes (2026-10-30, agent `certificate-defects`)

Branch `fix/v155-certificate-defects`. Each fix keeps the statement of every
publication theorem; where a Lean check changed, the old check is implied by
the new one or the new hypothesis is weaker. Results:
`results/agents/2026-10-30/certificate-defects/`.

### 5.1 ELC (E1, E2, dead witnesses, cost)

* **E1, existentials.** The v5 checker normalizes the direct partition with
  `certifyRawDirectToNormal`, which accepts no Skolem half; a Skolem pair is
  accepted only through a canonical-witness record. The producer wrote
  records only for functions a compiled residual uses. Fix (producer):
  `build_lean_source_partition` gives every other Skolem function an
  *identity* record (`witness = filler`) and the certificate ontology gains
  the tautology `filler ⊑ filler` the record requires. Exactness: the
  saturation is unchanged (the NF3 clause keeps its filler; the added NF1 is
  valid in every interpretation and its closure obligation holds by
  reflexivity), so the published answer is the same; the record's proof
  (`materialized_rewrittenExistential_satisfies_raw`) pins the function to the
  filler's canonical node, which every element below `sub` reaches by the NF3
  edge. Lean obligation: none new (the existing witness-record theorem
  covers `witness = filler`). A function whose pair is not in the source (a
  role half without a filler half, filler ⊤ or ⊥) gets no record and is still
  rejected.
* **Dead witnesses.** With a record for every existential, `D ⊑ ∃r.A` with
  an unsatisfiable `A` was rejected: `checkWitnessRecords` required the
  witness alive. The proof does not need it: if the witness is dead, every
  element below `sub` reaches it by an NF3 edge and is dead by the ⊥-edge
  closure, so both Skolem clauses hold vacuously on the alive domain.
  `CanonicalWitnessRecord.MaterializedValid` drops the aliveness conjunct
  (proof in `materialized_witnessRecords_satisfy_raw`), `checkWitnessRecords`
  requires the witness active only, and `functionBindings` pins only records
  with an alive witness (the pin of the others is unconstrained). Lean
  obligation: done (no `sorry`; axioms `propext`, `Classical.choice`,
  `Quot.sound`).
* **E2, ⊥ in a normal form.** `checkSignatureClosed` required every concept
  of every clause to be active, `checkActiveConcepts` requires ⊥ inactive, so
  `nf2 A B ⊥` (DisjointClasses on the `production_all` EL arm) could never
  pass. `SignatureClosed` now takes `bottom` and exempts it; its only use (the
  NF3 filler case of the canonical-model proofs) derives `filler ≠ bottom`
  from aliveness. This weakens a hypothesis of the exactness theorems; their
  conclusions are unchanged.
* **Residuals that do not hold.** The Lean checker evaluates every compiled
  residual clause on the finite canonical model, as Rust's
  `check_certificate` does. When Rust's check fails, the producer no longer
  writes a certificate (which Lean would reject, failing the run closed); it
  records `cannot_check` and proceeds as an unchecked worker (decline in
  Check mode).
* **Cost.** Producer: the formal closure that reconstructs the trace was a
  round-based loop over all facts times all normal forms; it is now a
  semi-naive worklist with premise indexes (the same least fixpoint; it is
  still compared with the production state), and the certificate is written
  through a buffer. Checker: `checkV5` tests every membership against a
  `List`, which is quadratic in the trace (NF4 and NF7 closure worse).
  `ELCompletionFastCheck.lean` defines `checkV5Fast` with hash sets and
  premise-indexed clause tables and proves `checkV5Fast = true → checkV5 = true`
  (`WireCertificate.checkFast_publication_semantics`); `elc-cert-check` runs
  it. On `ore_ont_10254` (0.9 MB ontology, 87 MB certificate, 532,564 steps):
  producer 180 s → 3 s, checker from no verdict (the old check ran past
  minutes; the 125 s figure of section 3 was an early rejection) to 16-25 s,
  whole checked run 27 s.
* **Budget.** Under `KM_LEAN_CHECKERS` (not in strict `KM_ELC_LEAN_REQUIRED`
  mode, and not when `KM_ELC_LEAN_CERT_OUT` asks for the file) the ELC worker
  writes no certificate when its closure holds more than
  `KM_LEAN_CHECK_MAX_ELC_FACTS` facts (default 1,000,000; `0` disables), records
  `cannot_check` and publishes its unchecked answer, as the CB worker does
  when it cannot certify. Acceptance of the certificates that are produced
  proves what it did before.

### 5.2 Checker process start-up

`lean_checkers::CheckerCommand` is the one way KM starts a Lean checker
(it replaces `lean_checker::run`, merged from `fix/v155-lean-rules-route`):
the `main` thread gets a 256 MiB `LEAN_STACK_SIZE_KB` unless the caller set
one, and the runtime's start-up abort ("failed to create thread", SIGABRT) is
retried with growing pauses for about 5 s. A checker dies with the thread
that started it (`PR_SET_PDEATHSIG`) and is killed after
`KM_LEAN_CHECK_TIMEOUT_SECS` (default 900 s); a killed checker is no
verdict (`cannot_check`). Every other exit is returned unchanged, so a
rejection still fails closed. The Lean runtime's "INTERNAL PANIC: out of
memory" (exit status 1) is reported as no verdict, not as a rejection. Every checker spawn in `cli.rs`,
`tableau.rs`, `hypertableau.rs`, `elcomplete.rs` and the rules modules goes
through it.

### 5.3 CB (C1, C2, C3, B1, B2)

Details, exactness arguments and Lean obligations:
`docs/CB-CERTIFICATION.md`, "Checkers-on certificate defects C1-C3, B1, B2
(2026-10-30)". In short:

* **C1** (functional and inverse-functional roles): the worker's clause uses
  other variable names than the proved encoding. `CBSourceWire` now accepts
  clauses that are mutual instances up to literal sets (`ClauseVariant`;
  validity and predicate bodies are preserved, proved); the old equivalence
  implies the new relation.
* **C2**: a standalone local trace ended in a literal-order variant of its
  claimed clause; the producer now writes the claimed clause into the last
  set-equal trace entry (the step check is invariant under set equality).
* **C3**: the filtered-seed evidence wrote `{"assumption": n}` instead of
  `{"assumption": {"index": n}}`; fixed in the producer.
* **B1**: `cb-live-taxonomy-publication-check`,
  `cb-live-exact-taxonomy-publication-check` and `cb-terminal-state-check`
  read a global-model document (global closure plus blocked saturation)
  that no production code builds. `KM_LEAN_CHECKERS_SET=all` no longer turns
  them on and records `cannot_check` for each; set by hand they still run and
  fail closed.
* **B2**: layer 1 fixed (the r-Succ sweep flag stayed set when no reach
  predicate exists; the engine clears it, no message changes). Layer 2 is a
  missing proof: the six Hyper-based closure checkers enumerate
  substitutions that move the central variable, which the CB Hyper rule
  never applies; restricting `hyperCandidates` needs a re-proof of the
  canonical-model step from Pred/Succ closure. Not done.
