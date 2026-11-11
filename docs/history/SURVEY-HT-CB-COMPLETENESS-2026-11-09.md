# Survey for v1.6.0 phases 2 (HT) and 3 (CB)

Worktree: `.work/worktrees/v1.6.0`, Lean sources `lean/ContextCalculus/` (abbreviated `L/`).
All line numbers refer to that worktree. Read-only survey; nothing was built.

## Bottom line

| Item | State | Executable Lean today? | Feasibility of reference procedure |
|---|---|---|---|
| A. HT regular totality | Theorems are conditional on a producer family; producers are never built in Lean | No (every search function is `noncomputable`) | Medium-high effort for the equality-free regular fragment; blocker-completeness obligation (`frontierAddress`) is the crux |
| B(a). CB, ALC-shaped, equality-free | Semantic completeness for ALC exists (type elimination, `CBALCEncoding`); production-calculus completeness does not | Only a `noncomputable` Finset type elimination | Feasible if the reference does not have to mimic the CB production DAG; hard if it must emit a CB wire document |
| B(b). CB, full language | Equality canonical model half built, unconnected; no termination; Nom, Eq, Succ, blocking rows open | No | Research scale; possibly not total for arbitrary role chains |
| C. Rules | Checker soundness only | No | Out of scope, as the plan says |

---

## A. Hypertableau totality

### A1. What a `CheckedRegularControlProducer` supplies

`CheckedRegularControlProducer` (`L/HypertableauRegularDecisionTotal.lean:450-458`) is one field:
`attempt : ∀ forbidden : Finset (Fin (8*2^budget) × Fin (8*2^budget)), CheckedRegularControlAttempt ... budget forbidden`.
So per budget it must answer for every forbidden-pair set, not only the ones a run reaches.
The theorem quantifies `∀ budget` (`:853-862`).

`CheckedRegularControlAttempt` (`:343-384`) has five constructors:

| Constructor | Data | Checked inside the type? |
|---|---|---|
| `regularSat` | `FiniteRegularCertificate`, `certificate.ontology = ontology`, `0 < nodeCount`, `certificate.check = true` | Yes, Boolean checker `check` (executable) |
| `finiteSat` | `FiniteSatCertificate`, same ontology equation, `checkSat = true` | Yes |
| `finiteUnsat` | certificate, `FiniteRefutationTree`, `EmptyRoot`, `tree.check certificate = true` | Yes |
| `frontier` | `WireAddressFrontier` document, concept/role counts, `document.checkScheduled budget = true` | Yes, but see A2 |
| `rejected` | `folds : Finset (pair)`, `fresh : ∃ fold ∈ folds, fold ∉ forbidden` | Only freshness; no semantic content |

`toGuarded` (`:396-410`) maps the first four to `.done` and `rejected` to `GuardedFoldAttempt.rejected`
(`L/HypertableauRegularProduction.lean:285-288`, `FreshFoldProducer.forbidden` grows by `current ∪ folds`).

Semantic correctness of the three certificate constructors is proved by
`CheckedRegularRoundOutcome.regularSat_semantics / finiteSat_semantics / finiteUnsat_semantics` (`:539-587`).
For the checker these state: `regularSat` and `finiteSat` imply `HasNonemptyModel target`, `finiteUnsat` implies `¬`.

### A2. Are always-`rejected` / always-`frontier` producers admissible?

Neither is admissible as a total producer, so the theorem is not merely about the schedule.

- Always `rejected`: `attempt` must be defined at every `forbidden`, including the full pair set, where `fresh` is
  unprovable. A producer must therefore return a non-`rejected` constructor once the finite blacklist saturates.
  This is the content of `fold_learning_eventually_done`, used in `checked_regular_fold_learning_doubling_decides`
  (`:665-699`).
- Always `frontier`: `checkScheduled budget = true` forces an injective rooted-address map from
  `Fin (8*2^budget)` into `WitnessAddress (Fin 1) (Fin c) (Fin r)` (`CheckedRegularControlAttempt.frontier_of_address`
  `:386-394`; `WireAddressFrontier.ofAddress_checkScheduled`). `mode6_doubling_eventually_rejects_checked_frontier`
  (`L/HypertableauFrontierWire.lean:270-276`) shows some round cannot pass. For large budgets the producer must
  therefore return a SAT or UNSAT certificate whose checker accepts.

Consequence, stated sceptically: `checked_regular_control_producer_decides_source` is "if a total family of checked
attempts exists, some attempt is conclusive and its semantics transfer through `ModelEquivalent`". Existence of the
family at large budgets is the decision itself. The theorem proves termination of the control loop (finite blacklist,
finite address space) and transport of the semantic claim. It does not prove that certificates exist. The only theorem
that argues existence from semantics is the exhaustive-search settlement (A3).

`checked_*_doubling_execution_decides_source` (`L/HypertableauProductionDecisionTotal.lean:558`, `:805`, `:1131`,
`:1525`) is weaker still: it takes a `CartesianFoldDoublingExecution` trace as an argument and proves soundness of the
traced outcome. It is a publication-soundness theorem, not totality.

### A3. Is anything constructed executably?

No. Grep over `L/*.lean` (excluding `.lake`) finds no `def`/`instance` of type `CheckedRegularControlProducer`,
`CheckedEqualityControlProducer`, `ConstructedRegularFiniteSearchFamily` or any other family; they occur only as
parameters (`ProductionDecisionTotal.lean:545`, `:2465`, `:2351-2400`).

What exists is a `noncomputable` existence package:

- `CartesianFoldExpansionRuntime` (`L/HypertableauExpansionProduction.lean:79-93`) is a structure of an inner runtime
  plus two invariants (`checkConclusive`, `expansionExact`). `.execute` (`:225`), `.settled` (`:418`),
  `.settledExecution` (`:427`) are `noncomputable` because they use `classical` choice over finite data.
- `ConstructedRegularFiniteSearchFamily` (`ProductionDecisionTotal.lean:506-542`) bundles `parent`, `ancestors`
  (the blocker, arbitrary functions), `branchable`, `guarded`, `frontierAddress`, `regularFallback`.
  `.runtime` (`:544`) is `noncomputable`, built from `ofConstructedRegularFiniteSearch` (`:458`) and
  `ofSettledProductionSearch` (`L/HypertableauRegularRouteProduction.lean:827`).
- `frontierAddress` is a proof obligation about the blocker: every node-exhausted search leaf has a checked rooted
  address (`:529-535`). Nothing in `L/` proves it for a concrete `parent`/`ancestors`. It is where blocking
  correctness lives.
- `regularFallback` returns `Option CheckedRegularFallbackCandidate` (`:266-280`), whose `check : certificate.check = true`
  is an executable Boolean. The function may return `none`; the search runtime then learns folds or settles on a
  fold-free terminal (`ProductionBlockedLeafAt.regularFoldFreeResult`). So a family with trivial `parent`, `ancestors`
  and `regularFallback := none` type-checks once `frontierAddress` is proved. I did not check that this makes the
  fold-free terminal path sufficient, so treat that as a hypothesis for phase 2.
- The search steps are `noncomputable` because they use classical selection, not because they are infinite:
  `allGroundings` (`L/HypertableauRuntimeSearch.lean:47`), `selectClauseGrounding` (`:198`), `selectUnwitnessed` (`:329`),
  `runtimeNextBlocked` (`:491`), `runtimeNext` (`:809`). Their statements (finite `Fintype` node, concept, role,
  variable universes) are executable in spirit, since `Fintype`/`DecidableEq` data exists.
- `finiteProductionRoundConstructionSettlement` (`L/HypertableauRegularDecisionTotal.lean:101-156`) is the settlement
  theorem as a `noncomputable def`: for a fixed budget it returns either a `ConstructedRegularRoundOutcome` or a
  blocked leaf that still needs the fold-assignment layer.
- End-to-end form: `checked_regular_finite_search_decides_source` (`ProductionDecisionTotal.lean:1726`) and
  `CertifiedHTAssignmentProductionGlobalRoute` (`:2459`). Both take the family data as arguments.
- `L/HypertableauExecutablePublicationWire.lean:24-31, 71-78` has wire-level publication checks for HT. They check a
  supplied document; they do not generate one.

### A4. Fragment covered by the regular theorems

- Clause type `Hypertableau.Clause (Fin v) (Fin c) (Fin r)` with atoms `concept lit`, `role`, `exists_`, `eq`
  (`L/Hypertableau.lean:50-60`).
- `Branchable` (`:279`) forbids `eq` heads, so the regular family is equality-free in heads.
- `GuardedBody` (`:439`) with `BodyAtom` (`:417`) allows positive concepts, roles and `eq` in bodies; it forbids
  `exists_` and negated concept tests in bodies. Negative concepts in heads are allowed.
- Roles: `FiniteRegularCertificate` carries `subRoles`, `inverseRoles`, `chains`, `reflexiveRoles`, `roleClauses`
  (`L/HypertableauRegularCertificate.lean:16-28`). So role hierarchy, inverse, chains and reflexivity are inside the
  certificate language of the regular family. The Rust wire sets `inverse_roles := []` for the plain regular wire
  (`HypertableauRegularDecisionWire.lean:119`), so check which checker constructor a given source reaches.
- `source`/`target` relation: `ModelEquivalent source target` (`L/HypertableauEqualityNormalization.lean:182`):
  equivalence over every `Domain : Type` and `Interp`. Normalisation (Skolem pairs, nominal handling, etc.) is outside
  the regular theorem.
- Nominals: equality family (`ConstructedEqualityFiniteSearchFamily`, `ProductionDecisionTotal.lean:765`), index
  `EqualityHasNonemptyModel`. Cardinality: `:1085`. Native ABox with cardinality: `:1478`. These are four separate
  families, `CertifiedHTProductionGlobalRoute` at `:2351`. Phase 2 as drafted ("equality-free ALCH-shaped") covers
  only the first.

### A5. From `CheckedRegularRoundOutcome` to the common routing source

Direction of the existing bridge is HT to FCL, not FCL to HT.

- `HTCheckerTermEmbedding.encodeClause` embeds `Hypertableau.Clause Nat Nat Nat` into `FCL`
  (`L/HTCheckerTermEmbedding.lean:26-40`, direct existential-free case).
- `KMCommonRoutingSource.directHTOntology` (`L/KMCommonRoutingSource.lean:119-121`) maps a clause list;
  `entails_directHTOntology_iff` (`:123`) and `unsatisfiable_directHTOntology_iff` (`:130`) are definitional unfoldings.
- `HTRoutingSource.Source` (`L/HTRoutingSource.lean:25-29`) is `direct` clauses plus Skolem pairs with distinct function
  keys; `Source.target` projects pairs to `exists_` atoms; `entailsSub_iff_target` (`:60`).
- `HTDirectTaxonomyCommonPublication.DecodedDirectTaxonomyPublication.common_semantics` (`:71`) states the taxonomy
  published by an HT wire document equals `CommonEntailsSub (mapOntology ...)`.
- There is no inverse: nothing recognises a `List FCL` as HT clauses. Grep for `recogni` finds only
  `ELCommonSourceRecognizer`. Phase 2 needs a recogniser `List FCL → Option (HT clauses over Fin)` (or over Nat then
  `mapOntology` to `Fin`) with an iff theorem, analogous to `recognizeEL_entails_iff`. It must also handle Skolem
  function symbols (existentials arrive as `app` terms, cf. `HTRoutingSource`).
- Granularity. `CheckedRegularRoundOutcome` and `CertifiedHTGlobalVerdict` (`ProductionDecisionTotal.lean:104-106`)
  decide one global question (`HasNonemptyModel source`). A taxonomy needs
  `CertifiedHTProductionTaxonomyRoute` (`L/HypertableauProductionTaxonomyTotal.lean:381-401`): one run per named
  concept (`conceptRun`) and per ordered named pair (`subsumptionRun`), each a `CheckedTaxonomyRoundOutcome`
  (`:28-36`) with `holds`/`refutes`/`frontier`. `.decides` (`:403`) gives `CompleteTaxonomyCertificate`.
  The current publication endpoints are the complete-assignment ones (`L/HypertableauCertificationSurface.lean:1-12, 64-69`);
  the older producer interfaces are intermediate lemmas. Cell runs are rooted searches (the `Rooted*TaxonomyProductionRunWire`
  modules), which I did not read. A reference taxonomy therefore means 1 + n + n^2 root-seeded regular searches.

---

## B. CB completeness and termination

### B1. Inventory of the completeness chain

| Module (lines) | Main theorem(s) | Fragment | Assumed / supplied |
|---|---|---|---|
| `CompletenessProp` (366), `CompletenessClause` (320), `CompletenessOrdered` (199) | `ordered_completeness` (`CompletenessOrdered.lean:187`), `ordered_model_exists` (`:194`) | Propositional ground clauses; ordered resolution under one total order | A well-founded linear order on atoms |
| `CompletenessExchange` (781) | `exchange_refutation_complete` (`:412`), `exchange_unit_readout_complete` (`:437`), `downward_server_complete` (`:678`); `ordered_server_interface_not_lower_counterexample` (`:709`) | Ground core; server (nominal context) and consumer under unrelated ranks with an atom interface | Interface and rank conditions as hypotheses; counterexample shows they are needed |
| `CompletenessEq` (714) | `herbrand_complete_ground` (`:705`), `herbrand_complete` (`:517`) | `OClause` = gci, exR, allR, exL, subR, inv, func, nom, atMost, guardedAtMost, guardedAtLeast (`:91-102`). Equality, merging, nominals, inverse, hierarchy, number restrictions | Finite `T` with `wit`/`minWit`, and `¬ Derivable (ground ...) ⊥`. Header says the `≤n`, n>=2, pigeonhole step is "not unfolded here" (`:39-41`) while the final docstring claims atMost; reconcile before relying on it |
| `CBRoleChainGroundCompleteness` (334) | `quotient_models_source` (`:258`), `source_complete_ground` (`:283`), `..._nonempty` (`:305`) | `SourceOntology` = `OClause` list + arbitrary `RoleChain`s + `RoleAxiom`s (symmetric, asymmetric, reflexive, irreflexive, inverseFunctional, disjoint) (`CBRoleChainEncoding.lean:45-48`) | `hclash : ¬ Derivable (groundSource wit minWit source) ⊥` |
| `CBNamedGroundCompleteness` (132) | `source_complete_ground_named(_nonempty)` (`:97`, `:111`) | Same, with a separate individual type | Same |
| `CBBlockedGroundSaturationWire` (147) | `source_model` (`:108`), `check_sound` (`:~126`) | Blocked ground set of the production source; carrier, witness table and terminal saturation are in the document | Terminal saturation is supplied and checked (`Saturation (encodedBlockedGround ..) terminal`), not computed |
| `CBBlockedCarrierWire` (213) | `WireBlockedCarrierDocument.decode` (`:~40`) | Carrier size = ordered production terms; witness table row-major | Wire-supplied witnesses |
| `CBSourceCanonicalClosure` (102) | `check_sound` (`:79`), re-exported as `certifiedCBSourceCanonicalClosure` (`CBCertificationSurface.lean:~321-337`) | Production-closed document plus computed linear extensions for root and non-root literal orders | Document from Rust |
| `CBSourceCanonicalOrder` (141) | `canonical_max_is_production_maximal` (`:117`), `production_le_implies_global_le` (`:79`) | Global well-founded order on `FLit` extending the checked rank | Checked extension |
| `CBSourceEqualityFreeCompleteness` (238) | `SourceProductionClosed.ordered_candidate_source_instance_eqFree` (`:132`), `all_context_source_instances_eqFree` (`:203`) | Source and retained clauses equality-free (`EqFree`) | Hypotheses `hbot` (no `⊥` retained), `hsourceFree`, `hretainedFree`. Concludes: the ordered candidate valuation `Itrue (rawSet retained)` satisfies every substitution instance of every source clause. It does not conclude a model of the source theory or an `Entails` equivalence |
| `CBSourceEqualityCanonicalModel` (1532) | Last theorem `productiveGroundValuation_of_Itrue_positive` (`:1453`); `productiveQuotientModel` (`:1165`), `productiveQuotientModel_equality_of_true` (`:1288`), `evalGroundLiteral_productiveGroundValuation_iff` (`:1422`) | Equality extension: oriented rewriting, class normal forms, congruence quotient | See below |
| `CBNominalAllocationWire` (659) | `check_sound` (`:213`), `check_family_sound` (`:248`), `escape_of_valid_counting_premise` (`:307`), `emitted_conclusion_sound` (`:347`) | Nom rule: allocation of fresh individual blocks | Soundness side only; no completeness |
| `CBCertificationSurface` (518) | `certifiedCBProductionExactTaxonomyPublication` (`:382`), `certifiedCBClashFreeGlobalProductionModel` (`:86`), `certifiedCBSourceCanonicalClosure`, `certifiedCBSharedProductionTaxonomyPublication` (`:~108`) | Accepted wire document | Checker soundness plus exactness: for an accepted document, `answer = true ↔ SourceExactEntails live` (`:390-396`). Positive cells carry chronological derivations, negative cells carry finite, blocked or regular countermodels |

`CBSourceEqualityCanonicalModel` (what is proved, what is open). Its docstring (`:3-9`) says it "begins the equality
extension". The module proves: retained equalities orient strictly downward (`retained_equality_strictly_decreases`
`:213`), the productive rewrite relation is well-founded (`productiveEqualityRewrite_wellFounded` `:304`,
`productiveClassRewrite_wellFounded` `:372`) and directly joinable (`:386`), normal forms are unique on
equivalence classes (`:475, :542`), a quotient model is built (`:1165`), and it satisfies the true positive atoms
(`:1453`). Missing is the equality analogue of `all_context_source_instances_eqFree`: the theorem that the quotient
model satisfies every source instance, and the link to a model of the source ontology. No other `L/` module imports it
(only `ContextCalculus.lean:73` does). The "Eq" row in `docs/CB-RULE-CERTIFICATION.tsv:7` lists the same open item
(canonical-model ordered paramodulation).

Two distinct completeness routes therefore exist, and neither is an executable procedure:

1. Blocked ground route (`CBBlockedGroundSaturationWire`): a finite carrier and witness table from the document, ground
   resolution saturation from the document, `¬⊥` gives a model of the full `SourceOntology` through
   `source_complete_ground_named_nonempty`. This covers equality, nominals, inverse, hierarchy, number restrictions and
   arbitrary chains for the model-existence direction only, because the ground theorem requires the carrier to be
   supplied.
2. Canonical production-closure route (`CBSourceCanonicalClosure` to `EqualityFree`/`EqualityCanonicalModel`): works
   from the Rust production fixpoint, equality-free finished, equality partly.

The converse that a reference procedure needs for totality is absent in both: if the source has a model, then the
chosen finite carrier (or the production closure) is clash-free. The model-existence theorems are "no `⊥` implies model".
"Model implies no `⊥`" holds for any grounding by `derivable_sound`, but only for groundings that the model satisfies,
and a model satisfies a particular finite grounding only if the carrier and witness functions are chosen to fit that
model. That is a finite-model/blocking argument, and `Termination.lean` explicitly does not provide it (B3).

Negative cells for ALC-shaped and richer sources are also covered by the HT bridge: `CBRegularALCCountermodel`
(`:1-15`) turns a checked regular HT model into an ALC model and installs CB Skolem functions via
`CBALCEncoding.models_extend`; `CBRegularNominalCountermodel`, `CBRegularCardinalityCountermodel`,
`CBRegularFreshCardinalityCountermodel`, `CBRegularArbitraryChainCountermodel` (restricted `SafeSource` with binary
chains, `:15-19`) extend it. These depend on the phase-2 HT work for their inputs.

### B2. Executable CB saturation?

None in Lean returning data.

- Grep for `def saturate|fixpoint|closure` in `L/CB*.lean` and `L/Completeness*.lean` yields only wire decoders and
  `...ClosedAt` Props (`CBGlobalProductionClosure.lean:42-153`). `Saturation` is a Prop; the saturated terminal is read
  from the document and checked (`CBBlockedGroundSaturationWire.lean:~126-130`).
- Executable one-step enumerators do exist and are used to check closure: `CBHyperClosure.substitutions`
  (used at `CBSourceEqualityFreeCompleteness.lean:195`), `CBLocalEqEnumeration`, `CBPredEnumeration`,
  `CBPredSendEnumeration`, `CBRootPredSendEnumeration`, `CBJoin3Closure`, `CBLocalResolutionClosureWire`. A saturation
  loop could reuse them as step functions, but each is shaped as "verify the document's list is complete", so
  repurposing them is real work.
- The only saturation function is ALC type elimination, `CompletenessStrategy.saturate` (`:229`, `noncomputable` Finset,
  `open Classical` in `CompletenessContext.lean`). Statement: `mem_saturate_iff_good` (`:255`), `saturate_decides`
  (`:271`), fixpoint in at most `|cand|` rounds (`exists_fixed` `:210`). The file states (`:1-8, 50-60`) that no theorem
  identifies a production terminal state with this fixpoint and that the engine's disjunctive-clause saturation computing
  `goodFS` "is a substantial theorem that is not claimed here".
- ALC bridge to CB terms: `CBALCEncoding` (415 lines) encodes `Ctx.Clause` (gci, exRight, exLeft, allRight) to `FCL`
  with indexed unary Skolems; `entailsSub_iff_good` and `finite_countermodel_of_not_entailsSub` (`CBALCEncoding.lean:~383`)
  give an exact semantic equivalence and a finite canonical countermodel. `CompletenessContext.lean` header (`:40-44`)
  says role hierarchies, nominals, number restrictions and inverse roles are not covered there.

### B3. Termination

- `Termination.lean`: `branch_depth_bound` (`:49`), `no_infinite_branch`, `reachable_finite`, instance
  `Fintype (blockedUniverse CN)` (`:88`), `context_branch_bound : BlockedBranch br → br.length ≤ 2 ^ Fintype.card CN`
  (`:92-96`). It is a statement about duplicate-free lists of `Finset CN`. Its own docstring (`:4-9`) says it does not
  prove that blocking preserves models, that production contexts are branches of this universe, or that production
  saturation terminates.
- `docs/CB-RULE-CERTIFICATION.tsv:20` (last row): "Blocking/core-growth | Termination and abstract strategy theorems only |
  Not refined to Rust state | Bind finite context keys, trigger growth, blocking, and abstract complete fixpoint".
  Row 19 (Queue-terminal) lists as open "Emit the complete nested document from live Rust state and prove that this
  production-rule closure constructs ...". Rows 14 (Nom) and 7 (Eq) also list open obligations.
- Hence there is no termination theorem for the CB calculus on any fragment, including function-symbol growth from Skolems.
  The ALC type-elimination bound `|cand| <= 2^|CN|` is the only termination argument, and it belongs to a different
  algorithm.

### B4. What a Lean-executable reference CB procedure would still need

(a) ALC-shaped equality-free sources.

1. Recogniser `List FCL → Option (Ctx.Ontology (Fin n) (Fin m))` that inverts `CBALCEncoding.encode` (gci, exRight with the
   Skolem pair, exLeft, allRight), with an iff on entailment. Same shape as `recognizeEL_entails_iff` (109 lines).
2. A computable type elimination: replace the classical `Finset` filters in `CompletenessContext`/`CompletenessStrategy`
   by `List`-based decidable functions and prove it equals `saturate`. Exponential in `|CN|`; fine for an idealised reference.
3. Publication. This is the expensive part. A CB publication is a `WireLiveExactTaxonomyPublication`
   (`CBLiveExactTaxonomyPublication.lean:496`, soundness `certifiedCBProductionExactTaxonomyPublication`): positive
   cells need a chronological production derivation accepted by the CB proof checker, negative cells need a countermodel
   document (`CBFiniteModelWire`, `CBRegularALCCountermodelWire`, `CBBlockedTaxonomyCountermodelWire`). Type elimination
   gives the verdict and the finite model (`finite_countermodel_of_not_entailsSub`) but no derivation. Generating CB
   derivations from an elimination run needs a proof-extraction argument that does not exist.
   If the reference may instead publish through a different accepted checker (for example via the HT route for ALC-shaped
   sources, whose clause bridge `CBRegularALCCountermodel` already exists), item 3 shrinks to routing.

(b) Full language.

1. Everything in (a) minus the finite-type assumption: finite model property fails with nominals, inverse and
   cardinality together, so negative cells need regular countermodels (the HT side, phase 2) and positive cells need
   refutation completeness of the production calculus on the full language.
2. Equality canonical model: finish `CBSourceEqualityCanonicalModel` (source instances satisfied by the quotient model,
   including negative literals, role literals under congruence) and a combined theorem "closed + `⊥` absent implies model
   of the typed source".
3. Nom, Succ, r-Succ and ordering rows in `CB-RULE-CERTIFICATION.tsv` (rows 7, 14, 20): completeness-relevant but
   currently only soundness/closure checking.
4. An executable saturation and a termination theorem refined to it (finite context keys, core growth, blocking).
   Nothing exists; `Termination.lean` is a library of abstract bounds.
5. Decidability caveat: `RoleChain` is an arbitrary `body ⊑ sup` (`CBRoleChainEncoding.lean:16-19`) with no regularity
   condition, and `CBRegularArbitraryChainCountermodel` restricts to binary chains (`:15-19`). If the frontend can emit
   non-regular chain sets, no total reference procedure exists for the full accepted language. Confirm what the frontend
   guarantees before fixing the fragment.

---

## C. Rules

`docs/DL-SAFE-RULES.md` "Lean coverage (2026-10-30, v1.5.5)" (`:207-340`):

- Semantics (`RulesRouteSemantics.lean`, 440 lines): `clauseModel_of_dlSafeModel`, `dlSafeModel_of_clauseModel` make the
  guarded clause list exact for DL-safe rules.
- Certificates: closed tableau (`RulesRouteRefutation`, 610 lines), finite model (`RulesRouteModel`, 364 lines,
  `FModel.check_sound`), answer (`RulesRouteCertificate`, 342 lines, `Certificate.check_sound` `:156`,
  `WireRulesCertificate.check_sound` `:325`).
- Statement proved is checker soundness: if `check` accepts, the published answer is exact for `decode O nominals ontology`
  (consistency flag, unsatisfiable classes, subsumptions), relative to premises.
- No completeness statement. Nothing says the rule tableau (`tableau.rs` careful expansion) closes or yields a model on every
  input, and there is no termination or blocking-correctness theorem for it. Grep for `complete` in `Rules*.lean` finds only
  the helper lemma family `cands_complete`/`extComplete`/`predComplete` (candidate enumeration inside the model checker).
  The doc itself notes the composition of rule-route premises with the CB taxonomy is unproved (`DL-SAFE-RULES.md:~315`).
- The tableau's model side relies on pairwise blocking folding, with a Rust pre-check choosing among completion graphs, so a
  reference would also need blocking correctness for DL-safe rules with equality.

---

## D. Feasibility

### D.A HT (phase 2)

Write: (i) executable (computable) versions of the clause-first search of `HypertableauRuntimeSearch` (groundings, clash,
witness, fresh node) and of the blocker `parent`/`ancestors`; (ii) a proof of `frontierAddress` for that blocker, which is the
blocker-completeness theorem; (iii) an executable reference that, for each budget and forbidden set, returns a
`CheckedRegularControlAttempt` (or builds the `ConstructedRegularFiniteSearchFamily` with executable fields), and an outer
doubling loop with the termination argument already available from `mode6_doubling_eventually_rejects_checked_frontier`;
(iv) a recogniser from `List FCL` to HT clauses with its iff; (v) taxonomy assembly: 1 + n + n^2 root-seeded runs into
`CertifiedHTProductionTaxonomyRoute`. The control-flow theory (learning, doubling, transport) is done; I estimate new code
at a size comparable to `HypertableauRuntimeSearch` plus `HypertableauRegularRouteProduction` (about 2,000 lines), with the
recogniser and taxonomy assembly adding a few hundred. Main risk: `frontierAddress`. It couples a concrete blocker to the
address-refinement checker (`HypertableauAddressRefinement`), and nothing in `L/` proves it for any blocker. Secondary risks:
the fragment is equality-free heads only, so nominals, equality and cardinality sources (the `nominals`/`production_all`
routes) are not covered; and the executable `Fin (8*2^budget)` universes make a naive implementation very slow, which only
matters for tests, not for the theorem.

### D.B(a) CB, ALC-shaped equality-free

Write: the recogniser (about 150 lines, mirroring EL), a computable ALC type elimination with equivalence to
`CompletenessStrategy.saturate` (about 300 lines on top of 680 existing lines), and then either (1) route the verdict through
the HT regular reference (cheap given phase 2 and `CBRegularALCCountermodel`, 177 lines) or (2) emit a CB wire document, which
needs derivation extraction from elimination failures and a serializer that passes `WireLiveExactTaxonomyPublication.check`.
Option (2) is a new piece of proof theory of unknown size (I would not estimate below 1,500 lines) and has no precedent in
the tree. Main risk: the publication format, not the decision. Decide first whether `CompleteAt` for a CB route may be
satisfied by a publication that did not come from CB.

### D.B(b) CB, full language

Write: finish the equality canonical model (the remaining statement is probably 500 to 1,000 lines given the 1,532 existing),
build an executable saturation with a termination proof and a blocking model-preservation theorem (both absent; the
latter is the research content of SHOIQ-style finite blocked completions), prove production-calculus refutation completeness
for the full language, and cover Nom and Succ rows. Main risk: scope and possible non-decidability for arbitrary role chains
(B4.b.5); the existing ground completeness gives only model existence for a supplied carrier. I judge this not achievable for
v1.6.0 without narrowing the fragment, and the plan already labels it research scale.

### D.C Rules

Write: a termination and blocking-correctness theorem for the DL-safe rule tableau (pairwise blocking with equality), a
completeness theorem "closed tableau or checked finite model exists", an executable Lean tableau, and a rules-source
recogniser. No existing module is a base for the completeness part; the soundness modules (about 2,300 lines) fix the
semantics only. Main risk: the tableau includes merges and nominals with blocking, so this is the same research problem as
B(b) plus rules. Out of scope for v1.6.0, consistent with the plan (`docs/V1.6.0-COMPLETENESS-PLAN.md` section 3 table).

Report path: `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/v160/survey-ht-cb.md`
