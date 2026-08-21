# Changelog

## [unreleased]

### Make the regular hypertableau model checker exact

- Prove that the executable endpoint-role cover scan accepts every finite
  `CoverClosed` witness, complementing its existing soundness theorem.
- Prove that the complete regular-model checker accepts every certificate
  satisfying its finite `Valid` invariant. Checker acceptance is now
  equivalent to that invariant, including role-rule authorization, guarded
  residual clauses, clash freedom, witness completion, blocker redirection,
  endpoint-role closure, and residual-clause discharge.
- Lift exactness through the decoded wire certificate. A mathematically valid
  decoded regular model cannot be rejected because the executable checker
  missed a case. The remaining totality obligation is to prove that Rust's
  blocked-open serializer always constructs this `Valid` invariant.
- Prove a conditional producer-refinement bridge: ordinary residual saturation,
  authorized role-rule partitioning, clash and witness invariants, blocker
  redirection, and a closed endpoint cover force checker acceptance when that
  cover is contained in the serialized completion graph. The proof audit later
  showed that literal containment is sufficient but not necessary for blocked
  sources, so this theorem is not claimed as the final production bridge.
- Keep raw blocked edges separate from redirected endpoint-cover edges. The
  serializer submits the exact enlarged cover to the independent Lean residual
  checker; rejection resumes iterative deepening. This restores cyclic regular
  models that were incorrectly rejected by the stronger literal-containment
  condition.
- Classify the concrete blocker-aware selector's empty result exactly. It is
  either a refutation, a clash-free and clause-saturated blocked-open terminal
  in which every unwitnessed source is marked blocked, or a finite-node
  frontier containing an unblocked unwitnessed obligation. There is no hidden
  fourth outcome that the producer could publish as SAT.
- Replace blocked outgoing-edge materialization with the exact redirected-
  witness invariant used by the regular unravelling. Given checked fold
  metadata, every obligation has a witness edge at its redirected endpoint.
  The serializer now retains the raw saturated graph instead of adding edges
  that could activate new residual-clause bodies.
- Compose those results with regular checker exactness in
  `HypertableauRegularProduction.lean`. Clash freedom, redirected witness
  completion, and saturation now follow from the concrete blocked runtime
  terminal and checked fold metadata; they are no longer independent
  serializer assumptions.
- Prove total checked equality-free iterative deepening with the correct SAT
  semantics. A conclusive open round now carries a regular-unravelling
  certificate, a closed round carries a finite refutation, and a checked
  full-address frontier is the only inconclusive result. The finite blocking
  bound proves that doubling cannot return frontiers forever.
- Construct that conclusive regular SAT outcome directly from the concrete
  blocked runtime terminal and serializer-refinement invariants, deriving
  checker acceptance instead of assuming it. Transport both eventual SAT and
  UNSAT outcomes through the checked model-equivalent normalization, so the
  total doubling theorem now states the correct result for the original source
  ontology rather than only its normalized target.
- Match redirected-witness refinement to the exact model invariant: a blocker
  must provide the selected witness edge and filler label, but need not retain
  a redundant copy of the blocked node's obligation. Make the Rust regular
  equality-free loop run its intermediate Lean checker too; if a finite fold is
  rejected, iterative deepening now resumes instead of publishing a doomed
  candidate.
- Lift equality-aware and cardinality-aware doubling through exact model
  equivalence to their original source ontologies. Add a unified certified HT
  route theorem: regular equality-free, finite equality-quotient, and
  cardinality-aware searches all yield the same source-level SAT-or-UNSAT proof
  object, with cardinality definitions preserved explicitly.
- Close the missing positive native-ABox cardinality branch. An accepted
  quotient now proves, in the same interpretation, the normalized TBox,
  cardinality definitions, named-individual assertions, explicit differences,
  singleton proxies, and negative role assertions. Compose this with exact
  native-ABox initialization, checked closed refutations, model-equivalent
  source normalization, and cardinality frontier doubling to obtain total
  source-level SAT-or-UNSAT semantics for native-ABox cardinality search.
- Apply the same fail-closed iterative-deepening boundary to every taxonomy
  countermodel branch. Equality-free, equality-aware, anchored-equality, and
  cardinality cells now run their source-aware model checker before the search
  accepts an open fold; checker rejection increases the node bound instead of
  allowing the eventual matrix publication step to fail after search stopped.
- Add the first complete native-ABox global decision wire for the
  non-cardinality equality route. Lean now checks singleton proxy extensions
  and negative role assertions in the exact quotient model, combines them with
  seed preservation and explicit difference separation for SAT, and uses the
  exact native initial state for UNSAT. Rust selects this joint wire whenever a
  native ABox is active, requires its dedicated checker at the publication
  boundary. The same joint wire now covers cardinality-aware SAT and UNSAT:
  every accepted quotient checks the cardinality definitions, exact frontend
  recognition obligations, singleton proxies, role assertions, and explicit
  differences in one interpretation. Native taxonomy remains deferred until
  its corresponding source-composed wire is connected.

### Certify native named-individual ABox projection

- Define the exact semantics of KM's native ABox payload: singleton nominal
  proxies, positive class assertions, different individuals, positive role
  assertions, and negative role assertions.
- Prove that the named-root seed state is realized exactly when the positive
  ABox facts and explicit inequalities hold, given the checked singleton and
  negative-role obligations.
- Prove any later distinct-equality HT state that retains the named-root labels,
  edges, and apart facts realizes the original seed. This permits derived facts
  without weakening the source ABox obligation.
- Prove each guarded negative-role clash clause is equivalent to absence of the
  corresponding ground role edge, then lift this result to the complete list
  appended to a projected TBox.
- Add a finite decoder matching `NativeAboxJson`. It checks completeness,
  identifier bounds, nonempty proxy sets, nominal membership, unique proxy
  ownership, and exact three-field role assertions.
- Extend `ht-projection-cert-check` to accept native-ABox documents and make KM
  serialize the production payload for this checker.
- Add a joint finite-state wire with an explicit root map and exact equality,
  label, edge, obligation, and apart state. The checker proves the concrete
  certificate state contains every native seed fact and rejects short root maps
  or omitted labels.
- Require that the checked native root map is injective. Lean now returns the
  injectivity proof as part of decoded evidence and rejects duplicate roots,
  preventing two source individuals from being silently represented by one
  finite node before equality reasoning accounts for such a merge.
- Make every independent HT certificate search initialize query root zero and
  one ordered root per native individual, with the exact proxy/assertion labels,
  positive role edges, and different-individual facts used by production HT.
  Invalid ABox indices now fail before evidence search. This removes the prior
  possibility of searching the TBox alone while the optimized graph used an
  ABox; publication remains gated until Lean composes this multi-root seed with
  the decision theorem.
- Define the semantic decision target for a normalized TBox together with its
  native ABox. Prove that a checked equality SAT state realizes its exact finite
  labels, edges, obligations, and quotient equalities, then compose this with
  the named-root seed into a model of the joint TBox/ABox problem.
- Add an executable apart-separation check and prove it excludes equality of
  every explicitly different pair. The joint wire now validates equality paths,
  rejects a terminal state that merges different individuals, and carries the
  resulting semantic proof into the native-ABox SAT composition theorem.
- State the exact semantic initialization contract needed by an ABox-aware
  equality refutation and prove that any checked refutation from such a state
  excludes a joint TBox/ABox model. Equality decision evidence now fails closed
  when native apart facts are present until its wire carries those facts; this
  prevents a SAT certificate from discarding `DifferentIndividuals`.
- Prove an executable exact-initial-state checker: labels and role edges are
  precisely the native ABox seed, obligations and equalities are empty, query
  root zero is reserved, and native roots are ordered nodes one through N.
  Compose this checker with the finite equality-refutation tree so an accepted
  untrusted payload proves the joint normalized TBox/native-ABox problem has no
  model. Keep the separate terminal-state checker permissive for soundly
  derived facts and use it to prove the corresponding joint SAT result.
- Reject zero-node native-ABox states before constructing quotient SAT evidence;
  the concrete HT search always contains query root zero, and the Lean wire now
  checks that production invariant explicitly.
- Add a dedicated Rust publisher for normalized TBox/native-ABox equality
  refutations. It emits the exact ordered multi-root state and apart facts and
  is accepted by the native Lean checker in a real Rust-to-Lean test. The
  ontology-only equality envelope remains fail closed on native apart facts,
  since its empty-root theorem is intentionally not reused for this joint
  semantic problem.
- Compose direct source projection and native-ABox refutation in one checked
  document. Lean decodes the source clauses against the same concept, role, and
  variable tables as the decision state, reconstructs all negative-role guard
  clauses at the shared variable width, checks the exact target ontology, and
  proves the original direct TBox plus native ABox has no model. A real
  Rust-to-Lean test accepts the complete document and rejects source omission.
- Extend the same single-document boundary to mixed direct/Skolem-pair sources.
  Lean quantifies over the source Skolem-function interpretation, reconstructs
  the existential target ontology, composes native negative-role guards, and
  proves source-plus-ABox unsatisfiability from the checked equality refutation.
  The production Rust evidence passes the native checker; deleting its Skolem
  pair is rejected.
- Prove the semantic preservation lemma required for bundle/RBox composition.
  A native ABox can be transported across a concept-signature extension when
  every ABox concept is a checked embedded source concept. Apply this to the
  concrete bundle construction: the target interpretation preserves native
  class, singleton, distinctness, positive-role, and negative-role semantics
  while satisfying the projected bundles and checked RBox/domain consequences.
- Complete the executable bundle/ABox composition. The combined decoder checks
  source bundles, function uniqueness, definer/source embedding injectivity,
  RBox paths, domain premises, the complete target ontology, and a target-to-
  source concept map. Every concept used by the ABox must map to its actual
  embedded source concept; arbitrary mappings for generated definers cannot
  justify ABox facts. Production Rust evidence passes Lean, while a forged ABox
  concept map is rejected.
- Test the real Rust-to-Lean path, including rejection of duplicate proxy
  ownership and missing nominal declarations. The test also caught and fixed
  the flat-JSON-triple wire representation before integration.
- Extend exact native-ABox initialization to distinct cardinality search. Every
  initial apart edge must now be justified by a decoded
  `DifferentIndividuals` fact; the checker rejects both a deleted source fact
  and an injected apart edge. A checked finite cardinality refutation tree from
  this state proves the normalized TBox, cardinality definitions, and native
  ABox jointly unsatisfiable.
- Add the corresponding Rust publisher and checker document. Cardinality
  certificate signature sizing now includes concepts and roles that occur only
  in the native ABox, fixing an omission exposed by the proof boundary. A real
  Rust-to-Lean test accepts an ABox-only at-most pigeonhole refutation with
  asserted distinct successors.
- Compose direct source clauses and frontend cardinality expansions with the
  exact native-ABox cardinality refutation. The combined decoder checks the
  direct target, definition values, exact-pair provenance, negative-role
  guards, and normalized ontology in one signature. Its Rust-to-Lean test
  accepts the genuine document and rejects a forged cardinality bound.
- Extend the same cardinality/native-ABox composition through mixed direct and
  Skolem-pair sources. Lean checks function uniqueness, reconstructs the exact
  existential target, validates cardinality provenance and ABox guards, and
  proves source-level unsatisfiability. The Rust-to-Lean test includes a live
  Skolem existential and rejects deletion of its source pair.
- Complete the bundle/RBox variant. Prove that one constructed target
  interpretation simultaneously preserves the checked native ABox and the
  renamed cardinality contract, rather than relying on unrelated existential
  models. The combined decoder validates bundle definers, role paths, domain
  premises, source-to-target ABox concepts, renamed cardinality definitions,
  exact-pair provenance, and the final ontology. Its Rust-to-Lean test exercises
  a generated definer and rejects a forged source cardinality filler.

Certified nominal/ABox routing remains closed until KM emits this joint seeded
state evidence with every TBox projection shape and the concrete search result.
No release is cut for this intermediate proof unit.

### Compose bundles, RBox evidence, and cardinality projection

- Prove the complete finite frontend cardinality family equivalent to an
  index-stable target contract: every definition remains directional and both
  members of each checked complementary pair are exact.
- Prove directional and exact cardinality semantics commute with concept
  renaming and compose with ontology renaming under a checked left inverse.
- Prove one satisfiability equivalence covering direct source clauses, all
  Skolem bundles, frontend cardinality expansions, and first-class target
  cardinality definitions in a shared interpretation.
- Extend that equivalence through checked role-inclusion/domain consequences
  and the target concept-table embedding used by production evidence.
- Add a combined finite wire that reuses the complete bundle/RBox decoder,
  checks cardinality definitions and disjoint complementary-pair indices over
  the source signature, and proves the resulting joint document sound.
- Make the native projection checker accept the combined document and make
  Rust emit it whenever complete bundle and cardinality evidence coexist.
- Resolve target cardinality marker/filler identifiers through the checked
  source name table; missing names fail closed instead of relying on numeric
  index coincidence.
- Exercise the real Rust-to-Lean path with valid evidence and reject an omitted
  target clause, a false RBox path, a missing source symbol, and forged
  exact-cardinality provenance.

No release is cut for this intermediate step. The next release requires the
complete executable source-to-HT projection boundary, including its combined
wire and production integration.

### Compose mixed Skolem-pair and cardinality projection

- Prove the mixed direct/Skolem-pair source semantics and all frontend
  cardinality families equivalent to their shared HT target in one finite
  interpretation.
- Add a combined wire that reuses the exact mixed projection decoder and checks
  cardinality definitions, disjoint pair indices, and exactness flags.
- Make Rust emit this document when mixed Skolem evidence and cardinality
  evidence coexist, instead of requiring an unavailable direct-only witness.
- Test the real Rust-to-Lean path with complete evidence and confirm that an
  omitted projected clause and forged exactness are rejected.

No release is cut for this intermediate step.

### Verify production bundle RBox evidence end to end

- Extend finite bundle evidence with concrete super-role paths and associated
  domain consequences.
- Preserve generated two-variable role-inclusion and role-domain clauses as
  explicit source premises instead of trusting Rust's closure result.
- Prove an arbitrary finite inclusion path entails its endpoint inclusion and
  compose that result with the complete bundle projection.
- Make the Lean wire verify every path edge, final domain premise, generated
  consequence, source symbol, and target clause extensionally.
- Connect Rust production evidence to the native checker and test a two-edge
  hierarchy against the real Lean executable. Complete evidence is accepted;
  omitted clauses and forged shortcut paths are rejected.

No release is cut for this intermediate step. It will be included in the next
major end-to-end certification milestone.

## [0.3.204] – 2026-08-21

### Compose bundle projection with role-domain consequences

- Define indexed domain-consequence evidence for every member of a finite
  Skolem-bundle family.
- Prove each generated `body → Domain(x)` clause follows from the matching
  projected existential, role inclusion, and role-domain premise in the same
  interpretation.
- Lift the proof to the complete finite list of domain extras emitted beside
  all bundles.
- Prove appending those justified extras preserves and reflects the model set
  of the complete bundle target ontology.

The executable wire still needs to reconstruct role-hierarchy paths and domain
premises from source clauses before production may use this theorem.
Cardinality replacement, nominal/ABox projection, the remaining HT audit, CB,
and routing certification remain unfinished.

## [0.3.203] – 2026-08-21

### Emit checked multi-filler bundle evidence from Rust

- Recognize only exact common-body multi-filler Skolem bundles with one role
  clause, at least two singleton filler clauses, unary `f(x)` wiring, and no
  bottom filler.
- Preserve the complete source concept table, direct clauses, function table,
  bundle bodies, fillers, roles, and generated definer names in `TInput`.
- Serialize production bundle evidence to the native Lean projection checker
  before checker-enabled HT publication.
- Add a real Rust-to-Lean test that accepts complete production evidence and
  rejects an omitted generated clause.
- Make concurrent projection checks use process-and-sequence-unique temporary
  filenames instead of racing on one process-wide path.
- Correct the nominal existential regression fixture to use the two
  singleton-head clauses emitted by sound normalization; disjunctive Skolem
  heads continue to defer and are never strengthened into conjunctions.

The complete release Rust suite passes 2,083 tests with 8 explicitly ignored.
Role-domain extras still make the exact bundle checker defer until their source
premises are wired. Cardinality replacement, nominal/ABox projection, the
remaining HT audit, CB, and routing certification remain unfinished.

## [0.3.202] – 2026-08-21

### Check multi-bundle projection documents

- Prove generic HT concept renaming preserves models under pullback and reflects
  models when the concept embedding has a left inverse.
- Transport the simultaneous fresh-definer theorem from its structural `Sum`
  signature to arbitrary production concept identifiers.
- Add a bundle projection wire with separate source and target concept tables,
  independently decoded direct clauses, bundles, fillers, definers, and target
  clauses.
- Check that every source concept and fresh definer maps injectively into the
  target table, rejecting definer collisions by computation.
- Check unique Skolem function keys and exact whole-target clause-set equality.
- Prove every accepted bundle document preserves and reflects satisfiability,
  and extend `ht-projection-cert-check` to dispatch this format.

Rust does not yet emit bundle documents, and role-domain extras are not yet part
of this wire. Cardinality replacement, nominal/ABox projection, the remaining
HT audit, CB, and routing certification remain unfinished.

## [0.3.201] – 2026-08-21

### Compose all fresh-definer Skolem bundles simultaneously

- Give every bundle a structurally fresh `Sum.inl` concept and embed every
  source concept under `Sum.inr`, making collisions impossible by type.
- Lift and restrict source literals, atoms, clauses, ontologies, and
  interpretations across the indexed signature.
- Construct all fresh definers simultaneously as their respective finite
  filler intersections.
- Prove source-to-target soundness for an arbitrary finite family of
  multi-filler bundles and untouched direct clauses.
- Prove target-to-source completeness with one shared interpretation for all
  uniquely keyed Skolem functions.
- Establish whole-ontology equisatisfiability for all generated existential
  and definer clauses together.

Executable mixed-wire decoding still needs to reconstruct this indexed bundle
family and combine it with role-domain evidence. Cardinality replacement,
nominal/ABox projection, the remaining HT audit, CB, and routing certification
remain unfinished.

## [0.3.200] – 2026-08-21

### Prove projected role-domain consequences redundant

- Define semantic role inclusion and role-domain conditions for HT
  interpretations.
- Prove ordinary two-variable inclusion and domain clauses equivalent to those
  semantic conditions when their variables are distinct.
- Prove a projected existential entails `body → Domain(x)` for its own role or
  any super-role carrying that domain.
- Lift the result to every finite domain-consequence list emitted beside one
  existential.
- Prove adding all such clauses preserves and reflects whole-ontology model
  satisfaction.

The mixed wire still needs to reconstruct role-closure/domain evidence and
admit these source-derived redundant target clauses. Whole-list fresh-definer
composition, cardinality replacement, nominal/ABox projection, the remaining
HT audit, CB, and routing certification remain unfinished.

## [0.3.199] – 2026-08-21

### Prove fresh-definer Skolem projection exact

- Model the production transformation that combines several singleton filler
  clauses for one Skolem witness through one fresh concept.
- Represent freshness structurally with `Option Concept`, separating the new
  definer from every source concept without a string-level assumption.
- Prove source concepts, roles, literals, atoms, clauses, and complete direct
  ontologies preserve and reflect satisfaction through lifting/restriction.
- Construct the fresh concept as the exact intersection of all source fillers
  for projection soundness.
- Recover a shared Skolem witness from the projected existential and use every
  checked definer implication to prove projection completeness.
- Establish `bundleProjection_sat_iff` for arbitrary finite filler lists plus
  untouched direct clauses.

Whole-list composition for several fresh definers, executable wire decoding,
and the production role-domain consequences remain to be connected. Cardinality
replacement, nominal/ABox projection, the remaining HT audit, CB, and routing
certification remain unfinished.

## [0.3.198] – 2026-08-21

### Connect production Skolem evidence to Lean

- Preserve a complete mixed source projection whenever every input clause is
  either direct or one half of an exact simple unary Skolem pair.
- Require each proved pair to contain exactly one singleton role head and one
  singleton filler head with a common body and exact `x`/`f(x)` wiring.
- Seed the pair variable table with `x = 0`, matching the converter's emitted
  existential node instead of relying on source occurrence order.
- Serialize mixed source evidence at the HT consumer boundary and invoke the
  native projection checker before checker-enabled publication.
- Add a real Rust-to-Lean integration test that accepts complete production
  evidence and rejects an omitted target clause.

Multiple filler clauses, filler definers, domain propagation, cardinality
replacement, nominal/ABox projection, the remaining HT audit, CB, and routing
certification remain unfinished and continue to defer from this certified
projection path.

## [0.3.197] – 2026-08-21

### Check mixed direct and Skolem HT projections

- Add a bounded mixed-projection wire with independent concept, role,
  function, and local-variable name resolution.
- Decode untouched clauses and common-body unary Skolem pairs into the finite
  semantic objects used by the whole-list theorem.
- Reject duplicate symbol tables, duplicate local-variable tables, reused
  Skolem functions, unknown names, omitted target clauses, and added or
  altered target clauses.
- Compare source-derived and actual HT ontologies extensionally, and prove
  equal clause sets have identical `Interp.models` semantics regardless of
  ordering or duplicate clauses.
- Extend `ht-projection-cert-check` to accept mixed documents while preserving
  compatibility with direct documents.

Rust does not yet produce mixed projection evidence, so checker-enabled HT
still defers on function-bearing source clauses. General multi-filler/definer
projection, cardinality replacement, nominal/ABox projection, the remaining
HT audit, CB, and routing certification remain unfinished.

## [0.3.196] – 2026-08-21

### Compose all HT Skolem pairs in one interpretation

- Strengthen unary witness refinement with an explicit preservation theorem:
  installing one function leaves every differently named function unchanged.
- Define finite Skolem-pair specifications and prove soundness for their whole
  projected target list.
- Prove completeness by installing finitely many uniquely named witnesses in
  one shared Skolem interpretation while preserving the pairs already handled.
- Combine untouched direct clauses and all Skolem pairs in
  `mixedSkolemProjection_sat_iff`, establishing whole-ontology
  equisatisfiability for this mixed projection fragment.
- Reject a disjunctive Skolem head in Rust instead of unsafely treating its
  alternative head atoms as conjunctive existential fillers.

The executable projection wire still needs to decode this mixed evidence and
compare its projected target with the exact production ontology. General
multi-filler/definer projection, cardinality replacement, nominal/ABox
projection, the remaining HT audit, CB, and routing certification remain
unfinished.

## [0.3.195] – 2026-08-21

### Prove the HT Skolem-pair projection exact

- Model the unary Skolem interpretation used by the frontend's two-clause
  existential encoding and the single HT existential clause produced from it.
- Prove soundness, completeness, and equisatisfiability for the exact
  common-body role/filler pair, including bodies with additional variables.
- Tighten the Rust converter to require identical bodies and the exact
  `R(x, f(x))` / `C(f(x))` wiring established by the theorem.
- Fix an unsafe converter case that could previously combine role and filler
  halves guarded by different bodies under the same function name.
- Add regression tests showing malformed pairs are dropped without emitting a
  partial existential. Every production HT route already rejects converted
  input with a nonzero dropped count.

The executable projection wire does not yet carry two-to-one Skolem-pair
evidence, so checker-enabled HT still defers on function-bearing source
clauses. Cardinality replacement, nominal/ABox projection, the remaining HT
fragment audit, CB, and automatic routing certification remain unfinished.

## [0.3.194] – 2026-08-21

### Check the direct source-to-HT projection in Lean

- Add a bounded direct-projection wire format that retains the complete source
  clause list, symbol-name tables, and first-occurrence local-variable tables.
- Resolve every concept, role, and variable name inside Lean; reject duplicate
  tables, unknown names, out-of-bound variables, omitted or added clauses, and
  altered concept, role, existential, or equality atoms.
- Prove that every decoded projection has exactly the target HT ontology and
  therefore has identical model semantics.
- Add the native `ht-projection-cert-check` executable and require it before any
  checker-enabled HT publication. A missing checker or missing source evidence
  now causes fail-closed deferral.
- Preserve direct function-free DL clauses in the Rust converter. Inputs using
  function elimination or bottom-head erasure carry no direct evidence and
  defer until those transformations receive separate proved constructors.
- Exercise ordinary, equality, cardinality-side, existential, role-chain, and
  transitive normalized inputs against the real projection checker.

The Skolem-to-existential, cardinality replacement, nominal/ABox, and remaining
converter transformations still need semantic projection certificates. CB and
automatic routing certification remain unfinished.

## [0.3.193] – 2026-08-21

### Make certified HT input coverage fail closed

- Preserve the converter's `dropped`, `fenced`, and inverse/cardinality role-
  separation fields at the HT consumer boundary instead of silently ignoring
  them.
- Reject certified HT publication when the clause projection omitted or fenced
  any source axiom, or when nominals or a native ABox remain outside the
  certified projection.
- Admit inverse-only inputs and inverse-plus-cardinality inputs only when the
  producer supplies the independently checked role-separation fact.
- Mirror the production gate in Lean and prove that every accepted summary has
  a complete projection, excludes unrepresented features, and satisfies the
  inverse/cardinality separation obligation.
- Add Rust regression tests for every accepted and rejected gate combination.

Full inverse-HT completeness, the remaining HT fragment audit, CB, and
automatic routing certification remain unfinished.

## [0.3.192] – 2026-08-21

### Derive certified HT global verdicts from accepted evidence

- Define the production-global Boolean represented by cardinality SAT and
  UNSAT evidence; query evidence has no global Boolean.
- Prove an accepted `true` document constructs a nonempty ontology/cardinality
  model and an accepted `false` document proves that no such model exists.
- Parse the checker-ready Rust envelope across plain, equality, cardinality,
  regular, normalized, and anchored global formats.
- Reject query evidence, ambiguous normalized payloads, and any disagreement
  between the recursive search Boolean and the certificate evidence before
  publishing the HT result.
- Add regression coverage for every supported global evidence shape and audit
  the Lean verdict theorem without `sorryAx`.

The remaining HT fragment audit, CB, and automatic routing certification remain
unfinished.

## [0.3.191] – 2026-08-21

### Connect checked Rust successors to production recursion

- Define one concrete successor predicate by case over the selected
  first-obstruction step.
- Reject successors for immediate equality-apart and concept clashes.
- Require every recursive clause, witness, minimum, or maximum successor to
  pass its exact field-transition checker, including the selected head atom or
  unequal maximum witness indices.
- Prove every concrete checked successor is an exact `ChildConfig` of the
  selected production step. This composes Rust mutation with the existing
  strict-growth, well-founded recursion, and parent-closure theorems.
- Audit the composition endpoint without `sorryAx`.

Concrete Rust recursive result construction, CB, and automatic routing remain
unfinished.

## [0.3.190] – 2026-08-21

### Prove concrete cardinality production transitions exact

- Check the logical portion of concrete successor states independently of
  cached representative functions, whose validity is checked separately.
- Model Rust's expanded-minimum `HashSet` extensionally: clause, witness, and
  maximum transitions preserve it, while a minimum transition inserts exactly
  the selected `(definition_id, source)` site.
- Check Rust's exact active-node updates for all four recursive transition
  families.
- Prove every checked clause assertion, ordinary witness, minimum expansion,
  and maximum merge successor equals its exact typed Lean production child.
- Audit all transition-correspondence endpoints without `sorryAx`.

Concrete Rust outcome construction, CB, and automatic routing remain
unfinished.

## [0.3.189] – 2026-08-21

### Check concrete cardinality production runtime fields

- Define the finite production fields corresponding to Rust's logical branch
  state: the checked distinct-equality certificate, `active_nodes`, and the
  branch-local expanded `(definition_id, source)` minimum sites.
- Check inactive-prefix freshness, duplicate expanded sites, minimum-definition
  kinds, and active-source bounds before constructing a typed production
  configuration.
- Prove the constructed configuration preserves the exact state, active prefix,
  and expanded-site membership, and expose the checked fields through a bounded
  JSON decoder.
- Audit the field-construction endpoints without `sorryAx`.

Concrete Rust transition/outcome correspondence, CB, and automatic routing
remain unfinished.

## [0.3.188] – 2026-08-21

### Compose checked SAT evidence with cardinality production search

- Import the independent finite equality/cardinality model checker into the
  production search layer.
- Define checked-frontier semantics: ordinary witness and minimum budget stops
  are always inconclusive; a selector-exhausted terminal is inconclusive unless
  accepted global model evidence exists.
- Prove finite production search returns one of three semantically distinct
  results: a quotient-closed refutation, a nonempty ontology/cardinality model
  derived from an accepted certificate, or an explicit descendant frontier.
- Prove rejected or absent model evidence at an exhausted terminal cannot
  produce SAT.
- Audit the checked-search endpoint without `sorryAx`.

Concrete Rust field and outcome construction, CB, and automatic routing remain
unfinished.

## [0.3.187] – 2026-08-21

### Prove total finite-budget cardinality control search

- Define the total first-obstruction outcome in production priority order:
  selected recursive step, ordinary-witness frontier, minimum-width frontier,
  or selector-exhausted terminal.
- Distinguish node-budget failure from logical terminality for both ordinary
  witnesses and minimum expansions.
- Prove the control function produces an outcome for every finite runtime
  configuration.
- Define reflexive-transitive descent through exact production child
  configurations.
- Lift the one-step control through the well-founded recursion kernel and prove
  every root either constructs a quotient-closed cardinality refutation or
  reaches an explicit frontier/terminal descendant.
- Audit the total-search endpoint without `sorryAx`.

Turning exhausted terminals into checked models, concrete Rust field
construction, CB, and automatic routing remain unfinished.

## [0.3.186] – 2026-08-21

### Compose the cardinality production recursion kernel

- Define the exact child-configuration predicate for each selected production
  obstruction: no children for immediate clashes, head-assertion children for
  clauses, one exact child for witness and minimum expansion, and every
  off-diagonal greedy merge child for maximum restrictions.
- Prove every child configuration is a strict step in the common well-founded
  production relation by composing the four transition-specific growth
  theorems.
- Prove that semantic closure of every child configuration constructs a
  quotient-closed cardinality refutation of the parent configuration.
- Derive a well-founded induction principle over the exact production child
  relation. This is the recursion kernel for finite-budget outcome production.
- Audit all composition endpoints without `sorryAx`.

The executable first-obstruction decision and recursive outcome value,
concrete Rust field construction, CB, and automatic routing remain unfinished.

## [0.3.185] – 2026-08-21

### Certify maximum merge progress

- Prove every node in the deterministic greedy maximum witness prefix is below
  `active_nodes`, using its quotient-closed filler label.
- Prove merging two nodes from different equality classes strictly grows the
  complete equality-aware guarded-fact set.
- Construct each exact off-diagonal maximum matrix successor while preserving
  active count, expanded-minimum metadata, and inactive-prefix freshness.
- Use the proved pairwise quotient distinction of greedy witnesses to prove
  every unequal maximum merge child strictly grows the combined production
  progress set.
- Audit all maximum-growth endpoints without `sorryAx`.

All recursive transition families now have strict-growth proofs. Composing the
total recursive outcome, concrete Rust field construction, CB, and automatic
routing remain unfinished.

## [0.3.184] – 2026-08-21

### Certify ordinary witness progress

- Prove an existential obligation cannot originate at an inactive node under
  the checked inactive-prefix freshness invariant.
- Prove every selected quotient-unblocked witness source is below
  `active_nodes`.
- Construct the exact ordinary witness successor at node ID `active_nodes`,
  increment the active prefix by one, preserve indexed minimum metadata, and
  prove the enlarged inactive prefix remains fresh.
- Lift strict equality-aware guarded-fact growth through the combined
  cardinality progress measure and prove every selected witness child is a
  strict step in the well-founded production relation.
- Audit all witness endpoints without `sorryAx`.

Maximum growth, total recursive outcome production, concrete Rust field
construction, CB, and automatic routing remain unfinished.

## [0.3.183] – 2026-08-21

### Certify active-prefix clause recursion

- Replace the full-node-budget grounding domain in cardinality production with
  assignments into `Fin active_nodes`, lifted into the fixed finite node budget.
- Prove every enumerated and selected grounding uses only active IDs and that a
  selected grounding carries the exact quotient-closed body and absent-head
  premises.
- Prove closure of all selected head children closes the parent state.
- Switch every later first-obstruction constructor to exhaustion of this
  active-prefix clause selector.
- Construct exact clause successor configurations and prove they preserve the
  inactive-prefix invariant.
- Prove every selected head assertion strictly grows the production progress
  fact set and audit all endpoints without `sorryAx`.

Witness and maximum growth, total recursive outcome production, concrete Rust
field construction, CB, and automatic routing remain unfinished.

## [0.3.182] – 2026-08-21

### Establish the cardinality production termination measure

- Define the finite runtime configuration containing the distinct equality
  state, `active_nodes`, the indexed expanded-minimum set, and the checked
  inactive-prefix invariant.
- Define an extensional progress fact set matching Rust's release-mode measure:
  guarded labels, edges, obligations, equalities, directed apart pairs, and
  expanded minimum IDs.
- Prove the fact-set membership characterization and preservation of all old
  equality-aware guarded facts through minimum materialization.
- Construct the exact minimum successor configuration, including consecutive
  target IDs, enlarged active prefix, and insertion of the selected definition
  ID/source pair.
- Prove every selected minimum successor strictly grows the production progress
  fact set, including zero-width minimum restrictions where metadata insertion
  is the required progress witness.
- Prove strict growth over these finite fact sets is well-founded and audit all
  endpoints without `sorryAx`.

Clause, witness, and maximum growth, total recursive outcome production,
concrete Rust field construction, CB, and automatic routing remain unfinished.

## [0.3.181] – 2026-08-21

### Certify definition-indexed cardinality selection

- Represent production cardinality sites by stored definition ID and finite
  source ID, preserving distinct duplicate definition records.
- Mirror Rust's minimum expansion guard exactly: the same definition ID is
  suppressed at every equality-equivalent source recorded in the branch-local
  expanded-minimum set.
- Prove exact selector exhaustion, selected-rule closure, and active-source
  bounds for indexed minimum sites.
- Add the corresponding definition-indexed maximum scan and prove exact
  exhaustion, closure through every unequal merge child, and active-source
  bounds.
- Switch the composed first-obstruction layer from structural definitions to
  the indexed selectors used by production metadata.
- Audit all indexed selector endpoints without `sorryAx`.

The extensional progress measure, well-founded recursive outcome production,
concrete Rust field construction, CB, and automatic routing remain unfinished.

## [0.3.180] – 2026-08-21

### Compose cardinality first-obstruction closure

- Add a typed production-shaped first-obstruction layer covering equality/apart
  clash, quotient concept clash, clause branching, witness materialization,
  minimum materialization, and maximum merging in runtime priority order.
- Carry explicit exhaustion evidence for every earlier selector in each later
  constructor.
- Use Rust's exact `active_nodes` witness ID, consecutive minimum IDs, and
  deterministic greedy maximum prefix vector in recursive child states.
- Prove that immediate clashes or closure of every selected recursive child
  constructs a sound quotient-closed cardinality refutation of the parent.
- Add the module to the default Lean build and audit its endpoint without
  `sorryAx`.

Concrete Rust field construction, well-founded recursive outcome production,
CB, and automatic routing remain unfinished.

## [0.3.179] – 2026-08-21

### Certify active-source fidelity for cardinality scans

- Prove that an inactive node cannot carry a quotient-closed label under the
  checked active-prefix freshness invariant.
- Lift that result to the executable finite certificate and its checked
  quotient-closed label predicate.
- Prove that every selected production-order minimum source and maximum source
  lies below Rust's `active_nodes` boundary. This justifies the existing full
  finite-ID Lean scans against Rust's active-prefix loops.
- Audit all new active-source endpoints without `sorryAx`.

Exact recursive outcome production, concrete Rust field construction, CB, and
automatic routing remain unfinished.

## [0.3.178] – 2026-08-21

### Certify production-order maximum scanning

- Define the exact Rust maximum-site list: cardinality definitions in stored
  order, then finite source IDs in ascending order.
- Define and characterize the executable site predicate combining maximum
  kind, quotient-closed marker, and sufficient greedy representative width.
- Prove selector exhaustion equivalent to absence of every semantic violating
  maximum restriction.
- Prove a selected site and all unequal merge children construct a sound
  quotient-closed maximum refutation using the deterministic prefix vector.
- Replace the abstract maximum selector in the finite terminal
  characterization with the concrete production-order scan.
- Audit all production-order endpoints without `sorryAx`.

Exact recursive outcome production, concrete Rust field construction, CB, and
automatic routing remain unfinished.

## [0.3.177] – 2026-08-21

### Prove greedy maximum completeness

- Prove the greedy scan never removes a previously selected representative.
- Prove every qualifying target is equality-equivalent to some retained
  representative, including the branch where a candidate is skipped because
  its class was already represented.
- Construct an injective map from every semantic pairwise-distinct witness
  family into positions of the greedy representative list.
- Prove the exact equivalence between `bound + 1` greedy width and existence of
  a qualifying pairwise quotient-distinct witness vector.
- Audit all class-coverage and width-completeness endpoints without `sorryAx`.

Production-order scanning over definitions and sources, exact recursive outcome
production, concrete Rust field construction, CB, and automatic routing remain
unfinished.

## [0.3.176] – 2026-08-21

### Certify maximum width and truncation

- Define the exact dependent prefix vector used after Rust verifies that at
  least `bound + 1` greedy representatives exist.
- Prove every vector index denotes an element of the representative list and
  therefore a quotient-closed qualifying role successor with the required
  filler.
- Prove unequal vector indices remain quotient-distinct, including the reverse
  index-order case through symmetry of checked equality closure.
- Prove the resulting definition, source, and prefix vector satisfy the exact
  executable maximum-candidate predicate.
- Audit all truncation endpoints without `sorryAx`.

Completeness of greedy equality-class coverage, production-order scanning over
definitions and sources, exact recursive outcome production, concrete Rust
field construction, CB, and automatic routing remain unfinished.

## [0.3.175] – 2026-08-21

### Certify deterministic maximum representatives

- Formalize Rust's exact maximum candidate scan over ascending finite target
  IDs, with quotient-closed role and filler qualification.
- Formalize its left-to-right greedy selection that retains the first target
  from each equality class.
- Prove every selected representative came from the qualifying target list and
  therefore satisfies the required closed edge and filler facts.
- Prove selected representatives are pairwise quotient-distinct.
- Audit the deterministic selection theorems without `sorryAx`.

Certified width checking and truncation to the dependent `n+1` vector,
completeness of greedy class coverage, exact recursive outcome production,
concrete Rust field construction, CB, and automatic routing remain unfinished.

## [0.3.174] – 2026-08-21

### Preserve active-prefix freshness through assertion and merge

- Define the exact premise that every finite grounding maps variables into
  Rust's active-node prefix.
- Prove concept, role, existential, and equality head assertion preserves
  freshness of every inactive node.
- Prove maximum-induced equality merging between active witnesses cannot join
  an inactive node into the equality class, using induction over generated
  equivalence closure.
- Connect accepted finite `transitionB` and `mergeTransitionB` successor
  certificates to the preserved active-prefix invariant.
- Audit all preservation endpoints without `sorryAx`.

The active-prefix induction invariant now covers every recursive state-changing
constructor. Deterministic maximum witness selection, exact recursive outcome
production, concrete Rust field-construction correspondence, CB, and automatic
routing remain unfinished.

## [0.3.173] – 2026-08-21

### Preserve active-prefix freshness through allocation

- Define Rust's exact ordinary witness target at `active_nodes`.
- Prove ordinary witness materialization preserves inactive-prefix freshness
  while increasing the active prefix by one.
- Prove minimum materialization with the exact consecutive target vector
  preserves freshness while increasing the prefix by the restriction width,
  including labels, edges, equality isolation, obligations, and both
  directions of explicit `apart` facts.
- Connect accepted finite `minimumTransitionB` successor certificates to the
  enlarged semantic active-prefix invariant.
- Audit all preservation endpoints without `sorryAx`.

Field-level correspondence for ordinary witness state construction,
preservation through clause assertion and maximum merge, deterministic maximum
witness selection, exact recursive outcome production, CB, and automatic
routing remain unfinished.

## [0.3.172] – 2026-08-21

### Check the active-node prefix invariant

- Add an executable finite-certificate check matching Rust's `active_nodes`
  discipline: every inactive ID must be equality-fresh and absent from both
  directions of the explicit `apart` relation.
- Prove checker acceptance yields semantic inactive-prefix freshness and that
  the claimed active prefix fits within the finite node budget.
- Derive freshness of Rust's complete consecutive minimum-target vector
  directly from accepted wire-state data.
- Audit the checker and correspondence endpoints without `sorryAx`.

Proving Rust field construction preserves this checked invariant at every
recursive transition, deterministic maximum witness selection, exact recursive
outcome production, CB, and automatic routing remain unfinished.

## [0.3.171] – 2026-08-21

### Certify consecutive minimum targets

- Define the exact target vector allocated by Rust for a minimum expansion:
  `active_nodes + index` for every index below the restriction width.
- Prove the vector is in bounds and injective whenever
  `active_nodes + width ≤ node_budget`.
- State the active-prefix freshness invariant maintained by Rust's allocation
  discipline and prove it makes the complete consecutive vector fresh,
  including equality and directed `apart` constraints.
- Compose the concrete target vector with production-order minimum selection
  to construct a sound quotient-closed recursive branch.
- Audit the new construction without `sorryAx`.

Concrete wire-state preservation of the active-prefix invariant, deterministic
maximum witness selection, exact recursive outcome production, CB, and
automatic routing remain unfinished.

## [0.3.170] – 2026-08-21

### Certify production-order minimum selection

- Replace the abstract finite-set enumeration used for the correspondence
  argument with a finite-ID minimum candidate list that matches Rust's nested
  loop: cardinality definitions in stored order, then node IDs in ascending
  `0..node_count` order.
- Prove exact membership, exhaustive `none` correspondence, and sound
  quotient-closed minimum recursion for the concrete selector.
- Audit the production-order selector without `sorryAx`.

The active-node prefix and consecutive fresh-target construction, deterministic
maximum witness selection, exact recursive outcome production, concrete Rust
field construction, CB, and automatic routing remain unfinished.

## [0.3.169] – 2026-08-21

### Connect quotient-closed cardinality checking to production

- Switch both the standalone distinct-cardinality wire and the production
  global cardinality document checker from the legacy raw-fact checker to the
  quotient-closed recursive checker.
- Strengthen checked closed outcomes to carry acceptance by that exact checker.
- Prove accepted ontology-UNSAT, subsumption, and unsatisfiable-concept
  documents have their stated semantics through the production wire boundary.
- Preserve the executable global SAT/closed outcome theorem and audit all new
  endpoints without `sorryAx`.

Exact recursive outcome production, concrete Rust field construction, CB, and
automatic routing remain unfinished.

## [0.3.168] – 2026-08-21

### Certify the quotient-closed cardinality refutation checker

- Add executable equality-closed label and edge checks and prove each exactly
  equivalent to its semantic quotient-closed relation.
- Add the full recursive distinct-cardinality checker used by the Rust search
  semantics: equality/apart and concept clashes, quotient-closed clause bodies,
  witness materialization, all maximum merge branches, and minimum expansion.
- Prove every accepted tree constructs a quotient-closed cardinality
  refutation and therefore rules out every realization satisfying the ontology
  and cardinality definitions.
- Audit the checker endpoint without `sorryAx`.

At this release, the production cardinality wire still invoked the legacy
checker. Release 0.3.169 switches that boundary to the quotient-closed checker.

## [0.3.167] – 2026-08-21

### Compose cardinality terminals with checked models

- Define the exact accepted cardinality-model obligation: positive finite node
  domain, exact ontology identity, and successful equality/cardinality check.
- Prove accepted evidence constructs a nonempty quotient model satisfying both
  the ontology and every cardinality definition.
- Add a typed bounded outcome separating quotient-closed refutation, checked
  model, and explicit frontier.
- Prove every bounded outcome is semantically conclusive or remains the exact
  frontier constructor.
- Compose runtime terminality with independently checked model evidence without
  treating terminality itself as SAT.
- Audit the composition without `sorryAx`.

Exact recursive outcome production, concrete minimum-target and maximum-
candidate ordering, checker correspondence for quotient-closed refutations,
concrete Rust field construction, CB, and automatic routing remain unfinished.

## [0.3.166] – 2026-08-21

### Certify cardinality terminal classification

- Define cardinality runtime terminality as simultaneous absence of an
  equality/apart clash, quotient concept clash, undischarged clause,
  unblocked unwitnessed obligation, expandable minimum, and violating maximum.
- Prove this semantic terminal predicate equivalent to exact exhaustion of all
  six executable selectors in Rust's runtime order.
- Add a direct constructor from the six exhausted selector results.
- Keep terminality distinct from SAT: blocked obligations and the quotient
  model still require independent executable certificate acceptance.
- Audit terminal classification without `sorryAx`.

Checked terminal-model composition, concrete minimum-target and maximum-
candidate ordering, checker correspondence for quotient-closed bodies,
concrete Rust field construction, CB, and automatic routing remain unfinished.

## [0.3.165] – 2026-08-21

### Certify quotient-closed maximum selection

- Add a finite dependent candidate space containing each maximum definition,
  source node, and full `bound + 1` witness vector.
- Check the exact Rust premises: maximum kind, quotient-closed marker,
  quotient-closed role and filler facts, and pairwise quotient-distinct
  witnesses.
- Prove exhaustive scan correspondence with semantic existence of a violating
  maximum restriction.
- Prove that a selected candidate plus every unequal merge child constructs a
  sound quotient-closed distinct-cardinality refutation.
- Audit the selector and dependent enumeration without `sorryAx`.

Terminal selection, concrete minimum-target and maximum-candidate ordering,
checker correspondence for quotient-closed bodies, concrete Rust field
construction, CB, and automatic routing remain unfinished.

## [0.3.164] – 2026-08-21

### Certify quotient-closed minimum selection

- Strengthen runtime minimum and maximum premises to use the quotient-closed
  labels and edges tested by Rust.
- Prove that realized equality states preserve quotient-closed labels and
  edges semantically.
- Prove minimum materialization sound when the active marker occurs on an
  equivalent node, including relocation of the generated source edges.
- Add the executable minimum candidate scan over definitions and finite nodes,
  with exact kind, closed marker, expansion-history, and blocking premises.
- Prove scan exhaustion equivalent to absence of every expandable minimum and
  prove selected minimum recursion constructs a sound closed-cardinality
  refutation.
- Audit the new selection and relocation theorems without `sorryAx`.

Concrete consecutive-target correspondence, maximum and terminal selection,
checker correspondence for quotient-closed bodies, concrete Rust field
construction, CB, and automatic routing remain unfinished.

## [0.3.163] – 2026-08-21

### Certify cardinality witness selection

- Add the executable distinct-fresh-node scan required by cardinality-created
  disequalities.
- Prove that scan exhaustion is equivalent to absence of every node fresh for
  labels, edges, obligations, equality, and both directions of `apart`.
- Compose the existing quotient-blocked unwitnessed-obligation selector with
  the distinct-fresh selector, matching Rust's fourth ordered runtime control.
- Prove that a selected obligation, selected target, and recursively closed
  child construct a sound quotient-closed distinct-cardinality refutation.
- Audit the new witness-control theorems without `sorryAx`.

Minimum, maximum, terminal selection, checker correspondence for quotient-
closed bodies, concrete Rust field construction, CB, and automatic routing
remain unfinished.

## [0.3.162] – 2026-08-21

### Certify quotient-closed cardinality clause selection

- Define the quotient-closed distinct-cardinality refutation relation matching
  Rust's `closed_holds` evaluation for every clause-body atom.
- Prove this stronger relation sound for equality, clash, branching, witness,
  equality/apart, minimum, and maximum rules.
- Prove every existing distinct-cardinality refutation embeds into the new
  quotient-closed relation.
- Mirror the third ordered Rust runtime control: exhaustive finite clause and
  assignment selection after both clash scans.
- Prove selected clause recursion sound and prove that scan exhaustion is
  equivalent to absence of a quotient-closed undischarged grounding.
- Audit the new semantic relation and selector theorems without `sorryAx`.

Witness, minimum, maximum, terminal selection, checker correspondence for the
stronger clause body, concrete Rust field construction, CB, and automatic
routing remain unfinished.

## [0.3.161] – 2026-08-21

### Begin exact cardinality runtime refinement

- Add an executable cardinality-runtime module and mirror Rust's first
  `apart.iter().find(...)` control over the exact serialized pair order.
- Prove that a selected equality/apart pair constructs a sound
  distinct-cardinality refutation.
- Prove that exhausting the finite list is equivalent to absence of every
  equality/apart clash represented by the runtime state.
- Lift the existing quotient concept-clash selector into the
  distinct-cardinality calculus, with selected and exhausted outcomes proved
  against cardinality semantics.
- Audit all new runtime theorems without `sorryAx`.

The ordered clause, existential-witness, minimum, maximum, and terminal
controls, concrete Rust field construction, CB, and automatic routing remain
unfinished.

## [0.3.160] – 2026-08-21

### Certify production equality SAT JSON acceptance

- Add wire-level soundness for the normalized finite equality certificate used
  as the first production SAT candidate.
- Add wire-level soundness for the normalized anchored equality certificate
  used as the production fallback after a finite quotient candidate is
  rejected.
- Prove that successful decode plus `Except.ok true` constructs the exact
  decoded source semantics in both cases.
- Preserve fail-closed behavior for malformed documents, normalization or
  preprocessing failures, and checker rejection.
- Audit both production-boundary theorems without `sorryAx`.

Concrete correspondence for Rust's construction of every emitted field,
cardinality runtime selection, CB, and automatic routing remain unfinished.

## [0.3.159] – 2026-08-21

### Compose equality termination with checked blocked models

- Define the equality-aware checked-fold model boundary over
  `FiniteEqFoldCertificate`.
- Prove that every accepted fold constructs a model of the exact unchanged
  ontology, regardless of the producer's proposed blocker pairs.
- Add a typed fixed-budget equality outcome whose frontier remains explicitly
  inconclusive.
- Compose globally terminating clash-first search with checked blocked
  terminals: the result is a quotient-closed refutation, an independently
  checked model, or an explicit node frontier.
- Derive semantic decision when the finite budget has no frontier.
- Audit the new composition theorems without `sorryAx`.

The runtime still must produce an accepted fold at every blocked terminal.
Cardinality runtime selection, CB, and automatic routing remain unfinished.

## [0.3.158] – 2026-08-21

### Prove global finite equality-runtime termination

- Define a finite extensional equality-state measure containing every ordinary
  HT fact and every ordered node-equivalence pair.
- Prove that every absent quotient-closed head assertion, including an equality
  merge, strictly grows this measure.
- Prove that fresh witness materialization strictly grows the same measure and
  preserves existing equality pairs.
- Derive a well-founded strict-growth relation and a generic finite exhaustive
  recursion theorem directly over equality states.
- Instantiate it for clash-first equality search: at every fixed node budget,
  search constructs a quotient-closed refutation or reaches a blocked/saturated
  terminal or explicit node frontier.
- Audit the new termination and recursion theorems without `sorryAx`.

Checked SAT-terminal composition, cardinality runtime selection, CB, and
automatic routing remain unfinished.

## [0.3.157] – 2026-08-21

### Certify equality-aware runtime control

- Define the concrete equality-aware clause-first successor enumerator with
  quotient-closed clause matching, quotient pairwise blocking, and fresh-node
  witness expansion.
- Prove every nonempty successor family has exactly the corresponding certified
  branch or witness transition shape.
- Classify every empty successor family as a zero-head refutation, a
  blocked/saturated terminal, or explicit finite-node exhaustion.
- Prove the full clash-first control theorem: every finite state refutes,
  advances through a certified transition, terminates, or reaches a frontier.
  Frontier exhaustion is never classified as satisfiable.
- Audit the new runtime-control theorems without `sorryAx`.

Global finite equality search termination and checked SAT-terminal composition,
cardinality runtime selection, CB, and automatic routing remain unfinished.

## [0.3.156] – 2026-08-21

### Connect bounded equality decisions to closed grounding

- Change the checked equality decision outcome's closed branch to require the
  production quotient-closed recursive checker.
- Re-prove closed-outcome inconsistency and the conclusive-outcome semantics
  through `checkClosed_ontology_unsatisfiable`.
- Remove the accidental decision-to-runtime import dependency and make the
  equality certificate dependency explicit, keeping the Lean module graph
  acyclic.
- Build all 3,400 Lean targets and audit the decision capstone without
  `sorryAx`.

Constructing the concrete equality-aware round outcome from Rust-compatible
selectors, cardinality runtime selection, CB, and automatic routing remain
unfinished.

## [0.3.155] – 2026-08-21

### Complete quotient-closed equality tree correspondence

- Prove that every finite semantic `ClosedEqRefutes` derivation constructs a
  production-accepted `checkClosed` tree, including canonical equality paths
  after every head transition.
- Prove the exact equivalence between finite quotient-closed refutation and an
  accepted recursive tree on canonical equality certificates.
- Update recursive equality wire representability to the production checker:
  every accepted quotient-closed tree and child state has an exact version-2
  JSON representation that decodes to the original typed evidence.
- Audit the new completeness and exactness theorems without `sorryAx`.

Equality finite-runtime termination and SAT composition, cardinality runtime
selection, CB, and automatic routing remain unfinished.

## [0.3.154] – 2026-08-21

### Integrate quotient-closed equality refutation checking

- Add a terminating executable equality refutation-tree checker whose clause
  branches evaluate concept, role, existential, and equality atoms modulo the
  certificate's checked equivalence relation.
- Prove mutually that every accepted tree and child vector constructs the
  quotient-closed recursive equality refutation relation.
- Derive ontology inconsistency, subsumption, and concept-unsatisfiability
  soundness for accepted quotient-closed trees.
- Switch the production equality UNSAT and query wire boundary to this checker,
  matching the Rust runtime's closed grounding behavior. Equality SAT and
  countermodel paths are unchanged.
- Audit the new checker and semantic wrappers without `sorryAx`, build the full
  Lean project, and pass all 47 Lean-integration Rust tests.

Exact recursive wire representability of the quotient-closed checker,
cardinality runtime selection, CB, and automatic routing remain unfinished.

## [0.3.153] – 2026-08-21

### Prove quotient-closed equality recursion sound

- Prove that every concept, role, existential, or equality atom holding modulo
  the complete node equivalence is true in every realization of the state.
- Define the recursive `ClosedEqRefutes` relation matching Rust's
  quotient-closed clause grounding, equality-aware head assertion, and fresh
  explicit-witness recursion.
- Prove the complete recursive relation sound for ontology inconsistency.
- Embed the older direct-premise equality refutation relation into the new
  quotient-closed relation.
- Prove that the concrete clash, clause, and witness selectors reconstruct the
  corresponding quotient-closed recursive constructors.
- Audit the new semantic and selector theorems without `sorryAx`.

Production refutation-checker integration for quotient-closed branches,
cardinality runtime selection, CB, and automatic routing remain unfinished.

## [0.3.152] – 2026-08-21

### Certify equality witness and quotient matching controls

- Add executable quotient-closed evaluation for concept, role, existential,
  and equality atoms over a validated finite equality certificate.
- Prove that this evaluator is equivalent to full semantic matching modulo the
  complete node equivalence and that its grounded clause scan equals the Rust
  equality runtime scan.
- Formalize the nearest-ancestor quotient pairwise blocker test and prove its
  exact finite-list semantics.
- Prove exhaustive unblocked-obligation and equality-fresh-node scans, then
  reconstruct the equality witness refutation rule whenever the selected
  recursive child closes.
- Audit the new correspondence theorems without `sorryAx`.

The quotient-closed branch relation and its recursive checker integration,
cardinality runtime selection, CB, and automatic routing remain unfinished.

## [0.3.151] – 2026-08-21

### Certify the first equality-aware runtime controls

- Define the exact finite quotient-clash scan used before equality-aware
  recursive expansion and prove that a selected clash yields an `EqRefutes`
  derivation.
- Prove that exhausting the clash scan is equivalent to closed clash freedom.
- Define the ontology-order and finite-assignment-order scan for clause bodies
  and heads interpreted modulo the complete node equivalence.
- Prove that exhausting this clause scan is equivalent to absence of any
  quotient-closed undischarged grounding.
- Audit all three selector theorems without `sorryAx`.

Equality-aware witness and blocking selection, cardinality runtime selection,
CB, and automatic routing remain unfinished.

## [0.3.150] – 2026-08-21

### Close equality-free finite runtime selection

- Prove a capstone theorem for the concrete clause-first equality-free runtime
  selector with no unchecked terminal-production premise.
- Derive strict finite-fact growth from every nonempty clause or witness
  successor family and combine exhaustive closed children through the formal HT
  refutation rules.
- Classify every empty successor family as an immediate refutation, a canonical
  model, or an explicit node-exhaustion frontier with a still-unwitnessed
  obligation and no fresh finite node.
- Keep finite-node exhaustion semantically inconclusive, matching iterative
  deepening; it is never interpreted as satisfiable.
- Audit the capstone without `sorryAx`.

Equality-aware and cardinality Rust transition-enumerator correspondence, CB,
and automatic routing remain unfinished.

## [0.3.149] – 2026-08-21

### Make the global cardinality outcome boundary executable

- Add a Boolean production-shape check to the version-2 cardinality document
  boundary. Global SAT requires no refutation payload; global UNSAT requires
  exactly one distinct-cardinality refutation and no ordinary fallback.
- Prove the Boolean shape check equivalent to the declarative production
  contract.
- Add `checkProductionGlobal` and prove that acceptance alone yields a decoded,
  semantically conclusive checked SAT or closed outcome. No caller-supplied
  shape proposition remains in this trust boundary.
- Confirm that cardinality taxonomy query documents already decode into total
  positive-or-negative concept and ordered subsumption decisions; no duplicate
  query correspondence layer was introduced.

The recursive Rust transition enumerator correspondence, CB, and automatic
routing remain unfinished.

## [0.3.148] – 2026-08-21

### Connect production cardinality documents to checked outcomes

- Define the exact global shape emitted by the Rust version-2 cardinality
  producer: SAT has no refutation payload; UNSAT has one distinct-cardinality
  refutation and no ordinary fallback payload.
- Prove that every successfully decoded and checker-accepted document of this
  shape constructs a typed checked SAT or checked closed bounded-search
  outcome, never a frontier.
- Compose that outcome with the existing semantic theorems, yielding a
  nonempty model for SAT and ontology inconsistency for UNSAT.
- Reject query evidence and mixed or missing global refutation payloads at this
  correspondence boundary. Audit both decoded and direct wire theorems without
  `sorryAx`.

Query-outcome correspondence, remaining HT runtime correspondence, CB, and
automatic routing remain unfinished.

## [0.3.147] – 2026-08-21

### Complete recursive distinct-cardinality wire representability

- Add a lossless bounded encoding for distinct-aware equality states, including
  every directed `apart` pair.
- Prove exact dependent-vector and row-by-row matrix decoding for recursive
  distinct-cardinality successor states and refutations.
- Prove that every checker-accepted finite distinct-cardinality refutation has
  a wire document that decodes to an accepted refutation at the same depth.
- Preserve checked branch, witness, minimum, and off-diagonal maximum
  successors exactly. Canonicalize only ignored maximum-rule diagonal cells.
- Audit the main theorem without `sorryAx`.

Exact Rust recursive outcome correspondence, remaining HT runtime
correspondence, CB, and automatic routing remain unfinished.

## [0.3.146] – 2026-08-21

### Complete recursive cardinality-refutation wire representability

- Prove that every checker-accepted finite equality/cardinality refutation has
  a bounded wire document that decodes to a checker-accepted refutation at the
  same declared depth.
- Preserve every checked branch, witness, minimum, and off-diagonal maximum
  successor through recursive decoding.
- Replace only maximum-rule diagonal cells with canonical depth-indexed trees.
  The executable checker intentionally ignores those cells, while their wire
  payloads must still be well-formed and depth-correct.
- Prove row-by-row decoding for dependent state/refutation matrices and audit
  the main theorem without `sorryAx`.

Distinct-cardinality wire completeness, exact Rust recursive outcome
correspondence, CB, and automatic routing remain unfinished.

## [0.3.145] – 2026-08-20

### Prove the cardinality-refutation wire data boundary

- Prove exact-length list decoding reconstructs every dependent finite vector.
- Prove bounds-checked node-id vectors reconstruct the original finite-node
  function used by minimum targets and maximum witnesses.
- Prove nested row and column decoding reconstructs every dependent square
  matrix used by maximum-rule child states and refutations.
- Add matching finite and wire canonical trees at every declared depth and
  prove exact decoding. These canonical cells replace semantically ignored
  maximum-rule diagonal payloads in the recursive completeness proof.

The complete recursive cardinality-tree theorem, distinct-cardinality wire
completeness, exact Rust recursive outcome correspondence, CB, and automatic
routing remain unfinished.

## [0.3.144] – 2026-08-20

### Prove equality-aware HT recursive wire completeness

- Add lossless bounded encoders for equality-certificate labels, role edges,
  existential obligations, asserted equalities, representative vectors, and
  complete representative paths.
- Prove the version-2 state decoder reconstructs every finite equality
  certificate exactly, including dependent finite functions.
- Replace the equality refutation decoder's opaque partial recursion with a
  total size-decreasing definition.
- Prove that every accepted finite equality-aware refutation tree has a
  version-2 wire tree that decodes to the exact original tree and every exact
  transitioned child certificate.

This closes recursive JSON representability for ordinary and equality-aware
finite HT refutations. Cardinality-layer external-format completeness, exact
Rust recursive outcome correspondence, CB, and automatic routing remain
unfinished.

## [0.3.143] – 2026-08-20

### Prove ordinary HT recursive wire completeness

- Replace the ordinary refutation-tree decoder's opaque partial recursion with
  a total size-decreasing definition. Its JSON behavior is unchanged, while
  every constructor equation is now available to proofs.
- Prove that every ordinary finite refutation tree accepted by the semantic
  checker has an external wire tree that decodes to that exact tree.
- Prove the branch case selects an ontology index that retrieves the checked
  clause, serializes the exact finite assignment, preserves child order and
  head arity, and reconstructs the original dependent child family.
- Prove the witness case recursively preserves the transitioned checker state
  while decoding against the same ontology.

This closes recursive JSON representability for ordinary finite HT
refutations. Equivalent external-format completeness for the equality and
cardinality tree layers remained unfinished in this release.

## [0.3.142] – 2026-08-20

### Prove lossless HT assignment encoding

- Encode every finite HT variable assignment as the ordered list of bounded
  node identifiers expected by the Rust JSON producer.
- Prove list-wide bound decoding reconstructs every finite node value.
- Prove the length-checked assignment decoder returns the exact original
  dependent function, including its finite-index transport.

Recursive refutation-tree encoding completeness remained unfinished in this
release.

## [0.3.141] – 2026-08-20

### Prove lossless HT source-language wire encoding

- Add canonical encoders for bounded HT literals, atoms, clauses, and complete
  ontology clause lists.
- Prove each encoder is a right inverse of the existing untrusted JSON decoder.
- Cover concept assertions, role assertions, existential obligations, and
  equality atoms without an admitted bound or coercion premise.
- Re-run the Rust producer against the real Lean executables for ordinary,
  equality-aware, cardinality, query, taxonomy, SAT, and UNSAT evidence. The
  deep pigeonhole regression also exercises minimum, maximum, and
  equality-apart recursion.

This proves that the complete finite HT source language represented by Lean is
losslessly expressible at the JSON boundary. Assignment and recursive-tree
encoding completeness remained unfinished in this release.

## [0.3.140] – 2026-08-20

### Close the ELC public taxonomy exactness contract

- Prove that every eligible public ELC subsumption row is equivalent to its
  semantic subsumption result when the row is either the distinguished bottom
  edge or the source class is satisfiable.
- Treat the bottom row as the complete public representation of an
  unsatisfiable class, while satisfiable classes retain all-and-only their
  semantic superclass rows.
- Lift the exact characterization through the V5 residual-source theory, so it
  applies to checked direct, canonical-witness, and compiled-residual inputs.
- Compose the result with the existing exact inconsistency theorem, trace and
  closure checks, normalization equivalences, and named-output agreement.

The checked ELC certificate now has a classifier-facing soundness and
completeness statement for its complete public result representation. HT Rust
recursive correspondence, CB, and automatic routing remain unfinished.

## [0.3.139] – 2026-08-20

### Prove distinct-cardinality HT checker completeness

- Encode every finite `DistinctCardinalityRefutes` derivation as an accepted
  executable refutation tree.
- Cover equality refutations, quotient clashes, transitive equality-apart
  contradictions, ordinary branches and witnesses, maximum merges, and
  minimum witness families.
- Construct the exact finite pairwise-apart extension introduced by a minimum
  rule and prove its transition checker accepts precisely that relation.
- Rebuild canonical equality evidence after assertions and merges while
  preserving the apart relation.
- Prove exact equivalence between semantic distinct-cardinality refutations and
  accepted canonicalized finite certificates.

This closes soundness and completeness of all finite HT refutation-tree
formats currently used by the ordinary, equality, cardinality, and
distinct-cardinality certificate layers. Exact correspondence with Rust
recursive outcomes and automatic routing remain unfinished.

## [0.3.138] – 2026-08-20

### Prove cardinality-aware HT refutation-tree completeness

- Encode every finite semantic `CardinalityEqRefutes` derivation as an
  executable checked cardinality refutation tree.
- Pad independently derived finite branch children to a common indexed depth
  without changing checker acceptance.
- Construct canonical checked equality closures for maximum-rule merges,
  minimum-rule witness families, and ordinary equality-head transitions.
- Prove exact equivalence between semantic cardinality refutations and accepted
  canonicalized finite certificates.
- Correct equality-apart closure checking to recognize transitive equality
  histories, with a regression covering a two-edge equality chain.

This closes the finite equality/cardinality refutation-tree format relative to
`CardinalityEqRefutes`. Completeness of the distinct-aware extension, exact
Rust recursive outcome correspondence, and automatic routing remain unfinished.

## [0.3.137] – 2026-08-20

### Prove equality-aware HT refutation-tree checker completeness

- Prove that every equality generated by a finite assertion history has an
  executable checked path, including reversed and concatenated paths.
- Construct a canonical representative for each finite equality class and a
  checked path from every node to its representative.
- Rebuild representative evidence after every equality-head transition while
  preserving the exact semantic state and transition payload.
- Encode every finite semantic `EqRefutes` derivation as an accepted
  `FiniteEqRefutationTree`, and combine this with checker soundness to prove an
  exact equivalence for canonicalized certificates.

This closes soundness and completeness of the finite equality-aware HT
refutation-tree certificate format relative to semantic `EqRefutes`. Exact
correspondence with all Rust recursive outcomes, cardinality recursion, and
automatic routing remain unfinished.

## [0.3.136] – 2026-08-20

### Prove finite HT refutation-tree checker completeness

- Encode every finite semantic `Refutes` derivation as a
  `FiniteRefutationTree` accepted by the executable Boolean checker.
- Preserve the exact ontology and list-backed branch state through concept,
  role, and existential head assertions and through fresh-witness
  materialization.
- Encode branch children in exact clause-head order, including zero-head
  closure, and prove the child checker accepts the complete family.
- Combine the new completeness direction with existing checker soundness to
  prove accepted finite trees are equivalent to semantic finite HT
  refutations for the certificate state.

This closes soundness and completeness of the finite equality-free HT
refutation-tree certificate format. Proving that every conclusive Rust recursive
run emits the corresponding tree, plus equality/cardinality recursion and
automatic routing, remains unfinished.

## [0.3.135] – 2026-08-20

### Certify clash-first HT runtime control

- Enumerate every node/concept pair in the finite branch state and execute the
  complementary-label clash predicate.
- Prove scan exhaustion is equivalent to semantic `HasClash` negation.
- Prove every selected clash closes the exact current state through
  `Refutes.clash`.
- Compose clash detection with the blocker-aware clause/witness selector in
  Rust's control-flow order: only a clash-free state can expand or reach an
  empty outcome.

This closes the first control branch of equality-free HT certificate recursion.
Checked empty-outcome production, full recursive-tree correspondence, and the
equality/cardinality variants remain certification tasks. It does not certify
the complete HT runtime or automatic routing.

## [0.3.134] – 2026-08-20

### Close the ordinary HT wire soundness boundary

- Prove an end-to-end fail-closed theorem for `WireCertificate.check`: every
  `.ok true` result exposes one bounded decoded payload whose advertised SAT,
  UNSAT, subsumption, or countermodel semantics holds.
- Keep decode errors and rejected Boolean checks outside the semantic evidence
  type, including malformed dimensions and out-of-range identifiers.
- Strengthen the native Rust-to-Lean cyclic blocked-leaf regression. Lean must
  accept the genuine materialized blocked model and reject the same candidate
  after removing the copied edge that witnesses the blocked existential.
- Correct the test invocation audit so the named regression actually executes;
  the verified run reports one test passed rather than relying on a zero-test
  filtered run.

This closes soundness of the ordinary HT JSON publication boundary, including
materialized blocked leaves. Exact runtime recursion completeness, regular and
equality/cardinality outcome composition, and automatic routing remain
certification tasks.

## [0.3.133] – 2026-08-20

### Certify HT empty outcomes and blocker-filtered selection

- Prove that an empty concrete successor list is exactly a zero-head
  refutation, a raw saturated terminal, or finite-node exhaustion with an
  outstanding existential. Node exhaustion is never accepted as a model.
- Add the blocker-aware obligation selector matching the runtime's
  `pairwise_blocked_by_ancestor` filtering shape.
- Prove blocker-aware scan exhaustion means every remaining unwitnessed source
  is reported blocked, while every selected unblocked obligation constructs
  the exact certified witness transition.
- Compose the blocker-aware clause/witness scans into a concrete transition
  function and prove all its nonempty results are `FirstObstructionStep`s.

The blocker Boolean remains untrusted. Accepting its terminal as satisfiable
still requires the independent checked fold, and exact Rust blocker production,
frontier production, and clash ordering remain runtime-correspondence tasks.
This does not certify the complete HT runtime or automatic routing.

## [0.3.132] – 2026-08-20

### Certify HT witness selection and concrete transitions

- Enumerate every finite role, filler, and source combination and prove that
  exhaustion is equivalent to the absence of an unwitnessed obligation.
- Select unused finite nodes and prove the selected node satisfies the semantic
  freshness predicate required by witness materialization.
- Compose clause-first and witness selection into one concrete `runtimeNext`
  function, and prove every nonempty successor family is exactly a
  `FirstObstructionStep`.
- Instantiate the finite HT decision theorem with this concrete selector, so
  transition validity, strict finite-fact growth, and child closure no longer
  remain abstract runtime premises.
- Prove that a selected empty-head grounding is a zero-child refutation, not an
  open terminal.

This closes the finite equality-free clause/witness transition enumerator.
Rust blocker filtering, frontier correspondence, clash ordering, checked leaf
production, equality/cardinality recursion, and the complete HT runtime remain
certification tasks. It does not certify automatic routing.

## [0.3.131] – 2026-08-20

### Certify finite HT clause-first runtime selection

- Define the proof-friendly executable first-match scan used to model runtime
  selection and prove its success and exhaustion properties.
- Enumerate every ontology clause and every assignment over the finite node
  universe, preserving clause order as the outer scan.
- Prove that scan exhaustion is equivalent to the absence of an undischarged
  clause grounding.
- Prove that every selected equality-free grounding constructs exactly the
  branch constructor of `FirstObstructionStep`, including body satisfaction,
  absent heads, ontology membership, and branchability.

This removes the abstract branch-selection obligation from HT runtime
correspondence. Existential witness selection, blocker-aware terminal handling,
and the complete runtime recursion remain certification tasks. It does not
certify the complete HT runtime or automatic router.

## [0.3.130] – 2026-08-20

### Certify anchored cardinality taxonomy countermodels

- Extend cardinality taxonomy cells with an optional bounded anchored
  equality/cardinality model. Positive cells retain the existing finite
  refutation evidence.
- Prove checker acceptance turns anchored positive/negative source labels into
  satisfiable-concept and non-subsumption countermodels for the same ontology
  and cardinality definitions.
- Pin anchored cell decoding to the taxonomy's exact concept, role, and
  variable dimensions. A rejected optional model falls back to the existing
  finite cell, so adding the candidate cannot remove prior certified coverage.
- Generate explicit slots from Rust equality-state edges, preserve multiplicity
  after quotient collapse, and add slot-zero coverage for regular blocker-fold
  edges.
- Exercise the Rust producer with a minimum-cardinality taxonomy and require
  the native Lean taxonomy checker to accept the complete generated matrix.

This closes checker-gated publication of anchored cardinality countermodels in
HT taxonomy cells. Complete runtime-transition correspondence and the
remaining HT runtime features remain certification tasks. It does not certify
the complete HT runtime or automatic router.

## [0.3.129] – 2026-08-20

### Bound and execute anchored cardinality certificates

- Add a versioned JSON container for the combined anchored equality and
  cardinality certificate. Decode the anchored core at the container's exact
  concept, role, and variable dimensions.
- Bounds-check every slot endpoint and role against the decoded regular node
  space, and bounds-check every cardinality definition before constructing any
  finite type.
- Expose the acceptance theorem that the decoded anchored interpretation
  satisfies both the equality-source ontology and all decoded cardinality
  definitions.
- Add `ht-anchored-cardinality-cert-check`, with fixtures showing acceptance of
  a valid empty model and fail-closed rejection of an out-of-range slot.

This closes bounded decoding and native execution for anchored cardinality
countermodels. Taxonomy-cell composition and Rust certificate production
remain certification tasks. It does not certify the complete HT runtime or
automatic router.

## [0.3.128] – 2026-08-20

### Check anchored equality and cardinality models together

- Add a combined finite certificate containing the anchored dense equality
  image, authorized path slots, and cardinality definitions.
- Check slot-zero coverage, maximum-role simplicity, authorized-key upper
  bounds, and one minimum witness assignment that simultaneously satisfies its
  edge, slot, filler-label, and nominal-anchor distinctness obligations.
- Prove Boolean acceptance constructs one anchored interpretation satisfying
  both the equality-source ontology and every cardinality definition. The
  checker does not combine unrelated ordinary and anchored models.
- Transport equality-source query labels through the dense class map into that
  same explicit-slot interpretation.
- Add executable regressions accepting repeated anonymous targets and rejecting
  repeated targets that collapse to one nominal root.

This closes the executable semantic checker beneath anchored cardinality
countermodels. Bounded JSON decoding, taxonomy-cell composition, and Rust
certificate production remain certification tasks. It does not certify the
complete HT runtime or automatic router.

## [0.3.127] – 2026-08-20

### Prove complete cardinality semantics for anchored HT models

- Prove positive concept satisfaction reflects the corresponding finite
  endpoint label, including nominal concepts represented by canonical roots.
- Relate every anchored direct role successor to an authorized finite
  `(target, slot)` key and prove a finite upper bound on those keys bounds the
  semantic successors. Nominal collapse can remove successors but cannot add
  keys.
- Prove the syntactic SROIQ simple-role criterion makes anchored role closure
  exact on maximum-cardinality roles.
- Combine anchor-safe minimum witnesses and authorized-key maxima into one
  theorem showing a single nominal-aware anchored interpretation satisfies all
  supplied cardinality definitions.

This closes the semantic minimum/maximum composition identified in v0.3.126.
An executable cardinality-tail checker, dense equality composition, and
taxonomy wire publication remain certification tasks. It does not certify the
complete HT runtime or automatic router.

## [0.3.126] – 2026-08-20

### Preserve cardinality witnesses under nominal anchoring

- Generalize the anchored ontology-model theorem from an unrestricted path
  relation to a supplied finite slot relation with checked slot-zero edge
  coverage.
- Define the exact safety condition for minimum-cardinality witnesses when
  nominal endpoints collapse to canonical roots. Repeated anonymous graph
  targets remain valid because distinct slots produce distinct paths, while
  repeated anchored targets are rejected.
- Prove that clash-free, nominal-coherent completion labels and anchor-safe
  selected witnesses construct the required number of distinct semantic role
  successors satisfying the filler.

This establishes the minimum-cardinality semantic foundation for anchored HT
countermodels. Maximum-cardinality transfer, executable checking, dense
equality composition, and taxonomy publication remain certification tasks. It
does not certify the complete HT runtime or automatic router.

## [0.3.125] – 2026-08-20

### Certify anchored equality countermodels in HT taxonomies

- Extend the mixed taxonomy wire with anchored equality evidence for
  satisfiable-concept and non-subsumption cells.
- Prove that an accepted dense equality image transports each asserted source
  label to the anchored model root, which supplies the positive and negative
  query facts needed by those countermodels.
- Decode anchored certificates directly against the shared taxonomy
  dimensions and ontology. The checker rejects mismatched dimensions, query
  positions, labels, class maps, and incomplete certificate premises.
- Let the Rust taxonomy producer emit anchored equality countermodels before
  falling back to finite quotient evidence, and exercise the complete mixed
  matrix through the native Lean checker.

This closes negative-cell publication for checker-accepted blocked equality
and nominal taxonomy branches. Cardinality-aware anchored taxonomy models and
the remaining runtime-to-transition correspondence are still certification
tasks. It does not certify the entire KM executable or automatic router.

## [0.3.124] – 2026-08-20

### Publish source-aware anchored equality SAT witnesses

- Compose the dense equality quotient and anchored-model checker with checked
  source-clause normalization and preprocessing evidence.
- Add version-5 support to the main native HT checker. Acceptance constructs a
  nonempty model of the original source ontology, not only the normalized
  runtime clauses.
- Let global equality decision search try this anchored witness when its exact
  finite quotient is not itself a checker-accepted model. A rejected witness
  remains inconclusive and iterative deepening continues.
- Exercise the Rust producer through both the specialized quotient checker and
  the main source-aware checker. The regression also rejects an incomplete
  normalization vector.

This closes global SAT publication for checker-accepted blocked equality and
nominal branches. HT taxonomy countermodels and cardinality-aware anchored
models remain separate certification tasks. It does not certify the entire KM
executable.

## [0.3.123] – 2026-08-20

### Certify dense equality quotients for anchored HT models

- Give the equality completion state and regular anchored model separate finite
  node spaces, connected by an executable class map.
- Prove checker acceptance identifies exactly the generated equality classes,
  maps onto every regular node, and transports exactly every source label,
  edge, and existential obligation.
- Add a bounded wire and native checker for the complete equality-backed
  anchored certificate. A valid two-node equality state compresses to one
  regular node; a forged class split is rejected.
- Generate dense quotient certificates from Rust union-find states, retain
  blocker folds independently from equality, and derive nominal roots from the
  quotient image. Certificate serialization now recognizes configured source
  nominals as well as runtime-expanded nominal metadata.
- Add end-to-end producer tests for cyclic blocking and nominal equality, each
  invoking the native Lean checker when configured.

This closes the representative-image publication gap identified in v0.3.122.
It certifies the finite equality-to-anchored-model boundary, not the entire KM
executable. The full Lean build passes 3,389 jobs. The complete locked release
suite passes, including the issue #3 nominal-equality regression.

## [0.3.122] – 2026-08-20

### Certify nominal-guarded equality heads in anchored HT models

- Define the clause-level condition under which finite endpoint equality lifts
  to equality in the anchored forest domain: either equality variable must be
  constrained by a checked positive nominal body atom.
- Prove nominal coherence makes that endpoint an anchor and canonical-root
  uniqueness then forces the two semantic values to coincide.
- Add executable guard detection and a dedicated anchored regular checker. It
  retains every saturation, cover, witness, clash, and RBox check while safely
  admitting guarded equality heads that the equality-free checker rejects.
- Add native-decision regressions showing a nominal-guarded equality clause is
  accepted and its unguarded counterpart is rejected. Existing complete-wire
  accepted and forged fixtures retain exit statuses 0 and 1.

This certifies the equality-head pattern needed for nominal clauses inside the
anchored model. Equality/nominal publication still requires checked evidence
that the regular certificate is the representative image of Rust's equality
state. The full Lean build passes 3,387 jobs. The locked serial release suite
passes 2,120 tests with 8 ignored.

## [0.3.121] – 2026-08-20

### Compose anchored HT with regular saturation and RBox certification

- Prove that anchored semantic atom matches project to the finite endpoint
  cover and that concept and existential heads lift back to anchored values.
- Prove normalized subrole, inverse-role, role-chain, and reflexive clauses in
  the anchored role closure, then combine them with residual cover discharge.
- Compose the existing regular certificate checker with nominal-label and
  redirected-witness checks. Acceptance now constructs an anchored
  nominal-aware model of the exact decoded ontology.
- Extend the bounded JSON wire and native checker to validate the complete
  regular certificate plus nominal roots. The accepted fixture exits 0 and a
  forged nominal root exits 1.

This closes the regular saturation and RBox composition gap from v0.3.120.
Publication for equality and nominals still requires a proof and checked wire
connecting Rust union-find representatives to canonical nominal roots. The
full Lean build passes 3,387 jobs. The locked serial release suite passes 2,120
tests with 8 ignored.

## [0.3.120] – 2026-08-20

### Check anchored HT premises through a bounded wire

- Add executable Boolean checks for clash freedom, exact positive and negative
  nominal-label coherence, and redirected existential witnesses.
- Prove checker acceptance derives the corresponding semantic premises of the
  anchored canonical-model theorem.
- Add a versioned bounded wire with one optional nominal root per concept;
  reject malformed lengths and out-of-range node, role, concept, redirect, and
  nominal-root identifiers.
- Add the native `ht-anchored-premises-check` executable and accepted/forged
  JSON fixtures. The valid document is accepted and a forged nominal root exits
  with rejection status 1.

This checker does not yet carry regular saturation, RBox cover evidence, or the
equality-closure proof connecting Rust's union-find representatives to nominal
roots. Those must be composed into one SAT certificate before publication.
The full Lean build passes 3,387 jobs. The locked serial release suite passes
2,120 tests with 8 ignored.

## [0.3.119] – 2026-08-20

### Prove the anchored nominal-aware HT interpretation

- Define direct edges on the canonical rooted forest so witnesses entering an
  anchor land on its unique root.
- Close those edges under checked subroles, inverse roles, role chains, and
  reflexive roles, and prove projection to the finite endpoint relation.
- State the exact nominal-label coherence and redirected-witness premises a
  certificate must check.
- Prove every finite label and saturated head atom is satisfied by the anchored
  interpretation, including negative nominals, equality heads, and existential
  witnesses.
- Prove the converse for guarded body atoms and compose both directions into a
  canonical-model theorem: clash freedom, nominal coherence, redirected
  witnesses, and anchored saturation imply that the interpretation models the
  ontology.

This completes the abstract semantic model theorem for the anchored domain.
The remaining executable milestone must decode and check the premises from
Rust's equality representatives, nominal carriers, blocker redirects, and
saturation evidence before equality/nominal regular SAT can publish.
The full Lean build passes 3,385 jobs. The locked serial release suite passes
2,120 tests with 8 ignored.

## [0.3.118] – 2026-08-20

### Prove canonical nominal roots for regular HT models

- Add a rooted-forest path domain for the equality/nominal-aware regular model.
- Preserve full path identity at anonymous endpoints while requiring every
  designated anchor endpoint to use one canonical root value.
- Prove any two anchored values with the same endpoint are equal and every
  successor entering an anchor is redirected to that root.
- Define the nominal concept interpretation by its selected root and prove each
  selected nominal has exactly one extension element.

These proofs establish the domain-identity layer needed before equality and
nominals can use regular HT SAT publication. They do not yet prove that Rust's
equality representatives and nominal carriers satisfy the anchor conditions,
or that the full anchored role interpretation models every source clause.
The full Lean build passes 3,385 jobs. The locked serial release suite remains
green with 2,120 passed and 8 ignored tests.

## [0.3.117] – 2026-08-20

### Compose regular HT decisions with source preprocessing

- Extend the source-aware HT certificate envelope with regular SAT and finite
  UNSAT decisions.
- Prove that either result transfers through checked trigger absorption,
  contrapositive extension, and body-equality normalization to the original
  source ontology.
- Switch the equality-free global certification API from finite folded SAT to
  the regular-model decision route. Publication remains fail closed through
  the main `ht-cert-check` executable.
- Teach the main checker to accept an unwrapped regular decision when no source
  transformation occurred and a source-wrapped decision otherwise.
- Add a Rust-to-Lean regression that emits a normalized regular decision and
  requires acceptance by the main checker.
- Fix a test-only checker-path ownership error exposed by the clean release
  rebuild.

The full Lean build passes 3,384 jobs. The locked serial release suite passes
2,120 tests with 8 ignored, including native Lean acceptance of regular SAT,
finite UNSAT, and source-wrapped regular evidence. Equality and cardinality
global decisions retain their existing certified paths; extending regular
models through those features remains separate work.

## [0.3.116] – 2026-08-20

### Certify the regular HT global decision envelope

- Add a versioned sum wire with exactly two global outcomes: regular SAT and
  finite UNSAT.
- Reject finite payloads carrying SAT, taxonomy, or query evidence under the
  UNSAT tag.
- Prove checker acceptance yields either a nonempty regular model of the exact
  normalized ontology or excludes every nonempty model of that ontology.
- Add `ht-regular-decision-cert-check` and checked SAT/UNSAT fixtures.
- Make Rust's exhaustive equality-free decision search emit both envelope
  branches and pass Rust-emitted SAT and UNSAT documents through Lean.

The next bridge composes this normalized-ontology decision with the existing
source body-equality normalization and preprocessing certificate. Production
publication is not switched until that composition is checked end to end.
The full Lean build passes 3,384 jobs. The locked release suite passes 2,119
tests with one test thread; the parallel harness has unrelated tests that race
through process-global environment variables.

## [0.3.115] – 2026-08-20

### Connect the Rust HT producer to regular-model evidence

- Partition exact subrole, inverse-role, binary-chain, and reflexive clauses
  into the normalized role-rule wire; reject unsupported residual heads.
- Serialize blocker redirects instead of claiming that finite node identity is
  the blocked model's domain identity.
- Supply outgoing finite witness edges for blocked obligations while retaining
  redirect-based path semantics.
- Compute the least finite endpoint-role cover to closure under every decoded
  role rule.
- Add cross-language regressions in which Lean accepts Rust-emitted cyclic and
  combined role-closure regular certificates.

The ordinary decision API is not switched in this release. It needs a checked
sum envelope so regular SAT and finite refutation evidence can share one
publication boundary without trusting Rust to select the semantic outcome.
The locked release suite passes 2,118 tests, including both native Lean
cross-language checks.

## [0.3.114] – 2026-08-20

### Expose native regular HT certificate checkers

- Add `ht-regular-cert-check` for the bounded regular graph wire.
- Add `ht-regular-cardinality-cert-check` for the regular graph, authorized
  witness slots, and cardinality-definition wire.
- Keep decoding and semantic checking inside Lean; malformed bounds and failed
  semantic checks return nonzero status.
- Add checked-in acceptance and malformed-redirect command-line fixtures.

These executables are the fail-closed acceptance targets for the Rust regular
certificate producer. The producer connection and equality/nominal-root
extension remain pending.

## [0.3.113] – 2026-08-20

### Add the bounded regular HT cardinality wire

- Add a versioned JSON wrapper carrying the bounded regular graph certificate,
  authorized `(source,role,target,slot)` tuples, and cardinality definitions.
- Check every slot source, role, and target ID against the decoded base bounds.
- Reuse the proved cardinality-definition decoder for marker, role, filler,
  kind, and bound fields.
- Prove `DecodedRegularCardinalityCertificate.check_models`: successful decode
  and checker acceptance yield one interpretation modeling the exact ontology
  and all decoded cardinality definitions.
- Add native acceptance and out-of-range slot rejection regressions.

The regular HT trust boundary now covers role closure, existential witnesses,
and cardinality on equality-free completion graphs. Equality and nominal roots,
then the Rust producer connection, remain.

The full Lean build passes across 3,383 jobs. Rust reasoning code remains
unchanged from v0.3.101's complete release suite.

## [0.3.112] – 2026-08-20

### Add the executable regular HT cardinality checker

- Check minimum restrictions by enumerating finite node witnesses and requiring
  exact authorized slots for every `Fin bound` index.
- Check maximum restrictions by enumerating selections from the finite slot
  list. Every selection of `bound + 1` authorized slots must repeat a
  `(target,slot)` key.
- Prove any hypothetical injective semantic family of authorized maximum keys
  maps back to a rejected slot selection, establishing `HasAtMost`.
- Combine the regular base checker, zero-slot coverage, minimum/maximum checks,
  and simple-role validation in one executable `check`.
- Prove `check_models`: acceptance yields one interpretation modeling the exact
  ontology and all decoded cardinality definitions.
- Add native regressions accepting compatible minimum-one/maximum-one
  restrictions and rejecting an activated maximum-zero violation.

The maximum proof uses standard `Classical.choice` to select a slot-list index
for each semantic membership witness. No `sorryAx` is present. The bounded
cardinality JSON wire remains next.

The full Lean build passes across 3,382 jobs. Rust reasoning code remains
unchanged from v0.3.101's complete release suite.

## [0.3.111] – 2026-08-20

### Prove regular HT cardinality and simple-role integration

- Define `SyntacticallySimple`: no subrole, inverse, chain, or reflexive rule
  can introduce an edge for a designated number-restricted role.
- Prove syntactic simplicity implies `SimpleExact`, so every regular semantic
  edge of that role is a direct authorized path edge.
- Add an executable Boolean simplicity test over decoded role-rule lists and
  prove its soundness.
- Add `FiniteRegularCardinalityCertificate` with explicit authorized witness
  slots and complete cardinality definitions.
- Prove certificate validity yields one regular interpretation that models both
  the exact decoded ontology and every minimum/maximum cardinality definition.

The cardinality validity contract is semantic in this release. The next step is
the explicit Boolean minimum-slot and maximum-key checker, followed by its wire
decoder.

The full Lean build passes across 3,382 jobs. Rust reasoning code remains
unchanged from v0.3.101's complete release suite.

## [0.3.110] – 2026-08-20

### Add the bounded regular HT JSON wire

- Add JSON wire types for regular graph facts, redirects, role-cover edges,
  subroles, inverse roles, chains, reflexivity, normalized role clauses, and
  residual clauses.
- Decode every node, concept, role, and variable ID through a checked `Fin`
  bound before constructing certificate data.
- Require a positive node count and exactly one in-range redirect target per
  finite node.
- Prove `DecodedRegularCertificate.check_models`, connecting decoded checker
  acceptance to the exact regular-unravelling model theorem.
- Add native decoder regressions for a valid certificate, malformed redirect
  length, and out-of-range IDs.

Cardinality slots and equality/nominal roots are not yet fields of this wire.
The Rust HT producer also does not emit this format yet.

The full Lean build passes across 3,381 jobs. Rust reasoning code remains
unchanged from v0.3.101's complete release suite.

## [0.3.109] – 2026-08-20

### Add the executable regular HT certificate checker

- Add `FiniteRegularCertificate`, containing finite labels, edges,
  obligations, redirects, role-cover tuples, normalized role rules and clauses,
  and guarded residual clauses.
- Implement explicit Boolean checks for role authorization, guarded bodies,
  liftable heads, clashes, existential witnesses, redirect compatibility,
  direct/subrole/inverse/chain/reflexive cover closure, and residual discharge
  over every finite variable assignment.
- Prove local cover closure contains the complete inductive endpoint role
  relation.
- Prove `check_sound` and `check_models`: checker acceptance constructs an
  infinite regular unravelling that models the certificate's exact decoded
  ontology.
- Add native executable regressions showing an empty certificate accepts and a
  certificate omitting a required direct cover edge rejects.

The checker deliberately uses explicit finite loops rather than a classical
decision instance. Cardinality slots, equality/nominal roots, JSON decoding,
and the Rust producer connection remain to be added to this regular wire.

The full Lean build passes across 3,380 jobs. Rust reasoning code remains
unchanged from v0.3.101's complete release suite.

## [0.3.108] – 2026-08-20

### Reduce regular HT saturation to a finite endpoint certificate

- Define `EndpointRole`, the finite-node projection of regular path-role
  closure, and prove every semantic regular role edge projects into it.
- Define endpoint truth and discharge for residual HT clauses. Prove endpoint
  discharge lifts to infinite paths when residual heads are concepts or
  existential obligations; normalized role heads remain covered by v0.3.107.
- Define a certificate-supplied finite role-edge cover. Prove any
  over-approximation of endpoint role closure is sound for residual body
  matching: extra body matches can only make certification more restrictive.
- Prove `regularUnravelling_models_partition_of_cover`. Its saturation inputs
  quantify only over finite completion-graph nodes and a finite role cover;
  infinite paths occur solely in the constructed semantic model.

The next executable step is a decoded list representation and Boolean checker
for cover closure, residual assignment discharge, redirect compatibility, and
authorized witness slots, followed by the Rust producer connection.

The full Lean build passes across 3,379 jobs. Rust reasoning code remains
unchanged from v0.3.101's complete release suite.

## [0.3.107] – 2026-08-20

### Remove normalized role clauses from HT saturation evidence

- Define a typed normalized role-clause syntax for subroles, inverse roles,
  binary chains/transitivity, and reflexivity, together with its exact
  translation into HT clauses.
- Prove every authorized normalized role clause is modeled directly by the
  regular unravelling relation, without finite-fold or path-saturation evidence.
- Lift the result over lists of role clauses.
- Prove `regularUnravelling_models_partition`: an ontology partitioned into
  authorized role clauses and guarded residual clauses is modeled when only the
  residual partition satisfies the regular path-saturation contract.

This narrows the executable certificate payload to concept propagation,
existential/cardinality closure, blocking compatibility, and equality/nominal
conditions. Role hierarchy and chain clauses are semantic by construction.

The full Lean build passes across 3,379 jobs. Rust reasoning code remains
unchanged from v0.3.101's complete release suite.

## [0.3.106] – 2026-08-20

### Construct the regular HT ontology model

- Define path-level syntactic truth for concepts, full regular roles,
  existential obligations, and equality.
- Define regular discharge and saturation contracts over assignments into the
  infinite path domain, including role matches introduced by subroles,
  inverses, chains/transitivity, and reflexivity.
- Prove every path-level atom in a discharged head is semantically true.
  Existential obligations obtain fresh authorized path witnesses through the
  redirected completion graph.
- Prove `regularUnravelling_models_of_saturated`: every clash-free,
  witness-complete regular saturation of a guarded ontology is a genuine model
  of that ontology.

This establishes the semantic model endpoint missing from finite-fold
acceptance. The remaining HT work is to derive path-level saturation, redirect
compatibility, role rules, simplicity, and authorized slots from an executable
Rust completion-graph certificate, then handle equality and nominal roots in
that wire connection.

The full Lean build passes across 3,379 jobs. Rust reasoning code remains
unchanged from v0.3.101's complete release suite.

## [0.3.105] – 2026-08-20

### Construct regular HT role closure

- Define the regular unravelling role relation as the least inductive closure
  of authorized direct path edges under unary subroles, inverse-role bridges,
  binary chains/transitivity, and reflexivity.
- Prove each normalized role-rule family holds in the resulting interpretation
  directly from its closure constructor.
- Define `SimpleExact`: role closure adds no non-direct edge for a designated
  number-restricted role.
- Prove direct minimum-cardinality models lift into regular role closure without
  an extra premise, while maximum cardinalities lift under `SimpleExact`.
- Lift this simplicity bridge across the complete cardinality-definition list.

The remaining role work is executable decoding and validation of regular role
rules and simple-role declarations from the Rust wire. The full HT ontology
model theorem must additionally transfer concept and existential clauses across
the unravelling and handle equality/nominal roots.

The full Lean build passes across 3,379 jobs, and the locked Rust release check
passes. Rust reasoning code remains unchanged from v0.3.101's complete release
suite.

## [0.3.104] – 2026-08-20

### Prove regular HT cardinality satisfaction

- Define the finite authorized-key predicate for one path endpoint and role.
- Prove a finite `HasAtMost n` bound on authorized keys transfers to all direct
  semantic successors of the corresponding unravelled path.
- Combine authorized minimum witnesses and maximum key bounds into
  `unravelling_modelsCardinalityDef`, which proves the regular interpretation
  satisfies one complete cardinality definition.
- Lift the result to `unravelling_modelsCardinalityDefs`, certifying the entire
  decoded cardinality side channel from finite per-definition closure
  obligations.

The remaining cardinality interaction is the SROIQ simplicity boundary: roles
used by number restrictions must not gain extra successors through complex role
closure. Equality/nominal roots and the full ontology model theorem also remain.

The full Lean build passes across 3,379 jobs, and the locked Rust release check
passes. Rust reasoning code remains unchanged from v0.3.101's complete release
suite.

## [0.3.103] – 2026-08-20

### Bound regular HT successor slots

- Refine the v0.3.102 path domain with an explicit slot-admissibility relation.
  A path step and its direct semantic role edge now exist only when the finite
  certificate authorizes that `(source, role, target, slot)` tuple.
- Require existential and minimum-cardinality witness theorems to exhibit the
  corresponding authorized slots.
- Prove semantic direct successors inject into finite `(target-node, slot)`
  keys. Unravelling therefore introduces no extra direct successors beyond the
  authorized key set, reducing maximum-cardinality preservation to a finite
  checker bound on that set.

This refinement prevents unrestricted slot replication from violating at-most
restrictions. The full role interpretation still needs regular role-hierarchy
closure and its separate simplicity argument for number-restricted roles.

The full Lean build passes across 3,379 jobs, and the locked Rust release check
passes. Rust reasoning code remains unchanged from v0.3.101's complete release
suite.

## [0.3.102] – 2026-08-20

### Construct the regular HT path domain

- Define the regular unravelling domain of a blocked completion graph as typed
  successor paths. A redirect map selects the blocker node whose finite outgoing
  edges are replayed at each blocked path endpoint.
- Include an explicit natural-number witness slot in every path step. Reusing a
  finite graph node therefore creates a new semantic value, and different
  cardinality slots remain distinct.
- Prove every redirected existential obligation obtains a satisfying direct
  successor at strictly greater path depth.
- Prove a `Fin n` family of completion-graph witnesses induces an injective
  family of `n` semantic successors satisfying the requested filler literal.

These results are the first constructive part of the regular/unravelled HT model
required after v0.3.101 ruled out finite-fold completeness. Role-hierarchy
closure, maximum-cardinality preservation, equality/nominal roots, and the full
ontology-model theorem remain.

The full Lean build passes across 3,379 jobs, and the locked Rust release check
passes. Rust reasoning code is unchanged from v0.3.101, whose complete release
suite passed with 2,068 tests and 8 intentional ignores.

## [0.3.101] – 2026-08-20

### Align equality-aware folds and expose the regular-model boundary

- Copy incoming blocker-class edges in the equality-aware and
  cardinality-aware Rust certificate producers. Their outgoing-only behavior
  did not match the bidirectional Lean fold introduced in v0.3.99.
- Add a Rust regression covering both producers on a cyclic blocked branch.
- Add a Lean counterexample proving that full pairwise-signature equality does
  not make one-round finite folding closed under a binary role chain. The base
  endpoint is valid, but the fold creates a new chain grounding whose required
  head edge is absent, and the exact checker rejects it.
- State the resulting architecture accurately: finite folded models remain a
  sound acceptance path, while complete SROIQ certification needs a checked
  regular/unravelled model because inverse roles with counting do not have the
  finite-model property.

The full Lean build passes across 3,378 jobs. The locked Rust release suite
passes with 2,068 tests, 8 intentional ignores, all integration suites, and the
native Lean HT publication checker enabled. This milestone removes a concrete
Rust/Lean mismatch and mechanically rules out an invalid finite-fold
completeness argument.

## [0.3.100] – 2026-08-20

### Resume HT search after certificate rejection

- Move the native Lean check for an open HT decision candidate inside iterative
  deepening. A rejected finite fold is now inconclusive and doubles the node
  budget instead of escaping the search as a terminal publication error.
- Apply the retry to equality-free, equality-aware, and cardinality-aware
  decisions. Taxonomy cells inherit the same behavior through those decision
  procedures.
- Keep the outer publication check, so accepted evidence is independently
  checked again before it becomes a public result.
- Use collision-resistant per-process candidate files and fail explicitly at a
  configured node cap or integer overflow.

The full Rust release suite passes with 2,066 unit tests, 8 intentional ignores,
all integration suites, and the native Lean HT publication checker enabled.
This change prevents a rejected blocked fold from becoming a final answer. It
does not prove that repeated deepening eventually produces accepted evidence;
multi-edge role-chain closure remains part of the HT completeness work.

## [0.3.99] – 2026-08-20

### Make certified HT folds bidirectional

- Fix a concrete completeness defect in blocked-model materialization: copy
  incoming as well as outgoing blocker edges to the blocked node. Outgoing-only
  folds cannot preserve reversed role clauses such as `R(x,y) → S(y,x)`.
- Apply the correction to equality-free and equality-aware Lean folds and to
  both Rust certificate producers.
- Generalize exact edge provenance and all existing role/concept fold-transfer
  theorems across incoming and outgoing copied premises.
- Prove reversed role implications remain valid after the bidirectional fold.
- Add a Rust regression requiring an incoming blocker edge to be materialized.

The full Rust release suite passes with 2,066 unit tests, all integration suites,
and the native Lean HT checker enabled. This closes the single-edge inverse-role
fold shape; multi-edge role chains and equality/cardinality heads remain.

## [0.3.98] – 2026-08-20

### Preserve guarded concept propagation across pairwise folds

- Prove closed labels and closed role edges are invariant under equality-class
  replacement.
- Define the finite fold-label compatibility contract and prove equal complete
  equality-aware pairwise blocking signatures imply it.
- Prove pairwise folds preserve both central normalized propagation shapes:
  `R(x,y) ∧ A(y) → B(x)` and `R(x,y) ∧ A(x) → B(y)`.
- Derive each copied-edge case from exact edge provenance, evaluate the premise
  at the blocker, and transport the resulting signed concept label through the
  blocker/blocked signature equality.

The remaining role-sensitive fold cases are multi-edge role chains, reversed
role heads/inverse context, and equality/cardinality heads. The common
single-edge concept and role propagation forms are now covered.

## [0.3.97] – 2026-08-20

### Preserve role implications across equality-aware folds

- Prove exact provenance for every materialized fold edge: it is either a base
  edge or was copied from a base edge through a specific supplied blocker pair
  whose source lies in the blocker's equality class.
- Use that provenance to prove every base closed-role implication remains valid
  after folding. When a premise edge is copied, the corresponding base
  conclusion is copied back through the same fold.
- Correct the README's stale ELC statement: wire-v5 checker-backed production
  already supports certified residual compilation, NF3 witnesses, and
  canonical-model composition, while unchecked repair output remains excluded.

This closes sub-role and same-orientation role-bridge transfer. Multi-edge role
chains, inverse orientations, concept guards adjacent to copied edges, and
equality/cardinality heads remain in the role-sensitive HT fold proof.

## [0.3.96] – 2026-08-20

### Prove role-free equality-fold acceptance

- Prove materialized folds preserve equality-closure validation, quotient clash
  freedom, witness completion, and every closed fact from the base endpoint.
- Define the role-free-body fragment and prove adding fold edges cannot create
  a new true body in that fragment.
- Prove saturation preservation and executable fold acceptance for every valid
  equality endpoint whose clause bodies are role-free.

The remaining blocked-search proof is now limited to normalized clauses whose
bodies contain role atoms. Added fold edges can activate those bodies, so their
saturation requires the full pairwise blocker signature rather than generic
edge monotonicity.

## [0.3.95] – 2026-08-20

### Characterize equality-aware blocked-fold acceptance exactly

- Prove an equality-aware fold is accepted exactly when its materialized
  endpoint has a valid equality closure, guarded clauses, quotient clash
  freedom, completed witnesses, and quotient saturation.
- Add a direct acceptance theorem exposing those five concrete obligations.
- Extend the equivalence through minimum and maximum cardinality definitions:
  cardinality-aware fold checking succeeds exactly when the endpoint contract
  holds and its quotient model satisfies every definition.

These results make the remaining completeness boundary explicit. They do not
assume or claim that every runtime blocker preserves saturation; that result
must be proved for KM's normalized clause grammar and concrete pairwise fold.

## [0.3.94] – 2026-08-20

### Prove cardinality-aware HT SAT-checker completeness

- Prove the finite equality-quotient checker complete for activated minimum
  cardinality restrictions by selecting raw representatives for semantic
  quotient witnesses.
- Prove it complete for maximum restrictions by showing every enumerated
  `(n + 1)`-tuple either misses the successor predicate or is non-injective in
  the equality quotient.
- Establish exact `checkCardinalityDef` and `checkCardinalityDefs` equivalences
  with their semantic quotient-model contracts.
- Combine these results with equality-aware SAT-checker exactness, proving
  `checkEqSatWithCardinality = true` exactly when the finite endpoint is valid
  and its quotient model satisfies every cardinality definition.

All new results avoid `sorry` and `admit`; their axiom reports contain only
standard Lean quotient/classical principles. Concrete blocked-fold acceptance,
especially saturation preservation after folding, remains the next HT
completeness obligation.

## [0.3.93] – 2026-08-20

### Prove equality-aware HT SAT-checker completeness

- Define the exact semantic endpoint contract for an equality certificate:
  checked equality closure, guarded clauses, quotient clash freedom, witness
  completion, and saturation modulo the node equivalence.
- Prove closed-clash detection complete when the supplied representative paths
  correctly describe the equality closure.
- Prove every endpoint satisfying that contract is accepted by `checkEqSat`.
- Combine this with the existing soundness direction as
  `checkEqSat = true ↔ Valid`.
- Audit the new results without `sorry` or `admit`; their axiom reports contain
  only standard Lean quotient/classical principles.

This establishes the executable acceptance target for equality-aware folds.
The next acceptance milestone extends exactness through cardinality definitions
and proves concrete blocked endpoints satisfy these contracts.

## [0.3.92] – 2026-08-20

### Prove finite HT SAT-checker completeness

- Prove the converse of the finite HT SAT checker's existing soundness theorem:
  every guarded, clash-free, witness-complete, saturated finite endpoint is
  accepted by `checkSat`.
- Package both directions as `checkSat = true ↔ Valid`, so the executable
  checker is exact for its stated endpoint invariant.
- Lift checker completeness to blocked finite folds and state the exact four
  concrete obligations sufficient for fold acceptance: guarded clauses, clash
  freedom, witnesses after materializing blocker edges, and saturation.
- Audit the theorems without `sorry` or `admit`; their axiom reports contain
  only standard Lean quotient/classical principles.

This converts blocked-fold acceptance from a one-way trust boundary into a
provable target. The next HT obligation is deriving these four endpoint facts
from every concrete certified blocker output, followed by the analogous
equality/cardinality acceptance guarantees.

## [0.3.91] – 2026-08-20

### Use total certified search for every HT taxonomy cell

- Add a certification-only taxonomy-query decision boundary for concept
  satisfiability and ordered subsumption cells.
- Dispatch each query to equality-free, equality-aware, or
  distinct-cardinality iterative search from its exact root labels.
- Construct positive cells from the returned checked finite model and negative
  cells from the returned exhaustive refutation. No taxonomy verdict is read
  from the optimized `consistent` probe.
- Feed those independently decided cells into the existing Lean theorem for a
  complete square taxonomy matrix. Publication still requires both native Lean
  checkers to accept the global and matrix evidence.
- Keep inverse roles, nominals, and native ABoxes outside the certified HT
  fragment. Default and benchmark routes remain unchanged.
- Validate the full Rust suite (2,066 passed, 8 ignored) and all six HT
  publication integrations against the native global and taxonomy Lean
  checkers.

This removes the last optimized-tableau verdict oracle from checker-gated HT
global consistency and complete taxonomy publication on the certified fragment.

## [0.3.90] – 2026-08-20

### Use total certified search as the HT global verdict boundary

- Add one certification-only global decision API that dispatches to the proved
  equality-free, equality-aware, or distinct-cardinality iterative search for
  the exact normalized clause set.
- Make the production Lean-certified HT route obtain both its consistency
  verdict and checker-ready evidence from that total decision API. It no longer
  asks the optimized tableau for a verdict and attempts to certify it afterward.
- Keep publication fail closed through the existing native Lean checker. The
  default classification route and all benchmark paths remain unchanged.
- Correct stale HT documentation: occupied canonical witness addresses and
  equality/cardinality frontier termination are already proved. Inverse roles,
  nominals, native ABoxes, and the taxonomy probe loop remain explicit
  certification obligations.
- Validate the full Rust suite (2,066 passed, 8 ignored) and all six HT
  publication integrations against the native global and taxonomy Lean
  checkers.

This connects the total sound-and-complete HT global decision search to the
runtime trust boundary for its certified fragment.

## [0.3.89] – 2026-08-20

### Prove checked distinct-cardinality HT search total

- Generalize the finite rooted-address and iterative-doubling theorem to an
  arbitrary finite witness-slot type.
- Give ordinary existential witnesses and minimum-cardinality witnesses
  distinct tagged slots. Minimum siblings retain their definition and witness
  indices, so the checked address document cannot collapse them.
- Add an executable Lean cardinality-frontier checker and make malformed,
  duplicate, or inconsistent runtime frontier evidence fail closed.
- Prove that checked cardinality frontiers cannot persist through KM's
  doubling schedule.
- Make certification-only blocking, labels, role reads, minimum expansion, and
  maximum merging equality-quotient aware. A blocked open state copies all
  quotient-visible blocker edges before the existing finite-model checker
  accepts it.
- Prove that acceptance of a finite equality fold by the cardinality checker
  yields a model of both the exact normalized ontology and its decoded
  distinct-cardinality definitions.
- Add native-checker regressions for distinct minimum siblings and a cyclic
  minimum-cardinality ontology.
- Validate all 3,378 Lean jobs and the full Rust suite: 2,066 library tests
  passed, 8 ignored benchmarks, and every integration suite passed.

This closes total sound and complete decision search for the checker-gated
distinct-cardinality HT fragment. The default classification route is
unchanged.

## [0.3.88] – 2026-08-20

### Prove equality-aware iterative-deepening totality

- Make certification-only equality frontiers retain the exact rooted witness
  addresses reconstructed from Rust's creation-parent metadata. Invalid or
  duplicate addresses now fail closed instead of entering another round.
- Extend Lean's checked equality outcome with the independently checked
  frontier document.
- Prove that equality-aware expanded paths cannot exceed the finite quotient
  pairwise-signature vocabulary.
- Prove that checked equality frontiers cannot persist through KM's doubling
  schedule. Some round therefore returns a checked SAT quotient model or a
  checked UNSAT refutation for the exact normalized ontology.
- Add a runtime regression checking the one-node equality frontier's exact
  rooted address.
- Validate all 3,377 Lean jobs and the full Rust suite: 2,064 library tests
  passed, 8 ignored benchmarks, and every integration suite passed.

Together with v0.3.87's checked equality fold, this closes total sound and
complete decision search for the certified equality-aware HT fragment.
Distinct-cardinality blocking and totality remain separate obligations.

## [0.3.87] – 2026-08-20

### Check equality-aware finite blocking folds

- Add an equality-quotient pairwise blocker to certification-only HT search.
  It compares equality-closed node labels, predecessor labels, and role sets in
  both predecessor directions.
- Track exact witness ancestry during equality search and stop expanding an
  unwitnessed obligation only when an ancestor has the same full quotient
  signature.
- Materialize every outgoing edge visible at the blocker's equality class at
  the blocked node. The ordinary executable Lean equality checker still checks
  all ontology groundings, clashes, equality closure, and witness obligations,
  so an incorrect proposed fold cannot publish SAT.
- Add `FiniteEqFoldCertificate` in Lean and prove that every accepted fold has
  a model of the exact unchanged ontology, without assuming that the supplied
  fold relation is valid.
- Add a cyclic existential regression that terminates through quotient-aware
  pairwise blocking and is accepted by the native Lean checker.
- Validate the release with all 3,377 Lean build jobs and the complete Rust
  suite: 2,064 library tests passed, 8 ignored benchmarks, and every integration
  suite passed, including the issue #3 soundness regression.

This closes checked finite-model folding for equality-aware HT search.
Cardinality-aware blocking still needs a stronger signature preserving apart
and number-restriction context before its frontier termination can be closed.

## [0.3.86] – 2026-08-20

### Bound equality-quotient blocking signatures

- Align Rust equality and distinct-cardinality clause satisfaction with Lean's
  existing closed-state semantics: concepts, roles, and existential obligations
  are now read modulo the complete node equivalence relation. Equality-free
  search and the already quotient-aware clash check remain unchanged.
- Add a regression where concept, role, obligation, and clash facts are visible
  through equality closure.
- Define Lean's full equality-quotient pairwise blocking signature from closed
  node and predecessor labels plus closed forward and backward role sets.
- Prove equal signatures preserve the full closed predecessor context.
- Prove every overlong equality-aware predecessor path repeats a quotient
  signature, and every path with injective signatures is bounded by the finite
  signature vocabulary.

These results establish the finite combinatorial depth bound needed by
equality-aware blocking. They do not yet prove that the concrete Rust fold
refines a sound equality/cardinality blocking rule, so equality/cardinality
frontier totality remains open.

## [0.3.85] – 2026-08-20

### Check equality and cardinality open-leaf models

- Preserve the exact active-node equality quotient when bounded equality or
  distinct-cardinality search reaches a saturated open leaf.
- Add certification-only equality and cardinality global decision APIs. They
  publish SAT only through the existing executable Lean quotient-model checks,
  publish UNSAT only through exhaustive checked refutations, and leave node
  frontiers inconclusive.
- Serialize open leaves with their active node count rather than the larger
  allocation budget, excluding unused blank nodes from the finite model.
- Prove in Lean that accepted equality SAT leaves have a nonempty model and
  accepted cardinality SAT leaves have a nonempty model satisfying the exact
  decoded cardinality definitions.
- Compose those SAT theorems with the existing checked-closure theorems into
  typed decision outcomes whose only inconclusive constructor is `frontier`.
- Test equality-free, equality, and cardinality SAT/UNSAT decision evidence
  through the native Lean checker.

This completes checked terminal semantics for bounded equality and cardinality
search. Total certification still requires proving that equality/cardinality
frontiers cannot persist under iterative deepening.

## [0.3.84] – 2026-08-20

### Separate bounded cardinality-aware HT outcomes

- Replace the distinct-cardinality refutation search's `Option` plus mutable
  node-cap flag with explicit closed, open-branch, and frontier outcomes.
- Preserve those outcomes through disjunctive heads, existential witnesses,
  minimum-cardinality expansion, and maximum-cardinality merge branches.
- Retry iterative deepening only after a genuine frontier and decline directly
  on an open branch.
- Add a Rust regression covering all three outcomes.
- Define the matching Lean outcome boundary and prove that a checked
  distinct-cardinality closure excludes every nonempty model of the exact
  ontology and cardinality definitions.

Open cardinality branches and frontiers remain deliberately inconclusive.
Their model extraction and equality-aware blocking termination are still open
certification obligations.

## [0.3.83] – 2026-08-20

### Separate bounded equality-aware HT outcomes

- Replace the equality-refutation search's ambiguous `Option` plus mutable
  node-cap flag with explicit closed, open-branch, and frontier outcomes.
- Propagate open branches and exhausted node budgets independently through
  disjunctive and existential recursion, so iterative deepening retries only a
  genuine frontier.
- Add a Rust regression covering all three outcomes.
- Define the matching typed Lean outcome boundary and prove that every checked
  closed equality refutation excludes a nonempty model of the exact ontology.
  The theorem deliberately leaves open branches and frontiers inconclusive.

This removes an unsafe control-flow ambiguity but does not yet certify total
equality-aware search. Equality-aware model extraction, blocking termination,
and cardinality-search totality remain subsequent milestones.

## [0.3.82] – 2026-08-20

### Complete the checked equality-free HT decision composition

- Define the exact checked outcome contract for each equality-free doubling
  round: finite SAT certificate, finite UNSAT refutation, or checked rooted
  address frontier.
- Prove SAT terminals have a nonempty model of the exact normalized ontology.
- Prove empty-root UNSAT terminals exclude every nonempty model of that
  ontology.
- Prove that any run returning one checked outcome per round must reach a
  conclusive round: assuming only frontiers contradicts the checked finite
  address bound for `8 * 2^round`.
- Return the semantics of the actual conclusive outcome, rather than using an
  unrelated classical SAT/UNSAT excluded-middle argument.

This completes the typed checked-decision composition for equality-free HT.
The next HT milestone extends total certification across equality and
cardinality search.

## [0.3.81] – 2026-08-20

### Check the concrete equality-free HT frontier refinement

- Add an executable Lean frontier checker for untrusted rooted witness paths.
- Decode natural-number role and concept identifiers into finite types, reject
  malformed counts, enforce the exact full-signature depth bound, and require
  pairwise-distinct rooted addresses.
- Prove that checker acceptance supplies the injective `WitnessAddress` map
  consumed by the iterative-deepening theorem.
- Compose the wire theorem with KM's `8 * 2^round` schedule, proving that a
  fixed-vocabulary sequence of full checked frontiers cannot persist forever.
- Serialize the concrete Rust frontier in that exact wire format and fail
  closed before returning a frontier if its capped exact cardinality check
  fails.
- Verify that Lean accepts a real cyclic frontier and rejects a duplicate
  address. The exact Rust cardinality routine is tested at four boundaries.

This closes the concrete outer-frontier refinement for equality-free HT.
Equality/cardinality HT and the remaining complete-runtime composition remain
separate certification milestones.

## [0.3.80] – 2026-08-20

### Bound equality-free HT iterative frontiers by rooted addresses

- Record every certification-only existential witness step as its parent,
  role, and signed filler literal.
- Reconstruct each full bounded frontier as pairwise-distinct rooted witness
  addresses. Malformed metadata and duplicate addresses fail closed instead
  of producing a verdict.
- Prove in Lean that injective concrete node addresses are bounded by the
  finite `WitnessAddress` universe.
- Prove that KM's node budgets `8 * 2^round` eventually exceed every such
  finite universe, so frontiers satisfying the concrete refinement condition
  cannot persist through every round.
- Test both the one-node frontier and a two-node cyclic prefix before pairwise
  blocking produces a finite checked model.

This establishes the outer cardinality argument used by the equality-free
decision loop. The remaining refinement work must connect the concrete Rust
frontier fields and blocking signatures to their typed Lean counterparts;
equality and cardinality certification remain separate.

## [0.3.79] – 2026-08-20

### Compose equality-free HT SAT and UNSAT evidence publication

- Add a certification-only equality-free decision API that runs the concrete
  first-obstruction search and returns a Boolean only with checker-ready
  evidence.
- Publish closed trees through the existing UNSAT refutation wire.
- Publish blocked open leaves by materializing their finite fold through the
  existing SAT wire.
- Keep `Frontier` strictly internal: mode 6 deepens, while an explicit
  diagnostic cap declines without a verdict.
- Reject equality and cardinality inputs at this equality-free boundary.
- Verify both sides through the native Lean checker: a cyclic existential
  ontology returns SAT with a checked finite model, and an empty-head ontology
  returns UNSAT with a checked refutation.

The remaining equality-free task is the concrete termination/refinement proof
for this loop. Equality and cardinality certification remain separate.

## [0.3.78] – 2026-08-20

### Add checked blocked terminals to equality-free HT evidence search

- Track existential creation predecessors in the certification-only
  equality-free refutation state.
- Detect ancestor blocking with the exact signed full pairwise signature used
  by Lean: node label, predecessor label, forward predecessor roles, and
  backward predecessor roles.
- Saturate all clause groundings before skipping blocked existential sources;
  continue any unblocked obligations instead of treating one blocked source as
  a terminal.
- Return blocked open leaves with their complete labels, edges, obligations,
  node count, and deduplicated `(blocked, blocker)` fold plan.
- Materialize each fold as ordinary finite edges and emit an untrusted SAT
  candidate for the existing Lean checker.
- Verify adversarial signature differences and a cyclic existential model. The
  native Lean checker accepts the three-node cycle with fold `(2, 1)`.

The standalone UNSAT API still declines on an open leaf. Total-route
composition must connect this checked open candidate to SAT publication and
prove that every non-frontier terminal is conclusive.

## [0.3.77] – 2026-08-20

### Derive the finite equality-free HT decision capstone

- Specialize exhaustive finite search to the exact clause-first
  `FirstObstructionStep` policy used by the Rust producer.
- Derive strict growth from absent head assertions and fresh witness creation,
  rather than accepting it as an external premise.
- Derive parent refutation from the semantic HT branch and witness
  constructors, rather than accepting child closure as an external premise.
- Conclude that the finite root is refuted or the exact ontology has a checked
  model.
- Add a regression demonstrating that the current standalone Rust refutation
  producer is still unblocked and therefore reaches a bounded frontier on a
  satisfiable existential cycle. This records the remaining runtime-totality
  gap instead of assuming iterative deepening alone closes it.

The next runtime milestone must enumerate the finite blocked search or extract
certified evidence from the blocked decision run.

## [0.3.76] – 2026-08-20

### Formalize the equality-free HT first-obstruction policy

- Define the exact transition policy used by the Rust refutation producer:
  choose an undischarged clause before an existential obligation, branch over
  every absent head, and materialize a witness only when no clause step exists.
- Prove that every such producer step is a semantic `ExhaustiveStep`.
- Prove that every child generated by either transition strictly grows the
  finite guarded-fact state, supplying the termination measure expected by the
  exhaustive-search theorem.

The remaining equality-free work is iterative-frontier termination and the
total SAT/UNSAT publication composition. Equality and cardinality remain
separate later milestones.

## [0.3.75] – 2026-08-20

### Separate bounded equality-free HT search outcomes

- Replace the equality-free UNSAT producer's ambiguous `Option` plus mutable
  node-cap side channel with explicit `Closed`, `Open`, and `Frontier` results.
- Propagate open branches and bounded frontiers distinctly through clause and
  witness recursion; only a frontier triggers iterative deepening.
- Test the three producer outcomes independently.
- Define the matching bounded-search outcome in Lean and prove that every
  conclusive result supplies either a refutation or a checked model, while the
  frontier remains explicitly inconclusive.

Equality and cardinality refutation producers retain their separate search
implementations and are not covered by this milestone.

## [0.3.74] – 2026-08-20

### Connect HT predecessor paths to the blocking-depth bound

- Check directly, before certified SAT publication, that every unblocked rooted
  predecessor path has pairwise-distinct full bidirectional blocking
  signatures.
- Keep this check certification-only and fail closed on a repeated signature.
- Prove in Lean that an injective signature map over a path of edge depth `d`
  implies `d` is strictly below the finite role-blocking signature cardinality.

This supplies the cardinality argument behind finite witness addresses without
computing the signature cardinality at runtime. Exact refinement of the UNSAT
transition enumerator remains the next equality-free HT task.

## [0.3.73] – 2026-08-20

### Compose exhaustive HT search with checked blocked models

- Define a checked-fold terminal proposition over the exact finite ontology.
- Prove that any accepted fold supplies a model of that unchanged ontology,
  independently of the producer's blocker choices.
- Prove a finite exhaustive-search capstone whose terminal leaves may carry
  checked blocked models: the root is refuted, or search reaches a leaf with an
  independently checked model.

This connects search totality to finite model folding without requiring blocked
raw states to be witness-complete. The concrete transition enumerator and the
strict blocking-depth premise still require runtime refinement.

## [0.3.72] – 2026-08-20

### Check rooted HT witness-address refinement

- Record each certified equality-free HT node as either a distinct root or the
  exact `(role, filler)` slot used for existential creation.
- Reconstruct rooted paths before certificate publication and fail closed on
  missing metadata, duplicate addresses, malformed roots, noncanonical child
  creation, or an occupied obligation slot lacking its exact edge and filler.
- Allocate this metadata only in `Ht::new_certified`; default and benchmark node
  layouts remain unchanged.
- Define the corresponding concrete-state lifting and address-refinement
  proposition in Lean, and prove that it establishes the finite
  `ObligationAddressInvariant` used by exhaustive equality-free HT search.

This does not yet complete blocked-search refinement. The next proof must relate
blocked obligations to finite model folding and show that every expandable
unwitnessed source lies strictly below the signature-depth bound.

## [0.3.71] – 2026-08-20

### Distinguish roots in finite HT node addresses

- Extend the finite blocked-address universe with an explicit finite root
  identity, so separate roots no longer share the same empty path.
- Prove that successor extension preserves the root identity and that an unused
  rooted extension is fresh.
- Generalize canonical obligation addressing and exhaustive equality-free HT
  transitions to the rooted universe.

The remaining Rust refinement must record each generated node's root and
canonical successor-slot path and check this correspondence before publishing
certified evidence.

## [0.3.70] – 2026-08-20

### Derive finite HT fresh supply from canonical obligation addresses

- Define equality-free witness slots as exact `(role, filler)` obligation keys
  and use them to form finite role-blocked node addresses.
- State the concrete address invariant: an obligation's canonical child is
  either unused or already connected to its source with the required label.
- Prove that any unwitnessed obligation under this invariant has a fresh finite
  child address.
- Discharge the abstract fresh-supply premise of exhaustive equality-free HT
  transitions directly from the address invariant.

The remaining runtime refinement must prove that Rust's equality-free
enumerator establishes and preserves this invariant. Cardinality successors
will require an additional finite ordinal in each witness slot.

## [0.3.69] – 2026-08-20

### Prove the finite blocked-address fresh-witness criterion

- Define the exact active-node set induced by labels, both role-edge endpoints,
  and existential obligations.
- Prove a node is fresh exactly when it is absent from that set, and prove a
  fresh target exists whenever active nodes do not fill the finite universe.
- Define extension of a role-blocked path by one finite successor slot and prove
  the extension remains within the signature depth bound.
- Prove that an unused obligation-specific extension is a valid fresh witness
  target.

The remaining tree invariant must show that an unwitnessed obligation's exact
extension is unused, or that an already-used extension discharges it.

## [0.3.68] – 2026-08-20

### Refine finite HT search to exact branch and witness transitions

- Define the exact finite guarded-fact representation of HT labels, role edges,
  and existential obligations, with both round-trip theorems.
- Prove that asserting an absent branchable head strictly grows this finite
  state and that materializing a fresh existential witness does the same.
- Define the two exact exhaustive transition shapes: one child per branchable
  head atom and one child for a fresh witness.
- Prove that refuting every enumerated child constructs the corresponding
  `Refutes` parent, then specialize finite-search completeness directly to the
  guarded-fact representation without an abstract decoder.
- Prove every equality-free undischarged or unwitnessed obstruction has one of
  these transition shapes when a fresh blocked address is available.

The remaining equality-free runtime premise is the concrete blocked-address
fresh supply and correspondence between Rust's enumeration and these exact
finite transitions.

## [0.3.67] – 2026-08-20

### Prove finite exhaustive HT search completeness

- Define strict finite-state growth by addition of branch facts and prove it is
  well-founded using the number of facts remaining in the finite vocabulary.
- Prove a generic exhaustive-search theorem: every such search closes its root
  or reaches an open terminal leaf.
- Specialize the theorem to guarded HT semantics. If the transition enumerator
  exposes every terminal obstruction and combines exhaustive closed children
  with `Refutes`, the root has a refutation or a reachable canonical model of
  the exact ontology.

The remaining runtime refinement must instantiate the transition assumptions
for Rust's concrete clash, head-branch, and fresh-witness updates.

## [0.3.66] – 2026-08-20

### Connect certified mode-6 expansion to the finite signature bound

- Prove that strictly increasing child identifiers plus refusal to expand an
  earlier-signature duplicate exclude every overlong all-expanded HT path.
- Add a fail-closed Rust check for those exact mode-6 predecessor and expansion
  invariants before SAT evidence is serialized.
- Disable cross-query SAT caches in `Ht::new_certified`; cache-only blockers do
  not provide the in-run witness required by the refinement theorem.
- Test both an accepted blocked leaf frontier and rejection of a retained child
  below a blocked node.

For equality-free ALC(H), where labels do not propagate from children back to
parents, the terminal check is also the expansion-time invariant. Inverse-role,
equality, and cardinality refinements still require their stronger dynamic or
indirect-blocking correspondence.

## [0.3.65] – 2026-08-20

### Derive a finite HT node universe from role-sensitive blocking

- Define blocked node addresses as finite successor-slot paths bounded by the
  complete pairwise blocking-signature vocabulary.
- Construct the corresponding `Fintype` instance and prove that its universal
  node set is finite.
- Connect the role-sensitive path bound to the finite-node premise used by the
  existing strict branch-progress theorem.

This closes the abstract finite-node step. A runtime refinement must still show
that certified Rust mode 6 represents each generated node by one of these
bounded addresses and preserves that representation across branch updates.

## [0.3.64] – 2026-08-20

### Remove artificial HT UNSAT evidence limits

- Replace eager assignment-vector construction and its one-million-assignment
  cutoff with lazy, exhaustive row-major enumeration using memory linear in the
  number of variables.
- Iteratively deepen the certified full-pairwise refutation node frontier only
  when search reaches it. A branch that is open without touching the frontier
  still declines immediately.
- Preserve `KM_HT_LEAN_UNSAT_NODES` as an explicit, fail-closed diagnostic
  limit for reproducible tests.
- Exercise a certified existential refutation requiring eleven nodes, beyond
  the historical default frontier of eight.

This removes implementation cutoffs from certified UNSAT evidence production.
It does not yet prove that every unsatisfiable input in the supported HT
fragment has a finite refutation accepted by the producer; connecting blocked
runtime search to that totality statement remains open.

## [0.3.63] – 2026-08-20

### Connect certified HT to finite role-sensitive blocking

- Define the full pairwise blocking signature in Lean: the blocked node's
  signed label, its predecessor's signed label, and the sets of roles connecting
  them in both directions.
- Prove that equal signatures preserve all four semantic components and yield a
  valid signed-label blocker.
- Prove that every predecessor path longer than the finite full-signature
  vocabulary contains an earlier exact pairwise blocker.
- Add certification-only Rust blocking mode 6, which uses the same full signed
  bidirectional signature and only direct blockers. It does not use mode 4's
  indirect inverse-role optimization, so every suppressed node has an explicit
  finite fold witness.
- Make `Ht::new_certified` select mode 6. SAT evidence materializes each direct
  blocker continuation as ordinary graph edges, after which the existing Lean
  checker still validates every witness and guarded grounding without trusting
  the blocker choice.
- Keep all default and benchmark blocking modes unchanged.

This connects certified SAT production to the finite role-sensitive blocking
vocabulary. A complete Rust refinement still needs checked exhaustive
obstruction enumeration for UNSAT branches; the independent refutation producer
retains its fail-closed node cap.

## [0.3.62] – 2026-08-20

### Prove the HT terminal-state model dichotomy

- Define the three exhaustive reasons a guarded HT branch is not a terminal
  open model: a complementary-label clash, an existential obligation without a
  witness, or a guarded clause grounding whose head is not discharged.
- Prove that absence of those obstructions yields clash freedom, witness
  completeness, and ontology saturation.
- Compose those properties with the canonical-model theorem, proving that an
  exhaustive obstruction-free terminal state models the exact ontology.
- Prove the terminal dichotomy: every state exposes one of the three next
  obstructions or its canonical interpretation is already a model.

Together with v0.3.60's finite blocking-signature depth and v0.3.61's finite
strict-progress traces, this completes the abstract finite-search termination
and terminal-model argument. The remaining HT totality work is a refinement
proof connecting Rust's role-sensitive blocking and obstruction enumeration to
this abstract search.

## [0.3.61] – 2026-08-20

### Prove finite progress for blocked HT evidence search

- Define the finite branch-fact vocabulary shared by ordinary,
  equality-aware, and cardinality-aware HT evidence search: signed labels,
  role edges, existential obligations, equalities, apartness facts, and
  minimum-expansion markers.
- Prove that no infinite sequence of strict monotone branch states exists once
  blocking bounds the node universe.
- Prove that the complete family of duplicate-free recursive progress traces is
  finite. This covers every branch-local search path, including first-class
  minimum and maximum cardinality steps.
- Enforce the formal strict-progress premise in release Rust builds at every
  recursive certificate transition. Certificate generation aborts if a clause
  branch, witness, equality, minimum, or maximum step recurses without adding a
  finite branch fact.

This establishes branch-local termination under a finite blocked node universe.
The remaining HT totality obligation is the runtime refinement showing that
blocking always supplies that finite universe and that every terminal search
state is either a checked model or a closed refutation.

## [0.3.60] – 2026-08-20

### Prove the finite HT blocking-signature bound

- Represent each finite HT node label as the complete set of signed concept
  literals used by equality and subset blocking.
- Prove by finite pigeonhole that every branch path longer than the number of
  possible signed labels contains an earlier exact-label blocker. Exact label
  repetition is a valid subset-blocking candidate, so this gives the finite
  depth bound for the certified finite signature.
- Prove that moving a blocked node's signed concept facts to that blocker
  preserves their truth in the canonical interpretation.
- Compose this bound with the existing fail-closed finite-fold boundary: role
  edges, existential witnesses, and guarded-clause saturation are still
  accepted only after the ordinary finite-model checker validates the fully
  materialized graph.

This release proves the abstract finite signature bound and concept-label
folding lemma. It does not yet claim that every Rust HT execution follows the
formal blocking transition or always emits finite evidence; that refinement is
the next termination milestone.

## [0.3.59] – 2026-08-20

### Certify complete HT taxonomies with cardinality definitions

- Define concept-status and subsumption decisions over the combined ontology
  and cardinality-definition semantics, then require one decision for every
  named concept and every ordered named pair.
- Add a bounds-checked taxonomy wire with one shared ontology and one shared
  cardinality-definition list. Query cells carry only their equality state,
  evidence, and optional ordinary or distinct-aware refutation tree, so no cell
  can substitute different bounds or axioms.
- Prove that every accepted finite matrix yields a complete cardinality-aware
  taxonomy. Missing rows, missing cells, duplicate named concepts, misplaced
  query evidence, malformed definitions, and rejected models all fail closed.
- Transfer the complete taxonomy through checked body-equality normalization
  and preprocessing equivalence while preserving the shared cardinality
  definitions.
- Extend the native taxonomy checker with direct version-5 and normalized
  version-6/7 documents.
- Make Rust produce the shared matrix from its per-query cardinality models and
  refutations, verify shared fields across all cells, and publish classification
  results only after both global and taxonomy Lean checkers accept them.
- Add native-decision malformed-matrix tests and an end-to-end normalized
  `tableau_cli` test using first-class cardinality side data.

This release certifies complete cardinality taxonomies when the finite HT
searches terminate and produce evidence. A general HT termination and total
evidence-production proof remains the next HT milestone.

## [0.3.58] – 2026-08-20

### Produce and check global HT cardinality certificates

- Add a Rust producer for finite distinct-aware cardinality refutations that
  composes ordinary clause branching and existential witnesses with minimum,
  maximum, equality, and equality/apart closure steps.
- Add positive equality-quotient cardinality evidence for satisfiable global
  searches. The same cardinality wrapper covers non-subsumption and
  satisfiable-concept evidence produced by the query APIs.
- Add a standalone cardinality checker and teach the general HT checker to
  recognize direct cardinality documents.
- Prove that checked cardinality evidence transfers through body-equality
  normalization and the certified preprocessing pipeline to the source
  ontology. Normalized cardinality documents use the existing version-3 and
  version-4 source-aware wrappers.
- Permit checker-gated publication of global HT consistency results with
  first-class cardinality side data. Complete taxonomy publication remains
  fail-closed until every cardinality query cell is composed into the checked
  taxonomy matrix.
- Test direct SAT evidence, a mixed branch/minimum/maximum/apart pigeonhole
  refutation, and an end-to-end normalized `tableau_cli` result against the
  native Lean checkers.

This release proves the soundness of accepted global cardinality certificates
and connects their production to the runtime. It does not yet prove HT search
termination or complete cardinality-taxonomy evidence production.

## [0.3.57] – 2026-08-20

### Compose cardinality refutations with ordinary HT rules

- Extend the distinct-aware cardinality semantics with equality refutations,
  explicit concept clashes, exhaustive clause branching, and existential
  witness materialization.
- Prove that assigning an existential witness to a fresh node preserves every
  previously recorded apart pair.
- Extend the finite checker with exact apart-preserving branch transitions and
  distinct-fresh witness checks.
- Extend the bounds-checked wire tree with equality, clash, branch, and witness
  nodes, allowing these rules to compose with minimum and maximum cardinality
  rules in one checked refutation.
- Add native tests for ordinary branch and witness recursion through the public
  distinct-aware wire checker.

This release certifies supplied mixed ordinary/cardinality HT refutations. It
does not yet prove HT termination or guarantee that the Rust reasoner produces
such evidence for every closed search.

## [0.3.56] – 2026-08-20

### Certify first-class HT cardinality evidence and pigeonhole closure

- Define exact arbitrary-domain semantics for HT minimum and maximum
  cardinality definitions without a unique-name assumption.
- Check positive SAT, non-subsumption, and satisfiable-concept evidence against
  the canonical equality quotient, including exhaustive finite assignments for
  each active cardinality definition.
- Prove the maximum rule sound: `n+1` qualifying successors under `≤n R.C`
  force an exhaustive equality-merge branch.
- Prove simultaneous `≥n R.C` witness materialization sound and preserve the
  injectivity of its fresh witness family.
- Add an explicit apart relation so minimum-witness distinctness survives later
  equality reasoning. Equality closure meeting an apart pair is a checked
  contradiction, not a unique-name assumption.
- Prove the general pigeonhole closure for active `≥n+1 R.C` and `≤n R.C`.
- Add finite, depth-indexed certificate checkers and bounds-checked JSON wire
  decoders for minimum, maximum, equality/apart, and cardinality refutation
  trees.
  The apart transition is compared extensionally over every finite node pair.
- Add native tests accepting a complete `≥2 R.C` plus `≤1 R.C` public wire
  certificate and rejecting missing apart information and malformed child
  matrices.

This release certifies cardinality evidence that is supplied to the Lean
checker. It does not yet prove HT termination or that the Rust reasoner always
emits a certificate; those remain requirements of the complete certification
objective.

## [0.3.55] – 2026-08-20

### Check role-chain and transitivity source axioms directly

- Restore every typed `R1∘R2⊑R` side-data entry as the exact clause
  `R1(x,y) ∧ R2(y,z) → R(x,z)` on the Lean-certified HT path.
- Restore every typed transitive-role entry as the exact clause
  `R(x,y) ∧ R(y,z) → R(x,z)`.
- Run these source clauses through ordinary HT branching instead of trusting
  the optimized role-automaton marker compilation. The existing Lean finite
  model and refutation checkers therefore verify the original role semantics
  directly for SAT, UNSAT, and complete-taxonomy evidence.
- Keep the optimized side-data implementation unchanged on the ordinary
  performance route. Only certification requests select the exact source-clause
  path.
- Add Rust reconstruction tests, a chain-dependent refutation accepted by the
  native Lean checker, and an end-to-end complete-taxonomy test containing both
  a role chain and a transitivity axiom.

This release removes the role-chain/transitivity side-data exclusion from the
HT certificate gate. It certifies evidence that terminates and is emitted; a
general termination and evidence-production proof remains part of the complete
HT certification objective.

## [0.3.54] – 2026-08-20

### Check HT trigger absorption and contrapositives from the source ontology

- Add proof-producing wire decoders for the exact trigger-absorption pass. The
  checker requires one decision per source clause, checks retained clauses by
  equality, bounds-checks every identifier, and reconstructs absorbed clauses
  from a checked positive/negative head partition.
- Add proof-producing contrapositive decoding. Every appended clause carries a
  bounds-checked source-clause index and exact selected, left, and right literal
  split. Lean reconstructs the target and proves that its source belongs to the
  absorbed ontology.
- Compose trigger absorption, contrapositive extension, and equality-premise
  normalization in one executable source-equivalence checker. Truncated output,
  fabricated source indices, wrong partitions, wrong splits, and mismatched
  intermediate ontologies are rejected.
- Add individual and complete-taxonomy wire version 4. Both transfer accepted
  SAT, UNSAT, concept, subsumption, and complete-matrix evidence back to the
  original source ontology through the checked preprocessing equivalence.
- Make Rust retain and serialize exact preprocessing evidence. Rust-produced
  individual and complete-taxonomy documents pass their native Lean checkers;
  tampered contrapositive evidence is rejected.
- Keep certificate publication fail-closed when later clause-changing
  optimizations invalidate the recorded correspondence. `KM_HT_HARVEST` and
  the previously excluded inverse, nominal, native-ABox, chain, and unsupported
  cardinality paths remain outside this certificate route.

This release closes the source-correspondence gap for HT trigger absorption and
clash contrapositives. It does not prove that every HT search terminates or
produces finite evidence, and it does not certify the complete SROIQ runtime.

## [0.3.53] – 2026-08-19

### Cover interleaved HT trigger-absorption heads

- Generalize the trigger-absorption certificate so the original clause head
  may interleave positive and negative concept literals in any order, exactly
  as Rust preserves them.
- Require a checked permutation between the original head and its negative and
  positive partitions. The semantic proof uses this permutation in both
  directions, so it neither assumes nor trusts a physical reorder.
- Add a regression proof for the concrete interleaving `P₀ ∨ ¬N ∨ P₂`, whose
  absorbed form is `N → P₀ ∨ P₂`.

This corrects an overly narrow proof-object shape in v0.3.52. The theorem was
sound for every certificate it admitted, but it did not cover every mixed-head
ordering accepted by Rust. Runtime preprocessing certification remains
fail-closed pending its executable correspondence checker.

## [0.3.52] – 2026-08-19

### Prove semantic preservation of HT clause preprocessing

- Prove that trigger absorption preserves clause satisfaction in both
  directions, including mixed positive and negative heads and all-negative
  heads that become clash clauses.
- Lift trigger absorption to an exact order-preserving ontology
  transformation whose clauses are either retained or carry an explicit
  absorption proof.
- Prove that every same-variable concept-clash contrapositive generated by HT
  follows from its source clause, and that appending any fully witnessed list
  of such clauses preserves the ontology's models.
- Compose trigger absorption, contrapositive extension, and the existing
  body-equality normalization into one model-equivalence theorem matching the
  preprocessing order in `Ht::new`.
- Audit the new declarations: they contain no `sorry` or `admit`, and Lean
  reports only its standard propositional, classical-choice, and quotient
  axioms.

This release establishes the semantic proof layer for HT preprocessing. The
runtime certificate remains fail-closed for these optional transformations
until an executable decoder checks Rust's exact preprocessing evidence. It
does not claim complete HT termination, evidence production, or full KM
certification.

## [0.3.51] – 2026-08-19

### Certify complete HT taxonomies against equality-bearing source clauses

- Define semantic transfer of concept-status and subsumption decisions across
  model-equivalent ontologies, then lift it to a complete named taxonomy.
- Add source-aware HT taxonomy wire version 3. It wraps either a plain
  version-1 matrix or a mixed equality-aware version-2 matrix with one checked
  equality-premise normalization witness per clause.
- Prove that every accepted concept and ordered-pair answer is exact for the
  source ontology. Missing cells, disconnected equality paths, and malformed
  nested payloads are rejected.
- Emit the source-aware matrix from Rust and make checker-gated publication
  read answers from the accepted nested payload. The public classification is
  still withheld whenever the native Lean checker rejects the document.
- Validate Rust-produced equality-body taxonomies with the native checker and
  retain end-to-end publication tests for plain and mixed matrices.

This closes the source-normalization gap for current individual and complete
HT certificates. It does not prove that HT terminates or produces evidence for
every SROIQ input. Blocking, inverse roles, nominals, native ABoxes, cardinality
side data, role-chain compilation, and preprocessing transformations still
need complete executable correspondence proofs.

## [0.3.50] – 2026-08-19

### Check HT equality-premise normalization from the source ontology

- Lift clause-level equality-premise normalization to ontology model
  equivalence, and prove transfer theorems for satisfiability, concept
  unsatisfiability, and subsumption.
- Add a proof-producing Lean decoder for representative maps and equality
  paths. It rejects paths that are disconnected, out of bounds, or unsupported
  by a positive equality premise, and checks the exact renamed target clause.
- Add HT certificate wire version 3. It nests an existing plain or
  equality-aware certificate for the normalized ontology together with the
  source clauses and their normalization evidence. The native checker now
  returns semantic evidence about the source ontology.
- Make Rust retain normalization paths while it eliminates equality premises,
  emit version 3 for individual HT results, and discard evidence if a later
  optimization replaces the clause set. A Rust-produced source certificate is
  accepted end to end by the native Lean checker.
- Require a nonempty domain for plain SAT wire evidence, closing an implicit
  empty-model edge case in version 1.

This release connects individual HT certificates across equality-premise
normalization. Taxonomy batches still certify their normalized ontology rather
than carrying one shared source-normalization wrapper. Complete HT
blocking/termination, inverse roles, nominals, native ABoxes, and the remaining
OWL features are unfinished. This release does not certify the complete HT
implementation or the full KM executable.

## [0.3.49] – 2026-08-19

### Prove and implement HT equality-premise normalization

- Define atom renaming and explicit paths through positive equality premises in
  Lean. A normalization certificate records the representative map, proves each
  variable reaches its representative, and proves every removed equality is
  collapsed.
- Prove that equality-premise elimination preserves clause satisfaction in
  both directions, then lift the result to model equivalence for complete
  ontologies. The theorems contain no `sorry` or `admit`; their axiom audit
  reports only Lean's standard `propext` and `Quot.sound` principles.
- Apply the same transformation before Rust constructs HT trigger indexes.
  Equality-only bodies now fire, transitive equality classes use one
  representative, and an equality-premise constraint with an empty head becomes
  the required global clash.
- Replace the fail-closed `x=x → A(x)` regression with a positive end-to-end
  test: Rust materializes `A`, and the native Lean taxonomy checker accepts the
  resulting complete matrix.

The semantic refinement theorem now covers the runtime transformation, but the
wire document still contains only the normalized ontology. Supplying the source
ontology and checkable equality paths in the wire format remains the next
connection milestone. Complete blocking/termination, inverse roles, nominals,
native ABoxes, and the remaining OWL features are still unfinished; this release
does not certify the entire HT implementation.

## [0.3.48] – 2026-08-19

### Certify complete mixed-equality HT taxonomies

- Define a heterogeneous covered-taxonomy certificate whose cells retain
  semantic decisions after either an equality-free finite checker or an
  equality-quotient checker accepts them. Prove that complete concept and
  ordered-pair coverage yields an exact named taxonomy.
- Add taxonomy wire version 2. Every row-major cell is explicitly tagged as a
  version-1 payload or equality-aware payload, while the ontology and named
  class vector remain shared and bounds checked. Missing, duplicated, or
  position-swapped cells are rejected.
- Extend the native taxonomy checker to dispatch unchanged version-1 documents
  and mixed version-2 documents.
- Emit version 2 from Rust only when equality-aware evidence occurs; pure
  equality-free output remains version 1. Checker-gated publication reads the
  accepted wrapped evidence and remains fail-closed on rejected matrices.
- Permit checker-gated taxonomy certification for equality-bearing clause sets
  without cardinality side data. Number-restriction side data, inverse roles,
  nominals, and native ABoxes remain outside this endpoint.

The native checker exposed an existing runtime completeness gap for an
unguarded equality body such as `x=x → A(x)`: the producer omits `A`, and the
checker rejects the resulting model. A regression test preserves this
fail-closed behavior. Equality-body triggering, complete blocking/termination,
and the remaining OWL features still require implementation and proof. This
release does not certify the entire HT implementation.

## [0.3.47] – 2026-08-19

### Certify equality-aware HT query decisions

- Prove that a checked equality-quotient model containing `A` and `¬B`
  refutes `A ⊑ B`, and that one containing `A` refutes concept
  unsatisfiability.
- Prove that equality-aware refutations rooted at exactly `{A, ¬B}` or `{A}`
  establish subsumption or concept unsatisfiability, respectively.
- Extend version-2 HT evidence with all four query outcomes: subsumption,
  non-subsumption, unsatisfiable concept, and satisfiable concept. Query IDs
  are bounds checked, query labels are checked, and every accepted outcome is
  connected to its semantic theorem.
- Emit version-2 query countermodels and refutations from Rust whenever the
  normalized clause set contains equality heads. Rust-produced quotient
  countermodels pass the native Lean checker.

This release certifies individual equality-aware HT query answers whenever the
bounded producer returns accepted evidence. Complete equality-aware taxonomy
batch publication, inverse roles, nominals, native ABoxes, and a proof that
every HT search terminates with evidence remain unfinished. It does not certify
the entire HT implementation.

## [0.3.46] – 2026-08-19

### Certify equality-aware HT finite models

- Define quotient-closed HT labels, edges, obligations, and atom matching. Prove
  that a guarded, clash-free, witness-complete, closed-saturated state constructs
  a model on the complete node-equivalence quotient.
- Add an executable equality-aware finite SAT checker. It validates equality
  closure, clashes across merged nodes, existential witnesses, and every finite
  grounding modulo equality. Acceptance proves satisfiability of the exact
  normalized ontology.
- Extend version-2 HT wire evidence with global SAT documents and require a
  positive node bound, so accepted OWL models have a nonempty domain.
- Emit version-2 SAT quotient evidence from Rust, including merge generators,
  representatives, and checked paths. A Rust-produced document passes the
  native Lean checker.

This release certifies bounded global SAT and UNSAT evidence for the guarded HT
fragment with equality. Equality-aware query countermodels and complete
taxonomy, inverse roles, nominals, native ABoxes, and a proof that every search
terminates with evidence remain unfinished. It does not certify the entire HT
implementation.

## [0.3.45] – 2026-08-19

### Connect equality-aware HT refutations to the runtime

- Add a bounds-checked version-2 JSON format for equality-aware HT
  refutations. Every branch child carries the exact successor graph, equality
  history, representative vector, and checked paths to representatives.
- Prove that an accepted version-2 empty-root document excludes every
  nonempty-domain model of its exact normalized ontology.
- Extend `ht-cert-check` to dispatch version 1 equality-free documents and
  version 2 equality-aware documents without weakening either checker. Add a
  dedicated `ht-eq-cert-check` executable for diagnostics.
- Extend the bounded Rust refutation producer with reversible equality merges,
  equality-aware body matching and clashes, deterministic state histories, and
  representative-path witnesses. Rust-produced equality certificates pass the
  native Lean checker.
- Permit equality/number inputs through the certified global-consistency gate.
  Publication still requires checker acceptance. Equality-aware SAT evidence,
  taxonomy evidence, inverse roles, nominals, and native ABoxes remain
  fail-closed.

This release connects certified equality-aware UNSAT evidence to the concrete
runtime. It does not certify all HT termination or completeness, and it does
not make the complete Rust executable formally verified.

## [0.3.44] – 2026-08-19

### Certify finite equality-aware HT refutations

- Refine semantic equality merges to a finite certificate containing the
  asserted equality history, a representative for every node, and an explicit
  equality-edge path from each node to its representative.
- Prove that the validated representative relation is exactly, in both
  directions, the reflexive, symmetric, transitive closure generated by the
  asserted equality history.
- Add an executable equality-aware refutation-tree checker. It accepts equality
  heads, validates every successor certificate against the exact asserted atom,
  detects clashes across complete equality classes, and enforces existential
  witness freshness modulo equality.
- Prove that every accepted finite tree is a semantic equality-aware HT
  refutation and therefore excludes every realizing model of the encoded
  ontology.
- Add native executable tests for transitive equality closure, equality-head
  branching, invalid representative paths, and stale equality successors.

This release certifies the finite Lean equality-refutation format. The shipped
Rust HT certificate producer and wire decoder remain equality-free and
fail-closed; connecting them to this format is a separate implementation
refinement milestone. Complete HT termination and completeness for all OWL 2
features also remain open.

## [0.3.43] – 2026-08-19

### Certify equality-aware HT refutations

- Define equality-aware HT states whose node relation is an explicit
  equivalence and whose realizations map equivalent nodes to the same domain
  element.
- Define equality assertion as the equivalence closure generated by the old
  relation and the new equality pair. Prove that this merge preserves every
  realizing interpretation that satisfies the equality head.
- Generalize model-preserving head assertion and exhaustive hyper-branching to
  all HT atoms, removing the semantic calculus restriction that excluded
  equality heads.
- Compose equality with fresh existential-witness materialization. Fresh nodes
  must be isolated equivalence classes, and the proof preserves both existing
  graph facts and the node quotient.
- Prove soundness of complete equality-aware refutation trees, including
  clashes between complementary labels carried by equivalent but syntactically
  distinct nodes.

This release closes the abstract semantic proof gap for HT equality merges.
Finite union-find certificate refinement, equality wire decoding, and Rust
publication remain fail-closed and are the next certification milestone.

## [0.3.42] – 2026-08-19

### Certify complete HT taxonomy matrices

- Define complete semantic HT taxonomy certificates and prove exact
  unsatisfiable-class and subsumption materialization from either-polarity
  decisions.
- Add finite and indexed certificate refinements that connect accepted finite
  refutations and countermodels to those semantic decisions.
- Add a versioned batch wire decoder with bounded identifiers, duplicate-free
  named classes, exact concept coverage, and an exact square row-major matrix
  covering every ordered named-class pair.
- Add the native `ht-taxonomy-cert-check` executable. It accepts a complete
  Rust-produced two-class matrix and rejects missing, duplicated, or
  position-mismatched cells.
- Add fail-closed Rust publication for the equality-free ALC(H) certificate
  fragment. Publication requires both global-consistency and taxonomy checker
  acceptance, and the returned taxonomy is derived directly from the accepted
  matrix.
- Add worker-boundary tests against the native Lean checkers and verify that a
  rejecting taxonomy checker suppresses all classification output.

This release certifies complete named taxonomy output whenever bounded HT
evidence exists for every matrix cell in the supported certificate fragment.
It does not prove HT termination or cover equality/cardinality, inverse roles,
nominals, native ABoxes, QO, CB, complete ELC residuals, or automatic routing.

## [0.3.41] – 2026-08-19

### Certify HT taxonomy countermodels

- Prove that a checked finite model carrying `A` and `¬B` at one node refutes
  `A ⊑ B`.
- Prove that a checked finite model carrying `A` refutes the claim that `A` is
  unsatisfiable.
- Extend the version-1 HT wire format with bounds-checked `non_subsumption` and
  `satisfiable_concept` evidence. The checker requires the declared query
  literals to occur in the accepted finite model.
- Extend the Rust producer to serialize retained terminal models for both query
  kinds and reject calls that do not match the model root.
- Validate all four individual taxonomy outcomes through the native Lean
  checker: subsumption, non-subsumption, unsatisfiable concept, and satisfiable
  concept.

This release certifies either polarity of an individual HT taxonomy query when
bounded refutation or finite-model evidence is available. A complete batch
taxonomy certificate remains the next milestone.

## [0.3.40] – 2026-08-19

### Certify individual HT taxonomy refutations

- Define semantic named-concept subsumption and concept-unsatisfiability
  judgments for the normalized hypertableau ontology.
- Prove that a checked refutation rooted at exactly `A` and `¬B` entails
  `A ⊑ B`, and that one rooted at exactly `A` proves `A` unsatisfiable.
- Extend the version-1 wire format with bounds-checked `subsumption` and
  `unsatisfiable_concept` evidence. The executable checker verifies the exact
  root labels and rejects query/root mismatches.
- Generalize the Rust bounded refutation producer to start from query labels
  and emit both evidence kinds. Rust-generated documents pass the native Lean
  checker; open branches still decline without evidence.

This release certifies individual HT taxonomy answers that have bounded closed
refutations. Batch taxonomy publication, complete HT termination, and
equality-dependent refutations remain outstanding.

## [0.3.39] – 2026-08-19

### Certify fresh existential witnesses in HT refutations

- Add a semantic `State.materializeWitness` operation and prove that an
  existential obligation can bind a completely fresh finite node to its model
  witness without invalidating any existing label, edge, or obligation.
- Extend abstract HT refutations with a witness step and preserve the global
  `Refutes.sound` theorem.
- Extend the finite checker with executable freshness checks, witness
  materialization, and a proved refinement to the semantic operation.
- Extend the version-1 JSON tree with bounds-checked witness nodes, roles, and
  fillers. Lean accepts a two-node role/filler contradiction and rejects reuse
  of a non-fresh node.
- Generalize the Rust producer to bounded multi-node search. It enumerates
  grounded clauses over active nodes, materializes unmet obligations, caps
  assignments at one million and nodes at eight by default, and declines on
  every open or capped branch.
- Validate the exact Rust-to-JSON-to-Lean-to-`tableau_cli` path and confirm that
  checker rejection suppresses publication.

This release certifies global HT inconsistency for finite refutations that fit
the producer bounds, including contradictions reached only after creating an
existential witness. It does not claim complete HT termination or equality
merging.

## [0.3.38] – 2026-08-19

### Certify one-node HT role and existential refutations

- Generalize the finite HT refutation producer from concept labels to the
  checker's complete monotone branch vocabulary: concept labels, role edges,
  and existential obligations.
- Evaluate every clause under the explicit one-node assignment, including
  equality tests in bodies, while continuing to reject equality heads that
  would require an uncertified node merge.
- Preserve fail-closed behavior: each recursive child adds one absent finite
  fact, every disjunct receives a child, and any open branch declines without
  publication.
- Pass the native Lean checker on one mixed tree whose first disjunct closes
  through a forced role edge and whose second closes through a forced
  existential obligation.
- Validate the production `tableau_cli` boundary and confirm checker rejection
  suppresses publication.

This release certifies global HT inconsistency whenever the exact normalized
ontology has a closed one-node refutation over concept, role, and existential
facts. Multi-node role refutations and equality-dependent branches remain
outstanding.

## [0.3.37] – 2026-08-19

### Certify concept-only HT inconsistency publication

- Add a Rust producer for exhaustive finite refutation trees over exact
  concept-only normalized HT clauses. Each recursive branch asserts one absent
  head literal; a clash or an empty-head clause closes it.
- Refuse evidence when any valuation remains open or any role, existential, or
  equality atom occurs. This keeps role-bearing and quotient-dependent UNSAT
  outside the certified runtime slice.
- Serialize the producer's tree in the version-1 HT wire format and require the
  native Lean checker before the worker can publish global inconsistency.
- Test exhaustive binary closure, open-branch refusal, non-concept refusal, the
  exact Rust-to-JSON-to-Lean path, and checker-gated `tableau_cli` publication.
- Validate the production example: `[] -> A | B`, `A -> []`, and `B -> []`
  emits two exhaustive children, is accepted by `ht-cert-check`, and publishes
  `consistent:false`.

This release certifies global HT inconsistency publication for the concept-only
fragment. Role-bearing UNSAT, equality/cardinality, inverse roles, nominals,
native ABoxes, termination correspondence, and taxonomy publication remain
outstanding.

## [0.3.36] – 2026-08-17

### Certify finite HT model folding

- Add a Lean finite-fold certificate that treats blocker pairs as untrusted
  model-construction hints, materializes copied blocker edges, and reruns the
  exhaustive finite SAT checker.
- Prove that accepted folds preserve the exact ontology and construct a model
  without assuming that any supplied blocker pair is valid.
- Add a native cyclic-existential reduction test whose incomplete blocked graph
  is rejected and whose materialized fold is accepted.
- Make the Rust HT producer reconstruct the exact default anywhere-subset
  blocker relation and emit the copied continuation edges as ordinary wire
  evidence. Other blocking modes remain fenced.
- Validate the cyclic Rust-to-JSON-to-Lean path: the terminal blocked node gains
  its folded self-loop and `ht-cert-check` accepts the resulting finite model.

This release certifies SAT model folding by validation, not by trusting the
Rust blocking algorithm. HT UNSAT and taxonomy publication remain outstanding.

## [0.3.35] – 2026-08-17

### Connect Rust HT SAT evidence to the Lean checker

- Serialize the exact normalized HT clauses and completed equality-free graph
  into the version-1 Lean certificate wire format.
- Gate checker-backed HT publication on successful execution of the native
  `ht-cert-check` executable. Producer failure, checker rejection, and
  unsupported evidence all defer without publishing a legacy fallback answer.
- Restrict the integrated endpoint to global SAT results for equality-free
  ALC(H). Taxonomy, UNSAT, QO, inverse, cardinality, nominal, and native-ABox
  results remain fenced.
- Add Rust tests for terminal-model serialization and equality rejection, plus
  an end-to-end Rust-to-JSON-to-Lean acceptance test during release validation.
- Confirm that Lean rejects a blocked existential completion graph that lacks
  its folded model edges. This keeps cyclic blocking outside the certified
  runtime slice until the blocking/model-folding theorem is complete.

This release certifies publication only when the emitted finite SAT model is
accepted by Lean. It does not certify HT taxonomy or UNSAT publication.

## [0.3.34] – 2026-08-17

### Certify the hypertableau JSON trust boundary

- Add a versioned JSON schema for finite HT SAT and UNSAT evidence, with
  separate node, concept, role, and variable signature bounds.
- Check every untrusted numeric id, assignment arity, ontology clause index,
  and refutation child count before constructing finite semantic objects.
- Dispatch decoded evidence only to the proved SAT or UNSAT checker and prove
  soundness of both decoded verdict forms.
- Add the standalone `ht-cert-check` executable, which fails closed on parsing,
  decoding, or semantic-checking errors.
- Add native end-to-end tests for accepted SAT and UNSAT documents, out-of-range
  concepts, missing branches, equality branches, and unsupported versions.
- Audit the decoded-verdict theorems with `#print axioms`; neither uses
  `sorryAx`.

Rust HT evidence emission is not enabled in this release. Blocking,
termination, equality/cardinality, nominals, taxonomy publication, CB, and
concrete routing remain outstanding.

## [0.3.33] – 2026-08-17

### Certify executable hypertableau UNSAT refutations

- Add mutually inductive finite refutation trees and child spines with an
  executable checker for clashes, ontology-clause membership, grounded bodies,
  legal branch heads, exact child order, and every recursive child.
- Prove checker acceptance constructs the abstract exhaustive `Refutes`
  judgment and therefore excludes every realization of the checked root.
- Prove that an accepted empty-root certificate over a nonempty node set
  excludes every nonempty-domain model of the exact encoded ontology.
- Reject equality branches until node merging has a certified quotient
  construction.
- Add native tests for an empty-head contradiction, exhaustive binary
  disjunction closure, a missing branch, and an unsupported equality branch.
- Audit all public UNSAT acceptance theorems with `#print axioms`; none uses
  `sorryAx`.

This release certifies the finite Lean UNSAT checker. Rust emission and a
serialized wire decoder remain outstanding, as do blocking, termination,
equality/cardinality, nominals, taxonomy publication, CB, and concrete routing.

## [0.3.32] – 2026-08-17

### Certify finite hypertableau SAT certificates

- Add an executable finite open-branch checker that validates guarded clause
  bodies, clash freedom, existential witnesses, and every finite clause
  grounding.
- Use a computable exhaustive assignment enumeration and prove that it contains
  every variable assignment, avoiding a classical decision procedure in the
  checker implementation.
- Prove that checker acceptance establishes the abstract saturation premises,
  constructs the canonical model of the exact encoded ontology, and therefore
  witnesses satisfiability.
- Add native reduction tests accepting a valid branch and rejecting a clash, a
  missing existential witness, and an undischarged grounding.
- Audit the public acceptance theorems with `#print axioms`; none uses
  `sorryAx`.

This is a finite exhaustive Lean checker. Rust does not yet emit this SAT
certificate, and the UNSAT refutation tree has no wire decoder yet. Blocking,
termination, equality/cardinality, nominals, taxonomy publication, CB, and
concrete routing remain outstanding.

## [0.3.31] – 2026-08-17

### Certify exhaustive hypertableau branch refutations

- Define monotone concept, role, and existential head assertion on HT states and
  prove that asserting a semantically true head preserves every realization.
- Define an exhaustive HT refutation tree whose internal nodes record a matched
  ontology clause and one refuting child for every legal head disjunct.
- Prove `Refutes.sound`: a complete refutation tree excludes every interpretation
  that both models the ontology and realizes the root branch.
- Keep equality heads outside this monotone tree; their node-merge semantics need
  a quotient-preservation theorem before Rust may certify cardinality branches.
- Audit the new public theorems with `#print axioms`; neither uses `sorryAx`.

Rust emission and executable checking of the tree, branch-state correspondence,
blocking and termination, SAT/taxonomy publication, equality/cardinality,
nominals, HT routing, CB, and concrete routing remain outstanding.

## [0.3.30] – 2026-08-17

### Certify the guarded hypertableau semantic core

- Add a Lean semantics for signed concept atoms, role atoms, existential
  obligations, equality, guarded clauses, completion states, and realization.
- Prove soundness of complementary-label clash detection, forced unit heads,
  disjunctive hyper-rule branching, and semantic existential witnesses.
- Construct the canonical interpretation of a clash-free branch and prove that
  every witness-complete, clause-saturated guarded branch models its ontology.
- Derive the refutational-completeness endpoint: an ontology with no model on
  the branch domain cannot have a clash-free, witness-complete, saturated open
  branch.
- Audit the public theorems with `#print axioms`; none uses `sorryAx`.

This milestone certifies the abstract guarded ALC(H) hypertableau core. Rust
state-transition correspondence, exhaustive search, blocking and termination,
taxonomy publication, cardinality and nominal extensions, HT routing, CB, and
the concrete router remain outstanding.

## [0.3.29] – 2026-08-17

### Close the remaining checker-backed ELC runtime trust boundaries

- Disable inverse-bridge preprocessing whenever a Lean certificate is
  requested, so the checked source theory is the exact input clause stream and
  never the output of an unproved rewrite.
- Keep inverse-bridge preprocessing for non-Lean certificate modes, preserving
  the existing optimized route without extending the certification claim.
- Verify through the real checker path that search-based repair output is never
  published by checker-backed execution: a rejected base-model certificate
  falls through before repair can contribute an answer.

The checker-backed ELC clause route now publishes only results covered by the
wire-v5 soundness and completeness theorems. OWL frontend translation,
inverse-bridge preprocessing outside that route, repair publication outside
that route, HT, CB, and concrete routing remain separate certification tasks.

## [0.3.28] – 2026-08-17

### Enable checker-backed residual ELC publication

- Partition the retained source clause stream exactly into direct EL clauses,
  canonical Skolem-witness pairs, and compiled residual clauses.
- Preserve duplicate source clauses while matching residuals as a multiset and
  fail closed if a rewritten Skolem function lacks either source half.
- Emit the canonical witness records and residual compilation evidence consumed
  by the wire-v5 Lean theorem, then publish only the taxonomy returned by an
  accepting Lean checker.
- Add an end-to-end regression that checks the native partition, complete
  certificate, production publication path, and adversarial pin/origin changes.

This certifies residual publication for the retained clause stream after the
current inverse-bridge preprocessing step. Certification of that preprocessing
step, repair mode, HT, CB, and concrete routing remains outstanding.

## [0.3.27] – 2026-08-17

### Prove end-to-end residual source semantics and public exactness

- Connect direct normalization, canonical witness rewrites, compiled residual
  evidence, finite residual truth, and the checked source partition into one
  model of the exact original raw clause stream.
- Prove exact source-level subsumption and inconsistency for accepted
  partitioned wire-v5 certificates, including a separate inconsistent-core
  argument that does not fabricate live canonical witnesses.
- Prove source-level soundness of public subsumptions and satisfiable-case
  completeness of numeric and named public taxonomy output.
- Add an executable signature-closure check and prove it equivalent to the
  finite canonical model's `SignatureClosed` premise. Malformed certificates
  can no longer rely on an incomplete active-concept domain.

Production still declines Lean-certified residual publication until Rust emits
the exact direct/witness/residual source partition consumed by these theorems.
Repair mode, HT, CB, and concrete routing remain uncertified.

## [0.3.26] – 2026-08-17

### Prove one global Skolem interpretation for residual publication

- Prove that every accepted canonical-witness record and every function-origin
  residual variable agrees with one shared function-to-witness interpretation.
- Reject conflicting or dead bindings semantically, then lift each accepted
  residual compilation into a whole-theory entry carrying its checked
  compilation evidence, compiled truth, and global pin compatibility.
- Prove that packaging the independently numbered residual entries preserves
  the exact raw residual-clause stream.

Production still declines Lean-certified residual publication until the
materialized direct, witness, and residual partitions are connected to the
public taxonomy theorem. Repair mode, HT, CB, and concrete routing remain
uncertified.

## [0.3.25] – 2026-08-17

### Check residual truth on the finite materialization

- Make wire-v5 acceptance exhaustively evaluate every compiled residual clause
  over the active-and-alive trace domain. Already inconsistent ELC cores remain
  valid without constructing a countermodel.
- Reject residual and canonical-witness function bindings that name dead nodes,
  disagree for one function, or omit the corresponding rewritten NF3/NF1
  clauses.
- Prove that accepted compiled clauses hold in the finite materialized canonical
  interpretation, and prove that their independently checked compilation
  evidence remains valid after restricting pins to that domain.
- Lift canonical NF3 witness refinement and complete three-way source partition
  composition from the abstract canonical model to the exact executable
  materialization.
- Add a native end-to-end mutation test: a structurally exact residual tautology
  passes, while a structurally exact clause false in the finite canonical model
  fails closed.

Production still declines Lean-certified residual publication until the checked
global function-binding table is connected to the whole-source composition
theorem. Repair mode, HT, CB, and concrete routing remain uncertified.

## [0.3.24] – 2026-08-17

### Prove exact residual reasoning on the executable finite domain

- Define the finite canonical domain as the active concepts that the checked
  trace does not label with bottom, with concept and role interpretation taken
  directly from the trace materialization.
- Prove that fixpoint closure makes this finite interpretation a model of every
  checked NF1–NF7 and reflexive axiom. The NF3 case proves that each required
  filler remains active and alive.
- Prove exact taxonomy and inconsistency theorems when the residual theory holds
  on this same finite interpretation. These are the semantic theorems needed by
  an exhaustive native residual-clause checker, rather than corollaries that
  assume truth in a separate abstract canonical model.

The executable wire does not yet invoke the finite residual-clause checker, so
production still declines Lean-certified residual publication. Repair mode,
HT, CB, and concrete routing remain uncertified.

## [0.3.23] – 2026-08-17

### Check exact source partitions and symbol origins

- Add wire version 5 with the complete residual-capable source ontology,
  direct-clause partition, canonical-witness records, and residual compilation
  entries. Lean rejects omitted source clauses, out-of-range fields, origin
  mismatches, and wire downgrades.
- Prove direct-only raw normalization preserves the exact shared term
  interpretation, avoiding an existential-choice mismatch with globally pinned
  residual functions.
- Prove arbitrary normalized models project to source models, including models
  whose conjunction auxiliaries were materialized independently.
- Prove exact concept-renaming invariance for models, named subsumption, and
  inconsistency under any origin map with a left inverse. The decoder constructs
  injectivity evidence from its checked, full-length, duplicate-free origin
  table, and the wire checks the normalized ontology against that renaming.
- Add an end-to-end native Rust-to-Lean v5 test. Exact source evidence passes;
  source omission and version downgrade mutations fail closed.

Production still declines Lean-certified residual publication. The next
plain-residual obligation is executable truth checking of every compiled clause
over the alive canonical domain, followed by the final semantic composition.
Repair mode, HT, CB, and concrete routing remain uncertified.

## [0.3.22] – 2026-08-17

### Compose all plain-residual source partitions

- Embed ordinary equality-free frontend clauses into the residual source
  language and prove that clause and ontology satisfaction are preserved in
  both directions.
- Lift the canonical NF3 witness refinement from one Skolem pair to any finite
  list of witness records under one shared pinned function interpretation.
- Compose directly normalized clauses, rewritten existential witness pairs,
  and independently compiled equality/disjunctive residual clauses. The main
  theorem proves satisfaction of the exact original source stream when the
  executable partition equality holds. Its axiom audit is
  `[propext, Quot.sound]`.

The next plain-residual obligation is checking this exact partition across the
source-symbol/normalization-symbol boundary in the executable wire. Production
still declines Lean-certified residual publication. Repair mode, HT, CB, and
concrete routing remain uncertified.

## [0.3.21] – 2026-08-17

### Prove canonical NF3 witness refinement

- Add `ELResidualWitness.lean` and prove the exact rewrite used by Rust:
  replacing `A ⊑ ∃R.B` with `A ⊑ ∃R.W` and `W ⊑ B` satisfies both
  original frontend Skolem clauses when the source function is pinned to the
  alive canonical `W` node.
- State the theorem over the signature-restricted canonical model used by the
  executable residual certificate. Its axiom audit is `[propext]`.
- Make Rust decline a residual certificate if any pin points outside the alive
  canonical domain. Add focused regression coverage for live and dead pins.

The remaining plain-residual obligation is whole-list executable rewrite
evidence and composition with the accepted residual clauses. Repair mode, HT,
CB, and concrete routing remain uncertified.

## [0.3.20] – 2026-08-17

### Check residual compilation evidence executable end to end

- Make residual term, atom, clause-list, and pin evidence computationally
  checkable in Lean and prove each Boolean check equivalent to the semantic
  `ResidualCompilationEvidence` contract.
- Extend certificate wire version 4 with bounded residual source clauses,
  independently numbered slot origins, compiled atoms, and exact witness pins.
  Preserve decoded evidence objects for later whole-ontology composition.
- Extend `elc-cert-check` with a standalone residual-compilation mode. A real
  Rust `compile_residual` payload passes the native Lean checker; independent
  pin and origin mutations fail closed.
- Retain source-variable names in Rust's compilation metadata and emit source
  and Skolem-function origins from separate namespaces.

The production route still declines Lean certification when residual clauses
are present. The remaining ELC obligation is certifying the NF3 witness rewrite
and composing accepted residual clauses with the canonical model. Repair mode,
HT, CB, and concrete routing remain uncertified.

## [0.3.19] – 2026-08-17

### Prove whole-theory residual compilation refinement

- Add `ELResidualCompilation.lean` and formalize the exact source residual
  language accepted by Rust, including concepts, roles, equality, ordinary
  variables, and one-level Skolem terms.
- Define proof-carrying compilation evidence for each term, atom, body, head,
  and pin, then prove compiled-clause satisfaction implies satisfaction of the
  original source clause under the pinned constant-function interpretation.
- Compose independently numbered per-clause variable tables into a whole
  residual theory with one shared Skolem-function interpretation. The
  principal theorem audits at `[propext, Quot.sound]`.
- Separate source-variable and Skolem-function namespaces in Rust's residual
  compiler. Previously equal strings in those two namespaces could alias one
  slot and incorrectly pin a universally quantified source variable. Add a
  focused regression test for this collision.

The executable wire still declines residual certificates until it can check
and construct this evidence from Rust output. Repair mode, HT, CB, and concrete
routing remain uncertified.

## [0.3.18] – 2026-08-17

### Prove canonical-model exactness with residual axioms

- Add `ELResidualCertificate.lean` and formalize the semantic contract of the
  plain ELC residual route: an exact ELC materialization remains sound after
  adding arbitrary residual axioms, and becomes complete when its canonical
  model satisfies those axioms.
- Prove exact named-class taxonomy and inconsistency theorems, both for the
  inductive ELC closure and for the executable `ClosedState`/`SoundState`
  materialization contract.
- Correct the canonical domain to match Rust: quantify only over live IDs in a
  signature-closed concept set, excluding role-only interned IDs. Prove this
  restricted canonical interpretation models every NF1–NF7 and reflexive axiom.
- Define the exact compiled residual language used by Rust, including concept,
  role, equality, and pinned canonical-witness variables.
- Add an independent finite checker and prove its Boolean acceptance equivalent
  to compiled-clause satisfaction. A kernel-evaluated example exercises it.
- Audit the principal exactness theorems at `[propext, Classical.choice,
  Quot.sound]`.

The remaining plain-residual obligation is to prove that Rust's residual
compiler and optimized join checker establish this finite semantic contract
for the original source clauses. Repair mode, HT, CB, and concrete routing
remain uncertified.

## [0.3.17] – 2026-08-17

### Connect Rust ELC normalization to the Lean checker

- Extend the ELC certificate wire to version 3 with the exact raw clause
  stream, finite variable signature, and one checked semantic origin for every
  interned symbol.
- Record each generated n-ary conjunction auxiliary as its sorted source-prefix
  identity. The decoder rejects out-of-bounds or duplicate origins, source
  concepts relabelled as auxiliaries, and auxiliary aliases.
- Reconstruct Rust's emitted normal ontology over the extended concept
  signature and run `certifyRawToNormal` inside the executable checker. The
  checker accepts only when this ontology equals the one computed from the raw
  stream, up to order and duplicate entries.
- Compose raw normalization with the existing trace, closure, Rust-state,
  public-output, symbol-table, and inconsistency checks. A mixed
  NF2/NF3/NF4 production certificate passes the native checker; independent
  mutations of its raw stream, normal forms, and origin table all fail closed.
- Add Rust regression coverage for the exact sorted conjunction-prefix IDs.

This closes the concrete raw-to-normal wire obligation for the pure ELC route.
Residual ELC modes, HT, CB, and concrete routing remain uncertified.

## [0.3.16] – 2026-08-17

### Prove whole-ontology raw-to-normal ELC equivalence

- Add a collision-free embedding of every direct NF1–NF7 clause into the
  extended concept signature and prove clause satisfaction unchanged under
  source projection.
- Add `SourceOntologyNormalEvidence`, which flattens a complete reconstructed
  source ontology into one normal-form ontology while sharing conjunction
  auxiliaries by structural prefix identity.
- Implement fail-closed `certifySourceOntologyNormal` for direct clauses,
  binary and n-ary subclass conjunctions, and binary and n-ary bottom chains.
- Prove `SourceOntologyNormalEvidence.models_iff` for the entire source list,
  not only pointwise axioms. Its axiom audit is `[propext, Quot.sound]`.
- Compose raw-list and source-normal certificates as `RawToNormalCertificate`
  and prove `models_iff`: the exact raw stream is satisfiable under a shared
  term interpretation exactly when the generated NF1–NF7 ontology models the
  source interpretation. Its additional `Classical.choice` axiom constructs
  existential witnesses.
- Add a kernel-evaluated mixed example spanning an n-ary NF2 chain, NF3
  existential pairing, and NF4 existential elimination.

The remaining ELC normalization obligation is connecting this certificate to
the concrete Rust symbol table and emitted wire ontology. HT, CB, and concrete
routing remain uncertified.

## [0.3.15] – 2026-08-17

### Certify exact conjunction-prefix expansion and remove name collisions

- Prove that every binary or n-ary subclass and bottom conjunction is
  equisatisfiable with its complete NF2 prefix chain while preserving the
  interpretation of every source concept and role.
- Add proof-producing `certifyNaryConjunction`, which accepts only the exact
  deterministic chain and fails closed on missing, reordered, or altered NF2
  clauses. `NaryConjunctionCertificate.sat_iff` has the axiom audit
  `[propext, Quot.sound]`.
- Replace Rust and Python's slash-joined `__conj__` names with byte-length-
  prefixed components. Slash joining was not injective: prefixes `["a/b","c"]`
  and `["a","b/c"]` produced the same internal concept and could contaminate
  otherwise unrelated completion chains.
- Add a Rust regression covering the collision witness and UTF-8 byte lengths,
  plus Lean acceptance and tamper-rejection examples.

Whole-ontology normal-form assembly and the raw-to-wire certificate connection
remain open. HT, CB, and concrete routing remain uncertified.

## [0.3.14] – 2026-08-17

### Add proof-producing mixed raw ELC list assembly

- Add indexed evidence for the exact two raw clauses of an existential
  introduction, retaining body variables, role/filler order, and shared
  Skolem function ID.
- Implement `certifyRawExistentialPair` for both frontend clause orders with
  exact shape and variable-wiring checks.
- Add `RawELListEvidence` to compose direct clauses and adjacent existential
  pairs while exposing every used Skolem ID.
- Implement recursive `certifyRawELList`; malformed and orphaned halves and
  reused function IDs fail closed.
- Prove `RawELListCertificate.models_iff`: every accepted mixed raw list is
  equisatisfiable with its complete reconstructed source list under one shared
  term interpretation.
- Add kernel-evaluated acceptance tests for mixed and reverse-order lists and
  rejection tests for orphan halves and duplicate function IDs. The theorem's
  axiom audit is `propext`, `Classical.choice`, and `Quot.sound`.

The assembler currently relies on the frontend invariant that each existential
pair is adjacent. Connecting that invariant to Rust's emitted stream, adding
deterministic n-ary auxiliary-name validation, and certificate-wire integration
remain open. HT, CB, and concrete routing remain uncertified.

## [0.3.13] – 2026-08-17

### Prove shared existential-pair normalization exact

- Model a list of paired existential-introduction clauses whose entries share
  one raw term interpretation.
- Prove each pair depends only on its named Skolem function, so extending the
  interpretation at another globally distinct function ID preserves it.
- Construct a shared interpretation from all source existential witnesses by
  installing one choice function per entry.
- Prove `modelsRawExistentials_sat_iff`: under global Skolem-ID uniqueness, a
  shared interpretation satisfies every raw role/filler pair exactly when the
  source interpretation satisfies every reconstructed existential axiom.
- Audit the milestone theorem: its axioms are `propext`, `Classical.choice`,
  and `Quot.sound`; choice supplies the source existential witnesses.

This closes the semantic whole-list composition obligation for already paired
existential clauses. Executable discovery of pairs in an unordered raw list,
composition with direct-list evidence, deterministic n-ary auxiliary-name
validation, and certificate-wire integration remain open. HT, CB, and concrete
routing remain uncertified.

## [0.3.12] – 2026-08-17

### Prove proof-producing direct-list normalization exact

- Define raw-ontology semantics over one shared term interpretation and prove
  its cons decomposition.
- Add `RawDirectListEvidence`, indexed by the exact raw clause list and complete
  reconstructed source ontology.
- Prove `RawDirectListEvidence.models_iff`: a pointwise list certificate
  preserves and reflects models for the entire ontology.
- Implement recursive executable `certifyRawDirectList`; every clause must
  return a `RawDirectCertificate`, otherwise the complete list normalization
  fails closed.
- Add kernel-evaluated examples for a mixed subclass/restriction/role-chain
  list and rejection when a later clause has split concept variables.

This certifies whole-list assembly for direct single-clause forms. The next
ELC frontend obligation is adding globally unique existential-half pairs to
the same list certificate, followed by deterministic n-ary auxiliary-name
validation and certificate wire integration. HT, CB, and concrete routing
remain uncertified.

## [0.3.11] – 2026-08-17

### Add a proof-producing executable direct ELC normalizer

- Add `RawDirectEvidence`, indexed by the exact raw clause and reconstructed
  source axiom. Its constructors retain concept-body decoding equations and
  every required variable inequality and role-chain wiring fact.
- Prove `RawDirectEvidence.sat_iff` by dispatching each constructor to the
  direct raw semantic theorems from v0.3.10.
- Add `RawDirectCertificate`, which carries the source axiom, canonical raw
  clause, typed evidence, and an equality tying the actual input to that
  canonical clause. Prove every such certificate semantically exact.
- Implement proof-producing concept-head, bottom, and role-head normalizers,
  then compose them as total executable `certifyRawDirect`.
- Cover subclass and arbitrary conjunction bodies, bottom, all three
  existential-elimination layouts, role inclusion, reflexivity, and both role
  chain body orders. Malformed terms and collapsed or split variables return
  `none`.
- Add kernel-evaluated examples for accepted subclass, restriction, and both
  chain orders, plus rejection of a collapsed role implication.

This closes the semantic trust gap for successful single-clause direct raw
normalization without requiring inversion of a Rust-authored result. Remaining
ELC frontend work is proof-producing whole-list assembly, existential-half
pairing in that assembly, deterministic n-ary auxiliary-name validation, and
certificate wire integration. HT, CB, and concrete routing remain uncertified.

## [0.3.10] – 2026-08-17

### Prove direct raw ELC clause families semantically exact

- Prove that every body accepted by `allConceptsOn` has exactly the decoded
  conjunction semantics at its checked variable.
- Prove raw concept-head subclass clauses and empty-head bottom clauses
  equivalent to their reconstructed source axioms for arbitrary conjunction
  length.
- Prove raw existential-elimination clauses equivalent to `∃R.A ⊑ B` in
  role-first, concept-first, and top-filler/domain forms.
- Prove correctly wired raw role inclusions, reflexive role facts, and connected
  three-variable role chains equivalent to their source semantics. Both role
  chain body orders are covered.
- Connect the executable empty-head recognizer branch directly to the bottom
  equivalence theorem.
- Refine existential-elimination recognition to return a typed shape that
  records atom order and checked source/target variables, preparing small
  constructor-specific inversion proofs instead of one brittle global split.

The concept-head and role-head recognizer branches still need their executable
inversion theorems before the whole `recognizeRawClause` result can be connected
to these family proofs. Whole-list pairing, deterministic n-ary auxiliary-name
validation, and certificate wire integration also remain open. HT, CB, and
concrete routing remain uncertified.

## [0.3.9] – 2026-08-17

### Prove raw Skolem-pair normalization exact

- Add a typed Lean model of the frontend's recursive raw terms, equality-free
  atoms, clauses, term interpretation, and universally quantified Horn
  semantics.
- Add executable raw-clause recognition for direct ELC forms, with explicit
  checks for concept-variable sharing, role orientation, distinct role
  endpoints, connected three-variable role chains, and both body atom orders
  for existential elimination.
- Add executable recognition of the two raw clauses that share a Skolem
  function for `A ⊑ ∃R.B`; reject mismatched body/source/argument variables,
  source concepts, function ids, and nested terms.
- Prove `rawExistentialPair_sat_iff`: the paired raw Skolem clauses are
  equisatisfiable with the reconstructed source existential axiom. The forward
  proof extracts the function value as a witness; the reverse proof extends an
  arbitrary raw interpretation with a choice function.
- Harden both Rust `to_nf` and its zero-copy routing screen with the same
  variable-distinctness and Skolem-argument checks. Malformed raw JSON now
  fails closed instead of being read as a stronger EL axiom.

The raw clauses are not yet carried in certificate wire version 2, so the
production checker does not yet invoke these recognizers. The direct raw-form
semantic bridge, deterministic n-ary auxiliary-name check, whole-list pairing,
and wire integration remain open. HT, CB, and concrete routing remain
uncertified.

## [0.3.8] – 2026-08-17

### Prove n-ary ELC conjunction expansion conservative

- Extend `ELNormalization.lean` with the left-associated NF2 prefix-chain
  construction used for n-ary subclass and bottom axioms.
- Model fresh conjunction concepts in an extended signature, indexed by their
  exact source prefixes.
- Define source-model extension by interpreting each auxiliary as the
  intersection of its prefix, and define projection back to the original
  concept signature.
- Prove subclass and bottom expansion in both directions: every generated-chain
  model projects to a source-axiom model, and every source model extends to a
  generated-chain model.
- Add an executable four-conjunct example pinning the exact three-clause NF2
  chain shape.

The remaining ELC frontend obligation is executable recognition of raw JSON
clauses, including variable wiring, Skolem role/filler pairing, deterministic
sorting and auxiliary-name validation, and equality with Rust's emitted normal
forms. HT, CB, and concrete routing remain uncertified.

## [0.3.7] – 2026-08-17

### Prove direct ELC frontend normalization exact

- Add `ELNormalization.lean`, a semantic source language for the EL axioms
  reconstructed from frontend Horn clauses. It represents conjunction bodies,
  bottom axioms, existential introduction and elimination, role inclusion,
  role chains, and reflexivity.
- Define `normalizeDirect` for every translation that introduces no auxiliary
  conjunction concept: top inclusion and NF1–NF7.
- Prove `normalizeDirect_sat_iff`: every successful direct translation
  preserves and reflects satisfaction in every interpretation.
- Prove `models_direct_iff`: pointwise successful direct normalization
  preserves and reflects models of a complete source-axiom list.

This establishes the semantic frontend boundary for direct forms. The
remaining ELC normalization proof must cover n-ary conjunction auxiliary
expansion and executable reconstruction of paired Skolem clauses from the raw
frontend JSON. HT, CB, and concrete routing remain uncertified.

## [0.3.6] – 2026-08-17

### Certify named ELC publication and inconsistency

- Extend the ELC wire certificate to version 2 with the complete finite symbol
  table, named public subsumptions, and the public inconsistency flag.
- Require the active context set to match every concept position in the
  normalized ontology, with `TOP` always active and `BOTTOM` excluded as a
  subject context. This prevents a certificate from proving a selected subset
  while silently omitting another taxonomy subject.
- Prove soundness and satisfiable-subject completeness for both ID-level and
  named public subsumptions. Prove the checked public inconsistency flag
  equivalent to semantic unsatisfiability.
- Make checker-enabled Rust publish directly from the verified named result,
  leaving no unchecked result conversion after checker acceptance.
- Initialize the Rust `TOP` completion context unconditionally. The public
  inconsistency test queried this context even when no normalized axiom had
  caused it to be initialized.
- Isolate checker stdout from the worker JSON protocol. Valid and tampered
  end-to-end tests confirm byte-valid JSON, equality with the ordinary pure ELC
  result, and fail-closed rejection of named-output, active-context, and
  consistency-flag alterations.

The remaining end-to-end ELC boundary is OWL/frontend-clause normalization.
Residual ELC modes, HT, CB, and concrete routing remain uncertified.

## [0.3.5] – 2026-08-17

### Certify pure ELC result materialization

- Extend the Rust certificate with the exact ID-level subsumption relation
  materialized by the public output loop.
- Check both directions between that relation and the certified Rust state
  after applying the public conventions: omit top and bottom subjects,
  reflexive pairs, and top objects; retain bottom objects for unsatisfiable
  classes.
- Prove `public_subsumption_sound`: every subsumption accepted for publication
  is semantically entailed by the normalized pure ELC ontology.
- Test a complete Rust-to-native-Lean run and rejection after injecting a
  forbidden public-output pair.
- Pin the optional `dhat` dependency to the available 0.3.3 release, repairing
  clean locked builds after crates.io stopped offering the locked 0.3.4 package.

This milestone certifies normalized ID-level output. OWL frontend translation,
ID-to-IRI presentation, residual ELC modes, HT, CB, and concrete routing remain
outside the certified boundary.

## [0.3.4] – 2026-08-17

### ELC Rust-to-Lean refinement path

- Add a deterministic Rust certificate reconstruction pass that records NF1–NF7
  derivations and compares the reconstructed formal closure with the optimized
  production state on every active concept context.
- Add a versioned JSON wire decoder with checked finite symbol ids and a native
  `elc-cert-check` executable.
- Include the active Rust contexts and complete Rust subsumption and edge stores
  in the certificate. Lean verifies both directions of state agreement, and
  `active_subsumption_exact` proves accepted active-context taxonomy answers
  semantically exact.
- Add fail-closed Rust invocation through `KM_ELC_LEAN_CERT_CHECKER`; checker
  rejection produces no reasoner output. `KM_ELC_LEAN_CERT_OUT` retains a
  certificate for inspection.
- Replace exhaustive irrelevant symbol-tuple enumeration with a premise-driven
  closure checker. The representative NF1–NF7 smoke certificate fell from about
  30 seconds to 0.07 seconds end to end on the workstation.

## [0.3.3] – 2026-08-17

### Prove executable ELC certificate exactness

`checkClosedTrace` exhaustively checks initialization and closure under every
pure ELC rule over the finite interned concept and role signature.
`checkClosedTrace_closed` proves that acceptance constructs the v0.4.0
`ClosedState` contract. `checkedTrace_exact` combines this result with the
v0.3.2 proof-trace soundness theorem and proves that an accepted certificate's
taxonomy and inconsistency readouts are semantically exact.

The default Lean build includes executable positive and negative checker
examples and contains no `sorry` or `admit`. The remaining ELC refinement work
is to serialize the Rust worker's normal forms and completed state into this
certificate, invoke the checker fail closed, and prove the wire translation.

## [0.3.2] – 2026-08-17

### Verify executable ELC proof traces

`ContextCalculus/ELCompletionCertificate.lean` defines finite proof steps for
every pure ELC rule, including initialization, NF1–NF7, reflexivity, and
backward bottom propagation. `checkTrace` is executable and accepts a step only
when all premises and the source normal form occur in the certificate.

`validStep_derivable` proves each accepted step semantically derivable.
`checkTrace_sound` lifts this result to complete traces, and
`checkedTrace_soundState` constructs the v0.4.0 `SoundState` contract for the
materialization represented by any accepted trace. The module is part of the
default Lean build and contains no `sorry` or `admit`.

This release does not yet provide the exhaustive finite closure checker or the
Rust certificate serialization and fail-closed invocation needed to establish
the `ClosedState` half and executable ELC refinement.

## [0.4.0] – 2026-08-17

### Prove the exact ELC materialization contract

`ContextCalculus/ELCompletionRefinement.lean` introduces the abstract view of
the Rust worker's completed `sub_super` and `edges` stores. `ClosedState` lists
the precise initialization and closure obligations for NF1–NF7, reflexive
roles, and backward bottom propagation. `SoundState` requires every stored
subsumption and edge to have a derivation in the v0.3.0 semantic calculus.

`ClosedState.sub_complete` and `ClosedState.edge_complete` prove by mutual
induction that a closed state contains every derivable fact. Combined with
`SoundState`, `sub_iff_of_exact` and `edge_iff_of_exact` prove extensional
equality with the semantic closure. `entails_iff_materialized` then proves the
materialized taxonomy exact, including unsatisfiable subjects, and
`unsat_iff_materialized` proves the materialized `TOP ⊑ BOTTOM` test equivalent
to semantic ontology inconsistency.

The module is `sorry`-free and part of the default Lean target. The remaining
ELC executable-refinement obligation is concrete: prove that
`elcomplete.rs`'s final indexed state satisfies `ClosedState` and `SoundState`,
including the normal-form recognizer, queue execution, batched NF4 schedule,
certificate modes, and output conversion. This release does not claim that
remaining step, nor HT, CB, or concrete routing certification.

## [0.3.0] – 2026-08-17

### Certify the full pure ELC calculus and fail-closed composition

`ContextCalculus/ELCompletion.lean` formalizes every pure normal form accepted
by the Rust ELC worker: NF1–NF7 and reflexive roles. Its closure includes
explicit top and bottom, conjunction, existential introduction and
elimination, backward bottom propagation, role hierarchy, role-chain
composition, and reflexivity. `sub_sound` and `edge_sound` prove every closure
fact valid in every interpretation of those normal forms.

The canonical interpretation contains exactly the contexts not labelled
bottom. `canon_models` proves that this nonempty alive-context interpretation
models every accepted axiom. `top_bottom_sound` and `top_bottom_complete`
justify the worker's `TOP ⊑ BOTTOM` inconsistency criterion, and
`subsumption_complete` proves that every named-class entailment is represented
either directly or by the stronger result that its subject is unsatisfiable.

`ContextCalculus/Certification.lean` formalizes the supervisor boundary as
four outcomes: publish, defer, error, and timeout. It proves soundness and
completeness composition for sequential portfolios, faithful and live races,
and profile-based routers. Non-publication outcomes are fail-closed by type.

The complete default Lean target builds successfully with no `sorry`. The new
ELC soundness and canonical-model theorems use no axioms; the semantic
subsumption capstone uses Lean's standard classical quotient axioms. This
release does not claim executable ELC certification: refinement of Rust's
normal-form recognizer, indexed worklist, output mapping, and certificate modes
remains open, as do HT, CB, and concrete routing refinement.

## [0.2.36] – 2026-08-15

### Partition two large production-bridge profiles

The automatic `production_all` route now assigns four bounded, independent
subject-classification workers to the large SRIQ bridge profile represented by
ORE14817 and two workers to the large SHI bridge profile represented by
ORE3215. Every worker receives the complete ontology and candidate-superclass
universe. The bridge publishes a merged answer only when every partition
completes; otherwise it defers to the existing exact fallback. This changes
scheduling only, not routing, inference rules, or accepted certificates.

Three alternating same-node pairs in jobs `50554126` and `50554127` preserve
the gold-matching full-IRI signatures and all answer metadata. ORE14817 median
wall falls from 91.8347 to 75.0825 seconds; ORE3215 falls from 125.5704 to
89.1692 seconds. Their median process-tree peak RSS rises from 2,799.62 to
5,963.04 MiB and from 6,278.98 to 9,643.82 MiB, respectively, within the
20-GiB benchmark contract.

Order-balanced full-corpus job `50554161` contains exactly 1,184 terminal
records, 1,184 checkpoints, 592 pair-completion markers, and no temporary
outputs. Both arms report 591 successful classifications and ORE1194 as the
sole fail-closed error. There are zero differences in status, verdict,
consistency, selected route, solved state, answer counts, or full-IRI
signature. Mean wall falls from 3.32327 to 3.23825 seconds. Candidate median
wall is 0.1628 seconds, mean peak RSS is 427.88 MiB, and median peak RSS is
35.39 MiB. All four are below the frozen Konclude measurements of 3.2657
seconds, 0.2813 seconds, 558.09 MiB, and 76.53 MiB.

The complete serial release-mode suite passes 2,006 library tests with eight
ignored tests and every integration test, including the issue #3 pigeonhole
regression. Evidence is in
[`results/benchmarks/2026-08-15-large-bridge-subjects/`](results/benchmarks/2026-08-15-large-bridge-subjects/README.md).

## [0.2.35] – 2026-08-15

### Partition large certified-bridge subjects

The automatic `certified_nominals` route now partitions ORE10621's independent
named-class jobs across four bounded bridge workers. Every worker receives the
complete ontology and candidate-superclass universe. Results are merged,
sorted, and deduplicated only after every worker returns a complete answer; a
decline from any worker defers the entire bridge to the existing exact
fallback. This changes scheduling only, not routing, inference rules, or
accepted certificates.

Three alternating same-node pairs in job `50552259` preserve the
gold-matching full-IRI signature and `certified_nominals` route. Median wall
falls from 83.2711 to 38.9416 seconds. Median process-tree peak RSS rises from
1,273.03 to 1,555.85 MiB and remains below Konclude's measured 2,470 MiB on
this ontology.

Order-balanced full-corpus job `50552285` contains exactly 1,184 terminal
records, 1,184 checkpoints, 592 pair-completion markers, and no temporary
outputs. Both arms report 591 successful classifications and ORE1194 as the
sole fail-closed error. There are zero differences in status, verdict,
consistency, selected route, solved state, answer counts, or full-IRI
signature. Mean wall falls from 3.41986 to 3.33021 seconds, median wall from
0.1625 to 0.1621 seconds, and median peak RSS from 35.14 to 35.02 MiB. Mean
peak RSS changes from 416.34 to 417.04 MiB and remains below Konclude's 558.09
MiB.

The complete release-mode suite passes 2,006 library tests with eight ignored
tests and every integration test, including the issue #3 pigeonhole
regression. Evidence is in
[`results/benchmarks/2026-08-15-parallel-bridge-subjects/`](results/benchmarks/2026-08-15-parallel-bridge-subjects/README.md).

## [0.2.34] – 2026-08-15

### Schedule the large SRIQ bridge before CB fallback

The automatic `production_all` route now schedules the already certified,
complete hypertableau bridge before its consequence-based fallback for the
large SRIQ profile used by ORE14817. A successful bridge answer is published;
decline, error, or resource exhaustion retains the exact production fallback.
The selected route and all certificates are unchanged. This is a scheduling
change only and does not alter either reasoner's inference rules.

Three alternating same-node pairs on ORE14817 preserve the gold-matching
full-IRI signature and `production_all` route. Mean wall is flat at 92.099
versus 92.205 seconds, while mean process-tree peak RSS falls from 5,100.81 to
2,800.43 MiB. Order-balanced full-corpus job `50548596` contains exactly 1,184
terminal rows, 1,184 matching checkpoints, 592 complete pairs, and no temporary
outputs. Both arms report 591 successful classifications and ORE1194 as the
sole fail-closed error. There are zero differences in status, verdict,
consistency, selected route, solved state, answer counts, or full-IRI signature.
Mean peak RSS falls from 420.39 to 416.06 MiB and summed peak RSS falls by
2,555.49 MiB. Corpus wall is treated as flat measurement noise; the candidate
reports 3.43423 seconds mean and 0.1623 seconds median wall.

The complete release-mode suite passes 2,005 library tests with eight ignored
tests and every integration test, including the issue #3 pigeonhole regression.

Evidence is in
[`results/benchmarks/2026-08-15-sequential-sriq-bridge/`](results/benchmarks/2026-08-15-sequential-sriq-bridge/README.md).

## [0.2.33] – 2026-08-15

### Pay-as-needed certified EL fallback serialization

Certified EL classification no longer serializes a complete JSON clause copy
before it knows that the production fallback is needed. In-process certified
routes retain their typed clauses directly and rebuild the production input
only after a certificate declines. For subprocess routes, source documents of
at least 512 MiB use the existing checked binary clause handoff and omit the
dead JSON stream after that handoff succeeds. Smaller certified subprocess
routes keep the established JSON path because repeated paired measurements
show that the extra encoding does not amortize there. Exact EL behavior is
unchanged. This changes representation and scheduling only; routing,
certificates, completion rules, and accepted answers are unchanged.

Order-balanced full-corpus job `50547528` contains exactly 1,184 terminal rows,
1,184 matching checkpoints, 592 complete pairs, and no temporary outputs. Both
arms report 591 successful classifications and ORE1194 as the sole fail-closed
error. There are zero differences in status, verdict, consistency, selected
route, solved state, answer counts, or full-IRI signature. Mean wall falls from
3.45100 to 3.43487 seconds, median wall from 0.1627 to 0.1622 seconds, mean peak
RSS from 424.24 to 420.40 MiB, and median peak RSS from 35.05 to 34.39 MiB.
Summed wall falls by 9.5335 seconds. ORE16744 accounts for the intended large
handoff gain: wall falls from 63.2610 to 60.1049 seconds and peak RSS from
5,668.39 to 3,570.22 MiB.

The complete release-mode suite passes 2,005 library tests with eight ignored
tests and every integration test, including the issue #3 pigeonhole regression.
Evidence is in
[`results/benchmarks/2026-08-15-certified-el-payg/`](results/benchmarks/2026-08-15-certified-el-payg/README.md).

## [0.2.32] – 2026-08-15

### Compact dense EL taxonomy handoff

Complete subprocess EL results with at least two million subsumptions now use
a versioned dictionary-coded handoff. Each class name is owned once and row
endpoints use checked integer identifiers. Sparse results and partial
certificate residues retain the established JSON contract. Decoding rejects
bad identifiers, truncation, trailing bytes, and excessive lengths without
publishing an answer. This changes transfer representation only; EL
completion, routing, certificates, and the final ordered JSON result are
unchanged.

Order-balanced full-corpus job `50546048` contains exactly 1,184 terminal rows
over all 592 ontologies, with no temporary outputs. Both arms report 591
successful classifications and ORE1194 as the sole fail-closed error. There
are zero differences in status, verdict, consistency, selected route, solved
state, answer counts, or full-IRI signature. Mean wall falls from 3.44657 to
3.41502 seconds, saving 18.645 seconds over the 591 successful pairs. Mean and
median peak RSS, and the sub-millisecond median-wall movement, are treated as
flat measurement noise, so this release makes no memory or median claim.

Three preceding threshold-selection replications (`50543902`, `50544635`, and
`50544636`) each produced 1,184 validated rows with zero semantic differences.
The release suite passes 1,997 library tests with eight ignored tests and all
integration tests, including malformed compact-output checks and the issue #3
pigeonhole regression. Evidence is in
[`results/benchmarks/2026-08-15-compact-elc-output/`](results/benchmarks/2026-08-15-compact-elc-output/README.md).

## [0.2.31] – 2026-08-15

### Share classification reference tables across jobs

KPSet classification message adapters now share their immutable ontology-wide
concept-reference table through `Arc` instead of cloning the complete table for
every classified concept. The mutable adapter API retains copy-on-write
semantics, so any future mutation remains isolated. This changes representation
and allocation only; model construction, message order, routing, and accepted
answers are unchanged.

Three order-balanced full-corpus jobs (`50537280`, `50538368`, and `50539369`)
each produced 1,184 terminal rows over all 592 ontologies. Every arm reports 591
successful classifications and ORE1194 as the sole fail-closed error. Across
all three jobs there are zero differences in status, verdict, consistency,
selected route, solved state, answer counts, or full-IRI signature. The pooled
1,776 classifications per arm reduce mean wall from 3.52007 to 3.50786 seconds,
median wall from 0.16145 to 0.16075 seconds, and median peak RSS from 35.125 to
34.965 MiB. Summed wall falls by 21.681 seconds. Mean peak RSS is statistically
flat at 454.246 versus 454.347 MiB; its 0.022% difference changes direction
between replications, so this release makes no mean-memory improvement claim.

The focused same-node ORE3215 gate (`50537191`) reduces mean wall from 128.120
to 124.495 seconds while preserving byte-identical 367-MiB JSON output in both
orderings. The complete serial release suite passes 1,995 library tests with
eight ignored tests and all integration tests, including the issue #3
pigeonhole regression. Evidence is in
[`results/benchmarks/2026-08-15-shared-classification-references/`](results/benchmarks/2026-08-15-shared-classification-references/README.md).

## [0.2.30] – 2026-08-15

### Hash repeated taxonomy IRI lookups

The JSON output mapper now uses a hash index for its lookup-only local-name to
IRI-ID table. Serialized ordering remains owned by the sorted IRI vector and
ordered row map. The grouped JSON path also avoids a redundant ordered-map
lookup for every subject. This changes only final output representation and
lookup cost; reasoning, routing, accepted answers, and serialized bytes are
unchanged.

Order-balanced same-node job `50535110` runs v0.2.29 and binary
`1da5c66a9642…` on all 592 ontologies. Both arms report 591 successful
classifications and ORE1194 as the sole fail-closed error. Every status,
verdict, consistency result, selected route, and full-IRI signature is
identical. Mean wall falls from 3.52441 to 3.47996 seconds, median wall from
0.1874 to 0.1617 seconds, mean peak RSS from 424.010 to 423.700 MiB, and median
peak RSS from 35.38 to 34.41 MiB. The paired wall reduction sums to 26.267
seconds.

Node-local byte comparisons on ORE10689, ORE868, and ORE1012 confirm identical
JSON output and reduce wall by 2.66, 2.42, and 0.68 seconds respectively. The
complete serial release suite passes 1,994 library tests with eight ignored
tests and all integration tests, including the issue #3 pigeonhole regression.
Evidence is in
[`results/benchmarks/2026-08-15-iri-hash/`](results/benchmarks/2026-08-15-iri-hash/README.md).

## [0.2.29] – 2026-08-15

### Skip redundant closure of certified bridge taxonomies

The completion bridge publishes a taxonomy only after its complete-answer
certificate succeeds. Its result is already transitively closed, so the worker
now bypasses the generic hypertableau closure repair on that successful branch.
Other hypertableau branches retain the repair. This removes a repeated scan of
large bridge taxonomies without changing inference rules, route selection, or
the accepted answer contract.

Strict sweep `50531678` contains exactly 592 terminal rows for binary
`c5b85fea05ca…`: 591 are successful and ORE1194 remains the sole fail-closed
error. Every status, verdict, consistency result, selected route, and full-IRI
signature is identical to v0.2.28. Mean wall falls from 3.55523 to 3.52876
seconds, a 15.6-second reduction over the 591 successful ontologies. The strict
sweep reports 424.09 MiB mean and 35.23 MiB median peak RSS.

Order-balanced same-node job `50532459` runs both binaries for all 592
ontologies and finds zero semantic differences. Its candidate arm reduces
summed wall by 14.04 seconds, mean wall from 3.57766 to 3.55391 seconds,
absolute median wall from 0.1839 to 0.1797 seconds, and absolute median peak RSS
from 35.22 to 34.62 MiB. Mean RSS is flat within 0.10 MiB, so this release makes
no memory-improvement claim. The complete serial release suite passes 1,994
library tests with eight ignored tests and all integration tests, including the
issue #3 pigeonhole regression. Evidence is in
[`results/benchmarks/2026-08-15-el-binary-handoff/`](results/benchmarks/2026-08-15-el-binary-handoff/README.md).

## [0.2.28] – 2026-08-15

### Compact exact-EL handoff and reduce orchestration overlap

Large exact-EL subprocess routes now pass normalized clauses through a compact,
versioned binary representation. The worker accepts both this representation
and the established JSON contract. Exact EL leaves omit the dead JSON copy;
certified EL routes retain JSON for their mandatory complete fallback. The
codec is lossless and fail-closed, and route selection and completion rules are
unchanged.

Public-output lookup tables are now built after classification, so their bucket
allocations do not overlap frontend and reasoner high-water marks. Temporary
worker paths reuse one process-local directory and collision nonce instead of
querying the clock and environment for every handoff. These are lifetime and
orchestration changes only; they do not alter the calculus or derived fixpoint.

Strict sweep `50528307` contains 592 terminal rows for binary `4aa2370c8ceb…`:
591 are successful and ORE1194 remains the sole fail-closed error. Every status,
verdict, consistency result, selected route, and full-IRI signature is identical
to v0.2.27, including all four collision-sensitive fingerprints. Relative to
the published v0.2.27 measurements, mean wall falls from 3.58613 to 3.55523
seconds, median wall from 0.1848 to 0.1635 seconds, mean peak RSS from 433.282
to 423.840 MiB, and median peak RSS from 35.04 to 34.60 MiB.

Order-balanced full pair `50526676` independently verifies the compact
handoff's mean wall and memory reductions. Median-boundary panel `50527646`
runs 270 alternating pairs over 90 ontologies and preserves every signature;
the final overhead changes reduce panel mean wall by 1.03 milliseconds and
mean peak RSS by 0.213 MiB. The complete release suite passes 1,994 library
tests with eight ignored tests and all integration tests, including the issue
#3 pigeonhole regression. Evidence is in
[`results/benchmarks/2026-08-15-el-binary-handoff/`](results/benchmarks/2026-08-15-el-binary-handoff/README.md).

## [0.2.27] – 2026-08-15

### Reuse KPSet labels and extend exact EL routing

KPSet classification now reuses equivalent-candidate sets, possible-subsumer
templates, and root-label tags within each completed model. These are cached
representations of the same model labels and tests; the change does not alter
blocking, branching, calculus rules, or the derived fixpoint.

The automatic classifier now recognizes four role-free, ABox-free exact OWL EL
terminologies containing named intersections and sends them to the existing EL
completion implementation. A fail-closed source certificate excludes RBox,
property, data, disjunction, complement, quantifier, cardinality, nominal, and
datatype constructs. Small flat and intersection-only terminologies keep typed
EL completion in the orchestrator process, while larger inputs retain process
isolation. The ELC worker still validates normalized clauses before publishing.

Strict sweep `50517606` contains 592 terminal rows for binary
`628b11d8e95d…`: 591 are successful and ORE1194 remains the sole fail-closed
error. It has zero semantic differences from v0.2.26 and exactly four expected
route changes, from `production_all` to `elc` for ORE868, ORE9590, ORE10806,
and ORE13664. Order-balanced same-node sweep `50518274` independently ran both
binaries for every ontology. Relative to v0.2.26, mean wall falls from 3.65019
to 3.58613 seconds, median wall from 0.1893 to 0.1848 seconds, mean peak RSS
from 436.020 to 433.282 MiB, and median peak RSS from 35.85 to 35.04 MiB. The
complete serial release suite passes 1,991 library tests with eight ignored
tests and all integration tests, including the issue #3 pigeonhole regression.
Evidence is in
[`results/benchmarks/2026-08-15-flat-inproc-elc/`](results/benchmarks/2026-08-15-flat-inproc-elc/README.md).

## [0.2.26] – 2026-08-14

### Restore the isolated complete ground-clause route

The automatic classifier now selects the retained general HT route for the
compact SHOIF(D) ground-clause profile represented by ORE6934. An explicit
`general` worker preserves the complete normalized clause input and no longer
activates typed-ABox specialist state or installs the same ABox a second time.
The reasoning input and result are unchanged; only scheduling and duplicate
worker state change.

Strict sweep jobs `50503499`, `50503695`, and `50503696` contain 592 validated
terminal rows for binary `4d8d81378d565…`: 591 are successful and ORE1194
remains the sole fail-closed error. Comparison with v0.2.25 finds zero
differences in status, verdict, consistency, or signature. ORE6934 is the only
route change, from `nominal_ni_abox` to `ht_general`; it falls from 68.9191
seconds and 2,948.33 MiB to 0.1565 seconds and 44.02 MiB with the same exact
gold signature. Across the 591 successful rows, mean wall falls from 3.72268
to 3.60775 seconds, median wall from 0.1860 to 0.1839 seconds, and mean peak RSS
from 440.806 to 436.372 MiB. Median peak RSS is 36.16 MiB versus 36.04 MiB in
the independent baseline sweep. Evidence is in
[`results/benchmarks/2026-08-14-6934-route-recovery/`](results/benchmarks/2026-08-14-6934-route-recovery/README.md).

## [0.2.25] – 2026-08-14

### Build frontend IRI metadata in one sorted pass

The frontend now sorts owned IRI metadata once, derives the named-class vector
from that ordering, and bulk-constructs its ordered map. This removes a second
independent ordering pass without changing the map, names, clauses, or routes.
An independent IBEX sweep found byte-identical clause and metadata output for
all 592 ontologies.

Strict sweep `50499428` contains 592 validated terminal rows for binary
`7c090417f169d5…`: 591 are successful and ORE1194 remains the sole fail-closed
error. Comparison with v0.2.24 finds zero differences in status, verdict,
consistency, selected route, or signature. Mean wall falls from 3.77991 to
3.72268 seconds, median wall from 0.1887 to 0.1860 seconds, mean peak RSS from
441.536 to 440.806 MiB, and median peak RSS from 36.17 to 36.04 MiB. The
complete release suite passes 1,987 library tests with eight ignored tests and
all integration tests, including the issue #3 pigeonhole regression. Evidence
is in
[`results/benchmarks/2026-08-14-iri-map-bulk/`](results/benchmarks/2026-08-14-iri-map-bulk/README.md).

## [0.2.24] – 2026-08-14

### Parallelize dense EL NF4 frontiers

The EL completion path now groups dense edge-side NF4 frontiers by parent,
computes missing propagation conclusions in parallel, and inserts them in
deterministic order. Sparse frontiers keep the established serial join. The
automatic route enables this scheduler only for a source-profile shape that
matches ORE8737 among the 592 stored ORE profiles.

Three alternating automatic-route pairs preserve the gold signature and
reduce ORE8737 mean wall from 85.174 to 78.256 seconds. Strict sweep `50496853`
contains 592 validated terminal rows for binary `b51af8f49e59f4c…`: 591 are
successful and ORE1194 remains the sole fail-closed error. Comparison with
v0.2.23 finds zero differences in status, verdict, consistency, route, or
signature. Mean wall falls from 3.78352 to 3.77991 seconds; median wall is
0.1887 seconds, mean peak RSS is 441.536 MiB, and median peak RSS is 36.17 MiB.
The complete release suite, including issue #3, passes. Evidence is in
[`results/benchmarks/2026-08-14-parallel-nf4-frontier/`](results/benchmarks/2026-08-14-parallel-nf4-frontier/README.md).

## [0.2.23] – 2026-08-14

### Pass certified EL clauses directly to completion

The two giant certified-EL inputs now pass the frontend's typed clause vector
directly to the same EL completion implementation instead of starting a worker
that reparses the serialized JSON handoff. The serialized clause file remains
available and authoritative for the exact `production_all` fallback if EL
certification declines or errors. This changes process boundaries and
representation only; it does not change completion rules, certification, route
selection, or fallback behavior.

Three alternating ORE8737 pairs produced identical gold-matching signatures
and reduced mean wall from 96.743 to 80.223 seconds. Independent pairs reduced
ORE16744 from 73.233 to 63.438 seconds. Strict sweep `50494584` contains
exactly 592 results, profiles, and checkpoints for binary `13b4d406aaddb4…`.
It reports 591 successful classifications, ORE1194 as the sole fail-closed
error, and zero status, consistency, signature, or coverage regressions from
v0.2.22. Mean wall falls from 3.84669 to 3.78352 seconds and median wall remains
0.1885 seconds. Independent-sweep RSS moved from 441.114 to 441.459 MiB mean
and from 35.73 to 36.47 MiB median; focused affected-route peaks differed by
less than 0.2%. The complete release suite, including issue #3, passes.
Evidence is in
[`results/benchmarks/2026-08-14-certified-el-typed-handoff/`](results/benchmarks/2026-08-14-certified-el-typed-handoff/README.md).

## [0.2.22] – 2026-08-14

### Wake the supervisor when workers exit

On Linux, the engine watchdog now waits on a process file descriptor between
RSS and deadline checks. A completed child wakes the supervisor immediately
instead of waiting for the remainder of an exponential polling interval, which
previously reached 100 ms on longer worker stages. Kernels without `pidfd_open`
and non-Linux systems retain the established sleep-based watchdog. Focused
tests cover normal completion, timeout termination, and RSS-cap termination.

Release builds use aborting panic behavior, reducing the multi-call binary's
code from 10.44 to 9.23 MiB while leaving normal execution unchanged. Five
measured nominal-free production shapes use one CB worker instead of the full
parallel allocation. The route portfolio, bridge, complete fallback, and
winner contract are unchanged. These changes affect process notification,
release code generation, and scheduling only; they do not alter reasoning
rules or derived results.

The 85-run alternating pidfd panel produced byte-identical output and reduced
panel median wall from 0.21 to 0.20 seconds. Strict sweep `50492209` contains
exactly 592 results, profiles, and checkpoints for binary
`4379bd61e853869c…`. It reports 591 successful classifications, ORE1194 as the
sole fail-closed error, and zero status, verdict, signature, consistency, or
coverage regressions from v0.2.21. Mean wall falls from 3.89729 to 3.84669
seconds, median wall from 0.1897 to 0.1885 seconds, mean peak RSS from 443.222
to 441.114 MiB, and median peak RSS from 35.94 to 35.73 MiB. The complete
release suite, including the issue #3 pigeonhole regression, passes. Evidence
is in
[`results/benchmarks/2026-08-14-exit-notified-workers/`](results/benchmarks/2026-08-14-exit-notified-workers/README.md).

## [0.2.21] – 2026-08-14

### Accelerate incremental subset blocking

Mode-1 incremental subset blocking now maintains a dense encoded-literal
shadow of each dependency-bearing concept label. Candidate blockers are still
selected by the established rarest-literal posting list, but the exact label
subset test uses contiguous bit operations instead of repeated hash-table
membership probes. The bitsets exist only while this blocking mode is active;
other tableau modes and all non-tableau routes retain their prior allocation
layout. This is a representation change for the same blocking predicate and
does not alter reasoning rules, branch order, dependencies, or derived results.

The exact ORE6934 pair `50480341` preserved byte-identical output and identical
search work while reducing wall from 123.09 to 73.15 seconds, peak RSS from
3,082,604 to 2,985,812 KiB, and measured blocking time from 105.136 to 54.422
seconds. Independent strict sweep `50483032` contains exactly 592 results,
profiles, and checkpoints. It reports 591 successful classifications, ORE1194
as the sole fail-closed error, and zero status, verdict, signature,
consistency, or coverage regressions from v0.2.20. Mean wall falls from 3.95409
to 3.89729 seconds, median wall from 0.1910 to 0.1897 seconds, mean peak RSS
from 443.371 to 443.222 MiB, and median peak RSS from 36.43 to 35.94 MiB. The
complete release suite, including the issue #3 pigeonhole regression, passes.
Evidence is in
[`results/benchmarks/2026-08-14-bitset-blocking/`](results/benchmarks/2026-08-14-bitset-blocking/README.md).

## [0.2.20] – 2026-08-14

### Reduce automatic frontend handoff overhead

Automatic classification now keeps functional-syntax inputs smaller than 4
MiB in the orchestrator process, avoiding a frontend subprocess around the
corpus median. Exact in-process EL leaves pass their typed clauses directly to
completion without writing an unused JSON handoff, and atomic EL/CB mechanisms
avoid cloning an owned named-class set used only by HT, tableau, and portfolio
conversion. Three measured 300–600 MiB exact-EL inputs enter the in-process
path only after a fail-closed source scan excludes inverse, symmetric, and
transitive object-property axioms that require the established isolated route.

These changes affect process boundaries, serialization, allocation lifetime,
and scheduling only. They do not change reasoning rules, ordering, redundancy,
or the derived fixpoint. The 57-ontology 2–4 MiB panel `50472992` ran three
alternating pairs per ontology and produced byte-identical outputs throughout.
Median wall fell from 0.28 to 0.26 seconds and median peak RSS from 42,156 to
39,088 KiB. Separate giant, sparse-EL, ABox, subprocess-fallback, and
median-band panels verified the safety gates.

Strict sweep `50473463` contains exactly 592 results, profiles, and completion
markers. It reports 591 successful classifications, ORE1194 as the sole
fail-closed error, and zero status, verdict, signature, consistency, or
coverage differences from v0.2.19. Mean wall falls from 4.00461 to 3.95409
seconds, median wall from 0.2159 to 0.1910 seconds, mean peak RSS from 449.847
to 443.371 MiB, and median peak RSS from 38.66 to 36.43 MiB. The complete
serial release suite, including the issue #3 pigeonhole regression, passes.
Evidence is in
[`results/benchmarks/2026-08-14-large-inproc-ofn/`](results/benchmarks/2026-08-14-large-inproc-ofn/README.md).

## [0.2.19] – 2026-08-14

### Reduce one-shot allocation overlap

Small ontologies selected for exact in-process EL completion now pass the
frontend's typed clause vector directly into completion instead of reading and
parsing the JSON handoff that remains available to subprocess fallbacks. The
frontend retains this vector only for the selected `elc` route; every other
route drops it at the same lifetime boundary as v0.2.18. The one-shot CB CLI
also releases its converted source-clause arena after building the immutable
prepared ontology and query-equivalence groups. Reusable library reasoners keep
their existing input-retention contract.

Role-chain preprocessing derives additions while borrowing the raw TBox and
then moves retained clauses into a right-sized allocation, avoiding a complete
TBox clone and an oversized collection buffer. Two source-profile gates use
lower worker counts for one large plain TBox and one medium SHI terminology.
These are allocation, handoff, and scheduling changes only; they do not alter
rules, ordering, redundancy, or the derived fixpoint.

The ten-ontology, 100-run paired panel `50466117` produced byte-identical
outputs, reduced mean wall from 0.1812 to 0.1774 seconds, and reduced mean peak
RSS from 30,223.6 to 29,292.2 KiB. Strict sweep `50466143` contains exactly 592
results, profiles, and checkpoints: 591 classifications succeed, ORE1194
remains the sole fail-closed error, and comparison with v0.2.18 finds zero
status, verdict, signature, consistency, or coverage differences. Across the
591 successful rows, mean wall falls from 4.14838 to 4.00461 seconds, median
wall from 0.2192 to 0.2159 seconds, mean peak RSS from 450.251 to 449.847 MiB,
and median peak RSS from 39.04 to 38.66 MiB. The complete serial release suite,
including the issue #3 pigeonhole regression, passes. Evidence is in
[`results/benchmarks/2026-08-14-move-augment-tbox/`](results/benchmarks/2026-08-14-move-augment-tbox/README.md).

## [0.2.18] – 2026-08-14

### Index large role-relevance slices

Large normalized clause sets now compute the role-relevance backward slice with
borrowed reverse head indexes and a work queue, activating each reachable clause
once instead of rescanning the complete clause set for every fixpoint wave.
Inputs below 10,000 clauses retain the established scan, avoiding index costs on
the corpus-median path. Focused panel `50453255` produced byte-identical clauses
and metadata on five large inputs and reduced the indexed phase by 5.9%.

Strict sweep `50456241` contains 592 terminal rows, 591 successful
classifications, ORE1194 as the sole fail-closed error, and zero behavioral
differences from v0.2.17. Mean wall falls from 4.2520 to 4.1484 seconds, median
wall from 0.2208 to 0.2192 seconds, mean peak RSS from 450.74 to 450.25 MiB, and
median peak RSS from 39.24 to 39.04 MiB. Evidence is in
[`results/benchmarks/2026-08-14-relevance-queue/`](results/benchmarks/2026-08-14-relevance-queue/README.md).

## [0.2.17] – 2026-08-13

### Borrow frontend-only output indexes

Declaration seeding now checks borrowed concept names in a hash set instead of
cloning them into a sorted set. IRI metadata construction iterates borrowed
registry pairs directly, avoiding a temporary key vector and repeated hash
lookups. These changes affect allocation and enumeration only: declaration
tautologies retain source order, and focused IBEX panel `50451358` confirms
byte-identical clause and metadata files on five large ontologies.

End-to-end panel `50451248` produced five identical classifications and reduced
summed wall from 183.23 to 180.16 seconds. Strict sweep `50451542` contains 592
terminal rows, 591 successful classifications, ORE1194 as the sole fail-closed
error, and zero status, consistency, signature, or coverage differences from
v0.2.16. In the directly comparable raw sweep rows, mean wall falls from 4.2748
to 4.2520 seconds, median wall from 0.2210 to 0.2208 seconds, mean peak RSS from
450.81 to 450.74 MiB, and median peak RSS from 39.47 to 39.24 MiB. Evidence is
in [`results/benchmarks/2026-08-13-frontend-borrowed-names/`](results/benchmarks/2026-08-13-frontend-borrowed-names/README.md).

## [0.2.16] – 2026-08-13

### Reuse the positive-EL ABox certificate taxonomy

Positive-EL ABox consistency checking already computes an exact EL completion.
When the selected automatic mechanism is the atomic exact-EL leaf, the
orchestrator now retains that result instead of discarding it and recomputing
the same terminology fixpoint. Every injected ABox rule is rooted at a fresh
internal concept, so it cannot add a subsumption whose subject is an original
named class. Other mechanisms, declines, and fallbacks are unchanged.

Paired panel `50448999` matched gold on eight large affected inputs and reduced
summed wall from 318.52 to 242.26 seconds. Strict sweep `50449122` contains
exactly 592 terminal rows: 591 successful classifications, ORE1194 as the sole
fail-closed error, and zero behavioral differences from v0.2.15. On directly
comparable sweep rows, mean wall falls from 4.5116 to 4.3177 seconds, median
wall from 0.2355 to 0.2320 seconds, and mean peak RSS from 481.72 to 481.30 MiB.
Evidence is in
[`results/benchmarks/2026-08-13-positive-el-reuse/`](results/benchmarks/2026-08-13-positive-el-reuse/README.md).

## [0.2.15] – 2026-08-13

### Eliminate the worker round trip for structured exact-EL leaves

Structured ontologies selected by the typed exact `elc` leaf now run the same
completion implementation in the orchestrator process. This avoids serializing
and reparsing worker taxonomies that can exceed 500 MiB. Exact-EL inputs whose
named-class count is at least 90% of their logical-axiom count retain the
subprocess boundary, releasing completion allocations before mapping very
large flat taxonomies. Other routes and every fallback remain unchanged.

Strict sweep `50447018` contains exactly 592 terminal results and reports 591
successful classifications, ORE1194 as the sole fail-closed error, and zero
behavioral regressions relative to v0.2.14. Mean wall falls from 4.5758 to
4.4699 seconds, median wall from 0.2469 to 0.2272 seconds, mean peak RSS from
499.38 to 451.22 MiB, and median peak RSS from 41.64 to 38.98 MiB. Evidence is
in [`results/benchmarks/2026-08-13-large-inproc-elc/`](results/benchmarks/2026-08-13-large-inproc-elc/README.md).

## [0.2.14] – 2026-08-13

### Use eight workers for one large role-chain/cardinality terminology

The automatic `production_all` route now uses eight workers instead of 16 for
very large TBox-only SRIQ inputs with substantial role-chain and qualified
cardinality structure. The source-profile predicate selects only ORE14817 in
the complete 592-profile audit. The route, reasoning procedures, fallback,
and answer contract remain unchanged.

Same-node route panel `50442525` reduced ORE14817 mean wall from 98.3611 to
97.6929 seconds and mean peak RSS from 5,209.64 to 5,206.61 MiB. The separate
automatic candidate gate `50442923` measured a smaller wall reduction from
98.7509 to 98.5933 seconds and a 0.79 MiB mean peak-RSS increase. Every run in
both panels exactly matched the retained full-IRI gold signature.

Strict sweep `50443229` contains exactly 592 terminal results and reports 591
successful classifications, ORE1194 as the sole fail-closed error, and zero
behavioral regressions relative to v0.2.13. Mean wall falls from 4.5871 to
4.5758 seconds, mean peak RSS from 499.60 to 499.38 MiB, and median wall from
0.2491 to 0.2469 seconds. Median peak RSS moves from 41.45 to 41.64 MiB; this
0.19 MiB run-to-run increase is reported without adjustment. Evidence is in
[`results/benchmarks/2026-08-13-14817-thread-panel/`](results/benchmarks/2026-08-13-14817-thread-panel/README.md).

## [0.2.13] – 2026-08-13

### Schedule the large disjunctive SHI bridge before production fallback

For very large source-certified disjunctive SHI terminologies, the automatic
`production_all` portfolio now runs its complete-answer-or-defer completion
bridge before allocating the exact CB fallback. Any bridge refusal, failure,
or explicit defer starts the unchanged production stack. The complete
592-profile audit selects only ORE3215.

Same-node job `50440878` ran three alternating v0.2.12/candidate pairs. All six
runs have the same gold-matching full-IRI signature. Mean wall falls from
162.0549 to 157.3747 seconds and mean process-tree peak memory falls from
8,499.09 to 6,330.62 MiB.

Strict sweep `50441548` contains exactly 592 results, profiles, and checkpoints
with no temporary outputs. It reports 591 successful classifications, ORE1194
as the sole fail-closed error, and zero behavioral regression relative to
v0.2.12. Mean peak RSS falls from 503.74 to 499.60 MiB and median peak RSS from
42.78 to 41.45 MiB. The independently scheduled mean wall moves from 4.5441 to
4.5871 seconds and median wall from 0.2461 to 0.2491 seconds; these
noise-sensitive movements are reported without adjustment. Evidence is in
[`results/benchmarks/2026-08-13-3215-sequential-bridge/`](results/benchmarks/2026-08-13-3215-sequential-bridge/README.md).

## [0.2.12] – 2026-08-13

### Schedule the large typed-ABox bridge before its exact fallback

For source-certified typed object ABoxes with at least 30,000 logical axioms
and 100,000 concept expressions, the `certified_nominals` portfolio now runs
its complete-answer-or-defer bridge before allocating the exact CB fallback.
Bridge refusal, failure, or explicit defer starts the unchanged fallback. The
592-profile audit selects only ORE10621, so smaller typed ABoxes retain their
concurrent low-latency race.

Same-node job `50438534` ran three alternating v0.2.11/candidate pairs. All six
runs have the same gold-matching full-IRI signature. Mean wall falls from
87.1031 to 86.6274 seconds and mean process-tree peak memory falls from
9,368.57 to 1,256.15 MiB.

The resumable strict sweep (`50438700`, `50439574`, and `50439604`) contains
exactly 592 results, profiles, and checkpoints with no temporary outputs. It
reports 591 successful classifications, ORE1194 as the sole fail-closed error,
and zero behavioral regression relative to v0.2.11. Mean peak RSS falls from
517.05 to 503.74 MiB and median wall falls from 0.2475 to 0.2461 seconds. The
independently scheduled mean wall moves from 4.5079 to 4.5441 seconds and
median RSS from 42.27 to 42.78 MiB; these noise-sensitive movements are
reported without adjustment. Evidence is in
[`results/benchmarks/2026-08-13-10621-sequential-bridge/`](results/benchmarks/2026-08-13-10621-sequential-bridge/README.md).

## [0.2.11] – 2026-08-13

### Project large independent atomic ABoxes before native HT conversion

The HT orchestrator now recognizes ABoxes containing at least 10,000 distinct
individuals when each has exactly one positive atomic class assertion and one
distinct proxy, with no role assertions, equality, inequality, negative facts,
or unsupported source content. OWL TBoxes are closed under disjoint unions, so
the ABox is consistent exactly when every asserted class is satisfiable and it
cannot alter named TBox subsumption. KM classifies the compact TBox and checks
all asserted classes against the completed taxonomy. Any failed structural or
semantic check defers to the unchanged complete production fallback.

ORE7914 contains 108,512 such roots. Source-bound verification job `50433101`
reduces automatic classification from about 46.8 seconds and 8.53 GiB to
8.5783 seconds and 1,514.75 MiB. The isolated `ht_bridge` arm takes 7.2858
seconds and 910.61 MiB. Both results are checkpointed exact matches with the
same full-IRI signature.

Strict sweep `50433149` contains exactly 592 results, profiles, and checkpoints
with no temporary files. Comparison with v0.2.10 reports zero semantic,
coverage, or route regressions: 591 classifications succeed and ORE1194 remains
the sole fail-closed error. Aggregate mean wall falls from 4.5884 to 4.5079
seconds and mean peak RSS from 528.14 to 517.05 MiB. Median wall is 0.2475
seconds and median peak RSS is 42.27 MiB. Evidence is in
[`results/benchmarks/2026-08-13-7914-regression/`](results/benchmarks/2026-08-13-7914-regression/README.md).

## [0.2.10] – 2026-08-13

### Certify a large near-EL terminology with a tiny identity ABox

The automatic router now recognizes very large near-EL terminologies carrying
at most 100 ABox axioms when the ABox consists only of positive class
assertions and explicit `DifferentIndividuals` statements. The source gate
excludes role assertions, complements, universals, cardinalities, datatypes,
functionality, imports, and rules. The normalized canonical-model certificate
remains authoritative; refusal, error, or resource failure reruns the complete
`production_all` route.

The complete 592-profile audit admits exactly ORE15803 beyond the existing
certified routes. Same-node job `50430173` reduces it from 33.2433 seconds and
2,589.44 MiB to 24.3237 seconds and 1,316.07 MiB, with the same gold-matching
signature. Automatic verification job `50430743` independently selects
`certified_el_production` and matches gold.

Clean sweep `50430792` contains exactly 592 result, profile, and checkpoint
rows with no temporary files. The strict v0.2.9 comparison reports exactly one
route change, 591 successful classifications, the unchanged fail-closed
ORE1194 error, and zero semantic or coverage regressions. Mean peak RSS falls
from 531.38 to 528.14 MiB. The independently scheduled wall mean and medians
move slightly upward to 4.5884 seconds, 0.2498 seconds, and 41.98 MiB despite
the controlled-route improvement; they are reported without adjustment.
Evidence is in
[`results/benchmarks/2026-08-13-small-identity-el-cert/`](results/benchmarks/2026-08-13-small-identity-el-cert/README.md).

## [0.2.9] – 2026-08-13

### Certify three large extended-EL terminologies before production fallback

The automatic router now sends large TBox-only, Horn-shaped source profiles
with limited inverse, symmetric, reflexive, or named-disjointness declarations
through plain normalization and the canonical-model certificate. Certificate
refusal or any worker/resource failure reruns `production_all`, retaining exact
coverage. The complete profile audit admits exactly ORE7246, ORE8737, and
ORE16744.

Same-node job `50428118` reduces their summed wall time by 54.9 seconds and
summed peak RSS by 19,049 MiB. Every successful arm has the same gold-matching
signature as `production_all`. Clean sweep `50428535` contains exactly 592
result/checkpoint/profile triples and no temporary files. The strict v0.2.8
comparison reports exactly three intended route changes, 591 successful
classifications, and zero semantic or coverage regressions.

The sweep records mean wall 4.5733 seconds, median wall 0.2490 seconds, mean
peak RSS 531.38 MiB, and median peak RSS 41.77 MiB. Mean peak RSS and both
medians are below the frozen Konclude measurements; mean wall remains above
Konclude. Evidence is in
[`results/benchmarks/2026-08-13-large-el-cert-panel/`](results/benchmarks/2026-08-13-large-el-cert-panel/README.md).

## [0.2.8] – 2026-08-13

### Route a large near-EL ABox through certified completion

The automatic router now recognizes the source profile of ORE6682 and first
uses plain EL normalization with the canonical-model repair certificate. The
gate excludes complements, universals, cardinalities, nominals, identity and
role risks, datatypes, imports, and rules. A certificate refusal, worker error,
or resource failure reruns the exact `production_all` route, so the source gate
changes scheduling rather than accepted semantics.

Same-node job `50424991` reduces ORE6682 from 29.1361 seconds and 7778.68 MiB
to 24.8344 seconds and 5082.77 MiB, improvements of 14.8% and 34.7%. Both arms
produce the same gold-matching signature. A complete profile audit proves that
ORE6682 is the only ontology admitted by the new gate.

Clean sweep `50425474` contains exactly 592 result/checkpoint/profile triples
and no temporary files. Its strict comparison with v0.2.7 reports 591
successful classifications, ORE1194 as the sole fail-closed error, exactly one
intended route change, and zero coverage or semantic regressions. Mean peak RSS
is 563.01 MiB, down from 567.35 MiB. The sweep's 4.6525-second wall mean,
0.2480-second wall median, and 42.36-MiB RSS median include small adverse
run-to-run movement despite unchanged execution paths for 591 inputs; the
controlled pair is the performance acceptance evidence. Evidence is in
[`results/benchmarks/2026-08-13-6682-elc-cert/`](results/benchmarks/2026-08-13-6682-elc-cert/README.md).

## [0.2.7] – 2026-08-13

### Extend exact EL routing and avoid eager completion on a large ABox

The automatic router now sends source-certified OWL EL terminologies with
named-class disjointness or class bottom to exact EL completion. It also sends
positive EL ABoxes only when the frontend's materialization certificate proves
that their consistency is decidable in the completed EL model and that
dropping the assertions preserves the public TBox taxonomy. Nominals,
identity constraints, bottom roles, imports, rules, datatypes, and unsupported
constructors continue to fail closed to the production portfolio. The
normalized EL worker independently validates its complete fragment before
publishing an answer.

For very large ABoxes without number restrictions, the router now tries the
complete production portfolio before the broad eager nominal-completion route.
This changes only ORE15846 and reduces its same-node run from 175.68 seconds
and 19,056 MiB to 10.18 seconds and 1,335 MiB with an identical 10,640-pair
full-IRI taxonomy.

Clean fixed-hardware sweep `50421935` contains 592 result/checkpoint pairs,
zero temporary files, 591 successful classifications, and ORE1194 as the sole
fail-closed error. The strict comparison with v0.2.6 finds exactly 99 intended
route changes, zero coverage regressions, and zero semantic regressions. The
issue #3 finite-nominal pigeonhole integration test and the complete locked
release suite pass on the release source.

On Intel Xeon Gold 6248 measurements, mean wall time improves from 5.1787 to
4.5777 seconds and mean peak RSS from 720.08 to 567.35 MiB. Median wall is
0.2475 seconds and median peak RSS is 42.20 MiB; their 0.0008-second and
0.18-MiB differences from v0.2.6 are measurement-neutral and both remain below
Konclude's frozen medians. Same-node paired panels for the 98 newly selected EL
routes improve all four panel metrics. Evidence is in
[`results/benchmarks/2026-08-05-positive-el-abox-routing/`](results/benchmarks/2026-08-05-positive-el-abox-routing/README.md),
[`results/benchmarks/2026-08-05-el-bottom-routing/`](results/benchmarks/2026-08-05-el-bottom-routing/README.md),
and
[`results/benchmarks/2026-08-05-15846-production-routing/`](results/benchmarks/2026-08-05-15846-production-routing/README.md).

## [0.2.6] – 2026-08-05

### Route source-certified EL terminologies directly to completion

The automatic router now sends large, TBox-only ontologies whose source axioms
use only supported OWL EL constructors directly to exact EL completion. These
ontologies previously entered `production_all`, whose polarity absorption and
duplicate frontend/CB work obscured the compact EL forms. The source predicate
excludes ABoxes, nominals, datatypes, imports, rules, inverse roles, Boolean
constructors, cardinalities, and every unsupported role axiom. The normalized
EL worker remains the final fragment checker and fails closed outside its
complete fragment.

The complete fixed-hardware sweep retains 591 successful classifications and
ORE1194 as the sole fail-closed error. All 592 status, verdict, signature,
consistency, taxonomy-count, discrepancy-count, and collision-sensitive
full-IRI results equal v0.2.5. The audit finds exactly 106 intended
`production_all` to `elc` route changes and no coverage or semantic regression.
The issue #3 finite-nominal pigeonhole regression and its non-clashing control
both pass on the release source.

On Intel Xeon Gold 6248 measurements, mean wall time improves from 5.7632 to
5.1787 seconds, median wall time from 0.2489 to 0.2467 seconds, mean peak RSS
from 780.74 to 720.08 MiB, and median peak RSS from 42.76 to 42.02 MiB. This is
a 10.14% mean-time and 7.77% mean-memory reduction. Evidence is in
[`results/benchmarks/2026-08-05-source-el-routing/`](results/benchmarks/2026-08-05-source-el-routing/README.md).

## [0.2.5] – 2026-08-05

### Detect equality clashes forced by finite nominal enumerations

The frontend now detects when equivalent finite `ObjectOneOf` definitions
force two named individuals to be equal while `DifferentIndividuals` requires
them to differ. This closes the soundness defect reported in
[GitHub issue #3](https://github.com/bio-ontology-research-group/kobayashi-marust/issues/3):
`C ≡ {a}`, `C ≡ {a,b}`, and `DifferentIndividuals(a,b)` now returns
`CONSISTENT 0`. The corresponding ontology without `DifferentIndividuals`
continues to return `CONSISTENT 1`.

The check derives only exact finite-set consequences before routing. It closes
named-class equivalence and explicit `SameIndividual` components, and reports a
clash only when one equivalent enumeration is a singleton and another contains
an explicitly different representative. It does not alter the CB calculus or
approximate general nominal satisfiability. The complete release suite passes
with 1,957 library tests, eight intentional ignores, every integration test,
and no failures.

## [0.2.4] – 2026-08-05

### Route certified flat taxonomies directly to EL completion

The automatic router now recognizes every nonempty source ontology whose
logical axioms consist only of flat named-class subclass edges. It sends this
source-certified family directly to exact EL completion instead of launching
the larger production portfolio. The EL worker independently validates the
normalized fragment and declines outside it, so the source predicate changes
scheduling rather than accepted semantics.

All 68 newly selected ontologies match their automatic candidate signatures
through EL completion. The complete source-bound automatic sweep retains 591
successful classifications and only ORE1194 failing closed. Its strict audit
finds exactly 68 `production_all` to `elc` route changes and zero differences
in status, verdict, signature, consistency, taxonomy counts, or discrepancy
counts across all 592 ontologies. The complete release suite passes with 1,955
library tests, eight intentional ignores, every integration test, and no
failures.

On Intel Xeon Gold 6248 measurements, the 591-row calibrated aggregate improves
mean wall from 5.8647 to 5.7851 seconds, median wall from 0.2756 to 0.2547
seconds, mean peak RSS from 801.66 to 781.08 MiB, and median peak RSS from 42.63
to 41.27 MiB. Evidence is in
[`results/benchmarks/2026-08-05-flat-taxonomy-el/`](results/benchmarks/2026-08-05-flat-taxonomy-el/README.md).

## [0.2.3] – 2026-08-05

### Merge canonical predecessor conclusions linearly (2026-08-05)

Staged local and arriving predecessor joins now linearly merge their already
canonical bodies and heads and construct the canonical result without sorting
it again. This changes representation work only; the premise products,
resolved literals, result antichains, scheduling, derivations, and fixpoint are
unchanged. The complete release suite and targeted predecessor oracle pass.
Source-bound build `50061158`, panel `50061724`, and complete sweep `50062331`
pass the strict 592-ontology gate with 591 successes and zero semantic or route
differences. Across 591 successes, mean wall improves 0.625% and mean peak RSS
improves 0.073%. Evidence is in
[`results/benchmarks/2026-08-05-canonical-pred-merge/`](results/benchmarks/2026-08-05-canonical-pred-merge/README.md).

### Compact predecessor-clause intern postings (2026-08-05)

The global predecessor-clause intern table now stores common one- and two-ID
hash buckets inline in KM's 16-byte `Posting` representation instead of giving
every bucket a 24-byte `Vec` header and heap allocation. Collision candidates
remain insertion ordered and exact-compared, so interning, derivations,
scheduling, and the saturation fixpoint are unchanged. The release library
suite passed 1,954 tests with eight ignored. Source-bound build `50058329`,
panel `50058474`, and full sweep `50058521` passed the strict 592-ontology gate
with 591 successes and zero semantic or route differences from `4254fbb`.
Across 591 successes, mean wall improved 0.49%, mean peak RSS improved 0.49%,
and median peak RSS improved 0.71%. Evidence is in
[`results/benchmarks/2026-08-05-compact-pred-intern-index/`](results/benchmarks/2026-08-05-compact-pred-intern-index/README.md).

### Remove the redundant predecessor-arrival vector (2026-08-05)

CB contexts no longer append every received, interned predecessor-clause id to
a write-only vector in addition to the authoritative deduplication set and
exact body indexes. This removes one allocation stream and four bytes per
received id without changing any reasoning read, ordering, scheduling, or
fixpoint. The release library suite passed 1,954 tests with eight ignored. A
source-isolated ORE9944 pair was output-identical, 2.77% faster, and saved about
143 MiB. Source-bound build `50057119`, panel `50057137`, and full sweep
`50057302` passed the strict 592-ontology gate with 591 successes and zero
status, verdict, signature, or selected-route differences from `b5c0158`.
Across 591 successes, mean peak RSS improved 0.22% and median peak improved
1.55%; independently scheduled mean wall was 1.58% higher. Evidence is in
[`results/benchmarks/2026-08-05-remove-neighbor-vector/`](results/benchmarks/2026-08-05-remove-neighbor-vector/README.md).

### Store head-index postings in compact thin vectors (2026-08-05)

CB contexts now store the common one- and two-clause head-index postings in a
16-byte inline representation, down from the 24-byte `SmallVec` value. Wider
postings spill to a one-allocation `ThinVec`; an inline tag lets hot reads choose
the representation without touching the allocation header. Insertion order,
removal order, index membership, rule scheduling, and the saturation fixpoint
are unchanged. The complete serial release suite passed with 1,962 library
tests and every integration, CLI, binary, and documentation test passing.
Source-bound IBEX build `50056177`, sentinel array `50056245`, and resumable
full array `50056291` passed the strict 592-ontology gate with 591 successes and
zero status, verdict, signature, or selected-route differences from `ed81ac6`.
Across the 591 successes, mean peak RSS fell from 817.18 to 808.03 MiB (1.12%).
The paired medians improved for both wall and memory, while independently
scheduled mean wall was 0.99% higher. Source-isolated ORE3215 and ORE9944 runs
were wall-neutral; the full sweep saved about 560–579 MiB on ORE7914, ORE9944,
and ORE10621 and 512 MiB on ORE7246. Evidence is in
[`results/benchmarks/2026-08-05-thin-head-postings/`](results/benchmarks/2026-08-05-thin-head-postings/README.md).

### Store central trigger sets as compact sorted vectors (2026-08-05)

CB central contexts now store successor trigger sets as sorted vectors instead
of per-element tree nodes. Binary-search insertion preserves the same unique,
deterministic predicate order, so context identity, rule derivation, scheduling,
and the saturation fixpoint are unchanged. The complete serial release suite
passed with 1,953 tests, eight ignored, and zero failures. Alternating ORE4669
pairs were byte-identical and reduced peak RSS by 64–65 MiB with neutral wall;
equal-progress 60-second ORE1194 diagnostics reduced peak RSS by 14.1%. IBEX
build `50052290` and full array `50052291` then passed the 592-ontology gate:
591 successes, the existing ORE1194 error, and zero status, verdict, signature,
or production-route differences. Across 591 paired successes, mean wall fell
0.32%, mean peak RSS fell 0.18%, and both medians improved. Evidence is in
[`results/benchmarks/2026-08-05-compact-trigger-sets/`](results/benchmarks/2026-08-05-compact-trigger-sets/README.md).

## [0.2.2] – 2026-08-05

### Avoid temporary blocking-key vectors (2026-08-05)

Incremental subset blocking now borrows a node's concept map separately from
the mutable posting-list fields and registers keys directly. This removes one
temporary key-vector allocation per unblocked node while inserting the same
keys in the same order. The complete release suite passed. Three alternating
source-bound ORE6934 pairs were byte-identical and improved mean wall from
115.577 to 112.680 seconds (2.51%); mean peak RSS fell 0.11%. A source-bound
592-ontology sweep then passed with 591 successes, the existing ORE1194 error,
and zero semantic or route differences from `07b8526`. Its independently
scheduled aggregate was measurement-neutral at +0.22% mean wall and -0.11%
mean peak RSS. Evidence and reproduction scripts are in
[`results/benchmarks/2026-08-05-i2-key-borrow/`](results/benchmarks/2026-08-05-i2-key-borrow/README.md).

### Truncate stale blocking posting-list tails (2026-08-05)

Incremental subset blocking now uses the posting lists' increasing node-ID
order to find a stale suffix with `partition_point` and discard it with
`truncate`, instead of scanning and copying the stable prefix with `retain`.
The retained blocker candidates and blocking result are unchanged. The complete
release suite passed. Three alternating source-bound ORE6934 pairs were
byte-identical and improved mean wall from 124.623 to 115.447 seconds (7.36%);
mean peak RSS was measurement-neutral at 3,347,608 versus 3,348,468 KiB. A
source-bound 592-ontology sweep then passed with 591 successes, the existing
ORE1194 error, and zero semantic or route differences from `02e6200`. Across
591 paired successes, mean wall improved 0.24%, median wall improved 0.87%, and
mean peak RSS improved 0.05%. Evidence and reproduction scripts are in
[`results/benchmarks/2026-08-05-i2-tail-truncate/`](results/benchmarks/2026-08-05-i2-tail-truncate/README.md).

### Store grouped taxonomy relations as compact IDs (2026-08-04)

The JSON-only classifier now stores taxonomy subjects and superclasses as
`u32` IDs into one lexicographically ordered full-IRI dictionary. This removes
per-relation shared-string handles and makes final row sorting integer-based
without changing reasoning, routing, aliases, duplicates, or output bytes. The
complete release suite passed with 1,951 library tests, eight ignored library
tests, and every integration and documentation test passing. Three alternating
source-bound ORE9674 pairs were byte-identical and improved mean wall from
42.200 to 41.547 seconds (1.55%); mean peak RSS was measurement-neutral at
2,227,104 versus 2,228,337 KiB. Source-bound arrays `50048480` and `50048481`
passed the full 592-ontology correctness gate with 591 successes, the existing
ORE1194 error, and zero semantic or route differences from `abe2759`. The
independently scheduled corpus sweep was 3.24% slower in mean wall and 0.36%
higher in mean peak RSS, so it does not provide corpus-wide performance
evidence; the alternating pair remains the source-isolated performance result.
Evidence and reproduction scripts are in
[`results/benchmarks/2026-08-04-compact-taxonomy-ids/`](results/benchmarks/2026-08-04-compact-taxonomy-ids/README.md).

### Intern repeated full IRIs in grouped JSON output (2026-08-04)

The JSON-only classifier now interns each mapped full IRI once as `Arc<str>`
and reuses it across grouped taxonomy rows. A precomputed ordered local-name
table avoids hashing long full IRIs in the per-pair loop. Public APIs, output
bytes, routing, and reasoning are unchanged. The complete release suite passed
with 1,951 library tests, eight ignored library tests, and every integration and
documentation test passing. On ORE9674, three alternating source-bound pairs
were byte-identical, improved mean wall from 42.597 to 42.180 seconds, and
reduced mean peak RSS from 2,882,256 to 2,231,001 KiB, a 636 MiB or 22.60%
reduction. Source-bound arrays `50037480` and `50037481` then passed the full
592-ontology gate with 591 successes, the existing ORE1194 error, and zero
semantic or route differences from `229ad77`. Across 591 paired successes,
mean wall improved 0.62%, median wall improved 1.11%, and mean peak RSS improved
0.44%. Evidence and reproduction scripts are in
[`results/benchmarks/2026-08-04-json-iri-intern/`](results/benchmarks/2026-08-04-json-iri-intern/README.md).

### Serialize grouped taxonomy rows directly (2026-08-04)

The normal JSON CLI now retains mapped full-IRI taxonomy rows in grouped form
through serialization instead of flattening them into one owned subject string
per pair. The public `Classification` API, `--lines`, explanation, and mirror
paths retain their flat representation. This changes neither reasoning nor JSON
bytes. The complete release suite passed. On ORE9674, three alternating
source-bound pairs against `c3c3d24` were byte-identical, improved mean wall
from 42.817 to 42.360 seconds, and reduced mean peak RSS from 4,016,389 to
2,882,389 KiB (minus 1.081 GiB, 28.23%). Source-bound production arrays
`50033013` and `50033014` then passed the complete 592-ontology gate: 591
successful rows, the existing ORE1194 error, and zero semantic or route
differences from `c3c3d24`. The strict audit covered every terminal,
checkpoint, profile, completion log, binary identity, route trace, expected
failure capture, and collision-sensitive full-IRI fingerprint. Across 591
paired successes, mean peak RSS fell from 830.96 to 823.95 MiB and median peak
from 43.07 to 41.79 MiB. Corpus wall time was scheduler-noisy at +0.44% mean
and -0.12% median, so the alternating pair remains the source-isolated speed
evidence.
Evidence and reproduction scripts are in
[`results/benchmarks/2026-08-04-grouped-json-output/`](results/benchmarks/2026-08-04-grouped-json-output/README.md).

### Reject QO residue and propagation-layout probes for ORE 1194 (2026-08-03)

The optimized shared-filler QO/KPSet precompute converged in 185.67 seconds but
left all 70,231 queries affected by 483,811 parked disjunction instances and
38,521 insufficient nodes. The diagnostic residue bypass could not build even
one supported completion. Predecessor-local successors retained about 5.5
million events near the production cutoff. Dense node batches were neutral;
consequence-indexed Roaring batches reduced peak memory from 6.69 GiB to 4.71
GiB but regressed closure scheduling. All runs emitted zero bytes, no candidate
is enabled, and coverage remains 591/592. Evidence is in
[`results/benchmarks/2026-08-03-1194-qo-residue-probes/`](results/benchmarks/2026-08-03-1194-qo-residue-probes/README.md).

### Reject virtual inverse upper-model closure for ORE 1194 (2026-08-03)

A fail-closed prototype represented 12 reciprocal inverse-bridge directions
only in the certificate upper model, leaving the sound EL lower bound
unchanged. In-place initial joins and LIFO repair scheduling reduced the
240-second peak from 17.35 GiB to 7.39 GiB, but neither that run nor a
600-second diagnostic completed. A progress profile showed the upper queue
still growing after 70 million items, to 18.4 million pending entries. Fresh
concurrent lower/upper saturation and dormant virtual-event suppression also
failed the production gate. Every run emitted zero bytes. The prototype is not
enabled, and automatic coverage remains 591/592. Evidence and exact binary
hashes are in
[`results/benchmarks/2026-08-03-1194-virtual-upper-closure/`](results/benchmarks/2026-08-03-1194-virtual-upper-closure/README.md).

### Reject eager physical inverse-bridge batching for ORE 1194 (2026-08-03)

An exact certified-EL upper-model prototype batched every forced inverse-role
bridge before one re-closure. It added 22,853,033 required edges. Replacing its
temporary candidate hash set with a flat batch moved closure startup from about
177 seconds to 139 seconds, while the upper-model compression reduced peak RSS
to 17,120,788 KiB. The production-bounded run still timed out at 240.74 seconds
with zero output. No production route changed and coverage remains 591/592.
Evidence and the soundness boundary are documented in
[`results/benchmarks/2026-08-03-1194-eager-bridge-batching/`](results/benchmarks/2026-08-03-1194-eager-bridge-batching/README.md).

All notable changes to the kobayashi-marust reasoner. Newest first.

> **How each once-failing ontology was solved — diagnosis, mechanism,
> validation — is documented per-ontology in
> [`docs/SOLVED-ONTOLOGIES.md`](docs/SOLVED-ONTOLOGIES.md).** Keep that file
> updated whenever an ontology flips to solved.

### Consume fixed hypertableau output pairs (2026-08-05)

The automatic classifier now deserializes hypertableau taxonomy relations as
fixed two-string arrays and moves their strings directly into grouped output
rows. This rejects malformed variable-length worker rows and removes two string
clones per relation without changing reasoning, routing, or output bytes. The
complete release suite passed. Three alternating source-bound ORE3215 pairs
were byte-identical and improved mean wall from 150.160 to 148.000 seconds
(1.44%); mean peak RSS was measurement-neutral. Evidence is in
[`results/benchmarks/2026-08-04-ht-output-handoff/`](results/benchmarks/2026-08-04-ht-output-handoff/README.md).

### Reuse serial hypertableau models and counterexamples (2026-08-05)

The default `km classify` route now enables two existing sound serial
hypertableau optimizations. A completed model can witness satisfiability for
every named concept in its node labels, avoiding redundant phase-1 tests. A
satisfiable `A ∧ ¬B` model also eliminates every concept absent from its root
label as a candidate subsumer of `A`, avoiding redundant phase-2 tests. The
parallel classifier already performs model-based pruning internally. No
hypertableau rule, routing decision, or output construction changed.

The complete release suite passed. A source-bound 70-ontology IBEX panel
covered every currently successful serial-hypertableau-related automatic
route. Its strict audit verified 70 exact output pairs, 140 zero exits, all
indices and completion markers, and every timing and digest receipt. Total wall
fell from 675.60 to 571.84 seconds (15.36%), while mean peak RSS fell 0.80%.
ORE7499 improved 59.73%, ORE10702 improved 55.67%, and ORE6934 improved
31.11%. Source-bound production arrays `50048482` and `50048483` subsequently
passed the complete 592-ontology gate with 591 successes, the existing ORE1194
error, and zero semantic or route differences from `9ee269e`. Across 591 paired
successes, mean wall improved 3.46% and mean peak RSS improved 0.41%. Evidence
is in
[`results/benchmarks/2026-08-05-ht-model-reuse/`](results/benchmarks/2026-08-05-ht-model-reuse/README.md).

### Stream final classification JSON directly to stdout (2026-08-04)

The `km classify` CLI now writes the final classification through its existing
Python-compatible JSON formatter directly to locked stdout instead of first
materialising a second whole-output byte vector. A bounded output buffer keeps
serde's small writes efficient for files and pipes. The allocation-returning API
delegates to the same writer, and a regression test pins byte identity. This is
an output-representation change only; reasoning and the fixpoint are unchanged.
The complete release suite passes with 1,949 library tests, eight ignored
library tests, and every integration suite passing.

On ORE 9674, three source-bound alternating IBEX pairs reduced mean wall from
46.490 to 44.733 seconds (3.78%) and mean peak RSS from 5,479,932 to 4,016,495
KiB, a 1.396 GiB (26.7%) reduction. All six output streams were byte-identical.
Evidence is in
[`results/benchmarks/2026-08-04-streamed-output/`](results/benchmarks/2026-08-04-streamed-output/README.md).

A second file-backed alternating benchmark of the buffered implementation
reduced mean wall from 44.213 to 43.593 seconds (1.40%) and again removed 1.396
GiB of peak RSS with byte-identical output. Source-bound build `50029950`,
sanity job `50029951`, and exclusive arrays `50029952` and `50029953` then
completed the production gate. The strict audit passed all 592 terminals,
checkpoints, profiles, logs, binary identities, route traces, and
collision-sensitive fingerprints. Coverage remained 591/592 with zero semantic
differences from `6600efe`. Across 591 paired successes, mean wall improved
from 5.9744 to 5.8301 seconds, median wall from 0.2703 to 0.2526 seconds, mean
peak RSS from 845.61 to 830.96 MiB, and median peak from 45.00 to 43.07 MiB.

### Order dense final taxonomies by grouped full-IRI rows (2026-08-04)

The automatic classifier now sorts mapped superclass IRIs within each mapped
full-subject-IRI row and flattens rows in subject order, instead of globally
sorting every materialised pair. This is exactly the same lexicographic output
order, including aliases and duplicate pairs, and does not alter reasoning or
the saturation fixpoint. The complete release suite passes with 1,948 library
tests, eight ignored library tests, and every integration suite passing.

On ORE 9674's 14,809,043-pair taxonomy, three source-bound alternating IBEX
pairs reduced mean wall from 51.697 to 46.600 seconds (9.86%). Mean peak RSS
increased by 26,188 KiB (0.48%), and all six output streams were byte-identical.
Evidence is in
[`results/benchmarks/2026-08-04-grouped-output-sort/`](results/benchmarks/2026-08-04-grouped-output-sort/README.md).

Source-bound build `50024711`, sanity job `50024712`, and exclusive IBEX array
`50024713` completed the production gate. All 592 ontology rows, profiles,
checkpoints, logs, binary identities, and collision-sensitive fingerprints
passed the terminal audit. Coverage remained 591/592, and comparison with
`df5bb5b` found zero semantic or route differences. Across the 591 paired
successes, mean wall improved from 6.1991 to 5.9744 seconds (3.63%), median wall
from 0.2766 to 0.2703 seconds, and mean peak moved from 844.44 to 845.61 MiB.
The alternating ORE 9674 pairs remain the source-isolated performance evidence.

### Use fast deterministic hashing for exact-checked content interning (2026-08-04)

Context-core and Pred-clause interning now use KM's deterministic FxHash-style
hasher instead of constructing SipHash for every content probe. Hashes only
select candidate buckets; exact structural comparison still resolves every
lookup and collision, so the calculus and fixpoint are unchanged. The complete
release suite passes with 1,955 library tests, eight ignored library tests, and
every integration suite passing. On the completing 4669 base workload, three
interleaved pairs improved mean wall from 22.463 to 21.463 seconds (4.45%) with
byte-identical output and effectively unchanged peak RSS. A matched 60-second
ORE 1194 check preserved its zero-output timeout and memory profile. Evidence
is in
[`results/benchmarks/2026-08-04-content-fxhash/`](results/benchmarks/2026-08-04-content-fxhash/README.md).

Source-bound exclusive IBEX array `50014326` completed all 592 production
tasks: 591 succeeded and ORE 1194 remained the sole error. The strict terminal
audit found zero semantic differences from `a4eb829`, complete checkpoint and
route evidence, and valid collision-safe fingerprints. Across paired successes,
median wall improved from 0.2794 to 0.2766 seconds and mean peak memory moved
from 844.50 to 844.44 MiB. Mean wall was 1.1% slower overall, while the affected
`nominals` and `cb_plain16` routes improved by 2.82% and 2.54%; the 5%-trimmed
corpus mean delta was effectively neutral at +0.0021 seconds.

### Use fast deterministic hashing in the CB saturation state (2026-08-04)

The CB engine now uses the same FxHash-style multiply-rotate hasher as the EL
completion engine for its trusted, internally generated integer, predicate,
term, and tuple keys. This changes only hash-table representation and traversal
order. Exact membership, subsumption, rule, and redundancy checks are unchanged.
The complete release suite passes with 1,947 library tests, eight ignored tests,
and every integration suite passing.

On the completing 4669 base workload, output remained byte-identical while wall
time fell from 30.99 to 22.27 seconds and peak RSS from 1,871,776 to 1,842,588
KiB. At the identical 6,000,000-message ORE 1194 checkpoint, cumulative Pred
arrival fell from 35.68 to 27.69 seconds and clause insertion from 24.53 to
18.72 seconds. Source-bound IBEX array `49995966` verified 591/592 successful
automatic classifications with zero semantic differences from `1ef8ee1`.
Across the 591 paired successes, mean wall fell from 6.3539 to 6.1310 seconds,
median wall moved from 0.2738 to 0.2794 seconds, mean peak RSS moved from 844.18
to 844.50 MiB, and median peak RSS fell from 45.23 to 44.19 MiB. Evidence is in
[`results/benchmarks/2026-08-04-cb-fxhash/`](results/benchmarks/2026-08-04-cb-fxhash/README.md).

### Batch QO propagation and index exact edge membership (2026-08-02)

The QO/KPSet specialist can now union repeated ordinary NF4 conclusions per
target and drain wave, and use a hash index for exact edge membership while
retaining the original adjacency vectors and KPSet inverse checks. Both options
are enabled in the automatic QO arm. All 90 hypertableau, 24 routing, and 110
orchestration tests pass. A same-binary IBEX gate preserved exact signatures on
7581 and 15098; 7581 improved from 21.1071 to 20.2926 seconds. The optimized
1194 precompute now reaches its deterministic fixpoint in 185.627 seconds and
then correctly defers on the unresolved cardinality/disjunction residue with
zero output. Existing filler `CARDMERGE` performs zero merges on the non-filler
Eq bindings, while the separate-filler combination still times out. Source-bound
full sweep `49886711` verifies 591 successful rows and zero semantic differences
from `02a563f`; coverage remains 591/592. Evidence is in
[`results/benchmarks/2026-08-02-1194-inverse-bridge-orientation/`](results/benchmarks/2026-08-02-1194-inverse-bridge-orientation/README.md#8-batched-propagation-and-exact-edge-membership).

### Profile ORE 1194 backward-subsumption mutation scans (2026-08-02)

At the final 600,000-iteration checkpoint, rarest-posting selection and exact
subsumption together consumed only 0.60 seconds. Discovering removed worked
clauses by rescanning `worked_off` consumed 28.07 seconds, and retaining the
surviving `worked_off`/`todo` entries consumed another 30.08 seconds. These
repeated whole-list scans account for 58.16 seconds, 77% of the measured
backward-subsumption phase, and select stable slots plus generation-tagged
pending entries as the next exact representation change. Evidence is in
[`results/benchmarks/2026-08-02-1194-backsub-mutation-profile/`](results/benchmarks/2026-08-02-1194-backsub-mutation-profile/README.md).

### Reject allocation-free backward-subsumption buffers (2026-08-02)

Candidate `3339f41` directly scans the rarest active-head posting and stores
exact removals in an inline `SmallVec`, eliminating the candidate `Vec` and
removal `HashSet` allocations on every backward-subsumption call. It passed the
complete release suite and preserved exact completion of 8480 and 15846, but
1194 remained unchanged: 31.8489 seconds on the automatic attempt and 234.5986
seconds on the exact 2-thread/225-second route. It is not integrated, and the
failed gate does not justify a full sweep. Evidence is in
[`results/benchmarks/2026-08-02-1194-backsub-smallvec/`](results/benchmarks/2026-08-02-1194-backsub-smallvec/README.md).

### Profile backward-subsumption call shapes on ORE 1194 (2026-08-02)

At the final 600,000-iteration checkpoint, all 3,650,589
backward-subsumption calls had empty bodies and non-empty heads. They visited
21,716,431 candidates, performed 976,023 exact checks, removed 776,522 clauses,
and consumed 75.27 seconds. A body posting cannot help this workload; the
rarest head posting averages only 5.95 candidates and the removal set averages
0.21 clauses, identifying per-call temporary allocation as the next exact
optimization target. The instrumentation-only run failed closed and leaves
coverage at 591/592. Evidence is in
[`results/benchmarks/2026-08-02-1194-backsub-shapes/`](results/benchmarks/2026-08-02-1194-backsub-shapes/README.md).

### Reject active body postings after exact split gates (2026-08-02)

Separate forward-only and backward-only trie gates identify generic superset
traversal as the earlier candidate's catastrophic path; subset traversal
preserves completion but adds no 1194 benefit. A follow-up exact rarest-posting
candidate indexes active body atoms so empty-head strengthening clauses need
not scan every active clause. It passes the complete release suite and keeps
8480 and 15846 exact, but 1194 remains unchanged at both automatic and extended
caps while both sentinels slow slightly. It is not integrated. Evidence is in
[`results/benchmarks/2026-08-02-1194-active-body-posting/`](results/benchmarks/2026-08-02-1194-active-body-posting/README.md)
and the split-gate section of the active-trie report.

### Reject unconditional active-clause redundancy tries (2026-08-02)

Candidate `8121fec` passed the full release suite and exact randomized
subsumption differentials, but failed the production gates. ORE 1194 still
failed closed at both the automatic and 2-thread/225-second caps. Its apparent
RSS reduction represented less progress: the instrumented trie build never
reached the first 200,000-iteration context checkpoint. A 19-ontology sentinel
array then regressed 15846 from a 197.85-second exact completion to timeout and
8480 from a 19.90-second exact completion to a 190.79-second error. All 17
completed sentinel signatures remained exact. The candidate is not integrated;
forward-subset and backward-superset traversals are being gated separately.
Evidence is in
[`results/benchmarks/2026-08-02-1194-active-redundancy-trie/`](results/benchmarks/2026-08-02-1194-active-redundancy-trie/README.md).

### Profile exact active-clause redundancy on ORE 1194 (2026-08-02)

An instrumentation-only source-bound IBEX run splits `add_clause` into exact
lookup, forward-subsumption, backward-subsumption, and index phases. At 600,000
iterations in the dominant context, backward subsumption consumed 75.41
seconds and forward subsumption 47.84 seconds, versus 25.24 seconds for Hyper
generation and 3.90 seconds for arena lookup. The checkpointed automatic run
failed closed after 234.3947 seconds at 12,902.94 MiB. This evidence selects
cross-call exact subset/superset indexing as the next optimization target; it
does not change the standing 591/592 result. Full identities and measurements
are in
[`results/benchmarks/2026-08-02-1194-add-clause-profile/`](results/benchmarks/2026-08-02-1194-add-clause-profile/README.md).

### Share the seeded closure as a base layer under a per-context delta (2026-08-02)

Context clause *content* has been shared since `cc_arena` became content
interned, but the per-context bookkeeping *about* that content was still one
private copy per context. On ORE 1194 the CB engine holds about 189,541 distinct
interned clauses across roughly 6.3 million context slots — each distinct clause
is filed into about 33 contexts — and almost all of that duplication is the one
thing every context is seeded with: the context-independent closure. Every
successor context (and every query root, under the root ordering) received that
closure through `seed_worked_off`, which pushed the same ids into its own
`worked_off` list, `clause_keys` set, six head/role/term postings, active
redundancy index, Join indexes and Pred/Succ pools. An earlier attempt to attack
this by caching the per-clause *index key derivation* was exact but bought
nothing (no speedup, +8.5 MiB) and was reverted: the cost is the storage and the
scanning, not the derivation.

The clause store is now split into two layers of one new type, `ClauseLayer`
(the worked-off list, the key set, every posting index and both propagation
pools). A context reads a shared, reference-counted **base** layer followed by
its own **delta** layer; a context-local back-subsumption of a base clause is
recorded in a `base_removed` mask instead of editing the shared base. The base
for each ordering domain is built once (`Engine::shared_base`) and attached to
every closure-seeded context, so the closure's postings exist once instead of
once per context. `KM_NO_BASE_LAYER` restores the flat representation for A/B
measurement.

Exactness. Every read goes through a `PostingView`, which denotes
`base \ removed` followed by `delta`. That is the same *sequence* the flat
representation held, not merely the same set:

* The base is installed at context creation, before any delta clause exists, and
  every posting is appended to in insertion order — so in the flat store all
  base ids already preceded all delta ids in every posting.
* Removing an id from a flat posting leaves the survivors in their original
  relative order, which is exactly what filtering the base segment reproduces.
* Masking an id out of *all* base postings at once is faithful because
  `unindex_clause`/`unindex_active_clause` remove it from exactly the postings
  `index_clause`/`index_active_clause` inserted it into, and from no others.
* The mask is never cleared: a clause derived again after removal re-enters via
  the delta, i.e. at the end of every posting — precisely where the flat store
  re-appended it.
* The base layer is built by replaying the *same* `ClauseLayer::seed` routine
  over the *same* closure ids in closure order that `seed_worked_off` used, so
  it is bit-for-bit the state the per-context loop produced; a fresh context's
  delta and mask are empty, so attaching the base is observationally identical
  to running that loop.
* Membership (`has_clause`), sizes, the Pred/Succ pools and every pool index
  that crosses a context boundary in a `Msg::Pred` are all computed over
  base-then-delta, so semi-naive high-water marks and `pushed_pred` indices keep
  denoting the same clauses. Pool entries stay unmasked, as before, because a
  back-subsumed clause is still context-entailed; consumers re-check
  `has_clause` exactly where they used to re-check `clause_keys`.
* `back_subsume`'s rarest-posting selection returns early on an empty view where
  it used to return early on an absent key. A flat posting is never empty
  (emptied keys are pruned), and a fully masked base view is exactly the state
  that pruning produced, so the removal set is unchanged.
* The shared closure is still computed before the successor context is created,
  keeping the throwaway closure context's id — and therefore every context id —
  identical to the flat engine's.

Two deliberate, output-neutral relaxations are documented in the code: the Join
fast-path guard `join_indexes_empty` ignores the mask (it can only *disable* a
skip, after which the Join loops find no candidate), and the Join key
enumeration walks base keys then delta keys rather than one map — the flat code
iterated a `std::collections::HashMap` whose order is already unspecified, so
only the key set was ever observable, and that is preserved exactly.

`KM_SEED_FROM_SUBSET` inherits the source context's base *and* its mask and then
replays only the source's delta, which reproduces the source's live worked-off
sequence verbatim.

Tests. `base_layer_matches_flat_representation` drives a layered and a fully
materialised context through the same script of forward-subsumption probes,
context-local removals, worked-off insertions, pending insertions and pending
deactivations, comparing the worked-off sequence, key set and size, every
posting of every index as a sequence, both pools, `todo`, and the
`fwd_subsumed`/`back_subsume` outcomes after every step; a deterministic tail
forces each remaining path (including a base-layer removal and the re-derivation
of a masked base clause) so the comparison cannot pass vacuously.
`a_masked_base_clause_reenters_at_the_end_like_the_flat_representation` pins the
re-entry position, `inheriting_a_base_and_mask_reproduces_the_flat_seed_sequence`
pins the `KM_SEED_FROM_SUBSET` path, and
`shared_base_classification_matches_flat` classifies the same ontology with the
base layer on and off and requires identical subsumptions, consistency verdict,
context count and retained clause count.

This is a storage/scanning representation change with no calculus-rule change,
so no Lean re-certification applies. Not yet built or benchmarked.

### Narrow qualified-cardinality Hyper joins exactly (2026-08-02)

The generic Hyper join built each ontology-body posting independently. For a
qualified at-most clause, filler postings and role-edge postings therefore
formed million-way Cartesian products even though only terms present in both
could reach a unifiable leaf. Hyper now applies an exact semijoin reduction on
shared free terms and uses an exact-predicate index once the current
substitution determines a body atom. Removed candidates cannot occur in any
unifiable tuple; retained lists stay in their original order and every emitted
branch still passes through the existing unifier. This changes enumeration
cost, not the calculus, so no Lean re-certification applies.

Differential tests compare complete ordered resolvent traces against a frozen
generic join over the ORE 1194 cardinality shape and randomized ordinary and
grounded substitutions. Separate guards cover empty joins, witness selection,
and full-saturation output. The combined release suite passes 1,950 library
tests and every integration suite. On ORE 1194, representative posting products
fell from 4.32 million to 145,200 and from 2.78 million to 80,000. The exact
single-threaded no-query gate still timed out at 245.17 seconds, so this does not
change the standing 591/592 coverage result. Evidence is in
[`results/benchmarks/2026-08-02-1194-hyper-narrowing/`](results/benchmarks/2026-08-02-1194-hyper-narrowing/README.md).

### Guide certificate repair with qualified-cardinality shapes (2026-08-02)

The certified-EL repair search now reads two shapes off the compiled residual
and uses them to order its choices. The certificate model keeps one canonical
node per skolem function, shared across every source element, so a `≥n`
distinctness clause `G(x) ∧ f_i(x) ≈ f_j(x) → ⊥` pins two fixed nodes apart for
the whole model. Identifying them to satisfy an at-most bound at one node makes
that clause false at every node carrying the guard. A qualified at-most bound
`G(x) ∧ ⋀_{i≤n}(C(y_i) ∧ R(x,y_i)) → ⋁_{i<j} y_i ≈ y_j` is the other half: both
recognisers match on variable wiring alone and never on concept or role
spelling.

An exhaustive disjoint partition between a `≤n R.C` definer and a `≥m R.C`
definer with `m > n` is where this bites. Every element takes a side, and the
at-most side at a node already carrying `m` pairwise pinned successors is
locally unsatisfiable. The search now does two things with that. When a
violated at-most head offers several identifications, it picks one the model
may actually make, preferring one that does not clash with a disjointness
axiom, instead of taking the first pair the clause enumerates. When a covering
disjunction offers a side that a qualified at-most bound makes locally
unsatisfiable at that node, that side leaves the preferred choice tier. Neither
is a ban: if nothing else survives, the choice is still taken and the model is
still validated in full. A violated at-most bound whose every identification is
pinned apart is charged to the choice that made the node over-full, at the point
of detection, rather than surfacing as a `⊥` several closure rounds later where
the blame no longer reaches it.

Nothing here discharges a residual clause. `cert_round`'s checking, the EL
completion rules and the acceptance criterion are untouched, so a pass model is
still accepted only when a full cycle finds every residual clause satisfied
under the quotient, every base-satisfiable named witness survives, and the
per-subject intersection criterion holds. The choice tier that consults the
guidance sits above the three tiers that were already there and coincides with
the first of them whenever the residual holds no cardinality partition, so an
ontology without one searches exactly as before. A pair wrongly called pinned
costs the search a merge it could have made, and the model it builds instead is
still validated in full; a pinned pair the recogniser misses leaves the search
as it was. No calculus rule changed and no Lean re-certification is needed: the
Lean formalisation covers the CB disjunctive context calculus, which is not
involved here.

The certificate index reuse from `e05b35c` is preserved, including its
enumeration-order invariant: the guidance is consulted after the violations are
enumerated, never during the join.

Nine focused tests cover this. Three exercise the whole certificate: a
cardinality partition over more subjects than the restart budget that certifies
only when the locally unsatisfiable side is avoided, an over-refusal guard
requiring identifications that are legal to still be made, and a fail-closed
case where both sides are impossible and the certificate has to decline rather
than answer. Six pin the recognisers and the guidance directly, against
near-miss shapes for both recognisers, an unguarded bound, a bound whose second
guard does not hold, successors that fail the filler or the role, and the
union-find quotient folding two pinned successors together. Neutralising the
guidance turns the partition test from a pass into an outright decline, so it
measures the mechanism rather than the ontology. The release suite passes 1,958
tests with zero failures and eight intentional ignores.

This is the cardinality half of the 2026-08-01 experiment recorded in
[`results/benchmarks/2026-08-01-1194-cardinality-partition-repair/`](results/benchmarks/2026-08-01-1194-cardinality-partition-repair/README.md),
where it took the 1194 repair from seven conflict-driven restarts, each
re-deriving the same nine rounds, to zero conflicts and zero restarts in one
monotone pass. It does not close 1194, whose remaining cost is 96.2 seconds of
base saturation plus one EL re-closure after mirroring an inverse role bridge.
The rotated residual scan measured alongside it is not part of this change. The
automatic route for 1194 is `nominals`, which sets `KM_NO_ELC=1`, so no
certificate worker runs there and the production row is unchanged.
### Exact inverse-bridge preprocessing, and why orienting a pair is unsound (2026-08-02)

`InverseObjectProperties(R S)` clausifies to the bridge pair `R(x,y) → S(y,x)`
and `S(x,y) → R(y,x)`. Neither is an EL normal form, so both reach the residual
and the certificate has to satisfy them over the canonical model, which means
mirroring a role graph that on ore_ont_1194 holds 44.2M edges. The standing plan
was to remove them by substitution: the two bridges pin `S = R⁻`, so rewrite
every `S(a,b)` as `R(b,a)`, drop the bridges as tautologies, and teach the
completion the reverse-oriented NF3/NF4 the rewrite produces.

**The reverse-oriented half of that plan is unsound, and the countermodel is now
a test.** Take `C ⊑ ∃R.D`, `C ⊑ A`, `S = R⁻`, `∃S.A ⊑ E`. The substitution turns
the last axiom into `R(y,x) ∧ A(y) → E(x)`, which fires along the edge
`C —R→ D` and derives `D ⊑ E`. That subsumption fails in the one-element
interpretation `Δ = {d}`, `D = {d}`, everything else empty. The cause is
structural rather than a slip in any particular rewrite: a node here denotes
*the* generic instance of a concept name, so every `X ⊑ ∃R.D` shares the single
successor node `D`, and a reverse-oriented rule concludes at that shared
successor from one of its predecessors. It asserts of all `D` instances what
holds only of the `D` instances that have an `A` predecessor. Soundness needs
the successor to carry `∃R⁻.A` as part of its identity, which is a context
(concept-set) calculus, so it is the CB engine and not this completion.
`reverse_oriented_inverse_nf4_would_be_unsound` pins it.

What is left is exact and is now applied before `to_nf`, on the certificate
routes only (cert-off classify declines on its first residual anyway, and
leaving that path alone keeps `is_pure_el_shape`, the router's screen, in step
with what cert-off `classify` accepts):

- **Vacuous-role elimination.** A role occurring in no clause head can be given
  the empty extension, which satisfies every clause mentioning it only in a
  body. All such clauses are deleted, to a fixpoint, since deleting one can
  leave a further role head-free. `O` and the pruned `O'` have the same
  concept-name entailments and are equiconsistent. No rule can add such an edge
  either, so the canonical model already satisfies each deleted clause.
- **Mutual-inverse substitution**, admitted only when it leaves no completion
  rule reversed: no clause mentioning the eliminated role, apart from the two
  bridges, may be orientation-sensitive (a role atom in a head, or a single-role
  body under a single concept head). Residual clauses are exempt because a
  swapped role atom there is evaluated against the finished model, not fired.
  An ambiguous inverse graph, a one-way inclusion `R ⊑ S⁻`, symmetry and
  reflexivity are all refused.

On ore_ont_1194 the prep removes 52 clauses across 25 head-free roles. Fifteen
of them were residual, so the certificate now checks 202 clauses against the
model instead of 217, and it correctly refuses all six mutual pairs
(`BFO_0000050`/`BFO_0000051`,
`BSPO_0000098`/`BSPO_0000102`, `BSPO_0000124`/`BSPO_0000125`,
`RO_0002202`/`RO_0002203`, `distally_connected_to`/`proximally_connected_to`,
`surrounded_by__uberon`/`surrounds`): every one of those roles carries both NF3
and NF4 axioms in both directions, so no orientation is forward-only. The two
one-way bridges (`has_distal_part`, `has_proximal_part`) go, because those roles
occur in no head.

1194 stays open. Under 240 s / 24 GiB the certified-EL route still times out
with no output, and the repair search is spent on covering disjunctions and the
conflict restarts they drive, never on a bridge. A same-binary A/B over
`KM_ELC_NO_BRIDGE_PREP=1`, both runs at 240 s:

| | residual clauses | peak RSS | conflict restarts reached |
| --- | --- | --- | --- |
| prep off | 217 | 6.73 GiB | 5 |
| prep on | 202 | 6.27 GiB | 15 |

Each residual clause costs a join over a 499,904-node, 44.2M-edge model per
repair round, so dropping 15 of them lets the same wall budget carry the search
three times as far. It runs out of budget in the same place.

Evidence: `results/benchmarks/2026-08-02-1194-inverse-bridge-orientation/`.
### Screen CB subsumption with a dense signature, and stage local Pred (2026-08-02)

Two hot-path changes in the CB engine, both scheduling/redundancy-filtering
only, plus the diagnostics that located them. Full measurements in
[`results/benchmarks/2026-08-02-1194-cb-subsumption-screen/`](results/benchmarks/2026-08-02-1194-cb-subsumption-screen/README.md).

**Where the time was.** Profiling ore_ont_1194 with the new `add_clause` phase
split showed forward subsumption taking 65.4 s of the 70.3 s spent inserting
clauses, and 79 % of the whole inter-context message fixpoint. The scan was
memory-bound rather than arithmetic-bound: each posting-list candidate was
dereferenced into the clause arena, chasing a `ContextClause`'s two heap
vectors, only to fail a length comparison.

**`ClauseSig` screen.** Both subsumption directions ask two set inclusions.
A flat array parallel to the clause arena now holds, per clause, the two
multiset sizes and a 64-bit Bloom signature per component. `a ⊆ b` implies
`|a| ≤ |b|` and `sig(a) & !sig(b) == 0`, so a candidate failing either test
provably cannot subsume and is skipped without touching the clause; survivors
still run the exact `strengthens` check. Forward subsumption 5.47x faster,
`add_clause` 4.35x, Pred arrival 3.42x, with the derived state bit-identical at
the same message count.

**Left-deep antichain join in local Pred.** `pred_from_neighbor` already
computed Sequoia's Pred antichain as a left-deep join; `pred_local_inner` still
enumerated the whole premise product and pushed every element through the
redundancy trie. On qualified cardinality restrictions, where a `≤n R.C`
premise set has several thousand-candidate dimensions, stack sampling caught a
single `pred_local_inner` call spending over 100 s inside
`RedundancyTrie::remove_supersets_from`. Local Pred now stages the same
antichain per premise, on the same argument: if partial `P` strengthens `Q`
then `P ∪ R` strengthens `Q ∪ R` for every choice `R` from the remaining
premises. Products of at most 64 selections keep the direct enumeration, and
`KM_SPLIT`'s Direction-B mode keeps it because its disjunctive-premise count is
a property of a whole selection. At equal 900 s budget and the identical
fixpoint point, local Pred 161.7 s → 135.5 s.

Neither change alters what is derived, so no Lean re-certification applies. New
guards in `engine.rs`: a no-false-negative property test and a selectivity test
for the screen, oracle-equality tests against unscreened forward and backward
subsumption, an arena/mirror drift test, and oracle-equality of the staged join
against a retained full-product reference over 40 randomised premise
populations. Full release suite green (1,914 lib tests).

**Diagnostics added** (all gated, inert by default): `KM_MSGPROF` reports the
heaviest Pred senders with their pool and predecessor counts plus arrival
statistics and arena/context-slot totals; `KM_PROF_TIME` gains the `add_clause`
phase split, the Pred sender/receiver split, a `saturate` total, and equality
rule time.

**Standing result for ore_ont_1194:** still out of reach at 240 s / 20 GiB, but
for a measured reason. With zero query roots the run still needs more than
900 s and 17.7 M Pred messages, so no query-side strategy can close it. Six
top-level covering disjunctions — the excluded-middle pairs of six qualified
max-cardinality restrictions — make every context a predecessor of the same six
successor hubs, which alone send 56.5 % of the Pred traffic. Clause content is
33x replicated across contexts (189,541 distinct clauses in 6.3 M context
slots), so the next lever is structural sharing of that content, not another
query schedule.

### Carry the repair certificate's enumeration index across rounds (2026-08-02)

Profiling the `KM_ELC_CERT=2` repair on ore_ont_1194 moved the bottleneck. A
repair round costs 1.5 seconds, of which 1.44 seconds is rebuilding the index
the residual join enumerates over: one pass across every label of every live
node for `members`, one across every edge of every live node for
`edges_by_role` — 78.4M label entries and 43.9M edges, for a round that changes
about 0.1M facts. Re-closing the repaired structure, the presumed cost, is 20
milliseconds a round outside the two rounds that cascade. Each conflict-driven
restart repeats sixteen such rounds before hitting the same ⊥ clause.

The index is now built once per repair pass and refreshed from the round's
delta. That is exact rather than approximate because both halves are defined by
an outer loop over the live-node list: a `members` bucket is the subsequence of
that list whose label holds the concept, so its order is the node order and a
new member merges in at its position; a `edges_by_role` bucket also runs over
nodes outermost but follows each node's own edge-set iteration inside one node,
which an insert may permute, so it is reused only while an edge epoch shows no
edge was added, removed, or re-cloned anywhere, and is rebuilt in full
otherwise. A change to the live domain rebuilds both, since a node that dies
has to leave every bucket. `State` carries the two signals: a label-addition
journal, switched on only for a repair pass and capped so it cannot become a
second copy of the label relation, and the edge epoch. The witness-mirror
re-sync assigns whole sets, so it reports its own effect, and falls back to a
full rebuild in the case its addition journal could not describe.

Every index handed to the join is therefore the one a full rebuild would
produce, contents and order included, so the violation enumeration order, the
repair choices, the accepted models, the budgets, the caps, and the route
eligibility are untouched. No calculus rule changed and no Lean
re-certification is needed. `KM_ELC_CERT_AUDIT=1` compares every reused index
against a full rebuild; through six completed restarts of 1194, no index
differed. Six focused regressions cover the delta merge, the edge-epoch
rebuild, a dying node, the mirror re-sync, invalidation, and a multi-round
repair verdict.

The exact 1194 gate is still a timeout, and this does not close it. In the same
245-second budget the repair now completes six conflict-driven restarts where
it completed three, and the banned-choice trace is identical restart for
restart. Wall time is 245.41 against 245.39 seconds; peak RSS is 6,692,196
against 6,725,988 KiB, 0.5% higher for the journal and the carried index. The
complete release suite passes 1,949
tests with zero failures and eight intentional ignores.

Cluster-native build job `49826807`, end-to-end gate array `49826957`, and
full resumable array `49826971` validate commit `e05b35c` over all 592
ontologies. The integrity audit found 590 newly completed tasks and two gate
rows correctly resumed, with no missing terminal markers or temporary files.
The sweep has 591 `ok` rows and only the expected 1194 error. All semantic
fields and selected-route traces are identical to the preceding complete
sweep. Mean and median wall time over successful rows are 6.6854 and 0.2758
seconds; mean and median peak RSS are 838.01 and 45.22 MiB. The tested IBEX
binary has SHA-256
`ffbd9afd129533e7fa67c1c86f726496d4e269dfc38418375c16aa033e32dd9b`.
The complete evidence is in
[`results/benchmarks/2026-08-02-e05b35c-auto/`](results/benchmarks/2026-08-02-e05b35c-auto/).

What remains is not a constant factor. Every restart bans one disjunct at one
node, and 1194 keeps conflicting on the same residual clause 149, first at
`FMA_35225` and later at other nodes. An extended diagnostic reached 30
restarts against a restart cap of 64 without the pass converging before it was
stopped. Closing 1194 through this route needs the conflict analysis to
generalise a banned choice, not faster restarts.

### Index EL backward links by exact role (2026-08-01)

EL completion now stores predecessor links under the exact `(target, role)`
key, with a first-arrival role list for rules that consume every predecessor.
Sub-NF4 therefore visits only parents on roles named by the applicable NF4
axioms. Bottom propagation, symmetric role-chain joins, repair merges,
self-edges, and incremental reuse and restart retain all of their former
inputs. This changes scheduling order but not the set of rule joins or the
monotone fixpoint, so it needs no Lean re-certification. Eight focused
regressions cover those consumers and input-order invariance. The complete
release suite passes 1,943 tests with zero failures and eight intentional
ignores.

The exact ORE 1194 gate retained essentially identical saturation counts and
still timed out after 245.29 seconds with zero output. Peak RSS fell from
7,078,600 KiB to 6,698,628 KiB, a 5.4% reduction. This is another memory
improvement, not a 1194 closure. The tested `elc` binary has SHA-256
`d7468bf1a39bbdae9415fd480be0de01cb98e42df8da64eab3bd3413d0ba7c5f`.

Cluster-native build job `49811241`, gate `49811822_401`, and full array
`49811856` validate the integrated source over all 592 ontologies. The audit
finds 591 `ok` rows and only the expected 1194 error. All statuses, verdicts,
signature and full-IRI digests, consistency values, subsumption counts, and
unsatisfiable-class counts are identical to the preceding sweep. Mean and
median wall time over successful rows are 6.6750 and 0.2779 seconds; mean and
median peak RSS are 842.06 and 44.79 MiB.

### Iterate Edge-NF4 propagation in place (2026-08-01)

EL completion no longer copies `prop[(target, role)]` into a scratch vector on
every Edge-NF4 firing. It holds the immutable propagation-slice borrow while
inserting conclusions through disjoint borrows of `sub_super` and the
worklist. Propagation buckets can grow only when a queued `Sub` item is
processed after the loop, so this preserves the exact conclusion and worklist
order, including self-edges. It changes neither the calculus nor its fixpoint
and needs no Lean re-certification. Five focused ordering and self-edge
regressions were added. The complete release suite passes 1,935 tests with zero
failures and eight intentional ignores.

The exact ORE 1194 gate retained essentially identical rule counts and still
timed out after 245.29 seconds with zero output. Peak RSS fell from 11,101,160
KiB to 7,078,600 KiB, a 36.2% reduction. This is a memory improvement, not a
1194 closure.

Cluster-native build job `49796295`, gate `49796423_0`, and full array
`49796520` validate the integrated source. The audit finds 591 `ok` rows and
only the expected 1194 error, with no semantic changes from the preceding
sweep. The same array now handles 4669 through streaming full-IRI
fingerprinting, so all 592 rows complete without a manual postprocessing
recovery job.

### Index exact-role NF4 backward joins (2026-08-01)

EL completion now sorts each `NF4` filler bucket by role and binary-searches
the exact-role range for every backward link. The rule fires the same axioms
and derives the same conclusions as the previous full-bucket scan; it only
skips entries that the former `role == axiom_role` guard rejected. A regression
with two roles and multiple conclusions on one filler pins that behavior. The
complete release suite passes 1,930 tests with zero failures and eight
intentional ignores.

On the exact ORE 1194 candidate gate, Sub-NF4 probes fell from about 3.32
billion to 774,848,772. The ontology still timed out after 245.40 seconds at
11,101,160 KiB with no output, while Edge-NF4 remained at 2,086,666,580 visits.
This is a fixpoint-preserving performance improvement, not a 1194 closure.

## [0.2.1] – 2026-08-01

### Automatic production coverage: 591 of 592 (2026-08-01)

Commit `994c7b3` adds a fail-closed private negative-existential mirror route
and generic EL completion for object-property domains. IBEX array `49778149`
and the exact 4669 oracle gate `49779419` produce 591 `ok` rows and one
`error` row under the 240-second, 20-GiB reasoner contract. All 592 records
carry binary SHA-256 `44c5c9094ad490702c213ae47e8a97eb113a6c66b145f98281a32606b7d73720`.

Ontology 4669 completes automatically in 68.95 seconds at 4,823,596 KiB. Its
846,306 subsumptions, zero unsatisfiable classes, and full-IRI digest
`d02decbafe66d8a9f1afaf7385785b6937fe46c1f288a33113c83c2bbe805b96`
match the independently derived mirror oracle. The ordinary Python benchmark
postprocessor exceeded its task cgroup while handling this 104-MiB taxonomy,
so the retained row records the direct reasoner measurement and the separate
oracle adjudication explicitly. Ontology 1194 remains the sole unresolved
input.

## [0.2.0] — 2026-08-01

This release raises the single-command `km classify` result to 590 operational
completions on the 592-ontology ORE 2015 corpus under the standard 240-second,
20-GiB contract. Of these, 587 exactly match retained Konclude full-IRI
signatures. Ontologies 2669 and 15516 complete with independently investigated
consistency results that differ from the retained Konclude results, and 10860
completes without usable Konclude gold through a fail-closed rule/ABox route
supported by an independently checked inconsistency core. The remaining inputs
1194 and 4669 still fail closed without a production taxonomy.

The release includes the pure-Rust multi-call CLI and automatic router,
standard OWL syntax ingestion, exact nominal, rule, cardinality, EL++, CB, and
gated Konclude-derived procedures, incremental reasoning, source-axiom
explanations, the Protégé integration, the complete route matrix, and retained
source-bound benchmark evidence. The separate Lean development remains a
specification and proof artifact for selected abstract calculus results. It
does not verify the complete Rust executable or production portfolio.

The certified production sweep is IBEX array `49721626`, with independent
audit `49734184`. It verified all 592 terminal records, checkpoints, route
traces, and binary identity. The serial Rust release suite for the certified
state passes 1,836 library tests, with zero failures and eight intentional
ignores, plus all integration and documentation test targets.

### CB engine scaling and ORE 2015 coverage push

### Recheck incremental residual repairs before choosing (2026-08-01)

The certified-EL model repair now processes forced single-head residuals before
covering choices and skips any violation whose head became true earlier in the
same repair round. The previous round-start violation batch could add a forced
cardinality consequence and then also add the opposite side of a stale
covering disjunction, creating an avoidable clash. The final closed-model and
all-residual checks remain unchanged, so this alters model-search order only.

A regression exercises a forced inverse-position residual together with an
exhaustive disjoint cover. The complete release suite passes 1,835 tests with
zero failures and eight intentional ignores, plus all integration targets. On
ORE 1194 the corrected repair moved beyond the previously immediate
`Q_118720`/`Q_118721` conflict family and explored later cardinality partitions,
but still timed out after 240.22 seconds at 5,443,724 KiB. This is progress in
the candidate certificate route, not a closure.

Cluster-native focus job `49725035` reproduced the 1194 timeout at 240.0628
seconds and 5,354.42 MiB while preserving exact forced-route signatures on
1034 and 2237. Follow-up conflict-attribution and canonical-witness-death
experiments did not improve completion and were removed.

### Revalidate the current ORE 1194 blocker (2026-07-31)

A source-current default `km classify` run establishes that ORE 1194 no longer
fails at the packed composite-term boundary. The automatic route selected
`nominals`, completed frontend processing in 8.64 seconds, and ran the exact
CB worker to its 190-second central cap. It emitted no taxonomy and returned
after 198.98 seconds total at 3.58 GiB peak RSS. The remaining operational
blocker is therefore exact-search wall time, not the former `f(o)` layout or
the 20-GiB memory limit. The reasoner still fails closed.

### Preserve distinct same-filler Skolem witnesses in the EL certificate (2026-07-31)

The certified EL canonical model no longer identifies two different Skolem
functions merely because their existential restrictions use the same filler
concept. Each function receives an internal EL-closed witness node, and its
NF3 edge targets that witness. The witness inherits the filler's completed
label and existential structure through an internal subclass axiom. This
preserves the required identity distinction for normalized `≥n R.C` clauses
without publishing internal witness symbols.

The previous collapse made `f0(x) ≈ f1(x)` true by construction whenever both
functions had filler `C`, so a normalized `≥2 R.C` disequality clause could
never certify. A regression test covers the exact same-filler shape in plain
and repair certificate modes. The complete serial release suite passes 1,828
library tests, all integration targets, and eight intentional ignores. This
changes only the certificate model construction; the final all-residual-clause
check remains the complete-answer gate, and no CB-calculus rule changes.

### Automatic production coverage: 590 of 592 (2026-08-01)

IBEX array `49721626` completed all 592 default `km classify` tasks from commit
`4703045`. Audit `49734184` verified every terminal row, checkpoint,
profile/production route trace, and binary identity. The final statuses are 590
`ok`, one `error`, and one `timeout`. Full-IRI scoring gives 587 exact retained
Konclude-signature matches, the independently adjudicated inconsistent cases
2669 and 15516, and the independently adjudicated 10860 `ok/nogold` result.

Ontology 10860 automatically selects `ht_rules` and completes in 0.0403 seconds
at 10.31 MiB. Its fail-closed explicit rule/ABox cardinality certificate is
independently supported by HermiT on the extracted inconsistency core. The only
remaining non-completing inputs are 1194 (`error`) and 4669 (`timeout`).

On ORE 1194 this correction reaches the next residual family rather than
closing the ontology. `Q_118720` and `Q_118721` form the exhaustive disjoint
partition between at most two and at least three qualified `connects`
successors. A restart-zero diagnostic still declined, in 113.92 seconds at
5.15 GiB, because the death-tolerant model pass encountered the same
empty-head contradiction. The next closure step must construct a consistent
cardinality-aware partition model; reducing the retry budget is insufficient.

### Complete automatic sweep: 587 exact matches (2026-07-31)

Source-bound IBEX array `49701329` completed all 592 default `km classify`
tasks using the `ebe56bd` source and binary SHA-256
`c6f3e01c67421f3ae97c5edadf59a10befea361385dcdd0912dcbb9e762f9317`.
Independent audit job `49710709` validated every terminal row, checkpoint,
profile/production route trace, and binary hash. The final statuses are 589
`ok`, one `error`, one `timeout`, and one `unsupported`. Full-IRI scoring gives
587 exact Konclude matches and the two adjudicated consistency mismatches 2669
and 15516.

The only semantic change from the accepted 592-row baseline is 7499: it moves
from `error` to `ok/match` through automatic `certified_card_proxy_abox`, in
86.7359 seconds at 2,409.59 MiB, with signature SHA-256
`f82850c6582131358cd9ecc108888e2131734900cf687d055a7a7c0f4fece17d`.
All other 591 status, verdict, signature, and selected-route rows are unchanged.
The three remaining non-completing ontologies are 10860, 1194, and 4669.

### Complete v16 automatic sweep: 586 exact matches (2026-07-31)

Source-bound IBEX array `49689798` completed all 592 default `km classify`
tasks with binary SHA-256
`afdc15a00168a23f4426b0ca155f54ad6c3cb65cbad745f07e5f2eef862f0e3a`.
Corrected independent audit `49692538` verified the frozen inputs, source,
binary, harness, checkpoints, route traces, and all terminal rows. The final
statuses are 588 `ok`, two `error`, one `timeout`, and one `unsupported`.
Full-IRI scoring gives 586 exact Konclude matches and two adjudicated
consistency mismatches. The four non-completing rows are 10860, 1194, 4669,
and 7499.

The new `nominal_ni_abox` route closes 6934 automatically and exactly in
199.3235 seconds at 1,434.64 MiB. Its signature SHA-256 is
`5e60a794400802833a9d5785abb6320b7b13d702e48a4c810462bad6c1fc931e`.
The regression controls remain exact, including 15846 through
`certified_nominals` in 219.4067 seconds at 19,036.76 MiB.

The first dependent audit, job `49689799`, exposed an audit-model gap: eight
ontologies legitimately refine the source candidate `nominals` to
`nominal_ni_abox` only after the frontend has proved the typed normalized ABox
certificate. The revised generic check permits that transition only when the
serialized source profile contains the required structural candidate fields;
it contains no ontology identifiers. Audit script SHA-256 is
`074690b2e9f3507048315d27f04e85be4ca69469c003a6c3cda934797877a57c`.

### Certify typed-ABox SHOIQ routing (2026-07-31)

The frontend now refines a nominal source candidate to `nominal_ni_abox` only
after normalization proves a complete positive-data-assertion omission
certificate. The certificate accounts for inherited data properties,
class-conditional maximum and exact cardinality one, duplicate values,
`rdfs:Literal`, `owl:topDataProperty`, and unsupported constructs on each
property. The route preserves the exact CB fallback and uses the no-blocking
SHOIQ complete-answer-or-defer worker.

The bridge also accepts a valid empty internal individual suffix when its full
IRI proxy resolves, allocates trusted ABox-only named classes, rejects generated
markers, and retains inverse-functional clauses exactly. No CB rule premise,
conclusion, ordering, redundancy condition, or fixpoint changed, so this work
does not require Lean re-certification. The serial release suite passes 1,825
tests with zero failures and eight intentional ignores. Focused IBEX job
`49689197` matched 6934, 10702, 15846, and 6999 exactly before the full sweep.

### Complete v15 automatic sweep: 585 exact matches (2026-07-31)

Source-bound IBEX array `49680023` completed all 592 automatic `km classify`
tasks with binary SHA-256
`914c7bb517ef90182a420f4cbbaec7051720b291d74db4fdd2b1e8c6eca72ef0`.
Dependency-bound audit `49680024` exited successfully after verifying all
terminal rows, source and binary hashes, harness components, route traces,
checkpoints, and expected nonmatches. Terminal statuses are 587 `ok`, three
`error`, one `timeout`, and one `unsupported`. Full-IRI scoring gives 585 exact
Konclude matches and two contested consistency mismatches.

This is one additional automatic exact match over v13: 10702 now selects
`nominal_ni_tbox` and matches exactly in 2.5909 seconds at 21.36 MiB. The
specialist-scoped `SameIndividual` admission preserves 15846, which matches
exactly through `certified_nominals` in 213.1123 seconds at 19,038.13 MiB.
The five non-completing rows are 10860, 1194, 4669, 6934, and 7499. The
contested completed rows remain 2669 and 15516.

### Scope native SameIndividual admission to the 10702 specialist (2026-07-31)

The generic native ABox bridge again rejects `SameIndividual` transactionally
and leaves classification to the exact fallback. Only the source-profile-gated
`nominal_ni_tbox` specialist may collapse equality components into native
roots. This preserves the automatic 10702 recovery without diverting large
equality-heavy ontologies into an unsuitable native run.

The change fixes a measured v14 regression on `ore_ont_15846.owl`, whose
129,647-individual ABox contains 66,423 `SameIndividual` axioms. Both the
pre-query-collapse v14 binary and a query-collapse-disabled candidate timed out
at 240 seconds near 6.4 GiB, proving that query equivalence was not the cause.
The source-bound replacement was built by IBEX job `49679551` from archive
SHA-256
`f5be1ce9ea8a6b663a39cac50c9a02c4eeb29342a86d8243540a8cf2ffbbb6fc`;
binary SHA-256 is
`914c7bb517ef90182a420f4cbbaec7051720b291d74db4fdd2b1e8c6eca72ef0`.
Automatic-route gate `49679552` matched Konclude exactly on all three arms:
10702 in 2.2759 seconds at 21.39 MiB, 15846 in 209.9367 seconds at
19,060.12 MiB, and control 6999 in 0.2980 seconds at 83.06 MiB. The complete
serial release library suite passes with 1,817 tests, zero failures, and eight
intentional ignores.

### Complete v13 automatic sweep: 584 exact matches (2026-07-31)

Source-bound IBEX array `49665768` completed all 592 automatic `km classify`
tasks. Integrity audit `49665770` verifies the frozen binary, source archive,
harness, canonicalizer, watchdog, and both audit programs. Terminal statuses
are 586 `ok`, four `error`, one `timeout`, and one `unsupported`. Full-IRI
scoring gives 584 exact Konclude matches and two contested consistency
mismatches. The non-completing rows are 10702, 10860, 1194, 4669, 6934, and
7499. This sweep includes the automatic 12653 recovery but predates the
automatic 10702 specialist.

Route-consistency audit `49665771` reports two metadata mismatches, 11311 and
11745: their source profile initially selects `elc`, the normalized frontend
sets `el_rbox_safe=false`, and production correctly falls through to
`cb_plain16`; both final signatures match gold exactly. The audit currently
models a selected route as terminal rather than allowing this documented ELC
defer path. These are audit false positives, not reasoner result differences.

### Collapse explicitly equivalent CB classification roots (2026-07-31)

The default CB classifier now runs one root query for each group of named
classes connected by explicit opposite unit implications
`A(x) -> B(x)` and `B(x) -> A(x)`. Those clauses prove that the classes have
the same interpretation in every model. KM classifies the least-id
representative through the unchanged calculus, then restores the exact
non-reflexive subsumption row for every group member. One-way implications are
never collapsed. `KM_NO_QUERY_EQUIV=1` retains the prior schedule for
differential testing, and split or ordered-resolution experimental routes
remain unchanged.

This changes query enumeration only, not rule premises, conclusions, ordering,
redundancy, or the derived per-query fixpoint, so it requires no Lean
re-certification. Focused tests cover transitive groups, exact output-row
restoration, and one-way rejection. The complete serial release library suite
passes with 1,815 tests, zero failures, and eight intentional ignores.

The target profile is ORE 1194. Its current one-worker nominal route seeded
only 2,850 of 70,231 roots in 300 seconds, created 7,378 contexts, and queued
278,269 messages without reaching the message fixpoint; peak RSS was 1.59 GiB.
An independent scan of its frozen 1,062,240-clause frontend payload finds
3,426 mutual-unit groups and 5,204 removable roots. This is a measured 7.4%
query reduction, not a closure claim. The source-bound IBEX candidate matched
gold exactly on controls 1034, 2237, and 6999, but 1194 still failed. A
separate scheduling gate tested periodic message-fixpoint drains every 64,
128, and 256 roots; all three runs failed at about 198 seconds and
3.75–3.77 GiB when the default 190-second central cap expired. Giving the
parallel central strategy 295 seconds and disabling its late retry also did
not close 1194: it reached the external 300.0413-second timeout at 4.17 GiB.
Query equivalence remains an exact general optimization, but neither query
batching nor central-budget reassignment is a route for this residual.

### NI-gated nominal specialist restores 10702 automatically (2026-07-31)

Automatic routing now recognizes the source-feature layout of
`ore_ont_10702.owl` and selects `nominal_ni_tbox`. The specialist preserves the
validated clausal TBox representation and runs the single-threaded
hypertableau with inverse-safe pairwise blocking. Before publishing any
classification, it checks completed models for the actual missing
nominal-introduction premise: a blockable number-role neighbour of a root that
is not that root's direct successor. It defers if that premise occurs.

The frontend can omit the ontology's one positive data assertion only after
proving its integer datatype range and explicitly asserted named domain.
`SameIndividual` components are canonicalized before native nominal roots are
constructed, and redundant universal ground markers no longer count as
dropped clauses. Inputs outside the complete source-layout gate retain the
ordinary exact nominal CB route.

The source-bound IBEX probe used binary SHA-256
`f2a7d50a60726c5c14f0fc1f3b4225db858749096658cd2b11539f1fc84642d9`.
It completed in 2.6099 seconds at 19.84 MiB and matched Konclude exactly:
587 canonical subsumptions, no unsatisfiable named classes, consistent, and
signature SHA-256
`eee761d0c89347a42ce9a221e7d98295f4a9d7527c755cb3eafa9978cc06d55b`.
The automatic-route 592-ontology regression sweep is job 49676527; its result
remains pending and is not included in the completed benchmark totals.

### Exact numeric datatype bridge restores 12653 automatically (2026-07-31)

The source-terminology bridge now certifies a bounded atomic numeric datatype
fragment instead of rejecting every decimal-derived range. The certificate
uses the frontend's OWL 2 datatype relation procedures to preserve the
directional tower
`positiveInteger ⊑ nonNegativeInteger ⊑ integer ⊑ decimal`. It accepts only
atomic ranges, cardinalities from zero through two, one declared range per data
role, and exact nested range intersections. Unknown ranges, larger
cardinalities, conflicting role ranges, unsupported datatype clauses, and
unrepresented interactions still defer to the complete fallback.

This restores `ore_ont_12653.owl` through the normal automatic
`production_all` route. Source-bound IBEX build job 49665164 produced binary
SHA-256
`1c904f79ed1058e4dd3395c1028eb14f6fb41e420940c88d66f67a1dd78e1bed`
from source archive SHA-256
`86b40a456258f161d673f6589826bce6ead9830dc360a2e65685578d141a2f95`.
Exact gate job 49665588 completed on an Intel Xeon Gold 6248 in 0.1012 seconds
at 39.81 MiB. KM and Konclude both produce ten subsumptions, no
unsatisfiable named classes, and a consistent ontology; the signature has
zero missing or extra entries. The complete local library suite passes with
1,808 tests, zero failures, and eight intentional ignores.

### Exact positive-EL ABox materialization restores 1579 and 3377 (2026-07-30)

Automatic routing now distinguishes a positive EL++ ABox from a general
nominal ontology. The frontend retains `SameIndividual` and
`DifferentIndividuals` exactly, checks their union-find consistency, and
issues a source-only materialization certificate only when the TBox and ABox
contain no disjunction, complement, number restriction, functionality,
concept-level nominal, datatype constraint, negative assertion, rule, import,
or bottom role.

The orchestrator does not simply drop that ABox. It represents each equality
class of individuals as a fresh EL completion node, seeds every class
assertion, materializes each ground role assertion as an edge between the
corresponding nodes, and checks all inequality pairs. A normalized non-EL
clause set or incomplete typed ABox makes the certificate decline. Only a
successful consistency decision permits the nominal-free `production_all`
taxonomy. This is a frontend routing and EL-model certificate, not a change to
the CB calculus, so it needs no Lean re-certification.

Source-bound IBEX build job 49637596 produced binary
`d4ccde36263f9044fc891787ad39bf543b96ab0f27a153477712fd2dadcd55c7`.
Automatic-route exactness job 49637883 matched the complete Konclude
signatures:

- 1579: 56,782 pairs, 12.33 seconds, 852,504 KiB;
- 3377: 4,490,309 pairs, 37.03 seconds, 1,971,828 KiB.

Both have zero missing or extra pairs, identical consistency, and identical
empty unsatisfiable-class sets. The complete release suite passes serially:
1,826 tests passed, zero failed, eight ignored. The serial setting avoids
pre-existing environment-variable interference between tests that configure
different reasoning routes.

### Elide isolated tautological top-role inclusions; restore ore_ont_541 (2026-07-30)

The functional-syntax frontend now removes
`SubObjectPropertyOf(R owl:topObjectProperty)` and the corresponding data-role
axiom only when the relevant top property has no other logical occurrence in
the ontology. Such an inclusion is true in every OWL 2 interpretation. Before
this pass KM represented the builtin as an ordinary role and produced a
write-only `R(x,y) -> U(x,y)` clause plus an RBox row. The CB result did not
depend on that row, but the universal-role feature made the otherwise suitable
Konclude-derived completion bridge decline `ore_ont_541`.

The pass scans the source document before normalization and removes matching
axioms from both the ontology AST and the independently extracted RBox. A
declaration is not treated as a logical use. Any other use of either builtin
top property disables the entire transformation, so an ontology that needs
universal-role semantics is unchanged and still follows the existing
fail-closed path. `KM_NO_TOP_ROLE_ELISION=1` is a differential-test switch,
not a routing option.

Source-bound IBEX job 49633775 built revision `af4cb54` with archive SHA-256
`a19af2619f9c083dee1508e82b9ca9f8235f17b393b489b77a7c63a61e2a50af`;
the installed binary SHA-256 is
`0e9e612a3c51b03f0709ce1ae3c10a67bdd70653bdc83480bc0f3cd8c64cd460`.
Exact test job 49633776 classified `ore_ont_541` through the normal automatic
portfolio in 0.15 seconds at 29,760 KiB. Its full result has 164/164 reference
pairs, zero missing, zero extra, the same empty unsatisfiable-class set and the
same consistency verdict. The change is semantics-preserving frontend
preprocessing and does not alter a calculus rule, so it needs no Lean
re-certification.

### One prepared ontology shared across parallel CB workers (2026-07-30)

Split the CB engine's immutable ontology state out of `Engine` into
`PreparedOntology` (`Engine::prepare` / `Engine::from_prepared`): the normalized
clause arena, the Hyper candidate indexes, the trigger-analysed `Sig` and the
nominal-enumeration certificates. `Reasoner::saturate` prepares the ontology
once and gives every worker the same `Arc`-shared copy, so the sequential run,
each static chunk and each work-stealing worker no longer hold a private clone
of the clause set. Retained insertion is the only writer and now goes through
`Arc::make_mut`, so an engine that still shares a prepared ontology copies
before it mutates. Preparing once also removes the throw-away engine that
existed only to enumerate the named queries, and the `KM_SPLIT` search reuses
one prepared ontology across its branch engines instead of re-indexing the
clause set per search node.

On `ore_ont_1194` (1,062,241 clauses, 88,440 interned concept names, 221,086
class assertions) the clones were the 20 GiB wall. Engine peak RSS over an equal
240 s of saturation, `KM_NOMINALS=1`, 56 threads: **19.58 GiB -> 4.15 GiB**.
TBox-only mode over the same 240 s: 1 thread 1.59 -> 1.59 GiB, 8 threads 4.90 ->
2.75, 16 threads 7.78 -> 3.87, 56 threads 19.67 -> 4.97. The marginal cost of an
extra worker at 56 threads falls from about 335 MB to about 62 MB, the residue
being per-engine saturation state that cannot be shared. A fixed 40-query run
(same work in both builds) drops 13.79 GiB -> 2.24 GiB.

1194 is **not** closed. With memory no longer the limit it is wall-clock bound
far past the contract (no fixpoint after 1,800 s at 56 threads), and its default
classify route still fails at about 33 s in both builds with the reported
`nominal mode: f(o) term space exhausted (f id 124950, individual 18055)` limit:
`COMP_IND_BITS = 17` leaves about 32,767 Skolem-function ids in the composite
`f(o)` range and the absorbed nominal route introduces 124,950. Lifting that
encoding limit is the next step for the route, and it is untouched here.

Fixpoint-preserving: preparation is a pure function of the input clause set
(`Engine::new` is `prepare` followed by `from_prepared`), the shared state is
immutable for the whole saturation, and the query partition is unchanged, so
each worker derives exactly what it derived before. Validation: byte-identical
engine output HEAD vs shared on 10 ORE ontologies at 1, 4 and 8 threads, the
same in nominal mode on the five of them with an ABox, byte-identical frontend
output, and `cargo test --release` at 1779 passed / 0 failed / 8 ignored plus the
integration suites. Numbers, commands and caveats in
[`results/benchmarks/2026-07-30-cb-shared-prepared-ontology/`](results/benchmarks/2026-07-30-cb-shared-prepared-ontology/README.md).

### Cached completion diagnostic gates restore ore_ont_3215 (2026-07-30)

`ore_ont_3215` classifies again inside the benchmark contract on current main.
IBEX job 49624875 ran the exclusive `cpu_intel_gold_6248` node at 240 seconds
and 20 GiB: the isolated `ht_bridge` route finished in 162.2 s at 5,560,592 KB
and the production `auto` route in 161.9 s at 5,500,480 KB. Both signatures are
exactly equal to Konclude gold, with 3,923,171 pairs, zero missing, zero extra,
no unsatisfiable-class difference, and the same consistency result.

The 2026-07-27 full sweep reported `ore_ont_3215` as a timeout on every one of
the 44 KM arms, and the source-bound historical rerun of the 2026-07-13 KPSet
closure binary (job 49522590, exclusive node) timed out as well. So the cause
was not a regression against that closure. Rebuilding `91db9fb` and current
main from source and running both on the same host confirms it: the historical
binary needs 397.7 s in its HT worker at 5,353,720 KB, current main 385.8 s at
5,536,200 KB, and both produce the exact 3,923,171-pair signature. The KPSet
design is intact; what the ontology lost was headroom.

Phase instrumentation (`KM_BRIDGE_PROGRESS`, now printing per-phase seconds)
places the cost precisely. Of the 386 s, the bridge environment takes 1.1 s,
saturation 34.4 s (answering 36,650 subjects directly and leaving the
documented 18,323-subject residue), the KPSet barrier 0.8 s, and verification
12.7 s with zero pairwise subsumption tests. The remaining 340 s is the
satisfiability phase: 18,323 synchronous completion jobs.

Sampling that phase shows over a third of it inside `getenv`. The completion
rule bodies read `KM_BRIDGE_WATCH_TAG`, `KM_BRIDGE_WATCH_NODE`,
`KM_BRIDGE_SEARCH_LOG`, `KM_BRIDGE_DUMP_CLASH` and their siblings inline, once
per concept addition, in `insert_concepts_to_individual_concept_set`,
`add_concept_to_individual{,_skip_and_processing}`, `create_successor_individual`
and the clash/OR sites, plus once per `pop_branch_epoch` in
`ProcessContext::ht_check_dangling_satellites`. `std::env::var` also takes the
process-wide environment lock and allocates a `String` on every call. The
2026-07-13 closure removed exactly this cost from the saturation hot path
(`saturation/mod.rs` cached gates); the completion layer never received the
same treatment, and later completion work multiplied the number of call sites
it crosses.

`konclude_ht::completion` now owns cached accessors for every one of these
CLI-only diagnostics, built from the same `OnceLock` pattern
`saturation/mod.rs` already uses, and all 50 inline reads route through them.
The environment is immutable for the life of a worker and no route bundle,
orchestrator path, or test sets any of these variables, so each accessor
returns exactly what the inline call returned. `KM_BRIDGE_WATCH_TAG=<tag>` and
the rest behave as before. Nothing else changes: no rule fires differently, no
derived set moves, and no Lean re-certification is required.

On the same workstation the isolated `ht_bridge` route drops from 385.8 s to
215.4 s at 5,543,772 KB, still exact. A new integration test
(`engine/tests/completion_hot_path_env.rs`) fails the build if an inline
`std::env::var` returns to a completion rule body or to the process-context
epoch check, and a unit test pins every cached gate to its unconfigured
default. Release validation is 1,813 passed, 0 failed, 8 ignored.

The first family harness, job 49622765, stopped early because its comparator
returned a nonzero status for a mismatch. Job 49625540 completed the remaining
panel: 7581 and 9540 stayed exact, 4669 timed out, and the intermediate binary
remained incomplete on 148. The corrected focused recheck, job 49625668, made
11745, 3215, 9663, and 10621 exact under the 240 s / 20 GiB contract. The
latest-source 20-case panel, job 49626062, completed with 16 exact signatures.
The exact set is 148, 3215, 4054, 4755, 7127, 7581, 8068, 8864, 9540, 9663,
9724, 10621, 11315, 11745, 12414, and 14817. Ontologies 541, 4669, and 12653
timed out. Ontology 7914 returned an error because that panel executable
predates the feature-based independent-ABox route; the focused feature-router
gate validates 7914 separately.

The evidence is in `results/benchmarks/2026-07-30-3215-restoration/` and the
causal record in `docs/SOLVE-3215.md`.

### Restore exact ore_ont_7499 with clause-retained cardinality fences (2026-07-30)

The 2026-07-27 full sweep records ore_ont_7499 as unsolved on every current-main
route: `auto` errors at 190 s, `manual` and the documented `card_race` /
`htforce_race` environments time out at 240 s, and `production_all` publishes a
SOUND but INCOMPLETE taxonomy — the CB engine finishes in 68.8 s with 32,847 of
the 36,145 gold subsumptions (full-IRI taxonomy `c9450c3e…` against the
Konclude/HermiT identity `a87bedcb…`). Every one of the 3,298 missing pairs
needs the `≥2 VO_0001243.OBI_0100026` recognition that defines `VO_0000641`;
the first-class `≥n` rules derive it, the CB engine does not. The historical
`card_race` binary (`0d20dd1`, 92.8 s / 18.5 GiB, sweep evidence
`results/benchmarks/2026-07-18-ore-solve-routes/evidence/retained-route-rerun/`)
answered gold-exact through the first-class cardinality arm.

Diffing that binary's `cb_to_ht` input against current main shows the arm is now
gated off by three certificate rules that are each stricter than their own
justification. The historical input reached the arm only because `spawn_ht`
passed `rbox = None` (no inverse pairs, no fences, no ABox), i.e. the arm ran
INVERSE-BLIND. This change instead admits the same ontology to the arm with the
inverse-aware configuration current main already has, and the exactness is
recovered at 1.2 GiB instead of 18.5 GiB.

**Clause-retained RBox fences.** `rbox.rs` records a `fenced` row whenever the
first-class RBox channel has no shape for an axiom, even where
`parse.rs`/`normalise.rs` still clausify it exactly: irreflexivity is
`R(x,x) → ⊥`, reflexivity the `R(x,x)` fact, and a complex domain/range on a
NAMED role the ordinary `∃R.⊤ ⊑ C` / `⊤ ⊑ ∀R.C` inclusion. 7499 carries
`IrreflexiveObjectProperty(RO_0002351)` and a `ObjectUnionOf` range on
`VO_0001480`, and both the source and the normalized certificate declined on
those markers alone. They are now admitted: like the plain `domain`/`range`
rows, they constrain a role against classes (or itself) and never merge two role
components, so they add no NN/NI number-role premise, and the Ht consumes the
axiom itself from the clause set. The source certificate additionally proves the
constrained role is outside the number-role component; `role-constraint` stays
fenced because `rbox.rs` uses that one reason for both asymmetry (clausified)
and `DisjointObjectProperties` (dropped), so the normalized recheck cannot tell
them apart.

**Write-only universal super-role.** 7499 declares
`SubObjectPropertyOf(RO_0001000, owl:topObjectProperty)`, a tautology the
frontend compiles to the bridge clause `R(x,y) → U(x,y)`. The certificate
declined on any universal-role occurrence. It now admits the super-role position
only, and the normalized recheck proves the universal role is WRITE-ONLY (no
clause body atom, no counted role, no other RBox row), so nothing can read the
edges it writes. A universal role in the sub position, in a restriction, or on a
number role still declines.

**Native ABox materialization is a separate question.** The old certificate
bundled the number-role separation proof with the native-ABox conditions, so
7499 lost the cardinality arm because its 74 `BFO_0000062` assertions feed a
proper role chain. `OntologyProfile` now carries both halves:
`card_number_role_separable` (number-role separation alone, the precondition of
the `≥n`/`≤n` rules) and the unchanged `inverse_cardinality_role_separable`
(that plus exact ABox materialization). `Route::CertifiedCardNominals` still
requires both — ore_ont_9540 keeps its exact native-ABox route — while the new
`certified_card_proxy_abox` route serves the number-role half alone. It
reproduces the validated `card_race` environment (`KM_HT_ONLY=card`,
`KM_HT_MODE=race`, `KM_ABSORB=0`, CB racing) and adds
`KM_HT_CARD_PROXY_ABOX=1`, which keeps an ABox that fails
`native_abox_role_automata_separable` out of the card input. Seeding the
uncertified ABox instead buys no completeness: the card arm does not finish in
400 s with it and finishes gold-exact in ~110 s without it.

**That route is MEASUREMENT-ONLY and is never selected automatically.**
Dropping ABox axioms removes constraints, so every subsumption it publishes is
entailed — but that is an under-approximation, which proves soundness, not
completeness for the ontology as a whole. Completeness would additionally
require that the ABox cannot change a named-class subsumption AND that the KB is
consistent, because an inconsistent KB entails every subsumption while a dropped
ABox still yields an ordinary taxonomy. The frontend's `abox_inconsistent`
precheck cannot supply the second premise: it closes asserted memberships over
named subclasses, domain/range and `SameIndividual` and fires only on an
asserted disjoint pair or a negative-assertion clash, so `A ⊑ ⊥` with
`ClassAssertion(A a)`, a cardinality clash, and a role-chain-derived range clash
all escape it (new test
`abox_consistency.rs::derived_abox_contradictions_are_not_detected` pins both
counterexamples). ore_ont_7499 alone cannot license the general rule, so
`select` keeps every unmaterializable ABox on the exact nominal calculus and the
route stays explicitly selectable only, pending a general ABox-irrelevance
certificate (the existing `positive_abox_tbox_separable` is the shape one would
take) plus a complete consistency decision.

Result on the workstation (56 shared cores, ontology SHA-256 `37450d59…`):
`km classify --route certified_card_proxy_abox ore_ont_7499.owl` returns 36,145
subsumptions, 0 unsatisfiable, in 114 s of HT worker time (1 m 54 s wall) at
1.04 GiB. The full-IRI fingerprint
(`results/benchmarks/2026-07-27-solving-routes-full-sweep/full_panel_fingerprint.py`)
is `a87bedcb6f6af4e3471686a5a6627a98e4ecd3a8fd102bd610ed38e352d22038`, byte-identical
to Konclude and HermiT in the frozen sweep and to the historical `card_race`
binary's own output. ore_ont_7499's AUTOMATIC route remains `nominals`. Route
selection over the local diagnostic corpus is unchanged everywhere (9540 keeps
`certified_card_nominals`; 10702, 15672, 9635, 10908, 12698, 7914 keep
`nominals`), and the answers of 1603, 7901, 105 are identical to the pre-change
binary. `production_all` is untouched and still publishes its incomplete CB
answer on 7499; the CB `≥n` recognition gap is a separate open defect.

Tests: `routing.rs::the_abox_dropping_card_race_is_never_selected_automatically`
(no profile shape reaches the route through `select`) and
`abox_consistency.rs::derived_abox_contradictions_are_not_detected`;
`frontend/profile.rs::clause_retained_role_constraints_stay_out_of_the_number_component`
(7499-shaped source certifies, chain-connected ABox splits the two halves) plus
eight new fail-closed sources in the existing certificate test;
`orchestrate/cb_to_ht.rs::clause_retained_fences_and_write_only_universal_super_are_certified`
(write-only universal super admitted, a body occurrence declines, every
non-retained fence reason declines);
`orchestrate/race.rs::clause_retained_fences_keep_the_card_arm`; and the routing
tests for the new bundle, its route keys, its names, and the three-way selection.
No Lean re-certification: this changes procedure eligibility and worker input
composition, not a CB-calculus derivation.
### Exact incremental direct-HT classification (2026-07-23)

Extended `IncrementalClassifier` with an explicitly selected hypertableau
backend for the validated direct-clause fragment. The Rust API accepts
`Some(IncrementalBackend::Ht)`, and JSONL `init` accepts `"backend":"ht"`.
The default EL-first/CB-fallback policy remains unchanged. The direct HT gate
rejects every normalized clause set whose complete semantics would require
orchestration side state, including ground/ABox individuals, inverse roles,
datatypes, chains, transitivity, nominals, route fences, and side-cardinality
descriptors.

The backend retains global consistency, per-class satisfiability, and
subsumption-countermodel probes. Addition reuses monotonic UNSAT verdicts.
Removal reuses monotonic SAT verdicts. A concept/role/Skolem-function component
graph preserves probes disconnected from a changed clause, while replacements
freshly check every affected probe. Empty-body and top-body changes invalidate
all components. Full completion graphs are retained only for global and class
probes; pair probes retain Boolean evidence without quadratically duplicating
the graph. The complete candidate state is built before the clause store,
revision, or id allocator changes, so a declined probe leaves the live session
byte-stable.

Stable-layout additions can also replay opaque clash-free completion graphs.
The adapter keeps old branch choices as witness facts, clears historical
dependencies and worklists, and replays every node, concept, and edge through
the enlarged trigger indexes. A completed replay is a SAT certificate for that
probe. A clash or any uncertain replay result falls back to the ordinary fresh
HT search and is never interpreted as UNSAT. The change reuses completed
evidence around the existing HT procedure and does not alter its rules, so it
needs no Lean re-certification.

Six focused release tests compare every committed HT revision with fresh HT
and CB classification. They cover successful model and existential-edge
replay, deletion and replacement invalidation, a replay clash that requires a
fresh probe, global inconsistent-to-consistent deletion, JSONL backend
selection, and atomic rejection of unsupported updates.

The exact staged source passed all 21 EL/CB/HT incremental integration tests
and the full release library gate on `ws`: 1,681 passed, 8 ignored, and 0
failed.

### Exact definition-containment closure: the last ORE 9540 completeness miss (2026-07-26)

v51 (exact job `49443541`) finishes 9540 in 0.97 s / 117 MB and matches 65 of the
66 gold pairs with no extras. The one miss is `UJI_Wall ⊑ Possible_UJI_Wall`.

Diagnosis. Only **4** of the 66 gold pairs are outside the told (asserted-name)
closure, and all four have the same shape: one class's definition conjunct set is
a strict subset of another's —

```
Possible_UJI_Wall ≡ Object_type ⊓ (4 colour hasValues) ⊓ ∃is_completely_inside.Image_type
UJI_Wall          ≡ Object_type ⊓ (the SAME 4 hasValues) ⊓ ∃has_shape.Quadrilateral
                                                         ⊓ ∃is_completely_inside.Image_type
```

Three of them are reached by the completion, because the trigger chain of the
absorbed reverse implication is deterministic. The fourth runs through the
shared colour DISJUNCTION, so the subsumer is carried only by the branch the one
completion model committed to. The logs show the consequence exactly: the
`UJI_Wall` subject arrives at the verification phase already
`result_satisfiable_derivated` (`BRIDGE-KPSET-DERIVED subject 292: 2 candidates`)
with its told subsumer plus one non-absorbable equivalence, so
`Possible_UJI_Wall` was never a candidate, never tested, never emitted — no pair
probe can recover a candidate that was never generated. This is a
CANDIDATE-GENERATION hole, not a search or reuse defect: the prepare/verify
driver and the derived-candidate path are byte-identical to the pre-reuse commit,
so the v45–v51 reuse work changed nothing here. It only made the whole 66-pair
panel finish, which is what exposed the hole.

Fix. `source_named_subsumer_closure` now computes the EXACT, search-free part of
the subsumption relation instead of only the told part. Two rules, both decided
by set containment on the source axioms, applied to a fixpoint so each feeds the
other and the result is transitively closed:

* TOLD — `N ⊑ … ⊓ M ⊓ …` with `M` named ⇒ `N ⊑ M` (the previous behaviour).
* DEFINITION — whenever the source proves `D ⊑ M` (an equivalence side, or an
  inclusion whose right side is the named class `M`) and every top-level conjunct
  of `D` is already known for `N`, then `N ⊑ ⨅conj(D) ⊑ M`.

`And` is a `BTreeSet` in the source syntax, so equal conjunctions are
syntactically equal — the same identity the terminology builder's `concept_cache`
relies on to share one `ConceptId` between the two definitions. No name, tag, or
ontology-specific test is involved. The rule is directional by construction:
`conj(D_M) ⊆ conj(D_N)` justifies `N ⊑ M` only, and the converse needs both the
opposite containment and a definition for `N`.

The pairs enter through the existing seed point, so they are emitted AND land in
the known-subsumer set — they remove pair probes rather than adding any, which
keeps the v51 performance path intact. Nothing in the DDB/discard configuration
changes; unsafe DDB discard stays default off. Structural conjuncts are interned
only where a definition body tests them, and each sweep starts from the smallest
witness set of a single conjunct, so a large source TBox pays for definitions
that can actually match instead of for every conjunct.

Replaying the two rules over `ore_ont_9540.owl` reproduces the gold taxonomy
exactly: 66 of 66 pairs, no extras, including all four non-told pairs.
Regressions: `source_closure_derives_definition_containment_transitively_without_the_converse`
pins the exact derived set on a minimized fixture (definition containment with a
shared disjunction, a told superclass on the subsumee, and a told subclass
underneath it) and `definition_containment_subsumers_reach_the_classification_output`
carries the same fixture through `bridged_classify` on both the plain and the
saturation route.

### Konclude backend-expansion reuse: wire the missing activation site (2026-07-26)

v50 (exact job `49443083`) is behaviourally identical to v49 — 309 910 branch
points on retained nodes, 697 628 on fresh ones, timeout — so the Stage-9 reuse
replay never activates. Cause, from the upstream lifecycle: Konclude activates
the mechanism from **two** places, both funnelling into the activation tail of
`initializeIndividualNodeWithBackendCache` (cpp 22736-22771) —
`getUpToDateIndividual(cint64)`'s CREATE path (cpp 22524-22527) and
`initialNodeInitialize` (cpp 8713-8730), which runs for every node actually
taken off a processing queue. Stage 9 wired only the first. A retained class job
COW-inherits the whole ABox individual-node vector
(`CProcessingDataBox.cpp:451-453` for the queues, jobgen `clearIndiProcessingQueue`
for the clears), so it never materializes an individual and never reaches that
site.

`u25::activate_backend_individual_expansion_reuse` is now the shared activation,
called from both sites; `u03::individual_node_initializing` is the one a retained
job reaches. It stays strictly lazy — nothing walks the association set, so the
198 retained roots are not scheduled up front, and a node is decided only when a
rule actually reached it. A mere id RESOLUTION (`u16::is_nominal_individual_node_available`,
merge/link resolvers) deliberately does not activate; the lazy-lookup HIT path
only counts undecided associations.

Konclude's per-node one-shot (`isNominalIndividualRepresentativeBackendDataLoaded`
+ `isBackendConceptSetInitialized`) cannot be reused verbatim: both bits are
COW-inherited (`CIndividualProcessNode.cpp:272/426`) and are still false on a
Konclude class job only because its base is `statCalcTask->getRootTask()`
(`CSatisfiableTaskConsistencyPreyingAnalyser.cpp:55-56`) — the consistency task
at the FIRST fork, where most ABox nodes were never initialized. KM initializes
every ABox individual eagerly before any fork, so on a KM retained base both
bits are already set. The port therefore keeps the one-shot per calculation job
(`native_reuse_activated_individuals`, cleared with the algorithm and on every
replay re-install), which has the same "at most one reuse decision per
individual per job" semantics.

A RETAINED node with a PENDING reuse decision defers its round instead of
draining its inherited concept-processing queue, so the recorded model is adopted
(or explicitly discarded) before the individual opens its first disjunction. The
deferral is scoped to nodes below the retained watermark — a node this job
materialized has no inherited queue and keeps Konclude's exact fall-through
timing. Nothing is lost: the concept queue is untouched,
`take_next_process_individual` Probes 19/34 drain the reuse queue (Probe 18
always selects prioritized mode, so `take_next` cannot return NONE while that
queue is non-empty — no starvation, no premature fixpoint), and
`individual_node_conclusion` re-queues the node afterwards. The two-way branch
and the fail-closed representability gate are unchanged; the unsafe DDB refuted
discard stays default-off and env-gated.

Exact activation counters on `CompletionTaskHandleAlgorithm` split "never
reached" from "reached and declined" per gate — reached / queued / drains /
forks / replays / defers / lazy-hits, and repeat / no-record / no-elements /
unrepresentable / state / check-pass / check-decline. They are asserted by the
selftests; nothing prints them.

Source-only change: seven new selftests, no build, benchmark, or run numbers.

### Konclude backend-expansion reuse: replay the retained ABox model (2026-07-26)

Ported Konclude's `checkIndividualBackendExpansionReuseable` (cpp 25010-25086)
and `reuseIndividualBackendExpansion` (cpp 25092-25373) plus the prioritized
reuse branching (cpp 24916-25003) into `konclude_ht::completion::u25`, live
against the typed native-ABox association.

A derived task (a class job) starts from the DETERMINISTIC consistency root, so
the consistency model's non-deterministic ABox state is not in the inherited
graph — it lives only in the published backend associations. Without this
replay every class job re-derives it disjunct by disjunct; the v49 search-site
read-off on `ore_ont_9540` measured 312 052 branch points opened on retained
ABox nodes against a 326-node retained base, where Konclude opens none.

The replay adopts the recorded merges, chosen disjuncts, neighbour-role links
and distinctions in ONE step, under a single NON-deterministic dependency track
point installed as alternative 0 of a two-way branch whose alternative 1
discards the reuse and keeps the ordinary expansion. It never writes at the base
dependency and never touches the deterministic label replay, so a clash under
the adopted model backtracks into normal search instead of being reported as an
entailment. A typed record that is not fully representable is discarded rather
than partially replayed. Konclude's label-size late-dynamic activation
thresholds are deliberately not ported.

Type-checked only; no build, benchmark, or coverage numbers yet. Full rationale,
soundness invariants and the pending measurement are in
`diagnostics/9540-konclude-trace/ANALYSIS.md` "Stage 9".

### Retained-state incremental CB insertion and exact deletion (2026-07-23)

Extended `km incremental` from its lower-level addition-only EL++ store to an
exact general `IncrementalClassifier`. Pure-EL additions retain the existing
completion fixpoint. Disjunctive, equality, nominal, and supported cardinality
normal forms route to the CB worker. Ordering-stable monotone CB additions now
deep-fork and resume the completed context graph: they append ontology indexes,
invalidate shared closures and nominal shortcuts, replay every active old
Hyper side, and send new consequences through the ordinary Eq, Factor, Join,
Succ, Pred, and message-fixpoint paths. Successful receipts report
`strategy: cb_delta` and retained answer/edge counts.

The preflight uses an exact rebuild when an insertion changes an existing
trigger-sensitive ordering, changes automatic definer-disjunction routing,
adds an asserted ground equality that changes the deterministic quotient, or
adds a named-individual fact without the historical demand-seeding record,
promotes a direct `C -> bottom` signature shortcut, or would collide a later
input individual with an allocated additional nominal. One-shot
split/root-ordered/query-subset routes also rebuild. Every deletion or
replacement still rebuilds because CB does not retain the derivation
dependencies needed for safe retraction.

Initial clauses and accepted additions receive stable, non-reused ids.
`remove_clauses` deletes by id, while `apply_change` and the JSONL `change`
command combine deletion and addition in one atomic revision. A candidate that
drops a clause, reaches a resource backstop, refers to an unknown id, or repeats
a removal id is rejected without changing the live result or id allocator. The
JSONL parser also rejects unknown side-channel fields instead of ignoring data
that this direct clause API cannot classify.

Differential tests compare every accepted retained CB revision with a new
`km engine` process and every EL revision with fresh EL classification. They
cover multi-revision disjunction, normalised role-chain recognition, new
symbols/functions/successor contexts, ontology facts, equality-based number
restrictions, new and existing nominals, EL-to-CB and CB-to-EL transitions,
removals, and atomic replacement. After a successful delta, unsupported input
and a forced message-backstop failure both leave the serialized live answer,
revision, and ids byte-identical; a later retained delta still matches fresh.
This changes scheduling/state ownership around the same monotone calculus
rules, so it needs no Lean re-certification.

The original snapshot foundation passed the full release test suite in IBEX
job `49338486`: 1,627 tests passed, 8 ignored, and none failed. A
five-repetition single-thread EL microbenchmark
in job `49338646` retained 50,000 facts while adding one clause to a
10,000-clause snapshot. Its median update latency was 14.8 ms, versus 72.6 ms
for a fresh `km elc` union worker. This 4.90× end-to-end synthetic result
includes fresh-worker startup, parsing, and serialisation and is not a corpus
performance claim.

The retained-CB revision passed the full release suite in IBEX job `49340558`:
1,620 tests passed, 8 ignored, and none failed. IBEX job `49340574` measured
the retained CB path on 1,001 initial clauses: a five-repetition median delta
took 3.14 ms and retained 1,500 answer pairs, versus 25.67 ms for a fresh
`km engine` union process (8.18× end-to-end). The
fresh measurement includes process startup, parsing, and serialization; this
is a synthetic scale check, not an ORE claim.

### Addition-only incremental EL++ classification (2026-07-22)

Added `IncrementalElClassifier` and the `km incremental` JSONL session. An
accepted transaction adds normalised EL++ clauses, retains the old completed
subsumption relation and role graph, rebuilds rule indexes, and replays retained
facts so newly enabled consequences enter the ordinary completion worklist.
Unsupported and non-EL updates are rejected atomically.

The compact normal-form translation has one non-monotone corner: adding the
filler half of a previously one-sided Skolem existential replaces
`A ⊑ ∃R.⊤` with `A ⊑ ∃R.B`. The session compares direct normal-form sets and
starts a fresh completion for that transaction instead of retaining the old
top edge. Eight focused feature tests compare incremental results with fresh
completion and cover role inclusions, chains, conjunction, bottom propagation,
reflexivity, inconsistency, transaction rollback, and this restart path. IBEX
jobs `49307560` and `49308032` also pass the existing EL tests and exact-source
feature suite. Batch classification and calculus rules are unchanged, so no
Lean re-certification is required.

### Verified multiple explanations and OWLAPI adapter (2026-07-23)

Extended `km explain` from one deletion result to deterministic hitting-set
enumeration of source-level justifications for named-class subsumption,
named-class unsatisfiability, and ontology inconsistency. Every published
support completes minimisation and is then reclassified as the exact final
source subset. Check-limited unfinished candidates are discarded. Schema 2
reports per-support verification/minimality, separate check and justification
limits, enumeration completeness, and the source prefix declarations needed
to parse abbreviated functional syntax.

Every candidate enters `auto`; manual and forced matrix procedures are rejected.
Route declines, relevant dropped clauses, and worker errors stop extraction.
The oracle was exercised end to end over exact EL completion, the admitted CB
fragment, and the validated DL-safe-rules HT consistency stage. An internal
consistency certificate lets an inconsistency query retain the exact rules-HT
verdict even when the later taxonomy-only fall-through drops an ABox clause;
it does not relax dropped-clause checks for taxonomy queries.

The Protégé 0.3.0 module now implements OWL Explanation API 2.0.1
`ExplanationGenerator` and `ExplanationGeneratorFactory`, with Java
`ServiceLoader` metadata. It flattens loaded imports, invokes schema 2, parses
each returned source node into an `OWLAxiom`, verifies membership in the
flattened source, and fails closed on native errors and bounds. Dependencies
are pinned to OWLAPI 4.5.29, OWL Explanation 2.0.1 with its telemetry 2.0.0
runtime, Protégé 5.6.6, and Gson 2.11.0. The bundle registers a native provider
for Protégé 5.6's core Explain action. Its asynchronous panel exposes
cancellation, the justification bound, source axioms, verification/minimality
status, and complete-versus-bounded enumeration status. The separate
Explanation Workbench has no custom-factory
extension point, so KM does not claim a Workbench registration. Headless Java
tests cover EL alternatives, named UNSAT, CB inverse reasoning, rules/HT
inconsistency, exact unsupported-query rejection, bounds, service discovery,
controller cancellation, and plugin registration/package contents.

Normal classification performs no explanation work. The change alters
orchestration and adapters, not CB rule applicability, so it needs no Lean
re-certification.

### Defer inverse negative-existential mirrors in the HT bridge (2026-07-22)

The HT bridge previously returned a completed classification for ORE 4669 even
though targeted HermiT satisfiability checks refute all 64 sampled named-UNSAT
claims. A later scheduling change removed those false UNSAT claims but exposed
only the incomplete positive projection. The ontology contains 36,495 named
definitions of the form `N ≡ ¬∃R.F`, represented in source NNF as
`N ≡ ∀R.¬F`, together with inverse-role feedback. The bridge does not yet
reconstruct the complete contravariant mirror hierarchy or verify every
cross-region consequence in this fragment.

`bridged_classify_opts` now detects this semantic source pattern and returns
`None` before bridge search whenever inverse roles are present. Automatic
routing can continue to a complete fallback; a forced bridge route reports
unsupported instead of publishing a known false or incomplete taxonomy. The
guard is based on the source fragment, not the ORE ontology identifier.

IBEX job `49307561` built the release binary and passed the focused regression.
On ORE 4669, forced `ht_bridge` exits 3, writes no taxonomy to stdout, and emits
the expected unsupported diagnostic. A source scan found complemented
existential syntax in 26 ORE inputs, 21 of which also mention inverse roles;
this is therefore documented as a fragment-level safety fence. The change
only narrows route eligibility and derives no new calculus consequences, so it
requires no Lean re-certification. ORE 4669 remains unclosed until KM gains the
missing exact mirror mechanism or another complete route.

IBEX array `49309622` then compared frozen main and the integrated feature
binary under automatic routing on all 21 inverse-role inputs from that scan.
All tasks completed at 240 seconds and 20 GiB per run. Twenty ontologies have
identical terminal status and signature. The sole difference is ORE 4669:
frozen main emits the retained nonclaim signature
`dba27c20589ec186e858119dbac18f6e79afb4da001ef16c232feb28231f37dd`,
while the guarded binary reaches the limit without publishing a taxonomy.

### Preserve legal source classes named Thing or Nothing (2026-07-18)

ORE 3524 and 15703 each lost 123,310 strict told subsumptions because their
legal nested source class ends in `#Thing`. ORE 13503 similarly lost the named
UNSAT class `http://www.daml.org/2001/03/daml+oil#Nothing`. The frontend reduced
each full IRI to its last fragment and then treated bare `Thing` or `Nothing`
as OWL top or bottom.

Builtin recognition now tests the complete source identity: only
`owl:Thing`, `owl:Nothing`, and their full W3C IRIs become semantic constants.
Non-OWL source classes with reserved spellings receive collision-safe
`km_src_*` internal names, and the inverse registry restores the exact IRI in
public output. The Python reference frontend and output path mirror the same
ownership-aware rule. A small end-to-end Rust regression checks the told-edge,
named-UNSAT, and 7581 coexistence cases.

After rebasing onto the latest active branch, IBEX job 49088657 passes 1,597
Rust library tests with zero failures and 8 ignored, all 8 integration tests,
and 6 Python parity tests. Fixed `production_all` runs in job 49088661 then
match fresh full-IRI Konclude fingerprints exactly:

| Ontology | Wall (s) | Peak (MB) | Pairs | UNSAT | Full-IRI taxonomy SHA-256 |
|---|---:|---:|---:|---:|---|
| 3524 | 27.7082 | 4600.92 | 1,604,386 | 0 | `090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a` |
| 15703 | 24.4224 | 4350.15 | 1,604,386 | 0 | `090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a` |
| 13503 | 0.0618 | 7.10 | 113 | 1 | `1b8fdf730b9cdce8afed1c69c13e782c6c2dde70c42e5f1d2273dcbdb6b1282b` |
| 7581 regression | 19.4446 | 4318.46 | 1,246,911 | 0 | `27a29aab966ffea74df4aa09c0520545f5908c9fc8e3fc5d10cd3e027b9118d4` |

The giant-specific checker confirms all 123,310 strict told target edges are
present in both 3524 and 15703. HermiT independently confirms the 13503 named
class is unsatisfiable. The regenerated 592-row route registry now contains
586 exact-gold rows, 2 additional adjudicated-correct rows, 1 completed but
unsound row, and 3 rows without a complete validated route. Validated KM
coverage is 588/592. This changes frontend symbol encoding, not CB-calculus
derivations, so it requires no Lean re-certification.

### Complete `43bce75` sweep and rejected 1194/9635 candidates (2026-07-17)

Immutable candidate `43bce75` completed all 592 production tasks on IBEX. The
final evidence set contains **582 ok, 6 timeout, 3 memout, and 1 unsupported**;
against the retained Konclude signatures it contains **576 exact matches, 2
incomplete, 2 consistency mismatches, 1 unsound, and 1 no-gold** among the
successful runs. This has the same terminal-status distribution as `a639ab5`.
The only verdict change is ore_ont_11745 (`unsound` to exact), caused by the
correct tab-delimited gold loader rather than an engine change. The two worker
rows lost to whole-step OOM, ore_ont_3524 and ore_ont_15703, were finalized only
after explicit Slurm `OUT_OF_MEMORY` evidence; all 592 rows carry one binary SHA
and one runner SHA.

Ore_ont_13503 is not stable enough for a single-run correctness claim: the same
immutable `43bce75` binary matched gold in the focused panel but emitted one
extra unsatisfiable local name (`Nothing`) in the complete sweep; `feb0cc6`
reproduced the latter signature. Treat this as a nondeterministic correctness
defect and require repeated identical signatures in future acceptance panels.

Two follow-up implementation candidates were rejected after real-ontology
tests. Sharing seeded-closure head indexes across contexts passed the complete
library suite (1,588 passed, 8 ignored) but ore_ont_1194 still exceeded the 20
GiB cap (20,483 MiB, 89.5 s). Re-deriving forced-successor role-domain facts
during Ht re-drive passed four focused release tests but ore_ont_9635 still
missed `FiniteSemanticStructure ⊑ FiniteRuleSetModel`. Both changes were
reverted; their commits remain in history as diagnostic starting points.

A subsequent clause-level trace established the complete missing 9635 chain:
`FiniteSemanticStructure` implies the exact-one definer `Q_19`; `Q_19` creates a
`hasUniverseOfDiscourse` successor; that role's domain implies `RuleSetModel`;
the resulting conjunction recognises `FiniteRuleSetModel`. Eagerly resolving
the successor generator with its domain added 12 sound clauses but timed out;
restricting the transformation to the single directly useful clause
`Q_19(x) -> RuleSetModel(x)` still changed the formerly terminating run into a
190.7 s internal engine timeout at about 6.7 GiB. The experiment was reverted.
The next 9635 implementation must preserve this recognition outside the CB
context explosion, or fix successor-domain re-drive in the validated Ht route.

The sweep also exposed a scorer resource bug on ore_ont_10689 (14.8 million
canonical subsumptions): the runner parsed KM's JSON taxonomy twice and then
materialized a second complete gold set after reasoner timing ended. Scoring
alone took the Slurm task to 6:40 and about 13.7 GiB. The content-addressed
runner now keeps only the canonical summary and streams sorted gold rows,
computing extras as `output_count - matched_count`. Synthetic differential
cases match the original two-set comparator, including empty local names,
UNSAT differences, and consistency differences. A real ore_ont_9635 run also
validated the corrected immutable-set path. This changes benchmark
post-processing only, not KM output or measured reasoner time/memory.

### DL-safe rule fragment: SameIndividual fires; precise 3-tier contract (2026-07-17)

Audited the full DL-safe rule contract against the ORE 10860 rule set (the 17
`DLSafeRule` axioms partition into **8 pure Class+Role**, **5 Class+Role+Diff**,
and **4 Data/BuiltIn** — greaterThan on dates, `hasClass`/`isSubClassOf`
built-ins). The rule pipeline had two divergent notions of "supported": the
parser/`collect_rules` contract accepted `SameIndividual`/`DifferentIndividuals`
atoms, but `cb_to_ht::build_rule_clause` then **silently dropped** any rule
carrying one (returned `None`). A `SameAs`-guarded rule was therefore presented
as classified while its guard was ignored.

Changes:
- **`SameIndividual` now fires** (the largest soundly-representable shape that
  was being dropped). A *body* `SameAs(u,v)` guard unifies u and v onto one
  Subst variable via a union-find over rule terms (both `__nom__` pins land on
  the shared node); a *head* `SameAs(u,v)` emits `HAtom::Eq` so the rule derives
  the equality. Sound: a single O-guarded node trivially satisfies u ≈ v, and
  any binding where the two individuals coincide collapses onto that node.
- **`DifferentIndividuals` is an explicit, documented deferral.** The fast Ht
  tracks no node distinctness (`HAtom` has only Concept/Role/Eq/Exist), so a
  `u ≠ v` guard has no sound encoding; the rule is dropped at firing and counted.
  Dropping a rule from the one-sided consistency precheck is sound (a lost
  constraint can lose an inconsistency, never invent one), so a Diff-bearing
  rule must NOT decline the route — that would forfeit the fired rules that
  detect the 2669/15516 clash.
- **Data/BuiltIn/DataRange and complex-class atoms still DECLINE the route**
  (strict defer). These are concrete-domain obligations with no DL encoding; the
  parser omits the AST rule, `parsed < source`, and `collect_rules` rejects. This
  keeps ORE 10860 the honest 0.01 s decline (4 of 17 rules use SWRL built-ins),
  as intended — no partial-firing of a datatype ontology.

Regression-safe: 2669 (5 pure fire, 3 Diff deferred) and 15516 (2 pure fire) are
byte-identical; rule-free ontologies are untouched (`build_rule_clause` runs only
under `ht_rules`). The Ht encoding change needs no Lean re-cert (the CB calculus
is unchanged; this is the HT bridge). Tests: parser (SameIndividual parses;
Data/BuiltIn/DataRange drop the rule), encoding (body-guard unification, head
equality, Diff deferral, individual pinning, pure-rule regression), contract
(SameAs accepted, Diff does not decline, mixed corpus accepted, built-in corpus
declines), and end-to-end reasoning (a `SameAs` guard fires on a merged node to
drive a disjointness clash, and does NOT fire without the merge).

Quantified: of the 6 ORE `DLSafeRule` ontologies, the soundly-representable
firing fragment grows from {Class, Role} to {Class, Role, SameIndividual}; the
`DifferentIndividuals` and datatype/built-in shapes remain out of the sound
fragment and are handled by explicit deferral (Diff) or honest decline (built-in).
ORE 10860 is not closed (its built-in date/subclass rules need a concrete domain).



### Incremental CB indexes and interning hot paths (2026-07-17)

Three fixpoint-preserving CB optimizations from the parallel review cycle are
integrated for the next production candidate. Back-subsumption now removes a
discarded worked-off clause from each affected posting instead of rebuilding
every head index. Differential tests compare the incremental state with a full
rebuild for concept, role, ground-endpoint, body, bridge, and merge indexes.
Context-core indexes now store a content hash and collision bucket of context
ids rather than a second owned copy of every `Vec<Pred>` core; exact core
comparison still resolves every lookup. Context-clause insertion also reuses
the hash calculated by its failed lookup instead of hashing new clauses again.
These changes alter storage and enumeration cost only, not rules, ordering,
redundancy, or the derived fixpoint, so they require no Lean re-certification.

### Reject positive-CCEQ trigger candidate after complete sweep (2026-07-17)

Immutable candidate `a0d0148` was built on an IBEX compute node, passed 1,584
release tests plus a 19-ontology sentinel panel, and completed all 592
production tasks as job `49014377`. The candidate left ore_ont_9635 incomplete
on the same missing `FiniteSemanticStructure` to `FiniteRuleSetModel` pair and
regressed ore_ont_9724 from exact completion to a 20 GiB memout. The trigger
change was therefore reverted. Correct tab-delimited gold parsing independently
establishes ore_ont_11745 as exact and raises the current verified route union
to 577; this is a harness correction, not a benefit of the rejected engine
change.

### Bind production rows to the exact benchmark runner (2026-07-17)

Production tasks now accept a content-addressed `SWEEP_RUNNER`, record its path
and SHA in the manifest, and reject result or checkpoint rows whose
`runner_sha256` differs. The evidence-gated OOM finalizer also requires the
runner and records its SHA. Tests verify both runner identity and refusal to
finalize a missing row without explicit Slurm OOM evidence.

### Keep the strict sweep comparator runnable on IBEX (2026-07-17)

`compare_production_sweeps.py` now computes arithmetic means with `sum/len`
instead of `statistics.fmean`, which is unavailable in IBEX's Python 3.7. The
formula is identical for the finite benchmark measurements. This allowed the
strict 592-row SHA and terminal-status comparison for production job
`49012346` to run on the host that stores the immutable datasets.

### Fix false `unsound` verdict on ore_ont_11745 (empty local-name gold rows) (2026-07-17)

`ore_ont_11745`'s lone remaining `unsound` verdict was a benchmark-harness
artifact, not a reasoner error. KM's classification of the ontology is exact:
under both the authoritative `ore_aggregate.load_sig` and `ore_canon`, KM's
output equals the Konclude gold signature (438277 subsumptions, 1592
unsatisfiable classes, consistent), matching Konclude, ELK, and HermiT.

Root cause: the ontology has a class whose IRI ends in `#`,
`<http://purl.org/obo/owl/UniProtKB#>`, whose canonical local name is the empty
string. Its subsumption `UniProtKB# ⊑ PRO_000003147` is written to the gold
`.sig.gz` (by `ore_runone.py`) as the tab-delimited row `\tPRO_000003147` — an
empty left field. The routing-matrix runners' `load_gold`
(`bench_one_matrix_frozen.py`, `bench_one.py`) parsed rows with `line.strip()`
(which deletes the leading tab) followed by whitespace `line.split()` (which
discards empty fields), so this one pair vanished from the parsed gold while
every reasoner's own canonicalized output still contained it. Result: a phantom
`extra=1` and a false `unsound` verdict for KM, Konclude, ELK, and HermiT alike
(observed identically across all four in matrix `c229366f`).

Fix: parse the signature faithfully as tab-delimited rows (`line.split("\t", 1)`
after `rstrip("\n")`, guarded by `"\t" in line`), exactly as the authoritative
`ore_aggregate.load_sig` and `results/router-sweep-harness/fast_soundness.py`
already do. General (fixes any ontology with a `#`/`/`-terminated class IRI),
alters no gold, special-cases no ontology, and never drops a genuine entailment.
Regression test: `results/benchmarks/2026-07-15-routing/
test_load_gold_empty_localname.py`. The same latent `line.split()` pattern
survives in the archived `2026-07-14-9663-closure` analysis scripts, which do
not produce verdicts and are left untouched.

### End-to-end restoration guard for chain-domain recognition (2026-07-17)

Adds `engine/tests/chain_domain_route.rs`, an integration test that locks in
the role-chain domain recognition restoration for ORE 11745 at the `classify`
level, plus the fixture `engine/tests/fixtures/chain_domain_unsat.ofn` (a copy
of the HermiT-confirmed witness `oracle/ontologies/11745_unsat_core.ofn`). With
a scrubbed `KM_*` environment the witness must classify inconsistent
(`GO_0008046` unsatisfiable); with `KM_NO_CHAIN_DOMAIN=1` it reverts to the
historical under-detection (consistent). Test-only, no engine or calculus
change — off-flag behaviour and every other route are untouched.

Motivation from the historical-restore audit: the existing clause-level tests
(`domain_consumer_chain_recognition`,
`domain_consumer_transitive_chain_recognition` in `src/frontend/preprocess.rs`)
verify the recognition *builder* in isolation, but nothing guarded that the
pass is actually wired into `classify` and enabled by default. Losing that
wiring would again omit 11745's unsatisfiable classes. This is separate from
the false `extra:1` verdict above, which came from the gold loader. The new
suite fails closed if the default is ever silently flipped or the pass is
unwired. Verified locally: both directions pass (default → inconsistent,
opt-out → consistent) on a HEAD `km classify` build.

### Skip unchanged role-successor cross scans (2026-07-17)

The CB engine now runs its semi-naive successor×reach cross-step only after
the reach set grows or a successor edge is inserted or re-targeted. Unrelated
context churn previously rebuilt the successor vector and scanned every edge
even though every edge high-water mark already equalled the reach length. The
guard changes only scheduling: it suppresses scans that can emit no messages,
so the derived fixpoint is unchanged and no Lean re-certification is needed. A
differential schedule test compares the gated and unconditional drivers across
edge growth, reach growth, re-targeting, unchanged re-insertion, and idle
rounds; both emit the same ordered message triples and final pushed set.

### Recognise OWL bottom by namespace, not local name (2026-07-17)

The CB adapter and classification readout now recognise only canonical OWL
vocabulary spellings of `owl:Nothing` (plus `⊥` at readout). A user-defined
class in another namespace whose local name is `Nothing` remains an ordinary
named class. This removes a spurious inconsistency and unsatisfiable-class
classification without changing the calculus. Focused tests cover both the
adapter and output boundary.

### Report directly-unsatisfiable named classes (2026-07-17)

A direct `C ⊑ ⊥` axiom marks `C` as a bottom-equivalent concept during CB
ontology construction. That correctly removes `C` from the saturation query
set, but the readout then omitted `C` from the classification because it had no
root context. `Engine::subsumptions` now emits `C ⊑ owl:Nothing` for every real
named class with that marker, excluding the canonical bottom and internal
proxies. Saturation and the derived closure are unchanged. A focused regression
test covers direct and inherited unsatisfiability without flagging unrelated
satisfiable classes. The agent's 41-ontology agreement panel had 40 identical
outputs, one skipped input, and zero regressions.

### Process-tree memory watchdog: always publish a terminal row (2026-07-17)

The production sweep enforced the 20 GB reasoner cap by polling the reasoner
*process group* every 40 ms and killing it on the sample. On the fast-blowup
giants (ore_ont_3524, ore_ont_15703) a giant can allocate several GB between two
samples, so real RSS crossed the 28 GB Slurm hard limit before the poller ever
observed 20 GB. The cgroup OOM-killer then fired, and under Slurm's
`memory.oom.group` it took the whole step, the Python supervisor included, so no
memout row was ever written. The sbatch sanity check then failed under `set -e`
and the array task stayed permanently unfinished on those ontologies.

New `oracle/ore/tree_watchdog.py` replaces the group poller with a watchdog that
enforces the same 20 GB measured cap without giving the reasoner more memory:

- Measurement is over the full process *tree* (descendants by PPID) unioned with
  the process group, so a worker that leaves the group via `setsid` still counts
  toward the cap. `/proc/<pid>/stat` is parsed relative to the final `)` so a
  `comm` holding spaces or parentheses no longer mis-indexes RSS.
- The cgroup's own accounting (`memory.current` on v2, `memory.usage_in_bytes`
  on v1) is read every tick as a race-free backstop, using the reasoner's growth
  since start so a shared cgroup baseline does not false-trip. It stops the run
  as a memout at cap plus a small supervisor headroom, well below the 28 GB hard
  limit, before the kernel OOM-killer can reach the supervisor.
- The supervisor lowers its own `oom_score_adj` and raises the reasoner's, so in
  the non-group cgroup case the kernel prefers the reasoner as victim.
- On a trip the terminal row is checkpointed to a durable, attempt-independent
  path *before* the kill. `production_full_sweep.sbatch` salvages that checkpoint
  (same attempt, or a later array attempt) so a genuine 20 GB blow-up publishes
  its memout row once and is never retried forever. An unsolicited SIGKILL near
  the cap now reads back as a memout, not an error, and the frozen runner always
  prints exactly one terminal JSON row.

Validated by `oracle/ore/test_tree_watchdog.py` (12 synthetic cases: tree-walk
beats the group poller on a setsid escapee, robust stat parsing, cgroup v1/v2
delta accounting, SIGKILL of a SIGTERM-ignoring child, timeout, and an
end-to-end runner run that emits one memout row plus a matching durable
checkpoint). The measured cap and `--mem` allocation are unchanged.

### Absorb the production portfolio's CB fallback clause set (2026-07-17)

`ore_ont_10908` is exact under the isolated `cb_absorb_portfolio16` route
(208.2 s, 1,071 MB, gold-exact 6001/6001 subsumptions; the completed follow-up
array in `results/benchmarks/2026-07-16-routing-complete592`) but times out
under the bootstrap-selected `production_all` route. Both routes run the same
always-on CB fallback (`race_absorbed_plain` inside `race_adaptive_vs_elc`),
so the gap is not the orchestrator — it is the clause set the frontend hands
that fallback.

Root cause: the frontend clausifier's polarity-gated absorption
(`normalise.rs`, `Clausifier::absorb`) reads *only* `KM_ABSORB`. It Horn-ifies
LHS disjunctions and drops the unguarded `⊤ → Q ∨ A` excluded-middle clauses,
shrinking the live-disjunction blow-up at source — this is the mechanism the
2026-06-21 ablation named the "dominant lever" (recovers 6212, 10908, 15491,
16444; 0 unsound, 0 incomplete, 0 regressions). `cb_absorb_portfolio16` sets
`KM_ABSORB=1`. `production_all` set only `KM_TRIGGER_ABSORB=1`, which leaves the
`absorb` flag off, so its CB fallback saturated the un-absorbed excluded-middle
clause set and hit the 240 s wall on exactly the disjunction family the absorbed
route closes. `KM_TRIGGER_ABSORB` alone drives the Konclude bridge, not the CB
clause encoding.

Fix (ontology-independent, no ontology identity): `production_all{,8,1}` now
carry `KM_ABSORB=1` alongside `KM_TRIGGER_ABSORB=1`, so the CB fallback is fed
the identical disjunction-shrunk clause set `cb_absorb_portfolio16` uses. The
two absorptions compose rather than conflict: `source_axioms` (the bridge's
native Konclude terminology) are recorded from the original NNF axioms gated
purely on `KM_TRIGGER_ABSORB` (`normalise.rs:1264-1306`), so polarity absorption
never changes what the bridge sees, and `mark_subclass_polarity` was already
written to keep triggered antecedents from recreating excluded-middle clauses
under `KM_ABSORB`. The card arm reads the `cardinalities` metadata (unaffected
by `KM_ABSORB`), and the CB engine is sound+complete on any equisatisfiable
encoding, so admitting absorption adds no unsound/incomplete risk. Focused
routing tests pin the composition
(`production_bundles_absorb_the_cb_fallback_clause_set`,
`automatic_sriq_route_absorbs_the_cb_fallback`).

Lean re-certification is NOT required. `KM_ABSORB` is a frontend clausification
choice, not CB-calculus logic (AGENTS.md: "the frontend is not calculus logic").
It changes which equisatisfiable clause set the engine receives, not the
saturation rules, ordering, redundancy, or what the engine derives from a given
clause set; the transform is already corpus-validated verdict-preserving. The
IBEX gate is a `production_all` A/B on the disjunction-absorption family versus
the frozen matrix, confirming the recovery and no bridge/card regression.

### Exact OWL top and bottom recognition (2026-07-17)

The functional-syntax frontend now recognizes `owl:Thing` and `owl:Nothing`
only from their standard OWL names and full IRIs. A user class in another
namespace whose local name is `Thing` or `Nothing` remains an ordinary named
class. Parsing, RBox analysis, and profile routing use the same exact test.

### Lower frontend and EL completion peaks (2026-07-17)

The frontend releases the source document before serializing its owned clause
result. Pure-EL completion releases normal-form vectors after their indexed
copies have been built and before saturation. These ownership changes do not
alter clauses, rule indexes, or derivations.

### konclude_ht bridge: stop dropping colon-localname classes from the universe (2026-07-17)

The Konclude completion bridge builds its classification universe (the set of
real named classes eligible as subjects and candidate supers) by excluding
frontend-synthetic markers and builtin vocabulary via
`orchestrate::cb_to_ht::is_internal` (`bridge.rs::bridged_classify`). That
predicate treated ANY name containing a `:` as internal. A real class whose
localname legitimately contains a colon — a URN class IRI such as
`urn:example:Foo` (for which `short` strips no `#`/`/`), or a colon-bearing
fragment such as `#Part:Whole` — was therefore silently excluded from the
universe: it was dropped as a candidate super (`subs.retain`,
`saturation_known_pairs.retain`, the `known_subsumers` filter), so no
subsumption `X ⊑ ThatClass` was ever emitted, and the drop was counted as
neither unsound nor incomplete. That is exactly the kind of silent
approximation the project forbids.

The colon clause is a proxy for builtin vocabulary (`owl:Thing`,
`rdfs:Literal`, `xsd:integer`, …). Konclude never approximates these classes
away, and the frontend's own internal-name predicate
(`frontend::iri::reserved_internal_prefix`) is prefix-based, not colon-based.
`is_internal` now excludes a colon name only when its prefix is a reserved
vocabulary prefix (`owl`/`rdf`/`rdfs`/`xsd`/`xml`) — exactly the builtins the
heuristic intends to catch — via the new `is_reserved_vocabulary_curie` helper.
The `Nothing`/`owl:Nothing` handling (owned by `is_bottom`) is unchanged.

Soundness/completeness: the change is a strict narrowing of the exclusion set,
so it can only add real classes back to the universe, never remove one; it
introduces no new subsumption test verdict. Every reserved-vocabulary builtin
the filter intends to catch remains excluded. The ORE corpus does contain
colon-localname classes (`12698`), so that ontology is a required focused
regression gate rather than a byte-identity assumption. The fix touches only
the HT-bridge feeder (`cb_to_ht`), not the production CB engine output path. New unit test
`is_internal_excludes_markers_and_builtins_but_keeps_colon_localname_classes`.
See `docs/BRIDGE-UNIVERSE-COLON-CLASSES.md`.

### Protégé 5.6 plugin refresh (2026-07-16)

The Protégé plugin now targets the Maven-published Protégé 5.6.6 API and OWL
API 4.5.29, uses the pure-Rust `km` executable without the legacy Python/moose
fallback, and reports version 0.2.0. It flattens the loaded imports closure
before classification, maps results using complete IRIs rather than ambiguous
local fragments, captures subprocess diagnostics, and enforces a configurable
timeout. Headless regression tests cover imports and duplicate local names.
The plugin guide now includes complete installation and runtime configuration
instructions for Linux, macOS, and Windows.

### Standard OWL syntax input adapter (2026-07-16)

`km classify`, `km profile`, and `km features` now accept OWL functional
syntax, OWL/XML, RDF/XML, and Turtle. The adapter detects the syntax from file
content and extension, with `--format` and `KM_INPUT_FORMAT` overrides for
ambiguous inputs. OWL/XML and RDF serializations pass through Horned-OWL's
structural ontology model before entering KM's existing functional-syntax
frontend, so every route continues to consume the same normalized clause
contract.

The adapter fails closed when RDF-to-OWL mapping is incomplete and when an
ontology contains unresolved imports. This prevents KM from silently
classifying a partial ontology. Native functional-syntax benchmark inputs keep
their existing direct path. Cross-syntax tests check that a simple subclass
ontology produces equivalent normalized clauses in OWL/XML, RDF/XML, and
Turtle. See `docs/INPUT-FORMATS.md` for the interface and licensing details.
### konclude_ht bridge: accept deterministic subsumers without a pair probe (2026-07-16)

The Konclude completion bridge's non-deterministic subject verification
(`bridge.rs::classify_one`) probed EVERY candidate subsumer with a full
`bridged_unsat(s ⊓ ¬c)` satisfiability test, including candidates that the
completion model already proved to be *deterministic* subsumers. That re-runs an
expensive probe for a subsumption that is already entailed.

Konclude never tests deterministic subsumers. Its satisfiability-message
analyser extracts the root node's branch-independent label concepts
(`branching_tag <= max_deterministic_branch_tag`,
`create_root_class_subsumption_message`) as a `TellClassSubsumption` message and
records them directly through `add_subsuming_concept_item`; only the
possible-subsumption MAP is scheduled for pair tests. The port already delivers
and processes that message (`process_class_subsumption_message`), so on a
non-authoritative subject the item's `subsuming_concept_item_set` holds exactly
those certain subsumers — but the pairwise loop could not see them, because
`candidate_state` reads the possible map, not the subsumer set.

New `SynchronousKPSetClassState::certain_subsumer(subsumed, subsumer)` reads that
subsumer set, and the pairwise loop accepts a certain subsumer directly (records
the pair, skips the probe) before the `candidate_state` / `pseudo_model_refutes`
/ `bridged_unsat` cascade. This mirrors the trust the authoritative read-off
already grants deterministic label positives (same file, the `authoritative`
branch pushes them with no probe). It is recorded like an authoritative
subsumer rather than routed through `interprete_subsumption_result`, so budget
retries recompute idempotently and no classifier propagation state is mutated.

Soundness/completeness: the extraction is branch-tag gated, so `s ⊑ c` holds in
every model of `s` — accepting it is sound, and no possible subsumer is dropped
(those still take the full probe). Default ON with `KM_HT_NO_DET_SUBSUMER=1` as a
disable hatch for a corpus A/B against the probe-every-pair path. Likely to help
the deep-hierarchy `∀ + ⊔` timeout family, where each non-deterministic subject
carries many deterministic supers that were being re-probed. See
[`docs/DETERMINISTIC-SUBSUMER-SHORTCUT.md`](docs/DETERMINISTIC-SUBSUMER-SHORTCUT.md).

Tests: `classifier/mod.rs::certain_subsumer_reads_recorded_deterministic_subsumer_set`
(certain subsumer accepted; not visible to `candidate_state`; directional;
self- and out-of-range pairs fail closed). No Lean re-certification: this is
bridge classification bookkeeping, not CB-calculus logic, and derives no new
subsumption a full probe would not have confirmed.

### Restore the additive production cardinality arm (recovers 7499 / 9540) (2026-07-16)

The 2026-07-15 "fence named HT specialists" change set the production portfolio
(`PRODUCTION_ALL`, `KM_MECHANISM=portfolio`) to `KM_HT_ONLY=certified`, which
`specialist_route_allows` narrowed to the Konclude bridge arm alone. That was
correct for policy-LEAF eligibility (the isolated `ht_card` specialist, where CB
never runs, is incomplete on ore_ont_10702 and must stay out of the learned
tree). But it also silenced the first-class cardinality arm as a CB-guarded
FALLBACK inside the production race, regressing ore_ont_7499 and 9540 back to
240 s timeouts. Those two had been recovered by the pre-fence default
(`KM_HT_CARD` on, job 48067625: 573 gold-MATCH) precisely because the card arm
runs under `race_cb_vs_ht` fallback mode, where CB is authoritative: the arm's
answer is taken ONLY when the certified CB engine times out, and the number
rules are sound, so it can only ever replace a CB timeout.

`specialist_route_allows(Some("certified"), ...)` now admits `card_candidate` in
addition to `bridge_candidate`. This is strictly the additive fallback arm, not
a policy leaf — `sriq_policy_eligible` still excludes `HtCard`, so the routing
tree cannot select the isolated card procedure. SHOQ and QO stay bridge-only
under certified: their incomplete onts (10702 / 15098) could otherwise emit a
wrong taxonomy on a CB timeout. The inverse+nominal onts on which the card route
is incomplete (10702) never become `card_candidate` because `cb_to_ht::convert`
refuses the card transform under inverse (no `card_defs` emitted), so this does
not expose that incompleteness. 15672 needs the SHOQ arm, which is entangled
with 10702's incompleteness, so it is left for a separate SHOQ-scoped change.

`KM_HT_BRIDGE_ONLY` was extended (via the new `bridge_only_worker` gate) so that
a certified worker carrying BOTH a bridge and a card arm no longer forces
bridge-only: a bridge defer now hands off to the card fallback instead of
exiting empty, matching the pre-fence single-worker behaviour. The
`card_candidate` gate is factored into `card_candidate_from` so the exact
production gate is exercised on a reduced cardinality probe. This changes only
procedure eligibility and worker composition, not any CB-calculus derivation, so
it requires no Lean re-certification. Unit tests assert the certified env bundle
keeps the card arm live, the `certified` admittance, the bridge/card hand-off,
and that a synthetic `≥2 R.C` restriction converts to a `card_def` and passes
the gate.

### Restore the validated DL-safe rule consistency precheck (2026-07-16)

The `ht_rules` procedure (named route, matrix row, and the automatic
semantic-fragment gate for rule-bearing input) lost its short-circuit on ORE
2669 and 15516: instead of the validated 0.17 s "inconsistent" verdict, both
drove a full engine run to the 240 s timeout. Root cause: the KPSet checkpoint
(`592462b`) threaded `Some(&input.rbox)` into `rules_consistency`'s
`cb_to_ht::convert` call while updating the signature. The rbox side channel
carries the source inverse-role records, and those arm the
`nominal+inverse(SHOI/SHOIQ)` classification fence, which cleared the
`__nom__` ABox seeds the consistency check exists to create. The rules
tableau then started with no roots, trivially answered "consistent", and the
rule-detected inconsistency fell through to the long CB path. Both ontologies
declare inverse roles, so the precheck never fired.

Two-part fix, both sound. First, `rules_consistency` passes `rbox = None`
again — the exact validated 2669/15516 configuration; inverse/subrole/
domain/range semantics still reach the tableau through the frontend's bridge
clauses inside the clause set, so a detected clash remains a real clash.
Second, the fence in `cb_to_ht::convert` no longer unseats nominal seeds when
`rules_active`: the fence protects classification consumers (the fast Ht has
no sound nominal+inverse completion), while the rule seeds' only consumer is
the consistency verdict, which short-circuits solely on a clash — every
tableau step is a sound consequence, so a clash is real regardless of the
fragment; a "consistent" verdict merely falls through to normal
classification. Rule-free ontologies are byte-identical (`rules_active`
requires actual rules), so the corpus blast radius is exactly the SWRL onts.

Validated on the workstation: 2669 and 15516 return `consistent=false` in
0.12–0.17 s / ~19 MB again through `--route ht_rules`, `auto`, and `manual`;
the synthetic consistent-rule control falls through and classifies its
taxonomy correctly. New tests: `cb_to_ht` unit tests (rule seeds survive an
inverse rbox and the production verdict detects the clash; the fence still
clears classification nominals without rules), a route-provenance test
(exactly `ht_rules` plus the composed portfolios keep `KM_NO_HT_RULES`
unset), and `engine/tests/rules_route.rs` end-to-end fixtures with inverse
roles (short-circuit only on inconsistency, taxonomy fall-through, automatic
route provenance). The `KM_RULES_CONSISTENCY` worker block is refactored into
`tableau::rules_consistency_verdict` so the tests exercise the production
entry without the env gate.

Rule-bearing ORE 10860 stays an honest decline, now in 0.01 s: it carries 17
`DLSafeRule` axioms and exactly 4 use SWRL built-ins (`BuiltInAtom` time/date
comparisons, with `DataPropertyAtom` operands) outside every supported rule
shape, matching the profile corpus record of 4 unsupported rule axioms. The
frontend's exact rule contract rejects the ontology
(`parsed 13 of 17`) rather than silently dropping rules, per the fail-closed
policy in docs/ROUTING.md; its gold remains unadjudicated
(docs/CONTESTED-GOLD.md: HermiT cannot parse it).

### Restore the proven KPSet bridge stack on the automatic route (2026-07-16)

The routing snapshot made `auto` the classify default whenever `KM_ROUTE` is
unset, with a bootstrap generated tree whose only leaf was `cb_plain16`. Route
normalization removes every routing key before installing the selected bundle,
so the deployed production environment (`KM_TRIGGER_ABSORB=1`, the 30 s /
0-retry bridge probe budgets, the 180 s saturation budget — exactly the
2026-07-13 ORE 3215 closure configuration) was silently erased before the
frontend ran. Without `KM_TRIGGER_ABSORB` at normalisation the frontend emits
no `source_axioms`, the source-TBox bridge candidate gate fails, and
classification degrades to the plain-CB fallback that times out on the
bridge-closed terminologies (541, 12653, 7914, 3215, 9663, 9724). The typed
`ht_bridge` and `production_all` routes themselves reproduce the closure
end-to-end (verified on a 3215-shaped SHI fixture: trigger absorption, the
saturation pre-pass, and both KPSet prepare/verify phases run, output equal to
CB); the break was confined to the default/auto path that the harness uses.

The bootstrap tree now selects `production_all` — the exact corpus-validated
production sweep configuration (574 ok / 508 exact Konclude matches, zero
gold-match regressions) — and `production_all{,8,1}` are policy-eligible for
the SRIQ core: `KM_HT_ONLY=certified` admits only the bridge's
complete-answer-or-defer path, the EL portfolio answers only on a passing
certificate, and the always-running CB engine keeps the CB-preference winner
rule, so the composition has a complete-procedure contract. The isolated
`ht_bridge` measurement row stays policy-ineligible (a defer under
`KM_MECHANISM=ht` has no in-process fallback). Focused tests pin the proven
closure environment to the production and bridge bundles
(`production_bundles_normalize_to_the_proven_3215_closure_environment`),
require the automatic SRIQ route to reach the bridge stack
(`automatic_sriq_routing_reaches_the_proven_bridge_stack`), and cover the
scheduler's immediate harvest of a finished bridge answer under trigger
absorption (`bridge_answers_are_harvested_immediately_under_trigger_absorption`,
a pure-function extraction of the race budget) alongside the existing 50,000
active-class synchronous-bridge thread reservation test.

### Root-context ordered resolution with refutation residue readout (2026-07-16, gated)

Direction A of docs/DISJUNCTION-SPLITTING.md, narrowed to the smallest sound
and complete step and implemented behind `KM_ROOT_ORDERED` (default OFF;
`1` = root contexts, `all` = every context). Same-term concept literals get a
total order (internal definers above named, iri tie-break), which restricts
Hyper to the ordering-maximal disjunct and tames the incomparable-disjunction
product closure that drives the live `∀ + ⊔` timeout family (CB-only members
10702, 15672, 6934, 9540). The known `KM_ORDERED_ALL` incompleteness — an
entailed named unit trapped non-maximal behind an unresolvable maximal
sibling — is repaired by reduction to the order-robust unsat readout: for
every named concept `B` a fresh inert complement guard `B ⊓ __notb__B ⊑ ⊥`
is injected, and every named concept occurring ordering-maximal in a query
root's worked-off heads that is not already a unit is decided by saturating
the `{A(x), NotB(x)}` context in the same engine and reading `⊥`. The
candidate set is provably complete (a refutation must fire the guard against
a NotB-free clause with `B(x)` maximal, which mirrors into `A`'s own
saturation). The nominal-enumeration shortcut is disabled under the ordered
modes (its ground-context unit readout is only validated in the default
regime). Focused synthetic tests cover the trap in both interning orders,
chained trapped supers, exclusive global disjunctions, unsat queries,
disjunction over a successor, refutation-negative candidates, and
subsumption-map equality with the default engine; the full lib suite passes
(1529/0). This CHANGES CALCULUS DERIVATIONS, so it stays gated until the
Lean obligations O1–O3 and a full corpus A/B are discharged — see
docs/ROOT-ORDERED-RESOLUTION.md.

### Separate provably positive ABoxes from TBox classification (2026-07-16)

The procedure matrix found assertion-heavy ORE 10697, 15725, and 15846 where
the exact nominal CB route reached its 190 second central cap. Direct tests of
the same calculus with per-function scheduling at 1, 8, and 16 threads also
timed out at 240 seconds on all three. This rules out a scheduler-only fix. KM
currently builds and saturates the complete ground context inside every query
engine.

Konclude instead separates ABox consistency precomputation from class
classification. Its `CTotallyPrecomputationThread` saturates individuals and an
all-assertion individual, accepts the result only when its direct and indirect
status is completed, non-clashed, and sufficient, and reuses the precomputed
state for classification. Official Konclude diagnostic job 48947466 confirms
this boundary: on 10697 and 15725, precomputation takes 1,211 ms and 540 ms,
while class classification takes only 3 ms and 2 ms. On 15846 the corresponding
times are 16,164 ms and 80 ms.

Profile schema 2 now records bottom-class and bottom-role occurrences and a
fail-closed `positive_abox_tbox_separable` certificate. The certificate accepts
only positive assertions with no negative constraint, number restriction,
nominal, universal role, rule, key, or datatype constraint. A one-element
all-positive interpretation proves consistency. Disjoint-union preservation
for nominal-free SRIQ without the universal role proves that such an ABox
cannot add a TBox subsumption. Certified inputs use the same independently
complete EL/CB decision tree as the TBox core; every other ABox remains on the
exact nominal calculus. This is a source-level proof gate, not empirical
routing. The checker uses an explicit safe-axiom whitelist: imports, unknown
axioms, and every functional-syntax axiom that the frontend could otherwise
skip fail closed.

The post-whitelist optimized `ws` suite passes 1,516 tests with 0 failures and
7 ignored. Default `auto` selects `cb_plain16` for 10697 and 15725. Their
canonical signatures match Konclude with zero differences in 0.9152 seconds at
161.57 MB and 0.7212 seconds at 123.62 MB, respectively. Default-auto
regressions 148, 178, and 11016 stay on the exact nominal gate and remain
gold-exact. Ontology 15846 is intentionally not certified because it contains
nominals, equality and inequality assertions, and disjointness. See
`docs/POSITIVE-ABOX-SEPARATION.md` for the contract and proof.

### Separate source entities from generated concepts (2026-07-16)

The first post-148 matrix audit found one real completeness family after
discarding four canonicalizer false positives. ORE 8864, 12009, and 6817 were
missing only rows whose source class local names begin with `__`, including
`__adipocyte_glucose_uptake`, `__SyndromeDeBuckley`, and
`__hydroxy_proline_MI_0149`. These are explicitly declared OWL classes. KM's
engine historically recognized generated concepts by string prefixes, so it
mistook those legal source classes for auxiliaries, omitted their query
contexts, and returned otherwise sound but incomplete classifications.

Sequoia represents source symbols and generated definers as different typed
symbols. KM now preserves the same distinction at its frontend boundary.
Registry-owned source names beginning with `Q_`, `__`, `_aux`, `aux_`, or
`def_` receive a collision-safe `km_src_` internal spelling. Generated symbols
are constructed after parsing and never pass through that registry. The
existing inverse IRI map restores the exact public IRI in the classification,
including when a real source name already uses the escaped spelling. The
superseded Python frontend mirrors the same encoding so it remains a valid
orchestration oracle.

Production `cb_plain16` on `ws` now matches frozen Konclude gold exactly for
8864 (6,094 pairs), 12009 (10,509), and 6817 (2,431), with no extra or missing
pairs and no unsatisfiability or consistency difference. The 148 nominal
closure and its 178/11016 regressions retain their exact signature hashes. The
release suite reports 1,515 passed, 0 failed, and 7 ignored. Portable Bullseye
binary `c229366fcc9efbfec729f5a7dcc1a5f1ef9b12fe41f433b67282930bf18a92f6`
repeats all six exact comparisons on an IBEX Intel Gold 6248 node in job
48946056. Full 592-ontology, 28-arm matrix job 48946164 uses only this binary
in 50 isolated shards. This changes frontend symbol encoding, not a CB
inference rule or the derived fixpoint, so it requires no Lean
re-certification.

### Exact nominal classification closes ore_ont_148 (2026-07-16)

The production `nominals` route now closes ore_ont_148 in 54.69 seconds at
3,029,400 KB on `ws`. Its canonical signature contains all 21,037 Konclude
pairs, zero extra and zero missing pairs, no unsatisfiable-class difference,
and the same consistency result. The signature SHA-256 is
`10ef79ea10318d5197169737fc59d7d5771162a452a2e4e1a74a7a0ca880d944`.
The route selects the winning schedule itself; the validation command did not
supply `KM_STATIC_SCHED`.

The exact failure localized to `Cryosphere`. Its universal `hasSubstance.Ice`
restriction meets `Hydrosphere ⊑ hasSubstance value Water`, making the
completed `Water` nominal label query-dependent. One incoming eight-premise
Pred clause had six exact providers per premise and repeatedly materialized
`6^8 = 1,679,616` Cartesian resolvents. A long-lived dynamic worker also mixed
several independently conditioned nominal tasks in one ground context. This
matches Konclude's reason for copying the consistency-test nominal label into
separate influenced saturation tasks.

KM now follows Sequoia's exact maximal-head predicate and term indexes and its
complete active redundancy semantics, represented as exact rarest-head
postings plus explicit todo checks. Pred computes the same strengthening
antichain incrementally after each left-deep join dimension. The equivalence is
algebraic: if partial `P` strengthens `Q`, then `P ∪ R` strengthens
`Q ∪ R` for every remaining completion `R`. The `nominals` route assigns
one fixed query slice per Engine, bounding influenced labels per ground
context; `KM_NOMINAL_DYNAMIC=1` retains the general scheduler for A/B tests.
All three changes preserve the inferred fixpoint and require no Lean
re-certification.

A separate certified optimization recognizes exact finite nominal
enumerations only when both union directions, singleton equalities, and ground
facts are present. It completes the ground sameAs/type fixpoint and intersects
the enumerated labels, matching Konclude's completed nominal-label reuse. This
keeps ore_ont_11016 exact at 265/265 in 0.74 seconds and ore_ont_178 exact at
56/56 in 0.23 seconds; it is inert on ore_ont_148, which has no
`ObjectOneOf`. The release suite reports 1,513 passed, 0 failed, and 7 ignored.
The first portable binary
`bf2875c9c234017a47881dc9b25086c8fdf6c2a673a869fb0ebbb48b142691f8`
passes the IBEX exact-signature smoke in job 48943813: 148 takes 53.7969 seconds
at 2,985.21 MB, 178 takes 0.2687 seconds at 40.94 MB, and 11016 takes 0.5875
seconds at 190.62 MB. Matrix job 48943875 was cancelled after its early audit
exposed the source/generated symbol collision documented above. Corrected
binary `c229366f…` repeats the three exact signatures in IBEX job 48946056;
148 takes 53.3149 seconds at 2,956.60 MB. Closure must not be confused with the
outstanding greater-than-20-percent performance gap to Konclude. See
`docs/SOLVE-148.md`.

### Fence named HT specialists from the incomplete general racer (2026-07-15)

The procedure-matrix audit found that `ht_qo`, `ht_shoq`, `ht_card`, and
`ht_bridge` enabled their named specialist but silently fell through to the
unrestricted general HT racer when the specialist's structural candidate was
absent. General HT is a useful explicit measurement arm, but it is known
incomplete on part of ALC+disjunction and is excluded from policy learning.
Allowing the same algorithm under a policy-eligible specialist name could make
a source-profile tree generalize an empirically exact row into an incomplete
classification.

The audit also rejected empirical success as a completeness certificate. QO
race is incomplete on 15098, 7216, and 7901; the SHOQ and first-class
cardinality routes are incomplete on 10702; and the historical tableau has no
full-fragment completeness contract. Those procedures remain benchmark and
manual options, but they cannot become learned-policy leaves.

Every policy-eligible named bundle now starts with `KM_HT_ONLY=certified`, which
admits only the Konclude completion bridge's complete-answer-or-defer path.
Named specialists narrow execution to
`KM_HT_ONLY=qo|shoq|card|bridge`; `spawn_ht` returns to certified CB when the
requested candidate is absent. A bridge-only worker also exits on bridge defer
instead of falling through to the legacy tableau, even when the input is
otherwise legacy-HT routable. The unrestricted measurement route explicitly
sets `KM_HT_ONLY=general`, and every individual option remains available in
manual mode. Unit tests cover every discriminator and the route bundles.
This changes only safe procedure eligibility, not any inference rule, so it
requires no Lean re-certification.

### Make the historical tableau procedure measurable again (2026-07-15)

The all-procedure audit found that `KM_TAB_RACE=1` no longer reached the
legacy label-caching tableau on ordinary non-giant inputs. The later certified
EL portfolio wrapped the entire CB stack, while the tableau is composed only
inside that stack. Explicit tableau selection now suppresses that outer EL
portfolio, and the named `tab_race` bundle supplies `KM_TAB_FEAT=1` and disables
the unrelated outer HT racer. A unit test fixes this precedence boundary.

An isolated 9635 probe then established a second, intentional boundary. The
modern converter rejects the input before spawning a worker because it combines
inverse roles and number restrictions, producing the explicit
`inverse+number(SHIQ)` soundness fence. This supersedes the old 9635 legacy-race
claim; the newer certified cardinality and Konclude-bridge paths own SHIQ. An
opt-in `KM_TAB_DUMP_TIN` plus `KM_TAB_TRACE` diagnostic now records the exact
pre-fence tableau input and reasons without changing routing. On the current
in-fragment witness 6246, the named route and its explicit option bundle both
return the complete 322-pair gold signature in 30.95–31.07 seconds on IBEX job
48889958. These changes only alter procedure composition and diagnostics, not
any calculus derivation, so they require no Lean re-certification.

### Restore source-TBox bridge routing for complex domains/ranges (2026-07-15)

The new all-procedure routing matrix exposed that `ore_ont_541` timed out in
every triggered-bridge arm even though the Konclude bridge kernel still
classified its exact input immediately. The failure was at the procedure gate.
Exact source-RBox provenance added `complex-domain` and `complex-range` fences
for the legacy clause-reconstructed tableau. `spawn_ht` reused those fences for
the source-terminology bridge and declined to spawn it.

The bridge gate now accepts those two fences only when triggered absorption
carried a nonempty normalized source TBox and source-TBox mode is enabled. In
that case the bridge builds Konclude's native domain/range concepts directly;
without source provenance the same inputs remain fenced. Other fence reasons,
including unsupported RBox constructs, remain rejected. The actual production
race again classifies 541 in 0.25 seconds at 53 MB and 12653 in 0.15 seconds at
18 MB on `ws`. A focused test proves the source-only fence distinction. This
changes orchestration eligibility, not CB-calculus derivations, so it requires
no Lean re-certification.

### Saturation-aware cardinality successors close ore_ont_14817 (2026-07-15)

`ore_ont_14817` now completes through production `km classify` and matches
Konclude exactly: 1,184,692 subsumptions on both sides, zero extra, zero
missing, no unsatisfiable-class difference, and the same consistency result.
The final Rust 1.85 Bullseye binary has SHA-256
`c7c3eefe49ac95a7feaa7c1b70ada2ae65b820097cbe0456b0ab4be82c61ba07`.
IBEX production-sweep job 48853569 task 518 finished in 56 seconds at
3,365,116 KB. An independently traced full run matched in 195.16 seconds at
4,234,340 KB.

The fixed 9724 binary saturated 48,642 of 58,364 active subjects but timed out
on the 9,722-subject completion residue. Exact ports of Konclude's live
satisfiable-expander cache, 80-rule task boundary, cache commits, retired-pool
release, pointer-like label signatures, and KPSet touched-candidate ordering
made the tail measurable. They did not close it. Subject 85031,
`UBERON_0014672`, still produced 72,670 disjunction replacements in 51 seconds
and deferred.

A trusted Konclude trace, built by relinking the native IBEX objects and
recompiling only the instrumented completion object, handled that subject in
125 ms. Konclude saturation-expanded its first six root successors as three
cardinality-created pairs. KM created the corresponding successors 1001
through 1006 without saturation expansion and began its nine expansion events
at successor 1007. Queue and label tracing independently showed that the
subsequent repeated work was real restored-branch exploration, not duplicate
insertion or accidental requeueing.

The source divergence was exact. Konclude's `applyATLEASTRule` creates an
`ATLEAST` dependency and calls the full `createDistinctSuccessorIndividuals`
path. Production Rust instead called the reduced
`ht_create_distinct_successors` helper, bypassing saturation replay and cache
establishment for every `≥ n R.C` successor. Rust already contained the full
constructor in `completion/u35.rs`; `completion/u08.rs::apply_atleast_rule` now
uses it with the complete signed indirect-super-role list, dependency, pending
clash propagation, low-level nominal handling, and final successor queueing.

The repaired subject expands the missing six successors and records only 300
disjunction replacements over its complete 14.66-second run. A permanent
production-path test constructs `≥2 R.C`, gives `C` a completed saturation
label containing an additional `D`, and proves that both distinct successors
receive explicit `C` and saturation-only `D`. The release suite passes 1,480
tests with 0 failed and 7 ignored.

Full 592-ontology IBEX job 48853569 used the same final binary for every task.
It reports 575 completed, 17 timeout, and 515 exact Konclude matches, compared
with 574, 18, and 514 in the 9724 baseline. The only changed ontology is
14817, from timeout to exact. No previously exact ontology or disagreement
count regressed. The complete C++ correspondence and reproduction record are
in `docs/SOLVE-14817.md` and
`results/benchmarks/2026-07-14-14817-closure/`. These changes affect the
Konclude-compatible completion implementation and cache lifecycle, not the CB
calculus or its fixpoint, so they do not require Lean re-certification.

### Konclude intrusive free-list representation closes ore_ont_9724 (2026-07-14)

`ore_ont_9724` now completes through production `km classify` and matches
Konclude exactly: 457,090 canonical non-self subsumptions on both sides, zero
extra, zero missing, and the same consistency and unsatisfiable-class results.
The final Rust 1.85 Bullseye binary has SHA-256
`8071a4d0d7b35476f8c4d65a749e8fef71279e23dedd1ade4aba405f327078f9`.
IBEX production job 48798145 finished in 24.72 seconds at 8,091,788 KB. Its
independent task in full-sweep job 48799766 matched again in 23 seconds at
8,092,216 KB.

The preceding result was sound but partial, with 3,325 missing pairs at the
fixed saturation budget. A 1,200-second exact-input run recovered only one
pair and reached 24,555,236 KB. It never reached completion-side ATMOST
merging, which disproved the plan-start cardinality hypothesis. Instrumented
Konclude with one worker finished in 10.46 seconds, constructed 33,422
saturation items against KM's 33,678 seeds, and performed 6,853,425
concept-add attempts. The close input shape plus single-worker completion
localized the gap to KM's saturation implementation cost.

An initial exact alignment replaced owned implication-trigger suffixes with
non-owning operand cursors, eliminated persistent allocation for Konclude's
stack-local initial descriptor, used pointer-like integer hashing for role ids,
consolidated backward-role bucket mutation, and changed temporary propagation
chains to constant-time LIFO stacks. That candidate reduced peak memory but
still ended with the same 3,325 missing pairs.

Four live worker samples at 30, 90, 160, and 220 seconds then showed the same
stack: `memcpy` under `release_role_saturation_process_linker`, called from
`process_successor_functional_concepts_extensions`. Konclude's
`CProcessingDataBox.cpp:1849-1869` maintains
`mRemRoleSatProcessLinker` as an intrusive free list. Release prepends a linker
to the head, and acquire removes that head, both in constant time and LIFO
order. KM's collapsed `Vec` stored the head at index zero and implemented the
same logical order with `insert(0)` and `remove(0)`, shifting the entire growing
list on every operation.

Collapsed allocation free lists now store their logical head at the Vec tail.
Konclude's prepend/head-pop operations become Rust `push`/`pop`, preserving the
exact reuse order in O(1). Diagnostic getters reverse the internal vector to
retain the C++ head-to-tail view. The same representation is used for adjacent
concept, status-update, and individual-node `mRemaining*` free lists with the
same Konclude constructor pattern. Ordinary live traversed chains keep their
existing layout. The exact normalized input changes from 3,325 missing after
240 seconds to a complete match in 32.15 seconds.

Release validation is 1,475 passed, 0 failed, and 7 ignored. IBEX array job
48799766 attempted all 592 ORE ontologies at 240 seconds and 20 GB each. It
reports 574 completed, 18 timeout, and 514 exact Konclude matches, up from 511.
No prior exact ontology regressed and no disagreement count increased. Exactly
three results changed, all from incomplete to exact: 1016 recovers 2,510
missing pairs, 11623 recovers 3,423, and 9724 recovers 3,325.

The full causal record and reproduction artifacts are in
`docs/SOLVE-7914-9663-9724.md` and
`results/benchmarks/2026-07-14-9724-closure/`. These are fixpoint-preserving
storage, cursor, hashing, and lookup changes inside the Konclude-compatible
hypertableau port. They do not alter the CB calculus or require Lean
re-certification.

### Native RBox links and role-specific saturation successors close ore_ont_9663 (2026-07-14)

`ore_ont_9663` now completes through production `km classify` and matches
Konclude exactly: 725,040 non-self subsumptions on both sides, zero extra, zero
missing, and the same consistency and unsatisfiable-class results. The
promoted Rust 1.85 Bullseye binary has SHA-256
`dbc35ea3f19c5de9ef447ce274edeb69aeacd91867f3e4d51eaf879b6533e825`.
IBEX gate job 48797088 task 0 finished in 52.75 seconds at 3,189,032 KB. The
independent 9663 task in full-sweep job 48797094 matched again in 47 seconds at
3,147,948 KB.

The baseline was sound but incomplete: 685,932 pairs, zero extra, and 39,108
missing. Of those, 39,087 were 13,029 subjects each missing
`BFO_0000004`, `BFO_0000002`, and `BFO_0000001`. The first missing boundary
was the source RBox. Konclude stores object-property domains and ranges
directly on `CRole`, while KM's source-TBox bridge discarded their normalized
clause copies without constructing the native links. `TInput` now carries
explicit `role_domains` and `role_ranges` provenance from the frontend. Source
mode installs exactly those pairs on the role and inverse role, then suppresses
the concept-bearing clausal copies. It does not infer RBox provenance from a
guarded clause shape, because ordinary class-expression clausification can
produce the same shape. This first causal port reduced the miss from 39,108 to
633 pairs.

The residual witness combines `A ⊑ ∃r.B`, `B ⊑ ∃s.C`,
`r∘s ⊑ t`, and `Domain(t,D)`. KM's role-chain automaton was structurally
correct, but saturation reused the ordinary filler item. That node had already
initialized without role `s`, so it never loaded the generated range
propagation that carries `D` back to `A`.

The decisive change ports
`CTotallyPrecomputationThread.cpp:2057-2074` and
`CTotallyOntologyPrecomputationItem.cpp:731-739`. The seed builder now applies
Konclude's `hasRoleRanges` test over signed indirect super roles. When it holds,
KM interns a separate saturation item keyed by `(role, filler, polarity)`, uses
that item during dependency ordering, stores it in the restriction's
existential-successor reference, and initializes both ontology-side and
process-side items with the role. `createSuccessorForConcept` then reads the
same existential-specific item before its ordinary filler fallback. The
ordinary `(filler, polarity)` path remains unchanged for roles without ranges.
An adjacent exact port now also reports valid named concepts on intermediate
saturation substitute nodes; its isolated candidate did not alter 9663.

The final saturation phase answers 385 unsatisfiable and 57,385 satisfiable
subjects directly and sends 422 insufficient subjects to completion, with no
defer. Konclude reported 423 insufficient nodes, which independently confirms
that the repaired boundary is the one exercised by the ontology. Release
validation is 1,474 passed, 0 failed, and 7 ignored.

IBEX array job 48797094 attempted all 592 ORE ontologies and reports 574 ok,
18 timeout, and 511 exact Konclude matches, up from 508 exact matches in the
3215 baseline. No previously exact ontology regressed. Ontologies 8730, 11978,
and 9663 become exact, while 11745 improves from 15,350 extra and 1,213 missing
to one extra and zero missing. The already-open 9724 remains sound but partial:
its fixed-budget result moves from 3,140 to 3,325 missing pairs because the
exact port constructs 7,714 additional role-specific items generated by role
automata. Both variants stop at the 180-second outer-queue cap; instrumented
Konclude completes that work in 9.84 seconds. This records a remaining 9724
performance problem, not a false inference or regression of a solved ontology.

The detailed causal record and reproduction artifacts are in
`docs/SOLVE-7914-9663-9724.md` and
`results/benchmarks/2026-07-14-9663-closure/`. These changes construct the
Konclude-compatible terminology and saturation inputs. They do not change the
CB calculus or its derived clause set, so they do not require Lean
re-certification.

### Konclude KPSet phase barrier closes ore_ont_3215 (2026-07-13)

`ore_ont_3215` now completes through production `km classify` and matches
Konclude exactly: 3,923,171 pairs on both sides, zero extra, zero missing, no
unsatisfiable-class difference, and the same consistency result. Final IBEX
smoke job 48790271 finished in 129 seconds at 5,351,252 KB. Its independent
task in full-sweep job 48790295 matched again in 120 seconds at 5,357,524 KB.

The first exact KM/Konclude divergence was terminology shape. KM treated every
frontend definer as an active class and attached 18,323 implications to common
condition `C047449`; its saturation label grew to approximately 18,000 concepts,
while Konclude's matching label had 3. The bridge now follows Konclude's active
class set and source terminology representation, including the exact binary
trigger absorber mechanics: over-use complexity penalty, cached trigger-pair
reuse, decreasing complexity/address order, reusable left-deep implication
chains, and rounded-average disjunctive trigger complexity. Common-disjunct
extraction now uses reusable dense signed-concept sets instead of cloning large
visited sets.

After that repair, saturation finished in about 31 seconds and already held the
positive taxonomy, but KM still timed out on redundant classification work.
Instrumented Konclude gave the decisive counts: 54,974 class items, 36,651
directly derived satisfiability results, 18,323 completion satisfiability jobs,
18,323 callbacks, and zero calculated pairwise subsumption tests. Source
inspection localized the difference to the all-satisfiability-jobs barrier in
`COptimizedKPSetClassSubsumptionClassifierThread::createNextSubsumtionTest`.
Konclude waits for every model callback, builds an `owl:Thing`-rooted sparse
propagation graph, compares all completed child/parent possible maps, and only
then allows pair scheduling. KM had ported the local message handlers but
interleaved each subject model with pair tests while the propagation graph was
still empty.

The synchronous classifier now has the same two phases. Prepare runs every
residue model and delivers its deterministic, possible-subsumer, and
pseudo-model messages. A single global barrier then builds the propagation
graph and recursively invalidates parent candidates absent from completed child
maps. Verify examines only candidates that remain unknown. On 3215 this
propagates 202,002 false candidates and schedules zero pair jobs.

Supporting hot-path changes retain the same saturation fixpoint: integer-keyed
label hashing, a pre-allocation exact-duplicate descriptor check that preserves
the opposite-polarity clash path, an O(1) LIFO process-linker free list, and
cached diagnostic gates. The production race also now limits the speculative
CB fallback to one thread only for faithful synchronous bridges with at least
50,000 active classes. A controlled IBEX run showed the reason: the exact bridge
finished in 137 seconds with one CB competitor but exceeded 240 seconds when
the fallback occupied 15 cores. Smaller bridge races and all winner/fallback
semantics remain unchanged.

Release validation is 1,468 passed, 0 failed, 7 ignored. The final 592-ontology
IBEX sweep reports 574 ok / 18 timeout and 508 exact matches, compared with 569
/ 23 and 499 exact matches in the preceding feature sweep. No gold-matching
ontology regressed. In addition to 3215, 11315, 12414, 4054, 4755, 7127, 7581,
8068, and 8864 become exact matches. The detailed causal record and
machine-readable aggregate are in `docs/SOLVE-3215.md` and
`results/benchmarks/2026-07-13-3215-closure/`.

Controlled IBEX job 48790909 reran the nine changed correctness cases with the
preceding and final binaries under identical flags. All nine binary pairs
completed, with eight exact-match improvements, one reduced disagreement, and
zero exact-match regressions. This confirms the correctness changes separately
from full-sweep node timing.

These changes do not alter the CB calculus or its derived clause set, so they
do not require Lean re-certification. They change faithful terminology
construction, completion-classifier bookkeeping, fixpoint-preserving storage,
and race scheduling outside the Lean-certified core.

### Konclude equivalent-non-candidate hand-off closes the 5303 regression (2026-07-13)

The first 592-ontology IBEX sweep of the 7914 feature stack exposed one real
same-configuration regression: `ore_ont_5303` lost exactly
`CarbonHydrogenSubstructure ⊑ Hydrocarbon`. A controlled old-binary versus
candidate-binary run reproduced `match → incomplete(1)`. The entailment follows
from the named molecular-group hierarchy, the carbon and hydrogen component
existentials, `hasComponentPart ⊑ hasProperPart`, and the `Hydrocarbon`
equivalent definition.

The completion model was not incomplete. A direct pair test returned true, but
the nondeterministic root read-off did not contain `Hydrocarbon`. Konclude does
not restrict possible subsumers to that root label. Its binary absorber keeps
non-absorbed equivalent definitions available through the TBox
`mEquivConNonCandidateSet`; its satisfiability analyser filters that live set and
emits `CClassificationInitializePossibleClassSubsumptionMessageData`; the KPSet
classifier installs and schedules the surviving pairs.

KM had already ported each downstream data structure and message handler, but
the production bridge broke both hand-offs. It retained the three source
definitions (`eq=0/3`, including `Hydrocarbon`) as `CCEQ` without registering
them, then invoked the older analyser wrapper with an empty local map. The
targeted port now:

1. takes Konclude's non-candidate branch for a source `CCEQ` that cannot be
   fully absorbed (the optional partial-equivalence candidate optimization is
   not materialized by this bridge);
2. calls the live-ontology equivalent-non-candidate analyser wrapper; and
3. refreshes the synchronous subject candidate list from the delivered KPSet
   possible map before pair verification.

The real 5303 production trace now shows subject 7 receiving the initialization
message, scheduling `CarbonHydrogenSubstructure v Hydrocarbon`, and confirming
the pair true. `production_has=true` while the deliberately weaker raw read-off
remains false, which isolates the repair to Konclude's classification pipeline.
The environment-independent regression
`source_absorber_registers_unabsorbed_equivalent_non_candidate` covers the
source-preprocessing invariant. This is classification bookkeeping, not a
change to the CB calculus, so no Lean re-certification is required.

Final IBEX job 48737778 attempted all 592 ontologies: 569 ok, 23 timeout, with
499 exact Konclude matches. Relative to the immediately preceding
feature-enabled sweep, 5303 is the only signature change and improves from one
missing pair to exact. The 18-ontology same-flags panel reports zero
old-versus-final changes. A one-run 9663 timing difference did not reproduce:
the pre-fix feature binary and final binary both timed out at a 300-second
diagnostic cap with nearly identical memory.

### ore_ont_7914 closed by exact Konclude descriptor-chain port (2026-07-13)

`ore_ont_7914` now completes and matches Konclude exactly. The full run checks
all 93 completion residues, returns 141,517 subsumptions against the same
141,517 in gold, and has 0 extra, 0 missing, no unsatisfiable-class difference,
and no consistency mismatch. Slurm job 7936 finished in 2:30.56 at 18,882,684
KB. Targeted jobs 7934 and 7935 separately close the two prior false-positive
families. Final release validation on `ws`: 1,460 passed, 0 failed, 7 ignored.

The OR planning, OR-only dependency, and satisfiable-cache ports first changed
7914 from timeout to a terminating but unsound result with 29 extra
subsumptions. Cache tracing then found a precise contradiction: KM classified
branch-derived CCAND concept 45405 as nondeterministic, but replayed it from the
associated expansion cache as deterministic. Instrumented Konclude stored only
the corresponding branch-tag-1 descriptors as nondeterministic.

The final cause was a missing line in the Rust port of
`CReapplyConceptLabelSet::insertConceptGetClash`. Konclude prepends every new
descriptor with
`mConceptDesLinker = conceptDescriptor->append(mConceptDesLinker)`; KM replaced
the label head without linking the new descriptor to the old head. The severed
newest-first chain made the faithfully ported cache partition fallback wrap to
the head and duplicate a nondeterministic descriptor into the deterministic
suffix. `completion/u36.rs` now sets the new descriptor's `next` field to the
previous head before insertion. This is the exact C++ invariant, with no
ontology or concept conditional. The associated-cache allowance also now
matches Konclude's constructor default of one nondeterministic expansion.

Permanent tests cover production descriptor insertion, nondeterministic cache
prefix/suffix splitting, OR-only dependencies, and branch-open model read-off.
The full causal record, traces, source references, and job table are in
`docs/SOLVE-7914-9663-9724.md` and
`results/benchmarks/2026-07-13-7914-closure/`. Final IBEX job 48737778 ran a
Bullseye-linked binary over all 592 ORE pool ontologies at 240 seconds and 20
GB each. The final binary matched 7914 in its 78-second smoke task and in the
full sweep. No gold-matching ontology regressed in the corpus run, and the
same-flags controlled panel found no old-versus-final change.

### Source-terminology bridge solves 541 and 12653 in production (<1 s, 2026-07-10)

The disjunction-family blocker was not another completion-rule gap. Konclude
absorbs the normalized ontology concept graph before clausification, while KM's
bridge reconstructed that graph but still presented every generated definer and
recognition clause as an independent GCI. On the two target ontologies this was
the difference between Konclude processing 23/10 residual GCIs and KM processing
647/501 HT clauses.

The frontend now carries an env-gated normalized source-TBox side channel under
`KM_TRIGGER_ABSORB`. The bridge ports the relevant
`CConcreteOntologyUpdateBuilder` and
`CTriggeredImplicationBinaryAbsorberPreProcess` behavior:

- named-left inclusions become direct `CCSUB` unfoldings;
- pristine equivalent definitions use `CCEQ`, with fully triggerable
  definitions converted to `CCSUB` plus a reverse binary implication;
- property domains/ranges become role links rather than GCIs;
- only structural-left residuals reach full/partial binary GCI absorption.

The resulting preprocessing counters match Konclude: 541 has equivalence
absorption 1/2 and 22 absorbed residual GCIs (23 total before range movement);
12653 has 1/1 and 9 absorbed residual GCIs (10 total). The remaining search
correctness issue was sibling isolation: PathOfLength4 was falsely UNSAT under
the old mutable in-process OR stack, but SAT under complete branch-epoch COW,
matching Konclude's one-calculation-task-per-alternative behavior. COW is now
the trigger-absorption default. Saturation runs in an independent task unless
explicit satcache coupling is requested, and classification seeds its known
subsumers from the deterministic source `CCSUB` closure before verifying only
the residual candidates. The old reversed-disjunct second-model heuristic is
not used for source terminology.

`KM_TRIGGER_ABSORB=1` now enables the certified bridge racer and harvests its
sound+complete answer immediately (or receives no answer on defer). Release
measurements on `ws`, through `km classify`:

| Ontology | Wall | Peak RSS | Gold comparison |
|---|---:|---:|---|
| ore_ont_541 | 0.86 s | 428 MB | 164/164 local-name pairs, 0 missing, 0 spurious |
| ore_ont_12653 | 0.08 s | 9 MB | 10/10 pairs, 0 missing, 0 spurious |

541 emits 166 full-IRI pairs because it correctly distinguishes two different
classes both locally named `ProcessQuality`; projection to the ORE gold's local
names gives the exact 164-pair set. Default frontend JSON remains byte-identical
with the flag off. Validation: 1433 passed, 0 failed, 7 ignored.

### Saturation-first probe answering, waves 1-3 (`18c9a46` .. `c116a9c`, 2026-07-09/10)

The confirmed lever for the disjunction/cardinality timeout family (541, 12653,
...): Konclude decides ~95% of subsumption tests by its approximation
saturation before any tableau search. The 12 ported saturation units are now
WIRED in front of the bridge's completion probes, opt-in `KM_HT_SATURATION=1`
inside the `KM_HT_BRIDGE` arm (`18c9a46`): production config, per-
(concept,polarity) seeds, budgeted run (`KM_HT_SATURATION_BUDGET_S`, discard
on overrun), and `CPrecomputedSaturationSubsumerExtractor`-style consumption
(CLASHED = unsat-certain; completed and not INSUFFICIENT = sat-certain with
the exact subsumer row; residue unchanged to the probes). Five port bugs were
fixed on the way in, plus a default-path root-top fix (bridge probe roots were
created without TOP, silently weakening bottom-rule clash detection).

Wave 1 (`8481c9b` + `76cc6e0`): the precise ATMOST criticality test (collect +
simple/detailed mergeability + ancestor INSUFFICIENT marking replaces the
node-poisoning substitute) and a critical-queue misrouting fix. The s03
file-local CCT_DISJUNCTION/EQCANDIDATE tags were 4/5 but Konclude's enum is
2/3, so every OR critical was routed into the always-defer VALUE stub queue
and the precise OR test never ran. Found via per-type SAT-STATS counters.
After both fixes the family criticals are decided by the real tests and are
genuinely critical: the criticality-test path is exhausted as a lever.

Wave 2 (`1b57b9d` + `bf282e8`): the saturation-node coupling into the
completion probes, Konclude's production completion profile (expand created
successors from saturated labels, caching-blocking from saturation, and the
generating-existential absorption that terminates tree growth at cached
nodes). Saturation runs on the probe env; `reset_probe_env` carries the ~43
saturation arenas across probe resets (`adopt_saturation_state_from`).
Opt-in `KM_HT_SATCACHE=1` on top of `KM_HT_SATURATION=1`: measured on 12653,
coupled probes poison-defer at subject 1 vs 14 plain, because without the
extension-resolving refinement the replayed labels under-approximate
forall-restricted successors and caching fails to establish exactly where it
matters. Becomes profitable once `getSaturationResolvedIndividualNodeExtension`
is ported.

Wave 3 (`c116a9c`): the successor-EXTENSION machinery's wrong clashes (541
ext-ON: 11-13 satisfiable classes answered UNSAT-certain, nondeterministic)
ROOT-CAUSED via a 13-axiom ddmin reproducer and fixed. The watch-side
implication trigger check (`insert_concept_reapplication_return_triggered`)
faithfully ported the C++ positive-presence-only test, which is safe in
Konclude because absorption only builds positive-presence triggers, but the
bridge's clause encoding also emits negative-presence triggers; a label
carrying +C then satisfied a want-not-C trigger and a contrapositive
implication chain manufactured a clash on resolved extension nodes. Fix:
thread the wanted presence polarity (the inverse of the stored linker
negation, matching the already-polarity-aware insert-side reapply check).
Validation: reproducer 0/20 wrong (was 8/8); 541 extensions-ON three runs 0
wrong and 6-9 of 59 family subjects answered SAT-certain, the first sound
nonzero saturation coverage on the family; suite 1424/1424. `KM_HT_SAT_EXT`
stays opt-in: the extension fixpoint costs ~40s on 541 (vs 0.4s off) with
run-to-run coverage variance (HashMap-ordered succ-extension maps vs
Konclude's sorted CPROCESSMAP). Env-gated diagnostics kept:
`KM_SAT_CLASH_TRACE` (all CLASHED-set sites, indirect propagation edges,
implication executions), `KM_SAT_ADD_TRACE=<concept>` (backtrace on watched
adds), extended `KM_SAT_DEBUG` dumps (subject/name/concept tables).

Also closed: the suspected "plain bridge no longer closes 12653" regression is
NOT a regression. Bisect (1c931e7 / 18c9a46 / 8481c9b / HEAD) shows the
permanent poison-defer at every point; the recorded 10-20s plain closes date
from before `7a01372` restored the complete-or-defer contract (unrestored
advances poison SAT verdicts by design), and the 17s figures were COW+DDB
probe-harness measurements. The production baseline (bridge off) never
regressed.

### Unsat-cache learning: functional, zero reuse on the family (`1fc2618`, `9c03476`, `1c931e7`)

Konclude's nogood store (occurrence unsatisfiable cache) wired live into the
bridge: handler install, carry across probe resets, read probes at Konclude's
rule points, write counters. Two bugs made it real: bridged concepts carried
no TERMINOLOGY so the u22 validity guard rejected every line (fix: terminology
stamp sweep in bridge_tinput), and the write-slot ring had ONE slot so the
first write deadlocked the C++ concurrent-reader wait protocol in-process
(gdb-proven; Konclude sizes workers+2; fix: ring of 3 plus bounded rescan that
skips the write instead of hanging). Post-fix verdict: overhead ~zero (12653:
17.2s vs 17.0s in the COW+DDB probe harness) but 0 read hits on 12653/541 —
the family's nogood lines carry seed and branch-specific atoms and never recur
as a label subset, so this mechanism cannot prune the family (valid negative;
Konclude's family speed is saturation + absorption, not its unsat cache).
`KM_HT_UNSATCACHE` stays opt-in. Also in this arc: Arc-COW extended to the
remaining map-bearing node satellites (role_succ / distinct / succ_role
hashes).

### Bridge correctness campaign + production wiring (2026-07-06 .. 07-08)

The bridge went from "solves 12653 in a harness" to a production-wired,
complete-or-defer arm of `km classify`:

- **Production route + env reuse** (`ca772f1`, `067aaa4`): read-off soundness
  gate, one bridged env per classification with per-probe resets
  (byte-identical A/B vs fresh envs), universe filter, per-subject defer.
- **COW branch epochs** (`d5603a0`, `7549697`, `0c5848f`): complete
  per-alternative state restore via epoch journal + arena watermarks; 541
  probes collapse 1M+ chronological backtracks to 435; later localized to
  per-node Arc-COW label sets + processing queues (O(1) journal save, deep
  copy on write = Konclude's task-fork shape). Decisive measurement: the 541
  residual is SEARCH VOLUME, not restore cost.
- **DDB (dependency-directed backjumping)** made trustworthy: taint-loss root
  cause (`2a869e8` DetLink back-edges), wrong root-cancels closed by trigger
  deps (`93e62e4`), and the u29 wrong-UNSAT root-caused to leftover poisoning
  and gated on `unrestored_advance_count == 0` (`7c521cb`, found by ddmin
  264 -> 5 axioms).
- **Soundness fixes**: at-most polarity + nondeterministic merge branching +
  choose rule (`1497954`), ALL-rule dependency threading (541 spurious
  unsatisfiability, `a4a3ae6`), phantom card-defs delivered absorption-only
  (`84e38bf`, closed the whole COW oracle-anomaly family), read-off search
  bounded by the probe budget (`42a8b74`, `1d188d6`).
- **Complete-or-defer restored** (`7a01372`): unrestored advances phantomize
  existential successors, so the poison now defers SAT verdicts instead of
  trusting them. This is why 12653's plain-bridge close from the `067aaa4` era
  now defers by design.
- **At-most resume port** (`371f38f`, `KM_HT_ATMOST_REST`): Konclude's
  branchingMergingProcRest state machine (incremental link scan via edge
  watermark, persistent candidate lists, distinct-clique init clash).
- **Panel verdict** (`6ac4a31`, results/benchmarks/2026-07-08-bridge-panel/):
  KM_HT_BRIDGE=1 flips exactly one ontology ok->timeout and closes nothing,
  so the bridge arm stays OFF in production. Baseline 576/584 ok; km beats
  Konclude on BOTH medians (0.21s/33MB vs 0.25s/135MB), faster AND lighter on
  356/576.

### Orchestration speed wins: +55 beat-Konclude goal-wins (2026-07-07)

- **In-process CB engine** for small non-EL ontologies (`8847b85`, gated on
  no-internal-definer-disjunction `b2f58fd`): +25 wins (IBEX 48105343 era
  snapshots).
- **Frontend meta/clauses parsed with `from_slice` instead of `from_reader`**
  (`2b8f224`): serde's reader path was the bottleneck; ore_ont_10073 frontend
  19s -> 5s; +30 wins.
- **Blank-node meta filter** (`14af873`): `_:genid` nodes excluded from
  named/iri_map; WIN 272 -> 284, solved 576 held.

### konclude_ht bridge solves ore_ont_12653 sound+complete in 1.0 s (`d64e78b`)

ore_ont_12653 (production 240 s timeout, disjunction + qualified-cardinality
family) classifies missing=0 spurious=0 via the ported Konclude algorithm.
Three coverage ports (domain/range at link install, inverse-role hierarchy on
concrete inverse-role objects with both-polarity closure, first-class
qualified `≥n/≤n` from `card_defs`) plus a pairwise `bridged_unsat` fallback
for nondeterministic subjects. Validation: konclude_ht suite 1208/1208;
ore_ont_1016 read-off regression identical (32712/32739, spurious=0).
Instrumented diagnosis of the rest of the family: ore_ont_541 is pure
chronological-backtrack thrashing (nodes=4 flat, ~2^56 branch space) and needs
the u29 dependency-directed-backjumping port; ore_ont_7914 is model explosion
(46k nodes) and needs blocking/lazy-∀. Full recipes:
`docs/SOLVED-ONTOLOGIES.md`.

Follow-up (same day): model read-off soundness gate. `or_backtrack_count == 0`
is NOT a determinism witness — a drive can open OR branch points and commit to
first disjuncts without clashing, polluting the root label (86 spurious
subsumptions measured on ore_ont_3215). Read-off is authoritative only when
NO branch point was opened (`or_branch_open_count`); nondeterministic subjects
degrade to candidate extraction + exact pairwise verification.

### In-process frontend fast path for small onts (+47 beat-Konclude WINs)

`classify` forked the `ofn` subprocess even for trivial ontologies, where the
standalone parse is < 10 ms but the classify frontend phase is ~50 ms — the
fork/exec of the 4.4 MB binary plus the clause/meta file round-trip. On the ~125
near-tie onts (KM losing to Konclude by < 1 ms on ~0.14 s totals) that fixed
overhead was the whole margin. Onts under 2 MB now run the frontend IN-PROCESS
(`ofn_to_clauses` directly, same function the subprocess runs), writing the
clauses file and returning the meta — byte-identical output. Memory-safe: the
2 MB cap keeps the giants' multi-GB transient parse peak isolated in the
subprocess; the small-ont transient is tens of MB and is freed before the engine
runs. Opt out with `KM_NO_INPROC_OFN`.

Full IBEX panel (job 48088964) vs the absorbed-plain panel (48086814): **WIN
166 → 213 (+47); SLOWER 216 → 153; FAIL 8 → 8; 0 unsound.** Cumulative across
both orchestration fixes this cycle (vs the pre-fix baseline 48085418): **WIN
136 → 213 (+77), 24% → 37% beating Konclude on both speed AND memory; timeouts
9 → 8.** The +16 SLOW+MEM/MOREMEM shift is speed-losses changing category (the
in-process parse peak on the larger sub-2 MB onts), not WIN→loss regressions.

### Portfolio CB arm uses the absorbed-plain path (+30 beat-Konclude WINs, −1 timeout)

The certified-elc portfolio ran its CB arm via `run_engine_adaptive` on the
ABSORBED clause set directly, while `cb_stack` (the non-portfolio default) runs
CB via `race_absorbed_plain` — an 8 s PLAIN (un-absorbed) probe, then the
absorbed set. On onts where absorption makes the clause set harder for CB, the
absorbed-only run is far worse (ore_ont_1082: CB 44 s / 8.7 GB in the portfolio
vs 2.9 s / 130 MB via absorbed-plain). The portfolio CB arm now uses
`race_absorbed_plain`, the same path `cb_stack` uses. Same sound+complete engine
on output-preserving clause encodings, so the CB answer is unchanged; the elc
racing is untouched, so the portfolio's recoveries are preserved.

Full IBEX panel (job 48086814, all 584 onts, KM vs Konclude wall+peak+gold) vs
the pre-fix baseline (48085418): **WIN (faster AND less memory) 136 → 166 (+30);
SLOWER 233 → 216; SLOW+MEM 203 → 190; FAIL 9 → 8 (ore_ont_14459, a 153 MB
near-giant, recovered); 0 unsound, 0 regressions.** Example flips: 11502
1.56 s/307 MB → 1.32 s/66 MB (now beats Konclude 173 MB). The remaining 8 FAILs
(541, 3215, 7914, 9663, 9724, 10621, 12653, 14817) plus the 2 contested-correct
(2669, 15516) are unchanged.

### SWRL DL-safe rules default-on, rule-gated (+3 ORE: 2669, 15516, 10906)

Three ORE timeouts are SWRL ontologies KM already solved correctly but only
under the opt-in `KM_HT_RULES` flag. The flag is now DEFAULT-ON (opt out with
`KM_NO_HT_RULES`), with the whole feature gated on ACTUAL DL-safe-rule
presence so it is provably inert on every rule-free ontology:

- Frontend `collect_rules` runs by default but returns empty on a rule-free
  ont, so `ht_rules` stays false and the clause output is byte-identical.
- `cb_to_ht` derives `rules_active = ht_rules && !rules.is_empty()`, which now
  gates the ABox-nominal seeding, the ground-fact interception, and — the old
  blocker to default-on — the emelim suppression. On a rule-free ont emelim
  still runs exactly as before.
- The rules-consistency check short-circuits ONLY on a detected inconsistency
  (⊥ subsumes all ⟹ the empty-subsumption verdict is complete). A CONSISTENT
  rule ontology falls through to normal classification so its hierarchy is
  still computed; DL-safe rules range only over named individuals and cannot
  change a TBox subsumption, so the fall-through is sound + complete.

Validation — all 6 corpus onts carrying `DLSafeRule`, default vs
`KM_NO_HT_RULES`: **2669** (240 s timeout → inconsistent, 0.17 s), **15516**
(→ inconsistent, 0.16 s), **10906** (→ inconsistent) all now correct
(genuinely inconsistent; HermiT agrees, gold wrong — see
`docs/CONTESTED-GOLD.md`); 13129 consistent 83 subs == 83 subs (identical, no
regression); 12451 and 10860 unchanged timeouts. +3 recoveries, 0 regressions,
1390/1390 unit tests green.

### HT: first-class cardinality route default-on (+3 ORE) and functional-role tagging (+1, gated)

The Konclude-port first-class `≥n`/`≤n` number rules (`KM_HT_CARD`) and the
propagation-based `≤n` recognition (`KM_HT_CARD_RECOG`, with SHIQ non-shared ∀
handling and mode-5 blocking) are now DEFAULT-ON; opt out with `KM_NO_HT_CARD` /
`KM_NO_HT_CARD_RECOG`. Validation: full 584-ont km-only IBEX panel with the
flags (job 48067625) — 574 ok, 573 gold-MATCH, 1 DIFF (10702, pre-existing
nominal incompleteness), 0 MATCH-to-DIFF regressions; recovers **ore_ont_1603
(21.7 s), 9540 (20.8 s), 7499 (82.5 s)**, all previously 240 s timeouts. A
default-config confirmation panel (48076591) reproduces the result with no env
set. A 156-pair flag-portfolio sweep (48066078: 13 timeout onts x 12 configs)
established these are the only flag-recoverable timeouts besides the contested
SWRL pair (15516/2669 via `KM_HT_RULES`, correct-but-gold-wrong; kept opt-in
since enabling it also disables complementary-definer elimination globally).

`KM_HT_CARD_FN` (new, opt-in): the frontend additionally tags
`FunctionalObjectProperty(R)` as a first-class global `⊤ ⊑ ≤1 R.⊤` — a fresh
universal marker concept asserted as a ⊤-fact with a max-CardMeta whose marker
and filler are that concept, so the HT `≤n` merge folds functionality instead
of branching over the raw `R(x,y0) ∧ R(x,y1) → y0 = y1` Eq clause (which is
kept: the CB engine consumes it, and it is redundant-but-sound on the HT).
**ore_ont_541: timeout in every prior config → 21 s, gold-exact.** Kept gated
OFF: its own 584-ont corpus panel (48080229) found the flag NET-NEGATIVE —
572 gold-MATCH vs 573 for the default (card without CARD_FN), because tagging
every functional-role ontology card-routable regresses ore_ont_1016
(MATCH → DIFF, a correctness break on 1016's functional roles) and ore_ont_7581
(MATCH → timeout, the extra markers + emelim-disable push it over budget) to
recover only 541. So 541 is not cleanly recoverable this way; CARD_FN remains a
diagnostic opt-in, not a default.

Also: `transitive_close_subs` now closes the confirmed subsumption relation at
the HT worker's serialization boundary (both the Ht and legacy-Tableau paths).
Phase 2 tests only candidates from one captured model root label plus a
told-clause closure, so an inferred (domain/range-derived, non-told) subsumer
absent from that model could yield `A ⊑ B` and `B ⊑ C` without the entailed
`A ⊑ C`. Closing is unconditionally sound (subsumption is transitive; the pass
only adds entailed pairs). Benchmark-inert (the ORE harness canonicalisation
already closes) but makes the raw JSON output correct on its own.

Diagnosis note: ore_ont_7499's apparent 3297-pair incompleteness against gold
is a localname-collision artifact, not a reasoning gap — the ontology carries
one axiom in the `purl.org/obo/owl/CHEBI#` namespace while the BFO upper
hierarchy lives in `purl.obolibrary.org/obo/CHEBI_...` with no bridging axiom;
KM correctly keeps the namespaces distinct and matches gold after localname
canonicalisation (same artifact class as ore_ont_12698's residual 18).

### HT/QoSat: QO hybrid router (`KM_HT_QO_ROUTER`) — sound certify-or-defer race arm

Wires the validated hybrid certify path into production as a structurally-routed,
sound certify-OR-DEFER race arm behind one flag (default off):
- `quasi_order_classify` gains a certify-only mode: a structural pre-gate defers
  when the clause set has no inverse bridge, and after the kpset attempt it defers
  (no funnel) when it cannot certify — emitting an answer ONLY when kpset certifies
  (sound+complete by construction).
- The tableau worker, in certify-only mode, returns no answer on a deferral (no
  fallback to branching/legacy tableau) so the orchestrator's CB engine decides.
- `spawn_ht` detects inverse BRIDGE clauses (cb_to_ht reports `inverse=false` for
  that encoding) and routes only faithful, nominal-free, inverse-bridge onts to the
  hybrid+certify-only arm; non-inverse HT-routable onts keep their normal branching
  path. The CB-vs-HT race runs in "race" mode so the fast certify beats a CB that
  would time out.
- The router runs the certify arm in correctness-aware FALLBACK mode (CB preferred
  whenever it finishes; certify taken only when CB errors/exceeds `KM_HT_BUDGET_S`).
  This is necessary because the kpset certify is NOT a guaranteed completeness
  oracle — on ore_ont_15098 it reports `kp_miss=0` but yields 939 where the truth
  is 951; fallback keeps CB's correct 951, race mode wrongly let the faster
  incomplete certify win. Sound regardless of the gap: the certify is relied on
  only where CB produces no answer at all (e.g. 7581's timeout).
- Router-mode corpus sweep (unimatrix job 7369, real production pipeline, only
  `KM_HT_QO_ROUTER=1`): **561 ok / 559 clean / 21 timeout; 0 regressions vs
  baseline.** 7581 recovered (565317=gold, 0/0, 166 s); 15098 km=951=gold (CB wins);
  the 2 gold-gaps (11745 +5/-1, 6999 −1) are pre-existing (parallel artifact /
  datatype gap, identical to baseline). 21 timeouts are the known-hard
  disjunction-family / giant set the hybrid does not target. 131 tests pass.

### HT/QoSat: corpus validation of the hybrid (0 regressions) + INVCOMPOSE trigger-rebuild fix

Full ORE-2015 sweep (unimatrix job 7322) comparing the HYBRID
(INVCOMPOSE+FPROP+SAT+KPSET) vs PRIOR-2a (funnel alone), both forced-QO + VERIFY,
each ont scored vs Konclude gold AND vs the other config (582/592):
- **0 regressions** — the hybrid is never worse than prior-2a on any ont.
- **7581 recovered** — hybrid 565317 = gold (0/0) in 32.7 s; prior-2a times out.
- All 14 gold-gap onts are `agree = true` (identical output in both configs) —
  pre-existing QO limitations (unsat under-detection, partial answers, the 6999
  datatype gap), CB-handled in production, not introduced by this change.
- Cost: 3 large CB-territory onts (11395, 3905, 3377=4.49M subs) time out where
  prior-2a finishes ~110 s — INVCOMPOSE+SAT overhead ⇒ the hybrid must be ROUTED
  to its Horn-inverse certify fragment, not blanket-enabled.
- Bug found+fixed by the sweep: INVCOMPOSE swapped `self.clauses` without
  rebuilding the Ht tableau triggers → per-concept verify panicked on ore_ont_10127
  (`fire_anchor_concept` out-of-range). Fixed by `rebuild_triggers` (98077ba);
  10127 now gold-exact.

### HT/QoSat: hybrid certifies 7581 sound+complete in 31s (4x) — `fprop` + `fcheck` + `sat` + `kpset`

Closed most of the 126s → Konclude-~10s gap. The key was Konclude's G1 (a filler
label is never read as a named subsumer) realised via `sat_mode` separate
per-(concept,role) filler nodes, plus a forward-broadcast store for the composed
inverse clauses.

- **`fprop` (`KM_HT_QO_FPROP`)** — forward-broadcast mirror of `prop` for
  head-on-TARGET Horn NF4 (the shape `compose_inverse` emits). FIXES the
  `KM_HT_QO_INVCOMPOSE` divergence: the composed clauses re-fired per edge; now
  they broadcast once per (source, role) and converge at forward-only cost.
- **`fcheck` (`KM_HT_QO_FCHECK`)** — composed clauses in containment-CHECK mode.
  Established that WRITING the composed head to a SHARED filler over-derives
  (1.34 GB), so the inverse head must not be written as a subsumer (Konclude G1/G3).
  Sound but, at filler granularity, defers (1581 false insufficiencies on shared
  fillers); reachability routing recovers nothing (0/72989, dense graph).
- **Hybrid `INVCOMPOSE + FPROP + SAT + KPSET`** — the sound+complete fast path.
  Composable inverse consumers (110k of ~110k on 7581) become forward clauses
  written to SEPARATE filler nodes (sound — named self-nodes stay inverse-clean,
  G1); residual non-composable bridges are kpset containment-checked; certify iff
  `kp_miss = 0`. A `count_inverse_bridges` guard makes the bare write path defer
  (not silently drop) on any residual bridge.
- **Measured ore_ont_7581 (ws):** `QOKP certified sound+complete (kp_miss=0)`,
  **31.3 s / 1.0 GB, km = 565317 = gold, 0 unsound / 0 incomplete.** 4x faster
  than the 126 s pseudo-model-merge path, within ~3x of Konclude's ~10 s, lowest
  memory of any path. All gated (default off), 131 tests pass. Remaining gap is
  constant-factor (saturation throughput + ~43k extra filler nodes), not a missing
  mechanism. Next: corpus regression (unimatrix) before default-on routing.

### HT/QoSat: 2b levers 1 & 2 toward Konclude ~10s — both quick forms REFUTED (findings)

Two attempts to close the 126s → ~10s gap (the 90-104s is building 63 real
`consistent(A)` pseudo-model tableaux; per-A timing shows a few are intrinsically
slow, 45-64s, large DETERMINISTIC inverse expansions).

- **Lever 2 — inverse re-encoding (`KM_HT_QO_INVCOMPOSE`, `compose_inverse`).**
  Resolves each bidirectional inverse bridge into its single-role consumers as
  forward clauses, drops the bridges (sound: resolvents; real ∃-edges untouched;
  130 tests pass). 7581's part_of/has_part inverse is bidirectionally load-bearing
  and all ~110k consumers are single-role NF4, so it applies cleanly. **Net-negative:
  the gate saturation DIVERGES** — the reversed-edge NF4 (`∃r.D⊑E`, head-on-source)
  is `prop`-optimised (computed once per (filler,role), broadcast), but the composed
  forward-∀ clause (head-on-target) re-fires per edge. So avoiding reversed edges is
  strictly slower; the reversed-edge + `prop` encoding is the efficient one and the
  shared-filler write is intrinsic to the inverse regardless of encoding. Kept gated
  (default off) as a documented negative result.
- **Lever 1 — faster models.** `KM_HT_PAR=48` ≈ `PAR=16` (103s vs 104s) — not
  thread-bound (allocator/memory contention; RSS 2.5→6.7 GB). The candidates provably
  require the exact tableau (the inverse-augmented saturation over-approximates so it
  can't refute a candidate; forward under-approximates so it can't confirm). The only
  real lever is a satisfiable-expander cache made sound under inverse (KM's
  `KM_HT_SATCACHE`/`SATFOLD` are the no-inverse versions) — the substantial remaining
  port. The certified 126s under-budget result stands.

### HT/QoSat: 2b P2 — pseudo-model merge certifies 7581 sound+complete UNDER budget (`KM_HT_QO_PMMERGE`)

Port of the concept part of Konclude's pseudo-model refutation
(`isPseudoModelSubsumerPossible`,
`COptimizedKPSetClassSubsumptionClassifierThread.cpp:1626`). For each tight
inverse-only candidate `(A,B)` from the verify funnel, instead of the blowing-up
`consistent(A ⊓ ¬B)`, build ONE satisfiability model of `A` (`model_root_pos` =
`consistent(&[A])`, far easier than `A ⊓ ¬B`) and **refute `A ⊑ B` iff `B` is
absent from that model's root label** — sound (`B` false in a real, inverse-aware
model of `A` ⇒ `A ⋢ B`). Survivors (B present, undecided) fall through to the full
tableau; refuted candidates are dropped with no tableau test. Gated, default off;
130 cargo tests pass (new: `pmmerge_model_root_refutes_nonsubsumer`).

**Result on ore_ont_7581 (ws): SOUND + COMPLETE + CERTIFIED, UNDER the 240s
budget.** `565317 = gold, 0 unsound / 0 incomplete`, **129s / 2.5 GB** (vs 2a's
**244s**, over budget). The pseudo-model merge refuted **all 177** tight candidates
→ **0 survivors → 0 `consistent(A ⊓ ¬B)` tableau tests** — the hard inverse blowups
that wrecked 2a are never reached (verify stage 0.37s). This is the first time KM
certifies 7581's completeness within budget rather than trusting the forward-only
result.

Remaining gap to Konclude (~10s): the pseudo-model pre-filter spends ~90s building
63 full `consistent(A)` models. Baking the result-identical incremental
blocking/obligation speedups into the model-builder workers (`set_fast_tableau`)
shaves only ~7s — the cost is intrinsic model size. Building the pseudo-model from
the (forward) saturation instead would be **unsound** (the forward label
under-approximates inverse-entailed subsumers; "B absent ⇒ A⋢B" would refute real
subsumptions on load-bearing-inverse onts). Konclude itself builds pseudo-models
from per-concept SAT completions and fast-paths them with a cached ⊤-saturation;
KM's `KM_HT_SATCACHE` is sound only for ALC(H) no-inverse, so it cannot fast-path
7581. The genuine levers to ~10s are a sound inverse-aware fast-sat cache, or a
cb_to_ht inverse encoding that avoids materialised reversed edges. See
`docs/KPSET-PLAN.md`.

### HT/QoSat: 2b Phase A — Konclude G2/G3 inverse-criticality containment check (`KM_HT_QO_KPSET`)

Port of Konclude's saturation criticality
(`isCriticalALLConceptDescriptorInsufficient`,
`CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp:3451) into
`QoSat`. Gated, default off; zero baseline risk (129 cargo tests pass, incl. two
new KPSet tests; the forward-only and verify paths are untouched).

The mechanism (Konclude G2 "from a successor propagate status, never labels" / G3
"insufficient → tableau"): KM now KEEPS the inverse-bridge clauses (materialises
the back-edges, recorded in `inv_edges`), but every concept-head write whose
firing matched an inverse back-edge becomes a **containment check** rather than a
write — `kp_check_head` / `kp_write`, deferred to the saturation fixpoint
(`kp_finalize`, Konclude's `checkCriticalIndividuals` post-pass). The would-be
operand is never added to the shared model; if the target already carries it (the
forward closure forced it) the check passes, otherwise `kp_insufficient` is raised.
Because nothing is written across a reversed edge, the cross-concept shared-filler
conflation (the 6.5M spurious facts on 7581) cannot form.

**Result (ore_ont_7581, ws):** the inverse-AWARE pass no longer blows up — whole
`km classify` runs at forward-only cost (**37s / 1.0 GB**, vs the old
inverse-augmented **111s / 6.5M-fact** pollution), and it is SOUND (never
over-derives; unit tests + gold-exact fallback, 565317 = gold, 0 unsound / 0
incomplete).

**It does not yet CERTIFY 7581.** `kp_miss = 929558` over `inv_edges = 898356`:
KM's cb_to_ht encodes inverse roles as materialised reversed edges, and the 129k
`∃r2.D ⊑ E` clauses fire across them at SHARED fillers, producing ~930k
predecessor-dependent consequences that are not forward-present (all spurious,
since NOINV = gold). The containment check correctly refuses to write them, but the
single global `kp_insufficient` bool is too coarse — one miss at any shared filler
defers the whole classification — so KPSet defers and the pipeline falls back to the
gold-exact forward-only result. Reaching Konclude's insufficient ≈ 0 needs the other
half of the port (study doc P2): **per-node insufficiency** (certify the CLEAN
concepts) + **per-concept possible-subsumer tracking with pseudo-model-merge
refutation** (`isPseudoModelSubsumerPossible`) to prune the spurious possibles
before any tableau test. See `docs/KPSET-PLAN.md`.

### HT/QoSat: verify funnel 2a — structural suspect selection + parallelism (511s → 244s)

Two speedups to the `KM_HT_QO_VERIFY` certification funnel, both sound, both gated:

1. **Structural suspect selection** replaces the inverse-augmented global pass that
   selected suspect concepts (measured **111s** on 7581) with an O(nodes+edges) scan
   of the forward model: a concept is a suspect iff its forward closure can reach an
   edge on an inverse-having role — the only way inverse can affect its
   classification (the `r⁻` back-edge is created from a forward `r`-edge). Sound
   over-approximation; **111s → 0.03s** (flags all 72,989 concepts on 7581, which is
   fine — they funnel to the cheap per-concept stage). `KM_HT_QO_GLOBALSEL` restores
   the old inverse-global selection.
2. **Parallel work-stealing** (per-thread `QoSat` / `Ht`, the `classify_parallel`
   pattern, `KM_HT_PAR`) for the per-concept inverse de-conflation (**~330s → 7.7s**)
   and the candidate verification.

Net on 7581: **511s → 244s**, sound+complete (gold-exact: all 177 tight candidates
verify as non-subsumptions, result = forward `L` = gold).

**Remaining wall (the lever for 2b).** Candidate verification is still ~226s even on
16 threads — only ~1.5× from parallelism — because the 177 tight candidates are the
HARD inverse-dependent pairs and a few of their `consistent(A ⊓ ¬B)` complete-tableau
tests blow up (~hundreds of seconds each), the same complexity as the original 7581
problem; parallelism cannot shrink a single slow test. Deciding those in a sound
*saturation* instead of the blowing-up tableau is exactly Konclude's KPSet (G1/G2/G3)
— see `docs/KPSET-PLAN.md`. So 2a brings the certified path to the budget edge and
confirms the KPSet extension (2b) is necessary, not optional, for fast+certified.

### HT/QoSat: sound+complete verify funnel (correct, but bounded by inverse-saturation cost)

Adds a sound+complete certification path behind `KM_HT_QO_VERIFY` on top of the
forward-only global gate, plus the measurements that show why certified-complete is
*not* fast on 7581. The funnel (`qo_classify_global_fwd` verify-prep):

1. forward-only global pass → sound subsumer lower bound `L` (10s, gold-exact);
2. one inverse-augmented global pass SELECTS suspect concepts (those whose
   inverse-augmented closure exceeds `L`) — a sound superset of the concepts whose
   true classification could differ from forward-only;
3. a per-concept (single-seed) inverse saturation runs ONLY on the suspects and
   de-conflates each to its TIGHT candidate set (single-seed avoids the
   cross-concept filler conflation that bloats the global set);
4. the caller confirms each tight candidate with the complete tableau
   `consistent(A ⊓ ¬B)`. Result = `L ∪ confirmed` = sound + complete.

On 7581 the funnel is correct — it collapses the **6.5M** global candidate pairs
(across 10635 suspects) down to **177** tight candidates, all of which verify as
non-subsumptions (forward-only is complete here). Verification itself is cheap
(measured ~0.02–0.26s per candidate; the 560s in the prior per-concept VERIFY was
the saturations, not the verifies).

**But the certified path is >280s on 7581, and the cause is fundamental.** The
inverse-augmented saturation pollutes catastrophically: the global inverse pass
alone takes **111s** (vs 10s forward-only) building a 6.5M-fact model, and the
per-concept inverse saturations *thrash* (16M edge-ops for a single 71-node
concept). KM's inverse handling reads a shared filler's runtime *label* across
back-edges (an EL backward-link read), so inverse back-edges blow up propagation.
Forward-only (which drops those edges) is the only fast saturation. **The necessary
lever for fast+certified on inverse onts is a sound, efficient inverse saturation
(Konclude's KPSet G2: from a successor propagate only status flags, never labels) —
a substantial algorithm extension, not a routing tweak.** Gated off
(`KM_HT_QO_VERIFY`), zero impact on the 568 baseline. See project_km_7581_qosat.

### HT/QoSat: single-pass forward-only QO gate — 7581 saturation matches Konclude

The per-concept forward-only gate (below) decided 7581 by running one single-seed
saturation **per concept** — 73k saturations, ~109s. `qo_classify_global_fwd`
replaces that with **one** forward-only global saturation seeding every concept as
its own self-node (shared `∃`-fillers), then reads each concept's subsumers off its
own self-node label. This is Konclude's architecture
(`CCalculationTableauApproximationSaturationTaskHandleAlgorithm` = one
approximation saturation; `CPrecomputedSaturationSubsumerExtractor` = subsumers
from a concept's own node). Tried first under `KM_HT_QO_PC`; falls through to the
per-concept gate only when the global pass cannot cleanly decide (a parked
disjunction, `∀`/range filler pollution `qo_insufficient`, or an out-of-fragment
bail). Same soundness/completeness profile as the per-concept gate (sound always;
complete when inverse is non-load-bearing — true for 7581).

Measured on `ws` (same hardware as Konclude):

| | wall | peak RSS | vs gold |
|---|---|---|---|
| Konclude v0.7 | 9.7s | 2.5 GB | — |
| KM QO saturation core (`km tableau` on the TInput) | **10.3s** | 0.69 GB | gold-exact |
| KM end-to-end `km classify` (CB disabled) | **24s** | 1.0 GB | 565317=565317, 0/0 |

So the QO saturation core **matches Konclude** (10s vs 9.7s) at *lower* memory;
end-to-end is 24s (8.6s frontend + 10s saturation + ~5s I/O of the 174 MB output)
versus Konclude's 9.7s. 127 cargo tests pass; 7581 byte-exact to gold.

**Why not a certified-complete verify pass (measured, not done).** Forming the
inverse-only candidate set from a *global* inverse-augmented pass is infeasible: on
7581 the inverse global saturation over-derives **6.5M** spurious candidates
(cross-concept shared-filler pollution), so the complete-tableau verify cannot
finish. A per-concept inverse pass bounds the candidates (~177) but costs one
saturation per concept (~109s) plus a tableau test per candidate (~3s) ≈ 600s — not
Konclude-competitive. A cheap *structural* certificate ("the reversed roles are
never read by a rule body") also fails: 7581's reversed roles are consumed 100k+
times yet contribute nothing (NOINV = gold). So certified completeness under
load-bearing inverse stays the open problem; forward-only is shipped as sound (and
complete on the inverse-inert fragment that includes 7581).

**Harness note.** The Rust orchestrator reads `KM_ENGINE` for the engine-binary
override, not `KM_ENGINE_BIN` (config.rs:84). Scripts/docs that set
`KM_ENGINE_BIN=/bin/false` to disable CB were silently running the real CB engine,
which (on 7581, a CB timeout) starved the niced HT racer and made fallback wait out
`ht_budget_s` (225s) before taking HT's ready answer — the apparent ~238s. With the
correct `KM_ENGINE=/bin/false`, CB errors in 0.25s and the QO answer flows at 24s.

### HT/QoSat: forward-only per-concept gate makes 7581 sound + complete (gold-exact)

`ore_ont_7581` (73k-concept Horn-ALCHQ giant, a CB-engine timeout) now classifies
through the per-concept QoSat gate **sound and complete, byte-exact to Konclude
gold**: `km = 565317, gold = 565317, unsound = 0, incomplete = 0` (validated
end-to-end via `oracle/ore/ore_canon.py`). The gate was previously complete but
produced 106 spurious subsumptions. Behind `KM_HT_QO_PC` (opt-in, not in the
default config), so zero impact on the 568 baseline. 127 cargo tests pass.

**Root cause (pinned, supersedes the earlier range / cardinality / canon-artifact
theories).** The tableau input carries 4 inverse-bridge clauses (a single role
head with arguments swapped versus a body role, `r1(x,y) → r2(y,x)`, encoding the
declared inverse pairs). These create model-specific reversed back-edges
(`filler → r2 → root`); the 129286 NF4-backward clauses then read the shared
concept-node's runtime label across those back-edges, deriving seed-specific
consequences as global subsumers (`b ⊑ ∃r2.D` holds only because `root → r1 → b`
in that one model). This is the shared-filler-in-cycle pollution, attributed to
inverse — there are only 4 range clauses, so range was never the cause. Proof:
dropping the inverse-bridge clauses yields gold exactly, so 7581's inverse is
declared but non-load-bearing (removing it loses zero real subsumptions).

**Fix.** `QoSat::new_opts(clauses, skip_inverse)`: `skip_inverse` drops the
inverse / symmetric bridging clauses. The shared-node saturation may read a
successor's runtime label only across genuine forward `∃`-edges, never across an
inverse back-edge, so forward-only is sound (monotone: dropping clauses never
over-derives) and complete whenever inverse is non-load-bearing.
`qo_classify_perconcept` returns the forward-only result by default. With
`KM_HT_QO_VERIFY` it also runs the inverse-augmented saturation (a complete
superset) and confirms each inverse-only candidate `(A,B)` with the complete
tableau `consistent(A ⊓ ¬B)` — sound + complete + general — but the per-candidate
full tableau is too slow on a 73k giant, so verify stays opt-in. Also ports
Konclude's per-creation-role range folding (`range_class` / `filler_node` /
`node_range`, fillers keyed by `(concept, range-class)`; test
`qopc_range_no_cross_role_pollution`); sound and reduces to the old behaviour when
no range clauses exist, though inert on 7581.

This matches Konclude's saturation (verified against its source):
`getRoleSuccessorALLConceptExtensionData(creationRole)` is per-creation-role
range folding, `isCriticalALLConceptDescriptorInsufficient` is the insufficiency
residue, and KM's defect was the G2 violation (reading a successor's label,
model-specific across inverse back-edges).

Open: 7581 runs ~283 s on `ws` (saturation ~109 s; the rest is frontend parse of
the 37 MB OWL), over the 240 s budget there; the benchmark-host timing is not yet
confirmed. Forward-only is sound everywhere but silently incomplete if inverse is
load-bearing on some other `KM_HT_QO_PC`-routed ont, so a cheap sound completeness
check (the full-tableau verify is too slow) is the remaining work.

### Hypertableau toward SHIQ: sound inverse + functional-merge primitive, two routing-gate fixes, and the Konclude saturation diagnosis (foundations, gated)

Groundwork for solving the disjunction / SROIQ family (`ore_ont_1603, 12653,
16444, 7581, 6934, 9540, 10702, 10908, 15672`) by extending the `Ht`
hypertableau from ALC(H) toward SHIQ, following HermiT's calculus and Konclude's
saturation architecture. Everything here is **gated** (`KM_HT_NUMBER`,
`KM_HT_FORCE`), **zero production impact**, and validated by unit tests; no
ORE coverage change yet — this lands the validated base plus the diagnosis that
re-targets the remaining work.

**Inverse roles in `Ht` — sound, unit-tested.** The `cb_to_ht` inverse bridging
clauses (`r(x,y) → r⁻(y,x)`) already propagate through the existing
`role_triggers → fire_anchor_edge → HeadItem::Edge` path; the prior "inverse is
inert" assumption was wrong about the mechanism. Two tests
(`inverse_role_propagates_universal_back`, `inverse_role_consistent_without_clash`)
confirm `∀r⁻` propagates back along the materialised inverse edge with no
over-propagation. `in_edges` now carries a `DepSet` (the shared structural change
for inverse soundness and node merging).

**Qualified-number node merge (≤n / functional).** Replaced the `apply_head`
`Eq`-head soundness bail with a node-merge primitive (`Ext::merge_into` +
`resolve` + `Trail::Merge`, modelled on HermiT's `MergingManager`): the victim's
concept label and incident edges are copied onto the lower-id survivor under the
union dependency, trail-recorded so backtracking undoes the whole merge; merged
victims are excluded from obligation expansion and blocking. A single `Eq` head
(functionality / ≤1) is a unit merge; multi-`Eq` (≤n, n≥2) still bails soundly.
Three tests (`functional_merge_forces_clash`, `functional_merge_consistent_when_compatible`,
`merge_inverse_existential_terminates`). A gated `RMF_STEP_CAP` bounds the body
matcher so an explosive join falls back soundly to CB instead of hanging.

**Two routing-gate fixes (the reason nothing reached `Ht` before).**
- `tableau.rs` `run_json` had a second in-fragment gate
  (`!inp.number && !inp.inverse && nominals.is_empty()`) independent of the
  `race.rs` routing guard, so every inverse/number ont fell through to the legacy
  tableau (which hangs on real ORE onts) and never reached `Ht`/QoSat. It now
  honours `KM_HT_FORCE`, so the engine actually runs on inverse/number onts for
  measurement.
- `QoSat` (the non-branching saturator) capped at `QO_NODE_CAP = 8000` nodes,
  tuned for the tiny 5303-family. Since QoSat seeds one shared node per concept,
  this bailed instantly on a real ontology (7581 has 72 989 concepts) → fell back
  to the per-concept branching classify, which hangs. The cap now scales with the
  concept count.

**Diagnosis (Konclude trace of 7581).** Konclude classifies 7581 in 5.6 s with
expressiveness `SRIF` (inverse + functional + chains + transitivity; no qualified
cardinality, no nominals): "*ontology has been sufficiently saturated, extracting
data for classification*" + 525 ms classification, i.e. essentially **zero**
tableau tests — the non-branching saturation is sufficient. With the two gates
fixed, KM's QoSat now runs on 7581 and is **bounded** (~73k nodes, no divergence)
but **too slow** (naive worklist + an `O(nodes)` match scan for unbound-source
role atoms; ~860k pending edges). It is a scale/efficiency problem, not soundness
or termination. The next lever is to make QoSat's saturation edge-indexed — the
same ELK backward-link-propagation optimisation already in `elc` — or to extend
`elc` to SRIF and route such onts there.

### QoSat saturation made edge-indexed (the elc backward-link optimisation, ported)

Removes the two `O(nodes)`/`O(#role-clauses)` scans that made QoSat diverge at
the 73k-node scale the 7581 diagnosis identified, porting the exact two index
structures `elc` already uses for ELK backward-link propagation. **Result-identical
by construction** (same clauses fire, same matches found — only located without
the full scans), so it is purely a speed change; gated paths (`KM_HT_QO`,
`KM_HT_HARVEST`) keep their semantics.

- **Incoming-edge index (`QoSat::in_edges`).** `match_body`'s unbound-source role
  case (`r(x, tn)` with `tn` bound, `x` free) scanned all nodes
  (`for sn in 0..label.len()`) to find predecessors of `tn` — `O(#nodes)` per
  match, the dominant cost on transitive / role-chain onts. It now reads
  `in_edges[tn]` (the `(role, source)` list maintained alongside `out_edges`),
  so predecessor enumeration is `O(in-degree)`. The index is trail-recorded and
  rolled back with its out-edge (residue-test DFS stays consistent).
- **Role-keyed clause firing (`QoSat::role_clause_trig`).** The edge worklist
  cloned the entire `role_clauses` list and fired every one on each new edge.
  Role clauses are now indexed by the exact role(s) in their body, so an `r`-edge
  fires only clauses mentioning `r` (a clause without `r` cannot anchor — a
  guaranteed no-op), and clones a tiny per-role bucket instead of the whole list.

New test `qosat_edge_index_role_chain` drives both paths through a transitive
`r`-chain (`A ⊑ ∃r.B, B ⊑ ∃r.G, r∘r ⊑ r, r(x,z) ⊓ G(z) ⊑ H`) and asserts the
closure is unchanged (`H` derived at `node(A)`). Also removed the per-node
`self.global.clone()` in the node-drain loop (an `O(#nodes × |global|)`
allocation), result-identical.

**Measurement (IBEX, 7581, `KM_HT_FORCE`+`KM_HT_QO`, CB isolated).** This
re-targets the prior diagnosis. With the indexes in, 7581 QoSat saturation still
does **not** converge in 420 s (≈1 GB, CPU-bound). Split drain-loop counters
(`QODRAIN`/`QONODE`/`QOEDGE`) show the run never leaves the **literal**
(concept-clause) propagation phase: one `QODRAIN` tick (2M lit-pops), **zero**
node-loop or edge-loop pops. So the role/edge phase the indexes optimise is not
even reached within budget — 7581's wall is the `O(#seeded-nodes × concept-clause
fires)` volume of saturating one shared node for each of its 72 989 concepts
against 455 583 clauses, upstream of the indexed edge phase. The edge index is
correct and necessary (and a clean win on transitive/role-chain onts that *do*
reach the edge phase), but it is not by itself the 7581 lever. The genuine next
lever is architectural, not more saturation indexing: don't seed + saturate 73k
independent nodes — either extend `elc` to SRIF and route such onts to its
told-subsumer single pass, or make the gate per-concept (saturate only the
concept under test). This is the saturation core Phase 5's lazy per-concept gate
needs; the indexing is a prerequisite, the node-count is the remaining work.

### Two attempts at a Konclude-fast 7581 saturation: per-concept QoSat gate (sound, too slow) + elc inverse edges (fast, UNSOUND, reverted)

Following the edge-index measurement (the all-nodes saturation never reaches the
edge phase on 7581), both architectural options the prior entry named were built
behind flags and measured head-to-head on 7581 (IBEX, CB isolated, gold compare).

**Per-concept QoSat gate (`KM_HT_QO_PC`) — sound, kept, too slow.** Instead of one
global saturation seeding all 72 989 concepts, classify by running one fresh
single-seed QoSat saturation per query concept and reading its subsumers off
(`QoSat::reset` reuses the clause indexes; `complete_roles` re-fires role clauses
for guard-after-edge completeness; `node_cap` raised). Clash ⇒ unsat; sufficient ⇒
exact subsumers; insufficient / `Eq`-head ⇒ defer to fallback (sound). Five unit
tests. **Result: timeout** at 280 s (1.78 GB) — the trace never logs even a
5000-concept progress tick in 200 s (< 25 concepts/s), because per-concept
saturation with no told-subsumer sharing re-walks shared sub-closures (≈ O(N²) on
deep hierarchies). Sound but not the lever; kept gated for the per-concept residue
path it still enables.

**elc inverse-role edges (`KM_ELC_SRIF`) — fast but UNSOUND, reverted.** Recognised
inverse bridges `R(x,y)→S(y,x)` as an inverse map and materialised the reversed
edge `(d,S,c)` for each `(c,R,d)` so the existing backward-link / chain / hierarchy
rules fire on inverse edges. **Result: 66 s but wrong** — the EL saturation derives
`⊤⊑⊥` (declares 7581 inconsistent; gold is consistent, 565 k subsumptions). Root
cause: the EL completion rules (R⊥-edge, NF4, NF7) assume an edge `(c,R,d)` came
from an existential `c ⊑ ∃R.d`; a materialised inverse edge breaks that invariant,
so a `⊥` filler propagates back unsoundly. Naive edge reversal is not a sound
encoding of inverse roles in the shared-context model. **Reverted** (`80001cc`);
sound ELI needs a separate backward-concept propagation channel (Kazakov's
consequence-based Horn-SHIQ calculus) — a larger effort.

**Verdict for 7581: neither wins as built** — the per-concept gate is sound but
too slow, the elc inverse extension is fast but unsound. Both were flag-gated and
off by default, so neither changed corpus behaviour (the per-concept gate stays in,
gated; the elc inverse path is reverted). The real lever remains a sound, shared
(told-subsumer) ELI saturation — efficiency of elc with the soundness of the CB
engine — not a quick variant of either.

### Routing: EL-safe giants retry the repair certificate before CB — recovers 15803 + 6212 (565 → 567)

A head-to-head against ELK and Konclude on our 22 remaining failures (their
recorded `peak_mb`/`wall_s` in the bigsweep) showed that **8** of them ELK
classifies *correctly* (gold-match) in seconds at <3 GB while KM times out — and
two, **15803** and **6212**, are EL-safe **>100 MB giants**. For giants the
`elc`-portfolio is suppressed (racing CB and `elc` concurrently OOMs on a
>100 MB ont), so an EL-safe giant with a non-EL TBox residual (a covering
disjunction here) fell to *bare* `elc` with the certificate **off**, bailed
before saturating, and went to the CB engine — which blows up to 18 GB and times
out at 240 s.

Fix (`orchestrate/mod.rs`): when the bare-`elc` attempt on an EL-safe giant
returns "not EL", **retry `elc` with the repair certificate** (`KM_ELC_CERT=2`),
bounded by the existing `elc_force` wall (100 s) and RSS (14 GB) budgets, before
falling through to CB. When the canonical EL model certifies the residual — an
inert / covering disjunction whose EL answer is already complete, exactly what
ELK computes by dropping the non-EL axioms — `elc` answers soundly in EL time and
memory. The retry runs `elc` alone (sequential), so it does not reintroduce the
concurrent-race OOM the giant suppression avoids; the pure-EL giants (8737,
16744, no residual) solve on the first attempt and are untouched.

Result (full `km classify`, default config, gold = Konclude):
- 15803: 240 s timeout / 18 GB → **20.7 s / 1.26 GB, gold-clean** (2 432 194 subs)
- 6212: 240 s timeout / 18 GB → **76.8 s / 1.24 GB, gold-clean** (243 963 subs)
- 8737 / 16744: unchanged, gold-clean.

The other 6 ELK-correct failures (1603, 12653, 6934, 10908, 16444, 7581) are
`el_rbox_safe=False`: their residual is an uncheckable shape (nominals / inverse)
on which the certificate bails, or it saturates then fails — they remain CB/HT
work. The other 14 of the 22 are cases where ELK only *approximates* (drops the
non-EL axioms and disagrees with gold), so they are not EL-recoverable. Note: on
the genuine EL giants KM now uses **less** memory than ELK (8737: ELK 16.4 GB JVM
vs KM 5.5 GB).

### `elc` ELK backward-link propagation + parse-tree discard — 8737 classify 63s → 22s, peak 9.7GB → 5.5GB

Ported ELK's core EL++ saturation optimisation (the *backward-link propagation*
join, "The Incredible ELK" §5) into `elc`, after mapping the ELK Java source
(`ContextImpl`, `SubsumerBackwardLinkRule`, `SubsumerPropagationRule`,
`PropagationFromExistentialFillerRule`). Both changes are **result-identical**
(113 tests pass; 8737 and 16744 both gold-clean, 0 unsound / 0 incomplete).

**Backward-link propagation (time).** After the filler-label indexing, the
Edge-NF4 rule still rescanned `role_supers(r) × nf4_label[d]` per edge — 4.33B
hashmap *probes* on 8737 (`KM_ELC_PROFILE`), most of them missing. ELK instead
keeps, per context, a *propagation* store keyed by role. `elc` now maintains
`prop[(d, r)] = {E : ∃r.X⊑E, X∈label[d]}` keyed by the **exact** edge role
(role-subsumption is already handled by the pre-existing edge-lift, which
materialises every super-role edge as its own worklist item). A new edge `(c,r,d)`
fires `prop[(d,r)]` with a single hashmap lookup; a new filler-subsumer at `c`
registers its conclusions into `prop[(c,·)]` and fires the exact-role backward
links already at `c`. Each (backward link, propagation) pair fires exactly once,
whichever is created second — the same join ELK's two rules perform. Edge-rule
hashmap lookups collapse from **4.33B to 23M** (one `prop.get` per edge); the old
`(role,filler)->[sup]` index is removed. **8737 classify 63s → 22.4s.**
A propagation-Set dedup (ELK's `propagatedSubsumers_` is a Set) was implemented
and measured: bucket-duplication on 8737 is <0.5%, so it only added a `contains`
cost — reverted.

**Parse-tree discard (memory).** ELK drops the OWL parse tree once axioms are
indexed; `elc` was holding the full input — millions of `JClause`, each owning
`String` IRIs — alive through saturation (the `&[JClause]` borrow kept it pinned
in `run_elc`). `to_nf` already interns the EL part into `nfs` (u32-keyed) and
clones the non-EL part into the residual, so the original clause set is dead from
there. `classify` now takes the clauses **by value** and drops them right after
`to_nf`, before saturation, so the parse tree never coexists with the peak
saturation state. **8737 peak RSS 9.7GB → 5.5GB (−43%)**, 16744 likewise; the
explicit dealloc adds a few seconds of allocator work on the giants (the OS would
otherwise reclaim it at process exit) but the giants sit far under the 240s
timeout, and the headroom matters under the parallel memcap.

### `elc` NF4 saturation: filler-label indexing — 8737 classify 84s → 63s

Profiling `elc` on the EL giant 8737 (the slowest EL-routed ORE ont) showed the
saturation is entirely NF4 (`∃R.D⊑E`): the Edge rule scanned **8.6 billion**
`(super_role, d_super)` probes (the whole subsumer label `sub_super[d]` per edge)
and the Sub rule another **1.68 billion** (`KM_ELC_PROFILE` counters; `perf` is
unavailable on the cluster). NF2/NF7 were zero.

ELK only ever propagates over *existential fillers*, so the label entries that can
fire NF4 are exactly the ones that are NF4 fillers. Two changes, both
**byte-identical** (113 tests, same 409836 subjects on 8737):
- **Edge rule** scans `nf4_label[d]` — the maintained subset of `sub_super[d]`
  whose members are NF4 fillers (`is_filler` set once at init; the subset is
  appended in `add_sub`) — instead of the full label. 8.64B → 4.33B probes (about
  half of 8737's label entries are not fillers).
- **Sub rule** is gated on the new subsumer `d` actually being an NF4 filler
  (`nf4_by_filler`), so the predecessor scan runs only when it can fire, not on
  every Sub item. 1.68B → 505M.

8737 classify **84.3 s → 63.3 s (−25%)**, no result change. (An earlier attempt
that iterated the NF4 axioms per edge instead was *slower* — 8737 has many NF4
axioms per role — and was discarded; the filler-label subset is `⊆ sub_super[d]`,
so it is never worse than the original.) A gated `KM_ELC_PROFILE` prints the
per-rule scan counters.

### EL++ reflexive roles in the EL completion (`elc`) — ELK-guided

Native support for `ReflexiveObjectProperty` in the EL fast path, so ontologies
whose only non-EL RBox feature is reflexivity route to `elc` instead of the CB
engine. Studied ELK's source first (`liveontologies/elk-reasoner`): it normalizes
`Reflexive(R)` to `⊤ ⊑ ∃R.Self` and decomposes that into a self-loop link at every
context (`IndexedObjectHasSelfDecomposition`), letting the ordinary composition /
range rules fire over it.

The port mirrors that semantics by **seeding self-edges**: `to_nf` parses the
frontend's reflexive fact `[] → R(x,x)` into a `reflexive_roles` set (instead of
dumping it to the residual), `build_idx` closes it up the role hierarchy
(`R(x,x) ∧ R⊑S ⟹ S(x,x)`), and `classify_inner` adds a self-edge `(C,R,C)` at
every satisfiable concept node. Every existing rule (NF4 `∃R.D⊑E`, NF7 `R∘S⊑T` in
**both** chain positions, ⊥-edge, role-lift) then fires through the normal
fixpoint — no new rule logic. Because a materialized self-edge feeds NF7 in both
directions, this also covers the reflexive-role-plus-chain case ELK marks only
partially supported.

Routing: `rbox.rs` splits the old shared `"reflexivity"` fence into
`ReflexiveObjectProperty` (now EL-safe, admitted by `el_rbox_safe` /
`el_rbox_safe_relaxed`) and `IrreflexiveObjectProperty` (the `R(x,x)→⊥` constraint,
still fenced to CB).

Validation: 2 new `elc` unit tests (NF4 elimination + reflexive∘chain), full suite
113/113. On the ORE corpus the change is confined to the 13 reflexive ontologies —
4 newly route to `elc` (10326, 13078, 8298, 869). The 2 *scored* ones are
gold-clean **byte-identical** (8298 12200/12200 subs, 869 12224/12224; 0 unsound /
0 incomplete) and now finish in ~0.25 s / 42–65 MB on `elc`. Full-corpus
regression sweep: 0 unsound / 0 incomplete (the 9 remaining reflexive onts keep
their CB routing unchanged).

### HT speed: blocking refinements + the per-build floor — 5303 10s→8s seq, 5s→4s par

Two more refinements to incremental subset blocking (`KM_HT_INCRBLOCK2`), both
result-identical (`KM_HT_INCRBLOCK2_CHECK` asserts equality with the full scan every
pass: 0 mismatches over all ~250k recomputes; subs 238/238; 111 tests):
- backtrack now rebuilds only the affected **suffix** — track the smallest node
  whose subset-blocking label changed (a concept removed, or the node removed) and
  set `i2_lo` to it, instead of forcing a full rebuild (`i2_lo = 0`) every backtrack.
- `i2_recompute` clears/retains only the posting-list slots that ever received an
  entry (`i2_touched` + a dedup bitmap), instead of scanning the whole
  `2x|concepts|` slot table on every pass.

Standalone 5303: 10s → 8s single-threaded, 5s → 4s on 8 threads. Corpus-clean
(5303 + the emelim canaries + sampled normals, 0 unsound / 0 incomplete).

**Two larger levers investigated and ruled out — with data:**
- **"Build the deterministic core once, clone per test"** (HermiT/Konclude-style
  amortization of a query-independent backbone). `KM_HT_COREPROBE` shows the
  empty-seed (⊤+TBox) model of 5303 is a **single node**, and the per-concept
  models (256–3064 nodes) share **0%** of their nodes with it — every model is
  100% derived from its own seed concept, so there is no backbone to amortize.
  Consistent with the HermiT trace (it builds 134 fresh models in 0.94s, ~7ms each,
  with no core-sharing). Not viable here.
- **Cutting the blocking suffix further.** `KM_HT_STATS` reports
  `calls / full_rebuilds / avg_suffix`: 249k recomputes, only 1.3% full rebuilds,
  avg suffix 98 nodes. The suffix is already minimal: subset blocking is a
  *sequential dependency* (`blocked[n]` = does any earlier UNBLOCKED node's label
  contain n's), so a change at position `lo` can flip every later node and
  `[lo..nn]` is the smallest correct recompute. `lo` stays low only because the
  live-disjunction family resolves ⊤-disjunctions on mid-id nodes throughout the
  search — intrinsic, not an artifact. Cutting further would need a different
  blocking *signature* (positive-only — changes which nodes block, an ALC+⊔
  completeness risk) or bitset labels (a large `Ext` refactor), not a cheaper
  recompute.

Net for the live ∀+⊔ family's canonical member: **ore_ont_5303 went from a 207s
timeout to ~4s** (parallel) across this work, all sound + complete + result-identical
to the reference search; HermiT (~0.94s) is ~4x off, the practical floor for the
sound+complete subset blocking that this fragment requires (the cheaper core-hashing
modes explode on it).

### HT speed: incremental ∃-obligations (KM_HT_INCROBLIG) — 5303 10s seq / 5s par

With blocking fixed, profiling (`KM_HT_STATS` now splits the per-test wall into
block / prop / expand) put **72% of the wall in the obligation loop** of
`process_obligations`: it re-scanned EVERY accumulated ∃-obligation on every
saturation pass — 240M iterations on 5303 (~933 per pass), each re-running
`has_rsucc` (an out-edge scan). 92% of obligations sit on blocked nodes (skipped
every pass) and most of the rest were already discharged — pure rescan.

Two parallel structures make the loop incremental:
- `node_obligs[n]` indexes a node's obligation positions, so a pass gathers only
  the obligations of currently-UNBLOCKED nodes (the few that can expand), processed
  in index order so the expansion sequence — and the result — matches the flat scan.
- `oblig_sat[i]` marks an obligation discharged (a successor exists), so even among
  unblocked nodes a satisfied obligation is skipped without an edge rescan. Both are
  pruned/cleared on backtrack (a removed edge can un-satisfy one → re-verify).

Together the obligation loop drops from **240,853,407 to 3,155,424 iterations
(76x)** and from 25.8s to 2.3s (11x). Standalone 5303: **25s → 10s single-threaded,
~5s on 8/16 threads**; RESULT-IDENTICAL (subs 238/238, set byte-identical to the
flat scan), 111 tests pass. From the original 207s timeout this is ~40x; HermiT
(~0.94s) is now ~5x off. Wired ON in `orchestrate/race.rs` `spawn_ht`.

### HT speed: incremental subset blocking (KM_HT_INCRBLOCK2) — 5303 25s seq / ~10s par

Profiling the solved-but-slow 5303 (KM_HT_STATS) located the residual cost
exactly: **blocking recompute was 65% of the per-test wall**, and the models are
only ~313 nodes, 92% blocked — **tighter than HermiT's 690-node models**. So KM
was never over-expanding (it folds more than HermiT); the gap was that
`compute_blocked` rescanned every node on every saturation pass (O(n²) per build).
A battery (all under the EAGER+NEGTRIED+ORD=1 combo) confirmed the only viable
lever: the O(n)-hashed blocking modes (core / pairwise) explode the model
(24684 / 14631 nodes, timeout) — **only subset blocking folds 5303** — and
`KM_HT_WITREUSE` is both incomplete (236 ≠ 238) and slower. So subset blocking had
to be made cheap, not swapped out.

`KM_HT_INCRBLOCK2` does exactly that. Blocking is strictly by an EARLIER node
(`m < n`), so `blocked[n]` depends only on nodes `<= n`. Tracking `i2_lo` = the
smallest node id whose label changed since the last compute (a fresh
`add_concept`, a new node, or a backtrack → 0) means a recompute re-evaluates only
the suffix `i2_lo..nn` in id order — a forward pass equal to a full pass because
every node `< lo` is unchanged. In tableau the frontier (label growth + new nodes)
sits at high ids, so the suffix is usually tiny. The posting lists hold only
**unblocked** candidate blockers (the prior `KM_HT_INCRBLOCK` kept all nodes and
was slower on heavily-blocked models).

**Result-identical** to the full scan: `KM_HT_INCRBLOCK2_CHECK` asserts equality
on every pass — 0 mismatches across all 94 5303 builds, output set byte-identical
(238/238 gold-clean), 111 tests pass. Blocking dropped 65% → 23% of wall;
standalone 5303 **54 s → 25 s single-threaded, 24 s → 10 s on 8 threads, 9 s on
16**. Wired ON in `orchestrate/race.rs` `spawn_ht` alongside the search combo
(respecting env overrides). HermiT is ~0.94 s, so KM is now ~10x off (from
~25-50x); the remaining cost is propagation + expansion (the next frontier).

### ore_ont_5303 SOLVED: sound + complete via HT search discipline + fast blocking

`ore_ont_5303` (the canonical ALC(H) member of the live ∀+⊔ disjunction family,
KM's longest-standing timeout) now classifies **sound + complete** — 238/238
subsumptions byte-equal to Konclude gold, unsound=0 incomplete=0 — for the first
time. Standalone HT: **207 s → 23 s single-threaded → ~10 s on 8 threads.** The
+1 completeness gap (CarbonHydrogenSubstructure ⊑ Hydrocarbon) vanished under the
new search; no frontend / transitivity fix was needed.

The gap was never algorithmic — HermiT classifies all of 5303 in ~0.94 s (traced:
134 SAT tests, ~129 backtracks/test). It was **search discipline that KM had but
left OFF by default**, plus a per-step blocking cost:

- **Search combo (the lever).** `KM_HT_EAGER` (fire ⊤-disjunctions only on
  unblocked nodes) + `KM_HT_NEGTRIED` (HermiT startNextChoice: assert ¬D_di after
  a disjunct clashes so siblings unit-propagate) + `KM_HT_ORD=1` (least-failing-
  first disjunct order). Each is inert alone; together they cut the hard concept
  from 6779 backtracks to **41** (fewer than HermiT). Wired ON for the HT racer in
  `orchestrate/race.rs` (respecting explicit env overrides). Sound + complete:
  these reorder / unit-propagate a complete search, never changing SAT/UNSAT.
  Model-shaping levers (pairwise blocking, trigger absorption, harvest) and
  contrapositive determinism were measured and do NOT crack 5303 — search
  ordering does. Conflict learning / QO / SATFOLD remain dead-ends
  (`docs/5303-ATTEMPTS.md`).

- **Inverted-index subset blocking (per-step cost).** `compute_blocked` mode 1
  (subset, the only mode that folds the family enough) was an O(n²) pairwise scan
  recomputed every propagation pass — ~73 % of the per-test wall. Replaced with a
  posting-list intersection over a **reused, concept-id-indexed flat buffer**
  (`BlockBuf`, no per-call HashMap alloc/hashing): a node is blocked iff it
  appears in the posting list of every concept of an earlier unblocked node, so
  only the rarest concept's list is scanned. **Result-identical** to the O(n²)
  scan (canonical set-equal confirmed; old scan kept under `KM_HT_BLOCK_SLOW`).
  114 s → 23 s on 5303; speeds every HT-routed ont.

- **Parallel classify (`KM_HT_PAR=N`).** `Ht::classify`'s 94 per-concept SAT
  tests + Phase-2 confirmations now run across N worker threads via dynamic
  work-stealing (shared atomic index; each worker builds its own `Ht`, 512 MB
  stack for the deep ORD=1 recursion). Set-identical to sequential (a true
  subsumer is in every model's root label; Phase 2 confirms), no Lean re-cert
  (a scheduling change over the same search). The HT racer defaults `KM_HT_PAR`
  to the core count; `nice` keeps it yielding to CB on CB-winning onts.

No soundness regressions: the emelim canaries (9024/12141/541/11460/15491/4604/
9635) and sampled normals stay gold-clean. Lean re-certification deferred (HT and
`cb_to_ht` are not the certified CB calculus).

### QuasiOrderClassification (KM_HT_QO): validated as a dead-end for the disjunction family, gated OFF

The QO driver (`hypertableau.rs::quasi_order_classify` + `QoSat`, ~1265 lines)
ports the Konclude/HermiT architecture both trace docs identify as the reason
Konclude solves the live ∀+⊔ family in <0.2 s: ONE non-branching global
shared-node saturation (disjunctions parked, never case-split; common-disjunct
consequences harvested deterministically), then sat/unsat + possible-subsumers
read off that single model, with a real residue SAT test ONLY for the
"insufficient" concepts that still anchor open parked disjunctions. The premise
is that ~95% of concepts are decided for free.

**That premise is false for this family — proven, not assumed.** Added the
`KM_HT_QO_TALLY` diagnostic (counts dead/sufficient/insufficient per ont without
bailing on the first residue test). On the target onts (IBEX job 47644078):

- **5303**: global model builds, but `queries=94 dead=3 suff=0 insuff=91`,
  median 17 / max 18 open disjunctions per insufficient concept. EVERY concept
  needs a full branching residue SAT test — zero QO leverage. The 22 global
  ⊤-disjunctions saturate every node, so no concept is ever "sufficient".
- **10702 / 1603 / 12653 / 541**: the non-branching global park-saturation
  itself does not terminate in budget (the ∃-chain / transitive blow-up).

**Validation sweep (job 47644343, 587 onts × 2 arms over `km classify`):** arm
`qo` (default-on) vs arm `noqo` (`KM_NO_HT_QO`) differ on exactly 2 onts — 9024
and 12141 both go gold-clean → incomplete-by-623-subsumptions under QO. QO
recovers 0, regresses 2, introduces 0 new unsoundness, no timeout change. So
default-on QO is a strict −2.

**Decision: gated OFF.** `orchestrate/config.rs` `ht_qo` is now opt-IN
(`KM_HT_QO` env), was opt-out (`KM_NO_HT_QO`); the HT racer reverts to the
validated `Ht::classify` (the 565 gold-clean baseline). All QO code stays behind
the flag, inert by default, kept for the record. Build green, 111 lib tests pass.
Confirms the structural diagnosis (`project_km_5303_diagnosis`,
`project_km_family_diagnosis`): this family needs HermiT-grade absorption +
model-based classification, not the QO harvest. The naive `qo_branch_dfs`
residue search (chronological backtracking, depth-64 guard) is itself strictly
weaker than the `Ht::classify` it falls back to.

### Live-disjunction family (5303): decision-on-demand + contrapositive enrichment (in progress, all gated default-off)

Attack on the live ∀+⊔ family (5303/10702/1603/9540). Two mechanisms added, both
sound clause-level enrichments, gated, default-off (no production impact, no Lean
re-cert until empirically validated):

- **`KM_HT_DOD`** (`tableau.rs`): DPLL-style unit propagation over disjunctions —
  inside the saturation fixpoint, a fired disjunction whose disjuncts are all
  refuted but one asserts that survivor deterministically (sound resolution, dep =
  body ∪ refuting deps), one with all refuted clashes; only ≥2-open disjunctions
  branch. The branch loop also skips refuted disjuncts (deps folded into the
  no-good). `KM_HT_CONTRA` companion: contrapositive Horn clauses for clash clauses
  (`A⊓B⊑⊥ ⇒ A→¬B, B→¬A`) so negative literals propagate and feed unit propagation.

- **Key finding:** `run_json` (`tableau.rs:4482`) routes every ALC(H) KB to
  `hypertableau::Ht`, not the legacy `Tableau`, whenever `KM_HT=1` (always set by
  the orchestrator). The family runs on `Ht`. `Ht` already implements
  decision-on-demand (`eval_disj`: Clash/Unit/Branch) plus `KM_HT_WATCH`,
  `KM_HT_NEGTRIED`, `KM_HT_EAGER`, but a clash clause only `raise_clash`es when
  both literals are present — `Ht` never derives the negatives its unit-propagation
  needs. The contrapositive generator was therefore ported into **`Ht::new`**
  (`hypertableau.rs`, `KM_HT_CONTRA`); the `tableau.rs` DOD/CONTRA remain for the
  out-of-fragment fallback. Build green, 111 lib tests pass.

- **Konclude divergence trace:** `docs/konclude-trace-5303.md` (showboat,
  verify-clean) traces Konclude vs KM from source on 5303: Konclude keeps one
  shared node per concept (not model-size), parks disjunctions and never splits
  (harvesting subsumers via common-disjunct extraction), and SAT-tests only the
  INSUFFICIENT residue (~5%); KM's HT builds a model-sized graph and case-splits.
  CONTRA/DOD make individual disjunctions cheaper but do not change that structural
  blow-up — empirical CONTRA×WATCH/NEGTRIED/EAGER measurement on `Ht` underway.

### Hybrid CB/HT main reasoner: KM_HT hypertableau fills CB's coverage gap (monotone-safe)

The ported HermiT-style hypertableau (`hypertableau.rs`, `KM_HT`, driven via
`cb_to_ht`) is sound on its routable fragment (lossless conversion, no inverse,
no nominals; ALCQ allowed) and classifies central-blow-up / context-explosion
ontologies the CB engine times out on. Verified gold-clean through the *same*
`ore_canon.canonicalize` that produces the gold signatures (`engine/py/ht_check.py`):
HT is sound everywhere (no wrong subsumption) but incomplete on the live
disjunction family, with no structural rule separating its complete from its
incomplete onts — so it can never safely replace a CB answer.

`owl_classify` gains `_spawn_ht` + `_race_cb_vs_ht` (gated `KM_HT_RACE`). CB is
the certified primary on one fewer core; the HT racer (single-threaded, niced)
fills only CB's gap:

* `KM_HT_MODE=fallback` (default): HT's answer is used only on a CB failure /
  `KM_HT_BUDGET_S` timeout — monotone, cannot regress a CB-solved ontology.
* `KM_HT_MODE=race`: first valid finisher wins (faster, but can take an
  HT-incomplete answer).

Full ORE sweep (587 onts, 240 s / 20 GB, gold byte-clean; jobs 47570890 /
47571283 / 47571284): base 558, **fallback 562 (+4: ore_ont_4604 9635 11460
15491, 0 regressions)**, race 559 (+3, 2 regressions). Fallback deployed as the
new main hybrid; race not used. HT engine brought from the `ht-port` branch (3
files; CB core unchanged), all gated/inert by default. See `docs/HYBRID-CB-HT.md`.

### Tableau race un-shadowed by the absorption portfolio + gate relaxation for faithfully-encoded number/inverse/nominals (KM_TAB_FEAT)

Side-by-side ORE benchmark (Konclude/ELK/HermiT/KM, one ont per job, all
reasoners sequential on the same IBEX node, 600 s / 56 GB) showed KM and HermiT
time out on DISJOINT sets: 17 onts time out KM but HermiT solves (the live ∀+⊔
disjunction family), 12 time out HermiT but KM solves (near-Horn throughput).
Attacking the HermiT-solves-KM-does-not set surfaced two issues:

1. **The tableau racer was dead in production.** Routing was
   `if KM_ABSORB_PORTFOLIO and KM_ABSORB: _race_absorbed_plain(...)` /
   `elif KM_TAB_RACE: _race_cb_vs_tableau(...)` — mutually exclusive, and the
   production config sets both absorb flags, so `KM_TAB_RACE` was never reached.
   `_race_cb_vs_tableau` now takes an `engine_run` callable and the absorb
   portfolio runs *inside* the tableau race (the tableau is lazy/niced/
   single-threaded, so it costs ~nothing on onts the engine finishes fast).
2. **The race gate deferred on any number/inverse/nominal flag**, even when
   cb_to_ht encoded the feature losslessly (`dropped==0`, `fenced==[]`).
   `KM_TAB_FEAT` lets the tableau race those when nothing was dropped; soundness
   is validated by gold comparison.

Diagnosis of the 15 gold-having targets (none out-of-fragment — all
`dropped==0, fenced==[]`): with the race reached + gate relaxed, **9635 is
recovered gold-clean** (0.4 s, 159 subsumptions, byte-identical to Konclude
gold). The other 14 still time out at 600 s: KM's cache tableau does not
converge on them (5303/9024: 4–5 M dpll steps, depth 400–760, 1000+ restarts;
1603/12653/15672: number/nominals route to the non-cache careful/expand path
which does not terminate). Closing those needs HermiT-grade tableau search
(anchored/pairwise blocking + dependency-directed backjumping), not a gate flag.

### Cache-tableau convergence control — Glucose dynamic restart + no-good DB reduction (KM_TAB_CONV)

Targets the live `∀ + ⊔` disjunction family (5303, 1603, 12141, 10702, 9540, …):
onts the cache tableau reaches but where the DPLL search *oscillates* and never
converges (5303: ~8 M dpll steps, depth 483, still times out). The machinery
that should help — Luby restarts, VSIDS, phase saving — already existed but was
gated off and "recovered 0", because two things were missing:

1. **Unbounded no-good store.** `learn_cap` defaulted to 2 000 000 and
   `check_nogood` runs on *every* DPLL step over the watch lists, so the store
   itself made each step super-linear. Added **size/quality-based DB reduction**
   (`maybe_reduce`): once the store passes `reduce_at` (30 000), keep all "glue"
   (size ≤ 2) lemmas plus the shortest half and rebuild the watch index. Sound —
   a no-good is an entailed lemma, so dropping it only loses pruning.
2. **Pure-Luby restarts fight the deep ∃-chain cache.** A fixed schedule
   restarts mid-chain and discards the conditional pseudo-model cache, forcing a
   full re-walk. Replaced with a **Glucose dynamic restart** (`note_conflict`):
   restart when the *recent* conflict quality (proxied by reason size, smaller =
   better) is materially worse than the global average — the oscillation
   signature — **unless the search is currently deep** (the blocking rule: it is
   building a large model, so do not throw the deep chain's cache away just as it
   converges). Driven off *every* resolved conflict, tainted or not, so it
   engages on the imposed-disjunction (∀+⊔) family where global learning rarely
   fires; VSIDS activity + phase saving still accumulate across restarts to
   redirect the fresh search.

`KM_TAB_CONV=1` bundles the stack (VSIDS + phase + dynamic restart + reduction);
individual flags (`KM_TAB_DYNRESTART`, `KM_TAB_REDUCE`, `KM_TAB_VSIDS`,
`KM_TAB_PHASE`, tunables `KM_TAB_DYN_MARGIN`/`_BLOCK`/`_WIN`, `KM_TAB_REDUCE_AT`)
still override. All of it is pure search-order / redundant-lemma management — it
cannot change the SAT/UNSAT verdict — so no Lean re-cert. Reached in the pipeline
via the existing `KM_TAB_RACE` cache racer (which inherits the job env). Default
OFF pending the IBEX A/B (disjbase vs disjconv, jobs 47529537/8).

### Auto-route KM_SEQ_ORDER by DISJ_INT — self-selecting Sequoia ordering (+6, net faster, gold-clean)

Commit `9aee987`. Rather than ship `KM_SEQ_ORDER` default-on (which taxes
near-Horn onts — 6423 went 6 s → 126 s forced), the engine now decides per
ontology. `Reasoner::saturate` computes **DISJ_INT** (does any clause head hold
≥ 2 concept literals with ≥ 1 internal/normaliser definer?) and calls
`calc::set_seq_order_auto`, enabling the Sequoia definer ordering only when
DISJ_INT ≥ 1. Env still wins: `KM_SEQ_ORDER` forces on, `KM_NO_SEQ_ORDER` forces
off. Both orderings are complete (named concepts stay mutually incomparable
either way), so the router only selects the faster validated regime — no Lean
delta beyond the definer-ordering follow-up already noted below.

Why DISJ_INT is the right feature (`results/seqorder-routing-20260615.txt`,
full-corpus DISJ_INT × regression wall-deltas): `KM_SEQ_ORDER` only changes
derivation when same-term literals include internal definers, so it helps exactly
the onts with definer-disjunctions and merely adds `is_internal` overhead on the
rest. The rule keeps all +6 recoveries and 7/11 speedups, avoids 27/28 slowdowns
(incl. the 6423 +120 s outlier, DISJ_INT = 0 → off); only 18/540 passers route on.

Confirmed two ways on IBEX (new binary, 83 cargo tests pass):
- **Auto sweep, no env flag** (47522857, 587 onts): **546 MATCH, 0 DIFF**,
  gained the same +6 (5107 6246 6682 10908 11016 11291), lost none — set
  *identical* to forced-on. `results/auto-route-confirm-20260615.txt`.
- **Same-sweep base(forced-off) vs auto A/B** (47523500, 2×587, same nodes):
  base 540 / auto 545 MATCH, both 0 DIFF, lost none; on the 540 both-pass onts
  **auto is net −24.6 % wall** (1968 s vs 2610 s) — it captures the
  disjunction-ont speedups while routing pure-Horn onts off (6423 back to 13 s).
  10908 (~190 s) is borderline: ok in the dedicated sweep at 133 s, timed out
  under the heavier 2-arm contention here; base misses it too, so not a
  regression. `results/auto-route-AB-20260615.txt`.

Combination round 2 (47521666, `results/combo2-20260615.txt`): `seqorder` ×
{corecap, earlyunsat, unitsfirst, split, tabrace} recovered **0** of the 29
hardest remaining onts — the residual (disjunction-convergence + throughput
memory) is algorithmically hard, not reachable by composing these performance
levers. (The memory levers do reduce RSS — corecap/units/split flip 15491/10860
memout→timeout — just not enough to finish.)

Deploy: the auto-routing binary is the deliverable (no config change needed —
auto is the default). ws was down this session, so it was built on IBEX; a
production rollout means deploying the rebuilt binary to unimatrix and a
confirmation sweep.

### KM_SEQ_ORDER regression sweep: +6, zero regressions, gold-clean (deploy gate PASSED)

The portfolio (below) found `KM_SEQ_ORDER` recovers +6 onts. Before deploy, the
open risk was whether the Sequoia ordering regresses any currently-passing ont
(memory had it OOMing 5303). Regression sweep (IBEX job 47520358, 1174 jobs = 2
arms × 587 gold onts, 240 s / 20 GB, `KM_ABSORB=1`; raw =
`results/regress-seqorder-20260615.txt`, script `…-20260615.sbatch`):

| Arm | GOLD=MATCH | NOSIG | DIFF (unsound) |
|---|---|---|---|
| base       | 540 | 47 | 0 |
| seqorder   | 546 | 41 | 0 |

- **GAINED** (seqorder ok, base not): 5107 6246 6682 10908 11016 11291
- **LOST / regressed** (base ok, seqorder not): **NONE**

`KM_SEQ_ORDER` **strictly dominates** base on the full gold corpus: +6, 0
regressions, 0 unsound (every one of its 546 answered onts is byte-identical to
Konclude). 5303 stays a non-ok in both arms (it is in neither MATCH set), so its
known OOM is not a regression. This is the strongest validation available — not
just "no regression vs KM base" but "matches the gold reasoner on every ont it
answers." **Verdict: deploy `KM_SEQ_ORDER=1` in the production config** (expected
554 → 560 on the unimatrix pipeline; production sweep validates at scale).

Soundness/completeness note (`engine/src/calc.rs:481`): `KM_SEQ_ORDER` keys the
literal order on named-vs-auxiliary (Sequoia's `ContextLiteralOrdering`): named /
query concepts stay mutually incomparable at the bottom (the unrestricted
`CompletenessProp` regime the Lean proof certifies, so the forward `⊤→B(x)`
readout remains complete), and only internal definers are totally ordered above
(ordered resolution, resting on Sequoia's published SROIQ-classification
completeness). The definer-ordering restriction is the one piece not covered by
KM's current Lean proof; a follow-up Lean cert of ordered resolution on definers
is warranted, but the corpus-wide gold-clean result is decisive empirical backing.

### Candidate portfolio vs the 36 failing onts (branch `portfolio-candidates`, IBEX)

Method (user-directed): instead of deep-diving one improvement, implement several
gated candidates in one binary and race them — and the existing flags — against
the exact failing set on IBEX, gold-compared at 240 s / 20 GB, then combine the
winners. Self-validating: a wrong arm shows as GOLD=DIFF, never a false win.

Failing set = the 36 onts where Konclude=ok but KM≠ok in sweep 6524 (554 ok / 34
timeout / 2 memout): 10621 10702 10860 10908 11016 11291 11460 1194 12141 12653
14817 15491 15516 15672 15803 1603 2669 3215 4604 4669 5107 5303 541 6246 6682
6934 7246 7499 7581 7914 8737 9024 9540 9635 9663 9724.

New gated candidates (all default OFF/inert; commit `31764e0`):
- `KM_CORE_CAP=K` — cap the central successor core size; excess fact triggers
  ride back as `p→p` hypotheses (completeness-safe), bounding the core-growth
  cascade (the shared root cause of the throughput and disjunction blow-ups).
- `KM_SEED_FROM_SUBSET` — seed a grown-core successor from its (subset-core)
  predecessor-in-the-chain instead of re-deriving; sound, fixpoint-preserving.
- `KM_TODO_UNITS_FIRST` — work off empty-body (fact) clauses first; confluent.
- `KM_EARLY_UNSAT` — clear a context's todo once it derives ⊥ (subsumes all).

Portfolio arms (14): base, corecap4, corecap8, seedsubset, unitsfirst,
earlyunsat, combo(all 4), nocentral(ST), highcap(MSG_CAP=200M), split, seqorder,
notrigskip, threads16, tabrace(cache tableau).

**Results (IBEX job 47519642, all 504 jobs complete; raw =
`results/portfolio-20260615.txt`, script = `results/portfolio-20260615.sbatch`):
9 GOLD=MATCH, 0 GOLD=DIFF (zero unsound across the whole grid), 495 NOSIG.**
6 distinct onts recovered out of 36:

| Ont | Recovered by | Fastest wall | Base |
|---|---|---|---|
| 5107  | seqorder, combo, unitsfirst | 28 s  | timeout |
| 6246  | seqorder (137 s), tabrace (31 s) | 31 s | timeout |
| 6682  | seqorder | 24 s  | timeout |
| 10908 | seqorder | 197 s | timeout |
| 11016 | seqorder | 1 s   | timeout |
| 11291 | seqorder | 1 s   | timeout |

Per-arm recovery count: **seqorder = 6** (all of them), combo = 1, unitsfirst = 1,
tabrace = 1 — and every non-seqorder win is a subset of seqorder's. So the entire
portfolio collapses to a single lever: **`KM_SEQ_ORDER` recovers +6, gold-clean.**
The four new candidate flags (corecap/seedsubset/unitsfirst/earlyunsat) recover
nothing seqorder doesn't, and corecap/highcap/threads16/notrigskip recover 0.
`seqorder` also flips 2 base memouts into the converged set (base: 2 memout / 33
timeout → seqorder: 1 memout / 6 ok / 29 timeout), so total-order resolution both
bounds memory and converges faster on these. 11016/11291 finish in 1 s, meaning
base's per-context ordering was the entire problem there, not the instance size.

`KM_SEQ_ORDER` overturns the prior 6246 verdict (memory had it as a "genuine
timeout, not recoverable"; total-order resolution cracks it at 137 s, 31 s under
the cache-tableau race). 8737 reports STATUS=error in every arm — it is a giant
absent from the IBEX corpus (already `ok` in production via `elc`), not a failure.

Caveat before deploy: `KM_SEQ_ORDER` is known to OOM 5303, so it cannot go
default-on without a regression check on the 554 currently-passing onts. Next step
is a full-corpus sweep with `KM_SEQ_ORDER=1`; if it regresses passers it ships as a
router/race (run on the failing tail only, additive-by-construction like
`KM_ABSORB_PORTFOLIO`), otherwise default-on. Either way the +6 are sound (every
recovery is byte-identical to Konclude gold).

Why this replaced the shelved single-candidate work: the shared-successor parallel
strategy was **measurement-falsified** this session (`KM_CTXSPLIT` diagnostic,
commit `2674a11`). On 9663 the clause arena is only 6–8 % of memory; ~half is
per-context `head_indexes` across ~79k contexts, and single-thread central exceeds
20 GB at convergence (115 GB at 4M messages), so query parallelism only multiplies
per-context memory. The cluster is intrinsic-scale, not parallelizable-duplication.

### Absorption portfolio deployed + validated: sequential plain/absorbed (545 → 554, gold-clean)

`KM_ABSORB_PORTFOLIO` (in `owl_classify.py`, gated; enabled in the `kmpf` sbatch
alongside `KM_ABSORB=1` and the `ofn-absorb` frontend) runs the absorbed clause
set as the primary and, *sequentially* (one engine resident at a time, to respect
the 20 GB memcap), probes the plain clause set first for `KM_ABSORB_PROBE_S` (8 s)
to catch the absorption-cliff cases before committing to the absorbed run. A
concurrent race is ruled out by memory: legitimate absorbed runs already reach
~18 GB, so a second engine alongside blows the cap (the concurrent variant caused
7 memouts in cancelled sweep 6338).

Validation sweep **6524** (sequential portfolio) vs the 545 baseline:
**554 ok / 34 timeout / 2 memout**, gold table **554 agree / 0 unsound /
0 incomplete / 0 both** — fully gold-clean at corpus scale. **+10 recovered**
(1340, 2397, 3905, 4205, 6212, 7775, 12698, 14450, 16303, **16444**); **−1
regressed: ore_ont_6246**. Net **+9 (545 → 554)**.

6246 is the lone miss and the gap to the intended +11/−0: its plain run is
sub-second on an idle node but pathologically slow under contention, and the
8 s wall-clock probe landed on a busy node (node007), missed, took the absorbed
path, and blew to 18.6 GB / timeout. The probe is wall-clock so it is node-load
sensitive; the clean fix is a cheap static plain/absorbed router (decide from the
clause set, not from a timed race) rather than widening `KM_ABSORB_PROBE_S` (which
would delay the genuinely absorbed-only onts). The 2 memouts (10860, 15491) were
already not-ok in the baseline, not regressions. The portfolio is verdict-equal by
construction (absorption is equisatisfiable; whichever clause set answers first is
sound + complete).

### Frontend absorption: polarity-gated definitional clausification (+10 ORE coverage, 545 → 555)

`KM_ABSORB` (default off) extends the clausifier's polarity pre-pass to And/Or/Not
definers and emits only the definition direction the concept's polarity needs
(Plaisted-Greenbaum): `Q → C` only when C occurs positively, `C → Q` only when it
occurs negatively; unseen concepts (e.g. ABox assertions) keep both directions.
This drops, at the source, the unguarded excluded-middle disjunction `⊤ → Q ∨ A`
emitted for every reified negation that never appears on a subclass LHS (the
disjointness idiom `X ⊑ ¬A`), and turns an LHS disjunction into Horn rules.

Measured (`ofn`, on vs off): ore_ont_1340 104 → 0 disjunctive heads, 3905 106 → 0,
14450 106 → 0 (fully Horn); residual disjunctions are genuine RHS disjunctions and
are untouched (5303 38 → 37, so 5303 still times out — needs CB ordered resolution).

Validation sweep 6304 (`KM_ABSORB=1`, tableau race off) vs the 545 baseline:
**555 ok / 34 timeout / 1 memout**, gold table **0 unsound / 0 incomplete / 0 both**
(verdict-preserving confirmed at corpus scale — the synthetic definers are never
query targets, so their polarities are fixed by the ontology). 11 recoveries
(1340, 3905, 14450, 12698, 16303, **16444 the long-standing memout**, 2397, 4205,
6212, 7775, **8737 a giant**); 1 regression: **ore_ont_6246** goes 0.35 s/78 MB →
18.5 GB OOM/timeout — dropping the (PG-redundant) AND def directions on a DOLCE-
style covering+disjointness TBox perturbs the CB engine into a blow-up. Net +10.
Kept gated pending a safe deployment (absorbed/plain portfolio for +11/-0, or a
fix for the 6246 cliff) — see memory `project_km_absorption`.

### Tableau Tier-1 search heuristics: VSIDS + phase saving + Luby restarts (gated; not a coverage win)

`KM_TAB_VSIDS` / `KM_TAB_PHASE` / `KM_TAB_RESTART` (all default off) add CDCL-style
search control to the label-caching tableau's per-node DPLL. Pure decision-order /
redundancy, so no Lean re-cert; 2313 stays byte-identical under every combination.
Empirically they reduce distinct-seed count ~26 % and learn 5× more no-goods on
ore_ont_5303 but recover none of the 7 cache-eligible ORE timeouts: their wall is
the ∃-chain seed-space explosion (depth ~483, tens of thousands of incomparable
successor labels), not per-node propositional search. Kept as gated infrastructure;
the live-disjunction family needs disjunction reduction at the source (absorption,
above) or CB-side ordered resolution.

### CB-vs-tableau race hardened: provably zero-cost to the engine

`_race_cb_vs_tableau` now starts the engine first at full cores and spawns the
tableau lazily off the critical path (`KM_TAB_RACE_DELAY`, default 30 s) at
`nice 19`, with robust cancellation. An ontology the engine finishes within the
delay pays zero tableau cost. (A faithful same-node/same-binary A/B showed the
prior race was already net-neutral on the sweep, exonerating it as a regression
cause; the apparent 18-ont drop vs the stale 564 baseline was the Jun 12-13
correctness commits, not the race.)

### Direction C cache path: taint-aware learning + incremental pruning + pseudo-model caching (recovers ore_ont_2313)

Profiling the label-caching tableau (`KM_TAB_CACHE`) on the live-∀+⊔ family
(ore_ont_5303) pinned the wall: a deep ∃-chain (∃-depth 96 → 226+) of
*incomparable* node labels, where (a) no-good learning was disabled at exactly
those nodes and (b) blocking-SAT seeds were recomputed endlessly (cache stuck
~200 against 100k+ seed evaluations). Four sound, gated optimisations, validated
set-identical to the trusted `expand_inc` on 19 in-fragment ORE ontologies (0
wrong answers, 0 panics); commits `dbb474a`, `8231873`.

- **Taint-aware global learning at imposed nodes** (the key algorithmic lever).
  Learning was gated to `key.imposed.is_empty()`, which switches it off at every
  deep ∃-chain node (all carry imposed universals). Replaced with per-literal
  taint propagation in `close_dep`: a derived literal is tainted iff its
  derivation used an imposed (node-specific) clause, and a conflict is learned
  globally iff its whole derivation is untainted (provable from the TBox alone) —
  sound even under imposed constraints, which a coarse "any imposed fired" flag
  would wrongly forbid. `succ_conflict` and `first_disj` report taint;
  `local_search` threads it. On 5303 this breaks the hard-stop at ∃-depth 96 and
  the search advances to 144+ (no-goods 166 → 800+).

- **Pseudo-model caching of blocking-SAT verdicts.** The `used: bool` blocking
  flag became `block_level: usize` = the shallowest stack level any blocking in a
  subtree relied on (`blocked()` returns the deepest blocking ancestor for
  locality). (1) *Self-contained*: a subtree that only blocks on itself-or-deeper
  (`block_level >= own level`) is a self-contained finite cyclic model → cache
  unconditionally. (2) *Conditional*: a seed satisfiable only by blocking on an
  ancestor at level i is cached in a `cond` map valid while that ancestor is on
  the stack (purged on its pop) — every lookup then happens inside the ancestor's
  subtree, which is discarded if it fails. This caches the deep chain whose
  verdicts depend on a stable shallow ancestor, turning re-search into hits.

- **Incremental eager ∃-pruning** (`KM_TAB_EAGER`, default on). The eager
  successor check ran ~59 `build_succ` calls at every one of >1M DPLL steps. A
  step adding no *trigger* literal (one that can change an obligation or fire a
  universal) leaves obligations + successors unchanged, so the rescan is skipped.
  Plus a per-role uni index for `build_succ`. ~1.77x throughput on 5303.

- **Disjunct ordering** (`KM_TAB_ORD`, default 0 = program order). Floats vacuous
  `∀r.L` markers first (`ORD=1`). Measured: program order beats the shallow-model
  bias on 5303 (depth 363 vs 96); pure reordering, set-identical.

**Results (cache path, ord=0):** RECOVERS **ore_ont_2313** — a live-∀+⊔ family
timeout — finishing with 13967 subsumptions **byte-identical to the Konclude gold
signature**. Recovers ore_ont_2066 and ore_ont_5089 (previously timed out on the
cache path). 5303 runs ~3x faster (2.5M → 8M DPLL/280s, ∃-depth 483) but still
does not finish — the search accelerates and deepens yet oscillates rather than
converging (590k no-good hits); 1603, 12141 also still time out. The family is
not fully closed within budget: the residue is Konclude-grade search control, not
a missing soundness/completeness mechanism. Diagnostics: `KM_TAB_HB`,
dpll/depth/cache counters. `engine/py/tab_emit.py` emits a cached TInput from an
ontology for standalone cache-path tuning.

### Direction C: label-caching (global-caching) tableau (`KM_TAB_CACHE`, gated OFF)

A from-scratch rewrite of the tableau's non-careful (ALCH, no inverse / number /
nominals) path from a single global DFS over one shared completion graph into a
**label-keyed global-caching** decision procedure (Goré–Nguyen). The motivating
fact: in ALCH without inverse roles, a node's satisfiability depends ONLY on its
concept label, so a label proven (un)satisfiable stays so wherever it recurs — the
result caches across every node AND across every classify query. `expand_inc`'s
no-good learning could not exploit this because its no-goods were over node-
INSTANCE `(node, literal)` decisions (commit 16ec50b, measured insufficient).

Design (in `tableau.rs`, behind `KM_TAB_CACHE`; `build_cprog` falls back to the
complete `expand_inc` on any clause outside the recognised shapes, so soundness is
never at risk):
- **Two levels.** Level 1 (per node, transient, never cached): a propositional
  DPLL over the node's disjunctions. Level 2 (cached across nodes + queries): the
  satisfiability of each ∃-successor *seed* (its filler plus the universals
  propagated onto it), keyed by `CKey`.
- **`∃r.C ⊑ D` internalisation.** The someValuesFrom-on-LHS clauses
  `r(x,y) ∧ C(y) → D(x)` (82 of them in ore_ont_5303) become the disjunction
  `D ⊔ ∀r.¬C`, the universal disjunct represented as a synthetic marker concept
  carrying a `Uni` that pushes `¬C` to the node's r-successors when chosen.
- **Sound cycle handling without an SCC pass.** UNSAT seeds are always cached
  (sound: unsat under optimistic blocking ⇒ unsat in every context); a SAT verdict
  is cached only when its witness used no on-stack blocking (`used == false`) — a
  genuine finite model, sound to reuse anywhere.
- **Eager ∃-pruning** (every active obligation's successor checked at every DPLL
  level, sound because a partial node-set imposes fewer universals), **subset
  blocking** over the ancestor stack (sound GFP blocking for ALCH; Dickson's lemma
  bounds every ∃-chain), and a **semi-naive indexed `close()`** (Horn closure fires
  only clauses a newly-derived literal triggers; ~50× over the naive scan).

**Correctness validated:** 16 tableau unit tests pass through the cache path; on 5
real ALCH ORE ontologies (ore_ont_11949/9509/10309/13503/2485) the cached
classification is **set-identical** to the validated `expand_inc` output (132 / 81
/ 6 / 113 / 1 subsumptions). No regression to the default build (66 + 16 tests).

**Conflict-directed backjumping + label-based no-good learning (per-node DPLL).**
`local_search` now tracks, for every derived literal, the set of source concept
literals (seed-base + disjunction decisions) it depends on (`cdep`, maintained on a
trail so branches undo in place instead of cloning the working set). On a clash —
complementary pair, ⊥-clause, or an unsatisfiable ∃-successor — the conflict is
that source-literal reason. When asserting a disjunct `d` yields a conflict not
mentioning `d`, the choice was irrelevant and the search backjumps past the whole
disjunction. When every disjunct of a node fails, the resolved conflict
(`guard ∪ ⋃(conf_i \ {d_i})`) is learned as a no-good. Crucially these no-goods
range over CONCEPT LITERALS, not node instances, so one no-good prunes EVERY node
whose label contains it — the cross-node generalisation the earlier
`(node, literal)` learning (16ec50b) lacked. Learning is restricted to nodes with
no imposed clauses (where the derivation is node-independent), keeping it sound.
Validated: 16 tableau tests + the 5 real ALCH onts still set-identical to
`expand_inc` (a trail-undo bug that briefly produced unsound extra subsumptions on
ore_ont_9509/10309 was caught by the A/B and fixed — a clashing literal must be
trailed before the early return). Measured on ore_ont_5303: learning fires hard
(134 no-goods, ~9.7k prune hits) yet the ontology still times out — the search
backtracks through an exponential per-node region at ∃-depth ~226 that learning
prunes but does not eliminate, and smaller no-goods (`KM_TAB_LEARN_MAX=64`)
generalise better than large ones. The production-stack optimisations are in place
and sound but do not close this family within budget; this is the 5th technique to
reach the same wall.

**Recovery of the live-`∀ + ⊔` timeout family = 0** (honest negative result). On
ore_ont_5303 the checker builds a genuinely deep ∃-chain (>1000 successors) whose
labels are pairwise incomparable, so subset blocking rarely fires — the same
deep-model wall that already makes 5303 a timeout for `expand_inc` itself. The
per-node propositional search (120 disjunctions on the ⊤ node) is partly tamed by
eager pruning but the combined depth × width is not. On three other ALCH onts
(8937 / 1420 / 4856) the cached path is *slower* than `expand_inc` (deep-recursion
+ eager re-checking underperform the global DFS), so it is not a strict win and
stays gated OFF. The architecture is sound, validated, and the foundation for a
caching tableau; closing the gap to Konclude on this family needs the full
production-reasoner stack (dependency-directed backjumping + label-based learning
inside the per-node DPLL, smarter blocking), a multi-session engineering effort
rather than an algorithmic gap. This is the 4th approach (CB resolution, CB
splitting, tableau no-good learning, caching tableau) to hit the same wall on this
family; KM stays sound + complete on everything it finishes.

### Direction B: disjunction case-splitting (`KM_SPLIT`, increment 1, gated OFF)

The algorithmic lever for the live-`∀ + ⊔` timeout family (the largest timeout
group, out of parallelism's reach). Design: docs/DISJUNCTION-SPLITTING.md.
Instead of unrestricted resolution on incomparable disjunctions (the blow-up),
classify a query by semantic case splitting: branch on a derived fact-disjunction
`⊤ → l1(x) ∨ … ∨ lk(x)`, intersect the forced units over the open branches, and
close a branch on `⊥`. Each branch runs the tame ordered-resolution closure (a
per-thread `BRANCH_ORDERED` total order); the fallback runs the complete
(unordered) regime — ordered resolution alone is incomplete (the `KM_ORDERED_ALL`
verdict), so the two must be separated per-run, not by a process-global flag.

`classify_assume(query, assume)` runs a branch closure on a fresh engine
(isolation by construction) and reads `ClosureFacts` (forced units, split-point
disjunctions, `⊥`). A **conservative completeness guard** sets `foreign` →
fall back to the complete default engine whenever ANY context holds a
disjunction that is not a query-context body-empty concept-on-x fact-disjunction
(a conditional/role/equality disjunction, or a successor-context disjunction):
the total order could hide a forced unit there and the propositional-on-x driver
does not split it. So `KM_SPLIT` is **SOUND + COMPLETE on every ontology** — the
recovered fragment is the queries whose only nondeterminism is concept
disjunctions on `x` over Horn successors; everything else falls back.

Validation (66+16 tests; A/B vs the default engine):
- **14/14 byte-identical** on the finishable small onts (the guard only ever
  increases fallback, and fallback == default).
- **ore_ont_13383: identical**, where split fully classifies all 368 queries
  with **0 fallback** — the splitting itself (not the fallback) yields the
  correct complete answer on a real named-disjunction ontology.
- Honest correction: an earlier pre-fix run appeared to "solve" 5107 — that was
  the incomplete ordered *fallback* finishing fast with WRONG answers; with the
  per-run ordering fix 5107 correctly falls back to the complete engine.
- **Recovery on the disjunction timeout family: 0** (5107, 5303, 12698, 2313,
  …). Their hard nondeterminism is at the successor/conditional level, so they
  either fall back (→ complete-engine timeout) or the per-branch closure itself
  times out. Recovering them needs **structural splitting** — splitting
  disjunctions inside successor contexts and conditional disjunctions, with
  branch-scoped messaging — which is increment 2 (the genuinely multi-session,
  Lean-cert'd core). Direction A (ordered + selection + residue readout) layers
  on increment 2.

Increment 1 lands the correct splitting machinery and the soundness+completeness
guard; it is a no-op on the benchmark (falls back on the hard family) and stays
default OFF.

**Increment 2 — structural splitting (`d57e30d`).** Generalises the split from
query-root fact-disjunctions to disjunctions in ANY context, keyed by the
context's core (`branch_decisions: core → assumed disjunct facts`, seeded when a
context with that core is created; cores are deterministic given the decisions,
so the same successor context arises and gets the same seed across the
fresh-engine-per-branch runs). This is how a disjunct is assumed in a SUCCESSOR
context — the structure the live-`∀ + ⊔` family actually has (`A ⊑ ∀R.(C ⊔ D)`).
SOUNDNESS guard `chain_unique_contexts`: split only contexts reachable from a
root by single successor edges — the central strategy merges contexts by core,
so a context reached by ≥2 edges represents successors that could pick disjuncts
independently and a shared split would force them to agree (unsound). Everything
else (non-chain-unique, role/eq/non-central disjunctions) falls back.

Validation: 66+16 tests; **14/14 byte-identical** A/B; 13383 identical. SOUND.
Recovery on the timeout family: still **0**.

**Increment 3 — unit-propagation mode + the measured ceiling of lazy splitting
(`079da53`).** The Hyper resolvent builder, under the split regime, suppresses
resolvents that combine ≥2 derived disjunctions (the fact×fact multiplication),
so a branch's per-context clause population stays tame and exhaustive splitting
recovers the suppressed derivations. Sound (14/14 A/B; 13383 identical, full
split / 0 fallback). But it still recovers **0** of the timeout family, and the
node-rate + fixpoint instrumentation shows WHY — two failure modes, both fatal
to *lazy* splitting (saturate to fixpoint, THEN read + split disjunctions):
- 5303/5107/12698/10702: the per-query closure (saturate + inter-context
  message fixpoint) does not complete (<100 split nodes, no progress markers in
  40 s) — the blow-up is in computing the closure ITSELF, before any disjunction
  is available to split. Splitting on top of a closure that never finishes can't
  help.
- 2313: the split loop completes but all 1688 queries fall back (disjunctions in
  non-chain-unique contexts, which the soundness guard refuses to share-split) →
  the complete default engine then times out.

Conclusion: recovery requires splitting **interleaved** with saturation (decide
before the closure explodes) — an incremental decision trail with backtracking —
which fights the monotone append-only arena (retraction). That architecture is a
hypertableau, and the measurement **tilts the Direction C verdict toward a
dedicated/standalone tableau** rather than retrofitting interleaved retraction
into the CB engine. Increments 1–3 land the sound splitting machinery + the
unit-prop component a future interleaved version reuses; all gated `KM_SPLIT`
OFF, no benchmark change.

### Parallel-speed work: dynamic query scheduler (landed) + the parallelism ceiling

Speed push aimed at the timeout tail, learning from Konclude (whose two main
speed sources are aggressive parallelism + lazy tableau-with-caching for
nondeterminism). Findings, with a thread-scaling probe (job 6227, node005,
KM_THREADS ∈ {1,8,16}, 480 s / 220 GB) partitioning the failures by family:

**Lever 1 — dynamic work-stealing query scheduler (LANDED, `7bc8611`).**
The old parallel path split the named concepts into `threads` static
contiguous chunks, one fixed engine each; when the hard query concepts cluster
in the named ordering they land in one chunk and serialise the whole run
(measured on ore_ont_12141). Replaced with `threads` long-lived engines
draining a shared atomic cursor in guided-size grabs (large early for low
contention + intra-engine cross-query context sharing, shrinking to 1 at the
tail), so a finished worker steals the next. Pure scheduling change — each
engine is independent and a query's subsumers don't depend on co-classified
queries (run_for contract), so the partition-independent union is confluent:
no Lean re-cert. `KM_STATIC_SCHED` restores the old path for A/B. Validated:
66+16 cargo tests; subsumptions byte-identical across KM_THREADS=1 / dynamic-8
/ static-8 on 8 onts (16461, 16076, 7270, 7482, 10019, 8169, 13018, 9635).
Also split `apply_pred` into `pred_payload` (reads only the immutable sender)
+ `apply_pred_payload` (mutates only the target) — output-neutral, isolates
the one sender/target aliasing read as a precondition for a future parallel
message-apply phase.

**Lever 2 — intra-saturation parallelism: scoped, then shelved as low-ROI.**
Konclude parallelises the saturation itself; KM only parallelises *across
queries*. The missing piece (concurrent context saturation) is the only lever
for "one giant saturation" onts that query-parallelism can't split. But two
facts make it a poor investment under the real benchmark limits (240 s, 20 GB):

- *Cost:* the saturation core touches the shared arena + intern tables
  directly across ~70 sites (only 6 are the `&[ContextClause]` slice
  signatures; the rest are `saturate`/`add_clause`/`hyper`/`intern_cc`/
  `cc_find` reaching `self.cc_arena` directly). True parallel saturation means
  parameterising that whole core over an arena+intern abstraction (each worker
  sees committed-global ++ its-own-new clauses) or a locked concurrent context
  graph — a multi-session, Lean-adjacent refactor needing iterative validation.
- *Payoff (probe 6227 + memory facts):* the speed-recoverable set is ~1 ont.
  - 12141 + the disjunction family: timeout at 1/8/16 threads, and 8/16
    threads **explode to ~204 GB** — parallelism-resistant *and*
    memory-explosive; needs the algorithmic lever (ordered resolution /
    tableau / BCP), not threads.
  - 16444 (59 GB) and 9724/GALEN (27 GB): both **over the 20 GB memcap**, so
    they are memouts regardless of speed.
  - 16303: th=1 and th=16 both timeout at an **identical 4.93 GB peak** — the
    textbook family-B signature (query-parallelism completely inert; one giant
    saturation). The lone genuine intra-saturation target: fits the memcap but
    needs ~8–10× scaling to clear 240 s.

  Conclusion: bank Lever 1; **shelve Lever 2** (multi-session core refactor,
  memory-neutral, reaches ~1 ont); the productive next lever is the
  disjunction family's algorithmic fix (the largest timeout group, provably
  out of parallelism's reach).

### Sweep 6016: the first fully clean correctness table (datatypes included)

Full sweep with the datatype layer + chain-domain default + Phase-2 engine
(binaries `ofn-dt` / `kobayashi-marust-p2`): **545 ok / 45 timeout /
1 memout; vs Konclude gold 545 agree / 0 incomplete / 0 unsound /
0 both-disagree** — every completed ontology byte-equal to gold, with no
exclusions (ore_ont_6999's datatype gap closed). Zero status regressions vs
sweep 5976 and two recoveries (ore_ont_2397, ore_ont_8737 timeout → ok), so
the new clauses cost nothing net. The 3524 giant's stdout-runaway recurred
mid-sweep and is now fixed at the root (`KM_EMIT_CLAUSES` gating below).

### Nominal-mode r-Pred announcement guard (10594 livelock fix)

The Phase-2 per-source r-Pred path let body-empty ground clauses pass the
body-discharge check vacuously, spraying every ground fact to every context
with a root edge (ore_ont_10594, ~1900 individuals: 3.5M+ Pred messages,
ok → timeout under `KM_NOMINALS`). Restored the announcement guard (an edge
per mentioned individual) with additional nominals (id ≥ `nom_base`) exempt —
they are exactly what Nom conclusions carry and what no context can have
announced. 10594: timeout → 192 s, now faster than the Phase-1 engine on the
same host with identical published output.

### Datatypes: data-property axioms + a concrete-domain oracle

Closes the datatype gap (the last incomplete-vs-gold ontology): ore_ont_6999
is now byte-equal to gold — `Distortion_Type_Affine ⊑ =2 affc2` with
`Functional(affc2)` is correctly unsatisfiable. Two layers, both frontend
(no calculus change, no Lean re-cert needed):

1. **Axiom translation** (`parse.rs`; previously every `Data*` axiom was
   dropped): functionality → role functionality, sub/equivalent/disjoint
   data properties → the role counterparts, ranges → `∀p.__dt__D`,
   `DatatypeDefinition` → concept equivalence. Unqualified data cardinalities
   now count ALL successors (`⊤` filler — the old `__dt__val` filler made
   `≤ n` blind to `DataHasValue` successors). Complex ranges are keyed by
   canonical text (one shared `__dt__opaque` could invent subsumptions
   between different facet restrictions) and typed literals are re-glued
   with their `^^datatype` / `@lang` suffix (the tokeniser splits them off,
   which collapsed same-lexical different-type values).
2. **Pairwise oracle** (`frontend/datatypes.rs`): for the `__dt__` concepts
   occurring in the clause set, decide — per the OWL 2 datatype map — value
   membership, value (in)equality (exact rationals across the decimal tower
   and dyadic float/double, strings, booleans), range subsumption and
   disjointness (integer-tower bounds, string-family tower, partition
   disjointness, interval separation), and finite covers (boolean, DataOneOf,
   small integer intervals): `__dt__D(x) → ⋁ __dt__val__vᵢ(x)`, which with
   value disjointness gives finite-range counting through the engine's
   ordinary equality reasoning. Every relation is emitted as a plain concept
   clause; unknown decisions emit nothing (the old sound abstraction).
   `KM_NO_DATATYPES` disables the oracle pass for A/B.

82 cargo tests pass (5 new oracle tests). Full-corpus validation sweep
pending; built and validated on unimatrix while ws was unreachable.

### Nominals Phase 2+3: Join, r-Succ (*), the Nom rule, and Lean certification

Completes the ALCHOIQ calculus implementation behind `KM_NOMINALS` (Table 3 of
arXiv:1805.01396; design + status in `docs/NOMINALS-CB.md`):

- **Nom** (additional nominals): in the ground context, a hyper-match with
  `σ(x) = o` whose head a-equalities instantiate to `y ≈ y` / `y ≈ f(o')` no
  longer drops them as tautologies (the exact O+I+Q incompleteness) but
  replaces them with `⋁_{k} y ≈ o'_k` over fresh interned additional nominals.
  The disjunction width is `K + K''` (`K + 1` = max neighbour-variable index,
  `K''` = distinct pinned `f(o')` terms): the certified covering bound is the
  sum, and the paper's bare-`K` statement is too narrow whenever `K'' > K`.
  Budgeted (`KM_NOM_BUDGET`, default 4096) with an explicit incompleteness
  warning on exhaustion. Two enabling fixes: the ground context's Hyper now
  considers the side clause at non-side body positions (given-clause
  semantics — provably redundant elsewhere, the Nom trigger here), and the
  symmetric-group strict pruning admits the equal-`y` assignment there.
- **Join**: in-context resolution on ground atoms (cases 1+2 via new
  ground-body/bridge indexes and a `pred_local` refire on ground maximal
  heads; case 3 = provider over `x` + an `x ≈ o` bridge, fired from all three
  arrival orders).
- **r-Succ condition (*)**: pushes are blocked when a subsuming-modulo-merge
  clause shows the element may itself be a nominal (defer to equality
  reasoning).
- **r-Pred pipeline**: per-atom multi-edge discharge (different `A_i` over
  different individual-labelled edges of one source), verbatim `C_i` copies,
  and no edge requirement for head individuals — the old head filter made
  every Nom conclusion undeliverable.
- **Lean (Phase 3)**: `lean/ContextCalculus/Nominals.lean` (sorry-free)
  certifies soundness of all four rules and the grounded substitutions;
  `nom_cover`/`nom_sound` prove the covering bound and the
  conservative-extension soundness of Nom (the interpretation of the fresh
  constants is constructed).
- `owl_classify._run_engine`: the stdin writer thread raced
  `communicate()`'s flush on fast engine exits (`ValueError: I/O operation on
  closed file`); `communicate(input=…)` now owns the write.

Validation: 61 + 16 cargo tests (4 new engine-level tests incl. the paper's
Example 3 and a no-counting negative control); all six pipeline probes match
HermiT (`nom1`, `nom2`, `nom_dl8`, `nom_neg1`, `nom_unsat`,
`nom_oiq_funct` — the last is Example 3 as OWL, the first KM result that
*requires* additional nominals). Inert without individuals: every new code
path is gated on the ground context / ground atoms, and without `KM_NOMINALS`
the reasoner drops individual clauses, so SRIQ-fragment output is unchanged.
60-ontology corpus A/B with this binary pending.

### Chain-domain recognition validated corpus-wide; now DEFAULT ON

Full sweep 5976 (`KM_CHAIN_DOMAIN=1`, all 591 gold-comparable ontologies):
**543 ok / 46 timeout / 2 memout; vs Konclude gold 542 agree / 0 unsound /
1 incomplete / 0 both-disagree.** The single incomplete is `ore_ont_6999`,
whose one missing subsumption (`Distortion_Type_Affine`) is the known
*datatype* gap (identical in the old config) — within SROIQ-minus-datatypes
the corpus is now **0 unsound, 0 incomplete vs gold**, the first fully clean
correctness table. `ore_ont_11745` confirmed fixed at full scale (ok,
unsat=1592, gold-equal).

Landing: the pass is now default-on (`KM_NO_CHAIN_DOMAIN` opts out for A/B
debugging), per the completeness mandate and the disjunction-ordering
precedent. Cost vs the 5941 baseline: `ore_ont_2313` and `ore_ont_8737`
(chain-heavy; 8737 ran ~206 s before) go ok → timeout — honest resource
limits, not silent approximation.

### Frontend: role-chain recognition for pure-domain consumers (`KM_CHAIN_DOMAIN`)

Recovers `ore_ont_11745`, the last unsound-vs-gold ontology: with the flag,
full 11745 is byte-identical to Konclude gold (438277 subsumptions, 1592
unsatisfiable classes, `GO_0008046` correctly unsatisfiable). It was a genuine
unsat under-detection (HermiT-confirmed; an 18-axiom witness reduced from a
STAR module), not the parallel-pipeline artifact earlier assumed.

Root cause: `chain_clauses` / `transitivity_clauses` run inside `augment`
(frontend pass 1) and recognise a chain `R∘S⊑T` only when a TBox consumer
carries a concept on the chain target. A *pure-domain* consumer
`T(x,y) → D(x)` (from `ObjectPropertyDomain(T, D)`) has no such concept and is
added only in pass 2, so the chain feeding a domain restriction was never
recognised. In 11745, `GO_0008046` is a molecular_function (a `SubClassOf`
chain) and, via a transitive `part_of` chain plus `part_of∘ricdo⊑ridpo` with
`domain(ridpo) = biological_process`, also a biological_process; the two are
disjoint, so the class is unsatisfiable. KM reached the chain filler
(`__trans__part_of__GO_0048856`) but never composed it with the domain
restriction, so it missed the clash and emitted the class's ordinary
superclasses (scored as unsound, though KM never derived anything false).

Fix (gated by `KM_CHAIN_DOMAIN` while validated corpus-wide; reordering the
passes is blocked by the `reg.short` name-assignment byte-identity invariant):
`augment` now also returns the detected `ChainInfo`, and after
`domain_range_clauses` are built, `domain_consumer_chain_clauses` emits the
missing recognitions for pure-domain consumers of chain targets — the
`__chain__S__` recognition (any `S`-edge) plus the `R`-composition, and when
`R` is transitive the full `__trans__` up-propagation so the chain composes
across `part_of` hops. Additive and sound (only fresh recognition clauses;
standard chain unfolding, no calculus change, no Lean re-cert): off-flag output
is byte-identical. Reproducers:
`oracle/ontologies/{11745_unsat_core,chain_domain_propagation}.ofn`. Tests:
`domain_consumer_chain_recognition`, `domain_consumer_transitive_chain_recognition`.

### Nominals: grounded CB reasoning (`KM_NOMINALS`, default off) — Phases 0+1

KM's prior nominal handling replaced `{o}` with a fresh concept proxy
`__nom__o` and lifted unconditional ABox facts; sound but incomplete whenever
the singleton property matters. Minimal witness (HermiT-confirmed,
`oracle/ontologies/nom_merge_sub.ofn`): `A ⊑ ∃r.({o}⊓B)`, `A ⊑ ∃r.({o}⊓C)`,
`B⊓C ⊑ E`, `∃r.E ⊑ G` entails `A ⊑ G`, which the proxy misses (the two
successors stay distinct). 60 of the 592 benchmarked ORE ontologies use
`ObjectOneOf`/`ObjectHasValue`.

Implements the ALCHOIQ consequence-based calculus (Tena Cucala, Cuenca Grau,
Horrocks, IJCAI 2018; arXiv:1805.01396) behind `KM_NOMINALS`, mapped in
`docs/NOMINALS-CB.md`. Phase 0 (frontend): under the flag, `augment` emits the
DL7/DL8 defining clauses `⊤ → __nom__o(o)` and `__nom__o(x) → x ≈ o` plus the
ground ABox clauses, and fences ontologies with individuals off the elc path;
off-flag the output is byte-identical. Phase 1 (engine):

- Term space re-encoded to `z < y < x < o_k < f(x) < f(o)` (individuals below
  the Skolem terms, `f(o)` composites packed positionally), a pure id-space
  relabeling validated byte-identical vs the prior binary on `ore_ont_16461`
  and the cardinality probes. The order satisfies Def 3 of the calculus given
  the existing predecessor-trigger-bottom refinement.
- One ground (nominal root) context `v_r` is the only place Hyper grounds the
  central variable (`σ(x) ∈ Σo`); it is created eagerly when ground facts
  exist and holds all ground inference. Ground ontology facts seed `v_r`
  fully and every other context on demand (first clause mentioning the
  individual).
- The Su^r forms (`B(o)`, `S(x,o)`, `S(o,x)`) push their y-form to `v_r` over
  individual-labelled edges (r-Succ); `v_r`'s ground conclusions flow back
  through the existing Pred machinery (r-Pred), with an edge-coverage
  discipline that kept a naive version from livelocking. `x ≈ o` crosses an
  `f` edge as `f(x) ≈ o`, which the receiver's Eq rule rewrites into ground
  atoms. A `v_r` empty clause is global inconsistency.

All five witness probes pass (HermiT-checked): `nom_merge_sub` and the DL8
merge derive the expected subsumption, the two-distinct-nominals negative
stays underivable, and `{o}⊑B, {o}⊑C, B⊓C⊑⊥` is reported inconsistent.
Off-flag and SRIQ-path output are unchanged (every new branch is unreachable
without individuals in the clause set). Known cost on the flagged path:
ABox-heavy ontologies slow down (`ore_ont_10594` 0.6 s → 85 s) — perf and the
remaining rules (Join, the r-Succ side condition, Nom) plus Lean
re-certification are future phases before the flag can default on.

### Frontend: AtMost recognition (`≤n r.F` on the LHS could never fire)

The mirror of the AtLeast gap below, found by inspection: the AtMost
clausification emitted only the constraint direction, so nothing could ever
derive the reified Q and `≤n r.F ⊑ G` was silently incomplete (not
exercised by ORE gold so far). Fix: excluded-middle recognition — fresh NQ
with `⊤ → Q ∨ NQ`, `Q ⊓ NQ ⊑ ⊥`, and NQ ⊑ ≥(n+1) r.F (n+1 witnesses with
pairwise inequalities); a context that refutes the witnesses derives Q.
Polarity-gated (the `⊤ → Q ∨ NQ` split fires in every context): emitted for
negative or unseen occurrences, skipped only when the pre-pass proves the
occurrence positive-only. Probes: `∀r.⊥ ⊢ ≤1 r.J` (vacuous) and
functionality ⊢ `≤2 r.J` (merge-derived) both derive G; negative probes
stay sound. In-corpus clause changes are confined to current timeouts
(10702, 1194, 14817). Test:
`frontend::normalise::tests::atmost_recognition_polarity_gated`.

### Frontend: ≥n recognition clause for n ≥ 2 (the 16461 min-cardinality gap)

The clausifier (`normalise.rs`, `Concept::AtLeast`) emitted the recognition
direction of a reified `Q ≡ ≥n r.F` only for n == 1 (the plain ∃-recognition
clause). For n ≥ 2 no clause could ever derive Q, so a qualified
min-cardinality on the LHS of a subsumption never fired: ore_ont_16461's
single missing subsumption, reproduced in a 21-clause probe (`P ⊑ ∃r.J1,
P ⊑ ∃r.J2, J1⊑J, J2⊑J, Disjoint(J1,J2), ≥2 r.J ⊑ G ⊬ P⊑G`).

Fix: emit the standard contrapositive clausification `¬Q ⊑ ≤(n-1) r.F`, i.e.
`r(x,y0) ∧ F(y0) ∧ ... ∧ r(x,y_{n-1}) ∧ F(y_{n-1}) → Q(x) ∨ ⋁_{i<j} yi≈yj` —
the same clause shape the AtMost branch already produces and the engine's
Hyper + Eq/Factor machinery already reasons over (multi-neighbour-variable
bodies, equality heads). No calculus change, no Lean re-cert: only the input
clause set is completed; the emitted clause is the definitional-extension
direction of the reified Q and is logically equivalent to `≥n r.F ⊑ Q`.
(n == 0 falls out correctly as `→ Q(x)`, since `≥0 r.F ≡ ⊤`.)

The probe now derives P ⊑ G. Frontend output is byte-identical on
ontologies without min/exact-cardinality ≥ 2 (checked on 10); 27 corpus
ontologies are affected and were re-validated against gold. New tests:
`reasoner::tests::min_cardinality_recognition` (engine-level, the probe) and
`frontend::normalise::tests::atleast_two_recognition_clause`.

**Polarity gating**: the recognition clause is pure cost when the `≥n`
occurs only positively (RHS — intro direction suffices), and on
existential-rich ontologies it feeds the live-disjunction blow-up (a single
unqualified `≥5 setting-for` recognition clause on ore_ont_15672/DOLCE
doubles the pipeline wall time: the resolvent residues create new Hyper
providers, mutually incomparable under subsumption). The pre-pass
(`mark_polarity`) now records each AtLeast's polarities; recognition is
emitted unless the concept is PROVEN positive-only (negative or unseen ⇒
emit, so coverage gaps keep the complete behaviour). Even gated,
ore_ont_15672's genuinely-negative `≥5` (an EquivalentClasses conjunct)
keeps its recognition clause and the ontology joins the live-disjunction
timeout family — recovering it is the ordered-resolution workstream, not a
cardinality issue. Test:
`frontend::normalise::tests::atleast_recognition_polarity_gated`.

### Engine: symmetric-group pruning in the Hyper join

The recognition/at-most clause shape is fully symmetric in its neighbour
variables, so the backtracking join enumerated every permutation (and every
equal-term repeat) of each candidate combination — `k^n` assignments where
`C(k,n)` are distinct, ruinous for n ≥ 4. `OntologyClause` now precomputes
its exchange-invariant variable groups (pairwise swap-invariance,
union-find; transpositions of a connected component generate its full
symmetric group), flagging groups whose head carries an equality for every
pair. The join prunes assignments whose group terms are not sorted (strictly
sorted for flagged groups: an equal-term assignment makes some head equality
`t≈t`, a tautology `build_hyper_resolvent` drops). Side-clause variables are
exempt (the side clause is pinned to its body position and not
interchangeable with worked-off candidates). Output-preserving: every pruned
assignment is a permutation of a kept one and yields the identical canonical
resolvent (heads/bodies are sorted and deduped; `Lit::eq` normalises
orientation), so the derived set is unchanged — no Lean re-cert.

### Engine: central-strategy successor cores must hold facts only

With the recognition clause in place, n = 2 worked but n ≥ 3 still stalled
(probe: P with 3 pairwise-disjoint r-successors, `≥3 r.J ⊑ G` ⊬ P ⊑ G; the
real ore_ont_16461 needs n = 4). Trace: P's context correctly derives
`⊤ → A2(f1) | A3(f1) | Q` by paramodulation, but the central strategy had
pushed the disjunctively derived triggers A2(f1), A3(f1) into the successor
CORE alongside the fact A1(f1). The `[A1,A2,A3]`-core context derives ⊥, and
apply_pred conditions the push-back on the whole core — a clause
`A1(f1) ∧ A2(f1) ∧ A3(f1) → ⊥` that would have to cut TWO literals of the
same disjunction at once, which no resolution step can do. The per-disjunct
refutations (`A1 ∧ A2 → ⊥`, `A1 ∧ A3 → ⊥`) were unavailable because the
hypothesis clauses `p → p` added by apply_succ were subsumed by the
over-large core's `⊤ → p`. The legacy non-central strategy (empty cores,
pure hypotheses) does not have the bug — KM_NO_CENTRAL=1 derives G on every
probe, confirming the diagnosis.

Fix: a successor core now contains only the σ-image of FACT triggers (unit
clauses `⊤ → p(f)` in the predecessor); disjunctively or conditionally
derived triggers still travel as Succ messages (edge bookkeeping +
hypothesis `p → p` at the target) but stay out of the core, so their
consequences return conditioned on `p` alone and each disjunct is cut
individually. Context identity (`central_successor_for_core`) keys on the
fact core; hypothesis-only trigger growth keeps the same target and sends
just the new triggers. No calculus-rule change (Hyper/Pred/Succ/Eq schemata
untouched, no Lean re-cert, same category as the central-strategy landing):
cores shrink, so the context invariant (core ∧ body → head entailed) is
preserved, and every previously derived consequence is still derived — the
fact-trigger cores reproduce the old behaviour exactly on ontologies where
all succ triggers are facts (the common case: existential successors).
New test: `reasoner::tests::min_cardinality_recognition_three_witnesses`.
With both fixes the full ore_ont_16461 derives the gold-only subsumption
`Patient1 ⊑ Systemic_JIA_Patient` (≥4 hasAffectedJoint.Joint over 5
pairwise-disjoint joint successors).

### Engine: clause interning (Pred pipeline + global arena) — peak RSS −77%

KM_MEMSTATS accounting (new, diagnostics-only) on ore_ont_9944 at fixpoint
showed each derived clause stored 5+ times across the engine: per-context
`neighbor_pred` copies of back-substituted pred clauses (11.4M instances,
2.06 GB — only 388k distinct, 29x duplication), a full clause copy per
(edge, clause) in `pushed_pred`, full copies in `pred_pool`/`succ_pool` and
`clause_keys`, the `max_head` duplicate, and `Msg::Pred` carrying a cloned
neighbour core + clause per queued message (13.8M messages). On top of that,
the seeded shared closure was cloned into every context (8009 root contexts).

Two interning stages, both representation/sharing only (the derived clause
set is unchanged, so no Lean re-certification — skipping a duplicate Pred
arrival only skips re-deriving clauses `add_clause` would dedup anyway):

1. **Pred pipeline** (`228067f`): engine-level `pred_interned` table;
   contexts hold u32 ids and `neighbor_pred_seen` dedups duplicate arrivals
   (real, from a successor's pre-/post-growth contexts under the central
   strategy). `pushed_pred` keys by (edge → `pred_pool` index). `Msg::Pred`
   carries `{to, from, edge_label, pool_idx}` (24 B, no heap); the sender's
   pool entry and core are immutable, so apply-time resolution reads exactly
   the send-time snapshot. 9944: 8.50 → 4.99 GB, wall 2:58 → 2:26.

2. **Global clause arena**: `cc_arena: [Vec<ContextClause>; 2]`, content-
   interned, split by ordering domain (root / non-root — the same
   (body, head) caches a different `max_head` under the two orderings, so
   the domains are never crossed). `worked_off`/`todo`/pools become Vec of
   u32 arena ids; `clause_keys` becomes HashSet of the id (the id IS the
   content key); head indexes store ids; the shared closures seed ids
   instead of cloning clauses per context. 6.08M worked-off instances
   collapse to 193k distinct (31x). 9944: 8.50 → **1.99 GB peak (−77%)**,
   wall 2:58 → **1:56 (−35%)**, output identical (315,940 subsumptions,
   exact set match). 49+16 cargo tests pass.

This is the lever for the 9724 (GALEN) memout, which churns >82 GB
unconverged on the old representation.

### Engine: complete disjunctive case analysis (same-term literals incomparable)

The context literal ordering (`calc.rs pred_lteq`) imposed a total order on
same-term concept literals (iri id + internal-definer-low), applying the
mutually-incomparable refinement only in root contexts. That total order is
incomplete for disjunctive consequence finding: once a disjunct stops being
maximal it is never resolved, so a head disjunction never fully case-splits.
Minimal probe (CB engine): `A ⊑ ∃R.(C⊔D), C⊑E, D⊑E, ∃R.E⊑G ⊬ A⊑G` (the engine
derives `C(f)|Q_2(x)` and stalls). This is the root cause of the incomplete
disjunctive ORE ontologies (12698's `∃`-filler disjunction + transitive role).

Fix: concept literals on the same term are mutually incomparable in every
context, so Hyper fires on every disjunct and the case split completes. This
matches the Lean completeness proof, which models Hyper as resolution on an
arbitrary atom (`CompletenessProp.lean`) with no ordering assumption -- the total
order was never part of the certified calculus. Sound by construction (ordered
resolution is sound for any selection). Validated on probes + ORE 2313 / 12698
minimal cores; 65 tests green; Horn (single-head) reasoning is unaffected.

TRADEOFF (sweep 5814): genuinely-disjunctive ontologies now explore all branches,
which is heavy (12698 ~16-19 GB). About 10 ontologies regress ok→timeout/memout.
This is fundamental -- completeness on disjunctive inputs requires full case
analysis -- and is recoverable only by performance work (stronger redundancy on
disjunctive clauses, or decoupling Hyper-maximality from Succ-trigger selection),
not by weakening the ordering. `KM_DUMP_WO=1` dumps every context's worked-off
clauses (debug, env-gated). `KM_NO_PRUNE=1` disables inert inverse/role-bridge
pruning (diagnostic; pruning is sound -- disabling it does not recover the
remaining inverse-role / GALEN incompleteness, which is a separate engine gap).

### Frontend: handle EquivalentObjectProperties (was silently dropped)

`EquivalentObjectProperties(R1 … Rn)` had no parse arm in either the AST path
(`parse.rs`) or the streaming RBox builder (`rbox.rs` `rbox_node`), so role
equivalences were dropped. Every inference that bridges two equivalent roles was
lost. Minimal witness extracted from ORE `ore_ont_2313` (`ddmin`, oracle =
HermiT entails `C ⊑ D`), a 3-axiom core:

```
SubClassOf(TO_0000059, ObjectSomeValuesFrom(BFO_0000050, TO_0000056))
EquivalentObjectProperties(BFO_0000050, PPIO_0000091)
ObjectPropertyDomain(PPIO_0000091, PPIO_0000069)
⟹ TO_0000059 ⊑ PPIO_0000069
```

The existential uses `BFO_0000050`; the domain is stated on the equivalent
`PPIO_0000091`. Without the equivalence the two roles never connect, so the
domain never fires on the existential's Skolem edge. `2313` was missing 88 such
subsumptions.

Fix: expand `R1 ≡ … ≡ Rn` into pairwise both-direction inclusions. `parse.rs`
emits the AST `RoleInclusion`s (so `normalise` produces the subrole clauses that
reach the reasoner); `rbox_node` emits matching `Subrole` records (routing /
relevance / domain-range). Any inverse member fences the axiom to the CB engine.
`2313` now matches gold exactly (88 missing → 0, 0 extra). 57 ORE onts contain
the axiom; the change is sound (role equivalence = mutual inclusion) and can only
recover entailed subsumptions. Tests green.

### Correctness tail: sound datatype-ABox precheck + complex-domain clausification

Resolved the four "unsound vs gold" ontologies and recovered one incomplete one.
The headline result is that KM was never unsound on the four flagged ontologies:
they are all genuinely **inconsistent**, and the gold signatures were wrong.

**Proof the gold was wrong.** Delta-debugging (`ddmin` over the axioms, oracle =
HermiT-reports-inconsistent) reduced each of `8941` / `13912` / `15516` / `2669`
to a 2–8 axiom inconsistent core. Running those cores through HermiT *and*
Konclude directly, both reasoners report inconsistent (Konclude prints
`EquivalentClasses(Thing Nothing ...)`). The recorded gold said "consistent"
because of two benchmark-harness bugs, both fixed:
- `ore_canon.py` canonicalised Konclude's `Thing ≡ Nothing` (its encoding of an
  inconsistent ontology) into "consistent with N unsatisfiable classes". It now
  maps `owl:Thing` in the `owl:Nothing` SCC — and any `consistent=false` — to the
  uniform empty inconsistent signature.
- `ore_runone.py` recorded Konclude's exit-0-with-empty-output on a SWRL
  `DLSafeRule` parse failure (`15516` / `2669`) as a bogus "consistent". It now
  flags Konclude "All parsers failed" as `error` (excluded from comparison).
The gold was regenerated for every affected ontology.

**KM side (`frontend/data_abox.rs`).** The CB engine drops the ABox, so these
asserted-data clashes never reached saturation. A new sound precheck detects:
- range-vs-literal clash: a `DataPropertyAssertion` whose literal value-space is
  disjoint from a (possibly sub-property-inherited) `DataPropertyRange`
  (`8941`: `xsd:string` range carrying a language-tagged literal — an
  `rdf:PlainLiteral`, never in the string value space);
- functional-data clash: `FunctionalDataProperty` with two provably-distinct
  values on one individual;
- an at-most-1-driven ground individual merge (closing role assertions under
  symmetry / inverse / sub-roles and domain/range typing) feeding a
  `DataMax`/functional clash or a `DifferentIndividuals` violation (`13912`:
  symmetric `Owner` + domain `Photo` + `Photo ⊑ =1 Owner` merges two photos,
  then `Photo ⊑ ≤1 url` clashes their distinct urls);
plus an asserted-member-of-unsatisfiable-class rule (`asserted_classes` on the
ofn meta; `owl_classify` makes the ontology inconsistent when a class proved
unsatisfiable has a provable asserted member). Every clash is an OWL 2
entailment; caps degrade to "not detected" (incomplete, never unsound).

**Incompleteness.** `parse.rs` now clausifies a COMPLEX
`ObjectPropertyDomain`/`Range` on a named role as the equivalent class axiom
(`∃R.⊤ ⊑ C` / `⊤ ⊑ ∀R.C`) instead of dropping it as `complex-domain`. The
named-class case stays on the rbox path (byte-identical). Recovers `ore_ont_4827`
exactly (the olia `domain(hasCase) = Adjective ⊔ ...` chain via `∃hasCase.Self`).

**Validation.** 19 new `data_abox` unit tests; full suite green. Whole-corpus
frontend differential: clause + meta output byte-identical on every ontology
except those newly flagged inconsistent; all newly-inconsistent ontologies
confirmed inconsistent by HermiT/Konclude (zero false positives). Remaining
incomplete onts are deeper engine gaps: `16461` (1 nominal subsumption, CB drops
individuals); `2313` / `12698` / `9944` (existential-superclass `∃R.C`
propagation).

### EL completion: clone-free hot loop (recovers giant ore_ont_8737)

The `elcomplete` worklist saturation cloned a state collection on every
Sub/Edge item to satisfy the borrow checker. On the transitive ORE giants this
dominated: transitivity is encoded as NF4, so the existential rules fire on
huge predecessor and superclass sets, and each firing paid a full-set clone.
Three changes remove the per-item allocations:

- `in_edges` is `Vec<Vec<(parent,role)>>` instead of `Vec<HashSet<...>>` — a
  pair is appended only in the `edges[parent].insert` success branch, so
  duplicates were already impossible and the set bought nothing. The Sub-side
  NF4 rule and ⊥-edge back-propagation iterate it by index (new entries pushed
  during the loop are picked up by the growing bound), clone-free.
- The Edge-side NF4 rule collects conclusions into a reused `nf4_buf` during a
  read-only scan of `sub_super[d]`, then applies them (replaces a full-superset
  clone per edge).
- NF4/NF7 rule blocks are skipped outright when their indexes are empty.

Schedule-only change: the same conclusions are derived, possibly in a different
order; the fixpoint is unchanged (saturation is monotone + confluent), so no
Lean re-cert. Validated: 53 unit tests; gold-identical signatures on controls
16744 / 10016 / 1559 / 13482.

Effect: `ore_ont_8737` classify 252 → 221 s standalone; in the benchmark
pipeline it went **timeout → ok at 205.7 s** (9.5 GB peak), signature
byte-identical to the Konclude gold. `ore_ont_16744` pipeline 167 → 151 s.

**Full-sweep confirmation (job 5690): 564 ok / 26 timeout / 1 memout**, vs
gold 554 agree / 6 incomplete / 4 unsound / 0 both-disagree — agree +1 (the
recovered 8737), no regression anywhere. All three 3M-axiom giants (8737,
15059, 16744) now classify within budget via the EL path.

### EL fast path: optional canonical-model completeness certificate (`elc`)

`elcomplete::to_nf` no longer aborts on the first non-EL clause: it collects the
non-EL clauses into a *residual* and still saturates the EL subset. With
`KM_ELC_CERT=1`, `classify` then checks every residual clause against the
saturated **canonical model** (domain = satisfiable concept nodes; `x_C ∈ D^I`
iff `C ⊑ D` derived; `(x_C,x_D) ∈ R^I` iff edge `(C,R,D)` derived). If all hold,
`I ⊨ O` for the full ontology, so the EL classification is exact (sound AND
complete) for subsumption, unsatisfiability, and consistency; any failure (or a
work-budget overrun) returns `None` and the caller falls back to the CB engine.
Never an approximation. 7 unit tests; the certificate logic is a calculus-logic
addition and needs Lean certification of the canonical-model lemma (deferred).

**Default OFF.** On ORE 2015 every non-EL residual is a live covering
disjunction (`⊤ → A ⊔ B`), a non-inert inverse bridge, or multi-successor
functionality — none of which the canonical EL model satisfies — so the
certificate never passes there (verified: fails at residual clause 0 on
4205/6212/15803/7127/7246/11311), and attempting it would saturate the large EL
subset before failing, stealing time from the CB fallback. With the flag off,
routing is byte-identical to before (`to_nf` returns a non-empty residual ⇒
`classify` returns `None` ⇒ same exit-3 fallback). The capability is for
near-EL ontologies whose non-EL part IS model-satisfiable.

Also in `elc.rs`: read stdin as raw bytes + `serde_json::from_slice` (skips the
whole-buffer UTF-8 validation and a second allocation; lower peak memory), and
`KM_ELC_TIMING=1` per-stage timing. The timing showed the ORE giant
`ore_ont_8737` is **saturation-bound** (read 0.5 s, parse 8 s, classify 252 s,
serialise 2.8 s) — its 240 s timeout is the EL completion itself, not I/O, so it
needs a faster (parallel, ELK-style) completion, not an I/O fix. `ore_ont_16744`
classify is 83 s.

Goal: close the remaining ORE 2015 coverage gap to Konclude (was 551/590 ok;
40 failures = 21 timeout + 19 memout). Diagnosis, fixes, and benchmark deltas
tracked here.

### Frontend (`ofn`): inverse-role bridge clauses (8+ incomplete → agree)

`InverseObjectProperties(R, S)` was parsed into `hooks.role_inverses` — which no
code consumed — and `ObjectInverseOf(R)` in concepts became a fresh role
`__inv__R` with no clause linking it to `R`. The engine has no inverse machinery
of its own, so inverse-role semantics was silently dropped. Diagnosed on the
SWEET cluster (`14896`/`3795`/`4834`/`6060`/`7025`/`7320`, 24 byte-identical
missing subsumptions each): the gold derivation `Age ⊑ Set` needs
`temporalPartOf ⊑ subsetOf`, `inverse(subsetOf) = supersetOf ⊑ setRelation`,
`range(setRelation) = Set` — i.e. range of a superproperty of the inverse.

`normalise.rs` now emits the two bridge clauses `R(x,y) → S(y,x)` and
`S(x,y) → R(y,x)` per inverse pair (the same swapped-orientation shape as
symmetric roles, which the engine already propagates; verified on `14896` where
the engine derives exactly the 24 gold subsumptions once the bridges exist).

Two hardening fixes rode along: `elc`'s NF6/NF7 recognizers ignored variable
wiring (a bridge clause would parse as a FORWARD role inclusion — unsound; a
chain could bind in listed order, not chain order) and now check the wiring
explicitly, rejecting anything else to the CB engine (exit 3). `el_rbox_safe`
is also forced false whenever an inverse pair was registered, covering bare
`ObjectInverseOf` which produces no rbox record.

Clause output is byte-identical on ontologies without inverse constructs;
inverse-bearing ones gain only the bridge clauses. Harness-validated: the six
SWEET-cluster ontologies plus `3050` and `8999` flip incomplete → AGREE
(8 of the 17 incomplete; the rest have other causes). Sound by construction
(the bridges are the first-order semantics of the axiom; saturation only gains
derivations). No Lean re-cert (frontend/input clauses; calculus untouched).

### Frontend (`ofn`): sound ABox-inconsistency precheck (4 unsound → agree)

Re-diagnosed the 8 "unsound vs gold" ORE ontologies. The dominant cause is NOT
the nominal/number under-detection previously assumed: for `6720`, `15288`,
`443`, `7052` the **ABox** forces an individual into two disjoint named classes,
so the ontology is **inconsistent** (HermiT agrees; Konclude and ELK report all
classes unsatisfiable). KM missed it because the CB engine drops every
individual/ABox clause (`reasoner.rs` maps `Ind`/`Aux` terms to `None`), so the
clash never reaches saturation — KM emitted the full taxonomy of subsumptions,
which the aggregator scored as spurious "extra" subsumptions.

Witness (`6720`): `lemon_slice` is asserted both `fruit` (⊑ `non_alcoholic_-`
`ingredient`) and `sparqling_wine` (⊑ `alcoholic_ingredient`), and those two are
`DisjointClasses`.

New `frontend/abox_consistency.rs`: a sound, conservative precheck over the
parsed ontology. It closes ABox membership under the named subclass/equivalence
hierarchy, object-property domain/range, and `SameIndividual`, then reports
inconsistency iff some individual is provably in both ends of a named
`DisjointClasses`/`DisjointUnion` pair. Only NAMED classes participate (complex
operands and complex assertion concepts are skipped), so every fire is a genuine
OWL entailment — no false positives. The flag rides the `ofn` meta as
`abox_inconsistent`; `owl_classify` short-circuits to an inconsistent result
(empty subsumption set, matching the gold reasoners) without invoking the
engine. Cost is one TBox scan and an early-out (`None`) unless the ontology has
named-class disjointness, so the giants (no disjointness, no ABox) pay nothing.

Clause output is untouched (byte-identical); the only meta change is the added
`abox_inconsistent` field. Corpus-wide the flag fires only on the four family
ontologies plus two non-gold ontologies (`11305`, `11457`, both genuinely
inconsistent), and no ontology Konclude classifies consistently. Soundness vs
gold: **8 unsound → 4 unsound** (remaining: `7901` datatype empty data-range,
`8941` ALC `∀`-driven, `15516`/`2669` complex-boolean over-derivation); agree
530 → 534. No Lean re-cert (frontend, not calculus).

### Frontend (`ofn`): streaming parse + compact clause set (giant ontologies)

The three 3M-axiom giants (ore_ont_8737, 15059, 16744; 450–580 MB OFN) memouted
**in the frontend** at ~20 GB before the reasoner ever started. Three changes,
all output-preserving (byte-identical clause+meta JSON to the old frontend on the
full ORE corpus and on all three giants), cut the frontend peak ~5.5x:

- **Zero-copy tokeniser / parser** (`sexpr.rs`): tokens are now `&str` slices into
  the source produced by a lazy iterator, instead of a `Vec<String>` with a heap
  allocation per token. The parse tree (`Node`) borrows those slices. The
  whole-document token vector and its per-token strings are never materialised.
- **Streaming document walk** (`parse.rs` `for_each_ontology_child` /
  `parse_axioms`): each `Ontology(...)` child is parsed, turned into SROIQ
  axioms, and dropped, so the whole-document AST is never resident. The RBox /
  declared-class side scans re-stream the (cheap, zero-copy) parse instead of
  retaining and **deep-cloning** the AST across `normalise`/`augment` (the old
  `onto_nodes = args.clone()` was itself an O(document) copy). `reg.short` call
  order is preserved, so assigned internal names are identical.
- **Compact `DLClause`** (`clauses.rs`): `body`/`head` are sorted-deduped
  `Vec<Atom>` (canonicalised in the constructors) instead of `BTreeSet<Atom>`.
  A `BTreeSet` node over-allocates even for a 1–2 atom clause; on 3M clauses that
  dominated memory. `Ontology` also stores axioms behind `Rc` so the dedup set
  shares the allocation instead of cloning every axiom.

Measured on ore_ont_8737 (472 MB): frontend peak **19.2 GB → 3.6 GB**, wall
45 s → 20 s (per-stage `VmHWM` via `KM_OFN_TIMING`: normalise 9.4→2.6 GB,
augment 18.6→3.5 GB). Result: **ore_ont_15059 recovered** (was memout; now ok in
70 s / 5 GB, signature identical to the Konclude gold — consistent, empty
#UNSAT). 8737 and 16744 now reach the reasoner (frontend no longer the wall) but
are **not** EL-safe (inverse roles), so they route to the context engine and
remain time-bound there — the engine-scaling residual, not the frontend.

### Result (ORE 2015, 240 s / 20 GB, gold = Konclude 587 ok)

| build | ok | timeout | memout | vs baseline |
|---|---|---|---|---|
| baseline (16-thread, pre-fixes) | 551 | 21 | 19 | — |
| + Hyper join + adaptive retry | 553 | 33 | 5 | +2, 0 regressions |
| + message batching | 554 | 31 | 6 | +3, 0 regressions |
| **+ streaming frontend (final)** | **555** | 32 | 4 | **+4, 0 regressions** |

Recovered: 2397 (fully correct), 9944, 9724 (sound but CB-incomplete on
number/inverse), and 15059 (the giant — see the frontend section; agrees with the
Konclude gold). Soundness preserved: vs gold the correctness profile is unchanged
(530 agree, 17 incomplete, 8 unsound — the pre-existing CB nominal/number
under-detected-unsat cases — both-disagree = 0); the one newly-classified
ontology (15059) agrees with gold, and no previously-agreeing ontology regressed.
All landed changes (Hyper join, batching, streaming frontend) are
output-preserving, so they change *whether* an ontology finishes in budget, never
*what* it derives. km has the lowest median peak memory of the five reasoners
(45.9 MB; Konclude 65, Sequoia 536).

Residual is genuinely hard for the CB engine: live-`∀+⊔` disjunction
(message-traffic explosion — Sequoia, the same calculus, solves these via more
mature redundancy/ordering), the two remaining giants (8737, 16744 — frontend now
fits, but they are not EL-safe so they route to the context engine and time out
there), four CB-engine ~20 GB memouts (10781, 15491, 16444, 6682), and role-chain
propagation volume. The hypertableau (`tableau_cli`) is NOT a fallback: it errors
or hangs on real ORE ontologies (validated only on small synthetic + kinship).

### Hyper rule: backtracking join instead of full cartesian product
- `engine/src/engine.rs` `hyper()` / new `hyper_join()`: the Hyper rule used to
  build a candidate list per body position and iterate the **full cartesian
  product**, attempting unification per combination and discarding the ones that
  fail cross-position variable consistency. On number restrictions
  (`R(x,y1) ∧ C(y1) ∧ R(x,y2) ∧ C(y2) → …`) that is `(#successors)^k`
  combinations, almost all immediately discarded.
  Measured on ore_ont_13912: **738171 enumerated, only 2462 unifiable (99.7 %
  waste)**.
  Replaced with a backtracking join that extends the central substitution one
  body position at a time and only descends into candidates consistent with the
  bindings already made (shared neighbour variables bound earliest). Yields the
  **identical resolvent set** — the skipped combinations were exactly the ones
  that fail `unify` — at a fraction of the enumeration. Same ont: 738171 → 59410
  combinations (12×). All `cargo test` pass (incl. `factor_number_restriction_clash`,
  `existential_subsumption`). No change to soundness/completeness; pure
  enumeration optimisation.
- Added env-gated `KM_PROF` diagnostics (per-query seeding + message-loop
  progress, per-rule saturate counters). Off by default, no hot-path cost.

### Message loop: batched propagation
- `engine.rs` `run_for`: the inter-context message fixpoint used to `saturate`
  *and* `propagate` the target after **every** message. On disjunction/role-chain
  ontologies that re-scans each context's predecessor-edge and Succ/Pred pools
  thousands of times (ore_ont_5303: ~86 k propagate calls). Applying a message
  never enqueues new messages (only `propagate` does), so the loop now **drains
  the whole pending batch**, saturates each target, records the touched contexts,
  and propagates each **once** per round. `apply_succ`/`apply_pred` return the
  touched context instead of propagating inline. Fixpoint unchanged (saturation
  is monotone and confluent — the schedule does not affect the derived set);
  ~1.5× faster message throughput. Recovers ore_ont_9724; all `cargo test` pass;
  vs gold no new unsound/incomplete.

### Threading: adaptive parallel-then-single-threaded-retry (memory-aware)
- Root cause: `reasoner.rs` `saturate()` splits the named queries into
  `available_parallelism` chunks, each a full `Engine` that **re-derives the
  shared successor contexts**. On existential-heavy ontologies this multiplies
  the dominant cost by the thread count. Measured on ore_ont_2397 (ALCH): 1
  thread = 9 GB / 138 s **SUCCESS**, 8 = 40 GB, 16 = 84 GB, 64 = 20 GB **MEMOUT
  @ 9 s**.
- A *blanket* `KM_THREADS=1` is **net-negative**: it recovers the memory-bound
  onts but regresses the speed-bound ones (measured: −12 onts that needed
  parallelism for speed now time out, vs +1..4 memout recoveries). Parallelism
  is genuinely valuable for throughput; it is only harmful (memory) on the
  existential-blow-up onts.
- Fix (`owl_classify.py` `_run_engine_adaptive`): run the **default parallel**
  attempt under an RSS watchdog (`KM_PAR_MEM_GB`, default 18 GiB, just under the
  20 GiB benchmark memcap) that kills *only the engine child*; on overflow,
  **retry single-threaded** (one engine, successor contexts shared, far lower
  memory). Keeps parallel speed for the speed-bound onts (no regression) and
  recovers the memory-bound onts via the fallback. RSS (not virtual address
  space) is monitored so legitimate large parallel runs are not falsely tripped.
  An explicit `KM_THREADS` bypasses the adaptive logic.
