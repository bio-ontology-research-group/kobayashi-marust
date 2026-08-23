# CB certification boundary

This document records the proof boundary for KM's production consequence-based
(CB) engine. It is a checklist for the complete CB certification layer, not a
claim that the layer is already complete.

## Established in Lean

- `Basic` proves soundness of resolution and the abstract context-calculus rule
  reductions. `CheckerTerm` proves that an accepted nested-term derivation
  establishes a positive subsumption or unsatisfiability verdict.
- `CompletenessProp`, `CompletenessClause`, and `CompletenessOrdered` prove
  refutational completeness of finite ground resolution, including ordered
  resolution.
- `CompletenessContext` and `CompletenessStrategy` prove that the abstract
  finite good-type elimination fixpoint decides the supported type-level
  semantics.
- `CompletenessEq` builds the finite congruence-quotient model for the grounded
  merging features. `Termination` supplies the abstract finite blocking bound.
- `Equivalence.saturation_models_iff` proves that a retained, sound production
  saturation preserves the complete model class. This is stronger than merely
  agreeing on the empty clause and is the semantic bridge needed by an exact
  taxonomy publication theorem.
- `CBSaturationCertificate` provides an executable finite ground checker. It
  validates an acyclic resolution trace, exact input retention, and terminal
  closure, then constructs `Equiv.Saturation`. Accepted certificates therefore
  preserve every model and consequence of the checked input. Its executable
  examples reject both a missing resolvent and a forged derivation.
- `CBTermDerivationWire` makes the nested-term source derivation theorem an
  executable, bounds-checked JSON boundary. An accepted positive subsumption or
  unsatisfiability verdict follows from the complete normalized clause list in
  that document through checked instantiation, resolution, or paramodulation.
  This establishes per-verdict soundness, but not completeness of omitted
  taxonomy cells.
- The term semantics now distinguish universally assigned variables from named
  individual constants. Constants have a fixed model interpretation and cannot
  be changed by substitutions. The certificate generator emits this corrected
  representation instead of encoding individuals as negative variable ids.
- `CBFiniteModel` proves that executable enumeration of every valuation over
  the variables occurring in a nested-term clause establishes universal clause
  validity. The model semantics cover nested unary functions, named constants,
  concepts, roles, equality, and inequality.
- `CBFiniteModelWire` checks complete finite truth and function tables against
  the exact source bounds. An accepted countermodel proves that a claimed
  subsumption does not follow from the complete decoded ontology.
- `CBTaxonomyWire` combines positive derivations and negative countermodels in
  one clause-bound, row-major named-concept matrix. It checks every coordinate,
  every publication bit, complete matrix shape, a duplicate-free public concept
  name table, and the exact non-reflexive public subsumption payload. The public theorem in
  `CBCertificationSurface` proves that every accepted bit is true exactly when
  its decoded source ontology entails that subsumption.
- `cb-taxonomy-cert-check` is the executable JSON checker for this exact
  publication boundary. Its fixtures accept a valid document and reject a
  forged publication bit.
- `CBALCEncoding` defines the exact indexed Skolem encoding from normalized ALC
  clauses into the nested-term clauses consumed by the CB checker. It proves
  both model directions: every term model restricts to an ALC model, and every
  nonempty ALC model extends to a term model by choosing witnesses for the
  indexed existential functions. Consequently, atomic subsumption in the
  encoded CB semantics is equivalent to ALC good-type semantics. Every failed
  ALC subsumption has a concrete countermodel over the finite domain of good
  types. These theorems certify the semantic encoding, not yet the production
  context saturation that computes a result.
- `CBEqEncoding` extends the exact two-way model bridge to the equational
  ontology language used by `CompletenessEq`: role inclusions, inverse-role
  bridges, functionality, nominals, and arbitrary qualified at-most
  restrictions, in addition to the disjunctive ALC constructors. Its encoding
  uses fixed individual constants, source-indexed existential functions, real
  equality, and the complete pairwise equality head for each at-most clause.
  It proves both atomic-subsumption equivalence and satisfiability equivalence
  under the standard nonempty-domain convention. The production-state
  refinement remains a separate obligation.
- `CBRoleChainEncoding` adds arbitrary finite role-chain inclusions to that
  source language. The generated nested-term clause has one universally
  quantified path position per endpoint, one body role atom per chain member,
  and the super-role edge as its head. `valid_encodeChain_iff` proves exact
  equivalence with the path semantics. The combined source has two-way model,
  atomic-subsumption, and nonempty-domain satisfiability equivalence.
  `satChain_transitiveChain_iff` separately proves that `R ∘ R ⊑ R` is exactly
  ordinary role transitivity.
- `CBSourceWire` bounds-checks a typed normalized source containing all of the
  constructors above and requires its decoded nested-term clauses to equal the
  verified source encoding exactly. `CBSourceTaxonomyWire` then requires that
  source document and the complete taxonomy document have identical symbol
  bounds and clause lists. Its theorem proves every accepted matrix bit is
  exactly the corresponding typed-source semantic answer. Countermodel and
  taxonomy decoders retain proofs that all query coordinates are within the
  source concept table. The public capstone
  `certifiedCBSourceExactTaxonomyPublication` exposes this complete semantic
  chain. It does not yet prove that an unchecked Rust saturation produced the
  evidence.
- `CBProductionTrace` generalizes the derivation checker from one query concept
  to a production context with an arbitrary duplicate-free predicate core. It
  checks ontology instantiation, local assumptions, tautologies, resolution,
  and paramodulation, and proves every retained trace clause under the complete
  context core. `CBProductionTraceWire` binds all contexts to the verified typed
  source, requires unique context ids, exact retained trace terminals, and
  bounds-checked symbols. Every discarded clause must name a retained clause
  that syntactically strengthens it; Lean proves the deletion preserves local
  truth. The source-level theorem evaluates traces in the exact Skolem extension
  of a typed source model. The Rust engine does not yet emit this document, and
  the current trace language still needs checked decompositions or direct rules
  for every production inference family.
- `CBProductionTrace` also has direct executable rules for the two local
  transformations not represented by ordinary resolution or paramodulation:
  equality Factor and removal of a reflexive inequality. Both transformations
  have semantic soundness theorems and rejecting examples. The live rule audit
  and remaining production bindings are tracked in
  `docs/CB-RULE-CERTIFICATION.tsv`.
- `CBInterContext.predTransfer_sound` proves the semantic sender half shared by
  ordinary Pred and nominal r-Pred. A clause valid under its context core
  becomes an ordinarily valid payload after the edge substitution when the
  substituted core is appended to the payload body, exactly as production
  `pred_payload` does before sort/dedup normalization. The same module proves
  the exact `p → p` hypothesis installed by Succ and r-Succ universally valid.
  `CBInterContextWire` makes the sender theorem executable: every transfer is
  indexed into an accepted production context and retained clause, records its
  exact destination context, checks both context ids and the duplicate-free
  substitution, and requires its payload to be clause-equivalent to the
  substituted clause plus substituted core. Its tests reject forged sender ids
  and payloads. The same executable document binds each accepted arrival to the
  transfer's recorded destination and a sequence of retained providers. It
  checks every provider index, positive-head and current-body occurrence,
  reconstructs the complete resolution fold, and proves the exact result valid
  under the receiver core. The public checker theorem retains the checked
  transfer-to-arrival destination equality. Forged providers and results are
  rejected. Production edge eligibility and complete queue delivery remain
  refinement obligations.
  `coveredResults_contextValid` closes the semantic antichain step: if the
  executable enumeration layer shows that every raw Cartesian conclusion has
  a retained strengthening, validity of the retained antichain implies
  validity of every pruned conclusion. What remains is to compute and check
  that exhaustive finite coverage from the production snapshot.
- `CBPredEnumeration` supplies the exact finite foundation for that check. It
  computes each provider posting directly from every retained receiver clause
  whose head contains the required literal, enumerates the Cartesian product,
  and proves membership equivalent to choosing exactly one member of every
  complete dimension. The next wire layer must account for ground remainder
  literals and bind every generated selection to either an emitted arrival or
  a retained strengthening.
  `providerPlan_exact` now handles the ground exception used by production:
  every accepted payload-body plan classifies each literal as either a complete
  nonempty provider dimension or a provider-free, syntactically ground
  remainder. A missing provider for a non-ground literal rejects the arrival.
  `CBPredCoverageWire` joins those pieces executably. For each checked
  transfer/receiver pair it recomputes the complete Cartesian signature list,
  requires exactly one generated record per signature, reconstructs each raw
  resolution result, and checks an accepted arrival from the same transfer and
  recorded destination syntactically strengthens it. The whole document must
  contain exactly one ordered coverage record for every accepted transfer, so
  no transfer may be omitted or duplicated. Lean proves every covered raw
  result receiver-core valid and exports both exact whole-transfer coverage and
  target equality. Kernel-evaluated tests reject an omitted selection, a forged
  provider, an out-of-range strengthening arrival, and duplicated transfer
  coverage. Edge eligibility, exact enumeration of all production transfers,
  and complete queue delivery remain open.
- `CBPredSendEnumeration` independently specifies the finite ordinary-Pred
  sender scan over a typed terminal context snapshot. It recomputes
  function-free Pred-compatible head eligibility and complete edge-body
  coverage for every retained-clause/edge pair. `mem_enumerate_iff` proves that
  its clause-major, edge-minor output contains exactly the eligible pairs. The
  next wire layer must bind the snapshot to KM's final retained clauses and
  predecessor edges, require the transfer list to equal this enumeration, and
  add the separate nominal r-Pred eligibility cases.
- `CBPredSendCoverageWire` applies the ordinary and root enumerators to every
  sender in one inter-context document. It bounds-checks every edge destination
  and label, decodes duplicate-free pushed sets, derives the ordinary or root
  backward substitution, and compares each sender's ordered transfer
  signatures with the recomputed eligible signatures. The snapshots cover all
  non-ground contexts plus exactly the designated ground context, and their
  two transfer partitions cover all ordinary and root transfers. Tests accept
  both sender modes and reject an omitted transfer, a forged pushed set, a
  missing root snapshot, and a non-individual root label. The same document now
  requires its ground-context designation to equal exactly the production
  context carrying the dedicated nominal-ground marker, rejecting both a
  missing marker and multiple markers. The ordinary `root` flag is deliberately
  separate because KM also marks query and top contexts as calculus roots. It
  binds every runtime individual-table extension to a checked Nom allocation
  over the identical source bounds and ontology. A standalone
  `cb-pred-send-coverage-check` executable exposes this boundary. Binding the
  predecessor snapshots to serialized terminal Rust state remains open.
- `CBTerminalStateWire` rejects termination-as-evidence and instead checks the
  concrete fixpoint bookkeeping used by KM. The global message queue must be
  empty, neither the message cap nor Nom budget may have truncated the run, and
  every production context must occur exactly once with an empty local todo
  queue and a cleared dirty flag. Pred, Succ, and r-Succ pool high-water marks,
  the r-Succ reach driver and every successor-pair watermark must be complete.
  Every predecessor-edge watermark must equal the pushed-set length from the
  exact send snapshot. Kernel tests reject pending messages, truncation,
  incomplete pool scans, and stale edge scans. The standalone
  `cb-terminal-state-check` checker exposes this boundary. Production emission
  and the semantic theorem connecting these finite bookkeeping conditions to
  rule closure remain open.
- `CBLocalResolutionClosureWire` independently enumerates every ordinary local
  resolution candidate in every terminal production context: all ordered
  retained-clause pairs and every literal occurring in the first clause's head
  and the second clause's body. Every candidate must have a retained syntactic
  strengthening, and the supplied ordered signatures must equal the computed
  list exactly. Its non-vacuous fixture checks interacting retained clauses and
  rejects omission of the generated candidates. The standalone
  `cb-local-resolution-closure-check` exposes this boundary. This proves closure
  modulo redundancy for ordinary local resolution only; it does not establish
  Hyper, equality, Factor, Join-3, Succ, blocking, or whole-engine closure.
- `CBLocalFactorClosureWire` nests that resolution certificate and independently
  enumerates every ordered pair of distinct terminal head equalities that share
  a left side and have different right sides. It mirrors production removal of
  reflexive inequalities and rejection of reflexive-equality or
  equality/inequality-complement tautologies, then requires a retained
  strengthening for every remaining Factor result. Lean proves normalization
  preserves truth and proves every enumerated candidate from the checked source
  clause. Terminal retained heads must already be normalized. The standalone
  `cb-local-factor-closure-check` exposes this boundary. The Rust-only
  `owl:Nothing` predicate filter still needs an exact source-symbol binding;
  this checker does not silently identify an arbitrary concept id as bottom.
  General Eq paramodulation and whole-engine closure remain open.
- `CBFiniteTermOrderWire` supplies the finite order foundation needed to check
  Eq orientation and maximality without trusting runtime flags. It collects all
  direct terms from the exact verified source and every terminal retained
  context, then requires the supplied low-to-high list to be a duplicate-free
  permutation of exactly that finite universe. Lean proves every production
  term has a bounded rank and equal ranks identify equal production terms. The
  standalone `cb-finite-term-order-check` exposes this boundary. It is not yet
  an Eq closure theorem: literal maximality, all three production Eq candidate
  paths, and the ordered-paramodulation completeness connection remain open.
- `CBFiniteLiteralOrderWire` extends that boundary to every literal in the
  verified source and terminal retained contexts. The supplied low-to-high
  literal list must be an exact duplicate-free permutation. Lean derives every
  maximal head index from rank comparison and proves its executable membership
  condition equivalent to a bounded index whose literal dominates every other
  head literal. The standalone `cb-finite-literal-order-check` exposes this
  boundary. This removes runtime maximality masks from the trusted base, but it
  does not yet prove Eq or Hyper candidate closure or that the selected order
  satisfies the final ordered-calculus admissibility theorem.
- `CBLocalEqEnumeration` defines KM's direct-position rewrite separately from
  the older recursive term-checker rewrite and proves that the exact operation
  preserves literal truth under its equality premise. It also specifies the
  terminal union of the `eq_from_pred` and `eq_from_equation` scans from checked
  maximal head indexes, including the production equality and inequality
  suppression cases, and proves exact list membership. Retained-strengthening
  coverage, candidate-level semantic composition, Rust-state emission, and the
  ordered-paramodulation completeness connection remain open.
- `CBLocalEqClosureWire` turns that specification into an executable nested
  terminal-state certificate. For every context, Lean reconstructs each
  provider and target from bounded retained-clause indexes, recomputes both
  maximality tests, performs the direct rewrite and head normalization, and
  requires the serialized list to equal the complete candidate enumeration.
  Every surviving candidate has a retained strengthening witness. The semantic
  capstone proves every reconstructed normalized conclusion from validity of
  its two retained premises. The standalone `cb-local-eq-closure-check` exposes
  this boundary. Rust emission and the ordered-calculus completeness theorem
  remain open.
- `CBFiniteOrderAdmissibilityWire` strengthens the order boundary required by
  the eventual ordered-paramodulation theorem. The finite production universe
  now contains every nested proper subterm, not only top-level literal
  arguments. The checker requires every proper subterm to rank below its
  containing term and requires strict order to be preserved by every unary
  function context represented in the finite production universe. Lean proves
  those properties, strict trichotomy on production terms, and well-foundedness
  of the rank-induced order. The standalone
  `cb-finite-order-admissibility-check` exposes this boundary. The final
  ordered-paramodulation model theorem still remains open.
- `CBRootPredSendEnumeration` specifies the x-free nominal r-Pred sender scan.
  It allows different individual-labelled edges of one receiving source to
  discharge different body predicates, checks that every non-fresh individual
  mentioned by the clause was announced by that source, and selects exactly
  the first minimum-labelled representative edge for each source. Its exact
  membership theorem rules out omitted and invented retained-clause/source
  pairs. It also specifies the x-containing per-edge branch, requiring one
  edge to cover the complete body and its receiving source to have announced
  every individual in the clause. `enumerateAll` composes the mutually
  exclusive branches in KM's clause-major order and has an exact membership
  theorem. `CBPredSendCoverageWire` now composes this enumeration with the
  executable transfer list; terminal Rust-state emission remains open.
- Production traces now distinguish the normalized source individual bound
  from the runtime individual bound. The runtime table must extend the source
  table, while concept, role, and function bounds remain identical. Context
  clauses, substitutions, payloads, and arrivals decode against the runtime
  bound, so Nom-generated fresh constants can be represented instead of being
  rejected before their allocation proof is checked. Tests accept a fresh
  runtime constant under an extended table and reject the same trace when the
  runtime table is truncated. The send-coverage document requires an allocation
  exactly when the runtime table extends the source table, and checks identical
  source bounds, identical encoded ontology, and equal runtime count.
- The production trace also checks the exact three-premise Join-3 rule used for
  nominal propagation. It requires empty provider and bridge bodies, the
  consumer ground literal, the provider general literal, the canonical bridge
  equality `term ≈ x`, and the exact syntactic `x ↦ term` instance before
  accepting the combined conclusion. Lean proves this transformation sound;
  executable examples accept the production shape and reject a forged ground
  instance. Rust emission and index binding remain outstanding.
- `Nominals.nom_family_sound` lifts the single-firing Nom covering theorem to
  any finite family when each firing receives a disjoint block of fresh
  constants. A separate finite theorem demonstrates that independently valid
  one-firing witnesses cannot in general share one constant block. The proof
  audit therefore changed KM's interner: each exact grounded Hyper firing now
  receives a stable disjoint block, while an exact replay reuses that block so
  saturation remains finite. Allocation is all-or-nothing and exhaustion marks
  the run incomplete. `nom_shared_cover_sound` also records the stronger
  invariant that would permit cross-firing reuse, but KM no longer relies on
  that unproved optimization. `CBNominalAllocationWire` now checks exact firing
  identities, positive widths, one consecutive allocation sequence, global
  freshness and disjointness, exact budget accounting, an exact final runtime
  individual count, and no truncation. Its executable checker rejects
  overlapping blocks, replayed keys, trailing unallocated runtime identifiers,
  and truncated runs. `check_family_sound` composes accepted allocation evidence with
  `nom_family_sound`: once the next decoder supplies one width-aligned semantic
  obligation per firing, all obligations receive simultaneous witnesses while
  their concrete blocks remain fresh and disjoint. `nomConclusion_sound` proves
  that such a witness satisfies the exact retained-head-plus-`y ≈ fresh`
  production clause. `nomConclusion_exists_extension` constructs the
  corresponding first-order model extension and proves that every source clause
  below the fresh boundary retains its truth. Each allocation block now carries
  its decoded body, residual head, and emitted clause; the executable checker
  requires that clause to be exactly the residual head plus every equality in
  the block and rejects a forged omitted equality. The remaining Nom evidence
  must derive each obligation from the firing's exact covering/counting premises
  and check that its decoded body and residual head have the required meanings.
  The firing now also carries a source-clause index. Decoding requires its
  recorded source body and head to equal that exact clause in the verified
  normalized ontology; an out-of-range index is rejected. Lean transports the
  indexed source clause's validity to the recorded premise without trusting the
  duplicate payload. `escape_of_valid_counting_premise` now proves the central
  semantic step that had previously only been described: validity of that
  counting premise, truth of every selected body match, and exhaustive
  classification of every possible true head literal imply exactly
  `groundEscape ∨ Escapes`, the premise consumed by `nom_sound`. The remaining
  executable refinement must reconstruct the tuple assignment from the checked
  substitution and providers and discharge the body-truth and exhaustive-head
  classification hypotheses from their concrete syntax.

## Not yet established

The production Rust worker does not currently emit or invoke the complete
production-run CB document. Generated files under `lean/Validation` certify
selected positive verdicts, but they do not certify every production run,
terminal closure, omitted taxonomy cells, or the supervisor's publication
behavior.

The remaining production gap is the representation refinement between:

1. the Rust engine's contexts, cores, clause stores, inter-context messages,
   literal ordering, redundancy deletion, blocking, and termination state; and
2. the abstract complete saturation or good-type fixpoint used by the Lean
   completeness theorems.

For source ontologies with suitable finite countermodels, exact result
certification can avoid that refinement: a complete taxonomy document can
prove every positive cell by derivation and every negative cell by a finite
countermodel. The refinement remains necessary for general SROIQ and whenever
a production terminal saturation justifies an omission without such a model.

For the normalized ALC slice, `CBALCEncoding` now closes the source-semantics
side of this gap. `CBEqEncoding` extends that source-to-term refinement through
role inclusions, inverse roles, nominals, equality, functionality, and
qualified at-most restrictions. `CBRoleChainEncoding` closes the remaining
arbitrary role-chain and transitivity source-semantics bridge. All features
still need refinement from the Rust context stores and terminal queues to the
complete abstract calculus, plus mandatory checked publication.

Finite countermodels are a sound evidence form, not a complete replacement for
the production refinement over full SROIQ. SROIQ does not in general have the
finite-model property. The complete CB layer must therefore justify every
remaining negative cell through a complete terminal-state theorem or another
certificate form capable of representing the required infinite models.

Benchmark agreement with another reasoner is regression evidence only.

## Requirements for the complete CB layer

The CB layer is complete only when one release gate establishes all of the
following over the exact production input and output:

1. **Exact decoding.** The checker reconstructs the complete symbol table,
   normalized clauses, query roots, contexts, clauses, ordering data, and
   published taxonomy. Duplicate or aliased public names are rejected.
2. **Retained-input identity.** The checked premise set is exactly the clause
   stream received by the CB worker. No omitted, added, or reordered data may
   change its set semantics unnoticed.
3. **Sound production steps.** Every retained context clause has a checked
   derivation from source clauses, core clauses, or earlier checked clauses.
   Hyper, Pred, Succ, Eq, Ineq, Factor, nominal rules, and inter-context
   transfers must match the production term and substitution conventions.
4. **Redundancy safety.** Every discarded clause is redundant under the exact
   production strengthening relation. Base-plus-delta storage, back
   subsumption, batching, and parallel scheduling must preserve the same
   logical saturation.
5. **Closure and fairness.** A successful terminal state is closed under every
   applicable production inference. Resource limits, overflow, worker errors,
   or unfinished queues must decline rather than publish.
6. **Representation refinement.** The checked context-clause terminal state
   represents exactly the abstract complete fixpoint, including successors,
   inverse roles, equality, nominals, and qualified cardinalities admitted by
   the production route.
7. **Exact publication.** Every published subsumption is sound and every omitted
   eligible subsumption has a checked countermodel or follows from the complete
   terminal-state theorem. Global inconsistency and unsatisfiable named classes
   are exact, and internal symbols cannot leak into the public result.
8. **Fail-closed execution.** Certified production mode requires the real Lean
   checker. A missing, malformed, timing-out, crashing, or rejecting checker
   produces no CB answer and no partial stdout.
9. **Axiom and integration audit.** The public capstone has no admitted theorem,
   its axiom surface is recorded, tampering tests reject each wire component,
   and Rust-to-Lean tests exercise accepting and rejecting production paths.

Only after these items pass together should the CB layer receive a certification
release. Automatic profile selection, races, fallbacks, and frontend-to-worker
composition belong to the later routing certification layer.
