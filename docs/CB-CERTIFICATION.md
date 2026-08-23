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
