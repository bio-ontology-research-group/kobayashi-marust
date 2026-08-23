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
  one source-bound, row-major named-concept matrix. It checks every coordinate,
  every publication bit, complete matrix shape, a duplicate-free public concept
  name table, and the exact non-reflexive public subsumption payload. The public theorem in
  `CBCertificationSurface` proves that every accepted bit is true exactly when
  its decoded source ontology entails that subsumption.
- `cb-taxonomy-cert-check` is the executable JSON checker for this exact
  publication boundary. Its fixtures accept a valid document and reject a
  forged publication bit.

## Not yet established

The production Rust worker does not currently invoke a mandatory Lean CB
checker. Generated files under `lean/Validation` certify selected positive
verdicts, but they do not certify every production run, omitted taxonomy cells,
or the supervisor's publication behavior.

The remaining production gap is the representation refinement between:

1. the Rust engine's contexts, cores, clause stores, inter-context messages,
   literal ordering, redundancy deletion, blocking, and termination state; and
2. the abstract complete saturation or good-type fixpoint used by the Lean
   completeness theorems.

Exact result certification no longer depends on that refinement: a complete
taxonomy document can prove every positive cell by derivation and every
negative cell by a finite countermodel. The refinement remains necessary if a
production terminal saturation is to justify omissions without emitting
countermodels.

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
