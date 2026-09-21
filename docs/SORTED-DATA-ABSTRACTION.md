# Sorted data-node abstraction

Status: semantic core checked in Lean (`lean/ContextCalculus/SortedDataAbstraction.lean`,
standalone, no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`). Runtime
work in progress. Nothing here is promoted or benchmarked as a recovery yet.

## Why

The strict v8 panel declines 275 of the 1,920 inputs for one reason: data-property
assertions have no exact treatment. The per-shape projections (ground data, functional
data, finite `DataHasValue` membership) cannot express data cardinalities, which the
largest cluster (95 inputs) needs. The legacy `__dt__` abstraction already routes data
existentials, universals and cardinalities through ordinary object reasoning, and
`DataPropertyAssertion(p a v)` is exactly `ClassAssertion(DataHasValue(p v) a)`.
A source rewrite of that equivalence alone, run on the unmodified v12 binary, matches
HermiT exactly on 188 of the first 251 declines (experiment `fable-dataabs-v0`).

Two gaps keep the abstraction from being exact.

1. **Sort confusion.** Data values become ordinary nodes, so an axiom that speaks about
   every object (`owl:Thing ⊑ {a}`, `¬A ⊑ B`, `∀r.C ⊑ D`, reflexivity) also constrains
   data nodes. `bounded.owl` is the known counterexample, and it affects the accepted
   TBox-only path as well.
2. **Oracle gaps.** The datatype oracle emits nothing when a relation is unknown, which
   is sound but incomplete. ore_ont_6951 loses two unsatisfiable classes because
   `"100"^^xsd:int` is not declared disjoint from `xsd:float`.

## The scheme

Keep the source expression shape (`plain`). Compute `sortShape e = (anchored, vacuous)`:
`anchored` means the expression is false at every data node (named class, nominal,
existential, at-least n ≥ 1, self, a conjunction with an anchored conjunct, a disjunction
of anchored disjuncts); `vacuous` means it is true at every data node (`⊤`, universal,
at-most, at-least 0, and the dual combinations; negation swaps the two).

An axiom `C ⊑ D` is emitted unchanged when `C` is anchored or `D` is vacuous. Otherwise
it is emitted as `Obj ⊓ C ⊑ D` with a private class `Obj`. When at least one axiom needs
the guard, the frontend also emits `Obj ⊑ ∀r.Obj` for every object role, `A ⊑ Obj` for
every named class, and `Obj(a)` for every individual. When no axiom needs the guard,
nothing is added and the output is unchanged.

Lean statements:

- `sortShape_sound`: the shape analysis is correct at every canonical data node.
- `canonical_plain_exact`, `canonical_axiom`: every two-sorted model of the source yields
  a one-sorted model of the emitted axioms (soundness of "satisfiable" answers and of
  non-entailments).
- `typed_plain_exact`, `abstract_axiom`: every adequately labelled one-sorted model in
  which object-role successors of objects are objects yields a two-sorted model of the
  source (soundness of "unsatisfiable" answers and of entailments).
- `abstract_exact`, `canonical_exact`: the same two directions for the fully relativised
  translation, kept as the reference statement.

## Validation boundaries (not proved in Lean)

- `Adequate`: every data node of the one-sorted model can be labelled with a value that
  lies in exactly the asserted data ranges, with distinct labels for distinct data
  successors of one object. The datatype oracle must make every permitted data-node type
  realisable (by infinitely many values, or by one enumerated value with a singleton
  clause). This needs a fail-closed region check in `frontend/datatypes.rs`.
- Literal decoding, fresh-name allocation for `Obj`, role classification (object vs
  data), reflexive and universal roles (declined together with data for now), routing,
  and output filtering of the private class.

## Frontend passes

`KM_SORTED_DATA=1` runs the established frontend first, with the object-sort guard added.
Every exact ABox certificate (separable, atomic, ground, finite membership) keeps priority,
which matters for speed: a first wiring that always desugared data assertions turned 29
previously fast inputs into timeouts, because it switched the ABox-omission certificates off.
Only when that pass declines for data-assertion coverage, or finds that a guard is needed, is
the source read again with data assertions as `DataHasValue` class assertions and the full ABox
retained.

Known gap: a reflexive or universal role defeats the shape analysis. The first pass then keeps
the established behaviour (no guard), and the second pass declines. The exact treatment is
`Obj ⊑ ∃r.Self` in place of the reflexivity axiom, which also has to reach the typed RBox.

## Oracle changes made for adequacy

- Float and double literals decode to exact IEEE values; float, double and the decimal tower are
  separate partitions (OWL 2 Structural Specification 4.2: pairwise disjoint value spaces).
- Distinctness of more than 64 values uses a binary index encoding, O(n log n) clauses.
- Still open: a fail-closed check that every data-node type the clauses permit is realisable
  (laminar ranges, finite regions enumerated), duplicate facets with mixed inclusivity in
  `DatatypeRestriction`, facet restrictions over float and double, string subtypes, dateTime order.
