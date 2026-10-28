# Data-property assertions above the literal cap

Status: implemented in `frontend/literal_profiles.rs` and
`Ontology::commit_data_assertions_as_class` (v1.5.4). Frontend only; no
calculus change.

## Problem

A positive `DataPropertyAssertion(u a v)` holds iff `a` is an instance of
`DataHasValue(u v)` (OWL 2 Direct Semantics). The frontend carries it as the
class assertion `a : ∃u.{v}`, with `{v}` the value concept `__dt__val__v`
(see [DATATYPES.md](DATATYPES.md)). The datatype relation clauses are
pairwise over the value vocabulary, so the conversion is capped at 512
distinct literals (`KM_DATA_ASSERTION_LITERAL_CAP`). Above the cap the
assertions used to stay uncarried; v1.5.4 publishes them as dropped axioms.
Eight ORE inputs that v1.5.3 solved have several thousand assertions over
more than 512 literals.

## Profiles

Let `O` be the ontology and `N` the set of `__dt__` concepts its axioms
mention, other than the asserted values: every data range (named, facet,
enumeration, boolean combination, each under its own name) and every value
token (`DataHasValue`, `DataOneOf` members appear inside their range names).
The *profile* of a data value `w` is the vector

    π(w) = ( w ∈ D : D a range in N ) ++ ( w = t : t a token in N ).

`datatypes::literal_value_profile` computes it with the same exact deciders
(`val_in_range`, `val_eq`) that produce the relation clauses. A literal whose
profile has an undecided entry, or that is opaque or ill-typed, has no
profile and keeps its own identity; so does a literal equal to a mentioned
token.

For every asserted literal `v` with a profile, its *representative* `ρ(v)`
is the first asserted literal with the same profile; otherwise `ρ(v) = v`.
`O'` is `O` with every `DataPropertyAssertion(u a v)` replaced by
`DataPropertyAssertion(u a ρ(v))`, carried as `a : ∃u.{ρ(v)}`. The value
vocabulary of `O'` has at most one literal per profile plus the literals
without a profile; if that is still above the cap the conversion declines as
before.

## Gate

The abstraction is applied only when none of these occurs (checked on the
parsed axioms, and on the source text for constructs the parser drops):

- a construct that counts the values of a property that is not certainly an
  object property: `≥n` with `n ≥ 2`, `≤n` with `n ≥ 1` (also from exact
  cardinalities), `FunctionalDataProperty`;
- `DisjointDataProperties` (or a disjointness involving such a property);
- `HasKey`;
- a rule (`DLSafeRule`).

A property is *certainly an object property* when it occurs in an object
assertion, a role chain, a transitivity, symmetry, asymmetry, reflexivity,
irreflexivity, inverse or inverse-functionality axiom, as an inverse, or
with a filler that is neither a data range nor `⊤`/`⊥`. Every other property
is treated as possibly a data property, which only makes the gate stricter.
The gate depends on the presence of constructs, never on the input size.

## Exactness

Claim: under the gate, `O` and `O'` have the same models up to the data
edges of the asserted individuals. In particular they agree on consistency,
on every subsumption and on every unsatisfiable class over the source
signature.

For an interpretation `I`, an element `x` and a data property `p`, let
`Π_p(x) = { π(w) : (x, w) ∈ p^I }` be the set of profiles of the
`p`-successors of `x`.

**Lemma.** Under the gate, the extension of every class expression of `O`
(and of `O'`, which has the same class expressions) is determined by the
interpretation of classes, object properties and individuals together with
the sets `Π_p(x)`.

By induction on the class expression. Object constructs do not look at data
values. The remaining data constructs are `∃p.D`, `∀p.D`, `≥1 p.D`,
`≤0 p.D` and `p value t` (and `DataPropertyDomain`/`DataPropertyRange`,
which are `∃p.⊤ ⊑ C` and `⊤ ⊑ ∀p.D`), with `D` a range in `N` and `t` a
token in `N`. At `x` each one holds iff some, every, some, no
`p`-successor has the bit of `D` (resp. of `t`) set, so it is decided by
`Π_p(x)`. The gate removes every construct that counts successors with
`n ≥ 2` or bounds them by `n ≥ 1`, that relates the successor sets of two
properties at the same value (disjointness), that compares values across
individuals (keys), or that inspects values in rules.

**From `O'` to `O`.** Let `I'` be a model of `O'`. Define `I` from `I'` by
adding, for every assertion `u(a, v)` of `O` and every `p` with `u ⊑* p`
(the reflexive-transitive closure of the property inclusions), the edge
`(a^I', v)` to `p`. `O'` asserts `u(a, ρ(v))`, so `(a^I', ρ(v)) ∈ p^I'`
already, and `π(v) = π(ρ(v))`. Each added edge therefore adds a successor
whose profile is already in `Π_p(a^I')`: every `Π_p(x)` is unchanged, and by
the lemma so is every class extension. `I` satisfies every class axiom and
class assertion of `O` because `I'` does; property inclusions hold because
the edges were added along their closure; every data assertion of `O` holds
by construction; nothing else changed.

**From `O` to `O'`.** Symmetric: add `(a^I, ρ(v))` along the closure of
`u` for every assertion `u(a, v)`. `(a^I, v)` is already an edge and has the
same profile.

Both constructions keep the interpretation of every class, object property
and individual, so the two ontologies have the same consistency, the same
subsumptions and the same unsatisfiable classes.

**Why the gate is needed.** With counting, the representative of two values
on one subject may be the same literal. With `≤1 u`, `u(a, 1)` and `u(a, 2)`
are inconsistent while `u(a, 1)` twice is not. Ranking values per subject
does not repair this once individuals can be identified (`SameIndividual`,
functional or inverse-functional object properties, object `≤n`, nominals):

    FunctionalDataProperty(u)  FunctionalObjectProperty(r)
    r(x, a)  r(x, b)  u(a, 1)  u(b, 2)

is inconsistent (`a = b`), but per subject both values are the first of
their profile and would share a representative. Disjoint data properties
see the identity of a value across two properties, and keys see it across
individuals. These inputs keep the plain conversion when it fits the cap,
and otherwise publish the uncarried assertions as dropped.

Negative data-property assertions are never converted; they stay uncarried
and are published as dropped axioms, independently of the abstraction.
