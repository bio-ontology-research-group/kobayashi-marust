# Datatype (concrete-domain) reasoning

Status: IMPLEMENTED (2026-06-12), frontend-only. Recovers the last
incomplete-vs-gold ORE ontology (ore_ont_6999, byte-equal to gold) and adds
genuine OWL 2 datatype semantics to the `__dt__` abstraction. No calculus
change: every emitted clause is an ordinary concept clause, so no Lean
re-certification is required; soundness reduces to the correctness of the
per-pair datatype-map decisions below.

## The abstraction

The frontend maps data expressions to concepts over abstracted data nodes:

- `DataSomeValuesFrom(p D)` → `∃p.__dt__D` (named D) or `∃p.__dt__c__<text>`
  (complex D, keyed by its canonical s-expression text),
- `DataHasValue(p v)` → `∃p.__dt__val__<v>` with `v` the *glued* literal
  (lexical form + `^^datatype` / `@lang` — the tokeniser splits these into
  two atoms, which previously collapsed same-lexical different-type values),
- data cardinalities → the standard `AtLeast`/`AtMost` encodings, with `⊤`
  as the unqualified filler (the old `__dt__val` filler made `≤ n` blind to
  `DataHasValue` successors).

Data property axioms map to their role counterparts (functionality,
inclusion, equivalence, disjointness, domain, range as `∀p.__dt__D`,
`DatatypeDefinition` as concept equivalence). A data node stands for its
value, which justifies the singleton clauses below.

## The oracle (`frontend/datatypes.rs`)

Over the `__dt__` concepts occurring in the clause set, the oracle decides
relations per the OWL 2 datatype map and emits clauses; every decision
procedure returns `Option<bool>` and `None` (unknown) emits nothing, so
unsupported corners degrade to the old sound abstraction, never to a wrong
clause.

| relation | clause |
|---|---|
| `v ∈ D` | `__dt__val__v(x) → __dt__D(x)` |
| `v ∉ D` | `__dt__val__v(x) ∧ __dt__D(x) → ⊥` |
| `v = w` | inclusions both ways |
| `v ≠ w` | `__dt__val__v(x) ∧ __dt__val__w(x) → ⊥` |
| `D₁ ⊑ D₂` | `__dt__D₁(x) → __dt__D₂(x)` |
| `D₁ ∩ D₂ = ∅` | `__dt__D₁(x) ∧ __dt__D₂(x) → ⊥` |
| `D = {v₁…v_k}`, k ≤ 8 | cover `__dt__D(x) → ⋁ __dt__val__vᵢ(x)` |
| every value `v` | singleton `__dt__val__v(z₁) ∧ __dt__val__v(z₂) → z₁ ≈ z₂` |

Value spaces: exact `i128` rationals for the decimal/integer tower and for
finite float/double values (dyadic conversion; the float specials are
tracked as tagged markers), strings with language tags, booleans. The named
type table covers the integer tower with its bounds (`int`, `long`, …,
`unsignedByte`), the string-family tower, boolean, anyURI, binary, and the
dateTime family as opaque partitions. Facet restrictions over numeric bases
become intervals (min/max, in/exclusive); `DataOneOf` becomes an
enumeration. Partition disjointness, interval separation, bound inclusion,
and enumeration membership drive the decisions.

Finite covers (boolean, `DataOneOf`, small integer intervals) plus the value
disjointness and singleton clauses give finite-range *counting* through the
engine's ordinary equality reasoning: `≥3 p.xsd:boolean ⊑ ⊥` derives from
the three pairwise-distinct witnesses each being `true` or `false`, two of
them merging by the singleton clause, and the `≉` witness clashing.

Probes (all unsat through the pipeline, oracle/ontologies/):
`data_functional_unsat` (`=2 p` + functional), `data_value_clash` (two
`DataHasValue` on a functional property), `data_boolean_count`
(`≥3 p.boolean`).

`KM_NO_DATATYPES` disables the oracle pass (the axiom translation is
unconditional).

## Open corners (sound, possibly incomplete)

- pattern / length facets (ranges containing them stay fully opaque),
- dateTime/duration ordering and arithmetic,
- float/double vs decimal cross-tower subsumption (values are compared
  exactly, but the named types are not ordered against each other),
- `DataComplementOf` / `DataIntersectionOf` / `DataUnionOf` structure,
- n-ary `DataSomeValuesFrom` (multi-property comparisons),
- `DataPropertyAssertion` under `KM_NOMINALS` (ABox datatype clashes are
  covered by the separate `data_abox` precheck),
- `HasKey`.
