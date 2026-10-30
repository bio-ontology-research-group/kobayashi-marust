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

## Asserted data values

Positive data-property assertions are carried as `DataHasValue` class
assertions. Above 512 distinct literals they are carried through the
profiles the TBox observes when no construct counts or compares values
([DATA-ASSERTION-PROFILES.md](DATA-ASSERTION-PROFILES.md)), and otherwise
with their own identities under the linear relation form of the next
section; since v1.5.5 no positive assertion is left uncarried.

## Exact data values without a literal cap (2026-10-30, v1.5.5)

### Gap

Positive data-property assertions are carried as class assertions
`a : ∃u.{v}` (above). The relation generator stated every relation between
two value concepts as its own clause, so a vocabulary of `n` literals cost
`n²/2` clauses (ore_ont_10425 with 5,289 literals reached 17 GB in the
frontend before it was stopped), and the conversion was capped at 512
literals. Above the cap the profile abstraction
([DATA-ASSERTION-PROFILES.md](DATA-ASSERTION-PROFILES.md)) applied only when
no construct counts values; every other input published its data
assertions as `DROPPED`. The ORE inputs of amendment 2 of the v1.5.4
release (10425, 15655, 4572, 5368, 4410, 10874, 7610) all count values with
`≤ 1` (functional data properties, `DataMaxCardinality(1 …)`,
`DataExactCardinality(1 …)`) next to functional or inverse-functional
object properties, so neither the cap nor the profile gate admitted them.

### Encoding

Let `V` be the value concepts of the vocabulary (asserted literals, TBox
tokens and the members of finite covers) and `R` its ranges. The datatype
oracle decides, for two values that are not opaque, `val_eq(v, w)`, and this
decision is equality of an identity key (`value_key`: the parsed value with
its variant; numeric values are normalised rationals, IEEE values their bit
patterns, strings their text and language tag). Above
`PAIRWISE_VALUE_LIMIT` (1,024) value concepts the generator
(`linear_value_relation_clauses`) emits, in place of the value-value and
value-range pairs:

1. *Identity classes.* The values with one key are made equivalent through
   the first of them (`v ↔ v₀`, a star, instead of every pair).
2. *Index bits.* The identity classes are numbered `0 … m-1`; with
   `k = ⌈log₂ m⌉`, class `i` implies `__dt__aux__bit__p__b` for every
   position `p < k`, where `b` is bit `p` of `i`, and each position carries
   `bit__p__0 ⊓ bit__p__1 ⊑ ⊥`. Two distinct classes differ at some
   position, so their values clash on one node: `O(m log m)` clauses for
   the `O(m²)` pairwise clashes.
3. *Membership profiles.* The values with one membership vector over `R`
   (`val_in_range` for every range, `None` entries included) imply one
   helper `__dt__aux__profile__i`, which carries `profile ⊑ R` for the
   members of `R` and `profile ⊓ R ⊑ ⊥` for the non-members: `O(|V| + P·|R|)`
   clauses for `O(|V|·|R|)`, with `P` the number of distinct vectors.

Range-range relations, finite covers, union covers, complement excluded
middles and integral cells are emitted as before. At or below the limit
the pairwise form is emitted unchanged, so every input that converted its
assertions in v1.5.4 keeps a byte-identical clause stream unless the
singleton rule below applies.

The cap no longer declines. Above 512 asserted literals the profile
abstraction is still tried first, because it shrinks the vocabulary where
it applies; where its gate blocks, every literal keeps its identity under
the linear form. `KM_DATA_ASSERTION_LITERAL_CAP` therefore selects between
two exact encodings and cannot change an answer.

**Exactness of the linear form.** Let `S` be the clause set with the
pairwise form and `S'` the one with the linear form; the helpers are fresh.
(a) `S'` entails every pairwise clause of `S`: `v → v₀ → v` gives the
equalities; for keys `k ≠ l` the indices differ at some position `p`
(`binaryIndex_separating` below), so `v → bit__p__b`, `w → bit__p__(1-b)`
and the position's clash give `v ⊓ w ⊑ ⊥`; and `v → profile → R` (resp.
`profile ⊓ R ⊑ ⊥`) gives each membership clause. (b) Every model `I` of
`S` expands to a model of `S'` by interpreting each helper as the union of
the values that imply it: `bit__p__b := ⋃ {v^I : bit p of index(key v) = b}`
and `profile_π := ⋃ {v^I : vector(v) = π}`. Every `v → helper` clause holds
by construction; `bit__p__0 ⊓ bit__p__1` is empty because its two sides are
unions of values with different keys, which `S` makes disjoint; and
`profile_π ⊑ R` holds because every member satisfies `v ⊑ R` in `S`. So `S'`
is a conservative extension of `S` over the source vocabulary: the two have
the same consistency, subsumptions and unsatisfiable classes. Both
directions are proved in Lean (`lean/ContextCalculus/LinearValueEncoding.lean`:
`bits_entail_pairwise`, `pairwise_admits_bits`, `profiles_entail_membership`,
`membership_admits_profiles`, `binaryIndex_separating`).

### Value singletons

Every value concept had the singleton clause `v(y₁) ∧ v(y₂) → y₁ ≈ y₂` (a
data node is its value). On the native bridge these clauses act as
nominals: a literal shared by many subjects merges all their data
successors (ore_ont_10425: thousands of merges, then the bridge budget),
and every subject test pays for them (ore_ont_5368: 126 s of 139 s in the
per-subject phase). The frontend now leaves the singleton clause out for
every value whose key and whose membership in every range of the
vocabulary are decided, when the source has no construct that can force
two data successors of one element apart and nothing compares values
across elements (`literal_profiles::distinct_data_successors_forced`):

- no positive `≥ n` with `n ≥ 2` and no negative `≤ n` with `n ≥ 1` over a
  role that is not certainly an object property (polarity-aware, so
  `≤ 1`, functionality and `≥ 1` are allowed),
- no `DisjointDataProperties`, no `HasKey`, no DL-safe rule.

The bridge admission checks the same condition on its own input
(`forced_distinct_data_successors`) before accepting a value without its
singleton clause.

**Exactness of the elision.** Dropping clauses can only add models, so
every entailment found without the singleton clauses is an entailment
with them. Conversely, let `J` be a model of the clause set without the
singleton clauses of the decided values `V_d`. Read `J` as a two-sorted
interpretation as in [NOMINALS-CB.md](NOMINALS-CB.md) §6 and map every
data node `n` that carries a value concept of `V_d` to that value, `val(n)`.
It carries exactly one identity class (the identity clashes of the
previous section hold in `J`), and its range labels are exactly the ranges
containing `val(n)` (every membership of a decided value is a clause).
Replace every data edge `(x, n)` by `(x, val(n))`; nodes without a decided
value are realized as before. Under this map:

- `∃p.D`, `≥ 1 p.D`, `p value t`, `∀p.D`, domains and ranges hold at `x`
  iff they hold in `J`, because they look only at the range and value
  labels of the successors, which `val` preserves;
- `≤ n p.D` holds at `x` because `val` maps the `D`-successors of `x` onto
  at most as many values as there are nodes;
- the gate excludes every other data construct: `≥ n` with `n ≥ 2` is the
  only source of `y₁ ≉ y₂` between data successors (two successors with one
  value would collapse), disjoint data properties and keys compare the
  identity of a value under two properties or across two elements, and
  rules can compare values.

So the image is a model of the source ontology with the same object part,
and every classification answer of the encoding without the singleton
clauses is exact. Where the gate fails, every value keeps its singleton
clause and the encoding is the one above.

### Counting over data values

Every asserted literal keeps its own identity (only the profile
abstraction, under its own gate, merges literals), so a count over asserted
values sees exactly the distinct values. Counting over anonymous values
uses the existing finite covers and integral cells; `≥ n` over a finite
range larger than the cover cap (8 enumerated values) stays an open corner
below.

### Bridge admission

The native bridge checks every relation clause against the datatype map.
It now reads the linear form (`DatatypeRelationIndex::for_input`): a
relation counts as present when the clauses entail it through a helper
(`includes`, `separated`, `equal`), and `linear_value_encoding_exact`
checks the helper clauses themselves: a helper is implied only by values;
two values with one bridge identity key never imply two bits of one
position (so bits separate only distinct values); and a profile includes
(excludes) a range only when every value implying it is in (outside) that
range. The pairwise check "every value pair is proved equal or disjoint"
runs in linear time over values whose identity class carries a complete
index, and pair by pair over the others. The singleton-clause check
scanned every concept per clause; it now reads the clause's own atom.

### Lean obligation

Proved: the conservative-extension lemma above for one arbitrary
interpretation (`LinearValueEncoding.lean`, core Lean, checked with
`lean ContextCalculus/LinearValueEncoding.lean`). Not proved, and outside
the current Lean boundary: that the Rust generator emits exactly these
clauses with a separating index, the oracle decisions `val_eq` and
`val_in_range`, the singleton elision (it needs the two-sorted reading of
the clause set, which the Lean development does not model), and the bridge
admission. The statement that would certify the elision is: for a clause
set `S` whose only clauses with an inequality between two successors of
one data role come from `≥ n` restrictions, and that contains no
role-disjointness clause between data roles and no rule, every model of
`S \ {singleton(v) : v ∈ V_d}` maps under `val` to a model of the source
ontology. Stating it needs a Lean model of the frontend's data-role
clauses, which does not exist yet.

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
