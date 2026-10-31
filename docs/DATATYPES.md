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
2. *Index digits.* The identity classes are numbered `0 … m-1`; with
   `k = ⌈log₂ m⌉`, class `i` implies `__dt__aux__digit__p__b` for every
   position `p < k`, where `b` is bit `p` of `i`, and the two digits of a
   position are disjoint. Two distinct classes differ at some position, so
   their values clash on one node: `O(m log m)` clauses for the `m²/2`
   pairwise clashes. (A base of `⌈√m⌉` needs only two labels per value node
   but one clash rule per pair of digits; on ore_ont_4572 it made the native
   bridge's consistency drive slower, so the generator uses base 2.)
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
(`binaryIndex_separating` below), so `v → digit__p__d`, `w → digit__p__e`
with `d ≠ e` and the position's clash give `v ⊓ w ⊑ ⊥`; and `v → profile → R` (resp.
`profile ⊓ R ⊑ ⊥`) gives each membership clause. (b) Every model `I` of
`S` expands to a model of `S'` by interpreting each helper as the union of
the values that imply it: `digit__p__d := ⋃ {v^I : digit p of index(key v) = d}`
and `profile_π := ⋃ {v^I : vector(v) = π}`. Every `v → helper` clause holds
by construction; `digit__p__d ⊓ digit__p__e` (`d ≠ e`) is empty because its
two sides are unions of values with different keys, which `S` makes
disjoint; and
`profile_π ⊑ R` holds because every member satisfies `v ⊑ R` in `S`. So `S'`
is a conservative extension of `S` over the source vocabulary: the two have
the same consistency, subsumptions and unsatisfiable classes. Both
directions are proved in Lean (`lean/ContextCalculus/LinearValueEncoding.lean`:
`bits_entail_pairwise`, `pairwise_admits_bits`, `binaryIndex_separating`,
`profiles_entail_membership`, `membership_admits_profiles`; the same lemmas
for an arbitrary digit base are `digits_entail_pairwise`,
`pairwise_admits_digits`, `twoDigitIndex_separating`). The file uses core
Lean only; since 2026-10-30 it is built by `lake build` as part of
`ContextCalculus` (see "Lean coverage" below).

### Object-level projection of data assertions

The linear form still gives the engines one data successor per asserted
value. On ore_ont_4572 (98,867 assertions on 32,990 individuals) the native
bridge's consistency drive then exceeded its budget, although the same
ontology without its data assertions classifies in about a second. Most of
the amendment-2 inputs use their data properties only through
functionality, class-conditional `≤ 1`, domains and atomic ranges, and for
such properties no data successor is needed at all
(`frontend/value_projection.rs`).

*Gate*, per group `G` of data properties connected by `SubDataPropertyOf`:
every TBox axiom that mentions a property of `G` is `FunctionalDataProperty(p)`,
`C ⊑ ≤ 1 p` or `C ⊑ ≤ 1 p.R` (`C` without properties of `G`, `R` a data
range), `DataPropertyDomain(p C)`, `DataPropertyRange(p R)` or
`SubDataPropertyOf(p q)`; no ABox axiom other than a positive data assertion
mentions `G`; the source has no key, rule or negative data assertion
(`literal_abstraction_blocked`); and for every assertion `u(a, v)` with
`u ∈ G`, every range of a super-property of `u` decidedly contains `v`, and
for every counted `(q, C, R)` with `u ⊑* q`, `v ∈ R` is decided and `v` has
an identity key.

*Projection* `O ↦ O'`: remove every assertion `u(a, v)` of an admitted
group and add `a : D` for every domain `D` of a super-property of `u`, and,
for every counted `(q, C, R)` with `u ⊑* q` and `v ∈ R`, the binary index
digits of the identity class of `v` among the values of `(q, C, R)` as
fresh object classes on `a`, with `C ⊓ digit_{q,C,R,k,0} ⊓ digit_{q,C,R,k,1} ⊑ ⊥`
for every position `k` (`DisjointClasses` when `C = ⊤`). The TBox axioms of
`G` stay.

**Theorem.** Under the gate, `O` and `O'` have the same models up to the
data edges of the admitted groups and the interpretation of the digit
classes; in particular they agree on consistency, subsumptions and
unsatisfiable classes.

*Proof.* (`O ⇒ O'`) Let `I ⊨ O`. Interpret `digit_{q,C,R,k,b}` as the
elements that have a `q`-value in `R` which is an asserted value of `G`
whose index has bit `b` at `k`. Every added class assertion holds: `a` has
the value `v` of its assertion along every super-property, and `I`
satisfies the domains. If `x ∈ C ⊓ digit_{…,k,0} ⊓ digit_{…,k,1}`, `x` has
two `q`-values in `R` with different indices, hence two distinct values,
contradicting `C ⊑ ≤ 1 q.R` in `I`. So `I` with these classes is a model of
`O'`.

(`O' ⇒ O`) Let `J ⊨ O'`. For every element `x` that is the interpretation
of an individual with assertions in `G`, delete the `G`-edges of `x` and add
`(x, v)` to `q` for every assertion `u(a, v)` with `a^J = x` and `u ⊑* q`;
call the result `I`. The TBox axioms of `G` are the only constraints on
`G`-edges. Every one of them is preserved: sub-properties hold because
edges were added along `⊑*` and `G`-edges of `x` were removed on all
properties of `G` alike; ranges hold because every asserted value is in
every range of its super-properties (gate); domains hold because the
domain classes are asserted in `O'` and an element without assertions keeps
its edges; `C ⊑ ≤ 1 q.R` (and functionality, `C = ⊤`, `R = ⊤`) holds at
`x ∈ C` because two distinct asserted values in `R` would differ in the
index of `(q, C, R)` at some position (division with remainder by 2 is
injective, `binaryIndex_separating`), so `x` would carry both digits of
that position, which `O'` forbids for `x ∈ C`; at an element without
assertions the edges are those of `J`. The edges deleted at `x` carried no
obligation: every TBox use of `G` is a domain, a range, an at-most or an
inclusion, none of which requires a successor. No other axiom mentions
`G`, and the object part, classes and individuals are those of `J`. The
data assertions hold by construction. So `I ⊨ O`. ∎

Lean: both directions are proved (`DataValueProjection.projection_sound`,
`projection_complete`; see "Lean coverage" below).

Groups outside the gate keep the data value encoding of the previous
sections.

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

**Theorem (singleton elision).** Let `O` be the source ontology and `S`
its clause set with every value singleton clause, `V_d` the values of the
vocabulary whose identity key and whose membership in every range of the
vocabulary the oracle decides, and `S⁻ = S \ {v(y₁) ∧ v(y₂) → y₁ ≈ y₂ : v ∈ V_d}`.
Assume the gate:

- (G1) no clause of `S` has an inequality between two successors over a
  data role, i.e. `O` has no positive `≥ n` with `n ≥ 2` and no negative
  `≤ n` with `n ≥ 1` over a role that is not certainly an object property;
- (G2) `O` has no `DisjointDataProperties`;
- (G3) `O` has no `HasKey` and no DL-safe rule.

Then for every model `J` of `S⁻`, the interpretation `I = ρ⁻(J)` defined
below is a model of `O` with the same interpretation of every class,
object property and individual as `J`. Hence `S⁻` and `S` agree on
consistency, on every subsumption and on every unsatisfiable class, for
every consumer that is exact on its clause set.

`ρ⁻` is the reading of a clause-set model as an ontology model that the
frontend's correctness arguments already use (data successors read as the
values their labels determine, objects as themselves; NOMINALS-CB.md §6 for
the two sorts and for one-sorted streams), changed in one point: a data
successor `n` that carries a value concept of `V_d` is read as that value,
`val(n)`, and two such successors with one value are read as one data
value, although `J` may keep them apart. `val(n)` is well defined because
the identity clashes of the linear form (or the pairwise clashes) are in
`S⁻`: `n` carries exactly one identity class.

*Proof.* Dropping clauses can only add models, so `S ⊨ φ` whenever
`S⁻ ⊨ φ`. For the converse, check every source construct at an object `x`
of `I`; constructs that mention no data role are evaluated on the object
part, which `ρ⁻` does not change.

- *Range labels are values' memberships.* For every range `R` of the
  vocabulary and every successor `n` with a decided value, `n` carries `R`
  in `J` iff `val(n) ∈ R`: each membership of a decided value is a clause
  of `S⁻` (`v ⊑ R` or `v ⊓ R ⊑ ⊥`, directly or through a profile).
- `∃p.R`, `≥ 1 p.R`, `p value t`, `∀p.R`, `DataPropertyDomain` and
  `DataPropertyRange` hold at `x` in `I` iff they hold in `J`: they ask for
  some, every, or no `p`-successor carrying `R` (or `{t}`), and `ρ⁻`
  preserves these labels.
- `≤ k p.R` (including functionality): `ρ⁻` maps the `R`-successors of `x`
  onto at most as many values, so the bound holds in `I` if it holds in `J`.
- `≥ n p.R` with `n ≥ 2` is the only construct whose clauses contain an
  inequality between data successors; it is excluded by (G1), as is the
  negative `≤`, which is a positive `≥` in negation normal form. Without
  it, no source construct needs two successors with one value to stay
  apart.
- `DisjointDataProperties(p q)` compares the identity of a value under two
  properties (G2); keys and rules compare values across elements (G3).
- Successors without a decided value are read exactly as before the change,
  and every decided value lies outside the fresh values that reading
  chooses, so the two kinds of successor never meet.

So `I ⊨ O`. ∎

The frontend evaluates the gate on the parsed source axioms after
DatatypeDefinition inlining (`distinct_data_successors_forced`, with
`HasKey` and rules read from the source profile, which is what the rule
grounding and the key lowering see), and only when data assertions are
carried. The bridge evaluates it again on its own input
(`forced_distinct_data_successors`, over the source axioms and data roles
of the TInput). The two do not need to agree: the frontend elides only
under its gate, which makes `S⁻` exact for every clause consumer, and the
bridge accepts a value without its singleton clause only under its own
gate, so a disagreement can only make the bridge defer.

Consumers checked for a dependence on the singleton clauses beyond the
datatype reasoning: the `data_abox` precheck reads the source text, not
the clause set; the sort encoding adds unary sort clauses and its
divergence argument only needed the singleton clauses not to fire across
object terms (removing them removes that risk); the nominal ABox merging
of §6 merges object terms only; `certified_card_proxy_abox` and every HT
worker read the clause set with ordinary clause semantics, so the theorem
covers them; rule grounding is excluded by (G3).

**Lean obligation.** Proved for a corrected `V_d` in
`DataValueSingletonElision.lean` (see "Lean coverage" below). The proof
shows that the theorem as stated above does not hold: `V_d` must also ask
that the relation of `v` to every other *value* of the vocabulary is
decided, and the Rust condition does not (finding 1 of "Lean coverage").

### Counting over data values

Every asserted literal keeps its own identity (only the profile
abstraction, under its own gate, merges literals), so a count over asserted
values sees exactly the distinct values. Counting over anonymous values
uses finite covers and integral cells. Until v1.5.4 a range was covered only
when it had at most 8 values, and KM answered `≥ 10 u.integer[1,9]`,
`≥ 257 u.unsignedByte` and `≥ 2 u.float[1.0,1.0]` satisfiable (HermiT:
unsatisfiable; probes in `results/agents/2026-10-30/data-values/probes/`).
Now:

- `≥ n p.R` with a finite `R` of fewer than `n` values is `⊥`, and
  `≤ n p.R` with at most `n` values in `R` is `⊤` (`syntax::data_at_least`,
  `data_at_most`; exact: a data successor is a value);
- every range and integral cell with at most `N` values is covered, where
  `N` is the largest number of pairwise distinct values one element can be
  forced to have (`literal_profiles::data_count_bound`: the maximum of the
  positive `≥ n` and negative `≤ n-1` bounds over data roles, their sum
  when two data roles are disjoint), capped at 4,096; finite IEEE intervals
  and bounded named integer types are enumerated too, and the native bridge
  admits such a cover when its heads are exactly the enumerated values
  (`exact_enumerated_cover`). A set of pairwise
  distinct successors comes from one `≥ n` restriction (the only source of
  `≉`), so no cell needs more than `N` distinct values unless two disjoint
  data roles add their successors, which the sum covers;
- a range the bound can exhaust but no cover reaches (a finite range larger
  than 4,096 values, or one whose size the oracle cannot tell, such as a
  string facet, next to a counting restriction) is published as not
  represented (`DROPPED`, reason "data cardinality over a range without an
  exact cover"): KM does not answer such an input as complete.

Covers of more than a few values make the engines search through the
assignments (pigeonhole), so `≥ 256 u.unsignedByte` (satisfiable) times
out instead of answering; the probes record this as a timeout, not as an
answer.

### Bridge admission

The native bridge checks every relation clause against the datatype map.
It now reads the linear form (`DatatypeRelationIndex::for_input`): a
relation counts as present when the clauses entail it through a helper
(`includes`, `separated`, `equal`), and `linear_value_encoding_exact`
checks the helper clauses themselves: a helper is implied only by values;
two values with one bridge identity key never imply two digits of one
position (so digits separate only distinct values); and a profile includes
(excludes) a range only when every value implying it is in (outside) that
range. The pairwise check "every value pair is proved equal or disjoint"
runs in linear time over values whose identity class carries a complete
index, and pair by pair over the others. The singleton-clause check
scanned every concept per clause; it now reads the clause's own atom.

### Lean obligations

1. *Linear form* (proved): the helper clauses are a conservative extension
   of the pairwise clauses for one arbitrary interpretation
   (`LinearValueEncoding.lean`, core Lean, built with `lake build` since
   2026-10-30). Not proved: that the Rust generator emits exactly these
   clauses with a separating index, and the oracle decisions `val_eq` and
   `val_in_range`.
2. *Object-level projection* (proved, 2026-10-30): both directions of the
   model construction, over a two-sorted language
   (`DataValueProjection.lean`; "Lean coverage" below).
3. *Singleton elision* (proved for a corrected condition, 2026-10-30;
   `DataValueSingletonElision.lean`). The Rust condition is weaker than
   the one the proof needs, and a probe shows a wrong answer
   ("Lean coverage", finding 1).
4. *Bridge admission* (not proved, as before): the gate is an executable
   check over the clause set; its correctness is tested.

None of these changes the CB or HT calculus; the engines consume the new
helper names as ordinary concepts.

### Lean coverage (2026-10-30)

Three modules, all built by `lake build` as part of `ContextCalculus`
(core Lean, no Mathlib import; axioms `propext`, `Classical.choice`,
`Quot.sound` only; no `sorry`):

- `lean/ContextCalculus/TwoSortedDL.lean`: the language. Class expressions
  with object constructors (`∃`, `∀`, `≥ n`, `≤ n`, `Self`, nominals) and
  data constructors (`∃u.R`, `∀u.R`, `≥ n u.R`, `≤ n u.R`) over atomic data
  ranges (`⊤` or a `__dt__` name; complex ranges are named by the frontend
  and `DatatypeDefinition` is inlined before the gates run); axioms `C ⊑ D`,
  class, object and data assertions, object and data sub-properties,
  `DisjointDataProperties`, `SameIndividual`, `DifferentIndividuals`.
  An interpretation has an object type, a data type and a free
  interpretation `dcon` of the data concept names. The OWL reading fixes
  the data type to a value space and `dcon` to the datatype map
  (`Interp.IsReal`); the clause reading leaves both free (data nodes are
  terms carrying `__dt__` labels, NOMINALS-CB.md §6). `HasKey` and DL-safe
  rules are not in the language.
- `lean/ContextCalculus/DataValueProjection.lean`: the object-level
  projection.
- `lean/ContextCalculus/DataValueSingletonElision.lean`: the singleton
  elision.

**Projection.** `projGate inG O sup memb key : Bool` is the gate as a
decidable function of the source axioms `O`, the admitted groups `inG`,
super-property lists `sup` and the oracle's decisions `memb` (range
membership, `Option Bool`) and `key` (identity key, `Option`): every axiom
mentions no role of `G` or is a domain `∃q.⊤ ⊑ D` with `D` free of `G`, an
atomic range `⊤ ⊑ ∀q.R`, a bound `C ⊑ ≤ 1 q.F` with `C` free of `G` (`F`
`⊤` or a range name; functionality is `C = F = ⊤`), a sub-property inside
or outside `G`, or an assertion of `G`; for every assertion `u(a, v)` of
`G`, `sup u` contains `u`, is certified reachable (`supCert`: each entry
is `u` or a direct super-property of an earlier entry) and closed under
`SubDataPropertyOf`, and `literalDecided` holds for every `q ∈ sup u`
(membership `some true` in every range of `q`; for every slot of `q`
`some false`, or `some true` with a key). `projGate_spec` turns the gate
into the facts the proofs use (`GateFacts`). `Proj` is `O'`: the kept
axioms, the domain assertions, the digit assertions and the digit clashes,
over class names `Cls ⊕ Digit` (fresh digits). With `ValuesSingleton`
(every asserted value name denotes one value `lit v`), `MembSound` and
`KeySound` (the oracle's decisions are true of `lit`):

- `projection_sound`: if `I ⊨ O` then `extend I ⊨ O'` and
  `(extend I).comapCls inl = I` (the digit classes are the elements with a
  `q`-value in `F` that is an asserted value with that index bit);
- `projection_complete`: with `IndexSeparates` (two different keys of one
  slot differ at some position below `npos`), if `J ⊨ O'` then
  `surgery J ⊨ O`, with the classes, object roles and individuals of `J`
  and the data roles outside `G` unchanged;
- `indexSeparates_of_injective`: an index injective on the slot's keys and
  below `2^npos` separates (from `binaryIndex_separating`), which is what
  the Rust numbering `0 … m-1` with `⌈log₂ m⌉` positions gives;
- `projection_consistency_iff`: `O` and `O'` are consistent together.

The data domain and `dcon` are arbitrary in these statements, so they hold
in the OWL reading and in the clause reading alike. The doc's proof needed
no change. Argued, not proved: that `value_projection::project` emits
exactly `Proj` for groups its gate admits, and that its gate implies
`projGate` (it is stricter: guards and domains mention no data role at
all, and negative data assertions, keys and rules block it).

**Singleton elision.** `gate O : Bool` is G1 and G2 as a decidable
function: `forces p C` mirrors `distinct_data_successors_forced::forces`
(polarity flips under `¬` and in the filler of `≤`; a positive `≥ n`,
`n ≥ 2`, or a negative `≤ n`, `n ≥ 1`, over a data role), `axForces` reads
`C ⊑ D` as `C` negative and `D` positive, class assertions as positive, and
rejects `DisjointDataProperties`; G3 is the restriction to the language.
Roles are sorted in the Lean language; the Rust gate's sort assignment
(`object_roles`: a role is data unless it is certainly an object property)
is the link, argued from the parser invariant that every data filler is a
`__dt__` name, its negation, `⊤` or `⊥`.

- `reading_models`: under `gate O`, if `J ⊨ O` (clause reading) and the
  node reading `ρ` respects the labels of every data successor
  (`Respects`), then `reading J ρ ⊨ O` (OWL reading) with the same object
  part. No singleton clause is used. The core is `eval_transfer`: at
  positive polarity truth moves from `J` to the reading, at negative
  polarity back, except for exactly the constructs `forces` reports.
- `decidedReading_respects`: reading a node that carries a value `v` with
  `fullyDecided voc isValue dec v` as `lit v` respects its labels, from the
  decision clauses (`DecisionClauses`, the pairwise form; the linear form
  entails it through the identity star, `bits_entail_pairwise` and
  `profiles_entail_membership`, a composition argued here, not stated in
  Lean)
  and the oracle's soundness (`DecisionSound`) alone.
- `singleton_elision_sound` (`S⁻ ⇒ O`): `J ⊨ O`, `J ⊨` decision clauses,
  and `UndecidedRealizable` (every successor without a fully decided value
  has a value with exactly its labels: the obligation the abstraction
  already had before the change) give an OWL model of `O` with the same
  object part.
- `real_model_satisfies_clauses` (`O ⇒ S`): an OWL model satisfies the
  decision clauses and every singleton clause.
- `consistency_iff`, `subsumption_iff` (class names): the two together.

`fullyDecided voc isValue dec v` asks that `v` is a value and that `dec v d`
is decided for *every* data concept name `d ≠ v` of the vocabulary: ranges
and the other values.

**Finding 1: the elision is not exact as implemented.** The Rust condition
`value_fully_decided` asks for a decided identity key and decided
memberships in the ranges, but not for decided relations to the other
values. `val_eq` is `None` between a keyed value and an opaque one, and the
derived string types (`xsd:token`, `xsd:normalizedString`, …) parse as
opaque although they share the string value space. A node can then carry
a decided value `v` and an opaque value `w`, and the decided reading does
not respect the label `w`. Probe
`results/agents/2026-10-30/lean-data-values/probes/opaque_merge.ofn`:
`FunctionalDataProperty(p)`, `p(x, "abc")`, `p(x, "abc"^^xsd:token)`,
`p(z, "abc")`, `¬p(z, "abc"^^xsd:token)`. HermiT: inconsistent. KM at
e62a4bce answers consistent on `auto`, `certified_nominals` and `nominals`;
the same ontology with an unrelated `Z ⊑ ≥ 2 q` (which closes the gate and
keeps the singletons, `opaque_merge_keep.ofn`) is answered inconsistent on
all three. With the singleton of `"abc"`, `x`'s merged successor and `z`'s
successor are one node, which carries the token and clashes with the
negative assertion; without it they stay apart. The fix the proof asks
for: elide `v` only when `val_eq(v, w)` is decided for every value `w` of
the vocabulary (equivalently here: no opaque value that `val_eq` cannot
separate from `v`), in the frontend and in the bridge's
`forced_distinct_data_successors` admission.

**Finding 2: exhaustion of a finite range by excluded values (not caused
by the elision).** `UndecidedRealizable` fails for a finite range with
more than 8 values when the data count bound is below 2: no cover is
emitted, so a node carrying `integer[1,9]` and none of its nine value
concepts satisfies the clauses but has no value. `range_exhaust.ofn`
(`x : ∃p.integer[1,9]`, `¬p(x, i)` for `i = 1 … 9`; HermiT inconsistent)
is answered consistent on all three routes, while the 8-value version is
answered correctly; v1.5.4 published the input with `DROPPED` (negative
assertions were not carried), so the wrong answer is new in v1.5.5. The
TBox form (`range_exhaust_tbox.ofn`, `A ⊑ ∃p.integer[1,9]` and
`A ⊑ ¬∃p.{i}`) misses `A ⊑ ⊥` in v1.5.4 and v1.5.5 alike. A range needs its
cover whenever the values of the vocabulary inside it, plus the count
bound, can exhaust it (`|R| ≤ |V ∩ R| + N`), not only when the count bound
can.

(Also observed, pre-existing, not a finding about these encodings:
`opaque_merge_tbox.ofn`, `A ≡ ∃p.{"abc"}`, `B ≡ ∃p.{"abc"^^xsd:token}`,
misses `A ≡ B` in v1.5.4 and v1.5.5 with or without the singletons; the
oracle does not relate the two spellings and publishes no `DROPPED`.)

**A run-time check.** The elision could carry a certificate: the list of
elided values, and for each the decision of its relation to every data
concept name of the clause set (a membership or exclusion clause, an
identity-star edge or a separating digit position). A checker would
evaluate `fullyDecided` on that list against the emitted clauses and `gate`
on the source axioms, in time linear in the clauses for the linear form
(one key class and its digits per value, one profile per value) and
quadratic for the pairwise form. It would have rejected `opaque_merge.ofn`
(the opaque value has no decision against `"abc"`). It would not check the
oracle's decisions themselves, the sort assignment of roles, or
`UndecidedRealizable`. Not implemented here.

### Fixes of findings 1 and 2 (2026-10-30, agent `data-values-2`)

**Derived string types.** The OWL 2 datatype map (Structural Specification,
section 4.3) gives `xsd:normalizedString`, `xsd:token`, `xsd:language`,
`xsd:Name`, `xsd:NCName` and `xsd:NMTOKEN` value spaces that are subsets of
the `xsd:string` value space, and the lexical-to-value mapping of each
applies XSD whitespace processing first (`replace` for `normalizedString`,
`collapse` for the others). The oracle (`datatypes::parse_literal`) now maps
such a literal to the string value of its normalized lexical form when that
form is in the type's value space (`derived_string_member`): `normalizedString`
excludes tab, line feed and carriage return, `token` additionally leading,
trailing and double spaces, `language` is the RFC 3066 pattern of XSD, and
the name types use the XML name-character classes. Those classes are decided
exactly on ASCII; a name with a non-ASCII character, or an ill-typed form,
stays opaque, as before. Membership of a string value in these types is the
same test. So `"abc"^^xsd:token` and `"abc"` are one value and receive one
identity key; `opaque_merge_tbox.ofn` (`A ≡ ∃p.{"abc"}`,
`B ≡ ∃p.{"abc"^^xsd:token}`) is answered `A ≡ B`.

`opaque_single.ofn` (`p(z, "abc")`, `¬p(z, "abc"^^xsd:token)`) is answered
inconsistent, which follows from the equality above; HermiT answers
consistent. HermiT is not consistent with itself here: on
`opaque_merge_tbox.ofn` it entails `A ≡ B`, which holds in a consistent
ontology with a functional `p` only if the two literals denote one value,
and that value would make `opaque_single.ofn` inconsistent. The integration
fixture records the datatype-map answer.

**Finding 1 (singleton elision).** `value_fully_decided` now takes the
values without an identity key (the opaque ones) and asks `val_eq` to be
decided against each of them, which is the hypothesis `fullyDecided` of
`DataValueSingletonElision.lean` (between two keyed values `val_eq` is always
decided). A value with an undecided relation keeps its singleton clause. The
native bridge admits a missing singleton only when every value of the
vocabulary has a bridge identity key (`bridge_value_identity_key`, extended
to the derived string types now that they parse exactly); otherwise it
defers. With the parse change `opaque_merge.ofn` has no opaque value left;
the gate change is what keeps a vocabulary with a genuinely undecided pair
(for example a non-ASCII `xsd:Name`) exact.

**Finding 2 (range exhaustion).** `datatypes::exhaustible_ranges` lists the
finite ranges `R` with `|R| ≤ |V ∩ R| + max(N, 1)`, where `V ∩ R` counts
every value of the vocabulary whose membership in `R` is not decided false
and `N` is the data count bound. The frontend raises the cover cap to the
size of each such range (up to `MAX_COUNTED_COVER`, 4,096), so the range
receives its exact cover `R ⊑ ⊔ {v}`; a range for which no cover is emitted
(too large, or a shape `enumerate_range` does not enumerate, such as a dense
point interval) is published as not represented (`DROPPED`), never answered.
An empty dense interval now receives the empty cover `R ⊑ ⊥`. Why the
condition suffices: a node labelled `R` without a cover is realizable unless
every value of `R` is excluded from it; it can only be excluded from values
the vocabulary names (a value concept is the only way a clause mentions a
single value), and it must differ from at most `N` (at least one: itself)
values chosen for sibling nodes, so with `|R| > |V ∩ R| + max(N, 1)` some value
of `R` remains for every node of an element (`UndecidedRealizable`). A cover
is a valid axiom (`R` is exactly the union of its values), so emitting more
covers never changes an answer. `range_exhaust.ofn` and
`range_exhaust_tbox.ofn` are answered as HermiT answers them.

Lean obligation: the derived-string parse is an oracle decision
(`DecisionSound` of `DataValueSingletonElision.lean`, not proved for the
Rust oracle, as for every other datatype). The gate now implements the
Lean hypothesis `fullyDecided` directly (argued from the code, not
extracted). The cover condition is `UndecidedRealizable` for finite ranges;
the counting argument above is not mechanised.

### Functional data values in the ABox quotient (2026-10-30, agent `data-values-2`)

The fail-closed ABox quotient (`orchestrate/abox_quotient.rs`) publishes the
taxonomy of `T ∪ Q` for a much smaller ABox `Q` when `T ∪ Q` is certified
consistent. Its only obligation is (1): `T ∪ Q` consistent implies `T ∪ A`
consistent; the taxonomy then follows from closure of `T` under disjoint
unions (`HypertableauDisjointUnionABoxProjection.lean`). Its merging key
contained the values of every count-restricted data property, so on
ore_ont_4572 (28 functional data properties, 33k individuals with distinct
values) no two individuals merged and the quotient declined
(29,113 blocks of 32,990).

New transformation S3 (`abstract_counted_values`): for a functional data
property `p` with no sub- or super-property and no data cardinality
restriction, the key and `Q` use, instead of the value `v` of `p(a, v)`, the
first value of `p` in the source with the same *datatype class* as `v`. A
class is a literal datatype (`xsd:string` with plain literals,
language-tagged strings, `xsd:decimal`, `xsd:boolean`, or one integer
datatype) whose values no datatype of the ontology separates. S3 applies
only when all of the following hold, and otherwise the quotient is built
as before:

- `T` has no nominal, no inverse role (`ObjectInverseOf`,
  `InverseObjectProperties`), no symmetric, reflexive or inverse functional
  property, no `ObjectHasSelf`, no `DisjointDataProperties`, no literal at
  all outside data-property assertions, no facet restriction or datatype
  definition and no derived string type; the ABox has no `SameIndividual`;
- no TBox datatype splits a class: an integer datatype `E` splits an
  integer datatype `D` when their value intervals meet and `E` does not
  contain `D`, and any integer datatype splits `xsd:decimal`;
- every value of an abstracted property is well formed (integer lexical
  forms inside the bounds of their type);
- no individual has two values of one abstracted property, and no
  individual has two asserted successors of one role under a cardinality
  restriction or a functionality axiom (through sub-roles).

Proof of (1). Let `I ⊨ T ∪ Q` and let `h` map each individual of `A` to its
block representative. Build `I'`: keep `I`, and add for every individual `a`
a fresh element `ȧ` (interpreting `a`) with the concept memberships of
`h(a)^I`; its outgoing edges are those of `h(a)^I`, except that for each
asserted `R(a, b)` (closed under the role hierarchy, transitivity and
chains) the edge to `h(b)^I` is replaced by an edge to `ḃ` where `R` is
counted, and added next to it where it is not. Its data edges are those of
`h(a)^I`, except that the single `p`-edge of an abstracted `p` (to the
representative `w`, which `Q` asserts, and only one since `p` is
functional) goes to `a`'s own value `v`. No edge of `I` enters a copy.
Then, by induction on concepts, every element of `I'` satisfies the same
concepts as its image in `I` (the image of `ȧ` is `h(a)^I`): `T` has no
inverse role, nominal or `Self`, so a concept depends only on the outgoing
structure; under a counted role the copy's successors map bijectively onto
the original's (one asserted successor per individual), under every other
role surjectively, which is all `∃`, `∀` and `≥` need there (a `≤` or a
`≥` read negatively makes the role counted); `v` and `w` lie in the same
datatypes of `T` and `T` names no value, so every data range and every
data restriction over `p` (functional, no cardinality) evaluates alike;
properties related to `p` do not exist. Transitivity and chains hold for
the copies by the closure of the asserted edges and, towards elements of
`I`, because `I` already has the composed edges. Disjoint, asymmetric and
irreflexive roles hold because every copy edge has an image edge in `I`.
`A` holds in `I'`: concept assertions by the memberships, role assertions
by the copy edges, `p(a, v)` by construction, every other data assertion
because `Q` repeats it for the block (exact values, or, for thinned
properties, by the thinning argument applied to the copy). Hence
`T ∪ A` is consistent.

On ore_ont_4572 the quotient now has 4,484 blocks and 48,639 assertions,
and the run takes 12 s instead of 381 s (taxonomy agrees with Konclude,
HermiT, Openllet). Lean obligation: none of S1 to S3 has a Lean model;
the quotient is checked by tests (`isolated_functional_values_are_abstracted_to_their_class`)
and by the scope run. A refutation of `T ∪ Q` is never published (defer).

### Boolean data ranges and ordered cells (2026-10-30, agent `data-values-3`)

**Defect.** `cell_exhaust_tbox.ofn` (`A ⊑ ∃p.(integer[1,9] ⊓ ¬integer[1,8])`,
`A ⊑ ¬∃p.{9}`) was answered with `A` satisfiable and `DROPPED 0` (HermiT:
`A ⊑ ⊥`). A `DataIntersectionOf` that is not a facet interval of one base was
one opaque range with no clause to its operands or to the values. The probes
of `results/agents/2026-10-30/data-values-3/` show that the same kind of hole
had more members, all answered wrongly without `DROPPED` by the branch point
(e2d5dd1f):

- three pairwise overlapping decimal-tower ranges with no common value
  (`∃p.integer ⊓ ∃p.decimal[1.2,3] ⊓ ∃p.decimal[0,1.8]`, functional `p`;
  `atomic_helly`): pairwise relations cannot see an empty triple
  intersection of an integer type and two dense intervals;
- two dense or IEEE intervals that meet in one point, next to an excluded
  value (`dense_point`, `float_cells`), and dense or IEEE complements
  (`bool_complement_dense`, `float_complement`);
- an integer cell that is exhausted by excluded values although no range
  of the vocabulary is (`int_cell_exhaust`);
- named types of the map that the oracle did not relate: `rdf:PlainLiteral`
  (treated as opaque), the string chain below `xsd:token`,
  `xsd:dateTimeStamp ⊑ xsd:dateTime`, `xsd:hexBinary` against
  `xsd:base64Binary`, and a decimal value against `xsd:float`/`xsd:double`
  (membership `None`);
- pattern and length facets and dateTime facets (`length_*`, `pattern_*`,
  `datetime_empty`, `datetime_value`, `datetime_subsumption`): opaque, so an
  empty facet range or a literal outside it was missed.

**What a label set must satisfy.** The relation clauses abstract a data node
by the set `L` of `__dt__` names it carries. A clause model `J` reads as an
OWL model when every data node gets a value `v` with `v ∈ d ⟺ d ∈ L` for
every name `d` of the vocabulary (the `Respects` hypothesis of
`DataValueSingletonElision.lean`), avoiding the values of the other nodes
where a count forces distinctness (`UndecidedRealizable`). The fix makes
every label set that the clauses admit realizable in this sense, or
publishes the input as not represented.

**Boolean structure** (`frontend/datatypes/vocabulary.rs`, `expand`). For
every name with Boolean structure the operands join the vocabulary and the
role groups of the name (closed transitively), and the frontend emits the
definitional clauses: `I → Mᵢ` and `M₁ ∧ … ∧ Mₖ → I` for
`I = DataIntersectionOf(M₁ … Mₖ)` (an `rdfs:Literal` member is left out of
the body), `Mᵢ → U` and the historical cover `U → M₁ ∨ … ∨ Mₖ` for a union,
and `C ∧ A → ⊥` with the historical excluded middle `→ C ∨ A` for
`C = DataComplementOf(A)`; `DataComplementOf(rdfs:Literal)` gets `C → ⊥`. In
every model of the clauses a Boolean name then holds at a node exactly when
the Boolean combination of its operand names does, so a label set is
realizable iff its atomic part is, and a value realizing the atomic part
gives each Boolean name its correct truth value. The oracle also decides
Boolean ranges directly (`DRange::Intersection`, value-by-value membership,
exact sizes by enumeration, `dense_band`); those clauses are consequences of
the definitional ones. Exhaustion and counting are decided on the atomic
names and the cells, not on the Boolean name (`DataVocabulary::boolean`).

**Ordered cells.** In a role group with at least two atomic ranges of the
decimal tower, one of them not integral, or with at least two ranges of
one IEEE width, `expand` cuts the partition at every range endpoint:

- decimal tower: every endpoint is a point cell (a value concept); every
  open gap between consecutive endpoints is split into bands by the value
  kinds present in the group: the integers of the gap (an integer facet
  interval, a value, or nothing), then each present kind minus the one
  below it, e.g. `DataIntersectionOf(DatatypeRestriction(xsd:decimal
  xsd:minExclusive a xsd:maxExclusive b) DataComplementOf(xsd:integer))`;
- IEEE: the rank segments between endpoints, with `-0`, `+0` and `NaN` as
  points of their own; a segment is named by its first and last value as
  an inclusive facet interval, and the name is checked to denote exactly
  that segment.

Every atomic range of the group contains a whole cell or none of it (the
cuts are its endpoints, and its kind is one of the bands), so a
representative decides the membership of the cell (`cell_member`; bands of
non-decimal rationals and of irrationals are decided by kind, which is exact
because only the unbounded named types `owl:rational` and `owl:real` have
those kinds; a facet interval over them next to another decimal-tower range
is reported). The frontend emits `c → R` or `c ∧ R → ⊥` for every cell `c`
and atomic range `R` of the group, the cover `R → ⋁{c ⊆ R}` for every range
of the partition, and `c ∧ c' → ⊥` for distinct cells (point cells are
values, separated by the value relations). Groups whose numeric ranges are
all integral keep the integral cells of `integral_cell_covers`, unchanged. A partition whose ranges the oracle decides pairwise nested or
disjoint, and in which every range has a cell of at least 2^62 values
outside all ranges strictly inside it (a chain of named types such as
`long ⊂ integer ⊂ decimal`), gets no cells either: a label set closed under
the pairwise clauses then has a least range `R` and none of its sub-ranges,
and the large residue of `R` holds a value with exactly those labels that
avoids every vocabulary value and every counted sibling. Such inputs keep
their clause stream, and with it the native bridge's admission
(ore_ont_5964).
Cells are ordinary range names: the value relations, the exhaustion test
and the counted covers apply to them, so a finite cell (an integer band, an
IEEE segment) that the values plus the count bound can exhaust receives its
enumerated cover or is published as not represented.

**Exactness.** Fix a model `J` of the clause set and a data node `n` with
label set `L`. (i) If `L` contains a range of an ordered partition with
cells, the cover gives `n` a cell `c ∈ L`, and the cell clauses fix the
membership of `L` in every atomic range of the group to that of `c`. A point
cell is a value whose relations to every name are decided. A band of a
nonempty open interval with a non-integer kind is infinite, and an integer
band or IEEE segment with more values than the vocabulary's values in it
plus the count bound has a value that no constraint excludes; a smaller one
has its enumerated cover, which puts a value concept into `L`. (ii) In the
string partition the named types form the chain `language ⊂ NCName ⊂ Name ⊂
NMTOKEN ⊂ token ⊂ normalizedString ⊂ string ⊂ rdf:PlainLiteral` (XSD 1.1
part 2 sections 3.3.1, 3.4.1 to 3.4.7: a language tag starts with a letter
and has only letters, digits and `-`, so it is an NCName; a NameStartChar
is a NameChar), with infinite differences, and the oracle now emits every
inclusion of the chain; an upward-closed label set is realized by a fresh
string of its least type. Booleans have their two-value cover; `anyURI`,
the binary types, `dateTime ⊃ dateTimeStamp` and `XMLLiteral` are single
types or a two-type chain with infinite difference. (iii) A Boolean name
holds exactly as its operands say (above). (iv) Finitely many values and
counted successors cannot exhaust an infinite cell. So every admissible
`L` is realized, with as many distinct values as a count can demand, and
the clause set is exact for the vocabulary.

**The decided fragment.** `expand` reports, and the frontend publishes as
not represented (`DROPPED`, reason "data range outside the decided datatype
fragment: …"), every name that the datatype map defines but the oracle does
not decide: a facet other than the four bounds, or a bound on a
non-numeric base (pattern, length, minLength, maxLength, totalDigits,
fractionDigits, langRange; dateTime bounds); a literal of a map datatype
that does not parse into an exact value (an ill-typed literal, a binary or
`XMLLiteral` value, a name type with a non-ASCII character); a literal whose
membership in a decided range is undecided; an `rdfs:Literal` member of a
union; a cell group with more than 512 cells. Datatypes outside the OWL 2
datatype map (custom IRIs, `xsd:date`, `xsd:time`, the `g*` types,
`xsd:duration`) have no fixed value space and keep the free abstraction:
their names and literals are related to nothing, as before. The native
bridge and the HT workers read the clause set; they defer on the new names
unless their own gates admit them (below).

**Native bridge: data complements** (supervisor item, seeds 2000 to 2399).
The bridge's exact atomic map now admits `DataComplementOf(A)` for a named
range or facet interval `A` of the decimal, IEEE, string, boolean, dateTime
or XMLLiteral family (`bridge_exact_complement_operand`). It requires the
disjointness `¬A ∧ A → ⊥` and the excluded middle `→ ¬A ∨ A` in its input,
treats `A` as body-sensitive in the cell certificates (a node with `¬A`
must be realized outside `A`; a node without `¬A` carries `A`), accepts a
partial overlap of `¬A` with a finite range, a union or another complement
(decided by their covers) or with a range of `A`'s own family (decided by
that family's certificate), runs the IEEE certificate when `A` is an IEEE
range, and defers when an `xsd:anyURI` range is present: a node that
carries only complements is realized by a fresh IRI, which lies in every
admitted complement and outside every other admitted range.

**Native bridge: singleton gate** (seeds m2009, m2023, m2123, m2255,
m2287). The frontend leaves out value singletons when
`literal_profiles::distinct_data_successors_forced` finds no number
restriction over a role that is not certainly an object property; the
bridge's `forced_distinct_data_successors` counted a number restriction as
a data restriction whenever its filler mentioned a datatype, so
`≤ 1 s.∃v.{"y"}` over the object property `s` made it demand singletons
the frontend had (correctly) left out, and the bridge deferred. The bridge
now decides by the role, as the frontend does, and reads `DisjointClasses`
with both sides negative, as the frontend does. Its data roles are the
roles with a datatype filler or range or a source data-property
declaration, all of which the frontend also treats as data roles (a role is
data unless certainly an object property), so whenever the frontend elides
a singleton the bridge's gate admits the elision.

**Lean obligation (not proved here).** Extend `TwoSortedDL` data ranges with
`DataIntersectionOf`, `DataUnionOf` and `DataComplementOf` and state: (a) the
definitional clauses make every Boolean name equivalent to the combination
of its operands in every clause model (a structural induction); (b) *cell
realizability*: for a vocabulary whose atomic ranges are intervals of the
decimal tower or of one IEEE width, with the cell cover, cell membership and
cell disjointness clauses, every label set closed under the clauses has a
value, and `n` distinct values when its cell has more than `n` values
outside the vocabulary's values (this discharges `UndecidedRealizable` for
those partitions); (c) the string chain inclusions as `DecisionSound`
facts. The oracle decisions themselves (`val_in_range`, cell membership by
kind) remain checked by tests, as before.

## Open corners (status 2026-10-30, after `data-values-3`)

Every corner now has one of two behaviours: an exact answer, or an input
published as not represented (`DROPPED`) or refused. Probes with HermiT
gold: `results/agents/2026-10-30/data-values-3/`; integration test
`engine/tests/data_range_corners.rs`.

| corner | behaviour | probes |
|---|---|---|
| `DataIntersectionOf` / `DataUnionOf` / `DataComplementOf` | exact (definitional clauses, cells) | `cell_exhaust_tbox`, `bool_*`, `union_complex`, `count_complex`, `int_cell_exhaust` |
| overlapping decimal / IEEE intervals | exact (ordered cells) | `atomic_helly`, `dense_point`, `dense_count`, `float_cells`, `float_complement`, `decimal_mixed_ok` |
| float/double vs decimal cross-tower | exact (disjoint value spaces; decimal values outside IEEE types) | `float_decimal`, `float_value_decimal`, `integer_double_sub` |
| string types, `rdf:PlainLiteral`, `dateTimeStamp`, binary types | exact (chain inclusions, PlainLiteral values, disjoint binary types) | `string_chain` (HermiT differs, see the fixture), `plain_literal`, `datetime_stamp`, `binary_disjoint` |
| dateTime identity | exact (timezone kept, as HermiT) | `datetime_offset` |
| pattern and length facets | DROPPED on the automatic route, refused on the forced nominal routes | `length_empty`, `length_exhaust`, `length_value`, `pattern_value`, `pattern_subsumption` |
| dateTime facets (ordering) | DROPPED / refused | `datetime_empty`, `datetime_value`, `datetime_subsumption` |
| `xsd:duration`, `xsd:date`, `g*`, custom datatypes | outside the OWL 2 map: free abstraction (HermiT rejects such inputs) | none |
| n-ary `DataSomeValuesFrom` | no n-ary datatype exists in the OWL 2 map; KM rejects the input (exit 2, "invalid OWL 2 DL input"), the OWL API does not parse it | `nary_some` (no gold) |
| `HasKey` with data properties | refused on every route | `haskey_data`, `haskey_data_ok` |
