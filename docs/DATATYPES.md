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

## Open corners (status 2026-10-30)

Handled exactly since v1.5.5 (sections above): data-property assertions of
any number of literals, with or without counting; negative data-property
assertions; `≥ n` / `≤ n` over finite ranges of known size (including IEEE
intervals and bounded integer types); data-property assertions on the
nominal routes (`KM_NOMINALS`), which receive the same clauses.

Still sound but possibly incomplete, with the behaviour KM shows:

- pattern / length facets: the range stays opaque; next to a data counting
  restriction it is reported as not represented (`DROPPED`), otherwise it
  is answered over the opaque abstraction (incomplete, not flagged);
- dateTime/duration ordering and arithmetic: not flagged;
- float/double vs decimal cross-tower subsumption: not flagged (values are
  compared exactly, but the named types are not ordered against each other);
- `DataComplementOf` / `DataIntersectionOf` / `DataUnionOf` structure beyond
  the excluded middle and union covers: not flagged;
- n-ary `DataSomeValuesFrom` (multi-property comparisons): unchanged from
  v1.5.4;
- `HasKey`: lowered to DL-safe rules (`has_key.rs`), whose data atoms fail
  closed on the rule routes.

The unflagged corners are the ones listed in v1.5.4; making each of them
either exact or flagged is not part of this change.
