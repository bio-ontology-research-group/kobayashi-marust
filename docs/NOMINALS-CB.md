# Nominal support in the CB engine (ALCHOIQ calculus)

Status: PHASES 0–2 IMPLEMENTED AND ROUTED; PHASE 3 IN PROGRESS. Phases 0+1 (frontend DL7/DL8 +
ground ABox; engine v_r, r-Succ/r-Pred, grounded Hyper, Table-2 deltas) landed
first; Phase 2 (Join, r-Succ condition (*), the Nom rule with additional
nominals) and the single-firing Lean soundness layer in
`lean/ContextCalculus/Nominals.lean` followed. All six witness probes pass
(the five Phase-1 probes plus `oracle/ontologies/nom_oiq_funct.ofn`, the
paper's Example 3, the O+I+Q interaction that *requires* Nom), each matching
the HermiT oracle. `KM_NOMINALS=1` is now the internal setting of the exact
`nominals` route. The default router selects that route whenever the source
profile contains an ABox or nominal individual, except when the version-2
source profile proves that a strictly positive ABox is consistent and cannot
change TBox subsumptions. It excludes proxy CB and EL from every uncertified
nominal fragment. ORE 148, 178, and 11016 match their exact Konclude
signatures with the production route; the post-fix full-corpus matrix is the
remaining regression and performance audit.

Phase-2 implementation notes (engine.rs):
- Nom fires inside `build_hyper_resolvent` in the ground context when σ(x)=o
  and a head a-equality instantiates to `y≈y` / `y≈f(o')` (previously dropped
  as a tautology — exactly the lost constraint). The emitted disjunction has
  `K + K''` additional nominals, NOT the paper's `K` (or its proof's
  `max(K,K'')`): the certified covering bound (`nom_cover` in Lean) is the sum
  `(n−1) + K''`, and wider disjunctions are sound. Additional nominals are
  allocated in a stable disjoint block per exact grounded Hyper firing. An
  exact replay reuses its block so saturation remains finite; unrelated
  firings do not share existential witnesses. `KM_NOM_BUDGET` defaults to
  4096; a block that does not fit marks the run incomplete before publication.
- The Hyper candidate scan includes the side clause at non-side positions in
  the ground context (given-clause `S_v ∪ {C}` semantics): elsewhere the
  self-pair is provably redundant, but `S(x,z₁)∧S(x,z₂)` matching the same
  `S(o,y)` hypothesis twice is the Nom trigger. The symmetric-group strict
  pruning likewise admits the equal-`y` assignment in the ground context.
- Join: per-context `ground_body_index` (clauses by ground body atom) and
  `bridge_index` (body-empty clauses with maximal `x≈o`); cases 1+2 fire from
  both arrival orders plus a `pred_local` refire on ground maximal heads;
  case 3 fires from consumer, provider, and bridge arrival.
- r-Succ (*): a push of `Γ → Δ ∨ Aσ` is blocked when a worked-off clause
  `Γ'' → Δ'' ∨ ⋁L_i` with `Γ''⊆Γ, Δ''⊆Δ` has only merge-form `L_i`
  (`x≈o, y≈o, x≈y`) — per-context `merge_clauses` index.
- r-Pred pipeline: body atoms may be discharged over different
  individual-labelled edges of the same source (the paper's per-`A_i` edges);
  ground `C_i` copy verbatim when their individuals are announced; head
  individuals (Nom's fresh nominals) need no edge — the old head-individual
  edge filter made Nom conclusions undeliverable.

The original design notes follow. Target calculus: Tena Cucala, Cuenca Grau,
Horrocks, "Consequence-based Reasoning for Description Logics with Disjunction,
Inverse Roles, Number Restrictions, and Nominals", IJCAI 2018
(arXiv:1805.01396). The engine header has referenced its Table 3
(Nom/Join/r-Succ/r-Pred) since the start; this doc maps it onto KM. The arXiv
source tarball includes full soundness/completeness proofs
(proof-sound.tex, proof-completeness.tex, proof-payasyougo.tex), which the
Lean re-certification will follow.

## 1. The gap before the port

The frontend rewrites `{o}` to a fresh concept `__nom__o`
(normalise.rs `nominal_name`), lifts unconditional ABox facts `C(o)` to
`__nom__o ⊑ C` (preprocess.rs `nominal_clauses`), and the CB engine drops any
clause that still mentions an individual term (reasoner.rs `term`, counted in
`dropped`). This is sound (proxy models are a superset) but incomplete
whenever the singleton property of `{o}` matters.

Confirmed minimal witness (HermiT-verified, ddmin-minimal, KM misses A ⊑ G;
probe `/tmp/probe_nom1.ofn` on ws):

```
SubClassOf(:A ObjectSomeValuesFrom(:r ObjectIntersectionOf(ObjectOneOf(:o) :B)))
SubClassOf(:A ObjectSomeValuesFrom(:r ObjectIntersectionOf(ObjectOneOf(:o) :C)))
SubClassOf(ObjectIntersectionOf(:B :C) :E)
SubClassOf(ObjectSomeValuesFrom(:r :E) :G)
```

Both r-successors of an A-element are o, so o ∈ B⊓C ⊑ E and A ⊑ ∃r.E ⊑ G.
With proxies the two successors stay distinct. The same witness defeats elc
(proxies are plain concepts, so nominal ontologies are not fenced from the EL
path). The dual ABox direction (ClassAssertion + `∃r.{o}`) IS covered by the
proxy lifting (probe_nom2 passes).

Corpus exposure: 60 of the 592 benchmarked ORE ontologies contain
`ObjectOneOf`/`ObjectHasValue` (unimatrix /tmp/nom_onts.txt). Gold currently
agrees with KM on all of them (the merge pattern does not change ORE class
subsumptions), so this work is driven by the completeness mandate, not the
passrate.

## 2. Calculus summary (what changes vs the SRIQ core KM implements)

Clausification keeps individuals as constants (no proxies):

- DL7: `{o} ⊑ B`  ⇝  `⊤ → B(o)`
- DL8: `B ⊑ {o}`  ⇝  `B(x) → x ≈ o`
- ABox: `C(a)` ⇝ `⊤ → C(a)`; `r(a,b)` ⇝ `⊤ → r(a,b)`;
  `a ≈ b` / `a ≉ b` as ground (in)equalities.

Terms: a-terms gain named individuals `o` and, in the root context, `f(o)`.
p-terms gain `B(o)`, `S(x,o)`, `S(o,x)`, `S(o,o')`. Context clauses may carry
ground literals anywhere; bodies of derived clauses may contain ground atoms.

One distinguished root context `v_r` holds all ground inference. (KM's
existing "root" flag marks query contexts; the paper gives query clauses their
own contexts too. `v_r` is a new, single, third kind. Naming below:
`nominal root context` to avoid collision.)

New trigger sets:
- `Su^r` (root successor triggers): all `B(o)`, `S(y,o)`, `S(o,y)`.
- `Pr^r` (root predecessor triggers): `Su^r ∪ {B(y)} ∪ {y ≈ o}`.
- `Pr` (ordinary predecessor triggers) is extended with `{x ≈ o}` and
  `{y ≈ o}` for every individual o.

Table 2 deltas (existing rules, exact):
- Hyper: `σ(x) = x` if `v ≠ v_r`; on `v_r`, `σ(x)` may be any individual.
- Eq: extra side condition: if the rewrite position `s2|p` is an individual,
  `s2` must contain no function symbols.
- Pred: does not apply to `v_r`. Ground body atoms `C_i` are copied verbatim
  into the derived clause's body (only nonground `A_i` resolve against the
  predecessor). `σ = {y↦x, x↦f(x)}` for ordinary predecessors u, and
  `σ = {y↦o, x↦f(o)}` when `u = v_r`.
- Succ: the trigger atom contains `f(x)` for ordinary u, `f(o)` when
  `u = v_r`; σ as in Pred.

Table 3 (new rules, exact):

- **Join** (ground resolution inside any context v): if
  1. `A ∧ Γ → Δ ∈ S_v`, A ground and mentioning o, and
  2. `Γ' → Δ' ∨ Δ'' ∨ A ∈ S_v` with `Δ'∪Δ'' ⋡_v A`, or
  3. `Γ' → Δ' ∨ A' ∈ S_v` with `Δ' ⋡_v A'`, `A'{x↦o} = A`, and
     `Γ' → Δ'' ∨ x≈o ∈ S_v`, `Δ'' ⋡_v x≈o`, `Γ' = ⊤`,
  then add `Γ ∧ Γ' → Δ ∨ Δ' ∨ Δ''` to `S_v`.
- **r-Succ** (context u → v_r): if `Γ → Δ ∨ Aσ ∈ S_u` (`Δ ⋡_u Aσ`, u ≠ v_r),
  `A ∈ Su^r` mentioning o, `σ = {y↦x}`, no edge `⟨u,v_r,o⟩` already covers
  A→A in `S_{v_r}`, and (*) no clause `Γ'' → Δ'' ∨ ⋁L_i ∈ S_u` with
  `Γ''⊆Γ`, `Δ''⊆Δ`, every `L_i` of the form `x≈o_i`, `y≈o_i`, `x≈y`,
  then add edge `⟨u,v_r,o⟩` and `A → A` to `S_{v_r}`.
  (Condition (*) defers to equality reasoning when u's element may itself be
  a nominal or merge with its predecessor.)
- **r-Pred** (v_r → any context with an o-edge; non-local): if
  `⋀A_i ∧ ⋀C_i → ⋁L_i ∈ S_{v_r}` with every nonground `L_i ∈ Pr^r`, every
  `C_i` ground, every `A_i ∈ Su^r` with individual `o_i`, and for each `o_i`
  there is `⟨u,v_r,o_i⟩ ∈ E` with `Γ_i → Δ_i ∨ A_iσ ∈ S_u` verifying (*),
  `Δ_i ⋡_u A_iσ`, `σ(y) = x`,
  then add `⋀Γ_i ∧ ⋀C_i → ⋁Δ_i ∨ ⋁L_iσ` to `S_u`.
- **Nom** (only in v_r; the doubly-exponential source): if an ontology clause
  `⋀A_i → ⋁_{i≤m}L_i ∨ ⋁_{m<i≤k}L_i` (the `L_i` a-equalities) hyper-matches
  in `v_r` under σ with `σ(x) = o`, and `L_iσ` has the form `y≈y` or
  `y≈f_i(o_i)` exactly for `m < i ≤ k`,
  then add `Γ → Δ ∨ ⋁_{i=1}^K y ≈ o'_{ρ·S^i}`, where the `o'_{ρ·S^i}` are
  fresh "additional nominals" indexed by nominal labels ρ (strings over role
  symbols) and `K+1 = max(i | z_i in O)`.
  Nom never fires unless inverse roles, nominals, AND number restrictions
  interact (rare in practice).

Order conditions (Def 3 + appendix A): the context order must satisfy
`A ≻ x ≻ y ≻ true`, `f(x) ≻ g(x)` for `f > g`, congruence/subterm conditions,
nominal-label monotonicity `o_ρ > o_ρ'` when ρ extends ρ', and crucially
`A ⊁ s` for every `A∈Pr∪Pr^r` and `s ∉ {x,y,true}∪Σ_o`. The appendix
constructs a valid order as an LPO relaxed by dropping all comparisons
`y≻o, o≻y, x≻o, o≻x` (nominals incomparable to variables). In KM this lands
in the literal-order functions (calc.rs `pred_lteq` family), exactly where the
d3a0e1e mutual-incomparability fix lives, NOT in `term_max`.

## 3. KM mapping

Representation:
- `Term` stays i32. Current: `0=x, -1=y, -(i+1)=z_i, i>0 = f_i(x)`.
  Extension: split the positive space by high bits into three tagged ranges:
  `f_i(x)` (existing), `o_k` (input individuals + additional nominals), and
  interned `f_i(o_k)` pairs (composite ids in a side table; only materialised
  in v_r, rare). `is_function`, `is_var`, ordering helpers, and the
  Pred/Succ trigger predicates branch on the tag. All order changes go
  through the lteq functions to encode the incomparabilities.
- `Lit`/`Pred` gain no new variants (ground atoms reuse Concept/Role/Eq with
  individual terms). `ContextClause` invariants that assume function-free
  heads for Pred eligibility must treat ground literals as a third class
  (copied, not resolved).
- reasoner.rs `term`: stop returning None for `JTerm::Ind`; intern the
  individual. `dropped` should go to 0 for nominal ontologies.

Engine:
- A single nominal root context `v_r`, created on demand when the ontology
  has any individual (clause mentioning Σ_o). Ground input clauses seed
  `S_{v_r}` via Core/Hyper with `σ(x) = o`.
- Edges to `v_r` are labelled by individuals (`⟨u, v_r, o⟩`), kept in a
  separate map from the function-labelled successor edges.
- Join is a within-context rule: index ground head atoms per context;
  resolve against ground body atoms. Case 3 needs the `x≈o` bridge form.
- r-Pred is non-local: any context with an o-edge subscribes to v_r
  conclusions. Reuse the existing Pred message queue with a v_r channel.
- Nom: gated behind detection of the O+I+Q interaction triple. Production now
  uses exact-firing witness blocks; the remaining certification must bind the
  generated block identity and ordering to the executable trace.

Frontend:
- New mode (env `KM_NOMINALS=1` while landing, default on once validated):
  emit DL7/DL8 + ground ABox clauses instead of `__nom__` proxies +
  `nominal_clauses` lifting. The data_abox.rs unsat precheck stays (it
  covers ground-only clashes the calculus also finds; byte-output parity
  matters only off-flag).
- Routing: ontologies with individuals must NOT route to elc until elc grows
  ELO rules; fence in owl_classify/ofn meta (`el_rbox_safe` stays true only
  for nominal-free input) once the engine path is complete.

## 4. Phasing and validation gates

- Phase 0 (frontend, flag-gated): DL7/DL8 + ground ABox emission.
  Gate: off-flag output byte-identical across the corpus; on-flag clause set
  validated on probes.
- Phase 1 (engine, no Nom): terms, v_r, Join, r-Succ, r-Pred, Table 2
  deltas. Complete for ontologies where O, I, Q do not all interact
  (covers ALCHOQ and ALCHOI, hence all 60 ORE nominal ontologies unless one
  has the triple). Gate: probe nom1 derives A ⊑ G; nom2 still passes;
  cargo tests; sig-vs-gold unchanged-or-better on the 60 nominal onts and
  byte-identical engine output on nominal-free onts (the rules are inert
  without individuals); HermiT oracle spot checks on the nominal onts.
- Phase 2: Nom + additional nominals + order conditions. Gate: synthetic
  O+I+Q probes (paper Example 3 as a test), termination guard
  (additional-nominal budget with explicit report, never silent).
- Phase 3: Lean certification of the four rules, generalised Table 2 rules,
  production-state refinement, and completeness. Single-firing Nom soundness,
  finite composition with disjoint blocks, and the exact Join-3 transformation
  are established. Executable Nom evidence, inter-context transfer, terminal
  closure, and the production completeness refinement remain open.

## 5. Open questions

- elc and ELHO: the calculus is polynomial for ELHO with the standard
  strategies, so the long-term option is ELO rules in elc (Kazakov et al.
  KR 2012) vs always fencing nominal ontologies to CB. Decide on measured
  cost over the 60-ontology set.
- Whether the central (grown-core) strategy interacts with r-Succ edge
  reuse; the paper's (*) condition references clauses of the SOURCE context,
  so trigger-set growth does not affect it, but this needs the same
  fact-core scrutiny as fd94c7e.
- Additional-nominal explosion control: the paper bounds Nom by input
  z_i-multiplicity; KM should surface a counter (KM_STATS) from day one.

## 6. Object and data sorts (`frontend/sorts.rs`)

OWL 2 Direct Semantics interprets class expressions over the object domain
`Δ_I` and data ranges over the data domain `Δ_D`, with `Δ_I ∩ Δ_D = ∅`,
object properties in `Δ_I × Δ_I`, and data properties in `Δ_I × Δ_D`.
The clause set is one-sorted: a data value is an element of the single
domain, carrying its `__dt__` concept, and the value's at-most-one clause
`v(z₁) ∧ v(z₂) → z₁ ≈ z₂` binds its two unguarded variables to any pair of
terms of a context. Under nominal clausification the ground context
instantiates every empty-body fact at every ground term. A fact `⊤ ⊑ C` is
`owl:Thing ⊑ C` and should range over `Δ_I` only; applied everywhere,
the excluded middle `⊤ ⊑ ¬{v} ⊔ {v}` of a negated value restriction offers
`{v}` at every named individual, every Skolem successor and the
universal-role hub (`⊤ ⊑ ∃link.{hub}` is the reproducer), the at-most-one
clause turns every pair of them into a merge candidate, and the ground
context does not terminate in practice. (An interim encoding of the
at-most-one clause as `v(x) → x ≈ o_v` over a fresh individual removed
the unguarded variables but made each value a hub of the ground context,
which cost ore_ont_9800 more than an order of magnitude; it was reverted
once the sort encoding below proved sufficient on its own.)

The frontend therefore makes the two sorts explicit, with one fresh marker
concept `D` (`__data__`, interpreted as `Δ_D`), only under nominal
clausification and only when the clause set carries a data value, a data
range or a data-property atom next to nominals or individuals (until
m2197, below, only a data value opened the gate). Everything else keeps its clause output unchanged.
The encoding is linear in the signature:

- every data range `R` (a `__dt__` concept): `R ⊑ D`;
- every object-sorted concept `A` (source classes, `__nom__` proxies,
  object-sorted definers): `A ⊑ ¬D`;
- every role `P`: `∃P.⊤ ⊑ ¬D`; `∃P⁻.⊤ ⊑ ¬D` when `P` is object-sorted
  and `∃P⁻.⊤ ⊑ D` when `P` is a data property;
- every class-level fact `→ C(x)` becomes `→ C(x) ∨ D(x)`, i.e.
  `¬D ⊑ C`: `owl:Thing` is `¬D`. A clause whose body consists only of
  polymorphic or data-sorted concepts and whose head is object-sorted is
  treated the same way: the normaliser writes `⊤ ⊑ ∀p.R` of a
  `DataPropertyRange` as `Q_⊤(x) → Q(x)` once `⊤` has a definer, and
  `Q_⊤` also holds on data values (it is the `rdfs:Literal` filler of an
  unqualified data cardinality), so the clause is a `⊤ ⊑ C` fact in
  disguise.

Sorts are inferred from the clause set: data ranges and the source's data
properties are data, source classes and named individuals are objects, and
the atoms on one term of one clause share a sort. A definer that appears in
both sorts (the `⊤` definer shared by `≥1 p` and `≥1 r`) gets no sort clause
and keeps its facts. A fact is class-level when every concept in its head is
object-sorted; a data-range-level fact, the excluded middle
`→ Q(x) ∨ R(x)` of a `DataComplementOf` definer `Q`, stays as it is, and so
does every ground fact.

Admissibility closure. Sort inference alone is not enough: it joins sorts
only on shared terms and never follows an implication from a data- or
both-sorted concept into an object-sorted one. In ore_ont_14321, 13132 and
6951, `≥1 d` reifies `⊤` as `Q_1`, whose only structural evidence is the
data successor, and `DataPropertyRange(e R)` is clausified as
`Q_1(x) → Q_7(x)`, `Q_7(x) ∧ e(x,y) → R(y)`. Inference gave `Q_1` data and
`Q_7` object, so `Q_7 ⊑ ¬D` together with the unrelativized fact `→ Q_1(x)`
made every data node inconsistent and every `≥1 d` unsatisfiable. Two rules
now prevent that. First, a clause whose body consists only of polymorphic or
data-sorted concepts on its single variable and whose head is object-sorted
is relativized like a `⊤` fact (`Q_1(x) → Q_7(x) ∨ D(x)`): it is a `⊤ ⊑ C`
axiom written through the shared `⊤` definer. Second, before any sort clause
is emitted, admissibility is closed under the clause set as a least
fixpoint: whenever the body of a clause admits a sort at a term and no head
atom on that term admits it, the head definers (or, when the head has none,
its internal role positions) are made to admit it. A definer or internal
role position that admits both sorts at the fixpoint gets no sort clause;
the encoding never guesses. Fixed sorts never widen (next paragraph). The
closure guarantees that every sort clause is
consistent with every clause of `S'` read in the two-sorted model of the
first direction below.

Fixed sorts. Some sorts are given by OWL 2 Direct Semantics and are never
widened by the closure: every named individual is an object (the frontend
pins each individual `a` that no object-only ground atom or source-property
assertion already pins: through its nominal proxy `p` when it has one
(`→ p(a)` and `p ⊓ D ⊑ ⊥`; the typed native ABox view represents `→ p(a)`
as the proxy of `a`, so HT-based consumers read it exactly), and otherwise
through a fresh object marker `O` (`→ O(a)`, `O ⊓ D ⊑ ⊥`). The ground form
`D(a) → ⊥` is avoided because the nominal CB engine mishandles an
empty-head clause whose only body atom is ground), every source class is
`⊑ ¬D` (also when no clause mentions it), every source property has an
object domain, a data property a data range and an object property an
object range, and every data range is `⊑ D`, complement ranges included
(`¬R` is `Δ_D \ R`). Only internal definers and internal roles widen.
Where the body of a clause admits a sort at a term `t` and the head offers
only fixed sorts on `t` that do not admit it, the clause is relativized:
for the data sort, `D(t)` joins the head (the clause holds for objects at
`t`); for the object sort, `D(t)` joins the body (it holds for data
elements). Both directions survive. A two-sorted model of `O` satisfies the
relativized clause: on the sort the clause was restricted to it holds as
before, and on the other sort `D(t)` (respectively `¬D(t)`) makes it true.
A model of the encoding restricted to `¬D`, with data values in `D`,
satisfies the source clause, because the source clause only ever meant the
restricted sort at `t`: a fixed-sort head on `t` is a class, a property
position or a data range, which is empty in the other sort under Direct
Semantics, so applying the clause there could only have required an
element of the wrong sort. In particular the excluded middle of a data
range becomes `D(x) → R(x) ∨ ¬R(x)`; on objects it is vacuous, and on data
elements it is the complement relative to `Δ_D`. The first version of the
closure (e054f6b7) instead widened fixed concepts and dropped their sort
clauses; with `⊤ ⊑ ≤2 u` and three `u`-values on an individual without a
proxy, nothing then kept the individual out of `D`, and the restriction
never applied.

Exactness. Let `O` be the source ontology, `S` its one-sorted clause set
before this pass, and `S'` the result. `S` is read against the two-sorted
semantics as in the rest of the frontend; the claim is that `S'` has the
same entailments over the source signature as `O`.

- A two-sorted model `I` of `O` yields a model of `S'`: take the one domain
  `Δ_I ⊎ Δ_D`, interpret `D` as `Δ_D`, and keep every other symbol. Data
  ranges lie in `Δ_D`, class expressions and named individuals in `Δ_I`,
  property domains in `Δ_I`, object ranges in `Δ_I` and data ranges in `Δ_D`,
  so every sort clause holds. A class-level fact `⊤ ⊑ C` of `O` holds on
  `Δ_I = ¬D`, so `→ C(x) ∨ D(x)` holds everywhere. A data-range-level fact
  `→ Q(x) ∨ R(x)` with `Q` the definer of `Δ_D \ R` holds on `Δ_D`; on
  `Δ_I` interpret `Q` as true, which satisfies `Q ∧ R → ⊥` there since `R`
  is empty on `Δ_I`, and `Q` occurs nowhere else than in such definer
  clauses and as a data-property filler, whose instances are in `Δ_D`.
- A model `J` of `S'` yields a two-sorted model of `O`: let
  `Δ_I = Δ_J \ D^J` and `Δ_D = D^J` (extended by the standard value space of
  the datatype map, on which no `__dt__` concept of `S'` is forced). Every
  source class is a subset of `Δ_I` by `A ⊑ ¬D`, every data range a subset
  of `Δ_D` by `R ⊑ D`, every property respects its sorts by the domain and
  range clauses, and every named individual is in `Δ_I` by
  `__nom__o ⊑ ¬D`. A source axiom other than a `⊤` fact is a clause with a
  body that pins its central element to a class, a property, or a nominal,
  so it is evaluated on `Δ_I` exactly as `S` evaluates it; a class-level
  `⊤ ⊑ C` holds on `¬D = Δ_I` by its relativized clause; a
  data-range-level fact holds on `Δ_D` because it was not relativized. The
  restriction of `J` to `Δ_I` therefore satisfies `O` under Direct
  Semantics, with the data values of `J` as its data interpretation.

Data-range-level facts are restricted to the data sort, never to the
object sort: relativizing them to `¬D` would be incomplete, since a data
node reached by a data property is in `D` and would lose the excluded
middle (`A ⊑ (u value 2)` and `C ≡ ¬∀u.{1}` entail `A ⊑ C`, which needs
`¬{1}` at the value `2`). The body guard `D(x)` keeps them on every data
node, where they belong.

Why the sorts alone stop the divergence: every ground object term carries
an object-sorted concept (a `__nom__` proxy, a source class, or an
object-sorted definer through its Skolem function), so `¬D` holds at it,
while `v ⊑ D`. The excluded middle `→ Q(x) ∨ v(x)` therefore collapses to
the unit `Q(t)` at every object term, `v` is never derived there, and the
at-most-one clause only ever matches data-sorted terms, the data successors
of the same element; no merge between object terms is ever proposed.

### Data successors without data values (m2197)

Bug. With `⊤ ⊑ ≥2 u` (`u` a data property) and `⊤ ⊑ {a}`, every nominal
route (`nominals`, `certified_nominals`, `ht_general`, `auto`) answered
"inconsistent"; HermiT answers "consistent", and one object `a` with two
distinct `u`-values is a model. The parser reads the unqualified data
filler `rdfs:Literal` as `⊤`, and the normaliser reifies it as the same
definer `Q_0` as `owl:Thing`, so the clause set is `→ Q_0(x)`,
`Q_0(x) → Q_1(x)`, `Q_1(x) → u(x, f_i(x)) ∧ Q_0(f_i(x))` for `i = 0, 1`,
`Q_1(x) ∧ f_0(x) ≈ f_1(x) → ⊥`, `Q_0(x) → __nom__a(x)` and
`__nom__a(x) → x ≈ a`. Read one-sorted, `⊤ ⊑ {a}` holds on both
`u`-successors, merges each with `a` and so with each other, and clashes
with their inequality. One-sorted reading is not a weakening of the
ontology here: it is strictly stronger, so even an "inconsistent" answer
from a route that otherwise drops nominals is wrong. The two-sorted
encoding above handles exactly this shape (`Q_0` is polymorphic, its
object-sorted implications are relativized), but it was gated on a data
value (`__dt__val__`) being present, and the input has no literal.

Fix (nominal CB route). `sorts::applies` replaces `has_data_values` as the
gate in `frontend/mod.rs`: under nominal clausification with nominals or
individuals, the encoding runs when the clause set carries a data value,
a data range (`__dt__` concept), or an atom of a source data property. On
m2197 it rewrites `Q_0(x) → __nom__a(x)` to `Q_0(x) → __nom__a(x) ∨ D(x)`
and `Q_0(x) → Q_1(x)` to `Q_0(x) → Q_1(x) ∨ D(x)`, and adds
`u(x, y) → D(y)` and `__nom__a ⊓ D ⊑ ⊥`; both successors are in `D`, the
nominal fact does not apply to them, and the inequality is satisfied.

Soundness and exactness. The exactness argument above never uses a data
value: it only needs that data ranges lie in `Δ_D`, source classes, nominal
proxies and property domains in `Δ_I`, and data-property ranges in `Δ_D`.
Those clauses are added whenever the gate opens, so the widened gate keeps
both directions of the argument. A clause set with no data property, no
data range and no data value has no element that the source semantics puts
in `Δ_D`, so the gate stays closed there and the clause output is
unchanged; in particular `⊤ ⊑ ≥2 r` with `⊤ ⊑ {a}` for an object property
`r` stays inconsistent. Inputs outside nominal clausification are
unaffected, as before. Regression tests:
`engine/tests/top_nominal_data_successors.rs` (fixtures in
`engine/tests/fixtures/top_nominal_data/`) and the unit test
`top_nominal_with_unvalued_data_cardinality_is_relativized` in
`frontend/sorts.rs`.

The HT consumers. Two consumers never see the sorted clause stream:

- the native completion bridge (`ht_bridge`, the HT arm of
  `certified_nominals`, and the route `auto` picks for these inputs)
  rebuilds class axioms from `source_axioms` in source mode, where
  `DataMinCardinality(2 u)` is `AtLeast(2, u, Top)`. Its datatype gate
  (`exact_atomic_datatype_bridge_fragment`, which checks every
  non-datatype axiom on a blank data node) only ran when a `__dt__`
  concept occurred, so a data property used only with `rdfs:Literal`
  fillers was invisible to it and the bridge answered "inconsistent";
- `ht_general` runs without `KM_NOMINALS`, so the sort pass never runs and
  the clausal hypertableau reads the data successors as objects (also with
  a qualified filler, `⊤ ⊑ ≥2 u.xsd:string`).

The clausal hypertableau itself is exact on the sorted clause set (the
`km tableau` worker answers "consistent" on the sorted m2197 input), so
both gaps are admission questions, not calculus defects. They are closed
as follows.

- Bridge. When the source has individuals or nominals, the frontend
  reports the data properties its clause set uses
  (`FrontendResult::data_roles`, carried in the clause file as
  `data_roles`), and every converted HT input records them as
  `TInput::data_roles` (`cb_to_ht::attach_data_roles`). The bridge's two
  datatype admissions (`exact_atomic_datatype_bridge_fragment` and
  `datatype_effects_covered_by_unit_bottom`) now run when either a
  `__dt__` concept or a data role occurs, and both treat the data roles as
  data roles. `⊤ ⊑ {a}` fails on a blank data node, so the bridge defers
  on m2197 and every probe; `auto` then answers on `certified_nominals`
  (the sorted CB arm). The change only adds defers, so it cannot make the
  bridge publish a verdict it did not publish before. Cost: an input whose
  `⊤` axioms a blank data node cannot satisfy (for example `⊤ ⊑ ≥2 u` with
  `A(a)`) now leaves the bridge for the nominal CB route.
- One-sorted routes. Outside nominal clausification the frontend sets
  `one_sorted_data_successors` when the source has a TBox nominal and
  `sorts::applies` holds for the clause set, except for the
  bridge-exclusive worker (`KM_HT_ONLY=bridge`), which defers by itself.
  On a forced route the orchestrator then publishes neither verdict: the
  one-sorted stream is stronger than the ontology, so the rule "an
  inconsistency found on a weakened input is still exact"
  (docs/ROUTING.md, "Forced routes") does not apply. `km classify` exits
  3; with `KM_ALLOW_APPROXIMATE=1` the answer carries `APPROXIMATE`.
  Automatic routing keeps nominal inputs on mechanisms that carry
  `KM_NOMINALS` or the typed bridge payload, except for the rule checker
  below, which is why the flag is also computed there.
  Individuals alone (an ABox without TBox nominals) do not set it: given a
  two-sorted model, give every data element the labels of an unravelled
  copy of some object (plus its data ranges) with fresh copies of that
  object's successors and predecessors. The copies are anonymous, at-most
  restrictions count the same number of copies as originals, and only a
  nominal concept could force a copy onto a named element, so the
  one-sorted stream has a model whenever the ontology has one.

- DL-safe rules. A unary or constant-data rule is lowered and its run sets
  `KM_NOMINALS`, so it sees the sorted stream. A binary rule is not
  lowered: the automatic route sends it to `ht_rules`, whose rule
  consistency checker (`orchestrate::rules_consistency`, a clausal
  hypertableau that reads `__nom__` proxies as nominals) ran on the
  one-sorted stream and published "inconsistent" for `⊤ ⊑ ≥2 u`,
  `⊤ ⊑ {a}`, `r(a,a)` and `r(x,y) → B(x)` (HermiT: consistent; also with
  `{a, b}` and `≥3 u`). The frontend now sets `one_sorted_data_successors`
  under automatic routing too, and the orchestrator does not publish an
  inconsistency of either rule checker on such a stream. The taxonomy run
  after the checker does not apply the rules, so it cannot settle the
  question: the input fails closed (exit 3) on every route that reaches the
  checker. A consistent checker verdict stays sound, since the one-sorted
  stream is stronger than the ontology. HasKey over a data property and
  rules with data atoms already fail closed before the checker. Probes:
  `rule_*.ofn` in `engine/tests/fixtures/top_nominal_data/`, test
  `rule_checker_does_not_publish_a_one_sorted_inconsistency`.

Tests: `hermit_answers_on_every_route` and
`forced_one_sorted_route_refuses_both_verdicts` in
`engine/tests/top_nominal_data_successors.rs`, and
`data_roles_without_datatypes_enter_the_datatype_gate` in
`konclude_ht/bridge.rs`.

### Inert object sorts in the rule checker (2026-10-30)

Cost. ore_ont_7278 and ore_ont_3726 took about 7 s in v1.5.3 and 32 s in
v1.5.4 on the automatic route. Their DL-safe rules compare data values, so
the frontend grounds them over the asserted literals (`lower_finite_rules`,
which also carries every data assertion as `a : ∃p.{v}`), the run sets
`KM_NOMINALS`, and this section's sort encoding applies; v1.5.3 had no sort
encoding. The rule-consistency worker (`orchestrate::rules_consistency`,
the clausal `Tableau`) then reads 478 more clauses (8,552 instead of
8,074), and 11 of the clauses it reads are relativized range facts
`Q_⊤(x) → Q(x) ∨ D(x)` of `DataPropertyRange` definers `Q`. The worker
branches on each of them at each of the 221 ABox nodes, and every branch
restarts the Horn saturation over the whole graph (`KM_TAB_STATS=1`: 2,431
branch points and 2,433 saturations instead of 2 saturations, no
backtracking). The worker took 25 s instead of 4 s on the same machine.
Removing the 11 `D` disjuncts and the 11 sort clauses `Q ∧ D → ⊥` from the
captured worker input, and nothing else, restores 4.3 s; removing the 340
concept sort clauses or the 56 role sort clauses instead leaves it at 26 to
27 s.

Remedy (`orchestrate/inert_sorts.rs`). Before conversion, the rule
checker releases the object sort of every definer `Q` that no clause reads
on a data element. A guard of a term `t` in a clause body is an atom false
at every data element in every model: an object-sorted concept with its
sort clause (not itself released), or a role atom whose domain or range
position at `t` has its sort clause; an individual is pinned when a unit
fact with such an atom puts it outside `D`. `Q` is released when it is an
internal definer (no IRI, not a query, not used by a rule, a cardinality
or a definer record), every clause with `Q(t)` in its body has a guard of
`t` or a pinned `t`, and every clause with `Q(t)` in its head has `D(t)` in
its head too or a guard or a pinned `t`. For released definers the pass
drops the `D` disjunct of their facts and their sort clauses; the guard
sort clauses stay. A model of the sorted clause set becomes a model of the
result by adding `Q` to every data element (every reading of `Q` is
guarded, so no clause fires there), and a model of the result becomes a
model of the sorted set by removing `Q` from every data element (every
unrelativized derivation of `Q` is guarded, and the relativized ones hold
through `D`). The two sets have the same models up to internal definers on
data elements, so the worker's consistency verdict, the only thing it
reports, is the same; the worker is sound on both inputs, so a difference
could only be a timeout or an error, never the opposite verdict. On 7278
and 3726 all 11 range definers are released and the worker runs in 4.2 s;
the classification is byte-identical to v1.5.4. `KM_RULES_KEEP_INERT_SORTS=1`
keeps the sorts. Frontend output, routing and every other consumer of the
sorted stream are unchanged.

Tests: the unit tests of `orchestrate/inert_sorts.rs`, among them a
randomized check over 3,000 sorted clause sets that the release keeps
satisfiability (decided by ground DPLL) and that releasing without the
guard conditions changes it on some of them, and
`unchecked_release_turns_a_consistent_input_inconsistent`, where
`Q_1(x) → A(x)` reads the definer on a data value. Measurements, the
differential over finite-rule seeds and the timing table:
`results/agents/2026-10-30/rules-worker-cost/`.

Lean coverage (2026-10-30). `lean/ContextCalculus/RulesInertSortRelease.lean`
formalises the worker's clause language (concept, role and equality atoms
over variables, individual and auxiliary constants and unary Skolem
functions, read as first-order clauses over a nonempty domain), the release
exactly as `release_inert_object_sorts` computes it (`conceptSortOf`,
`roleSortOf`, `removedSortClause`, `dropData`, `release`), and the guard
conditions as an executable check (`guards`, `guarded`, `bodyOk` for (B),
`headOk` for (H), `conditions`, which also requires `D ∉ P` and that no
released concept is reserved). Proved, with no `sorry` and only `propext`,
`Classical.choice` and `Quot.sound`:

- `extend_models`: a model of the sorted set, with every released definer
  added on every `D` element, is a model of the released set;
- `restrict_models`: a model of the released set, with every released
  definer removed from every `D` element, is a model of the sorted set;
- `release_equisatisfiable`: if `conditions` accepts, the two sets are
  satisfiable together with any side theory that reads only the reserved
  concepts (`ReadsOnly`: it cannot tell apart two interpretations that agree
  on the domain, roles, constants, functions and reserved concepts), in both
  directions, so the consistent and the inconsistent verdict are both
  preserved;
- `WireInertSortRelease.check_sound`: an accepted certificate's worker input
  (`result`) is equisatisfiable with its sorted clause set (`original`) in
  that sense.

The released set and the guards are not trusted: the checker recomputes the
guard tables from `original` and requires `result` to equal
`release original` exactly. `KM_RULES_INERT_CERT=<file.json | dir>` makes the
orchestrator write the certificate (original clauses, released definers,
reserved concepts, worker clauses, name tables); with
`KM_RULES_INERT_LEAN_CHECKER` naming `rules-inert-sort-release-check` the run
fails closed when Lean rejects it. The reserved set is every concept that
something other than the clauses reads: cardinality and definer records, rule
atoms, source axioms, and every name that is not a clausifier definer
(`Q_`, `aux_`, `def_`), which covers source names, queries, built-in
vocabulary, `__nom__` proxies, `__dt__` ranges and `D`.

This is the first machine check on the rules-consistency route: the
tableau refuses HT Lean certification under `KM_RULES_CONSISTENCY`, and the
orchestrator's `consistency_certified` flag is not a Lean check. Both maps in
the theorem leave every symbol outside `P` unchanged, so the reduct of a model
to the source symbols is preserved as well, which is what the source checks
of the `require_source_model` path read (IRI-mapped names, `__nom__`
proxies, `__dt__` labels; released definers have no IRI). The theorem does not
need the sort clause of a released definer to be present, and the clause
language has no negated concept atoms or existential fillers, so a released
definer occurs only as a positive concept atom by construction.

Argued, not proved: (1) that the worker's side channels (rules, cardinality
and definer records, datatype and nominal semantics, and the source-model
check of the `require_source_model` path) read only the reserved concepts,
which is the `ReadsOnly` premise; (2) that `cb_to_ht::convert` and the
clausal `Tableau` decide satisfiability of the clauses they are given (the
theorem is about the clause sets, and the same worker reads both); (3) the
translation of `JTerm::Aux` terms to constants. Gate:
`lean/run-rules-certification-gate.sh` (fixture
`engine/tests/fixtures/rules_inert_sorts/fr373.ofn`, ore_ont_7278, the
randomized release test with the Lean checker on every certificate, and a
forged fixture). Results: `results/agents/2026-10-30/lean-v155-coverage/`.

The duplicated frontend pass. On these inputs the frontend also runs twice
(about 2.8 s each, nearly all of it in the finite-rule grounding): the first
pass reports the 81 data assertions as not carried, because only the
parse-time conversion counts as carrying them, and
`run_ofn_split_cached` reruns it with `KM_DATA_ASSERTION_AS_CLASS`. The
grounding already carries them, and the two clause streams are identical
(8,552 clauses in the same order; only the `nominal_abox` diagnostics
differ). Skipping the second pass would need a proof that the first pass
then equals the converted one on every input, including every consumer
that reads the ontology between parsing and the grounding
(`abox_consistency`, `data_abox`, the ABox probes); that proof is not done,
so both passes stay. (Superseded for the cost by the closure memo below,
2026-10-30: the second pass stays and reuses the first pass's closure.)

### Rule checker follow-ups (2026-10-30)

Three findings of the exactness review of the inert-sort release
(`results/agents/2026-10-30/rules-route-followups/`).

**Worker failures that depended on machine load.** Under parallel load the
rule checker worker sometimes exited 1 about 0.01 s after it started, and
`rules_consistency` turned that into a classification error. Cause: the
worker ran its search on a 2 GiB thread and the rule checker on a nested
4 GiB thread (`stack_size(4 << 30)`, on the assumption that an untouched
stack costs nothing). On `ws` the kernel uses strict overcommit
(`vm.overcommit_memory = 2`, commit limit 264 GiB), so a thread stack is
charged in full when the thread starts; with other processes holding most
of the limit, `pthread_create` failed with `EAGAIN` and the worker printed
`tableau error: Resource temporarily unavailable (os error 11)` to a stderr
the orchestrator discarded. The same message appears deterministically
under `ulimit -v 5000000`. Remedy (`engine/src/bigstack.rs`): the main
thread's stack is the one mapping Linux commits page by page as it grows.
`km tableau` raises its soft `RLIMIT_STACK` to the deep-stack size plus
headroom and re-executes itself once, so `execve` reserves the larger gap
below the stack (address space only, no commit charge); the searches then
run inline on the main thread (`bigstack::run` checks the stack left below
the caller). A thread is spawned only when the current thread lacks the
requested stack (a library caller, the incremental probe), and a failed
spawn is retried for about 5 s before the error, with the stack size and
the operating system's reason, is returned. The HT worker pools, which run
in parallel and cannot share a stack, retry their spawns the same way
(`bigstack::spawn_scoped_retrying`). The orchestrator now keeps the
worker's stderr and includes its tail in the error. Exactness: the search
code is unchanged; only the stack it runs on and the time its pages are
charged change, so every verdict is the one the old worker computed when
its threads started. The worker now commits stack only for the depth a
search reaches; a failure that remains is one the input causes (an actual
stack or heap demand above the limit), and it reports its reason.

**The incremental rule adapter.** `incremental_rules::rules_consistent`
now applies the same release (`inert_sorts::release_inert_object_sorts_in`,
same source-name test, same `KM_RULES_KEEP_INERT_SORTS` switch), with the
batch exactness argument. The adapter is reached only when the session's
frontend carries every data assertion (`retained_backend_allowed`); on
ore_ont_7278 under default settings the frontend reports the 81 assertions
as uncarried, so every revision is an exact batch rebuild that already ran
the release. With `KM_DATA_ASSERTION_AS_CLASS=1` the adapter is used, and
the probe then releases the same 11 definers as the batch checker. The
probe still did not finish on 7278 with or without the release (stopped
after 28 and 21 minutes): the batch checker runs 7278 with
`KM_RULE_JOIN_ORDER=1` (its source-model mode), the incremental probe
without it, and on the batch checker's captured worker input the worker
takes 8 s with that setting and more than 100 s without it. Making the
probe use the selective join order is a separate change (a scheduling
change of the clause matcher, not made here).

**The second frontend pass.** The 2.8 s per pass is the positive-ABox
closure `rule_assertions::materialize`, which runs when the finite-rule
grounding fires; the grounding itself takes 0.2 s (`KM_TIMING frontend
finite-rule grounding` and `rule-assertion closure` lines). The second pass
cannot be skipped by a condition on the first pass's output without the
audit above: the parse-time conversion makes the converted assertions
visible to every consumer between parsing and the grounding, and on 7278
the passes already differ in `nominal_abox` (the unsupported-axiom reasons
and the `ClassAssertion` coverage counts), which the bridge routes and the
uncarried count read. Instead, `frontend::pass_cache` keeps the first
pass's closure for the duration of `run_ofn_split_cached`, and the second
pass reuses it when its closure input is equal. Exactness: `close` reads
only the asserted concept facts, role facts, class inclusions and positive
rules, compared as sets. Each round evaluates every inclusion and every
rule against the facts present at the start of the round and adds its
conclusions to sets, so the order and repetition of inclusions and rules
do not change a round; a rule's join order depends on its body order and
index sizes, and both resource bounds count bindings or facts, which the
order of index entries does not change. Equal inputs therefore have equal
closures, and the second pass receives exactly the closure it would
compute. On 7278 the second pass drops from about 2.8 s to 0.2 s (memo
hit). `KM_NO_FRONTEND_PASS_CACHE=1` disables the memo.

Lean obligations. None of the three changes alters a calculus, an encoding
or a worker input: the stack change is below the search, the incremental
release reuses the batch release (whose obligation, the equisatisfiability
argument of the previous subsection, is unchanged and not mechanised), and
the closure memo returns a value equal to the one the frontend computes.
Nothing was proved in Lean.

### Inert object sorts in the nominal CB input (2026-10-30)

Cost. On the generated nominal-plus-data seeds (`gen_nomdata.py
--no-inverse`, seeds 2000-2399) 130 of 400 runs of the automatic route gave
no answer within 60 s at the base of v1.5.5 (87fda54f). Every one of them
ran the nominal CB route alone: the native bridge defers on its datatype
gate (ten distinct reasons, `results/agents/2026-10-30/nominal-coverage/`).
Reducing seed 2032 axiom by axiom while the automatic route stays above 15 s
leaves three axioms (`tests/fixtures/nominal_inert_sorts/m2032_min.ofn`):

    DataPropertyDomain(:u DataSomeValuesFrom(:u xsd:string))
    EquivalentClasses(:Q1 ObjectComplementOf(ObjectSomeValuesFrom(:r ObjectHasValue(:r :c))))
    EquivalentClasses(:Q2 ObjectComplementOf(ObjectSomeValuesFrom(:r :C)))

The sort encoding turns each complement into a relativized fact such as
`→ Q_4(x) ∨ Q_6(x) ∨ D(x)` (`D` = `__data__`). The ground context
instantiates those facts at the nominal `c` and at every Skolem successor
of it, so each case split carries the `D` disjunct, and the engine does not
finish within 30 s in any ordering regime (context, base context, plain
Sequoia; `km engine`, one thread). Three of its definers are never read on
a data element.

Remedy (`inert_sorts::release_inert_object_sorts_for_cb`,
`orchestrate::nominal_cb_clause_input`). In nominal mode the orchestrator
gives the CB engine a copy of the clause file in which the object sort of
every inert definer is released, the pass of the rule checker (section
above) with two differences:

- Records do not reserve names. The CB engine builds its `Reasoner` from
  `input.clauses` alone, so a cardinality or definer record has no
  meaning there. The names it reads with a meaning of their own are the
  source names (`iri_map`, `named`), the asserted markers, the queries of
  `KM_QUERIES`, the nominal proxies and the nominal-ABox assertion markers;
  all of them stay reserved. Rule atoms stay reserved.
- The fixpoint keeps one of two mutual guards. The complementary markers
  of `≤1 p` and `≥2 p` share `Q_3 ∧ Q_4 → ⊥`; each is the other's only
  guard there, so the rule checker's pass keeps both. A failure is *soft*
  when the failing clause's body holds another candidate on the same term
  that has a sort clause, and *hard* otherwise. Hard failures are kept at
  once; when only soft failures remain, the greatest of them is kept and
  the rest are re-checked. The loop ends only when no candidate violates
  (B) or (H).

Exactness. The final set `P` satisfies (B) and (H), so the model
correspondence of the module documentation holds: a model of the sorted
clause set `S` becomes a model of the released set `S'` by adding every
`Q ∈ P` to every data element, and a model of `S'` becomes a model of `S`
by removing them. Neither map changes the interpretation of any name
outside `P`, of any role, of equality, or of the individuals. Every answer
the orchestrator reads from the CB engine (consistency, and the
superclasses and unsatisfiability of source names, asserted markers and
queries) mentions only names outside `P`, so it is the same for `S` and
`S'`: `S ⊨ A ⊑ B` iff `S' ⊨ A ⊑ B` for `A, B ∉ P`, because a countermodel
of one maps to a countermodel of the other with the same extensions of `A`
and `B`. The CB engine is complete for `S'` to the same standard as for
`S` (the copy only drops literals and clauses; the regime, R2's switch and
R3 are computed from it as from any other clause set), so its answers on
`S'` are the exact answers for the source. HT workers, which read the
cardinality and definer records, keep the frontend's file; the EL
certificate racer gets the copy only when it does not run. Runs that must
publish a CB Lean certificate (`KM_CB_LEAN_REQUIRED`, or a clause file with
`cb_typed_source`) keep the frontend's file, since the certificate's typed
source must equal the clauses. `KM_CB_KEEP_INERT_SORTS=1` opts out.

Lean obligation. Not discharged. What has to be proved is the ground
form of the correspondence: for a finite set of function-free clauses
over a signature with the sort predicate `D`, and a set `P` of predicates
satisfying (B) and (H), `S` and `S'` have the same Herbrand models up to
`P` on the atoms `D(t)` is true for, hence the same entailed ground
clauses over the predicates outside `P`. The CB obligation then reduces to
the existing ones (first-order lifting of the context calculus, open as
before; docs/CERTIFICATION-ROADMAP.md). The unit tests check the ground
form on random clause sets by DPLL (2,000 sets, consistency and
satisfiability and subsumption of the source classes with a fresh
individual), the rule checker's pass already on 3,000; that is evidence,
not a proof. A parallel review of the rule checker's pass in
`inert_sorts.rs` was still open on 2026-10-30. This variant reuses that
pass's sort-clause recognition, guards and (B)/(H) checks unchanged; the
reservations, the maximal fixpoint and the elimination below are new and
outside that review.

Second pass: universal definers (`inert_sorts::eliminate_universal_definers`).
After the release, a released definer `Q` whose relativized fact was
`→ Q(x) ∨ D(x)` has the unit fact `→ Q(x)`; so has the `⊤` definer of an
unqualified cardinality. Every model interprets such a `Q` as the whole
domain, so each body atom `Q(t)` is true and each clause with `Q(t)` in its
head is true. The pass drops both (the unit fact included) for every
internal definer with a unit fact, except the reserved names above, and
except a definer whose elimination would leave a clause with an empty body
and a role atom, an equality or a function term in its head (a shape the
frontend never emits; the definer is then kept unchanged). Exactness: a
model of the input satisfies the result, because every dropped body atom
was true; a model of the result becomes a model of the input by
interpreting each eliminated definer as the whole domain. No other name
changes its interpretation, so the CB engine's answers on every name that
is not eliminated, the reserved ones included, are the same. (Proved in
Lean on 2026-10-31; see "Lean coverage of the nominal CB input" below.) Clause sets with an inverse role (an `__inv__` role atom or an `inverse`
RBox row) are left unchanged by this pass: on
`tests/fixtures/top_nominal_data/probe_v7.ofn` (`⊤ ⊑ ≥2 u`, `⊤ ⊑ ∃r.{a}`,
`{a} ⊑ ≤1 r⁻`) dropping the `⊤` filler from the inverse at-most clause took
the CB engine from 0.06 s past 150 s, an exact answer reached far later
(nominals, inverse roles and number restrictions together are where the
Nom rule fires). The guard is about cost only. The Lean obligation is the ground form of that statement
(not discharged; the unit tests check it on 2,000 random clause sets by
DPLL, after the release).

On ore_ont_9800 the ground context held 250,295 clauses at work-off
iteration 250,000, 228,266 of them the 38 relativized facts
`→ D(a) ∨ Q_k(a)` instantiated at its individuals and 6,039 more the `⊤`
definer `Q_116`. The release turns the 38 facts into unit facts and the
elimination removes all 39 definers.

Where the copy is made. The orchestrator makes the copy inside each CB arm
when it starts (`with_nominal_cb_input`: the portfolio's CB arms and the
atomic CB worker of the `nominals` route), so a schedule that answers without
the CB engine (the sequential bridge of a large typed ABox, ORE 10621 and
11270) never pays for it, and in a race the HT worker starts at once. A byte
scan for the sort marker or a body-free fact on a `Q_` definer skips the
parse on every other clause file. If the copy cannot be made the arm runs on
the frontend's file.

Measurements (`results/agents/2026-10-30/nominal-coverage/`):

- ORE 9800 on the benchmark nodes (IBEX, one core, 240 s, the protocol's
  flags, 4 runs each): v1.5.4 design-run-9 binary 2 of 4 answered (184 s),
  87fda54f 1 of 4 (191 s), the merged base e1881695 (R2/R3 fix of
  7c238e52 included) 2 of 4 (205 s); this branch on that base 4 of 4 in
  14.1 to 14.2 s (13.8 to 17.3 s before the merge); the CB engine answers
  6 s after the race starts instead of about 180 s. 10874: 3.3 to 4.8 s on
  the merged base, 0.56 to 0.59 s with this branch. Both outputs are identical to those
  of the design-run-9 binary, whose 9800 answer the paired run verified
  against Konclude, HermiT and Openllet (10874 publishes its 879
  data-property assertions as dropped, so the protocol does not compare
  it). `km engine` on 9800's CB input, one thread, same load: 190.7 s user
  as emitted, 170.9 s with the release only, 39.5 s with the elimination of
  the `⊤` definer only, 3.4 s with both; the named subsumptions (10,413)
  are identical in all four.
- Generated seeds against the merged base (e1881695 against this branch
  merged onto it, both built on IBEX, run side by side on the shared
  workstation; 400 seeds, automatic route, 60 s, 3 workers each): 270
  answered before and 276 after, no wrong answer in either run; six gained
  (`m2032` 1.1 s, `m2058` 5.2 s, `m2131` 1.0 s, `m2173` 32 s, `m2319` 48 s,
  `m2342` 52 s), none lost; 124 timeouts remain. Rerun once on this branch
  merged with the head that carries the native data values and the revert
  of 0188fcc7 (3ae4185d; merge a814967e), same protocol: 275 answered, 125
  timeouts, no wrong answer; against the merged-base run five more answers
  (`m2032`, `m2058`, `m2131`, `m2173`, `m2177`), and `m2319` and `m2342`
  (48 s and 52 s before) at the cap. None of the 125 takes the native bridge:
  124 still defer at its datatype gate with the same ten reasons
  (`seeds-reverted-head-timeouts-bridge-defer.tsv`), and `m2296` defers at
  the ABox conversion (object property assertion count mismatch). The CB
  release now emits the rule checker's Lean certificate
  (`WireInertSortRelease`, KM_RULES_INERT_CERT) with the CB reservations
  (`reserved_concepts_for_cb`) for the clause set after the release and
  before the universal-definer elimination, which has no Lean check; the
  checker `rules-inert-sort-release-check` accepts it on the test fixtures
  (`cb_release_certificate_is_accepted_by_the_lean_checker`). A rejected
  certificate keeps the frontend's clause file for the CB arm. Earlier, before the merge
  (87fda54f against `km.fix`): 270 answered before, 271 after, no wrong
  answer either time. Five files gained an answer (`m2032`, `m2058`, `m2131`, `m2173`,
  `m2336`) and four lost one in that run (`m2059`, `m2185`: a worker
  aborted on an allocation failure under the host's strict overcommit and
  both answer in 0.05 s on rerun; `m2079`, `m2359`: 58 s and 45 s before,
  within load noise of the cap). Rerun twice with each binary, the nine
  files give: `km.base` answers `m2059`, `m2185` (both runs) and `m2359`
  (one run, 41 s); the final build answers `m2032`, `m2058`, `m2131`,
  `m2173`, `m2336`, `m2059`, `m2185` and `m2359` in both runs (`m2173` in
  47 and 59 s); `m2079` times out with both. So five seeds gain an answer
  and none loses one; 125 of the 130 timeouts remain.
- ORE inputs with individuals in the design half (353, the 201 gated and
  425 individual-bearing lists of `results/agents/2026-10-29/per-context-order/`
  intersected with `split.json`), 240 s, the v1.5.4 release binary
  (`.work/pgo-v154/km-pgo-use`) against this branch, two streams side by
  side on the shared workstation: 345 answered by both with identical
  SUB/UNSAT/CONSISTENT lines, 8 answered by neither, none lost or gained
  except 9800 (236 s before, 19 s after); the copy was made on 38 inputs
  (pre-merge build `km.fix`, which made the copy before the race).
- The same 353 inputs on IBEX against the merged base, paired (each input
  runs both binaries in one one-core task, order alternating; 240 s,
  protocol flags): 343 answered by both with identical lines, 9 by neither,
  9800 gained (240 s to 17.3 s), none lost or changed. Sums over the inputs
  both answer: 902.3 s base, 900.6 s with this branch; over the 20 of them
  where the copy was made: 52.2 s and 41.6 s; no input is more than 1.5
  times and 5 s slower. (The 9 timeouts of both, among them 16666 and 2792
  that the bridge answered in about 100 s in the v1.5.4 design run, are the
  same in both columns.)

What remains. Of the 130 seed timeouts, 124 still time out on the merged base. The copy is made
on most of them, but what remains is the case analysis of the nominal ground
context, not the sort disjunct: seed 2000 reduced while the CB engine stays
above 10 s even with every `D` disjunct dropped (an unsound diagnostic, used
only to locate the cost) leaves two axioms,

    SubClassOf(DataMaxCardinality(1 :u) ObjectHasValue(:s :a))
    SubClassOf(ObjectUnionOf(DataMinCardinality(1 :u) ObjectMaxCardinality(1 :t :A)) ObjectIntersectionOf(ObjectOneOf(:c :a) ObjectOneOf(:a)))

where every element is `≤1 u` or `≥2 u`, both branches lead to `a`, and the
ground context splits on `x ≈ a` for every individual and Skolem successor
under the at-most clauses. The native bridge, which decides these inputs at
once when it admits them, defers on all 130 at its datatype gate (ten
distinct reasons; `seeds-base-timeouts-bridge-defer.tsv`). Closing them
needs either a datatype-complete bridge admission or ground splitting in the
CB engine; both are calculus or encoding changes outside this pass.

### Two cost regressions of the nominal CB input (2026-10-31)

Agent `data-values-3`, branch `fix/v155-data-values-3-perf`;
`results/agents/2026-10-30/data-values-3/`. Both passes above are exact
rewrites; two of their applications cost more than they save. Each remedy
below only shrinks the set of definers a pass touches, so the clause set
the CB engine reads is either the frontend's own or one the arguments
above already cover: no calculus, encoding or route decision changes, and
the Lean obligation stays the one stated for the two passes.

**Released disjunctive facts on equated values (hub test).** The test
`data_value_next_to_universal_role_hub_stays_satisfiable`
(`tests/universal_role_and_top_data_range.rs`; the hub of bug 1 plus
`W2 ≡ F ⊓ (u value 1)` and `W3 ≡ S6 ⊓ (u value 1)`) took 0.5 to 0.6 s per
nominal route at e62a4bce and 6 to 15 s from the nominal-coverage merge
(f41b1af4) on. Bisecting over the first-parent merges and timing with
`KM_CB_KEEP_INERT_SORTS=1` locates it in the release (50bf7ba9): the CB
engine takes 0.3 s on the frontend's clause set and 6 s on the released
copy, which differs from it in two clauses only. The complement definer
`Q_4` of `¬(u value 1)` sits in the excluded middle `→ Q_4(x) ∨ Q_6(x) ∨ D(x)`
and is inert (it is read only through `Q_4(x) ∧ u(x, y) → Q_5(y)`, where `u`
has an object domain), so the pass releases it to `→ Q_4(x) ∨ Q_6(x)`. That
fact is true at every data element through `D` in the sorted set but a live
disjunction at every data element in the released one, and the literal's
identity clause `V(y0) ∧ V(y1) → y0 = y1` (`V` the value marker of
`"1"^^xsd:integer`) equates the data successors of every `u`-existential.
The engine's equality rules then copy the disjunction, and what follows from
it, between the data terms: `KM_STATS` goes from 16,127 to 21,628 worked-off
successor clauses, 110,690 to 174,586 Pred checks and, under `KM_PROF_TIME`,
148 ms to 4,646 ms in `add_clause` (3,866 ms of it forward subsumption) and
67 ms to 1,057 ms in the equality rules. Dropping the identity clause from
the released set (a diagnostic, unsound) brings the engine back to 0.2 s.

Remedy (`inert_sorts::equates_generated_values`,
`Options::data_guards_sorted`). When the clause set has the identity clause
of a value marker `V` and some clause puts `V` on a Skolem term
(`… → V(f(x))`, a `DataHasValue` in a positive position), a candidate whose
relativized fact is disjunctive and which guards a data role in a body
(`Q(t) ∧ p(t, y) → …` with `p(x, y) → D(y)`) keeps its sort. Everything
else is released as before: the unit facts of range definers (ORE 9800: 38
released, 39 eliminated, unchanged) and the disjunctive facts of definers
that read no data role, which the nominal seeds need (m2047 answers in
0.5 s released and not within 60 s with every disjunctive release withheld;
a first version of this remedy that withheld all of them lost m2047, m2179
and m2358 on the forced `nominals` route).

**Eliminated filler of an at-most asserted on an individual (r3602).**
`results/agents/2026-10-30/r3-unannounced/open_r3602.ofn` on forced
`nominals` answered in 4 s on the frontend's clause set and not within 60 s
on the copy. The copy differs in one eliminated definer: the `⊤` filler
`Q_4` of `ClassAssertion(≤1 s, c)`, dropped from
`Q_3(x) ∧ Q_4(y0) ∧ Q_4(y1) ∧ s(x, y0) ∧ s(x, y1) → y0 = y1` (`Q_3` the
assertion marker of `c`; `s(a, a)`, `s(c, a)` and `D ⊑ {a, b}` are in the
input). Without the filler the equality fires on every pair of
`s`-successors of `c` before their labels are known, the same cost the pass
already avoids beside inverse roles (probe_v7). Remedy
(`eliminate_universal_definers`): a definer on an equality-head term is kept
when the clause body holds a nominal proxy or an assertion marker and the
term is not a data successor. Fillers of TBox at-most clauses stay
eliminable: ORE 9800's one `⊤` filler sits in 33 functional-role clauses,
and keeping it (a first version of this remedy) took its CB arm from 2.3 s
to 30 s; the filler of a data at-most asserted on an individual (m2047,
`≤2 v` on `a`) stays eliminable too (0.5 s against 2.1 s kept).

Measured on the workstation (`km classify --lines`, medians of three runs;
`km-base-6c48c72e` is development/v1.5.5 before the subset-blocking gap
merge, "this branch" the final build on 0e1bd99a; load 50 to 70 unless
marked, the rows marked * at load 110 to 140 in one session; the full
tables are in `results/agents/2026-10-30/data-values-3/timings.md`):

| input, route | e62a4bce | development | this branch |
|---|---|---|---|
| hub test, automatic | 0.54 s | 0.03 s (object guard, bridge) | 0.02 s |
| hub test, `nominals` | 0.63 s | 12.4 s (a2e98d95); 32.7 s* | 0.53 s; 1.75 s* |
| hub test, `certified_nominals` | 0.54 s | 8.3 s (a2e98d95); >60 s* | 0.55 s; 1.86 s* |
| hub test, `nominal_ni_abox` | 0.62 s | 15.6 s (a2e98d95); 26.9 s* | 0.55 s; 2.15 s* |
| hub test, `certified_card_proxy_abox` | 0.61 s | 9.5 s (97515f0c); 33.2 s* | 0.63 s; 2.11 s* |
| open_r3602, `nominals` | 0.16 s (6 subsumptions, incomplete) | no answer in 60 s (sorted input: 4.1 s; 10 to 14 s*) | 4.4 s; 14.0 s* (7, HermiT's) |
| ORE 9800, automatic | | 11.9 s; 15.1 s* | 10.5 s; 12.8 s* |
| m2131 (nominal_inert_sorts), automatic | | 1.6 s (a2e98d95) | 0.8 s |
| seeds m2047, m2179, m2358, m2218, `nominals` | | 0.46, 2.5, 1.2, 3.4 s | 1.3, 2.5, 1.2, 3.4 s |
| seeds m2109, m2233, m2278, `nominals` | | 9.9, 17.5, 20.8 s | 15.8, 18.3, 20.5 s (m2109 keeps one sort) |

All answers are identical across the binaries, except r3602 where the
merge-hypotheses fix of section 10 made the answer complete.

### Lean coverage of the nominal CB input (2026-10-31)

Agent `lean-universal-definer`, branch `fix/v155-lean-universal-definer`;
`results/agents/2026-10-31/lean-universal-definer/`. This discharges the two
Lean items left open above: the universal-definer elimination had no proof,
and the release certificate of the CB arm was exact but not fail-closed.

**Theorem.** `lean/ContextCalculus/UniversalDefinerElimination.lean` states
`eliminate_universal_definers` over the clause language of
`RulesInertSortRelease.lean` (first-order clauses over concepts, roles,
equality, constants and unary Skolem functions, with arbitrary
interpretations, not only Herbrand ones). `eliminate U S` drops every clause
whose head holds `Q(t)` with `Q ∈ U`, then every body atom `Q(t)` with
`Q ∈ U`, in the order of the Rust pass. `elimConditions U reserved S`
requires each `Q ∈ U` to be outside `reserved` and to have a unit fact
`→ Q(x)` in `S`. Under that check, `models_iff` proves that the models of
`S` are exactly the models of `eliminate U S` that interpret every `Q ∈ U`
as the whole domain; `eliminate_equisatisfiable` proves equisatisfiability
with every side theory that reads only reserved concepts. The composed pass
of the CB arm, `nominalCBInput D P U S = eliminate U (release D P S)`, is
covered by `pipeline_equisatisfiable`, and the certificate
`WireNominalCBInput` by `check_sound`, `check_consistent`, `check_unsat`
and `check_entails`: an accepted certificate's CB input has the
consistency verdict, the unsatisfiable reserved classes and the
subsumptions between reserved classes of the frontend's clause set. All
theorems use only `propext`, `Quot.sound` and, for the answer corollaries,
`Classical.choice`; none uses `sorryAx`.

The cost guards of the pass (clause sets with inverse roles, the filler of
an at-most asserted on an individual, a definer whose elimination would
leave an unconditional role or Skolem head) only shrink `U`, so the theorem
covers them with no extra hypothesis. No corner of the transformation is
outside the theorem: a unit fact `→ Q(x)` makes `Q` the whole domain in
every model, whatever the other clauses say.

**Gate change.** The pass selected candidates with `cb_to_ht::is_internal`,
which also admits builtin vocabulary written as a CURIE (`owl:Thing`),
while `reserved_concepts_for_cb`, the reserved set of the certificate,
reserves every concept outside the frontend's definer prefixes (`Q_`,
`aux_`, `def_`). A unit fact `→ owl:Thing(x)` would have been eliminated
(exact, since no answer is read on `owl:Thing`) and the certificate then
rejected. The pass now also requires `inert_sorts::is_cb_definer`, the
predicate `reserved_concepts_for_cb` uses, so every eliminated definer is
unreserved by construction. This only shrinks `U`.

**CB reservation set.** `release_equisatisfiable` needs only its executable
check (`conditions`) and a side theory that reads reserved concepts. The CB
engine reads the clauses alone (no side theory), and the orchestrator reads
its answers on source names, queries and asserted markers, all in
`reserved_concepts_for_cb`; the subsumption and unsatisfiability queries
are side theories over two reserved names (`subCounterexample`,
`classWitness`). So the CB reservation set satisfies the theorem's
hypotheses; no variant was needed.

**Fail-closed certificate.** `nominal_cb_clause_input` now writes the
`WireNominalCBInput` document of the whole copy (release, then
elimination) when `KM_NOMINAL_CB_INPUT_CERT` names a file or directory,
or under `KM_LEAN_CHECKERS` when the checker directory holds
`nominal-cb-input-check`. The checker runs through
`lean_checkers::run`, so under `KM_LEAN_CHECKERS` a rejection is logged
and `km classify` publishes nothing (exit 6), and `cannot_check` lets the
arm answer as without the checker. With `KM_NOMINAL_CB_INPUT_LEAN_CHECKER`
set by hand, anything but acceptance fails the arm. A rejected certificate
of either kind (this one or the release-only `KM_RULES_INERT_CERT`
document) no longer falls back to the frontend's clauses: the CB arm
returns an error and gives no answer. A copy that cannot be made for other
reasons (I/O, JSON) still keeps the frontend's file, which is exact.

**Lean obligation.** Discharged for the transformation: the CB engine's
answers on the copy equal its answers on the frontend's clause set, for
every model, as far as the clause language above describes the clause
file (the same encoding assumption as `WireInertSortRelease`: variables,
individuals and auxiliary constants, unary Skolem functions). That the CB
engine's answers on its input are exact remains the existing CB
obligation (docs/CERTIFICATION-ROADMAP.md).

### Conditional-full schedule for data values on the bridge (2026-10-31)

ore_ont_10781 (590 individuals, 1,319 data assertions) went from 1.1 s to
13 to 17 s on the automatic route from the native data values merge
(c9602c7f) on; binaries of the two intermediate commits put it at 1b0f9239
(`frontend: carry every data value exactly, without a literal cap`). The
time is the native bridge running to its 12 s data-assertion budget and
declining, after which `certified_nominals` answers. The bridge itself
takes 2.3 s before and 34 to 53 s after on the same input
(`KM_ROUTE=ht_bridge KM_DATA_ASSERTION_AS_CLASS=1`); `KM_BRIDGE_PROGRESS`
puts the whole difference in the prepare phase (0.7 s to 33.7 s over 293
subjects) and shows the schedule change: before, `BRIDGE-REFUTATION
gated=true … number=true` with a saturation pass; after, `number=false` and
no saturation. Every carried value used to come with its singleton clause
`V(y0) ∧ V(y1) → y0 = y1`, whose equality head sets `tin.number`; the
frontend now leaves that clause out when nothing forces two data successors
apart (`datatypes::datatype_relation_clauses_with`, DATATYPES.md), so the
input lost its only number feature and
`native_conditional_full_abox_profile` moved it from the conditional-full
schedule (saturation first, one all-root consistency completion) to the
legacy nominal schedule. `KM_HT_NATIVE_FULL=1` restores 0.66 s.

Remedy (`konclude_ht::bridge::carries_data_values`): a literal value marker
`__dt__val__…` in the input counts as a number feature for the profile. The
profile selects the completion's scheduling configuration only; the bridge
publishes a complete answer or defers under either schedule, so no answer
changes. ore_ont_10781: 13.2 s to 0.6 s (15.9 s to 2.1 s at load 120),
identical 1,027 output lines. The 400 nominal seeds on the automatic route
(60 s, 3 workers per binary, side by side at load 120): 364 and 363
answered, 0 wrong, the one flip (m2336, 47.9 s before) at the time-out.

### Object guard for the native bridge (2026-10-30)

Cost. After the inert-sort release, 125 of the 400 seeds of `gen_nomdata.py
--no-inverse` (2000-2399) still had no answer within 60 s on the automatic
route (`results/agents/2026-10-30/nominal-coverage/seeds-reverted-head-auto.tsv`),
none wrong. None of them reached the native bridge: it deferred at its
datatype gate, and the nominal CB route ran alone. On the two-axiom
reduction of seed 2000 above the CB engine spends its time in single Hyper
inferences of the ground context: the at-most clause of `≤1 t.A`,
`A(y0) ∧ A(y1) ∧ Q_6(x) ∧ t(x,y0) ∧ t(x,y1) → y0 ≈ y1`, joins against 46 to
66 disjunctive context clauses per body atom, about 9 million combinations
per inference (`KM_TRACE_HYPER_PRODUCT`), and no context reaches its next
progress line within 15 s.

The gate. The bridge keeps data successors in its completion graph as
ordinary nodes. It therefore admits an input only if every class axiom
without a datatype holds at a blank node (no concept name, no edge, no
individual), or a witness label exists for such nodes; a datatype-bearing
axiom must have a left side that is false there. 56 of the 125 deferred on
exactly these two checks (`a non-datatype axiom rejects a blank data node`,
`a complex datatype subclass axiom can fire on a data node`), and many of
the 36 `outside the role-local fragment` deferrals are `⊤ ⊑ C` or
disjointness axioms of the same kind. In OWL 2 such an axiom constrains
objects only; data values are not objects.

The rewrite (`frontend/object_guard.rs`). With a fresh internal class `G`
(`__objguard__`), the parsed ontology `O` becomes `O'`:

- each class axiom that fails at a blank element gets `G` on its left:
  `C ⊑ D` becomes `G ⊓ C ⊑ D`, an equivalence that fails there is split into
  its two inclusions with the failing one guarded, a disjointness of two
  blank-true classes becomes `G ⊓ C ⊓ D ⊑ ⊥`;
- each class axiom with a datatype becomes its inclusions (an equivalence
  both directions, a disjointness `C ⊓ D ⊑ ⊥`), since the bridge's datatype
  admission reads inclusions whose left side is false at a blank node, and
  every one of them whose left side holds at a blank element (`⊤`
  included) gets `G`; guarding an axiom that already holds there is as
  exact as guarding one that fails;
- `A ⊑ G` for every class name of the signature (declared, used, or only
  named in an RBox domain or range), `∃r.⊤ ⊑ G` and `⊤ ⊑ ∀r.G` for every
  object role, `{a} ⊑ G` for every individual (an inclusion, not the
  assertion `G(a)`, so that the native ABox coverage check still counts
  the source's class assertions; the assertions moved to the TBox below
  are subtracted from the source count it compares against);
- a class assertion `C(a)` whose `C` holds a datatype outside the shape the
  bridge's ABox path admits becomes `{a} ⊑ C`;
- `∃u.⊤` for a data role `u` becomes `≥1 u.⊤` (the bridge's data-role check
  reads only the second spelling; `DataPropertyDomain(u C)` parses to the
  first).

It applies only when the ontology has a data role and an individual, no
DL-safe rule, no reflexive role, no self restriction and no universal role,
and when at least one axiom is guarded or moved, or a datatype-bearing axiom
is split or normalised (`profile.object_guard_candidate`, computed on every frontend
pass in one allocation-free scan).

Exactness. Two-sorted OWL 2 semantics, object domain `Δ`.

1. A model of `O` is a model of `O'` with `G := Δ`: the added axioms
   conclude `G` or are trivially true, a guarded axiom is weaker than its
   original, and the two normalisations are equivalences.
2. Given a model `J` of `O'`, restrict its object domain to `G^J` (data
   values and data edges unchanged). `G^J` contains every individual, every
   member of a named class, and both ends of every object edge (domain and
   range axioms; an inverse role's edges are the forward role's). By
   induction every class expression of `O` has the same truth value at a
   `G` element before and after the restriction (`∃`, `∀` and counting on
   object roles see only `G` neighbours; data restrictions read the
   unchanged data edges; nominals denote individuals, which stay). So every
   axiom of `O`, guarded or not, holds in the restriction, and so do the
   assertions and the role axioms (Horn conditions on the kept edges).
   Without reflexive roles, self restrictions and the universal role no
   other edge can leave `G^J`.
3. Hence `O` and `O'` are equally consistent; since `A ⊑ G` for each named
   class, a witness of `A ⊓ ¬B` in `O'` is a `G` element and survives the
   restriction, so both have the same subsumptions and unsatisfiable named
   classes. `G` has the `__` prefix and is never published.

After the rewrite every class axiom holds at a blank node by construction,
so the bridge's blank-node gate passes; whether its one-sorted reading of
`O'` is exact remains the bridge's own admission argument (the
blank-node/isolated-extension theorem `IsolatedObjectModelExtension`), which
this change does not touch. The bridge itself has no Lean model.

Lean. Step 2 is proved in `lean/ContextCalculus/ObjectGuardRestriction.lean`
(no sorry; axioms: `Classical.choice` only): `restrict_holds` (truth
preserved at `G` elements, with nominals, data atoms and qualified counting),
`guarded_inclusion_restricted`, `inclusion_restricted`,
`assertion_restricted`, `role_assertion_restricted`, the role-axiom lemmas,
`witness_restricted`, and `original_model_is_guarded` for step 1. Not
checked: that the Rust pass meets the theorem's hypotheses (the blank
evaluation `holds_at_blank`, the collected vocabulary, the refused
constructs); that is argued from the code above. The module was compiled
with `lean` against the Mathlib build of the `checkers-on` worktree; a full
`lake build` was not run.

Routing. The guarded ontology is built only on a third bounded bridge-first
attempt (`orchestrate/mod.rs`), after the historical attempt (or the
data-assertion attempt) declined and only when the frontend reported the
candidate flag; it has the budget of the attempt it follows (8 s, or 12 s
with data assertions; `KM_OBJECT_GUARD_BRIDGE_BUDGET_S`). If the bridge
declines or runs out of budget the schedule continues unchanged. The
forced `ht_bridge` route does not use the guard. `KM_NO_BRIDGE_OBJECT_GUARD`
switches the attempt off.

Repeated assertions (not changed). Seed 2296 states
`ObjectPropertyAssertion(:r :a :a)` twice; the native ABox coverage check
compares the parsed count (2, the parser keeps a set) with the source count
(3) and declines, so the bridge never sees it. Subtracting verbatim
repetitions from the source count was tried and withdrawn: it let the bridge
answer two random seeds of `results/agents/2026-10-30/r3-unannounced/`
(r2730, r3086) that the CB route answers correctly, and the bridge answers
them incompletely. The bridge answers the same inputs incompletely without
the repetition as well, on the development head
(`results/agents/2026-10-30/nominal-seeds/bridge_merge_min.ofn`, seven
axioms: `{b, c} ⊑ {b}`, `a : {b, c}`, `s(b, c)`, `a : ∀s.A`, `Q1 ≡ {b}`;
HermiT `Q1 ⊑ A`; `ht_bridge` and the automatic route miss it). That is a
bridge defect in nominal merging, outside this change; it is listed in
docs/V1.5.5-STATUS.md.

Measurements (`results/agents/2026-10-30/nominal-seeds/`, workstation under
load). Seeds 2000-2399, automatic route, 60 s: 275 ok / 125 timeout / 0 wrong
before, 366 / 34 / 0 after; no ok answer lost. Seeds 7000-7199: 142 / 58 / 0
before, 181 / 19 / 0 after. 112 nominal ORE inputs of the paired design half
at 300 s: same 108 answered, identical output, mean time ratio 0.966. A first
version put only the classes that axioms mention into `G` and missed 28
subsumptions on declared-only classes (all caught by the HermiT differential);
the signature-wide `A ⊑ G` fixes it. What remains: 21 seeds use
`DataComplementOf(xsd:integer)`, outside the bridge's exact atomic datatype
map; 5 defer on the singleton-elision mismatch between the frontend
(`literal_profiles::distinct_data_successors_forced`) and the bridge
(`forced_distinct_data_successors`); 3 use a data bound above 2; 4 other
datatype-value gates; m2296 the repeated assertion.

## 7. Sequoia ordering and nominals

`calc::pred_lteq` has two same-term concept orderings for the CB engine. The
unordered one (named and internal concepts mutually incomparable) is the
complete reference. The Sequoia ordering (`KM_SEQ_ORDER`) totally orders
internal concepts (definers, `__nom__*`, `__data__`, ...) above the named ones,
which restricts Hyper to the maximal internal literal. `set_seq_order_auto`
used to select it for every clause set with a disjunctive head that contains
an internal concept, on the grounds that both orderings are complete. Under
nominal clausification that claim does not hold.

Counterexample (v1.5.4, seed 297 of the bug-1 differential generator,
delta-debugged). Source, HermiT: `Q1` is unsatisfiable:

    SubClassOf(owl:Thing DataMinCardinality(1 :v))
    DataPropertyDomain(:v ObjectOneOf(:b))
    ObjectPropertyAssertion(:s :a :b)
    SubClassOf(DataHasValue(:u "x"^^xsd:string) DataHasValue(:v "2"^^xsd:integer))
    EquivalentClasses(:Q1 ObjectComplementOf(ObjectHasValue(:s :b)))

The data value switches on the sort encoding (section 6), which turns
`⊤ ⊑ ≥1 v` into the disjunctive fact `Q_0(x) → Q_1(x) ∨ __data__(x)`; both
disjuncts are internal, so the Sequoia ordering is selected. Twelve clauses
of the resulting set already show the loss (engine run directly with
`KM_NOMINALS=1`):

    → Q_0(x)                          Q_0(x) → Q_1(x) ∨ __data__(x)
    Q_1(x) → v(x,f(x))                Q_0(y) ∧ v(x,y) → Q_2(x)
    Q_2(x) → __nom__b(x)              __nom__b(x) → x≈b
    Q1(x) → Q_5(x)                    Q_5(x) ∧ s(x,y) → Q_6(y)
    Q_6(x) ∧ __nom__b(x) → ⊥          → s(a,b)
    Q_5(x) ∧ __data__(x) → ⊥          __data__(x) ∧ s(x,y) → ⊥

`Q1` is unsatisfiable: the object `a` (forced so by `s(a,b)`) has a `v`-value,
so `a ≈ b` and `s(b,b)`, and every `Q1` element is `b`, which then has the
`s`-successor `b`. The unordered regime derives `Q1 ⊑ ⊥`; under the Sequoia
ordering the engine stops at `Q1 ⊑ {Q_0, Q_1, Q_2, Q_5, __nom__b}`. The
consequence needs the ground context to resolve `__data__(a)` away in
`Q_1(a) ∨ __data__(a)` and to merge `a` into `b`, and then needs the query
context for `Q1`, which is merged into `b`, to see `s(b,b)`. With the internal
literals totally ordered, the inferences on the non-maximal disjunct that
these steps need are not performed, and the Sequoia completeness argument
(query concepts incomparable, everything else ordered above) does not cover
the cross-context flow through the nominal ground context.

Without nominals no counterexample is known: on 283 generated ALCHIQ
ontologies (inverses, number restrictions, role inclusions, functionality)
the two orderings never disagree, and both agree with HermiT.

Mitigation (v1.5.4, superseded by section 9): `set_seq_order_auto` never
enables the Sequoia ordering when `KM_NOMINALS` is set. This covers every path that runs the CB engine
with nominals (in-process, worker subprocess, certified-nominal routes),
since they all route the ordering through that function and run under the
same environment. An explicit `KM_SEQ_ORDER=1` still forces it, as a
diagnostic override. Nothing else in the calculus changes. Restoring the
Sequoia ordering under nominals needs an ordering whose completeness covers
the ground context, which is a calculus change and needs Lean
re-certification.

Cost (v1.5.4 measurement, automatic route, 300 s cap, sequential, the 201
ORE inputs that take the sort encoding plus 9800, 6951 and 14321):
`ore_ont_9800` (115 s) and `ore_ont_10874` (10 s) become timeouts,
`ore_ont_15655` goes from 29.6 s to 144.8 s, and the total over the 201 files
from 4811 s to 5437 s. The Protégé bug-1 reproducer
(`tests/fixtures/protege_plugin/bug1-nominal-top-property-hang.ofn`) goes
from 0.17 s to about 92 s on every nominal route, and the same input with two
`DataHasValue` probe classes (`data_value_next_to_universal_role_hub_*`)
from 0.2 s to no answer: more than 600 s on the automatic route and more than
1800 s on `nominals` and on `certified_nominals` (worker time cap raised). The
reproducer and the sort-differential fixtures (worst 66 s) now carry a 240 s
bound; both hub tests are ignored and point here. No
taxonomy changes where both regimes answer; the
Sequoia answers on 9800, 10874 and 15655 matched gold, and on 15655 the
engine's two orderings give identical answers, so the loss above is not
triggered there. The unordered regime spends the time in the nominal ground
context before query seeding: every disjunctive fact (notably the sort
encoding's relativized `→ C(x) ∨ __data__(x)`) is instantiated at every
individual (445 to 6038 here), and without an ordering Hyper fires on every
disjunct at every individual (15655: 2.7 M Hyper resolvents in 200 k
ground-context iterations; 9800: 9.1 M in 400 k before the limit; 10874 does
not reach 200 k iterations in 1800 s).

Two exact encodings were tried by hand on the engine input and do not
recover the speed: adding the ground instances `→ C(a)` of every relativized
class-level fact for every named individual (bug-1 reproducer 92.8 s → 93.3 s),
and guarding the relativized facts as `__object__(x) → C(x)` with
`→ __object__(a)` at every individual (101.7 s). Guarding the data-range
excluded middle `→ ¬{v}(x) ∨ {v}(x)` by `__data__(x)` made it slower (over
600 s). The cost is not in those facts alone.

Proposed route back to speed (v1.5.5/v1.6.0; settled in section 9, which
replaces it by a different regime): keep the Sequoia
ordering in ordinary contexts and use the unordered regime only in the
nominal ground context. Evidence: on the minimal clause set the Sequoia
ordering derives `Q1 ⊑ ⊥` once the ground facts `a ≈ b` or `s(b,b)` are given
as input, and still loses it when only `__nom__b(a)` or `Q_1(a)` is given, so
the consequence is lost in the ground context's derivation and propagation of
`a ≈ b`, not in the ordinary query context. This is not a proof: the
completeness argument for ordered resolution needs one admissible ordering
across all inferences that exchange clauses, and ordinary contexts send
non-unit clauses to the ground context. A per-context regime needs its own
completeness argument and Lean re-certification before it can be enabled.
Section 9 gives that argument. The obstacle turns out not to be the order
mismatch (arXiv:1805.01396 allows one order per context, and its completeness
proof judges every exchanged clause by the order of the context that uses it)
but KM's announcement guard on r-Pred, which the paper does not have.

Note on overrides: route bundles reset every routing key before applying
their own settings (`routing::Route::apply_environment`). Before v1.5.4 this
also cleared `KM_SEQ_ORDER` and `KM_NO_SEQ_ORDER`, so neither had any effect
on `km classify` with an explicit or automatically selected route. A value
the user sets is now kept by every bundle that does not set one of the two
keys itself (`seq_on` and `seq_off` decide on their own).

## 8. One definer for equal cardinality and existential restrictions

The recognition direction of `≤n r.F` (emitted when the restriction may occur
negatively) introduces `NQ` for its complement:

    → Q(x) ∨ NQ(x)        Q(x) ∧ NQ(x) → ⊥
    NQ(x) → r(x, g_i(x))  NQ(x) → F(g_i(x))   (i = 0..n)
    NQ(x) ∧ g_i(x) ≈ g_j(x) → ⊥               (i < j)

and `Q`'s own clause gives `Q ⊑ ≤n r.F`. Before v1.5.5 `NQ` was always fresh,
even when the clause set already had a definer `P` for the source restriction
`≥(n+1) r.F` (same role, same filler name `F`, which `q` shares). The CB
engine then saw two names and two Skolem successor families for one concept,
and its at-most clauses had to identify them pairwise in every context.

The clausifier now keys `NQ` in the structural cache under
`≥(n+1) r.F`: if `P` exists, it emits only `→ Q(x) ∨ P(x)` and
`Q(x) ∧ P(x) → ⊥`; otherwise it creates `NQ` as before and a later occurrence
of `≥(n+1) r.F` reuses it.

Exactness. Write `C` for `≥(n+1) r.F`, read with the clause set's own
interpretation of the filler name `F`.

1. In every model `I` of the old clause set `NQ^I = C^I`: `NQ ⊑ C` by the
   witness clauses, and `¬NQ ⊑ Q ⊑ ≤n r.F = ¬C` by the excluded middle and
   `Q`'s at-most clause.
2. New to old: a model of the new set is a model of the old set with
   `NQ := P` and `g_i := f_P_i`, since the old `NQ` clauses are the new `P`
   clauses renamed.
3. Old to new: given a model `I` of the old set, set `P := NQ^I = C^I` and,
   on elements of `NQ^I \ P^I`, `f_P_i := g_i`. `P`'s witness and
   distinctness clauses hold there by the `NQ` clauses, its recognition clause
   (if any) holds because `P` is now all of `C`, the excluded-middle pair holds
   by (1), and every clause with `P` in its head still holds, since `P` only
   grew. A clause with `P` in its body is either that pair or comes from a
   negative occurrence of `C`, and a negative occurrence always gets the
   recognition clause (`n + 1 = 1`, or the polarity pre-pass saw it negative),
   so `P^I` was already `C^I` and nothing changes for it.
4. The reverse order (the at-most first, `≥(n+1) r.F` later) is the same
   argument with the roles of `NQ` and the fresh `P` swapped; by (1) `NQ` is
   already exactly `C`, so it serves both a positive and a negative later
   occurrence.

The same cache serves `∃r.F` and `≥1 r.F`, which are one concept. Both
definitions emit the same clauses: `Q → r(x, f(x))`, `Q → F(f(x))` and the
recognition `r(x, y) ∧ F(y) → Q`, which both arms emit unconditionally (under
native cardinality the `≥1` witnesses go through `CardMeta` instead, the same
restriction). Whichever spelling comes first defines `Q`; the other reuses it.
Then the models are literally the same up to the name of the definer and its
Skolem function, and the `≤0 r.F` complement above finds the existential's
definer through this alias.

So the clause sets before and after have the same models up to the fresh
names, hence the same consistency, subsumptions and unsatisfiable classes.
Only clauses over fresh symbols change; no calculus rule changes, so no Lean
re-certification. With `KM_HT_CARD` the shared `P` keeps its own `CardMeta`;
the skipped `NQ` pushes none.

Scope. The sharing is on for every mechanism. At first (596987b2) it was
enabled only for `KM_MECHANISM=cb`, because the HT translation (`ht_general`)
missed a consequence of the shared shape, and missed the same consequence
without the change when the source spells the shape out:

    EquivalentClasses(:Has DataMinCardinality(1 :d))
    EquivalentClasses(:Two DataMinCardinality(2 :d))
    EquivalentClasses(:No ObjectComplementOf(:Has))
    EquivalentClasses(:AtMostOne ObjectComplementOf(:Two))

`No ⊑ AtMostOne` follows from `Two ⊑ Has`, but `KM_ROUTE=ht_general` reported
only `Two ⊑ Has`. The cause was the HT conversion's complementary-definer
fold (EMELIM), which wrote a folded complement in a clause body as a negative
literal that the worker matches only against an explicit label; it did not
depend on cardinality or on the encoding (docs/HYBRID-CB-HT.md section 7).
With the fold fixed, every test of `empty_and_universal_data_ranges`,
`universal_role_and_top_data_range`, `forced_route_fail_closed` and
`data_assertions_carried` passes with the sharing on, and the gate is gone
(results/agents/2026-10-29/ht-card-complement/).

Effect. The forced `nominals` route on the 26 data-range probes of
`tests/empty_and_universal_data_ranges.rs` hit both patterns after v1.5.4
began parsing `rdfs:Literal` qualifiers as the unqualified restriction
(2179c50c, 4f0cdc54). For example `Exact1 ≡ DataExactCardinality(1 d
rdfs:Literal)` now becomes `Q_0 ⊓ Q_5`, sharing `Has`'s `≥1 d` and
`AtMostOne`'s `≤1 d`, while the complements of `No ≡ ≤0 d` and
`AtMostOne ≡ ≤1 d` were fresh copies of `≥1 d` and `≥2 d`; and
`NotAll ≡ ¬∀d.¬rdfs:Literal` normalises to `∃d.⊤`, a second name for `Has`.
v1.5.3 was faster on several of these inputs only because it kept
`rdfs:Literal` as an opaque label, and it answered 23 of the 26 incompletely
(for example it missed `Exact1 ⊑ AtMostOne`, `All ⊑ No` and the
unsatisfiability of `Min1`). Given the same clause set (`lit_Exact1`, or the
v1.5.3 frontend on the unqualified spelling `DataExactCardinality(1 d)`), the
v1.5.3 engine needed the same time as head, so the engine did not regress.
With the shared definers every probe classifies in at most 0.6 s with
`KM_SEQ_ORDER=1` and 1.0 s in the default regime (head: 8.8 s and 29.3 s), with
unchanged answers. Of 127 test fixtures one (`isolated_list_rules.ofn`)
changes its clause set (two duplicate `∃`/`≥1` definers fewer), with the same
classification on `auto`, `production_all`, `ht_general` and `tableau`.
Measurements are in `results/agents/2026-10-29/nominal-perf/` and
`results/agents/2026-10-29/ht-card-complement/`.
## 9. The context regime (`KM_SEQ_ORDER=context`)

Full argument: docs/PER-CONTEXT-ORDERING.md. Ground theorem:
`lean/ContextCalculus/CompletenessExchange.lean`.

The nominal ground context sends a ground clause only to a context that
announced every individual in it (the announcement guard of the r-Pred scan).
A context therefore sees the ground clauses over its announced individuals
only, and its completeness depends on the ground context's saturation
containing the projection of the ground clause set onto that interface.
Ordered resolution computes such a projection exactly when the interface atoms
lie at the bottom of the order (`exchange_refutation_complete`; necessary by
`ordered_server_interface_not_lower_counterexample`). The receiving context
may use any order, so the Sequoia ordering stays admissible outside the
ground atoms.

The regime, selected by `set_seq_order_auto` in nominal mode wherever the
Sequoia ordering would be selected without nominals (elsewhere in nominal
mode, and under `KM_NO_SEQ_ORDER`, the base context regime: the unordered
same-term order with R2 and R3):

- R1: the Sequoia order on every literal with a variable or a Skolem term, in
  every context (the ground context's `x`-clauses included);
- R2: a ground atom (every argument an individual) lies below another ground
  atom only if its individuals are among the other's, and never below a
  ground equality, in every context; a
  weakening of the order that keeps the Sequoia order among ground atoms
  over the same individuals; it is switched on only when some clause with a
  variable mentions an individual, since otherwise no context but the ground
  context ever holds a ground atom;
- R3: a unit ground equality `→ o ≈ o'` crosses the guard to a context that
  announced either individual (an instance of the paper's r-Pred with `n = 0`).

Seed 297 needs R3 (the `Q1` context announced `b` only, and `b ≈ a` mentions
`a`) and the equality part of R2 (otherwise the unit `b ≈ a` can stay trapped
in `→ Q_0(a) ∨ b ≈ a`). R2 removes a second counterexample, which the unordered regime of
v1.5.4 also misses on the `nominals` route
(`tests/fixtures/nominal_seq_order/p1_cross_individual.ofn`, five axioms,
HermiT `Q ⊑ B`; docs/PER-CONTEXT-ORDERING.md section 4).

Runs that must publish a CB Lean certificate (`KM_CB_LEAN_REQUIRED`) keep the
plain unordered regime: the certification surface models KM's literal order and
the r-Pred guard exactly and does not model R2 or R3. That configuration is
known to miss `p1` and `p2` (`tests/fixtures/nominal_seq_order/p2_cross_individual_named.ofn`,
the same trap with only named disjunctions, which the v1.5.4 router therefore
sent to the plain unordered regime).

Measurements (2026-10-29, shared workstation, files in
`results/agents/2026-10-29/per-context-order/`):

- Engine level (`km engine`, one thread, the 2026-10-28 cost inputs):
  ore_ont_10874 5.7 s (plain Sequoia 5.6 s, unordered over 1800 s),
  ore_ont_9800 86 s (80 s, over 1800 s), ore_ont_15655 7.3 s (3.9 s, 92 s).
  Named subsumptions equal those of the plain Sequoia run on 10874 and 9800
  and those of the unordered run on 15655. 10874 and 9800 have no clause with
  both a variable and an individual, so R2 is off there.
- `km classify` on the 201 gated ORE inputs, automatic route, 300 s cap, one
  process at a time, same binary, same day: context regime 4 943 s raw
  (12 non-answers), unordered regime (`KM_NO_SEQ_ORDER=1`) 5 523 s
  (14 non-answers). 10874: 6.1 s (unordered: timeout; 2026-10-28 plain
  Sequoia 10.3 s). 9800: 120 s, answered by the CB worker at 110 s (unordered:
  115 s, answered by the HT worker at 105 s; 2026-10-28: 115 s and timeout).
  15655: 5.2 s (unordered 147 s; 2026-10-28: 29.5 s and 145 s). No file is
  more than 1.5 times and 5 s slower than under the unordered regime. Where
  both regimes answer (187 files) the SUB/UNSAT/CONSISTENT lines are
  identical. The 2026-10-28 baseline is not directly comparable on totals:
  21 of its plain-Sequoia runs and 20 of its unordered runs exited with rc 1
  within 10 s; today those files answer under both regimes, except
  ore_ont_699 (timeout under both) and ore_ont_3917 (280 s context, timeout
  unordered).
- Bug-1 reproducer: 0.22 to 0.26 s per nominal route (v1.5.4 unordered: about
  92 s). Hub with two data-value probes: 0.5 to 0.9 s per route (no answer
  within 1800 s before); both hub tests run again.
- HermiT differential (60 s cap per run, routes `auto`, `nominals`,
  `certified_nominals`; docs/PER-CONTEXT-ORDERING.md section 7): sorts
  fixtures 33/33 ok; 400 generated seeds without inverse roles 795 ok, 3
  wrong (`m2197`, equally wrong under the unordered regime), 395 timeouts, 7
  RSS-limit stops; 100 seeds with inverse roles 215 ok, 85 timeouts; 300
  ALCHIQ seeds 883 ok, 14 timeouts. 21 runs on 9 files answer only under the
  unordered regime; no wrong answer is specific to the context regime.
- Base context regime (unordered same-term order + R2 + R3, nominal mode
  where the Sequoia order is not selected): ORE files with individuals and
  without an internal disjunction (425 by the `km ofn` clause sets of the
  950 corpus files under 20 MB that mention individuals; 185 more gave no
  clause set within 60 s), 300 s cap, one process per regime: 423 answered
  by both regimes with identical SUB/UNSAT/CONSISTENT lines (one empty
  output under the new regime, ore_ont_4233, was identical on rerun), the
  same two non-answers (ore_ont_13700, ore_ont_7914), 1 196 s before against
  1 188 s after, none more than 1.5 times and 5 s slower, five faster
  (ore_ont_8640 9.6 to 0.7 s, ore_ont_2453 19.6 to 6.9 s). 9800, 10874 and
  15655 keep the context regime (127, 10.7, 7.7 s under heavier load).
- Known incompleteness that remained at v1.5.4: a disjunctive ground
  equality across an unannounced individual was not delivered (section 6 of
  the note). 2026-10-30: four HermiT-checked counterexample motifs; R3 now
  delivers the whole announced interface (an equality needs one announced
  side) and R2 orders ground equalities by shared individuals (section 8 of
  the note, `lean/ContextCalculus/ExchangeEquality.lean`). The first-order
  lifting is not mechanised.


## 10. Merge hypotheses and the nominal-label cache (2026-10-30)

Four random seeds of `results/agents/2026-10-30/r3-unannounced/gen_r3.py`
(`r1600`, `r1646`, `r3403`, `r3602`) were answered incompletely by the exact
`nominals` route under every rule set and with the announcement guard off;
`r1600` (`B ⊑ A`) also on the automatic and `certified_nominals` routes,
a wrong published answer of v1.5.4. They have two causes.
Results, binaries and commands: `results/agents/2026-10-30/nominal-r1600/`.

### 10.1 A query context whose element is an individual

Minimised from `r1600` (HermiT `B ⊑ D`;
`engine/tests/fixtures/nominal_seq_order/merge_r1600_min.ofn`):

    SubClassOf(:B ObjectOneOf(:c))
    ObjectPropertyAssertion(:s :b :c)
    SubClassOf(ObjectSomeValuesFrom(:s :B) ObjectOneOf(:c))
    ClassAssertion(ObjectAllValuesFrom(:s :D) :c)

A `B` element is `c`, so `B(c)`, hence `b ∈ ∃s.B`, `b ≈ c`, `s(c,c)` and
`D(c)`. HermiT's derivation needs the ground facts under the assumption
`B(c)`. The `B` context derives `⊤ → x ≈ c`. Side condition (*) of r-Succ
(arXiv:1805.01396 Table 3) then blocks every push from that context (the
merge clause has empty body and no other literal), so the ground context
never holds `B(c) → B(c)`; nothing in it mentions `B(c)` and it derives
nothing conditional on it. An ordinary context in that position is covered
by its predecessor: Pred carries `f(x) ≈ c` back, the predecessor rewrites
`B(f(x))` to `B(c)` and pushes it. A query context has no predecessor.
The paper's completeness proof builds the ground fragment with
`Γ_o = Ω ∩ R_c`, the ground atoms of the query context's model, and uses
hypotheses `A → A` for them; for a query context blocked by (*) the
calculus never adds them (proof-completeness.tex, unfolding strategy and
`lemma:unfolding:consistency`).

The fix (`Engine::merge_hypotheses`): a query (root) context with core
`K(x)` and a body-free merge clause `⊤ → Δ'' ∨ x ≈ o` (the Join case 3
bridge) pushes `K(o) → K(o)` to the ground context on the edge labelled
`o`. The ground context's conclusions `K(o) ∧ Γ → Δ` return through r-Pred
with `K(o)` copied verbatim into the body (no clause of the query context has
`K(o)` maximal), and Join case 3 resolves `K(o)` against the core clause
`⊤ → K(x)` and the bridge. `KM_NO_MERGE_HYPOTHESES` disables it
(diagnostic). The same fix answers `r3602` (`D ⊑ Q1`) and `r1646`
(`E ⊑ Q1`); on the forced route `r1646` and `r1600` need minutes (10.4).

*Exactness.* Soundness: a hypothesis `A → A` is a tautology
(`Nominals.rsucc_taut_sound`), and Join case 3 is sound
(`Nominals.join3_sound`); the rule adds premises, never conclusions that do
not follow. Completeness: only the core needs pushing. Every clause of the
query context is a consequence of its core and the ontology, so every ground
atom `A'{x↦o}` of its model under the bridge is derivable in the ground
context from the hypothesis `K(o)` by the same inferences grounded at `o`
(the ground context is the one context whose Hyper may map `x` to an
individual). Ground atoms the query context derives from delivered
ground-context clauses are heads of ground-context clauses already, and
ground atoms it derives by local inferences follow from its core and those
clauses, so the ground context derives them under `K(o)` as well. This is
argued, not proved: it is the step the paper's proof leaves implicit. The first version pushed
every maximal ground or `x`-atom of every body-free clause instantiated at
every bridge individual; it did not terminate on `r1600` within 30 s and
was replaced.

*Lean obligation.* Open: the paper's completeness argument with the
hypotheses of `Γ_o` made explicit, i.e. that the ground fragment built under
`K(o)` contains every ground atom of the query context's model (first-order,
not mechanised; the certified CB surface does not model r-Succ edges from
query contexts with merge clauses either). Mechanised parts used: the two
soundness lemmas above.

### 10.2 The nominal-label cache under an ordered ground context

`r3403` (`Q3 ≡ {c}`, HermiT `Q3 ⊑ A`) was missed by the nominal-label
cache (`complete_nominal_enumeration_queries`), which answers an enumeration
class `A ≡ {o1,…,on}` from the body-free unit clauses `→ B(oi)` of the
saturated ground context. The ground context of `r3403` holds
`→ A(c) ∨ c ≈ b` with `A(b)`; ordered superposition keeps `A(c)` maximal and
never derives the unit `→ A(c)`, so the cache saw no `A(c)`. Ordered
saturation is refutationally complete, not complete for unit readout. The
cache now runs only when every body-free clause of the saturated ground
context is a unit: the units then are the least model of the ground
closure (every fired ground instance has a unit head, every unfired one a
false premise), so every entailed type of `oi` is a unit up to the unit
equalities the cache already follows. Otherwise the query takes an ordinary
root context (and 10.1). Lean obligation: none mechanised (a Horn-readout
lemma for the ground closure is the statement to prove). Superseded
2026-10-31: `ExchangeCut.horn_unit_readout` proves it at the propositional
level (docs/PER-CONTEXT-ORDERING.md section 14.4).

### 10.3 Tests

`engine/tests/merge_hypotheses.rs`: the minimised `r1600` on the automatic,
`certified_nominals` and `nominals` routes and without the merge hypotheses
(missed); the four seeds on the automatic and `certified_nominals` routes;
`r3403` and `r3602` on `nominals`; `r1600` and `r1646` on `nominals` as an
ignored test (minutes).

### 10.4 Measurements and cost

`results/agents/2026-10-30/nominal-r1600/` (binaries, loads, commands).
Exact `nominals` route, HermiT oracle.

- Open seeds, 300 s: `r3403` and `r3602` correct on all three routes
  (7.0 s and 6.5 s on `nominals`, before 0.2 s and 0.5 s wrong); `r1600`
  correct on the automatic (16.5 s) and `certified_nominals` (18.5 s)
  routes, the shipping wrong answer is gone; `r1600` and `r1646` time out at
  300 s on the forced route (`r1600`'s `B` query alone answers correctly in
  238 s at engine level). `r1646` is correct on the other two routes.
- `gen_r3.py`, 4,000 seeds, 10 s: 2,191 ok, 0 wrong, 1,809 timeouts (5
  worker errors, answered or timed out on rerun). The r3-unannounced
  campaign at higher load: km.final 2,205 ok, 4 wrong (`r1600`, `r1646`,
  `r3403`, `r3602`), 1,761 timeouts, 30 errors; v1.5.4 2,217 ok, 4 wrong.
  On the 724 seeds rerun with km.final2 at the same load: km.final2 401 ok,
  this build 382 ok; 22 seeds km.final2 answered (several in under 0.1 s)
  time out here. The cost is the merge hypotheses: `r5`, `r10`, `r163` take
  0.03 s with `KM_NO_MERGE_HYPOTHESES` and more than 10 s with them. On
  `r5` (`C ⊑ {b, e}`, `e ∈ {a, d}`) the bridges multiply (`x ≈ b`, `x ≈ e`,
  then `x ≈ a`, `x ≈ d`), each adds a hypothesis, and the ground context and
  its successor contexts grow to 30,000 clauses with up to four hypotheses
  per body (122 s for the `C` query). The ground atoms these conclusions
  carry back are pushed again by ordinary r-Succ from other contexts; that
  is the calculus's r-Succ, so cutting it needs its own completeness
  argument (not attempted).
- Motif sets (section 8 of PER-CONTEXT-ORDERING.md), 20 s: m1 to m5 1,999
  ok, 1 timeout; m6, m7 997 ok, 3 timeouts; 0 wrong (as km.final).
- ORE paired design, 112 nominal inputs, automatic route, 300 s, against
  km.final2: 106 answered by both with identical SUB/UNSAT/CONSISTENT lines,
  2 answered only here (ore_ont_3077, ore_ont_699; km.final2 timed out at
  300 s), 3 time out in both (16420, 1833, 2548), and ore_ont_8250 exits 3 after 0.1 s here (the `ht_rules` worker declines; merged from `development/v1.5.5`) where km.final2 timed out; total 622 s against 657 s, median
  ratio 1.01, mean 1.37 (ore_ont_10781 1.1 s to 14.3 s; the frontend's
  second pass under `certified_nominals` takes 12 s with every change of this
  branch switched off, so it comes from the merged `development/v1.5.5`, not
  from these rules).
- After merging `development/v1.5.5` at a2e98d95: seeds r0 to r999 530 ok,
  0 wrong (531 before the merge). On forced `nominals`, r3602 times out on
  the merged base with the merge hypotheses switched off as well. The five
  seeds r1536, r1866, r2408, r2564 and r3777 that the automatic route
  answers wrongly are answered by the typed-nominal bridge's HT worker (the
  bridge merging defect of `results/agents/2026-10-30/nominal-seeds/`); the
  forced CB route of km.final2 answers them correctly, so they do not share
  r1600's cause. Under the merge hypotheses r1536 and r3777 time out at 60 s
  on forced `nominals`, and the hub with data values takes 30 s instead of
  10 s on `certified_nominals`.
- m2197 (`tests/fixtures/top_nominal_data/m2197.ofn`, `⊤ ⊑ {a}` next to
  data cardinalities and `≤2 t.D`; agent data-values-3, 2026-10-31): on
  forced `certified_nominals` and `nominals` 0.6 s at a2e98d95 and no
  answer in 150 s from the r1600 merge (2f5993c7) on, 20 s on
  `nominal_ni_abox`. `KM_NO_MERGE_HYPOTHESES=1` answers in 0.2 s on every
  nominal route with the same three subsumptions (HermiT's), and
  `KM_CONTEXT_PAIR_R2=1` changes nothing, so the cost is the merge
  hypotheses of 8bbbf1f2 alone, in the same way as r1536 and r3777 above.
  It is the same input on the sorted and the released clause set, so it is
  independent of the inert-sort passes. Not remedied: the hypotheses are
  what makes r1600 complete, and a cheaper form needs the completeness
  argument this section leaves open. `top_nominal_data_successors::
  hermit_answers_on_every_route` fails its 120 s bound on these routes.
- The "object value instead of data value" case of
  `universal_role_and_top_data_range::data_value_singleton_next_to_nominal_successors`
  (`¬(p value e) ⊑ B` with `S6 ≡ {c} ⊓ ∃r.{d} ⊓ ∃r⁻.{d}`; same agent, same
  day) has the same profile: forced `nominals` 0.4 s at e62a4bce and
  a2e98d95, no answer in 60 s at 6c48c72e on the sorted and the released
  clause set alike, 0.35 s with `KM_NO_MERGE_HYPOTHESES=1`;
  `certified_nominals` 0.05 s, `nominal_ni_abox` 20 s,
  `certified_card_proxy_abox` over 60 s. The test fails its 10 s bound from
  the r1600 merge on; the other six cases of the test answer in 0.02 s.

### 10.5 The exchange cut and the open obligation of 10.1 (2026-10-31)

docs/PER-CONTEXT-ORDERING.md section 14 removes the push-back cascade of
10.4 (`Engine::rsucc_covered`, `Engine::merge_hypothesis_covered`) and
states the propositional skeleton of the exchange with hypotheses in
`lean/ContextCalculus/ExchangeCut.lean`: the merge hypothesis is the push
that the demand condition asks for at the Join case 3 clause
`⊤ → Δ'' ∨ K(o)`, and `no_merge_hypothesis_counterexample` is the skeleton
of `merge_r1600_min`. What stays first-order and argued is the simulation
step of 10.1 (the ground context derives under `K(o)` the atoms the query
context derives by its own inferences).


## 11. Polarity encoding of complement definers (2026-11-01)

Agent `polarity-definers`, branch `fix/v155-polarity-definers`. Results:
`results/agents/2026-11-01/polarity-definers/`.

### 11.1 The defect

For `SubClassOf(ObjectComplementOf(ObjectHasValue(p e)) B)` the clausifier
reifies the NNF `∀p.¬{e}` (negative polarity) as `Q_0`, the filler `¬{e}` as
`Q_1 ≡ ¬nom_e`, and emits the `∀` introduction with the complement definer
`Q_3` of the filler:

    Q_1(x) ∧ nom_e(x) → ⊥        (definition, Q_1 ⊑ ¬{e})
    → Q_1(x) ∨ nom_e(x)          (excluded middle, ¬{e} ⊑ Q_1)
    Q_0(x) ∧ p(x,y) → Q_1(y)     (propagation)
    → Q_0(x) ∨ Q_2(x),  Q_0(x) ∧ Q_2(x) → ⊥
    Q_2(x) → p(x,f(x)),  Q_2(x) → Q_3(f(x))
    Q_3(x) ∧ Q_1(x) → ⊥          (complement constraint, Q_3 ⊑ ¬Q_1)

With nominal clausification (`KM_ABSORB=0`, every nominal route) the
excluded middle puts the bridge `Q_1(x) ∨ x ≈ e` into every context, every
query context pushes the merge hypothesis `K(e)`, and the `S6(e)` world of
the test case is the whole cost (docs/PER-CONTEXT-ORDERING.md section 15.4 on
`fix/v155-objvalue-cost`). `universal_role_and_top_data_range::
data_value_singleton_next_to_nominal_successors`, case "object value instead
of data value", exceeded its 10 s bound on forced `nominals` (no answer in
60 s; `certified_card_proxy_abox` over 60 s, `nominal_ni_abox` 20 s).

### 11.2 The repair (`frontend::normalise::polarity_definers`)

After clausification the frontend runs a Plaisted-Greenbaum pass over the
TBox and ABox clauses. Its candidates are the complement definers
`Q ≡ ¬A` of an atomic operand (a class name, a nominal `{o}`, a value
concept `__dt__val__v`), in definition order. For each candidate it
evaluates the gate on the current clause set:

* the definition clause `Q(v) ∧ A(v) → ⊥` and the excluded middle
  `→ Q(v) ∨ A(v)` are present and `Q ≠ A`;
* every clause whose body mentions `Q` is the definition clause or a
  complement constraint `N(v) ∧ Q(v) → ⊥` with `N ∉ {Q, A}`.

This is "`Q` occurs with one polarity only": apart from its definition and
the complement constraints, which the pass rewrites, `Q` occurs in heads
only. On acceptance the pass rewrites every complement constraint to
`N(v) → A(v)` (for the `∀` introduction above, `Q_3 → nom_e`, the hand edit
of section 15.4) and removes the excluded middle. A definer with any other
body occurrence keeps the biconditional. `KM_NO_POLARITY_DEFINERS=1` turns
the pass off (diagnostic).

Scope. The pass reads only the clause set, so it covers `¬A` in heads
(`X ⊑ ¬A`, disjointness) and the `∀` introduction of a filler `¬A` on every
setting of `KM_ABSORB`. It does not act on:

* `KM_ABSORB=1` with a negation of negative polarity only: absorption then
  omits the definition clause, so the gate fails and the clause set is
  unchanged (the excluded middle stays);
* a filler `¬A` of an `∃`, `≥n` or `≤n` restriction: the recognition clause
  `r(x,y) ∧ Q(y) → …` is a body occurrence, so the gate fails;
* `DataComplementOf` inside a data range: the data vocabulary
  (`frontend/datatypes`) emits its own complement clauses, which carry no
  `Q_` definer;
* the complement definers `nq`, `nd` of the `∀` introduction and of
  number restrictions: they are not candidates.

Consumers. The `definers` metadata (recorded under `KM_TRIGGER_ABSORB` and
native cardinality) still says `Q ≡ ¬A`; the konclude bridge replaces `Q` by
`¬A`, under which the removed excluded middle and the old and the new
complement constraint are tautologies, so its input is unchanged up to
tautologies. `KM_EMELIM` and the HT `elim_complements` look for excluded
middles and find fewer. The orchestrator, the incremental session, the
source-reuse module and the Lean checkers read `Q_` names only to classify
them as internal (`inert_sorts::is_internal`, `source_incremental`,
`calc::is_internal_concept`) and re-check every clause shape they use.

### 11.3 Exactness

Let `S` be the clause set before a step and `S'` after it. Every clause of
`S'` follows from `S`: a rewritten clause `N(v) → A(v)` follows from
`N(v) ∧ Q(v) → ⊥` and `→ Q(v) ∨ A(v)`. Conversely, let `J` be a model of
`S'` and `J'` the interpretation that agrees with `J` except that `Q` is
the complement of `A`. The definition clause is in `S'`, so `J(Q) ⊆ J'(Q)`.
In `J'` the excluded middle and the definition clause hold by construction,
a complement constraint holds because `J` satisfies its rewrite, and every
other clause holds because `Q` occurs in it only in the head, where
enlarging `Q` preserves truth. `J'` changes no symbol but the fresh `Q`, so
consistency, the unsatisfiable named classes and the subsumptions between
named classes are unchanged, and so is every symbol later passes read
(nominals, value concepts, roles).

### 11.4 Lean

`lean/ContextCalculus/PolarityDefiners.lean` (imported by
`ContextCalculus.lean`) states the gate (`gate`), the step (`transform`,
`step`) and the pass (`run`, a fold over the candidate list) exactly as the
Rust pass computes them, over the clause language of
`RulesInertSortRelease`, and proves

    theorem step_models_forward (hgate : gate reserved Q A clauses = true)
        (hmodels : Models I clauses) : Models I (transform Q A clauses)
    theorem step_models_backward (hgate : gate reserved Q A clauses = true)
        (hmodels : Models J (transform Q A clauses)) :
        Models (J.complementAt Q A) clauses
    theorem step_equisatisfiable (pair : Nat × Nat) (hside : ReadsOnly reserved side) :
        Satisfiable clauses side ↔ Satisfiable (step reserved clauses pair) side
    theorem run_equisatisfiable (pairs : List (Nat × Nat)) (clauses : List Clause)
        (hside : ReadsOnly reserved side) :
        Satisfiable clauses side ↔ Satisfiable (run reserved pairs clauses) side
    theorem run_answers (pairs : List (Nat × Nat)) (clauses : List Clause) :
        (Consistent clauses ↔ Consistent (run reserved pairs clauses)) ∧
        (∀ A ∈ reserved, ClassUnsat clauses A ↔ ClassUnsat (run reserved pairs clauses) A) ∧
        (∀ A ∈ reserved, ∀ B ∈ reserved,
          Entails clauses A B ↔ Entails (run reserved pairs clauses) A B)

`#print axioms`: `step_models_forward` `[propext, Quot.sound]`; the others
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`. The gate is the
hypothesis: `gate` is the Rust gate plus `Q ∉ reserved`, which holds because
every candidate is a fresh `Q_n` and `IriRegistry` escapes source names with
that prefix. `decide` checks the gate and the result of `run` on the clauses
of 11.1. The module was compiled with `lake env lean` against hard-linked
Mathlib packages (no full `lake build`).

The Rust side: `polarity_definer_tests::production_pass_matches_the_lean_definition`
compares the indexed production pass with a literal transcription of the
Lean definitions (`gate`, `rewrite`, `transform`, `run`, with the clause
shapes restated as atom sets) on 20,000 generated clause sets (definition
clauses, excluded middles, complement constraints in either order, other
body and head occurrences, other variables, Skolem and individual terms,
ABox clauses): equal clause sets and equal accepted candidates on all of
them, with both gate outcomes exercised. What stays argued, not mechanised:
the translation of the Rust `DLClause` (string names, `Term::Var` names) to
the Lean clause language, and the frontend before and after the pass.

### 11.5 Validation

Details and reproduction: `results/agents/2026-11-01/polarity-definers/README.md`.

* The object-value case answers in 0.04 s on forced `nominals` (over 60 s
  before), 0.03 s on `certified_card_proxy_abox` (over 60 s) and on
  `nominal_ni_abox` (20 s); `universal_role_and_top_data_range` passes
  13 of 13.
* Frontend: on the 1,094 ORE design-half inputs, 79 clause files change by
  default and under `KM_NOMINALS=1`, 23 under `KM_ABSORB=1`, and no meta file
  changes. On the 79, the automatic route (`KM_THREADS=1`, 240 s) gives
  identical answers with both binaries (889 s base, 766 s new).
* HermiT seeds: `gen_r3` r0-r999 on forced `nominals` at 60 s 639 ok, 4,000
  at 10 s 2,521 ok (forced `nominals`) and 3,795 ok (auto), the data-value
  pools of `forced-nominal-data-misses` on auto, `certified_nominals` and
  `nominals`: 0 WRONG everywhere. The pass changes none of the `gen_r3`
  seeds' frontend output, so r163, r219, r461, r481, r575, r696, r1536 and
  r3777 still time out (their cost is section 10.4).
