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

Open: the HT consumers. Two consumers never see the sorted clause stream
and still answer "inconsistent" on m2197 and its probes:

- the native completion bridge (`ht_bridge`, the HT arm of
  `certified_nominals`, and the route `auto` picks for these inputs)
  rebuilds class axioms from `source_axioms` in source mode, where
  `DataMinCardinality(2 u)` is `AtLeast(2, u, Top)`. Its datatype gate
  (`exact_atomic_datatype_bridge_fragment`, which checks every
  non-datatype axiom on a blank data node and would defer on `⊤ ⊑ {a}`)
  only runs when a `__dt__` concept occurs, so a data property used only
  with `rdfs:Literal` fillers is invisible to it;
- `ht_general` runs without `KM_NOMINALS`, so the sort pass never runs and
  the clausal hypertableau reads the data successors as objects (also with
  a qualified filler, `⊤ ⊑ ≥2 u.xsd:string`).

The clausal hypertableau itself is exact on the sorted clause set (the
`km tableau` worker answers "consistent" on the sorted m2197 input), so
both gaps are admission and routing questions, not calculus defects.

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
- Known incompleteness that remains: a disjunctive ground equality across an
  unannounced individual is not delivered (section 6 of the note); the
  first-order lifting is not mechanised.

