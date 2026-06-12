# Nominal support in the CB engine (ALCHOIQ calculus)

Status: DESIGN (2026-06-12). The last structural completeness gap besides
datatypes (excluded from the goal). Target calculus: Tena Cucala, Cuenca Grau,
Horrocks, "Consequence-based Reasoning for Description Logics with Disjunction,
Inverse Roles, Number Restrictions, and Nominals", IJCAI 2018
(arXiv:1805.01396). The engine header has referenced its Table 3
(Nom/Join/r-Succ/r-Pred) since the start; this doc maps it onto KM. The arXiv
source tarball includes full soundness/completeness proofs
(proof-sound.tex, proof-completeness.tex, proof-payasyougo.tex), which the
Lean re-certification will follow.

## 1. The gap today

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
- Nom: gated behind detection of the O+I+Q interaction triple; nominal
  labels ρ as interned strings with the `o_ρ > o_ρ'` order hook.

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
- Phase 3: Lean re-certification following proof-sound.tex (soundness of the
  four rules + the generalised Table 2 rules) and the completeness argument.
  This IS calculus logic: re-cert is mandatory before default-on.

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
