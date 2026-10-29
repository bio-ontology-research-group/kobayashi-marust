# The Sequoia ordering under nominals: the context regime

Status (v1.5.5 candidate): implemented as `KM_SEQ_ORDER=context`
(`calc::SEQ_ORDER_CONTEXT`). This note states the regime, the completeness
argument and its boundary, and the two counterexamples that fix its shape.
docs/NOMINALS-CB.md section 7 describes the problem and the cost; section 9
there points here. The ground theorem is
`lean/ContextCalculus/CompletenessExchange.lean`.

## 1. What the calculus allows

Checked against the source of arXiv:1805.01396 (Tena Cucala, Cuenca Grau,
Horrocks, IJCAI 2018; `calculus.tex`, `proof-completeness.tex`,
`proof-order.tex` of the arXiv tarball):

- Definition 5 (context structure) maps every context `v`, the root context
  `v_r` included, to its own context order `≻_v`. The text before Definition 3
  says: "although each context can use a different ≻ order, a-terms are
  compared in the same way across all contexts since ⋗ is globally defined".
  No condition relates `≻_u` and `≻_v`.
- Every side condition of a rule uses the order of the context that holds the
  premise: Hyper, Eq, Fact and Join use `≻_v` of the context they fire in;
  Pred, Succ, r-Succ and r-Pred use `≻_u` for the premises `Δ_i ⋡_u A_iσ` that
  live in `u`; Nom uses `≻_{v_r}`.
- The completeness proof (Appendix C) builds one model fragment `R_t` per term
  `t` from the clauses of ONE context `X_t`, grounded and totalised under that
  context's order (conditions O1, O2). Fragments are glued only through "rule
  `R` is not applicable" facts, and each such fact is stated with the premise
  context's order.

So a family of different orders is a legal instantiation, and a clause that
moves between contexts is judged by the order of the context that uses it.
The usual worry, that ordered resolution needs ONE admissible order across all
inferences that exchange clauses, does not arise in the paper's calculus.

Definition 3 still constrains each order. Condition 6 says that no atom of
`Pr` (ordinary contexts) or `Pr^r` (the root context) is greater than any
context term outside `{x, y, true}` and the individuals. `Pr^r` contains every
ground concept atom `B(o)`. In `v_r` a ground concept atom must therefore not
be greater than any other root atom. The plain Sequoia order puts internal
concepts above named ones on the same individual, so it violates condition 6
in `v_r`; KM's reference order (same-term concepts incomparable, different
terms compared term-major) violates it across individuals (`B(b) ≻ C(a)`
when `b ≻ a`). The published conditions are not jointly satisfiable for `v_r`
as stated (condition 2 orders the individuals, condition 4 then forces
`B(b) ≻ B(a)`, condition 6 forbids it); the appendix's argument for root
contexts lists only `B(y)`, `S(y,y)`, `S(y,o)`, `S(o,y)` as root predecessor
triggers. This note does not rely on condition 6 for `v_r`; section 3 derives
the property that KM needs directly.

## 2. Where KM departs from the paper: the announcement guard

The paper's r-Pred with `n = 0` copies every ground clause of `v_r` into every
context, and the completeness proof uses this: the query context `q` holds all
ground clauses, and the query fragment `R_c` decides the ground part of the
model (`Γ_o = Ω ∩ R_c`; Lemma "unfolding:noncontradiction": "By r-Pred with
n = 0, … ∈ S_{v_q}").

KM delivers a ground clause only to a context that announced every
individual the clause mentions (`engine.rs`, the ground-sender branch of the
Pred scan and `subscribe_merge_individuals`; the comment there records the
livelock on ore_ont_10594 without the guard). A context `u` therefore sees
only the ground clauses over its announced individuals `I_u`. Completeness of
`u` now depends on the ground context: its saturation must contain, over the
interface `V_u` (ground atoms whose individuals all lie in `I_u`), enough
clauses for every refutation in `u`. That is a projection property, and the
ground context's order decides whether it holds.

## 3. The ground theorem (Lean, sorry-free)

`lean/ContextCalculus/CompletenessExchange.lean`, propositional clauses,
resolution modulo strengthening and tautology deletion (the closure contract
of `CompletenessOrderedSubsumption.lean`), orders given as injective ranks:

- `based_model_correct` (projection lemma). Let `S` be closed under
  `rk`-ordered resolution and let `V` be a lower set of `rk`. Every
  assignment of `V` that satisfies the clauses of `S` inside `V` extends,
  unchanged on `V`, to a model of `S`.
- `exchange_refutation_complete`. A server `G` closed under its rank `rkG`,
  with `V` a lower set of `rkG`; a consumer `Q` closed under an UNRELATED rank
  `rkQ`; `G` delivers every clause inside `V` to `Q` (up to strengthening);
  `G` and `Q` share only atoms of `V`. If `G ∪ Q` is unsatisfiable, `Q`
  contains `⊥`. The theorem says nothing about which clauses `Q` sent to `G`:
  they are members of `G` like any other, so the non-unit clauses that
  ordinary contexts send to the ground context need no extra condition.
- `exchange_unit_readout_complete`. Same hypotheses; if `G ∪ Q` entails an
  atom `b` that is `rkQ`-least among the atoms of `Q` and lies in `V` or is
  private to `Q`, then `Q` contains `⊥` or a clause that strengthens `→ b`.
  This is the positive readout; condition C2 of Theorem 2 of the paper is the
  first-order form of "`b` least", and the Sequoia order meets it in query
  contexts (named concepts incomparable and below the internal ones).
- `closedR_of_closedAll`, `unordered_server_complete_for_every_interface`:
  a server closed under unrestricted resolution serves every interface.
- `closedR_of_closedMaximal`, `maximal_server_complete`: a server closed
  under resolution on the maximal literals of a strict relation serves `V`
  when some rank that extends the relation has `V` as a lower set.
- `ordered_server_interface_not_lower_counterexample`: the lower-set
  condition is necessary. Server `{→ B(b) ∨ Q_0(a), Q_0(a) → ⊥}` ranked with
  `B(b)` above `Q_0(a)`, consumer `{B(b) → ⊥}`, interface `{B(b)}`: the server
  is saturated, delivers nothing, the union is unsatisfiable, and the
  consumer has no `⊥`.

Axioms of every listed theorem: `propext`, `Classical.choice`, `Quot.sound`.

Consequence for KM. The consumer may use any order, so the Sequoia order is
admissible in every ordinary and query context. The ground context must,
for every interface `V_u` that the guard can produce, admit a linear
extension of its order with `V_u` at the bottom. Announced sets are arbitrary
subsets of the individuals, so no two ground atoms may be strictly ordered.
Literals with a variable or a Skolem term never pass the guard as interface
atoms, so the ground context may order them freely, the Sequoia way included.

## 4. The two counterexamples (HermiT-checked)

**Seed 297, plain Sequoia** (docs/NOMINALS-CB.md section 7; the 12-clause
engine input in `.work/agent-assets/2026-10-28-scratch/b3/m3_min.json`). The
ground context derives `b ≈ a` (oriented `b → a`) and `s(a,a)`; the `Q1`
context derives `x ≈ b`, subscribes to `b`, and never receives `b ≈ a`
because the clause mentions `a`. Under the unordered regime the ground
context's `x`-clauses (`→ __data__(x) ∨ x ≈ b`, …) and the pushed hypothesis
`Q_6(b)` produce `Q_6(b) → ⊥`, which mentions only `b` and passes the guard.
The guard makes the interface of `Q1` the atoms over `b` alone, while
equality moves the facts about `b` onto `a`. This is outside the propositional
theorem (equality), and the regime closes it with rule R3 below.

**`p1`, reference regime** (new, `engine/tests/fixtures/nominal_seq_order/p1_cross_individual.ofn`):

    SubClassOf(ObjectSomeValuesFrom(:r ObjectComplementOf(:B)) :C)
    ObjectPropertyAssertion(:r :a :b)
    ClassAssertion(ObjectComplementOf(:C) :a)
    SubClassOf(:Q ObjectOneOf(:b))

HermiT: `Q ⊑ B`. The ground context holds `→ B(b) ∨ Q_0(a)` with `B(b)`
maximal (term-major, `b` interned after `a`) and never resolves `Q_0(a)`;
`Q` announced only `b`. KM v1.5.4 misses `Q ⊑ B` on the exact `nominals`
route in the reference (unordered) regime; with `a` and `b` swapped it also
misses it on `certified_nominals`. This is the propositional counterexample of
section 3 inside the reference regime, so the reference regime is not the
complete baseline it was taken to be. Rule R2 below removes it.

## 5. The regime

`KM_SEQ_ORDER=context`; `set_seq_order_auto` selects it in nominal mode
wherever the plain Sequoia ordering would be selected without nominals,
except in runs that must publish a CB Lean certificate
(`KM_CB_LEAN_REQUIRED`): the certification surface models the literal order
(`CBSourceHyperClosure.predLe`) and the r-Pred guard
(`CBRootPredSendEnumeration`, exact send sets) of the unordered regime, so a
context-regime certificate would be rejected. Those runs keep the unordered
regime. `KM_SEQ_ORDER=1` (plain Sequoia) and `KM_NO_SEQ_ORDER` remain
diagnostic overrides.

- **R1.** In every context, same-term concept literals on a variable or a
  Skolem term (`x`, `f(x)`, `f(o)`) use the Sequoia order: internal concepts
  totally ordered above the named ones, named concepts incomparable.
- **R2.** In every context, two ground atoms (every argument a named
  individual or an additional nominal) are incomparable. Their comparisons
  with every other literal are unchanged. R2 only removes strict comparisons,
  so it weakens the order; every inference of the order without R2 is still
  performed.
- **R3.** The ground context delivers a unit ground equality `→ o ≈ o'` to a
  context that announced `o` or `o'`, not only to one that announced both.
  The receiving context rewrites with it, its merge clause then names the
  other individual, and the merge subscription extends its interface. R3 is
  an instance of the paper's r-Pred with `n = 0`, hence sound.

The literal order is the same in every context: it depends only on the
literals compared. R2 acts where ground atoms occur, which is mainly the
ground context; R1 keeps the Sequoia order on the ground context's
`x`-clauses. The literal reading of "unordered in the ground context only" was
measured and rejected (section 7): it keeps the cost, because the cost sits in
the ground context's `x`-clauses, and it does not remove `p1`, because the
reference order is not consequence-finding across individuals.

## 6. Completeness: what is proved, argued, and open

- **Proved (Lean, ground level).** The exchange between a ground context that
  satisfies R2 and a consumer with any order, for any announced interface:
  `unordered_server_complete_for_every_interface` (R2 makes all ground atoms
  incomparable; every literal with a Skolem term is above them, so the
  announced ground atoms form a lower set of a linear extension;
  `maximal_server_complete` covers the Sequoia order on the remaining
  literals), with the positive unit readout
  (`exchange_unit_readout_complete`). This covers the two-regime exchange
  itself, not only the single-order case.
- **Argued, not proved.** (a) The correspondence between KM's guard and the
  theorem's `ExchangeCond`: KM delivers the clauses inside the interface whose
  body atoms the receiver pushed (r-Succ hypotheses); a receiver that never
  holds an atom positively loses nothing by not receiving clauses that need it
  in the body. (b) Locality: a context holds ground atoms only over
  individuals it announced (merge subscriptions, r-Succ edges) or received.
  (c) The ground context's `x`-clauses form a vocabulary disjoint from its
  ground atoms at the propositional level; they meet ground atoms only through
  equality and Join case 3.
- **Not covered.** Equality: R3 handles unit ground equalities; a disjunctive
  equality `→ o ≈ o' ∨ C(o'')` across an unannounced individual is not
  delivered, and no proof covers that case. The first-order lifting of the
  context calculus (Skolem terms, Pred/Succ, Join, Nom) is the same open
  obligation as for the single-order case (lean/README.md, "What is NOT
  claimed"; docs/CERTIFICATION-ROADMAP.md).

The claim is therefore: the context regime meets the ground-level standard of
`CompletenessOrdered.lean`, extended by a proved exchange theorem for two
different orders, and it removes both known counterexamples. It is not a
first-order completeness proof, and the equality gap of the guard remains.

## 7. Measurements

See docs/NOMINALS-CB.md section 9 and
`results/agents/2026-10-29/per-context-order/`.
