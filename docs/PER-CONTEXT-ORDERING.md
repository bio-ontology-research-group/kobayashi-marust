# The Sequoia ordering under nominals: the context regime

Status (v1.5.5 candidate): implemented as `KM_SEQ_ORDER=context`
(`calc::SEQ_ORDER_CONTEXT`) and auto-selected in nominal mode wherever the
plain Sequoia ordering is selected without nominals. This note states the regime, the completeness
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
- `exists_rank_extending_lower`, `downward_server_complete`: on a finite atom
  set, a strict partial order and a downward-closed `V` always admit such a
  rank, so a server closed on maximal literals of a strict partial order
  serves every downward-closed interface.
- `ordered_server_interface_not_lower_counterexample`: the lower-set
  condition is necessary. Server `{→ B(b) ∨ Q_0(a), Q_0(a) → ⊥}` ranked with
  `B(b)` above `Q_0(a)`, consumer `{B(b) → ⊥}`, interface `{B(b)}`: the server
  is saturated, delivers nothing, the union is unsatisfiable, and the
  consumer has no `⊥`.

Axioms of every listed theorem: `propext`, `Classical.choice`, `Quot.sound`.

Consequence for KM. The consumer may use any order, so the Sequoia order is
admissible in every ordinary and query context. The ground context must,
for every interface `V_u` that the guard can produce, admit a linear
extension of its order with `V_u` at the bottom. `V_u` is the set of ground
atoms whose individuals were all announced by `u`, and announced sets are
arbitrary sets of individuals. `V_u` is downward closed for every `u` exactly
when a ground atom lies below another ground atom only if its individuals are
among the other's: `B(o) < C(o)` and `B(o) < r(o,o')` may stay, `B(a) < C(b)`
and `r(a,b) < C(b)` may not. Literals with a variable or a Skolem term never
pass the guard as interface atoms, so the ground context may order them
freely, the Sequoia way included.

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

**seed297_min, R2 without its equality part.** With R1, R3 and the
ground-atom part of R2 only, the `nominals` route lost `Q1 ⊑ ⊥` on
`seed297_min.ofn`, and the loss depended on the work order (`KM_NO_TODO_UNITS_FIRST`
or `KM_NO_CENTRAL` recovered it). The ground context held
`→ Q_0(a) ∨ b ≈ a` with `Q_0(a)` below the equality, so `Q_0(a)`, although
refutable, was never resolved, and the unit `b ≈ a` that R3 should deliver
existed only on the paths where it was derived before that clause. Ordered
resolution does not promise entailed units, only `⊥`; the equality part of
R2 puts the equality in the interface's downward-closed set and removes the
trap. With it the result no longer depends on the work order.

**`p2`, reference regime without any internal disjunction**
(`engine/tests/fixtures/nominal_seq_order/p2_cross_individual_named.ofn` and
its swapped variant): `⊤ ⊑ B ⊔ NB`, `∃r.NB ⊑ C`, `C ⊓ D ⊑ ⊥`, `D(a)`,
`r(a,b)`, `Q ⊑ {b}`; HermiT: `Q ⊑ B`. `p1` itself selects the Sequoia order,
because its clausification of `∃r.¬B ⊑ C` puts the internal `Q_1` into a
disjunction (`→ B(x) ∨ Q_1(x)`), so it never exercised the unordered default.
`p2` has only the named disjunction `B ∨ NB`, the router leaves the Sequoia
order off, and before the base context regime it was missed on `nominals` and
`certified_nominals` (the automatic route answered it on another arm).

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

Nominal mode always carries R2 and R3. `set_seq_order_auto` selects the
context regime (`KM_SEQ_ORDER=context`, `SEQ_ORDER_CONTEXT`: R1 + R2 + R3)
wherever the plain Sequoia ordering would be selected without nominals, and
the base context regime (`SEQ_ORDER_BASE_CONTEXT`: the unordered same-term
order + R2 + R3) everywhere else in nominal mode; `KM_NO_SEQ_ORDER` in nominal
mode also means the base context regime. The one exception is a run that must
publish a CB Lean certificate (`KM_CB_LEAN_REQUIRED`): the certification
surface models the literal order (`CBSourceHyperClosure.predLe`) and the r-Pred
guard (`CBRootPredSendEnumeration`, exact send sets) of the plain unordered
regime, so a certificate with R2 or R3 would be rejected. Those runs keep the
plain unordered regime, the configuration the checker models, and that
configuration is known to miss `p1` and `p2` (section 4). `KM_SEQ_ORDER=1`
(plain Sequoia, incomplete under nominals) remains a diagnostic override.

- **R1.** In every context, same-term concept literals on a variable or a
  Skolem term (`x`, `f(x)`, `f(o)`) use the Sequoia order: internal concepts
  totally ordered above the named ones, named concepts incomparable.
- **R2.** In every context, a ground atom (every argument a named individual
  or an additional nominal) lies below another ground atom only if its
  individuals are among the other's, and never below a ground equality
  `o ≈ o'`; every other such comparison is removed. (R3 makes a ground
  equality an interface atom of a context that announced only one of its two
  individuals, so nothing outside that interface may lie below it.) Ground
  atoms over the same individuals keep the Sequoia order (so `→ C(o) ∨ __data__(o)` still resolves only on the
  maximal disjunct), and comparisons with every other literal are unchanged.
  R2 only removes strict comparisons, so every clause keeps at least the
  maximal literals it has without R2. That does not make the outcome
  monotone in the order: the guard's consumers depend on units that ordered
  resolution need not derive, and section 4 (seed297_min) shows a weakening
  that lost an answer. R2 is switched on
  only when some ontology clause with a variable or a Skolem term mentions an
  individual (`reasoner::has_ground_interface`, `calc::set_ground_interfaces`).
  Without such a clause no context other than the ground context ever holds a
  ground atom: its clauses come from individual-free ontology clauses, Succ
  and Pred introduce only `x`, `y` and `f(x)`, the ground context delivers
  only to contexts with an individual-labelled edge or a merge subscription,
  and both need a clause that already mentions the individual (argued from
  the engine code, not mechanised). The guard then delivers nothing, every
  interface is empty, and the ground context matters only through its own
  refutation, which ordered resolution finds under any order. The switch is
  fixed per engine, because clause maxima are cached; the retained
  incremental path refuses an insertion that would flip it.
- **R3.** The ground context delivers a unit ground equality `→ o ≈ o'` to a
  context that announced `o` or `o'`, not only to one that announced both.
  The receiving context rewrites with it, its merge clause then names the
  other individual, and the merge subscription extends its interface. R3 is
  an instance of the paper's r-Pred with `n = 0`, hence sound.

The literal order is the same in every context: it depends only on the
literals compared. R2 acts where ground atoms occur, which is mainly the
ground context; R1 keeps the Sequoia order on the ground context's
`x`-clauses. The literal reading of "unordered in the ground context only" was
measured and rejected (section 7): it keeps the cost, and it does not remove
`p1`, because the reference order compares ground atoms across individuals
(term-major) and is therefore not consequence-finding for every interface.
A first version of R2 that made all ground atoms pairwise incomparable was
also rejected: it removes `p1` but restores the per-individual disjunction
blow-up of the ground context (ore_ont_10874 ran past 222 s, against 10 s
under the plain Sequoia ordering, before the run was stopped).

## 6. Completeness: what is proved, argued, and open

- **Proved (Lean, ground level).** The exchange between a ground context that
  satisfies R2 and a consumer with any order, for any announced interface.
  This covers the context and the base context regime alike: R2 is stated on
  top of whichever same-term order is in force, and both the Sequoia and the
  unordered same-term order compare ground atoms only when they are on the
  same individual or along the term-major order that R2 filters.
  Take as server the equality-free, `x`-free clauses of the ground context:
  their atoms are ground atoms, which R2 orders only along inclusion of
  their individual sets, and atoms on Skolem terms `f(o)`, which the
  term-major order puts above every ground atom. On these atoms KM's
  relation is a strict partial order (the Sequoia/term-major order is; R2
  keeps a comparison `A < B` only when the individuals of `A` are among those
  of `B`, which composes; this step is argued from `calc::pred_lteq`, not
  mechanised), and every comparison that ends at an interface atom starts at
  an interface atom. `downward_server_complete` then gives completeness of
  the exchange; its lemma `exists_rank_extending_lower` builds the linear
  extension with the interface at the bottom
  (`unordered_server_complete_for_every_interface` is the special case of a
  server without any order). The positive unit readout is
  `exchange_unit_readout_complete`. This covers the two-regime exchange
  itself, not only the single-order case. (Literals with `x` can sit between
  two ground atoms in the term-major order, `B(o1) < r(x,o2) < C(o3)`, and
  ground equalities likewise; they are not atoms of the server clause set, so
  they impose no comparison there.)
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
  delivered, and no proof covers that case. (Superseded 2026-10-30: the case
  has counterexamples, and section 8 extends R3 and R2 and mechanises the
  propositional skeleton with equality atoms.) The first-order lifting of the
  context calculus (Skolem terms, Pred/Succ, Join, Nom) is the same open
  obligation as for the single-order case (lean/README.md, "What is NOT
  claimed"; docs/CERTIFICATION-ROADMAP.md).

The claim is therefore: the context regime meets the ground-level standard of
`CompletenessOrdered.lean`, extended by a proved exchange theorem for two
different orders, and it removes both known counterexamples. It is not a
first-order completeness proof, and the equality gap of the guard remains.

## 7. Measurements and rejected variants

Numbers: docs/NOMINALS-CB.md section 9 and
`results/agents/2026-10-29/per-context-order/`.

Rejected variants, measured:

- *Unordered in the ground context, Sequoia elsewhere* (the original
  proposal). The ground context's own work is the cost: on the bug-1
  reproducer the ground context ends with 22 762 worked-off clauses when every
  non-query context is unordered, exactly as many as under the fully
  unordered regime, against 1 544 under the plain Sequoia ordering
  (`km classify`: 100 s with only the query contexts ordered, 0.17 s plain
  Sequoia; `km engine`: 158 s unordered). The
  variant with only the query contexts ordered was measured; the ground
  context alone was not isolated, the count shows where the time goes.
- *Same-term ground literals unordered, nothing else* (`KM_EXP_GROUND_FREE`
  of the 2026-10-28 attempt). Fast (0.18 s on bug 1) but still loses seed 297:
  the loss is the guard, not the order on one individual.
- *R2 with all ground atoms pairwise incomparable.* Removes `p1`, but
  restores the per-individual disjunction blow-up in the ground context
  (`ore_ont_10874` and `ore_ont_9800` past 300 s at engine level).
- *R2 without its equality part.* Loses seed297_min on the `nominals` route
  depending on the work order (section 4).
- *R1 + R3 without R2.* Fast and answers seed 297, but misses `p1` on the
  `nominals` and `certified_nominals` routes, like the unordered regime.

HermiT differential under the context regime (60 s cap per run; routes
`auto`, `nominals`, `certified_nominals`; every run that was not `ok` rerun
with `KM_NO_SEQ_ORDER=1`):

| set | runs | ok | wrong | timeout | no answer (RSS limit) |
|---|---|---|---|---|---|
| sorts_differential fixtures (11) | 33 | 33 | 0 | 0 | 0 |
| generated, no inverse roles (400) | 1200 | 795 | 3 | 395 | 7 |
| generated, with inverse roles (100) | 300 | 215 | 0 | 85 | 0 |
| ALCHIQ seeds `sq/` (300) | 900 | 883 | 0 | 14 | 0 |

The three wrong runs are `m2197` on every route: KM reports the ontology
inconsistent, HermiT consistent; the unordered regime gives the same wrong
answer in 0.02 s, so the context regime does not cause it (it is outside the
CB ordering; the file has `SubClassOf(owl:Thing ObjectOneOf(:a))` next to data
properties). Of the 494 timeouts and 7 RSS-limit stops, 480 also fail under
the unordered regime; 21 runs on 9 files answer under the unordered regime
within 60 s (`m2063`, `m2100`, `m2215`, `m2229`, `m2276`, `m2296`, `m2303`,
`n1052`, and `g56` on `nominals`, where R2 is off because the file has no
individuals). No run answered differently from HermiT under the context
regime where the unordered regime answered correctly. Three `sq/` runs
(`g282`) have no HermiT answer within 300 s.

Revalidation after the base context regime (same harness, binary at commit
a689c42b): the new rule changes the selected regime only where nominal mode
runs with `has_internal_definer_disjunction` false and the ontology has
individuals. By the `km ofn` clause sets that is no file of the 201 gated ORE
inputs (the sort encoding always adds an internal disjunction), no
no-inverse seed, one inverse-role seed (`n1089`, answered as before) and none
of the ALCHIQ seeds with individuals (they have none).

| set | runs | ok | wrong | timeout | no answer |
|---|---|---|---|---|---|
| sorts_differential fixtures (11) | 33 | 33 | 0 | 0 | 0 |
| ALCHIQ seeds `sq/` (300) | 900 | 881 | 0 | 15 | 1 |
| generated, with inverse roles (100) | 300 | 214 | 0 | 85 | 1 |
| generated, no inverse roles, first 128 of 400 | 384 | 255 | 0 | 125 | 4 |

The no-inverse rerun was stopped after 128 files because none of the 400
changes regime; the earlier run stands for the rest. Against the earlier
context-regime run, 9 runs went from `ok` to timeout and 6 from timeout to
a stop; every quick case among them (`g56`, `m2078`, `m2093`, `n1001` on
`certified_nominals` or `auto`, 0.02 s before) answers again in 0.02 s on a
rerun with both binaries, and the others were within 20 s of the cap before
(`g1` 59 s, `m2040` 42 s, `m2079` 57 to 58 s), so these are load effects of
the shared machine. No run answered differently from HermiT.

Cost of R2 where it is active: on `m2063` the automatic route takes 2.4 s
unordered, 12 s plain Sequoia, 12.8 s with `KM_CONTEXT_NO_R2`, and more than
40 s under the context regime. R2 widens Hyper joins over ground atoms of
different individuals; the other eight slower files were not analysed.

## 8. Disjunctive ground equalities across an unannounced individual (2026-10-30)

v1.5.4 listed this case as open ("not covered by R3, no counterexample
known"). It has counterexamples, and the fix extends R3 and R2.

### 8.1 The question, from the code

- *Announced.* Context `u` announced individual `o` when the ground context
  holds an edge `(u, o)` in its predecessor map: an r-Succ push of a maximal
  ground head atom `B(o)`, `S(x,o)` or `S(o,x)` of `u`
  (`root_succ_form`), or a merge subscription for a merge clause
  `Γ → Δ ∨ x ≈ o` of `u` (`subscribe_merge_individuals`). Additional
  nominals count as announced.
- *Guard.* The ground context delivers an `x`-free clause to `u` when every
  body atom is discharged by a hypothesis `u` pushed and every individual the
  clause mentions is announced by `u` (`propagate`, ground-sender branch;
  `subscribe_merge_individuals` for body-free clauses).
- *R3 in v1.5.4.* The unit `→ o ≈ o'` passes when `u` announced `o` or
  `o'`. Nothing else with an unannounced individual passes.
- *The open case.* A ground-context clause `Γ → Δ ∨ o ≈ o'` with `Δ ≠ ⊥`
  and `u` announcing `o` but not `o'`: not delivered. Its shapes in KM's
  clause sets: `→ E(o) ∨ o ≈ o'` (Hyper on an at-most clause `≤1 r.B` of a
  third individual `p` with `r(p,o)`, `r(p,o')`, and the disjunction `B(o) ∨
  C(o)`), `→ M(p) ∨ o ≈ o'` (`p: ≤1 r ⊔ M`), and `→ o ≈ o' ∨ o1 ≈ o2`
  (`p: ≤1 r ⊔ ≤1 s`). In the propositional reading of section 3 the
  equality `o ≈ o'` is an interface atom of `u` (R3 makes it one), so a
  clause whose atoms are all interface atoms must be delivered
  (`ExchangeCond.deliver`). The unit-only R3 violates that condition.

### 8.2 Counterexamples (HermiT-checked, exact `nominals` route of v1.5.4)

`results/agents/2026-10-30/r3-unannounced/`, generator `gen_tpl.py`; each
motif with random individual names, shuffled axiom order (hence interning
order and equality orientation) and up to three noise axioms. Fixtures in
`engine/tests/fixtures/nominal_seq_order/r3_*.ofn`, test
`engine/tests/r3_disjunctive_equality.rs`.

- **m1** (`r3_m1_atmost_qualified.ofn`): `e: ≤1 r.B`, `r(e,a)`, `r(e,d)`,
  `B(d)`, `D(d)`, `a: B ⊔ C`, `C ⊑ E`, `D ⊑ E`, `Q ⊑ {a}`; HermiT
  `Q ⊑ E`. The ground context saturates with `→ E(a) ∨ a ≈ d` and
  `→ E(a) ∨ B(a)`, `E(a)` maximal (when `a` is interned after `d`, the
  equality orients `a → d` and lies below `E(a)`), so ordered superposition
  never derives `→ E(a)`. The `Q` context announced `a` only and receives
  neither clause. Missed on `nominals` and `certified_nominals` in every
  literal-order regime (`KM_SEQ_ORDER=1`, `context`, `KM_NO_SEQ_ORDER`).
- **m4** (`r3_m4_atmost_union.ofn`): `b: ≤1 r ⊔ M`, `M ⊑ ∀r.E`, `r(b,c)`,
  `r(b,d)`, `D(c)`, `D ⊑ E`, `Q ⊑ {d}`; HermiT `Q ⊑ E`; the ground context
  resolves `M(b)` and keeps `→ E(d) ∨ d ≈ c`.
- **m6** (`r3_m6_private_equality.ofn`): `f: ≤1 r ⊔ M`, `M ⊑ ∀s.E`,
  `s(f,d)`, `r(f,b)`, `r(f,c)`, `b ≠ c`, `Q ⊑ {d}`; HermiT `Q ⊑ E`. The
  ground context keeps `→ E(d) ∨ b ≈ c` with `b ≈ c` below `E(d)`
  (term-major, `b, c` interned before `d`), so the equality is never
  superposed into `b ≉ c`. The equality is about two individuals `Q` never
  announced: this is the propositional counterexample of section 3
  (`ordered_server_interface_not_lower_counterexample`) with a private
  equality below an interface atom. R2 as of v1.5.4 orders ground atoms
  against each other and keeps ground atoms off ground equalities, but lets
  an equality lie below an unrelated ground atom.
- **m7** (`r3_m7_two_equalities.ofn`): `c: ≤1 r ⊔ ≤1 s`, `r(c,d)`, `r(c,b)`,
  `s(c,a)`, `s(c,f)`, `f ≠ a`, `D(d)`, `D ⊑ E`, `Q ⊑ {b}`; HermiT `Q ⊑ D`,
  `Q ⊑ E`. The ground context keeps `→ b ≈ d ∨ a ≈ f` with the private
  `a ≈ f` below the interface equality `b ≈ d` (equalities compared
  lexicographically).

Counts on v1.5.4 (`km-pgo-use`, exact `nominals` route): see 8.5.
None of the motifs depends on inverse roles; m5 (inverse-functional roles)
and m2, m3 are answered by v1.5.4.

### 8.3 The fix

- **R3 (the guard delivers the announced interface).** A clause passes the
  guard when each of its literals lies in the interface of the receiver: a
  ground equality or inequality `o ≈ o'` / `o ≉ o'` between individuals
  when `o` or `o'` is announced, every other literal when all its
  individuals are (`engine::in_announced_interface`, both delivery paths).
  The unit `→ o ≈ o'` is the special case R3 covered before. The receiver
  rewrites `o` to `x`; `→ Δ ∨ x ≈ o'` is a merge clause, its merge
  subscription announces `o'`, and Join case 3 brings the facts about `o'`
  across. A first version admitted every individual reachable through the
  clause's equalities (so also `→ C(o') ∨ o ≈ o'`); it delivered more than
  the interface and was slower (section 8.5).
- **R2 for equalities.** A ground equality or inequality between individuals
  lies below another ground (in)equality only when both are over the same
  two individuals, and below a ground atom only when it shares an
  individual with that atom (`calc::lteq`, `ground_eqn_pair`). With the
  existing parts of R2 (a ground atom lies below a ground atom only when its
  individuals are among the other's, and never below a ground equality),
  every announced interface, equality atoms included, is downward closed.
  The rule only removes comparisons.
- Both act only where R3 and R2 act (nominal mode, context and base context
  regimes; R2 additionally needs `has_ground_interface`). The diagnostics
  `KM_CONTEXT_UNIT_R3` and `KM_CONTEXT_NO_EQ_R2` restore the v1.5.4 rules.
- The certified CB surface (`KM_CB_LEAN_REQUIRED`) keeps the plain unordered
  regime and the exact v1.5.4 send sets that `CBRootPredSendEnumeration`
  models; it is unchanged and remains outside this argument (section 5).

### 8.4 Exactness argument

*Soundness.* The extended R3 delivers a subset of what the paper's r-Pred
with `n = 0` delivers (every ground clause to every context), so every
delivered clause is a consequence. R2 for equalities changes which literals
are maximal, never what an inference concludes. Neither part can make an
answer unsound.

*Completeness, propositional skeleton (mechanised).* Read ground equalities
as atoms: an (in)equality between `o` and `o'` is one atom with individuals
`{o, o'}`, an inequality in a head its negative literal. For a context that
announced `I`, the interface is the ground atoms with all individuals in `I`
and the equality atoms with at least one side in `I`.
`lean/ContextCalculus/ExchangeEquality.lean` proves, sorry-free (axioms
`propext`, `Classical.choice`, `Quot.sound`):

- `filt_trans`: R2 (all three parts) applied to a strict partial order
  yields a strict partial order;
- `iface_downward`: for every `I`, the interface is downward closed in the
  filtered order (this is where the two equality comparisons must go: m6 and
  m7 are the two ways it fails without them);
- `exchangeCond_of_guard`: a ground context that delivers every clause
  passing the guard (`InIface`, the literal-wise interface test that
  `in_announced_interface` implements) meets `ExchangeCond.deliver`; the
  unit-only guard does not (m1, m4); `inIface_of_all_announced`: the guard
  extends the v1.5.4 guard;
- `announced_exchange_complete`, `announced_unit_readout_complete`: with the
  ground context closed on maximal literals of the filtered order and the
  consumer closed under any rank, the exchange is refutationally complete and
  complete for the positive unit readout, for every announced set, via
  `downward_server_complete` and `exchange_unit_readout_complete` of
  section 3.

*What remains argued.* (1) Congruence: the theorem treats equalities as
opaque atoms. The receiving context does not need the ground context's
congruence closure over `o'`, because the extended guard delivers the clause
itself and the receiver's Eq rule and merge subscription reconstruct the
consequences over `o'`; that step is the existing (unmechanised) Eq, Join
case 3 and merge-subscription argument. (2) `ExchangeCond.local_`: an atom
the consumer holds outside its interface does not occur in the ground
context; a delivered clause can mention `o'` only through an equality
literal, which turns into a merge clause and announces `o'`, so at the
fixpoint the interface contains it (argued from the engine code, as item (b)
of section 6). (3) That KM's literal relation on the ground context's
`x`-free atoms is a strict partial order and that the ground context is
closed on its maximal literals (as in section 6). (4) Equalities with a
Skolem side `o ≈ f(o')` are outside the filter; they lie above every ground
literal in the term-major order and never enter an announced interface.

*Lean obligation created.* The new module is mechanised. The certified
surface does not model R2 or R3 (unchanged from section 5); extending
`CBSourceHyperClosure.predLe` and `CBRootPredSendEnumeration` to the context
regime remains open.

### 8.5 Measurements

`results/agents/2026-10-30/r3-unannounced/` (README there has the exact
binaries and commands). Routes forced to `nominals` (exact, no
`KM_ALLOW_APPROXIMATE`); HermiT 1.4.3.456 as oracle. "Same binary" means the
fixed binary with `KM_CONTEXT_UNIT_R3=1 KM_CONTEXT_NO_EQ_R2=1`, which
restores the v1.5.4 rules; v1.5.4 itself is the PGO release binary
`.work/pgo-v154/km-pgo-use`, faster by about a quarter for build reasons
alone. The workstation ran at load 75 to 100 throughout.

| set (seeds) | cap | v1.5.4 | same binary, v1.5.4 rules | fix |
|---|---|---|---|---|
| motifs m1 to m5 (2,000) | 20 s | 1,520 ok, 480 wrong | | 1,999 ok, 0 wrong, 1 timeout |
| motifs m6, m7 (1,000) | 20 s | 842 ok, 155 wrong, 2 timeouts, 1 no gold | | 997 ok, 0 wrong, 3 timeouts |
| random `gen_r3.py` (4,000) | 10 s | 2,217 ok, 4 wrong, 1,631 timeouts, 148 other | 2,259 ok, 6 wrong, 1,732 timeouts, 3 errors | 2,205 ok, 4 wrong, 1,761 timeouts, 30 errors |
| `gen_nomdata.py` 1000-1099, 2000-2199 (300) | 30 s | | 183 ok, 0 wrong, 117 timeouts | 186 ok, 0 wrong, 114 timeouts |
| sorts_differential fixtures (11 x 3 routes) | 60 s | | | 33 ok |

Errors are workers killed by the host's exhausted commit limit (rerun, they
answer); "other" for v1.5.4 are seeds without a cached HermiT answer at the
time.

*Wrong answers that remain.* `r1600`, `r1646`, `r3403`, `r3602` miss one
subsumption each on the `nominals` route under every rule set, with the
announcement guard switched off as well (`KM_CONTEXT_NO_GUARD=1`), so they
are not guard losses and are outside this section. `r1600` (`B ⊑ A`) is also
missed on the automatic and `certified_nominals` routes; the other three are
answered there. Copies: `open_r*.ofn` with their HermiT answers in the
results directory. `r673` and `r3351`, wrong under the v1.5.4 rules, are
instances of this section's case and time out under the fix (900 s at engine
level for `r673`).

*Cost.* On the 2,186 random seeds both rule sets answer within 10 s, the
fix takes 1.21 times as long in total (median ratio 1.13). Of the 73 seeds
the v1.5.4 rules answer and the fix does not, a paired rerun at 60 s has 33
answered by both, 36 only by the v1.5.4 rules, 1 only by the fix and 3 by
neither;
`r129` goes from 0.03 s to past 60 s. The ablations
(`KM_CONTEXT_UNIT_R3`, `KM_CONTEXT_NO_EQ_R2`) put the cost on R2 for
equalities: with the new guard alone `r129` takes 0.03 s and `r274` 0.10 s,
with the new R2 alone 42 s and 44 s. Equalities that R2 no longer keeps below
unrelated ground atoms become maximal and superpose into every clause over
their larger individual. The first version of the guard (an individual passes
when it is reachable through the clause's equalities) cost more: `r3351`
past 10 s with that guard alone. On `gen_nomdata.py` the fix is not slower
(183 seeds answered by both, total 199 s against 219 s).

*ORE, the paired design's nominal inputs.* The 112 inputs of the design half
of `results/benchmarks/2026-10-26-v154-routing/split.json` among the 201
gated nominal inputs of 2026-10-29, one process per stream, three streams
side by side. Automatic route, 300 s: the fix and the same binary with the
v1.5.4 rules answer 104 common inputs with identical SUB/UNSAT/CONSISTENT
lines, total 920 s against 964 s (mean ratio 0.946, median 0.950); 9800
(ht_bridge, 235 s under the old rules) and 11270 (certified_nominals, 130 s
under the fix) each crossed the cap once and answer on a rerun at 600 s under
both rule sets (9800: 241 s fix, 473 s old rules; 11270: 90 s fix, 32 s old
rules). Against v1.5.4 the fix answers the same inputs with identical lines
except 9800, at mean ratio 1.34 and median 1.24, the gap of the non-PGO
build: the same binary with the v1.5.4 rules is at 1.47 and 1.28. Forced
`nominals` route, 120 s: both rule sets answer the same 76 inputs with
identical lines, total 236 s against 239 s under the v1.5.4 rules (mean
ratio 0.978, median 0.974); the same 35 time out under both and one exits 3
(forced route cannot represent it) under both. No input of the paired design
changes its answer, and the cost seen on the random generator does not show
there.

## 9. Seed and ORE coverage at the base of v1.5.5 (2026-10-30)

At 87fda54f (the context regime merged), the automatic route on the 400
generated seeds without inverse roles (seeds 2000-2399, 60 s cap, 3
workers, shared workstation at load 50 to 100) answered 270 and timed out
on 130, with no wrong answer. Rerun with `KM_NO_SEQ_ORDER=1` (the base
context regime, unordered same-term order with R2 and R3) the 130 timeouts
gave 4 answers within 60 s, all equal to HermiT's: `m2063` (5.5 s), `m2100`
(15.0 s), `m2276` (1.1 s) and `m2303` (14.7 s). So the cost of the Sequoia
same-term order plus R2 accounts for 4 of the 130; the other 126 time out
in both regimes (docs/NOMINALS-CB.md, "Inert object sorts in the nominal
CB input (2026-10-30)", for their cause). Both regimes are complete to the
same standard (section 6), so a portfolio that runs the base context regime
beside the context regime would be exact; it was not built, because on one
core the two arms would share the CPU and the gain is four generated files.
Measurements: `results/agents/2026-10-30/nominal-coverage/`.

ORE 9800 and 10874, which the 2026-10-28 amendment set aside, are answered
under the context regime: 10874 in 3 to 5 s on the benchmark nodes (IBEX,
one core, 240 s) with the v1.5.4 binary of design run 9 and with 87fda54f.
9800 was not: with the protocol flags it answered in 2 of 4 runs (184 s)
with run 9's binary and in 1 of 4 (191 s) with 87fda54f, the others
reaching 240 s. Its CB engine needs about 95 s alone and shares the core
with the typed-nominal bridge, which needs as long; the merged base with the
R2/R3 fix of 7c238e52 answered 2 of 4 (205 s). The remedy is in the CB input,
not in the ordering: with it 9800 answers in 14 s on 4 of 4 runs
(docs/NOMINALS-CB.md, same subsection).

## 10. The data-sort marker in the order, and the stop at a global refutation (2026-10-30, agent `data-values-2`)

ore_ont_7610 (548 class and 1,058 property assertions, 613 data
assertions, inconsistent: every element needs a `has_factor` successor,
which is a `Disorder` and an `Organism ⊔ Material` at once) ran past 600 s
on the nominal CB routes; v1.5.3 answered it in 57 s because its frontend
did not yet emit the sort encoding (NOMINALS-CB.md section 6) for an input
with data properties but no data value. Two changes:

**Marker order.** Internal concepts are totally ordered by concept id in
the Sequoia regimes, and ids follow first occurrence in the clause stream.
`__data__` occurred early, so in `→ C(t) ∨ D(t)` the definer `C` was
maximal and `D(t)` rode along in every consequence of `C(t)`: the ground
context held 46,944 clauses after seeding, all with a `D(o)` literal that
no rule could remove, and every r-Pred arrival paid backward subsumption
against them. `reasoner::Builder::intern_data_sort_last` now gives the
marker the largest id (the relative order of every other concept is
unchanged) when the clause set mentions at least 64 individuals. On an
individual `o`, pinned to the object sort, Hyper then resolves the maximal
`D(o)` against `A(o)` and `A ⊓ D ⊑ ⊥` at once, and `→ C(o)` subsumes the
relativized fact. Exactness: R1 asks for *a* total order on internal
concepts above the named ones; the ground ordered-completeness theorem
(`CompletenessOrdered.lean`, `ordered_completeness`) and the exchange
theorem (`CompletenessExchange.lean`) are stated for an arbitrary
`LinearOrder`, R2 filters ground atoms by their individuals and not by
concept, and the id order it replaces is itself an artefact of clause
order. The Lean terminal-state model (`CBSourceHyperClosure.lean`,
`sameTermConceptLe`) reads the order from the same ids, so certificates
stay consistent with it. The threshold is a speed choice between exact
orders: the generated seed `m2313` (three individuals) takes 0.2 s with the
first-occurrence order and 47 s with the marker last, and ore_ont_7610
does not finish in 400 s without the change.

**Stop at a global refutation.** Once the ground context, or the root
context of `⊤`, has worked off the empty clause, the ontology is
inconsistent and the published answer is the fixed inconsistent one
(empty taxonomy). Saturation is monotone and the empty clause subsumes
every clause, so `inconsistent()` cannot become false again; the remaining
messages only add clauses elsewhere. `Engine::set_stop_on_global_refutation`
ends `run_for` there; `Reasoner::saturate` enables it on its one-shot
paths and keeps it off for an engine retained for a CB certificate
(`KM_CB_LIVE_STATE`, `KM_CB_LEAN_REQUIRED`), which must stay saturated. On
ore_ont_7610 the ground context refutes after about an eighth of the
message work. No Lean obligation: the answer is the one the full fixpoint
gives.

ore_ont_7610: timeout at 600 s (v1.5.4, v1.5.5 before) → 38 to 63 s on the
loaded workstation, inconsistent, as Konclude, HermiT, Openllet and JFact.

**Empty-head subsumption indexes (later the same day).** After the merge of
the nominal CB input remedy (`50bf7ba9`, released inert sorts), ore_ont_7610
ran past 300 s again: its relativized facts become plain facts, the ground
context still holds about 49,000 clauses, and the r-Pred arrivals there are
mostly empty-head clauses. Backward subsumption of an empty-head clause read
every active clause of the context (3.5·10⁹ candidates in 32,000 calls in
the first 60 s), and forward subsumption read every active empty-head
clause. Both scans now read, once a context's delta layer holds 4,096
active clauses (respectively 4,096 empty-head clauses), an index built on
demand and maintained with the active index: every active clause under each
of its body predicates (`active_body_index`; a clause the incoming
empty-head clause strengthens contains all of its body predicates, so it is
in the rarest of their postings), and every empty-head clause under its
least body predicate (`empty_head_body_index`; an empty-head clause whose
body is a subset of the incoming body has its least body predicate in that
body, so each candidate is visited once). The base layer is read as before.
The candidate sets contain every clause the full scans would accept and the
exact `strengthens` test decides, so the removed and the rejected clauses
are the same; no calculus change, no Lean obligation.
`KM_NO_ACTIVE_BODY_INDEX` restores the scans and `KM_ACTIVE_BODY_INDEX_MIN`
sets the threshold (`1` exercises the indexes in every context; the
2026-10-30 A/B runs used it). ore_ont_7610 on the engine input: more than
200 s → 52 s; `km classify`: 64 s on the loaded workstation.

## 11. A ranked R2 for ground equalities (2026-10-30)

Section 8's R2 lets a ground (in)equality lie below another one only over
the same pair, and below a ground atom only when they share an individual.
`ExchangeEquality.lean` shows why this is the largest safe filter when the
interface must be downward closed for every announced set `I`: some context
may announce only one side of the upper equality. It costs time on random
inputs (section 8.5). Results and commands:
`results/agents/2026-10-30/nominal-r1600/`.

### 11.1 Where the cost is

Engine-level timings on the seeds of section 8.5 (diagnostic switches that
reopen one group of comparisons each, `KM_DIAG_EQEQ_OPEN`,
`KM_DIAG_EQATOM_OPEN`; incomplete, attribution only):

- `r129`: section-8 rules 39 s; equality-below-atom comparisons reopened
  31 s; equality-below-equality reopened more than 60 s; both reopened, or
  the v1.5.4 rules, 0.02 s. The two groups interact: a private equality
  that is maximal superposes into every clause over its larger individual,
  and the ground context replicates the conditional clauses of `Q_2(a)`,
  `Q_4(c)` (`a ≈ b ∨ a ≈ d`, `B(c) ∨ c ≈ e`) under each.
- `r274`: section-8 rules 27 s; equality-below-equality reopened 0.08 s.
- `fr248` (rule seed set, CB route): section-8 rules more than 60 s; both
  groups reopened under the section-8 guard still more than 60 s; the
  ranked R2 below with the unit-only guard of v1.5.4 5.7 s; v1.5.4 rules
  6.8 s. Here the deliveries of the extended R3 cost as much as the
  comparisons.

### 11.2 The ranked filter and its interface

Enlarging the interface on the equality side lets the filter keep more.
Fix a rank on individuals (KM: the term id) and give a receiver that
announced `I` the bound `m`, its largest announced individual. Two variants
are proved in `lean/ContextCalculus/ExchangeEquality.lean` (sorry-free,
axioms `propext`, `Classical.choice`, `Quot.sound`):

- *max rank* (`IfaceM`, `CompatibleM`, default in KM): an equality is an
  interface atom when a side is announced or both sides are at most `m`; it
  lies below another equality over the same pair or when its larger side is
  at most the other's smaller side; below a ground atom when it shares an
  individual or its larger side is at most an individual of the atom (KM's
  term-major order implies this, so KM keeps every equality-below-atom
  comparison of v1.5.4); no ground atom lies below an equality; ground
  atoms as in section 8.
- *min rank* (`IfaceR`, `CompatibleR`, `KM_R2_MIN_RANK`): an equality is an
  interface atom when its smaller side is at most `m`; it lies below another
  equality when its smaller side is at most the other's smaller side.

For both: the filter of a strict partial order is a strict partial order
(`filtM_trans`, `filtR_trans`), every interface with `m` covering the
announced individuals is downward closed (`ifaceM_downward`,
`ifaceR_downward`), the filter keeps every comparison of section 8's
(`compatibleM_of_compatible`, `compatibleR_of_compatible`), the guard
passes every clause section 8's guard passes (`inIfaceM_of_inIface`,
`inIfaceR_of_inIface`), and the exchange and unit-readout theorems hold
(`maxranked_exchange_complete`, `maxranked_unit_readout_complete`,
`ranked_exchange_complete`, `ranked_unit_readout_complete`). Code:
`calc::lteq` (equality pairs), `engine::in_announced_interface` (the bound,
computed per receiver in `propagate` and `Engine::rank_bound`). With
additional nominals present the bound is unbounded (they count as announced
for every receiver). `KM_CONTEXT_PAIR_R2` restores section 8's rules.

*Exactness.* Soundness is unchanged (the guard delivers a subset of what
the paper's r-Pred with `n = 0` delivers; the filter changes only which
literals are maximal). Completeness: the propositional skeleton is the
mechanised theorem above; the remaining steps are those of section 8.4
(congruence, locality, KM's order being a strict partial order on the
ground context's `x`-free atoms). The locality argument now also covers
equalities delivered because both sides are at most the bound: such a
clause reaches the receiver as a ground clause, its equality literals stay
ground there unless a side is the receiver's own individual, in which case
the merge subscription announces the other side.

*Lean obligation.* The new filter and interface are mechanised as above.
The certified CB surface still models neither R2 nor R3 (unchanged).

### 11.3 Measurements

`results/agents/2026-10-30/nominal-r1600/data/`, binary `km.v4` (max-rank
default; `KM_CONTEXT_PAIR_R2=1` gives section 8's rules in the same binary).
The merge hypotheses of docs/NOMINALS-CB.md section 10 are on in both.

- Seeds r0 to r999, 10 s, run side by side: ranked R2 531 ok, section-8 R2
  534 ok, both 0 wrong; on the 524 seeds both answer, 190 s against 232 s
  (median ratio 1.08 in favour of the ranked R2).
- The 36 seeds of section 8.5 that only the v1.5.4 rules answered, at 60 s:
  this build answers 10, km.final2 5 in the same window. `r673`, `r3351` and
  `fr248` time out at 60 s in both; `r129` takes 26 s in km.final2 and more
  than 60 s here.
- `r1600`'s `B` query with the merge hypotheses: 238 s under the ranked R2,
  more than 600 s under section 8's.
- 4,000 seeds, motif sets, ORE: docs/NOMINALS-CB.md section 10.4 (0 wrong;
  ORE output identical).

Verdict: the ranked R2 is exact (mechanised skeleton) and orders more, but
it is not the cheaper R2 the brief asked for. It recovers 10 of the 36 seeds
and `r274`, is faster on the seeds both rule sets answer, and helps under
the merge hypotheses, but it does not recover `r129`, `r673`, `r3351` or
`fr248`. 11.1 shows why: the equality comparisons that matter for `r129` and
`fr248` need deliveries that cost as much as the comparisons save, since a
receiver that gets the extra equalities derives ground atoms that ordinary
r-Succ pushes back to the ground context as hypotheses. A cheaper exact
regime has to change that exchange (for instance, let a receiver fire
grounded ontology instances itself instead of pushing the atoms back); it
needs its own completeness argument.

## 12. The stop at a global refutation and the throwaway ⊤ closure (2026-10-31, agent `alchiq-regression`)

**Defect.** From b88c6253 (section 10) on, the automatic route answered
`CONSISTENT 1` on seeds 621, 1014 and 1022 of the 2026-10-29 ALCHIQ seed
set; HermiT finds all three inconsistent. The CB engine answers there (the
HT-first phase gives no answer), and the engine worker alone reproduces it
(`km engine` reports `"inconsistent":false` with `KM_THREADS=1` and 4). The
merge hypotheses, the ranked R2, the Horn cache gate, the bridge object
guard and the subset-blocking change are not involved: their switches leave
the answer wrong, and 8bbbf1f2 (the r1600 engine change on the
nominal-seeds base) answers all three correctly, while b88c6253 alone
answers all three wrongly.

In each seed the ontology facts alone refute `⊤` (621: `C ≡ ¬(C ⊓ B)` and
`⊤ ⊑ B`; 1022: `⊤ ⊑ B` with `B` disjoint from `⊤`; 1014: `⊤ ⊑ ≥2 t.B`
with `t` functional). The first query root context attaches the shared
root base (`attach_shared_base`), which `ensure_shared_root_closure`
computes by saturating a throwaway root context with an empty core and the
ontology facts only, then pops from `contexts`. That throwaway derives the
empty clause, and the test of section 10 (root context, empty core) sets
`global_refutation`. The stop then ends `run_for` after the first query,
before the `⊤` context is created. `Engine::inconsistent` scanned the
remaining contexts for a root context with an empty core, or the ground
context, holding the empty clause; neither exists, so the engine reported a
consistent ontology with a partial taxonomy. Before b88c6253 the `⊤`
context was always created, it inherits the same closure as its base, and
the scan found the empty clause there.

**Fix.** `Engine::inconsistent` returns true when `global_refutation` is
set, before the scan. One line of logic (engine.rs, `inconsistent`), plus
comments.

**Exactness.** The flag is set only when a context worked off the empty
clause and that context is the ground context or a root context with an
empty core. The throwaway context is the closure the `⊤` context is
seeded with: the same facts, no core clause, the same rules, and the `⊤`
context's clause set contains it. Its empty clause is therefore the
refutation of `⊤` that the `⊤` context derives on the full fixpoint, a
sound derivation of the calculus, and the ontology has no model. The other
contexts that set the flag are exactly those the scan already accepted, so
the flag never says inconsistent where the full fixpoint says consistent.
Incremental additions (`Engine::add_clauses`) are monotone, so a set flag
stays valid; the engine has no retraction. Conversely, a run that stops
does so only because the flag is set, so after this change every stopped
run reports inconsistent, and a run that does not stop is unchanged except
that a refutation in the throwaway closure is reported even if the `⊤`
context would only derive it later (the answer of the full fixpoint).

**Lean obligation.** No calculus rule, order or redundancy test changes,
so no rule needs re-certification. The readout `Engine::inconsistent` is
outside the mechanised boundary (docs/history/LEAN-BOUNDARY-AUDIT-2026-10-27.md),
as it was before. The obligation the fix relies on, stated for a future
boundary extension and not proved here: a clause worked off in a context
whose clause set is contained in the `⊤` context's clause set (the throwaway
closure) is in the saturated `⊤` context, so the empty clause there is the
refutation of `⊤` that the per-rule soundness of the calculus
turns into the absence of a model. Certified runs keep the stop off
(section 10) and create the `⊤` context as before, so a CB certificate
still carries the empty clause in a context the checker reads.

**Tests.** `engine/tests/global_refutation_closure.rs`: the three seeds and
their axiom-minimised forms (3, 4 and 3 axioms; reduced while 0e1bd99a
still answered consistent and 38173913 inconsistent, then checked against
HermiT), on the automatic route and on the engine worker, `KM_THREADS` 1
and 4. Measurements: `results/agents/2026-10-30/alchiq-regression/`.

## 13. Taxonomy rows of a stopped inconsistent run (2026-10-31, agent `incremental-ht-regression`)

**Defect.** The routing certification gate failed
`incremental_ht_reasoning::ht_reuses_existential_graphs_and_rechecks_global_deletion`
from 0e1bd99a on. The HT session was right; the fresh CB oracle it is
compared with was not. After the step that adds the empty clause (`⊤ ⊑ ⊥`)
to `A ⊑ ∃R.B`, `B ⊑ C`, the session answered every class below
`owl:Nothing`, and `classify_cb_fresh` answered
`{A: [owl:Nothing]}` with no rows for `B` and `C`. At 0e1bd99a the CB
oracle also reported the ontology consistent (the throwaway ⊤ closure of
section 12); after section 12 the flag is right and the rows are still
missing. The subset-blocking, object-guard and r1600 merges are not
involved: the HT answer is unchanged by them, and the CB rows come from
b88c6253 (section 10), which is in 0e1bd99a and not in 8a417f98.

Cause. The one-shot paths of `Reasoner::saturate` stop at a global
refutation (section 10). The sequential engine ends `run_for` before it
creates or finishes the root contexts of later queries, a static chunk
engine does the same per chunk, and a work-stealing worker stops claiming
queries. `Engine::subsumptions` reads only root contexts that exist, so the
rows of the other queries were missing or lacked `owl:Nothing`, and which
rows were present depended on the schedule. `km classify` publishes the
consistency flag and is unaffected in its verdict; the rows matter to every
reader of the CB taxonomy without the flag: `classify_cb_fresh`, which is
both the incremental CB snapshot backend (`CbBackendState::Snapshot`) and
the exact-rebuild oracle, the `km engine` worker's `subsumptions`, and the
incremental `IncrementalResult` rows (the HT adapter's
`result_from_inconsistent_queries` shape lists every query below
`owl:Nothing`).

**Fix.** `Reasoner::complete_inconsistent_rows` (reasoner.rs): after a
one-shot path (sequential without a retained certificate engine, static
chunks, work stealing) has absorbed every engine's answer, a run that
reports inconsistent and complete gives every requested query (after
`KM_QUERIES`/`KM_QUERIES_FILE`/prefix filtering, before the
mutual-unit collapse) the row entry `owl:Nothing`.

**Exactness.** An inconsistent ontology has no model, so every concept is
unsatisfiable and each added `owl:Nothing` is entailed. Every other row
entry was derived by the calculus as before. The rows no longer depend on
where the run stopped. The flag is unchanged, a consistent run is
unchanged (the completion reads the flag), an incomplete run is unchanged
(it is never published), and an engine retained for a CB certificate does
not stop and is not touched. No rule, order or redundancy test changes.

**Lean obligation.** None on the calculus. The readout is outside the
mechanised boundary, as `Engine::inconsistent` is (section 12). The fact
the completion uses, "no model implies every concept is unsatisfiable", is
the definition of entailment; a future boundary extension that covers the
taxonomy readout of an inconsistent run must state it for the published
rows. Certified runs keep the stop off and are not affected.

**Tests.** `engine/tests/inconsistent_cb_rows.rs` (the ontology of the
failing test and a 43-class variant, `KM_THREADS` 1 and 4, dynamic and
static schedule; a consistent control) and the whole
`incremental_ht_reasoning` suite. Measurements:
`results/agents/2026-10-30/incremental-ht-regression/`.
## 14. Hypotheses, merge hypotheses and the exchange cut (2026-10-31, agent `nominal-exchange`)

Section 11 and docs/NOMINALS-CB.md section 10.4 left two costs: the merge
hypotheses (22 of 724 random seeds lost at 10 s, `r1536`, `r3777`, `r1600`,
`r1646` past 60 s on forced `nominals`) and the R2 seeds `r129`, `r673`,
`r3351`, `fr248`. Results: `results/agents/2026-10-31/nominal-exchange/`.

### 14.1 Where the cost was

On `r5` (`C ⊑ {b, e}`, `e ∈ {a, d}`) the ground context exploded inside a
single saturation (400,000 superposition results after 10,000 work-offs).
Its labels were the four merge hypotheses `C(o)` and twenty further
hypotheses such as `Q_0(d)`, `__nom__b(d)`, `B(d)`. The query context
received `C(d) → Q_0(d)`, Join case 3 turned it into `⊤ → Δ'' ∨ Q_0(d)`,
`Q_0(d)` was maximal, and ordinary r-Succ pushed `Q_0(d) → Q_0(d)` back.
The ground context then repeated, under `Q_0(d)`, all the reasoning it had
already done under `C(d)`, sent the results back, and the next ground atom
was pushed. Every ground head atom of a delivered clause started another
round. On `r129` and `fr248` the same push-back follows the extra equality
deliveries of R3.

### 14.2 The cut

`Engine::rsucc_covered`: the r-Succ push of the maximal ground atom `a` of a
receiver clause `c = Γ → Δ ∨ a` is skipped when the ground context holds a
worked-off clause `e` such that

- every head literal of `e` is a head literal of `c`, and
- every body atom of `e` is a hypothesis the receiver pushed (an edge
  `(u, o)` of the ground context whose pushed set holds it) and is either
  a body atom of `c` or a merge hypothesis `K(o)` of the receiver with a
  body-free bridge `⊤ → Δ'' ∨ x ≈ o` whose other literals are head
  literals of `c` other than `a`.

A clause the receiver got verbatim is covered by itself; a Join case 3
result is covered by the clause it came from. `Engine::merge_hypothesis_covered`
applies the same test to the Join case 3 clause `⊤ → Δ'' ∨ K(o)` before
pushing a merge hypothesis: a bridge `x ≈ a` that the receiver derived from
the bridge `x ≈ d` and a ground `a ≈ d ∨ Φ` is covered by the ground
context's `K(d) → K(a) ∨ Φ`. `KM_NO_EXCHANGE_CUT` disables both,
`KM_NO_MERGE_CUT` only the second, `KM_DIAG_CUT` prints the uncovered
pushes. The cut is off under the experimental root-dependent orders
(`KM_ROOT_ORDERED`, `KM_ROOT_ONLY_INCOMP`).

### 14.3 Exactness

*Soundness.* The cut only omits hypotheses `A → A` (tautologies); fewer
premises cannot add a conclusion.

*Completeness, propositional skeleton (mechanised).*
`lean/ContextCalculus/ExchangeCut.lean`, sorry-free, axioms `propext`,
`Classical.choice`, `Quot.sound`. Unlike sections 3 and 8, the ground
context is not a clause set closed under resolution on its own: it fires
the ground instances of ontology clauses (the nuclei `P`) only on atoms it
holds in a head, and reasons under a receiver atom only after the receiver
pushed it. The module models this.

- `ClosedHyper rk P SG`: `SG` is closed under labelled ordered
  hyperresolution with the nuclei `P` (for each body atom of a nucleus an
  electron of `SG` with that atom strictly on top of its head; body atoms of
  `SG` are labels, never resolved in `SG`). `closedHyper_of_maximal`
  transfers KM's closure on maximal head literals of a strict partial order
  to every rank extending it.
- `labelledModel_sat_nuclei`: for labels `J` whose hypothesis clauses
  `h → h` lie in `SG`, the candidate model built from the clauses with
  labels in `J` satisfies `P`. This is the paper's ground fragment built
  under the hypotheses `Γ_o`.
- `CutCond`: hypothesis clauses in `SG`; hypotheses are interface atoms;
  ground-context atoms below an interface atom are interface atoms (one
  rank `rk` for both contexts); the guard delivers every interface clause
  whose labels are the receiver's hypotheses; locality; and *demand*: every
  interface atom that is the strict maximum of a receiver clause `c` is a
  hypothesis of the receiver or `c` is `Covered` (the cut condition of
  14.2, with Join case 3 read as the receiver clause `⊤ → Δ'' ∨ K(o)`).
- `cut_exchange_complete`: if `P ∪ SQ` is unsatisfiable, the receiver holds
  `⊥`. `cut_unit_readout_complete`: if `P ∪ SQ` entails an atom that is
  rank-least among the receiver's atoms and is an interface atom or outside
  `P`, the receiver holds `⊥` or a strengthening of the unit.
- `pushed_exchange_complete`: the case without covers, the paper's
  exchange. For a query context whose element may be `o`, the demanded atom
  of the Join case 3 clause `⊤ → Δ'' ∨ K(o)` is `K(o)`, and only the merge
  hypothesis meets the demand. `no_merge_hypothesis_counterexample`: ground
  theory `{K(o) → D(o)}`, receiver `{⊤ → K(o)}`, empty ground context, all
  closed, nothing to deliver, the union entails `D(o)`, the receiver holds
  neither `⊥` nor `→ D(o)`, and the demand fails exactly at `K(o)`. This
  closes, at the propositional level, the gap of the paper's proof noted in
  docs/NOMINALS-CB.md section 10.1: the proof needs `Γ_o` as hypotheses,
  and the demand condition says which ones.
- `covered_of_strengthened`: a receiver clause that a ground clause
  strengthens (labels being receiver hypotheses) is covered for every atom.
- `exists_common_rank`: a strict partial order in which the interface is
  downward closed among the ground context's atoms (R2) admits one injective
  rank extending it with that property, so `CutCond.lower` holds.

Why one rank: in the proof a covered clause `c` produces `a` in the
receiver's model, so the other head atoms of the covering `e` are false
there and lie below `a` in the receiver's rank; the induction that makes the
two models agree on the interface needs them below `a` in the ground
context's rank as well. KM's literal order (`calc::lteq`) is the same
function in every context outside the experimental root-dependent modes,
which is why the cut is off there.

*What remains argued.* (1) The correspondence of KM's Hyper in the ground
context with `ClosedHyper`, of its guard with `CutCond.deliver` (sections 6,
8), and locality. (2) Congruence: equalities are opaque atoms; the Eq rule,
rewriting `o` to `x` and Join case 3 read as the clause `⊤ → Δ'' ∨ K(o)` are
not mechanised. (3) Demand for the receiver clauses KM neither pushes nor
covers: pushes blocked by side condition (*), Join case 3 clauses for
non-core atoms `A(x)`, and ground role or equality atoms that a receiver
derives itself. The argument for them is the simulation of
docs/NOMINALS-CB.md section 10.1: under the hypothesis `K(o)` the ground
context derives these atoms by the receiver's inferences grounded at `o`.
That step is first-order and not mechanised.

*Lean obligation.* Mechanised as above. The certified CB surface
(`KM_CB_LEAN_REQUIRED`) keeps the plain unordered regime and its exact send
sets and is unchanged; it does not model r-Succ edges, merge hypotheses or
the cut.

### 14.4 Horn readout of the nominal-label cache

`horn_unit_readout` (same module, same axioms): if the ground context is
closed under labelled ordered hyperresolution and every body-free clause it
holds is a unit, every atom the ground theory entails is the head of a
unit. This is the condition of docs/NOMINALS-CB.md section 10.2, proved at
the propositional level (equalities opaque; the cache's following of unit
equalities is the congruence step, argued).

### 14.5 Measurements

`results/agents/2026-10-31/nominal-exchange/` (binary km.x3 at b411722e,
every run on one CPU, at most three at a time, forced `nominals`, HermiT
oracle). Seeds r0-r999 at 60 s: 636 ok, 0 wrong; on the 364 it does not
answer, km.v6 (merge hypotheses without the cut) answers 2 (r567, r696) and
km.final2 (no merge hypotheses, incomplete on r1600) 18. All 4,000 seeds at
10 s: 2,521 ok, 0 wrong. Motif sets m1-m7: 3,000 of 3,000 ok at 20 s. Of the
22 seeds lost to the merge hypotheses, 16 answer at 60 s and 6 do not
(r163, r219, r461, r481, r575, r696). Before and after on single seeds:
r5 more than 30 s to 0.2 s, r129 to 0.3 s, r1646 to 0.8 s, fr248 to 14 s,
m2197 more than 60 s to 2.1 s; r1600 on forced `nominals` 224 s, r3602
0.5 s; r1536 and r3777 still time out at 300 s on forced `nominals` (they
answer on the other routes). ORE paired design (112 nominal inputs,
automatic route, 300 s): 108 answered by km.x3 and km.v6 with identical
output, same timeouts, 772 s against 794 s.

*What the cut does not remove.* The seeds that still time out spend their
time inside the ground context under merge-hypothesis labels: superposition
on disjunctive ground equalities under the labels `K(o)` (r163: 2.6 million
Hyper results in 4,000 work-offs) and, on the object-value case of
`data_value_singleton_next_to_nominal_successors`, the ground context's
own Succ/Pred exchange with its successor contexts under those labels. With
`KM_CONTEXT_NO_R2` r163 answers in 0.02 s, so the cross-individual
comparisons that R2 removes make most of the labelled clauses' literals
maximal. Ordering only the labelled clauses by the plain Sequoia order was
measured (`KM_EXP_MERGE_ORDER`, not kept): it recovered r163, r208, r461
and lost r29, r376, r557, r576, and it has no exactness argument (the
receiver's interface must stay downward closed in the order of the clauses
it may receive).

## 15. Pred premises on composite edges, the unit-bridge restriction and least-key subsumption postings (2026-10-31, agent `objvalue-cost`)

The object-value case of `data_value_singleton_next_to_nominal_successors`
(`tests/universal_role_and_top_data_range.rs`: `¬(p value e) ⊑ B` with
`S6 ≡ {c} ⊓ ∃r.{d} ⊓ ∃r⁻.{d}`) did not answer within the test's 10 s
bound on the forced `nominals` route; at 60 s it still timed out, and the
engine worker alone ran past 300 s. Results and commands:
`results/agents/2026-10-31/objvalue-cost/`.

### 15.1 Where the cost was

The frontend encodes `¬(p value e)` with a complement `Q_1 ≡ ¬{e}`, so every
context holds the body-free bridge `⊤ → Q_1(x) ∨ x ≈ e`: every element may be
`e`. Every query context with core `K(x)` therefore pushes the merge
hypothesis `K(e)` (section 14), and the ground context reasons under
`S6(e)` as well as under `S6(c)`. Profiling the ground context (`KM_PROF`,
`KM_PROF_DUMP_AT`, attribution switches) showed three separate costs.

1. *Labels on the ground context's own successor terms.* After 1,000
   work-offs the ground context held clauses labelled by atoms such as
   `__nom__e(f(e))`, `p(f(e), f(e))` or `Q_2(f(d))`, over composite terms
   `f(o)`. No receiver ever pushes such an atom, so these labels are never
   discharged; they came from Pred. On an edge labelled by a composite
   `f(o)`, `pred_payload` maps `x ↦ f(o)` and `y ↦ o`, so the image of every
   sender atom is ground, and the receiving side copied every ground body
   atom without a provider into the conclusion's body (the `C_i` copy). The
   images `A_iσ` of the sender's atoms over `x` are not `C_i`: in
   arXiv:1805.01396 Table 2 only atoms that are ground *in the sender*
   (labels the sender holds) are copied, and the premises `A_iσ` must resolve
   against a clause of the receiver with `A_iσ` maximal. Shared empty-core
   successors (whose hypotheses come from many edges) sent back clauses over
   hypotheses that the ground context had never pushed on that edge, and the
   copy turned each of them into a new hypothesis of the ground context.
2. *The merge hypothesis `S6(e)`.* The query context `S6` holds the unit
   bridge `⊤ → x ≈ c` (from `S6 ⊑ {c}`) and the bridge
   `⊤ → Q_1(x) ∨ x ≈ e`. It pushed both `S6(c)` and `S6(e)`. Under `S6(e)`
   the ground context derives `e ≈ c` and rebuilds the whole `c` world, and
   through the templates `Q_1(t) ∨ t ≈ e` it spreads `S6` to every term.
   With the fix of item 1 alone, the engine worker still had 40,000 clauses
   in the ground context after 300 s; without `S6(e)` it answers in 7 s.
3. *Forward subsumption.* In the remaining 7 s, 3.7 s went to forward
   subsumption: 879,000 calls scanned 327 million candidates, because the
   least head literal (such as `Q_1(c)`) is shared by thousands of the
   ground context's disjunctions.

Neither the exchange cut of section 14 nor the switches `KM_CONTEXT_NO_R2`,
`KM_CONTEXT_PAIR_R2`, `KM_CONTEXT_UNIT_R3` change the outcome of 1 or 2.

### 15.2 Pred premises on composite edges

`PredClause` carries `resolve`, the premises `A_iσ` of the payload: on an
edge labelled by a composite `f(o)`, the images of the sender's body and core
atoms that mention `x`, minus any image that equals an atom the sender
already holds ground. `PredClause::copies_verbatim` admits a body atom
without a provider as a copied label only when it is ground and not in
`resolve`. All four Pred paths use it (`pred_from_neighbor_ordered`,
`pred_local_inner`, its full-product reference, `pred_rule_evidence`). Atoms
over `y` alone (images `B(o)`) stay copyable, as before, and so do all atoms
on ordinary edges (`resolve` is empty there). `KM_PRED_COPY_ALL` restores
the previous rule.

*Soundness.* Unchanged: the rule derives a subset of what it derived before.

*Completeness.* The rule is now the paper's Pred for these premises: a
conclusion needs, for each `A_iσ`, a receiver clause `Γ_i → Δ_i ∨ A_iσ` with
`A_iσ` maximal. When the provider is worked off after the payload arrived,
`pred_local` (fired on every maximal head atom over a function or composite
term) resolves the stored payload against it, exactly as for nonground
premises on ordinary edges. What the old rule added on top is the clause
`A_iσ ∧ Γ → Δ` with `A_iσ` as a label and everything derived from it. Such
a label is an atom over `f(o)`. In KM no context pushes it (r-Succ pushes
`root_succ_form` atoms over individuals, merge hypotheses `K(o)` are over
individuals), so (a) the guard never delivers a clause carrying it (every
body atom must be a hypothesis the receiver pushed), (b) it never takes part
in a cover of `rsucc_covered` (same condition), (c) Join case 3 never removes
it (its variants are atoms over individuals), (d) the global refutation and
the Horn readout read only body-free clauses. Join cases 1 and 2 resolve it
once a provider exists, which gives the Pred conclusion that the new rule
derives directly. The extra clauses were therefore sound consequences that
the paper's calculus does not derive; the completeness arguments of sections
3, 6, 8, 11 and 14 are stated for the paper's Pred with the `C_i` copy of
labels and do not use them.

*Lean obligation.* No calculus rule is added and no redundancy test changes;
the change removes inferences that are outside the paper's Pred, so the
mechanised exchange theorems (`ExchangeCut.lean`, `ExchangeEquality.lean`),
whose ground context is closed under labelled hyperresolution with labels
that are receiver hypotheses, are unaffected. The certified CB surface does
not model Pred into the ground context. What stays argued, as in section 14.3
item (1): the correspondence of KM's Pred and Join with the paper's rules.

### 15.3 The unit-bridge restriction of merge hypotheses

`Engine::merge_hypotheses`: when a query context `u` with core `K(x)` holds a
*unit* bridge `⊤ → x ≈ o'` (body-free, one literal), it pushes the merge
hypotheses `K(o')` only; the bridges `⊤ → Δ'' ∨ x ≈ o` with `o ≠ o'` get no
merge hypothesis. `KM_NO_UNIT_BRIDGE_CUT` restores the previous behaviour.
(A unit bridge is permanent: only the empty clause strengthens it.)

*Soundness.* Fewer hypotheses, fewer premises: unchanged.

*Completeness (argued, first-order, not mechanised).* Merge hypotheses exist
because the ground context must reason under the assumption that `u`'s
element is the individual `o` (section 14, `no_merge_hypothesis_counterexample`).
With the unit bridge, `u`'s element is `o'` in every model of `u`'s clauses,
so the assumption "the element is `o`" is the assumption `o ≈ o'` together
with `K(o')`. The ground context reasons under `K(o')` and holds the ground
instances `Δ''{x↦o'} ∨ o' ≈ o` of the bridge's source clauses (the bridge
`⊤ → Δ'' ∨ x ≈ o` is a consequence of `u`'s core and the ontology; with the
element fixed to `o'` the ground context derives the instance from `K(o')`).
Superposition in the ground context is complete for equality in the labelled
clause set under `K(o')`, so every clause `K(o) ∧ Γ → Λ` that the hypothesis
`K(o)` would have produced has a counterpart `K(o') ∧ Γ → Λ' ∨ Δ''{x↦o'}`
with `Λ'` the image of `Λ` under `o ↦ o'` (the case split on `o ≈ o'` moved
into `Δ''`). Join case 3 on `K(o')` with the unit bridge turns it into the
clause `Γ → Λ'' ∨ Δ''` of `u` that Join case 3 on `K(o)` with the bridge
`⊤ → Δ'' ∨ x ≈ o` would have given, up to the rewriting of `o'` to `x` that
`u`'s Eq rule performs with the unit bridge. This is a congruence argument;
the propositional skeleton of `ExchangeCut.lean` treats `K(o)` and `K(o')` as
unrelated atoms, so the demand condition of `CutCond` does not hold for
`K(o)` there and the mechanised theorem does not cover the restriction.

*Lean obligation (open).* A model of the exchange in which equalities are
interpreted (a congruence on the ground atoms) and the demand condition is
relaxed to "`K(o)` is a hypothesis, covered, or `u` holds a unit bridge to
`o'` with `K(o')` a hypothesis". Not done here: it needs equality in the
model construction of `cut_extend`, which the current modules leave out on
purpose (section 14.3, "What remains argued", item (2)). The differential
runs of 15.5 check the restriction against HermiT.

### 15.4 Least-key forward-subsumption postings

`ClauseLayer` keeps, beside `active_min_head_lit_index`, three postings of
its active non-empty-head clauses: one-literal heads under that literal,
two-literal heads under the pair, longer heads under their three least
literals (heads are sorted). A clause `d` strengthens an incoming clause
`c` only if `d.head ⊆ c.head`, so its key consists of literals of `c.head`
in sorted order; `fwd_subsumed` looks up the literals, pairs and triples of
`c.head` (heads of at most ten literals; longer heads, and the shared base
layer of root contexts, keep the least-literal scan) and runs the same
signature screen and exact `strengthens` test. It visits every candidate the
least-literal scan visits that can pass `strengthens`, so it returns the
same answer, and the derived set is unchanged. Unit test
`forward_subsumption_postings_match_a_full_scan` compares it with a scan of
every active clause under 3,000 random insertions and removals. On the
object-value case the scan count drops from 327 million to 73 million.

*Lean obligation.* None: an index change that leaves the redundancy test's
answer unchanged.
