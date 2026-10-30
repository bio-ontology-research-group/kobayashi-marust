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
  delivered, and no proof covers that case. The first-order lifting of the
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
