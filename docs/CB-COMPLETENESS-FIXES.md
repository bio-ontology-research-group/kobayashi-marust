# CB completeness fixes (v1.5.5)

This note records completeness defects of the consequence-based (CB) engine
found by HermiT differentials on generated ALCHIQ seeds and on the bridge
reproducers, with the soundness argument for each fix and its effect on the
Lean certification surface. Fixtures with HermiT answers live in
`engine/tests/fixtures/cb_route_completeness/` and run through
`engine/tests/cb_route_completeness.rs` on the automatic route and the CB
routes. Measurements: `results/agents/2026-10-29/cb-inverse-top/`.

## 1. Shared-closure clauses missing from the r-Succ pool

### Defect

Reproducer (`inverse_top_recognition.ofn`):

    SubClassOf(owl:Thing :D)
    SubClassOf(:B ObjectSomeValuesFrom(:t :C))
    EquivalentClasses(:Q3 ObjectSomeValuesFrom(:t ObjectSomeValuesFrom(ObjectInverseOf(:t) :D)))

HermiT derives `B ⊑ Q3`. Before the fix KM missed it on `auto`,
`production_all`, `default1`, `cb_plain1`, `cb_absorb1`, `cb_trigger1` and
`cb_portfolio16`; only `ht_bridge` found it.

The frontend clausification is correct. With `Q_0` for `⊤`, `Q_3` for
`∃t⁻.D` and `__inv__t` for `t⁻`, the relevant clauses are

    → Q_0(x)                    Q_0(x) → D(x)
    t(x,y) → __inv__t(y,x)      __inv__t(x,y) → t(y,x)
    __inv__t(x,y) ∧ D(y) → Q_3(x)
    t(x,y) ∧ Q_3(y) → Q_2(x)    Q_2(x) → Q3(x)

In the `B` context, `t(x,f(x))` gives `__inv__t(f(x),x)`, a Succ trigger
that reaches the successor as `__inv__t(x,y)`. The successor can fire the
recognition clause only with the parent label `D(y)`. Every clause with a
backward role switches on r-Succ (`sig.rsucc`), which offers each worked-off
clause whose maximal head is a central concept (`rsucc_pool_eligible`) to all
successors as the hypothesis `D(y) → D(y)`. The returned
`D(y) ∧ … → Q_3(x)` crosses Pred back only to edges whose pushed set holds
`D(y)`, where it resolves with the parent's `→ D(x)`.

The parent's `→ D(x)` comes from the context-independent facts+TBox closure.
A context created with that closure attached (`attach_shared_base`, the
default) or seeded flat from it (`seed_worked_off`, used with
`KM_NO_BASE_LAYER` and `KM_SEED_FROM_SUBSET`) received the closure clauses
into its worked-off set, head indexes and Pred/Succ pools, but never into its
own `rsucc_pool`, which only `saturate` fed. So `D(y)` was never offered and
`B ⊑ Q3` was lost. `KM_NO_SHARE=1`, which saturates the facts in each context,
already found it; so did certification runs, which never share the closure
(`certificate_history.is_some()` takes the `init_context` path).

Minimal engine input: `km ofn inverse_top_recognition.ofn | km engine` lists
`"B":["D","Q_0","Q_1"]` before the fix and
`"B":["D","Q3","Q_0","Q_1","Q_2"]` after, for the base layer and for
`KM_NO_BASE_LAYER=1`; `KM_NO_SHARE=1` gives the second answer on both
binaries.

### Fix

`engine/src/engine.rs`: `attach_shared_base` appends the closure's
r-Succ-eligible ids (computed once per ordering domain by
`ensure_shared_rsucc`, invalidated with `shared_base` on retained insertion)
to the context's `rsucc_pool`, and `seed_worked_off` pushes a newly seeded
eligible clause. `saturate` uses the same `rsucc_pool_eligible` test.

### Soundness

No rule changes. The r-Succ offer installs the hypothesis `p → p` at the
successor, which `CBInterContext` proves universally valid; Pred then
resolves the returned clause against worked-off clauses of the receiver,
an instance of the Lean `resolve` step (`Basic.lean`, `Derivable`). The
closure clauses are worked-off clauses of the context in both
representations: the shared base is by construction the state the per-context
seeding produces, and its clauses are ontology consequences valid in every
context of the domain. The fix makes the shared path offer exactly what the
flat `init_context` path offers for the same worked-off set.

### Completeness for this shape

r-Succ is specified, and checked by `CBRSuccClosure`, as the full product of
outgoing edges and the maximal central concept facts of the context's
retained clauses. The pool feed was the only place where the shared path
under-approximated that product: closure clauses are retained clauses of the
context. After the fix every retained clause enters the pool, whichever path
put it in the worked-off set, so the product the semi-naive scan reaches
equals the specified one.

### Lean boundary

The change does not alter what the Lean checkers verify. Certified runs
(`KM_CB_LEAN_REQUIRED`) never attach the shared closure, so their certificates
already contained these offers and are unchanged. No rule side condition
changes. Uncertified shared runs now produce the r-Succ offers the
`CBRSuccClosure` product demands of the same retained state, so they emit more
Succ hypotheses and their successors may retain more clauses.

### Cost

Offering the closure labels is not free on the pure CB route. On three of
the 700 ALCHIQ seeds the full offer product multiplies the candidate clauses
of at-most Hyper joins (seed 241: products near 10^6 for
`≤1 inverse(t).A`), and `cb_plain1` goes from under 15 s to over 60 s. The
old binary shows the same cost with `KM_NO_SHARE=1` (seed 169: 1.4 s shared,
over 100 s unshared), so the slowdown belongs to the specified r-Succ product,
not to the fix. The automatic route answered these seeds unchanged.

## 2. Retained CB insertion that enables r-Succ

### Defect

`Engine::prepare` turns r-Succ on when some clause has a backward role
(`R(s,x)` with `s ≠ x`, `clause_enables_rsucc`). A retained CB insertion
(`km incremental`, strategy `cb_delta`) copied the old flag. Starting a CB
session from `⊤ ⊑ D`, `B ⊑ ∃t.C`, `A ⊑ B ⊔ C` and adding
`Q3 ≡ ∃t.∃t⁻.D` resumed a fixpoint without r-Succ and returned no `B ⊑ Q3`,
while the fresh engine returns it. Forcing `KM_RSUCC=1` on the session gave
the right answer once fix 1 was in place, which isolates the flag.

### Fix

`retained_insert_boundary` reports `RSuccActivation` when the engine runs
without r-Succ and an addition enables it, so the session takes the exact
rebuild. r-Succ also changes which concept atoms are Succ triggers
(`Pred::is_succ_trigger`), so the retained maximal-head masks would be stale
as well; in-place activation is not exact.

### Soundness and Lean boundary

The change only routes more insertions to the fresh exact engine; it derives
nothing and changes no rule or side condition, so nothing the Lean checkers
verify changes. A rebuilt session is an ordinary fresh engine run.
