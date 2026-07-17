# Disjunction handling: splitting + learning (Direction B), ordered residue (Direction A)

Status: design + staged implementation. Both behind gated flags, default OFF.
Targets the live-`∀ + ⊔` timeout family (10702, 9540, 1603, 10860, 5303,
12141, ...) — the largest timeout group, provably out of parallelism's reach.

## 1. The blow-up, precisely

The engine is a faithful disjunctive-context calculus (Sequoia port). In a
context `K` with core `Γ` (assumed predicates on the central variable `x`),
`saturate()` derives clauses `body → l1 ∨ … ∨ lk`. Same-term concept literals
are **mutually incomparable** in the literal order (`calc.rs::pred_lteq`, the
`t1 == t2` branch returning `i1 == i2`), so every disjunct is a *maximal* head
literal and the Hyper rule (`engine.rs::saturate`, the `for max in &max_head`
loop) fires on **every** disjunct — unrestricted ground resolution.

That is *complete* (certified by `CompletenessProp.lean`, which models Hyper as
resolution on an arbitrary atom) — the answers are right. But the set of
derivable disjunctive clauses on `x` grows as the product of the disjunction
widths, and forward/back subsumption (`Context::fwd_subsumed` / `back_subsume`)
cannot prune incomparable disjunctions (none `⊆` another). Result: the
worked-off population explodes → 240 s timeout, and on the worst cases the
clause arena reaches ~204 GB.

`KM_ORDERED_ALL` (total order on all same-term concepts) tames the population
but is **incomplete**: an entailed unit `⊤ → B(x)` is never produced when the
named super `B` sits non-maximally behind an unresolvable maximal sibling
(`calc.rs` verdict comment, jobs 6123/6125). `KM_SEQ_ORDER` (order auxiliary
definers above, keep named incomparable) is complete and gold-clean but
net-neutral: it tames normaliser-introduced disjunctions, not the intrinsically
wide ones (19/22 still time out; Sequoia itself fails the same 19).

The lesson: **ordering prunes which resolutions fire, but still materialises
the disjunctive closure of the hard part.** To win we must avoid materialising
the product at all — i.e. case-split.

## 2. Direction B — split + conflict-driven learning (DPLL modulo the CB closure)

### Idea
To determine the consequences of `K`, branch on a derived **fact-disjunction**
`⊤ → l1 ∨ … ∨ lk` (body satisfied — `K` is committed to it), creating `k`
sub-derivations, each extending `Γ` with one `li`. A literal `L` on `x` is a
consequence of `K` iff `L` is derived in **every** open branch. A branch that
derives the empty clause `⊥` is **closed**: that disjunct is impossible, so the
disjunction shrinks (a **learned** strengthening); if it collapses to one live
disjunct, that disjunct is promoted to a forced **unit fact** in `K`.

This is DPLL(T) with the deterministic CB closure as the theory:
- **theory propagation** = the deterministic (Horn/unit-driven) closure rules,
- **decision** = pick an open fact-disjunction, assume one disjunct,
- **conflict** = `⊥` derived; the refutation's decision-core becomes a learned
  blocking clause; **backjump** non-chronologically,
- **model** = a branch that saturates without `⊥`, every fact-disjunction
  satisfied,
- **readout** = `Γ ⊨ L` iff `L` holds in every leaf model; for classification,
  the subsumers of query `Q` are the named `B` with `B(x)` in all models.

### Why do it inside the CB engine rather than a standalone tableau
Branches that share a decision prefix share their deterministic closure through
the **content-interned clause arena** (`cc_arena` + `cc_intern_idx`) and the
central-strategy successor contexts (keyed by core). Pure tableau re-derives
per branch; here the shared Horn closure is computed once. This is the one real
advantage of splitting-in-CB over bolt-on tableau.

### Integration: split is local to a context's saturation
The structural context graph (successor/predecessor messaging) models the
tree-model expansion (∃-fillers); it is **orthogonal** to disjunctive case
analysis (which disjunct holds *at* an element). So splitting is a sub-search
**within the saturation of one context**, over the non-deterministic choices
for that context's central variable, emitting back to the context only the
unit consequences true in all open branches (plus learned collapses). The
structural Succ/Pred rules continue to operate on the context's unit facts.

Branch-scoping rule (soundness-critical): a conclusion a successor context
pushes back is valid only under the branch assumptions that produced the facts
pushed to it. A branch therefore saturates its own successor closure under its
committed facts; the central strategy already re-keys successor contexts by
their (assumption-dependent) core, so distinct branches that push different
facts target distinct successor contexts and do not cross-contaminate. Shared
sub-cores are shared via the arena.

### Selective activation (must not regress the easy cases)
Splitting loses CB's sharing and can be exponentially worse where resolution
converges fine. So it is **demand-driven**: run normal CB saturation; when a
context's worked-off population crosses `KM_SPLIT_TRIGGER` without converging
(the blow-up signature — many incomparable multi-head clauses), switch that
context into split mode. Gate: `KM_SPLIT` (default OFF).

### Soundness / Lean (task #23)
- Splitting soundness: assuming a disjunct of an entailed disjunction then
  intersecting consequences is proof-by-cases — sound by construction; a learned
  unit (disjunction collapsed to a single live disjunct) is entailed.
- Completeness: every model of `Γ` satisfies some disjunct of each entailed
  disjunction, so lies in some branch; `L` in all branches ⇒ `L` in that model;
  conversely an entailed `L` holds in all branch models.
- Lean obligation: the branch-model construction + "all-branches readout =
  entailment" lemma, composed with the existing per-branch completeness (the
  deterministic closure inside a branch is the existing, already-certified
  calculus minus splitting). Reuses the model machinery of
  `CompletenessProp`/`CompletenessContext`.

## 3. Direction A — ordered resolution + selection + residue readout

> **2026-07-16 update:** implemented, gated `KM_ROOT_ORDERED` (modes `1` =
> root contexts, `all` = every context), with a complement-guard REFUTATION
> residue readout instead of the selection machinery sketched below — see
> docs/ROOT-ORDERED-RESOLUTION.md for the design, the soundness/completeness
> argument, the focused tests, and the precise Lean obligations (O1–O3).
>
> **2026-07-17 update:** measured on the four shared timeout targets
> (10702/15672/6934/9540) — it is sound + complete-preserving (15/15
> byte-identical to the default engine on the finishable local onts) but
> recovers **0** of the family: 15672/9540 are tiny-bounded-memory search spins
> (not disjunction-product-bound), and on 10702 ordering only slows, never
> bounds, the wide-head proliferation. This confirms §8 below: ordered
> resolution over the monotone engine cannot recover the family; the
> interleaved decision-trail + blocking is the required capability. See
> docs/ROOT-ORDERED-RESOLUTION.md §5.1.

Layered on B (or standalone): within a branch (or in a context not yet split),
order same-term concepts (the `KM_SEQ_ORDER` regime) so Hyper fires only on the
ordering-maximal disjunct, and recover the subsumptions `KM_ORDERED_ALL` loses
via a **residue / negative-literal-selection** readout: when an entailed `B` is
trapped in `B ∨ X` with `X` maximal-unresolvable, derive `B` by a guided
refutation against `X` rather than waiting for the bare unit to surface. Lean
re-cert reuses `CompletenessOrdered` (ordered ground resolution, refutationally
complete) + `CompletenessProp` (the unrestricted named part); the new obligation
is that the selection + residue readout is *positively* complete for
subsumption, not just refutationally complete.

## 4. The B ≈ C realization (informs the Direction C analysis, task #27)

Splitting with conflict-driven learning **is** a (hyper)tableau with caching —
decisions = tableau branches, learned blocking clauses = cached unsat cores,
the deterministic closure = the deterministic tableau expansion. So Direction B
and Direction C (route the disjunctive fragment to a caching tableau) are not
distinct algorithms; they are two **integration strategies** for the same
answer (model search + learning):
- **B** builds it into the context calculus, sharing the interned arena and the
  structural successor machinery (more sharing, deeper engine surgery, new Lean
  cert).
- **C** bolts the search onto the standalone `tableau_cli` (clean separation, no
  CB re-cert, but `tableau_cli` must first be made benchmark-grade — it
  currently errors/hangs on real ORE inputs).

The C-worth analysis (task #27) is therefore: after B's results are in, does the
residual justify a *second* implementation of essentially the same algorithm
through a different integration path? The honest answer will hinge on (a) how
much B recovers, (b) whether the remaining failures are intrinsically
tableau-shaped, and (c) the cost of making `tableau_cli` production-grade vs the
marginal recovery.

## 5. Staged implementation plan

1. **Split core (sound, gated, propositional-on-x first).** `KM_SPLIT` +
   `KM_SPLIT_TRIGGER`. Validate inert (byte-identical) on non-blow-up onts and
   correct on a disjunction probe. *(this branch)*
2. **Structural branch-scoping.** Branch-saturate successor closure under
   committed facts; intersect; promote all-branch units.
3. **Conflict-driven learning.** Decision-core extraction from the `⊥`
   refutation; blocking clauses; cross-context closed-core reuse via the arena.
4. **Direction A residue readout.** On top of `KM_SEQ_ORDER`.
5. **Lean re-cert** (tasks #23 splitting, #25 residue).
6. **Full ORE-2015 sweep + gold table; Direction C worth analysis.**

## 6. Increment 1 outcome (landed, gated `KM_SPLIT` OFF)

Built: `classify_assume` + `read_closure` (engine.rs), `split_recurse` +
`saturate_split` (reasoner.rs), the per-thread `BRANCH_ORDERED` order (calc.rs),
and the conservative completeness guard.

Validated SOUND + COMPLETE: 14/14 byte-identical to the default engine on the
finishable onts; ore_ont_13383 identical with all 368 queries split-classified
and 0 fallback (the splitting machinery is correct on a real named-disjunction
ont, independent of the fallback). The earlier apparent "5107 solve" was a
pre-fix artifact (the incomplete ordered *fallback*); fixed.

Benchmark recovery: **0**. The live-`∀ + ⊔` timeout family puts its
nondeterminism at the successor/conditional level (`A ⊑ ∀R.(C ⊔ D)`, `A ⊑ ∃R.⊤`
→ the disjunction `C ⊔ D` lives in the *successor* context, not the query
context), which increment 1 does not split → it falls back (→ complete-engine
timeout) or the per-branch ordered closure itself times out (5303, 5107).

## 7. Increment 2 — structural splitting (the benchmark-mover)

The narrow class increment 1 recovers (query-level concept disjunctions over
Horn successors) does not overlap the timeout family. To move the benchmark the
splitting must reach the disjunctions where they actually live:

- **Conditional disjunctions** `Γ → B(x) ∨ C(x)` with `Γ` satisfied: already
  become fact-disjunctions once `Γ`'s atoms are derived units (Hyper resolves
  the body), so these are largely handled — the remaining gap is genuinely
  *successor* disjunctions.
- **Successor-context disjunctions**: a branch must be able to assume a disjunct
  *in a successor context*, not only in the query root. The fresh-engine-per-root
  model cannot express that (successor cores are derived, not seeded). This needs
  one of: (a) a decision trail inside a single engine's saturation (assume a
  disjunct in a specific context, propagate, backjump on `⊥` — true DPLL(CB)), or
  (b) generalising "decisions" to `(context-core, disjunct)` pairs reproduced
  across branch engines. (a) is the principled design and the larger rewrite.
- **Conflict-driven learning** (increment 3) then prevents the branch count from
  exploding: extract the decision-core of each `⊥`, learn a blocking clause,
  reuse closed cores across contexts via the interned arena.

This is the multi-session, soundness-critical, Lean-cert'd core (task #23). It is
also where Direction B converges with Direction C (§4): a decision trail with
learned blocking clauses *is* a caching (hyper)tableau — the open question for
task #27 is whether to build it into the CB engine (B) or onto `tableau_cli` (C).

## 8. Increment 3 outcome + the measured ceiling (decisive)

Built (`079da53`, gated): a **unit-propagation mode** — the Hyper resolvent
builder suppresses resolvents combining ≥2 derived disjunctions, so a branch's
per-context clause population stays tame. Sound (14/14 A/B; 13383 identical, full
split / 0 fallback). Recovers **0** of the timeout family.

Instrumentation (node-rate + fixpoint profiling) reveals why, and it is an
architectural ceiling of *lazy* splitting (saturate to fixpoint, THEN split):
- **5303/5107/12698/10702**: the per-query closure (saturate + the inter-context
  message fixpoint) does not complete — the blow-up is in computing the closure
  ITSELF, *before* any disjunction is exposed to split. You cannot split your way
  out of a closure that never finishes.
- **2313**: the split loop completes but every query falls back (disjunctions in
  non-chain-unique contexts the soundness guard refuses to share-split) → the
  complete engine times out.

**Therefore lazy splitting over the monotone CB engine cannot recover this
family.** Recovery needs splitting **interleaved** with saturation — an
incremental decision trail that decides *before* the closure explodes and
backtracks on conflict. Interleaving + backtracking fights the engine's monotone,
append-only clause arena (retraction has no cheap implementation here).

**Refined Direction C verdict (task #27):** earlier this doc leaned "build the
trail into the CB engine (C-by-integration)." The measurement revises that: the
required interleave-and-retract architecture is exactly what a tableau is built
for and exactly what the monotone CB engine is built to avoid. So a
**dedicated/standalone caching tableau is now the cleaner path** for this family,
not a retrofit of the CB engine — provided `tableau_cli` is brought to
benchmark grade (it currently errors/hangs on real ORE inputs). The honest
recommendation flips: for the disjunction-blow-up family, invest in the tableau
(C) as a routed sub-solver, not in forcing an incremental trail into the CB core.
