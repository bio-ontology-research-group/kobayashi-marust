# Completeness gaps — minimal reproducers

Ontologies here are **small, hand-traceable cases where km is INCOMPLETE**: km
reports them consistent / a concept satisfiable, but HermiT and Konclude (and a
hand proof) agree the concept is **unsatisfiable**. Each is reduced from a real
ORE ontology so the gap is isolated from scale.

## `trans_inv_reconstruct_unsat.ofn` / `mini7914_unsat.ofn`  (ore_ont_7914)

A concept is **unsatisfiable** while the ontology stays consistent; the default
km (both the CB engine *and* the HT path) reports it satisfiable. The
unsatisfiable concept is the one carrying `∃po.H`:
- `trans_inv_reconstruct_unsat.ofn`: **`:A`** (HermiT: `A` unsat, ontology
  consistent).
- `mini7914_unsat.ofn`: **`:X`** (`:X ⊑ :A`, `:X ⊑ ∃po.H`; `:A` itself is
  satisfiable here because its `∃po.C` successor is not forced into the clash).
  HermiT: `X` unsat, ontology consistent.

In the 7914 source the corresponding unsat concepts are `UBERON_0001373` /
`UBERON_0008977`.

### STATUS (2026-06-26): FIXED in the CB engine, gated `KM_RSUCC` (commit pending)
`km classify` under `KM_RSUCC=1` now reports **`:A` unsat** (trans_inv) and
**`:X` unsat** (mini) — byte-exact with HermiT on both. Default (flag off) is
unchanged. The HT path (`consistent()`) still has the analogous gap, so the full
ore_ont_7914 (which routes to HT, the CB engine times out on it) is not yet
recovered — that is the HT port (see Fix direction below). The mini reproducer is
distilled from exactly the `UBERON_0008977` pattern, so its pass is the direct
evidence the CB mechanism is correct.

### The proof (hand-checked, mirrors km's own clausification)
Roles: `po` = part_of, `hp` = has_part, with `hp = po⁻` (inverse) and `hp`
**transitive**.

```
A ⊑ ∃po.H              H ⊑ F            H ⊑ D
A ⊑ ∃hp.G              B ≡ F ⊓ ∃hp.G    D DisjointWith B
hp = po⁻               hp transitive
```

1. `A ⊑ ∃po.H` ⟹ a po-successor `h`, `po(a,h)`, `h ∈ H`, so `h ∈ F` and `h ∈ D`.
2. `A ⊑ ∃hp.G` ⟹ `hp(a,g)`, `g ∈ G`.
3. `po(a,h)` + `hp = po⁻` ⟹ `hp(h,a)`.
4. `hp(h,a) · hp(a,g)` + `hp` transitive ⟹ `hp(h,g)`, so `h ⊑ ∃hp.G`.
5. `h ∈ F` + `h ⊑ ∃hp.G` ⟹ `h ∈ B` (the ⊒ direction of `B ≡ F ⊓ ∃hp.G`).
6. `h ∈ D` + `h ∈ B` + `D DisjointWith B` ⟹ `h ⊑ ⊥`.
7. `A ⊑ ∃po.H` forces such an `h`, all of which are `⊥` ⟹ `A ⊑ ⊥`. ∎

### Root cause
km clausifies transitivity via a propagation concept `P = __trans__hp__G`:
```
hp(x,y) ∧ G(y) → P(x)        # x reaches a G in one hp-hop
hp(x,y) ∧ P(y) → P(x)        # transitive: x reaches G via x→y→…
P(x)            → ∃hp.G(x)
```
The refutation needs `P(h)` derived from `P(a)` across the inverse edge
`hp(h,a)` — i.e. propagate a concept derived at the **predecessor** `a` (after
the successor `h` already exists) **down to the successor** `h`. That is the
Sequoia **r-Succ / r-Pred** role-propagation rules (Table 3), which
`engine.rs:15` states are **NOT IMPLEMENTED** ("clauses requiring them are
reported"). Here they were not even reported — the engine silently returned
`consistent:true`, an incomplete answer.

This is NOT a frontend bug: km's clause set is correct and complete (verified by
tracing all 39 clauses of the mini ontology and confirming the disjointness,
inverse-bridge `34/35`, and transitivity-propagation `36–38` clauses are
present). Injecting the logically-equivalent inverse-role variant of the
propagation clauses does NOT help — the gap is the engine's cross-context
propagation, not a missing clause.

### Root cause, pinned exactly (2026-06-26)

The refutation needs `__trans__hp__G` derived **about the po-successor `h`**
(`h` reaches `g` via the inverse back-edge `hp(h,a)` plus `__trans(a)`). Trace
why km never derives it:

1. At the predecessor `a` (its context, `a` = central var `x`), km derives
   `__trans(x)` (a reaches `g` in one hp-hop) and the inverse back-edge
   `hp(f₁,x)` (`f₁` = the po-successor function term, from `po(x,f₁)` via
   `po(x,y)→hp(y,x)`).
2. To get `__trans(f₁)` we would fire clause 37 `__trans(y)∧hp(x,y)→__trans(x)`
   with **x := f₁** (a function term), y := x. But km's `unify`
   (`calc.rs`, Role case) — faithfully matching Sequoia's `canUnify` — **forbids
   binding an ontology clause's central variable to a function term**. So
   clause 37 only ever fires with x = the context's own central element. The
   conclusion `__trans(f₁)` is therefore **never produced in `a`'s context**.
3. Consequently there is nothing to push down to `h`. (Removing the
   `__trans`/`__chain` exclusion in `is_succ_trigger` — `calc.rs:379` — is
   *necessary* for the eventual fix but provably **inert on its own**: the
   predicate it would forward is never derived. Verified by rebuild: T2/mini
   still report `consistent:true`.)

The clause that *must* fire is clause 37 **in `h`'s own context** (x = central
`h`, y = neighbour `a`), using the back-edge `hp(x',y)` km already pushes to the
successor — but that needs `__trans(y)`, i.e. the **predecessor's** `__trans(a)`
visible in `h` as a neighbour fact. km pushes predecessor predicates to a
successor only when they are over the *function term* (`is_succ_trigger`
requires `is_function(t)`); predecessor *central* facts (`__trans(x)` about `a`
itself) are **never forwarded**. That is the whole gap.

### Fix direction (the sound design)
- **r-Succ forward push** (the completeness fix — **IMPLEMENTED, gated `KM_RSUCC`**):
  when the predecessor pushes the back-edge role atom `hp(f₁,x)` to a successor,
  it **also** pushes its own central reachability facts `__trans/__chain(x)` to
  that successor as **edge-conditioned** neighbour facts `C(y)`
  (`engine.rs` `propagate`: `rsucc_pool` collected at work-off →
  forwarded via the ordinary `Msg::Succ` to every successor). The successor then
  fires clause 37 **normally** (no new rule): `hp(x',y)∧__trans(y)→__trans(x')`,
  conditioned on both pushed atoms, so the existing Pred routing (every body atom
  must be in the edge's pushed set) sends it back **only to predecessors that
  pushed `__trans`** — sound under the shared-successor central strategy. The
  predecessor derives `__trans(f)`, and the `is_succ_trigger` reach push (gated
  by the same flag, `calc.rs`) forwards it ⟹ successor gets `__trans` about
  itself ⟹ `Q_6`(∃hp.G) ⟹ `Q_5/B` ⟹ `B⊓D=⊥`. Validated byte-exact vs HermiT on
  both reproducers. Pending: corpus soundness/perf sweep before default-on; Lean
  re-cert (deferred per instruction).
- **Soundness hazard (why this is not a quick patch)**: under the central
  strategy a successor context is **shared across predecessors** (keyed by core).
  An *unconditional* forward push of `C(y)` is **unsound** for a co-sharing
  predecessor that does not entail `C`. The pushed fact must be tied to the
  specific predecessor edge — the forward analogue of Sequoia's
  `PredPush(neighbourCore, …)` conditioning. km has the conditioning machinery
  for the successor→predecessor direction (`neighbor_pred` / `pred_from_neighbor`,
  keyed by `edge_label` + sender core) but **no slot for the forward direction**;
  one must be added.
- **Validation gates (mandatory before default-on)**: this changes what is
  derived ⟹ **Lean re-certification** of the affected rules; plus the full
  corpus soundness-vs-gold sweep (the shared-successor hazard above can only be
  caught there). Land it **gated / opt-in** first, validate `A unsat` on
  `tests/completeness-gaps/` + the 159 unit tests on ws, *then* sweep + cert.
- **Sequoia note**: the cloned kernel (`Rules.scala`) implements only
  Hyper/Pred/Eq and handles inverse roles via the Pred round-trip
  (`neighborIndex` + `getContextStructurePredecessors`), **not** a liftable
  standalone r-Succ. The forward push above is the direct sound realisation.
- The **HT path has the analogous gap** (`consistent()` misses the same unsat),
  so deferring to HT alone does not restore completeness.

### Validation tooling (on ws)
- HermiT 1.4.6 + OWL API 5.1.9: `~/minimize/hermit_cp/`.
- Reproduce: `km classify trans_inv_reconstruct_unsat.ofn` ⟹ `unsat=[]` (wrong);
  HermiT ⟹ `A sat=false`. STAR-module extraction + black-box justification
  scripts used to isolate this live in the session scratch.
