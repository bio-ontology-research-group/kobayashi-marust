# Completeness gaps — minimal reproducers

Ontologies here are **small, hand-traceable cases where km is INCOMPLETE**: km
reports them consistent / a concept satisfiable, but HermiT and Konclude (and a
hand proof) agree the concept is **unsatisfiable**. Each is reduced from a real
ORE ontology so the gap is isolated from scale.

## `trans_inv_reconstruct_unsat.ofn` / `mini7914_unsat.ofn`  (ore_ont_7914)

`:A` (and in the 7914 source, `UBERON_0001373` / `UBERON_0008977`) is
**unsatisfiable**. km (both the CB engine *and* the HT path) reports it
satisfiable. HermiT on the same axioms: `A sat = false`.

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

### Fix direction
- **Completeness fix**: implement the Sequoia r-Succ / r-Pred rules in the CB
  engine (`engine.rs`) so a concept derived at a predecessor re-propagates to an
  existing successor context across `∃`/inverse edges. Requires **Lean
  re-certification** of the affected rules (calculus change). Likely resolves a
  whole class of the "correctness tail" under-detected-unsat ontologies.
- **Immediate soundness-of-router fix** (smaller): make the engine correctly
  DETECT clauses that need the unimplemented rules and *report* (defer) instead
  of silently returning an incomplete answer — restoring "never silently
  approximate". (The HT path has the analogous gap, so deferring to HT alone is
  not sufficient for completeness.)

### Validation tooling (on ws)
- HermiT 1.4.6 + OWL API 5.1.9: `~/minimize/hermit_cp/`.
- Reproduce: `km classify trans_inv_reconstruct_unsat.ofn` ⟹ `unsat=[]` (wrong);
  HermiT ⟹ `A sat=false`. STAR-module extraction + black-box justification
  scripts used to isolate this live in the session scratch.
