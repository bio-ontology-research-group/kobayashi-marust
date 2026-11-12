# v162-alc-translate: OWL ALC into Ctx normal clauses, proved correct

Branch `v162/alc-translate` (from `development/v1.6.2` at 9680a300), worktree
`/mnt/data1/leechuck/km-work/wt/v162-alc`.

## What changed

- `lean/ContextCalculus/OWLFrontend/ALCTranslate.lean` (new): `ALCTranslation`,
  `translateALC` and the state-passing translation (`ALC.transExpr`,
  `ALC.transList`, `ALC.transAxiom`, `ALC.run`), and the conversion of the
  `Nat`-indexed clause list to `Fin` indices (`ALC.finList`, `ALC.toFin`).
- `lean/ContextCalculus/OWLFrontend/ALCTranslateCorrect.lean` (new): the proofs.
- `lean/ContextCalculus/OWLFrontend/ALCTranslateTests.lean` (new): 35 `#guard`
  tests.
- `lean/ContextCalculus.lean`: imports the three modules.

Not touched: `OWL/Semantics.lean`, `OWL/Fragment.lean`, `OWL/Parse.lean`,
`OWL/Names.lean`, the EL files, any v1.6.0/v1.6.1 file.

### Reuse of the EL route

The ALC state is `{ b : EL.St, out : List (Ctx.Clause Nat Nat) }`: the EL state
carries the maps, the meaning tables (`cdefs`, `rdefs`), `top` and `bottom`
(its own clause list stays empty). The ALC route imports and reuses
`EL.internC`, `EL.internR`, `EL.freshC`, `EL.propIRI`, the prepass
`EL.scanAxiom`, `EL.internRequested`, `EL.setTopBottom`, and the lemmas
`EL.Le`, `EL.WF`, `EL.internC_*`, `EL.internR_*`, `EL.freshC_*`,
`EL.start_spec` (named list, index of every named IRI, WF), `EL.Covers`,
`EL.mem_foldl`, `EL.pair_sublist_cons`, `EL.chain_single`, `EL.ext_*`.
No EL lemma needed generalising.

## Theorems (namespace `ContextCalculus.OWLFrontend`, statements as briefed)

```lean
theorem translateALC_named (h : translateALC O requested = some T) :
    T.named = requested.eraseDups
theorem translateALC_isSome (hALC : O.isALC = true) :
    (translateALC O requested).isSome = true
theorem translateALC_correct (h : translateALC O requested = some T)
    (i j : Nat) (hi : i < T.named.length) (hj : j < T.named.length) :
    OWL.EntailsSub O T.named[i] T.named[j] ↔
      CBALCEncoding.EntailsSub T.ontology
        ⟨i, Nat.lt_of_lt_of_le hi T.hnamed⟩ ⟨j, Nat.lt_of_lt_of_le hj T.hnamed⟩
```

No statement was changed. `translateALC_correct` is proved against the `Ctx`
Tarski semantics and converted with `CBALCEncoding.entailsSub_iff_ctx`.

`#print axioms` (from the build log):

```
'ContextCalculus.OWLFrontend.translateALC_named' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.OWLFrontend.translateALC_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.OWLFrontend.translateALC_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `native_decide`, no new axioms, no raised heartbeats or
recursion depth. One `set_option linter.unusedSectionVars false in` on the
mutual block `transExpr_restrict`/`transList_restrict` (with a comment: the
linter does not see the section hypotheses used through the mutual call).

## Design as implemented

The lead's design and table, row for row:

- Concept indices: requested IRIs (duplicates removed) `0 .. n-1`; the other
  class IRIs of the ontology in first-occurrence order; `top`, `bottom`;
  definers. Role indices: property IRIs in first-occurrence order.
- The start state holds `gci [] [top]` and `gci [bottom] []`, so every
  translation begins with these two clauses.
- `and []` is `top`, `or []` is `bottom`, no definer. Every other complex
  occurrence gets one fresh definer by polarity, exactly the table
  (negative universal: `X`, then `W` meaning `∃r.¬c`, then `N` meaning `¬c`;
  clauses `gci [] [X, W]`, `exRight W r N`, `gci [N, Zc⁻] []`).
- Axioms: `SubClassOf` `gci [X_C⁻] [X_D⁺]`; `EquivalentClasses` `gci [N] [P]`
  for every negative/positive member pair with different indices;
  `DisjointClasses` `gci [Xi⁻, Xj⁻] []` for `i < j`; domain
  `exLeft r top X_C⁺`; range `allRight top r X_C⁺`; declarations nothing.
- `translateALC` returns `none` exactly when `O.isALC = false`. It contains a
  second test `named.length ≤ conceptCount` (to build `hnamed`), which
  `translateALC_isSome` proves never fails.
- The `Fin` ontology is built once at the end with
  `out.reverse.filterMap (toFin n m)`. The invariant `ALC.WF` records that
  every index of every emitted clause has an entry in the meaning tables, so
  `toFin` succeeds on every clause and nothing is dropped (`fin_models`).

### Checking the table

Every row holds in both directions; no row needed a fix. The two crossing
rows:

- negative `not c`, `gci [] [X, Y⁺]` with `Y⁺ ⊑ c`: if `x ∈ ¬c` then
  `x ∉ Y⁺`, so `x ∈ X`. Extension: `X := ¬c`, `Y := c`, and `X ⊔ Y` covers
  the domain classically.
- negative `all r c`: if `x ∈ ∀r.c` and `x ∈ W`, then some `r`-successor `y`
  is in `N` and in `c`, hence in `Zc⁻` (negative induction hypothesis),
  which contradicts `gci [N, Zc⁻] []`; so `x ∈ X`. Extension:
  `W := ∃r.¬c`, `N := ¬c`, and `X ⊔ W` covers the domain classically.

### Proof structure (`ALCTranslateCorrect.lean`)

- `Le` (EL order on `b`, clause list grows) and `WF` (EL invariant, meaning
  of `top`/`bottom`, every emitted index has a meaning); `transExpr_le`,
  `transExpr_wf` and their list twins, mutual over `ClassExpr`.
- (⇒) `restrict F J`; `transExpr_restrict` is the polarity lemma
  (`EL.Covers`); `transAxiom_restrict`. `top`/`bottom` facts come from the
  two start clauses.
- (⇐) `extend I F`; `transExpr_extend` gives exactness of every index and
  that every emitted clause holds; `transAxiom_extend`.
- `fin_models`: `lower` (Nat model read on Fin) and `raise` (Fin model read
  on Nat, out of range empty), `lower_raise`, `toFin_sat`, `toFin_isSome`.
- `correct_core` and the three public theorems; `run_spec` reuses
  `EL.start_spec`.

## Build and tests

```
cd lean
LEAN_NUM_THREADS=2 nice lake build ContextCalculus          # Build completed successfully (8684 jobs)
LEAN_NUM_THREADS=2 nice lake build ContextCalculus.KMSupervisorInstance   # Build completed successfully (3521 jobs)
```

`ALCTranslateTests.lean`: 35 `#guard` tests, all pass (the module builds in
about 4.5 s):

- hand-computed clause lists for each of the ten table rows, for
  `and []`/`or []`/`owl:Thing`/`owl:Nothing`, a nested two-polarity axiom,
  and the axiom kinds (EquivalentClasses with a repeated member,
  DisjointClasses, domain, range, class and property declarations);
- named list with duplicates, concept and role counts;
- `none` outside ALC: transitivity, a role inclusion, an inverse in a class
  expression, an inverse in a domain axiom;
- end to end through `ALCReference.alcBit`: `A ⊑ B ⊔ C, B ⊑ D, C ⊑ D` gives
  `A ⊑ D` (and not `A ⊑ B`, `D ⊑ A`); `A ⊑ ∀r.B, A ⊑ ∃r.C,
  E ≡ ∃r.(B ⊓ C)` gives `A ⊑ E` (and not without the universal, not
  `E ⊑ A`); `¬A ⊑ B, A ⊑ B` gives `P ⊑ B` for a fresh `P` (the
  `owl:Thing ⊑ B` reading; not without `A ⊑ B`); a range axiom gives
  `C ⊑ D` (not without it); a domain axiom; an unsatisfiable `A` through
  a fresh probe `Q` (`A ⊑ Q`, not `B ⊑ Q`); an inconsistent ontology through
  fresh probes `P ⊑ Q` (not when consistent).

A copy of the test file with two inverted guards fails on exactly those two
(checked in the scratch directory), so the guards are evaluated.

## Measurements

Interpreted (`#eval`, `lake env lean`), ontology of `n` axioms
`A_i ⊓ ¬B_i ⊑ ∀r_{i mod 7}.(A_{i+1} ⊔ ∃s.B_i)`:

| n | concepts | clauses | ms |
|---|---|---|---|
| 20 000 | 140 003 | 120 002 | 1 257 |
| 40 000 | 280 003 | 240 002 | 2 563 |
| 80 000 | 560 003 | 480 002 | 5 074 |

Linear. Compiled code recurses only over the depth of one class expression;
`transList`, `emitEach`, `finList`, the axiom loop and `internRequested` are
tail recursive or `foldl`; `filterMap`, `map`, `reverse` use the core
tail-recursive implementations. `EquivalentClasses` and `DisjointClasses`
are quadratic in the member count of one axiom, as in the EL route.

## Open

- `owlReference` and its capstone (`owlReference_sound`,
  `owlReference_complete`) are not part of this task.
- `EquivalentClasses` with repeated members emits repeated clauses (as the
  EL route does); harmless for the semantics.
