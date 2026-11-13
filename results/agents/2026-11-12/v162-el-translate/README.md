# v162-el-translate: OWL EL into NF1 to NF7, proved correct

Branch `v162/el-translate` (from `development/v1.6.2` at cacedafb), worktree
`/mnt/data1/leechuck/km-work/wt/v162-el`.

## What changed

- `lean/ContextCalculus/OWL/Fragment.lean`: the two probe lemmas are proved
  (statements unchanged). New: `Interp.withCls`, `Interp.ext_withCls`
  (the extension of `E` depends only on `E.names`), `Interp.sat_withCls`,
  and the agreement lemma `model_update_unmentioned` (changing the extension
  of a class IRI the ontology does not mention keeps a model a model).
- `lean/ContextCalculus/OWLFrontend/ELTranslate.lean`: `ELTranslation`,
  `translateEL` and the state-passing translation (`EL.transExpr`,
  `EL.transAxiom`, chain splitting `EL.transChain`, prepass `EL.scanAxiom`,
  `EL.internRequested`).
- `lean/ContextCalculus/OWLFrontend/ELTranslateCorrect.lean`: the proofs.
- `lean/ContextCalculus/OWLFrontend/ELTranslateTests.lean`: 25 `#guard`
  tests.
- `lean/ContextCalculus.lean`: imports the four modules.

`OWL/Semantics.lean` is unchanged; `OWL/Parse.lean` and `OWL/Names.lean` were
not touched.

## Theorems (namespace `ContextCalculus.OWLFrontend`, statements as briefed)

```lean
theorem translateEL_named (h : translateEL O requested = some T) :
    T.named = requested.eraseDups
theorem translateEL_isSome (hEL : O.isEL = true) :
    (translateEL O requested).isSome = true
theorem translateEL_correct (h : translateEL O requested = some T)
    (i j : Nat) (hi : i < T.named.length) (hj : j < T.named.length) :
    OWL.EntailsSub O T.named[i] T.named[j] ↔
      ELCompletion.EntailsSub (top := T.top) (bottom := T.bottom) T.ontology i j
```

and in `ContextCalculus.OWL` (statements fixed by the lead):

```lean
theorem inconsistent_iff_entailsSub_fresh (hP : ¬ O.mentionsClass P)
    (hQ : ¬ O.mentionsClass Q) (hPQ : P ≠ Q) : Inconsistent O ↔ EntailsSub O P Q
theorem unsatisfiable_iff_entailsSub_fresh (hQ : ¬ O.mentionsClass Q) (hAQ : A ≠ Q) :
    Unsatisfiable O A ↔ EntailsSub O A Q
```

No statement was changed. `eraseDups` uses `BEq String`, which is lawful,
so no `DecidableEq` gap arose; the executable code does not call `eraseDups`
(quadratic) but a HashMap-backed pass, `internRequested`, proved equal to it.

`#print axioms` (from the build log):

```
'ContextCalculus.OWL.inconsistent_iff_entailsSub_fresh' depends on axioms: [propext, Quot.sound]
'ContextCalculus.OWL.unsatisfiable_iff_entailsSub_fresh' depends on axioms: [propext, Quot.sound]
'ContextCalculus.OWLFrontend.translateEL_named' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.OWLFrontend.translateEL_isSome' depends on axioms: [propext, Quot.sound]
'ContextCalculus.OWLFrontend.translateEL_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `native_decide`, no new axioms, no raised heartbeats or
recursion depth.

## Design as implemented

The lead's design, with one difference in the index layout:

- Concept indices: requested IRIs (duplicates removed) `0 .. n-1`; the other
  class IRIs the ontology mentions, in first-occurrence order (prepass);
  **then `top`, `bottom`, then the definers**. The design put the definers
  before `top` and `bottom`; allocating `top` and `bottom` first lets the
  translation emit clauses that mention them in one pass. The theorem
  statements do not depend on this order.
- Role indices: property IRIs in first-occurrence order (prepass), then the
  fresh chain roles.
- One fresh definer per complex occurrence; negative `and` is a left-nested
  binary `nf2` chain (the intermediate definer stands for `and [e, c]`, so
  the meaning table stays linear); positive `and` gives `nf1 X Xi`;
  `some r c` gives `nf4`/`nf3`; `owl:Thing`/`owl:Nothing` are `top`/`bottom`.
- `EquivalentClasses`: `nf1 N_i P_j` for every pair whose indices differ
  (so `EquivalentClasses(A B)` is `nf1 A B`, `nf1 B A`); `DisjointClasses`:
  `nf2 N_i N_j bottom` for `i < j`; domain `nf4 r top X`; chains as in the
  brief (`nf6`; `nf7`; `nf7 r1 r2 u1`, `nf7 u1 r3 u2`, .., `nf7 u r`);
  `TransitiveObjectProperty(r)` is `nf7 r r r`; `EquivalentObjectProperties`:
  `nf6` both ways for every pair with different indices. An empty chain
  (excluded by `isEL`) would give `reflexive r`.
- The state keeps, per concept index, the class expression it stands for, and
  per role index the reversed chain it composes. The proof reads these
  tables; `extend` interprets index `k` as `ext I (cdefs[k])`, role `k` as
  the composition of its chain. `restrict` reads a model of the NF back as
  an OWL interpretation through the final maps.
- Compiled code recurses only over the depth of one class expression and the
  length of one chain; loops over axioms, members, requested names and
  conjuncts are `foldl` or self tail calls.

Proof structure (`ELTranslateCorrect.lean`): an extension order `Le` on
states and a map invariant `WF`; monotonicity and invariance by mutual
structural induction; the occurrence lemma in both directions
(`transExpr_restrict`, `transExpr_extend`), the axiom lemmas
(`transAxiom_restrict`, `transAxiom_extend`), the prepass and
`internRequested_spec`, and `correct_core`.

## Build and tests

```
cd lean && export PATH=$HOME/.elan/bin:$PATH
LEAN_NUM_THREADS=2 nice lake build ContextCalculus   # Build completed successfully (8681 jobs)
LEAN_NUM_THREADS=2 nice lake build Validation        # Build completed successfully (15 jobs)
```

`ELTranslateTests.lean` (built as part of `ContextCalculus`): 25 `#guard`s,
all pass. Hand-computed NF lists for an existential round trip, the index
layout with duplicated and unmentioned requested IRIs, a chain of length 3,
chains of length 1 and 2, transitivity, equivalent properties, negative and
positive conjunction, equivalent/disjoint classes, domain and declarations;
`none` outside OWL EL (union, inverse, range). End to end through
`ELReference.referenceBit`: `A ⊑ ∃r.B`, `∃r.B ⊑ C` give `A ⊑ C` (and not
`B ⊑ C`); a chain of length 3 gives `A ⊑ E` (not without the chain axiom);
transitivity; domain; `A ≡ B ⊓ C`; a disjointness that makes `A`
unsatisfiable (`A ⊑ Q` for a fresh probe, `B ⋢ Q`); an inconsistent ontology
(`P ⊑ Q` for fresh probes) against a consistent one (`P ⋢ Q`).

Measurement (interpreted, `lake env lean --run`, not compiled):
`translateEL` on 100,000 axioms of the form `Ai ⊑ ∃r.(A(i+1) ⊓ Bi)` takes
4.8 s (400,000 clauses), on 300,000 axioms 12.8 s (1,200,000 clauses); an
intersection of 200,000 conjuncts on the left and an equivalence with a
100,000-conjunct member run in 4.2 s without stack trouble; peak RSS 0.8 GB.

## Open

- Nothing in this task's statements. The index layout differs from the
  design in the position of `top`/`bottom` (above).
- Not measured: compiled throughput inside a `lake` executable (no
  executable uses `translateEL` yet).
