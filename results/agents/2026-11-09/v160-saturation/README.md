# v1.6.0 EL Reference Saturation Proofs (`v160-saturation`)

## What Was Proved

We proved the two reference-saturation obligations in
`lean/ContextCalculus/ELReferenceSaturation.lean` without changing any existing
executable definitions or public theorem statements:

1. **Soundness (`closure_sound`)**: `initial` derives only reflexivity and top
   label facts (`Sub.refl`, `Sub.top`), and each round `step` appends only
   consequences justified by `Sub` and `Edge` constructors from facts already in
   the state (`subConsequences_sound`, `edgeConsequences_sound`, `step_sound`,
   `saturate_sound`).
2. **Relative closure (`closure_closedOn`)**:
   - Every fact in `initial` and every consequence added by `step` over
     `U = contextUniverse top bottom named O` has its endpoints in `U` and its
     roles in `roleUniverse O` (`ScopedState`, `initial_scoped`,
     `ScopedState.step`).
   - By pigeonhole (`nodup_length_le_of_subset` on `prodList U U` and
     `prodList U (prodList (roleUniverse O) U)`), the number of distinct facts
     `State.uniqSize` is bounded by `factBound U (roleUniverse O)`.
   - Every non-fixpoint step strictly increases `State.uniqSize`
     (`uniqSize_step_gt`), so `saturate` with fuel `factBound + 1` terminates at
     a fixpoint `(step bottom O U s).size = s.size` (`saturate_fixpoint`).
   - Any fixpoint of `step` that retains `initial`'s label facts contains every
     rule consequence in `subConsequences` and `edgeConsequences`, satisfying
     `ClosedStateOn (fun a => a ∈ contextUniverse top bottom named O)`
     (`fixpoint_closedOn`).

We also added executable unit tests and `decide` examples in
`lean/ContextCalculus/ELReferenceSaturationTests.lean` (registered in
`lean/ContextCalculus.lean`) covering NF1 chains, NF2 conjunctions, NF3/NF4
existential round trips, backward bottom propagation through an edge, NF7 role
chains, reflexive roles firing NF4, and inconsistent ontologies.

## Exact Public Theorem Statements

```lean
theorem closure_closedOn (top bottom : Nat) (named : List Nat) (O : Ontology) :
    ClosedStateOn (fun a => a ∈ contextUniverse top bottom named O)
      (closure top bottom named O).toMaterialization top bottom O

theorem closure_sound (top bottom : Nat) (named : List Nat) (O : Ontology) :
    SoundState (closure top bottom named O).toMaterialization top bottom O

theorem referenceBit_exact (top bottom : Nat) (named : List Nat) (O : Ontology)
    {sub : Nat} (hsub : sub ∈ contextUniverse top bottom named O) (sup : Nat) :
    referenceBit top bottom named O sub sup = true ↔
      EntailsSub (top := top) (bottom := bottom) O sub sup

theorem referenceBit_exact_of_named (top bottom : Nat) (named : List Nat)
    (O : Ontology) {sub : Nat} (hsub : sub ∈ named) (sup : Nat) :
    referenceBit top bottom named O sub sup = true ↔
      EntailsSub (top := top) (bottom := bottom) O sub sup

theorem referenceInconsistent_exact (top bottom : Nat) (named : List Nat)
    (O : Ontology) :
    referenceInconsistent top bottom named O = true ↔
      Unsatisfiable (top := top) (bottom := bottom) O
```

## Build Command and Axiom Audit

Command:

```bash
cd lean && LEAN_NUM_THREADS=2 nice lake build ContextCalculus.ELReferenceSaturation ContextCalculus.ELReferenceSaturationTests
```

`#print axioms` output from the build log:

```text
info: ContextCalculus/ELReferenceSaturation.lean:787:0: 'ContextCalculus.ELReference.mem_universe_of_concept' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:788:0: 'ContextCalculus.ELReference.top_mem_contextUniverse' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:789:0: 'ContextCalculus.ELReference.bottom_mem_contextUniverse' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:790:0: 'ContextCalculus.ELReference.mem_universe_of_named' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:791:0: 'ContextCalculus.ELReference.closure_closedOn' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:792:0: 'ContextCalculus.ELReference.closure_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:793:0: 'ContextCalculus.ELReference.referenceBit_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:794:0: 'ContextCalculus.ELReference.referenceBit_exact_of_named' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:795:0: 'ContextCalculus.ELReference.referenceInconsistent_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What Remains Open

None for the `v160-saturation` task. Both `ELReferenceSaturation` and
`ELReferenceSaturationTests` build without `sorry`, `native_decide`, or extra
axioms.
