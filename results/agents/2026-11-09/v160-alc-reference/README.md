# v1.6.0 Phase 2: ALC Reference Procedure (`v160-alc-reference`)

Date: 2026-11-09
Branch: `v160/alc-reference`
Worktree: `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v160-alc-reference`

## What Was Proved

1. **Computable ALC reference saturation (`lean/ContextCalculus/ALCReferenceSaturation.lean`)**:
   - Defined computable `Decidable` instances for `Ctx.consistent O t`, `Ctx.compat O rr t s`, and `Ctx.realizedIn O G t` by bounding quantifiers over the ontology clause list `O` and the finite candidate set `G`.
   - Defined `stepC`, `candC`, `satC`, and `saturateC` without `Classical` for finite concept and role signatures (`Fin conceptCount`, `Fin roleCount`).
   - Proved `stepC_eq`, `candC_eq`, `satC_eq`, and `saturateC_eq : saturateC O = Ctx.saturate O` via `Subsingleton` elimination on the `Decidable` instances.
   - Defined `alcBit O A B : Bool := decide (∀ t ∈ saturateC O, A ∈ t → B ∈ t)` and proved `alcBit_exact` and `alcBit_iff_entailsSub` from `Ctx.saturate_decides` and `CBALCEncoding.entailsSub_iff_ctx`.

2. **Executable ALC common-source recogniser (`lean/ContextCalculus/ALCCommonSourceRecognizer.lean`)**:
   - Defined `RecognizedALC`, carrying `conceptCount`, `roleCount`, `ontology : Ctx.Ontology (Fin conceptCount) (Fin roleCount)`, the duplicate-free identifier tables (`conceptNames`, `roleNames`, `fnNames`), the lookup bijection `conceptIndex : Nat → Option (Fin conceptCount)` and `conceptName : Fin conceptCount → Nat` with round-trip theorems `conceptIndex_conceptName`, `conceptName_conceptIndex`, and `conceptIndex_eq_some_iff`.
   - Implemented `recognizeALC (named : List Nat) (source : List FCL) : Option (RecognizedALC named source)`, inverting `CBALCEncoding.encode` clause by clause (`gci`, paired `exRight` halves sharing one Skolem function and one subject, `exLeft`, and `allRight`), accepting both body literal orders and injective per-clause variable renamings while failing closed on equalities, inequalities, constants, nested function terms, unmatched/mismatched Skolem halves, duplicate Skolem functions, and role clauses outside the ALC table.
   - Proved `recognizeALC_conceptIndex_of_named` and `recognizeALC_entails_iff` by transporting `TModel` interpretations along the globally injective extensions `extendInj` of `conceptNames`, `roleNames`, and `fnNames` and mutual clause instantiation (`ALCClauseVariant.valid_iff`).

3. **Adapter and supervisor integration (`lean/ContextCalculus/KMConcreteWorkerAdapters.lean`, `lean/ContextCalculus/KMSupervisorInstance.lean`)**:
   - Added `KMExactEvidence.alcReference`, `alcReferenceBit`, `alcReferenceAnswer`, `alcReferenceAnswer_correct`, `alcReferenceAccept`, `alcReferenceAccept_sound`, `alcReferenceExecution`, and `alcReferenceExecution_completeAt`.
   - Extended `KMSupervisorInstance` with `ALCFragment`, updated `kmExecute rust route := ((rust route).orElse elReferenceExecution).orElse alcReferenceExecution`, updated `kmSupervisor_coversAt_of_EL` with outer `orElse_completeAt_left`, and proved `kmSupervisor_coversAt_of_ALC`, `kmSupervisor_complete_on_ALC`, `kmSupervisor_sound_and_complete_on_ALC`, and `kmSupervisor_complete_on_EL_or_ALC`.

4. **Executable test suites (`lean/ContextCalculus/ALCReferenceSaturationTests.lean`, `lean/ContextCalculus/ALCCommonSourceRecognizerTests.lean`)**:
   - Verified disjunctive GCI subsumption (`A ⊑ B ⊔ C`, `B ⊑ D`, `C ⊑ D` entails `A ⊑ D`), existential plus universal interaction (`A ⊑ ∃r.B`, `A ⊑ ∀r.C`, `B ⊓ C ⊑ BC`, `∃r.BC ⊑ D` entails `A ⊑ D`), unsatisfiable concept propagation (`B ⊑ ⊥`, `A ⊑ ∃r.B`), and fail-closed rejections using `#eval` and `example := by decide`.
   - Registered all four new modules in `lean/ContextCalculus.lean`.

## Exact Theorem Statements

```lean
theorem saturateC_eq (O : Ontology (Fin conceptCount) (Fin roleCount)) :
    saturateC O = Ctx.saturate O

theorem alcBit_exact (O : Ontology (Fin conceptCount) (Fin roleCount))
    (A B : Fin conceptCount) :
    alcBit O A B = true ↔
      (∀ (D : Type) (I : Interp D (Fin conceptCount) (Fin roleCount)),
        models I O → ∀ x, I.c A x → I.c B x)

theorem alcBit_iff_entailsSub (O : Ontology (Fin conceptCount) (Fin roleCount))
    (A B : Fin conceptCount) :
    alcBit O A B = true ↔ CBALCEncoding.EntailsSub O A B

theorem recognizeALC_conceptIndex_of_named (named : List Nat) (source : List FCL)
    (r : RecognizedALC named source)
    (_hrecognized : recognizeALC named source = some r)
    {a : Nat} (ha : a ∈ named) :
    ∃ i : Fin r.conceptCount, r.conceptIndex a = some i

theorem recognizeALC_entails_iff (named : List Nat) (source : List FCL)
    (r : RecognizedALC named source)
    (_hrecognized : recognizeALC named source = some r)
    {sub sup : Nat} {i j : Fin r.conceptCount}
    (hi : r.conceptIndex sub = some i) (hj : r.conceptIndex sup = some j) :
    Entails source sub sup ↔ CBALCEncoding.EntailsSub r.ontology i j

theorem alcReferenceAnswer_correct (named : List Nat) (ontology : List FCL)
    (recognized : ALCCommonSourceRecognizer.RecognizedALC named ontology)
    (hrecognized : ALCCommonSourceRecognizer.recognizeALC named ontology =
      some recognized)
    (hnodup : named.Nodup) :
    Correct ontology (alcReferenceAnswer recognized named)

theorem alcReferenceAccept_sound (ontology : List FCL) (answer : TaxonomyAnswer)
    (evidence : ALCReferenceEvidence)
    (haccept : alcReferenceAccept ontology answer evidence = true) :
    Correct ontology answer

theorem alcReferenceExecution_completeAt (source : RequestedTaxonomySource)
    (hrecognized :
      (ALCCommonSourceRecognizer.recognizeALC source.named source.ontology).isSome =
        true)
    (hnodup : source.named.Nodup) :
    alcReferenceExecution.worker.CompleteAt source

theorem kmSupervisor_coversAt_of_ALC (rust : Route → KMRequestedExecution)
    (decide : RoutingSource → Decision) (source : RoutingSource)
    (hsource : ALCFragment source) :
    (kmSupervisor rust decide).CoversAt source

theorem kmSupervisor_complete_on_ALC (rust : Route → KMRequestedExecution)
    (decide : RoutingSource → Decision) :
    CompleteOn RequestedCorrect ALCFragment (kmSupervisor rust decide).run

theorem kmSupervisor_sound_and_complete_on_ALC
    (rust : Route → KMRequestedExecution) (decide : RoutingSource → Decision) :
    (∀ source answer,
      (kmSupervisor rust decide).run.run source = .publish answer →
        RequestedCorrect source answer) ∧
    (∀ source, ALCFragment source →
      ∃ answer, (kmSupervisor rust decide).run.run source = .publish answer ∧
        RequestedCorrect source answer)

theorem kmSupervisor_complete_on_EL_or_ALC
    (rust : Route → KMRequestedExecution) (decide : RoutingSource → Decision) :
    CompleteOn RequestedCorrect (fun source => ELFragment source ∨ ALCFragment source)
      (kmSupervisor rust decide).run
```

## Build Command and `#print axioms` Output

Command run from `lean/`:
```bash
LEAN_NUM_THREADS=2 nice lake build ContextCalculus.KMSupervisorInstance ContextCalculus.ALCReferenceSaturationTests ContextCalculus.ALCCommonSourceRecognizerTests
```

Copied `#print axioms` lines from the build log:
```text
info: ContextCalculus/ALCReferenceSaturation.lean:193:0: 'ContextCalculus.ALCReference.saturateC_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ALCReferenceSaturation.lean:194:0: 'ContextCalculus.ALCReference.alcBit_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ALCReferenceSaturation.lean:195:0: 'ContextCalculus.ALCReference.alcBit_iff_entailsSub' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ALCCommonSourceRecognizer.lean:772:0: 'ContextCalculus.ALCCommonSourceRecognizer.recognizeALC_conceptIndex_of_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: ContextCalculus/ALCCommonSourceRecognizer.lean:773:0: 'ContextCalculus.ALCCommonSourceRecognizer.recognizeALC_entails_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: ContextCalculus/KMConcreteWorkerAdapters.lean:1580:0: 'ContextCalculus.KMConcreteWorkerAdapters.alcReferenceAnswer_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: ContextCalculus/KMConcreteWorkerAdapters.lean:1581:0: 'ContextCalculus.KMConcreteWorkerAdapters.alcReferenceAccept_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: ContextCalculus/KMConcreteWorkerAdapters.lean:1582:0: 'ContextCalculus.KMConcreteWorkerAdapters.alcReferenceExecution_completeAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
info: ContextCalculus/KMSupervisorInstance.lean:133:0: 'ContextCalculus.KMSupervisorInstance.kmSupervisor_coversAt_of_ALC' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
info: ContextCalculus/KMSupervisorInstance.lean:134:0: 'ContextCalculus.KMSupervisorInstance.kmSupervisor_complete_on_ALC' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
info: ContextCalculus/KMSupervisorInstance.lean:135:0: 'ContextCalculus.KMSupervisorInstance.kmSupervisor_sound_and_complete_on_ALC' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
info: ContextCalculus/KMSupervisorInstance.lean:136:0: 'ContextCalculus.KMSupervisorInstance.kmSupervisor_complete_on_EL_or_ALC' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

## What Remains Open

All ALC saturation, recogniser, answer correctness, and adapter acceptance theorems (`saturateC_eq`, `alcBit_exact`, `alcBit_iff_entailsSub`, `recognizeALC_conceptIndex_of_named`, `recognizeALC_entails_iff`, `alcReferenceAnswer_correct`, `alcReferenceAccept_sound`) depend only on `[propext, Classical.choice, Quot.sound]`.

`alcReferenceExecution_completeAt` and the `KMSupervisorInstance` theorems (`kmSupervisor_coversAt_of_ALC`, `kmSupervisor_complete_on_ALC`, `kmSupervisor_sound_and_complete_on_ALC`, `kmSupervisor_complete_on_EL_or_ALC`) mention `KMRequestedExecution.worker`, whose `accept_sound` field (`requestedExactAccept_sound` -> `kmExactAccept_sound`) includes the `.elReference` branch (`elReferenceAccept_sound`). On this branch, `elReferenceAccept_sound` still transitively references the open EL obligations (`ELReferenceSaturation.closure_closedOn`, `ELReferenceSaturation.closure_sound`, and `ELCommonSourceRecognizer.recognizeEL_entails_iff`) assigned to the `v160-saturation` and `v160-recognizer` worktrees. Once those two EL modules are merged without `sorry`, `sorryAx` disappears from `alcReferenceExecution_completeAt` and `kmSupervisor_complete_on_ALC` automatically.
