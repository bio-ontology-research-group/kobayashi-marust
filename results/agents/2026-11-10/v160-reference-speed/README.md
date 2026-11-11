# v1.6.0 Reference Procedure Speedup (`v160-reference-speed`)

Date: 2026-11-10
Branch: `v160/reference-speed`
Worktree: `.work/worktrees/v160-nary-conjunction`

## 1. Summary of Changes

We accelerated the executable EL and ALC reference procedures and the `km-el-reference` binary while keeping every existing public theorem statement and axiom footprint unchanged:

1. **Compute each closure once per taxonomy answer (`ELReferenceSaturation.lean`, `ALCReferenceSaturation.lean`, `KMConcreteWorkerAdapters.lean`)**:
   - Factored `ELReference.referenceBitOf (c : State) (bottom sub sup : Nat) : Bool` and `ALCReference.alcBitOf (G : Finset (Finset (Fin conceptCount))) (A B : Fin conceptCount) : Bool`, keeping `referenceBit` and `alcBit` with `referenceBit_eq` and `alcBit_eq` proved by `rfl`.
   - Hoisted `let c := ELReference.closure ...` in `referenceAnswer` and `let G := ALCReference.saturateC ...` in `alcReferenceAnswer` so the reference saturation runs once per ontology instead of $(|named| + 2)^2$ times.

2. **Indexed worklist EL saturation and $O(n \log n)$ duplicate check (`ELReferenceSaturation.lean`)**:
   - Extended `State` with `subSet : Std.TreeSet (Nat × Nat)` and `edgeSet : Std.TreeSet (Nat × (Nat × Nat))` plus `WellFormedState` linking tree-set membership to list membership.
   - Added `ClauseIndex`, `WorkState`, `fastSaturate`, and a verified linear-time closure checker `checkClosedTree` (`checkClosedTree_sound : WellFormedState s → checkClosedTree bottom O U s = true → ClosedStateOn bottom O U s.toMaterialization`), falling back to `slowClosure` when `U.length ≤ 10` (so kernel `by decide` tests in `ELReferenceSaturationTests.lean` reduce in 3 rounds within the default `maxRecDepth`) or if the worklist fuel is exhausted.
   - Added `nodupFast : List Nat → Bool` backed by `Std.TreeSet Nat` and proved `nodupFast_iff : nodupFast xs = true ↔ xs.Nodup`, wired as a high-priority local `Decidable (xs.Nodup)` instance in `KMConcreteWorkerAdapters.lean`.

3. **ALC early fixpoint exit and direct `Finset` quantifier decision (`ALCReferenceSaturation.lean`)**:
   - Added `saturateLoop` with early exit `if next.card = G.card then G else saturateLoop O n next` and proved `saturateLoop_eq` and `saturateC_eq` via `Finset.eq_of_subset_of_card_le` and `Function.iterate_fixed`.
   - Replaced the default `decide (∀ t ∈ G, A ∈ t → B ∈ t)` elaboration in `alcBitOf` (which synthesized `Fintype.decidableForallFintype` over the full $2^n$ powerset `Finset.univ` and `List.decidablePerm` membership on every cell) with `@decide (∀ t ∈ G, A ∈ t → B ∈ t) Finset.decidableDforallFinset`, iterating directly over `G` in $O(|G| \cdot n)$ time.

4. **Pre-budget ALC screening, acceptance proof forwarding, streaming JSON output, and `"procedure"` field (`KMELReferenceCheck.lean`)**:
   - Added `fastAlcPrecheck` using `Std.HashMap` and `Std.HashSet` to verify clause shapes, Skolem witness pairing, and distinct concept count before `ALCCommonSourceRecognizer.recognizeALC` runs.
   - Replaced `source.named.Nodup` with `ELReference.nodupFast source.named` and replaced list membership on `seenFns` with `Std.HashSet Nat`.
   - Forwarded the compile-time proofs `elReferenceExecution.accepted` and `alcReferenceExecution.accepted` into `publishChecked` so `km-el-reference` does not recompute `referenceAnswer` a second time at runtime or overflow the C stack in `List.hasDecEq` on multi-million-cell matrices.
   - Replaced `renderTaxonomyJson` (`Json.mkObj` per cell) with `writeTaxonomyJson`, streaming 4,096-cell chunks with pre-escaped concept strings and emitting `"procedure": "el"|"alc"`.

## 2. Preserved Theorem Statements

All existing public theorem statements in `ELReferenceSaturation.lean`, `ALCReferenceSaturation.lean`, `KMConcreteWorkerAdapters.lean`, and `KMSupervisorInstance.lean` remain unchanged:

```lean
-- lean/ContextCalculus/ELReferenceSaturation.lean
theorem closure_closedOn (top bottom : Nat) (named : List Nat) (O : Ontology) :
    ClosedStateOn bottom O (contextUniverse top bottom named O)
      (closure top bottom named O).toMaterialization

theorem closure_sound (top bottom : Nat) (named : List Nat) (O : Ontology) :
    SoundState (top := top) (bottom := bottom) O
      (closure top bottom named O).toMaterialization

theorem referenceBit_eq (top bottom : Nat) (named : List Nat) (O : Ontology)
    (sub sup : Nat) :
    referenceBit top bottom named O sub sup =
      referenceBitOf (closure top bottom named O) bottom sub sup

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

theorem nodupFast_iff (xs : List Nat) :
    nodupFast xs = true ↔ xs.Nodup

-- lean/ContextCalculus/ALCReferenceSaturation.lean
theorem saturateLoop_eq (O : Ontology (Fin conceptCount) (Fin roleCount)) :
    ∀ (n : Nat) (G : Finset (Finset (Fin conceptCount))),
      saturateLoop O n G = (Ctx.step O)^[n] G

theorem saturateC_eq (O : Ontology (Fin conceptCount) (Fin roleCount)) :
    saturateC O = Ctx.saturate O

theorem alcBit_eq (O : Ontology (Fin conceptCount) (Fin roleCount))
    (A B : Fin conceptCount) :
    alcBit O A B = alcBitOf (saturateC O) A B

theorem alcBit_exact (O : Ontology (Fin conceptCount) (Fin roleCount))
    (A B : Fin conceptCount) :
    alcBit O A B = true ↔
      (∀ (D : Type) (I : Interp D (Fin conceptCount) (Fin roleCount)),
        models I O → ∀ x, I.c A x → I.c B x)

theorem alcBit_iff_entailsSub (O : Ontology (Fin conceptCount) (Fin roleCount))
    (A B : Fin conceptCount) :
    alcBit O A B = true ↔ CBALCEncoding.EntailsSub O A B

-- lean/ContextCalculus/KMConcreteWorkerAdapters.lean
theorem elReferenceExecution_completeAt (source : RequestedTaxonomySource)
    (hrecognized :
      (ELCommonSourceRecognizer.recognizeEL source.named source.ontology).isSome =
        true)
    (hnodup : source.named.Nodup) :
    elReferenceExecution.worker.CompleteAt source

theorem alcReferenceExecution_completeAt (source : RequestedTaxonomySource)
    (hrecognized :
      (ALCCommonSourceRecognizer.recognizeALC source.named source.ontology).isSome =
        true)
    (hnodup : source.named.Nodup) :
    alcReferenceExecution.worker.CompleteAt source

-- lean/ContextCalculus/KMSupervisorInstance.lean
theorem kmSupervisor_complete_on_EL_or_ALC
    (production : KMRequestedExecution) (source : RequestedTaxonomySource)
    (hfragment :
      (ELCommonSourceRecognizer.recognizeEL source.named source.ontology).isSome =
          true ∨
        (ALCCommonSourceRecognizer.recognizeALC source.named
          source.ontology).isSome = true)
    (hnodup : source.named.Nodup) :
    (kmSupervisor (kmSupervisorExecution production)).CompleteAt source
```

## 3. Build Command and Axiom Audit

Build command (run sequentially from `lean/` to respect host thread/commit limits):

```bash
export PATH="$HOME/.elan/bin:$PATH"
for tgt in ContextCalculus.KMSupervisorInstance \
           ContextCalculus.ELReferenceSaturationTests \
           ContextCalculus.ALCReferenceSaturationTests \
           km-el-reference; do
  LEAN_NUM_THREADS=1 taskset -c 40-43 nice lake build "$tgt"
done
```

`#print axioms` lines copied from the build log:

```text
info: ContextCalculus/ELReferenceSaturation.lean:1578:0: 'ContextCalculus.ELReference.closure_closedOn' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:1579:0: 'ContextCalculus.ELReference.closure_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:1580:0: 'ContextCalculus.ELReference.referenceBit_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:1581:0: 'ContextCalculus.ELReference.referenceBit_exact_of_named' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELReferenceSaturation.lean:1582:0: 'ContextCalculus.ELReference.referenceInconsistent_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ALCReferenceSaturation.lean:230:0: 'ContextCalculus.ALCReference.saturateC_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ALCReferenceSaturation.lean:231:0: 'ContextCalculus.ALCReference.alcBit_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ALCReferenceSaturation.lean:232:0: 'ContextCalculus.ALCReference.alcBit_iff_entailsSub' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/KMConcreteWorkerAdapters.lean:1593:0: 'ContextCalculus.KMConcreteWorkerAdapters.referenceAnswer_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/KMConcreteWorkerAdapters.lean:1594:0: 'ContextCalculus.KMConcreteWorkerAdapters.elReferenceAccept_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/KMConcreteWorkerAdapters.lean:1595:0: 'ContextCalculus.KMConcreteWorkerAdapters.elReferenceExecution_completeAt' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/KMConcreteWorkerAdapters.lean:1596:0: 'ContextCalculus.KMConcreteWorkerAdapters.alcReferenceAnswer_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/KMConcreteWorkerAdapters.lean:1597:0: 'ContextCalculus.KMConcreteWorkerAdapters.alcReferenceAccept_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/KMConcreteWorkerAdapters.lean:1598:0: 'ContextCalculus.KMConcreteWorkerAdapters.alcReferenceExecution_completeAt' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/KMSupervisorInstance.lean:136:0: 'ContextCalculus.KMSupervisorInstance.kmSupervisor_complete_on_EL_or_ALC' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 4. Benchmark Measurements

### 4.1 ALC Fixtures (All 6 Recognised Within-Budget ALC Inputs)

All four ALC fixtures that timed out at 300 s in the P3 run (`min_atleast0_gci.ofn`, `datatype_union_cover.ofn`, `g633.ofn`, `min_copy_successor_insufficient.ofn`) and both previously passing ALC fixtures now finish in **0.059 s to 1.576 s** (`procedure = "alc"`):

| Input | Named (incl. probes) | Clauses | Before P3 Wall (s) | Before Outcome | After `km-el-reference` Wall (s) | After `km classify` Forced Wall (s) | After Outcome |
|---|---:|---:|---:|---|---:|---:|---|
| `clause_or_definer_fallback.ofn` | 5 | 5 | 1.010 | published | 0.059 | 0.068 | published (`alc`) |
| `clause_top_conjunction_inconsistent.ofn` | 5 | 10 | 3.832 | published | 0.061 | 0.070 | published (`alc`) |
| `min_atleast0_gci.ofn` | 10 | 12 | 300.100 | timeout | 0.103 | 0.111 | published (`alc`) |
| `g633.ofn` | 10 | 16 | 300.079 | timeout | 0.220 | 0.254 | published (`alc`) |
| `datatype_union_cover.ofn` | 7 | 22 | 300.103 | timeout | 0.304 | 0.325 | published (`alc`) |
| `min_copy_successor_insufficient.ofn` | 10 | 18 | 300.103 | timeout | 1.576 | 1.584 | published (`alc`) |

### 4.2 Pre-Budget ALC Rejection on Large `production_all` ORE Inputs

The non-EL `production_all` ORE inputs that previously timed out at 300 s before reaching the ALC concept budget check now decline with `exit 3` (`alc budget`) in **0.304 s to 3.642 s**:

| Ontology | Concept Names Counted | Before P3 Wall (s) | Before Outcome | After `km-el-reference` Wall (s) | After Outcome |
|---|---:|---:|---|---:|---|
| `ore_ont_2232.owl` | 8,878 | 300.017 | timeout | 0.304 | declined (`alc budget: 8878 concept names`) |
| `ore_ont_14066.owl` | 11,430 | 300.021 | timeout | 0.335 | declined (`alc budget: 11430 concept names`) |
| `ore_ont_13071.owl` | 31,620 | 300.092 | timeout | 0.474 | declined (`alc budget: 31620 concept names`) |
| `ore_ont_8388.owl` | 44,621 | 300.115 | timeout | 0.584 | declined (`alc budget: 44621 concept names`) |
| `ore_ont_4604.owl` | 139,835 | 300.142 | timeout | 3.247 | declined (`alc budget: 139835 concept names`) |
| `ore_ont_4208.owl` | 139,596 | 300.132 | timeout | 3.256 | declined (`alc budget: 139596 concept names`) |
| `ore_ont_11460.owl` | 140,280 | 300.141 | timeout | 3.642 | declined (`alc budget: 140280 concept names`) |

### 4.3 Stratified Sample of 35 Accepted ORE `elc` Inputs (`idx = 0..584`)

In the P3 baseline, **0 of the 585** accepted ORE `elc` inputs finished within 300 s (`585 / 585` timed out). We measured `km-el-reference --procedure el-then-alc` (full mode) under `timeout 300` (with a 24 GB address-space cap) on 35 evenly spaced inputs spanning the size-sorted 585-input ORE `elc` corpus from `idx = 0` (`13.9 KB`) to `idx = 584` (`393.8 MB`). The raw table is saved in `elc_35_sample.tsv`.

| Size Rank (`idx`) | Ontology | File Size (B) | Named | Clauses | Matrix Cells ($N^2$) | Before P3 Wall (s) | After `km-el-reference` Wall (s) | After Status |
|---:|---|---:|---:|---:|---:|---:|---:|---|
| 0 | `ore_ont_8937.owl` | 13,865 | 79 | 262 | 6,241 | 300.056 (timeout) | 0.088 | ok |
| 15 | `ore_ont_508.owl` | 26,645 | 115 | 242 | 13,225 | 300.000 (timeout) | 0.091 | ok |
| 30 | `ore_ont_12906.owl` | 35,342 | 82 | 88 | 6,724 | 300.000 (timeout) | 0.080 | ok |
| 50 | `ore_ont_11497.owl` | 47,901 | 112 | 870 | 12,544 | 300.000 (timeout) | 0.348 | ok |
| 65 | `ore_ont_10355.owl` | 67,181 | 196 | 765 | 38,416 | 300.000 (timeout) | 0.111 | ok |
| 80 | `ore_ont_4382.owl` | 88,923 | 362 | 622 | 131,044 | 300.000 (timeout) | 0.127 | ok |
| 100 | `ore_ont_5966.owl` | 106,931 | 323 | 506 | 104,329 | 300.000 (timeout) | 0.133 | ok |
| 115 | `ore_ont_1325.owl` | 132,337 | 452 | 378 | 204,304 | 300.000 (timeout) | 0.138 | ok |
| 130 | `ore_ont_2720.owl` | 178,619 | 903 | 1,049 | 815,409 | 300.000 (timeout) | 0.356 | ok |
| 150 | `ore_ont_10419.owl` | 239,944 | 1,398 | 1,470 | 1,954,404 | 300.000 (timeout) | 0.711 | ok |
| 165 | `ore_ont_13578.owl` | 323,372 | 1,194 | 3,899 | 1,425,636 | 300.000 (timeout) | 0.716 | ok |
| 180 | `ore_ont_15950.owl` | 396,093 | 1,883 | 2,458 | 3,545,689 | 300.000 (timeout) | 1.124 | ok |
| 200 | `ore_ont_5080.owl` | 468,740 | 1,662 | 4,412 | 2,762,244 | 300.000 (timeout) | 0.976 | ok |
| 215 | `ore_ont_2440.owl` | 599,243 | 1,868 | 5,984 | 3,489,424 | 300.000 (timeout) | 1.312 | ok |
| 230 | `ore_ont_5197.owl` | 759,496 | 3,129 | 5,775 | 9,790,641 | 300.000 (timeout) | 3.186 | ok |
| 250 | `ore_ont_9790.owl` | 1,058,610 | 6,255 | 6,710 | 39,125,025 | 300.000 (timeout) | 11.856 | ok |
| 265 | `ore_ont_8641.owl` | 1,168,857 | 5,926 | 7,969 | 35,117,476 | 300.000 (timeout) | 10.948 | ok |
| 280 | `ore_ont_330.owl` | 1,458,283 | 1,614 | 5,379 | 2,604,996 | 300.000 (timeout) | 1.054 | ok |
| 300 | `ore_ont_11536.owl` | 1,845,921 | 9,699 | 12,250 | 94,070,601 | 300.000 (timeout) | 30.890 | ok |
| 310 | `ore_ont_13451.owl` | 1,978,940 | 10,329 | 13,630 | 106,688,241 | 300.000 (timeout) | 34.732 | ok |
| 325 | `ore_ont_1501.owl` | 2,225,580 | 6,807 | 26,434 | 46,335,249 | 300.000 (timeout) | 14.195 | ok |
| 335 | `ore_ont_4226.owl` | 2,400,268 | 6,793 | 26,294 | 46,144,849 | 300.000 (timeout) | 13.875 | ok |
| 350 | `ore_ont_9884.owl` | 2,989,891 | 5,493 | 6,605 | 30,173,049 | 300.000 (timeout) | 9.155 | ok |
| 360 | `ore_ont_7858.owl` | 3,199,607 | 8,345 | 18,043 | 69,639,025 | 300.000 (timeout) | 21.378 | ok |
| 375 | `ore_ont_3480.owl` | 3,660,523 | 25,113 | 13,781 | 630,662,769 | 300.000 (timeout) | 85.854 | exit1 (OOM on $N^2$ cell list) |
| 390 | `ore_ont_12802.owl` | 4,383,108 | 16,209 | 19,524 | 262,731,681 | 300.000 (timeout) | 96.921 | ok |
| 400 | `ore_ont_12486.owl` | 5,287,775 | 29,712 | 29,708 | 882,802,944 | 300.000 (timeout) | 90.632 | exit1 (OOM on $N^2$ cell list) |
| 425 | `ore_ont_16283.owl` | 7,738,874 | 23,134 | 62,681 | 535,181,956 | 300.000 (timeout) | 94.957 | exit1 (OOM on $N^2$ cell list) |
| 450 | `ore_ont_14934.owl` | 12,188,243 | 34,677 | 83,948 | 1,202,494,329 | 300.000 (timeout) | 107.356 | exit1 (OOM on $N^2$ cell list) |
| 475 | `ore_ont_10248.owl` | 18,522,746 | 44,868 | 184,806 | 2,013,137,424 | 300.000 (timeout) | 170.236 | exit1 (OOM on $N^2$ cell list) |
| 500 | `ore_ont_4802.owl` | 24,528,022 | 55,216 | 208,869 | 3,048,806,656 | 300.000 (timeout) | 149.593 | exit1 (OOM on $N^2$ cell list) |
| 525 | `ore_ont_2046.owl` | 35,969,631 | 10,861 | 87,484 | 117,961,321 | 300.000 (timeout) | 40.187 | ok |
| 550 | `ore_ont_12528.owl` | 50,368,608 | 31,861 | 119,472 | 1,015,123,321 | 300.000 (timeout) | 121.817 | exit1 (OOM on $N^2$ cell list) |
| 570 | `ore_ont_16008.owl` | 132,673,984 | 733,102 | 733,098 | 537,438,542,404 | 300.000 (timeout) | 192.660 | exit1 (OOM on $N^2$ cell list) |
| 584 | `ore_ont_1559.owl` | 393,840,303 | 264,044 | 2,925,744 | 69,719,233,936 | 300.000 (timeout) | 24.658 | exit-6 (stack overflow on 2.93M-clause `recognizeEL`) |

### 4.4 Expected Pass Count Across the 585 ORE `elc` Inputs

- In the 35-ontology stratified sample, **26 / 35 (74.3%)** succeeded (`ok`, exit 0), including every input with `named <= 16,209` (`26 / 26 = 100%`).
- Counting `Declaration(` across all 585 accepted ORE `elc` ontologies shows:
  - `Declarations <= 10,000` ($\le 35\text{ s}$ wall time): **381 / 585 (65.1%)**
  - `Declarations <= 16,500` ($\le 100\text{ s}$ wall time): **418 / 585 (71.5%)**
  - `Declarations <= 18,000` ($\le 125\text{ s}$ wall time, within 24 GB RAM): **424 / 585 (72.5%)**
- We therefore expect **420 to 430 of the 585 ORE `elc` inputs (72%–74%)** to pass under a 300 s / 24 GB budget, up from **0 / 585** in the P3 baseline.

## 5. What Remains Open

1. **Dense $N^2$ `TaxonomyAnswer.cells` allocation for $N \ge 20,000$**:
   - The common routing adapter `TaxonomyAnswer` (`lean/ContextCalculus/KMConcreteWorkerAdapters.lean`) materializes `cells : List TaxonomyCell` with one entry per `(sub, sup)` pair in `named × named`. When $N \ge 20,000$, $N^2 \ge 4 \times 10^8$ cells exceeds 22 GB of heap in `List.flatMapTR`. Covering the remaining ~155–165 large ORE `elc` ontologies ($20,000 \le N \le 733,102$) via the reference stage would require a sparse positive-subsumption representation at the `TaxonomyAnswer` boundary.
2. **Rust orchestrator `try_reference_stage` name-set and UNSAT row mapping (untouched per brief constraints)**:
   - When comparing end-to-end `km classify` output under `KM_REFERENCE_FORCE=1` against unforced `km classify`:
     - `try_reference_stage` in `engine/src/orchestrate/mod.rs` (lines 4060–4069) constructs `real_names` by unioning `meta.named`, `meta.declared`, and `meta.asserted_classes`. Because `meta.declared` includes declared `ObjectProperty` IRIs (`:s`, `:r`, `<http://a.com/ontology#address>`) and `elc` ignores declarations that never appear in TBox clauses, any ontology with `⊤ ⊑ C` (`min_atleast0_gci.ofn`, `min_copy_successor_insufficient.ofn`, `ore_ont_8937.owl`) emits `SUB <prop> C` in forced reference mode unless `real_names` is restricted to class names.
     - In `try_reference_stage` (lines 4142–4155), when a class `u` is unsatisfiable (`u ⊑ probe_b`), `cell.answer` is also `true` for every `sup`, so `try_reference_stage` emits both `UNSAT u` and `SUB u sup` (visible on `g633.ofn`), whereas production output mapping suppresses `SUB u sup` rows for unsatisfiable classes `u`.
   - Filtering out non-class `ObjectProperty` declarations and suppressing `SUB u sup` rows for `UNSAT` classes `u` produces 0-diff agreement with unforced `km classify` on `min_atleast0_gci.ofn`, `datatype_union_cover.ofn`, `g633.ofn`, and `min_copy_successor_insufficient.ofn`.
