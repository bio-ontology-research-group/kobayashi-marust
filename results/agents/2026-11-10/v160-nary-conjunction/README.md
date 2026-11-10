# v1.6.0 N-ary Conjunction Extension in `ELCommonSourceRecognizer`

## Overview

In the initial P2 measurement (`results/agents/2026-11-09/v160-reference-binary/p2-recognition.tsv`), 114 of the 118 rejected `elc`-routed inputs failed with `not recognised: nary_concept_conjunction`: the frontend emitted a single clause `⟨[C A1(x), C A2(x), ..., C An(x)], [C D(x)]⟩` (or empty head for n-ary disjointness) with $n \ge 3$ body concept atoms on the same variable, whereas `ELCommonSourceRecognizer.parseClause` accepted only binary `nf2` bodies ($n = 2$).

We extended `ELCommonSourceRecognizer.lean` so that `recognizeEL` compiles any $n$-ary same-variable concept conjunction body ($n \ge 3$, whether concept names are distinct or repeated) into an `nf2` prefix chain with $n - 2$ fresh auxiliary concepts:

$$\text{nf2}(A_1, A_2, P_2),\ \text{nf2}(P_2, A_3, P_3),\ \dots,\ \text{nf2}(P_{n-1}, A_n, D)$$

(and the empty-head disjointness form ending in `bottom`).

## Formalisation Details

- **Fresh auxiliary allocation**: `freshBase named items = maxNatList (named ++ itemsConcepts items) + 1` bounds all source concepts and all concepts in `named` strictly below `freshBase named items`, while `selectTop named items <= freshBase named items` and `selectBottom named items <= freshBase named items + 1`. Starting conjunction auxiliary allocation at `firstAux := freshBase named items + 2` guarantees that every auxiliary concept is strictly greater than all source concepts, all `named` concepts, `top`, and `bottom`, and that distinct n-ary clauses receive disjoint auxiliary ranges `[nextAux, nextAux + (n - 2))`.
- **Soundness direction (`recognizeItems_models_to_satParsedItem`)**: `compileConjChain_derives` proves by induction on the chain that any `ELCompletion.Interp` satisfying all clauses in `compileConjChain acc middle rem target nextAux` satisfies `I.concept target u` whenever `I.concept acc u`, `I.concept middle u`, and `∀ c ∈ rem, I.concept c u` hold (and for `naryConjBottom`, `I.bottom_false u` yields `False`).
- **Completeness / model-extension direction (`recognizeItems_satParsedItem_to_models`)**: `compileConjChain_extend_interp` extends an `ELCompletion.Interp` along the prefix chain by interpreting each fresh auxiliary concept $P_k$ as the conjunction of the two preceding concepts (`setAuxConcept`), preserving `I.role` and `I.concept c` for all $c < \text{nextAux}$. `compileDirect_models` threads the extended interpretation across `items` while preserving all concepts below `firstAux` (including all `named` concepts, all source concepts, `top`, and `bottom`).
- **Unchanged theorem signatures and axioms**: `recognizeEL_entails_iff`, `recognizeEL_unsat_iff`, and `kmSupervisor_complete_on_EL_or_ALC` keep their exact statements and depend only on `[propext, Classical.choice, Quot.sound]`.

## Axiom Verification

Command:
```bash
LEAN_NUM_THREADS=2 taskset -c 0,1 nice lake build \
  ContextCalculus.KMSupervisorInstance \
  ContextCalculus.ELCommonSourceRecognizerTests \
  km-el-reference
```

Output:
```text
info: ContextCalculus/ELCommonSourceRecognizer.lean:1915:0: 'ContextCalculus.ELCommonSourceRecognizer.recognizeEL_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/ELCommonSourceRecognizer.lean:1916:0: 'ContextCalculus.ELCommonSourceRecognizer.recognizeEL_unsat_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ContextCalculus/KMSupervisorInstance.lean:136:0: 'ContextCalculus.KMSupervisorInstance.kmSupervisor_complete_on_EL_or_ALC' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Unit Tests (`lean/ContextCalculus/ELCommonSourceRecognizerTests.lean`)

Added six executable unit tests (`#eval` and `decide`):
1. Three-atom body (`A1(x) ∧ A2(x) ∧ A3(x) → D(x)`).
2. Five-atom body (`A1(x) ∧ A2(x) ∧ A3(x) ∧ A4(x) ∧ A5(x) → D(x)`).
3. N-ary disjointness (`A1(x) ∧ A2(x) ∧ A3(x) → ⊥`).
4. Two n-ary clauses in one source, verifying distinct fresh auxiliary concept IDs across clauses.
5. Repeated concept inside one body (`A1(x) ∧ A1(x) ∧ A2(x) → D(x)`).
6. Semantic check via `KMConcreteWorkerAdapters.referenceAnswer` confirming that `1 ⊑ 2`, `1 ⊑ 3`, `1 ⊑ 4`, and `2 ⊓ 3 ⊓ 4 ⊑ 5` reports `1 ⊑ 5` (`answer = true`) and not `5 ⊑ 1` (`answer = false`).

## Updated P2 Recognition Table (593 `elc`-routed inputs)

Per-input results (with separate `dump_s` and `rec_s` timings) are recorded in `results/agents/2026-11-10/v160-nary-conjunction/p2-recognition.tsv`.

| Outcome / Rejection Reason | Prior Count | New Count | New Share (%) | Example Input | Notes |
| --- | ---: | ---: | ---: | --- | --- |
| **Accepted (`recognised`)** | 475 | **589** | **99.33%** | `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_10008.owl` | `ELCommonSourceRecognizer.recognizeEL` returns `some` (exit 0); all 114 prior `nary_concept_conjunction` inputs are now accepted |
| **Rejected (total)** | 118 | **4** | **0.67%** | | |
| `not recognised: nary_concept_conjunction` | 114 | **0** | **0.00%** | `-` | Eliminated (114 -> 0) |
| `exit 124` (300 s recogniser timeout) | 3 | **3** | **0.51%** | `/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_11395.owl` | `ore_ont_11395.owl`, `ore_ont_14042.owl`, `ore_ont_1559.owl`; see timeout diagnosis below |
| `not recognised: individual_or_constant_term` | 1 | **1** | **0.17%** | `engine/tests/fixtures/finite_rule_taxonomy.ofn` | Clause 11 has grounded DL-safe rule constants before `finite_rule_class_projection` rewrites to a TBox-only ontology for `elc` |
| **Total `elc`-routed inputs** | **593** | **593** | **100.00%** | | |

### Breakdown by Family

- **ORE 2015 (`ore`, 585 inputs)**: **582 accepted (99.49%)**, 3 rejected (all 3 are `exit 124` timeouts).
- **Fixtures (`fixture`, 8 inputs)**: **7 accepted (87.50%)**, 1 rejected (`finite_rule_taxonomy.ofn`, `individual_or_constant_term`).

## Diagnosis of the 3 Timeouts

In `run_p2_measurement.py`, each input runs two subprocesses with separate 300 s `timeout` wrappers:
1. **Clause dump step**: `timeout 300 km classify --route auto <ont_path>` with `KM_KEEP_CLAUSES=<work_dir>`, `KM_REFERENCE_FORCE=1`, `KM_REFERENCE_STAGE=0`.
2. **Recogniser step**: `timeout 300 km-el-reference --recognize-only <clauses.json>`.

| Input | `.owl` Size | `clauses.json` Size | Total Clauses | `nf3Role` Halves | `nf3Filler` Halves | Clauses with `body.len >= 3` | Step 1 (`km classify` dump) | Step 2 (`km-el-reference --recognize-only`) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `ore_ont_11395.owl` | 173.85 MB | 282.95 MB | 1,331,669 | 150,890 | 150,890 | 0 | **40.10 s** (succeeds) | **300.16 s (`exit 124` timeout)** |
| `ore_ont_14042.owl` | 159.10 MB | 282.95 MB | 1,331,669 | 150,890 | 150,890 | 0 | **41.06 s** (succeeds) | **300.07 s (`exit 124` timeout)** |
| `ore_ont_1559.owl` | 393.84 MB | 536.76 MB | 2,925,744 | 225,283 | 225,283 | 0 | **76.53 s** (succeeds) | **300.15 s (`exit 124` timeout)** |

### Findings

1. **Which step timed out**: On all three inputs (`ore_ont_11395.owl`, `ore_ont_14042.owl`, `ore_ont_1559.owl`), **Step 1 (the Rust clause dump) completes well within the 300 s limit** (40.1 s, 41.1 s, and 76.5 s), producing `clauses.json` files of 282.95 MB (1.33M clauses) and 536.76 MB (2.93M clauses). **Step 2 (`km-el-reference --recognize-only`) is the step that hits the 300 s timeout (`exit 124`)** on all three inputs.
2. **Why the recogniser is the cost**:
   - First, `KMELReferenceCheck` reads the 283–537 MB `clauses.json` file into memory and parses it with `Lean.Json.parse` followed by `KMELReferenceCheck.parseSource`.
   - Second, and dominantly, `ELCommonSourceRecognizer.buildNF3Clauses` pairs `roles : List (Nat × Nat × Nat)` and `fillers : List (Nat × Nat × Nat)` using quadratic list operations:
     - `(roles.map Prod.fst).Nodup` and `(fillers.map Prod.fst).Nodup` (`List.Nodup` is $O(M^2)$ pairwise comparisons),
     - `roles.all (halfMatches fillers)` and `fillers.all (halfMatches roles)` (each calling linear `lookupHalf` over a list of length $M$, $O(M^2)$),
     - `roles.filterMap` calling linear `lookupHalf` ($O(M^2)$).
   - On `ore_ont_11395.owl` and `ore_ont_14042.owl`, $M = 150,890$ (`nf3` pairs), so $M^2 = 2.28 \times 10^{10}$ list steps per pass; on `ore_ont_1559.owl`, $M = 225,283$, so $M^2 = 5.08 \times 10^{10}$ list steps per pass.
3. **No n-ary conjunctions in the 3 timeouts**: All three timeout ontologies have 0 clauses with `body.length >= 3`.
