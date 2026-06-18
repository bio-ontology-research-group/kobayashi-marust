# Konclude source study — what it does that KM doesn't, and how to port it

Source read read-only from `github.com/konclude/Konclude` (cloned to `/tmp/Konclude`,
commit at clone time). All file:line refs are into `Source/Reasoner/` of that tree.
Per-subsystem raw notes: `/tmp/konclude-findings-{saturation,classification,tableau,absorption}.md`.

## The one-sentence finding

KM ships **two complete reasoners** — the CB engine (a *complete* consequence-based
disjunctive saturation) and the HT tableau (a *complete* hypertableau) — and runs one
of them over the *whole* ontology. Konclude wins by being **lazy**: an *incomplete*,
non-branching saturation decides the ~95% of concepts that are easy, and a complete
tableau runs only on the small residue, with each surviving test made cheap by
pseudo-model refutation and cross-test caching. KM's CB engine blows up on the live
`∀+⊔` family precisely *because* it is complete — it materialises every incomparable
disjunctive context. Konclude never does, because its saturation never splits.

The good news: **KM already owns the hard pieces** (the `elc` EL-completion = the
saturation core; the canonical-model certificate = the residue check; HT already has
backjumping + disjunction learning + anywhere blocking + VSIDS). The gaps are mostly
about *granularity and wiring*, not missing algorithms.

---

## Konclude's pipeline (confirmed from source)

```
parse → PREPROCESS (absorption → triggered implications)
      → SATURATION (one non-branching deterministic pass over the whole TBox)
      → CLASSIFICATION (KPSet: told/possible subsumers; pseudo-model merge;
                        transitive propagation; real tableau only on the residue)
          └─ each surviving SAT test: CCalculationTableauCompletion
             (semantic branching + VSIDS disjunct order + backjumping +
              anywhere blocking + 3 caches)
```

### 1. Saturation as a residue filter  — `CCalculationTableauApproximationSaturationTaskHandleAlgorithm`
- A single **non-branching** tableau pass. One shared node per (concept, polarity);
  `∃r.C` reuses the *shared* `C`-node instead of a fresh successor
  (`createSuccessorForConcept`, cpp:6918) ⇒ graph size O(#concepts), not O(model).
- Rules applied deterministically: AND/SUB/TOP/EQ/IMPL add operands; `∀r.C`
  propagates **backward** over recorded role links only (cpp:6159); `≤` records a
  cardinality bound; `∃/≥` reuse the shared filler node.
- **Disjunctions are never split.** `applyORRule` (cpp:6021) parks the disjunction and
  (a) if any disjunct is already in the label ⇒ discharged; (b) extracts
  **common disjuncts** — a concept in *every* disjunct's node is a sound subsumer of
  the disjunction (the rule `A⊑X ∧ B⊑X ⟹ A⊔B⊑X`, `CSaturationDisjunctCommonConceptCountHash`).
- Output per concept is exactly one of three states (`CIndividualSaturationProcessNodeStatusFlags.h:121`):
  **CLASHED** (definitely unsat) / **CLEAN** (label is the exact, complete subsumer set)
  / **INSUFFICIENT** (label is a sound lower bound; a real test is still needed).

### 2. KPSet classification  — `Classifier/COptimizedKPSetClassSubsumptionClassifierThread`
Per concept it keeps **K**nown subsumers, **P**ossible subsumers (3-state
unknown/confirmed/invalid), a pseudo-model, and up/down propagation edges. A real
tableau subsumption test is reached only after **four cheaper gates** fail
(cpp:1333-1345):
1. saturation said CLEAN/CLASHED ⇒ **zero tests** for that concept (cpp:340);
2. B is already a known/told subsumer of A;
3. the **pseudo-model merge** refutes `A⊑B` (see below);
4. transitive propagation already decided it: confirmed `A⊑B` propagates **down** to
   A's descendants; refuted `A⋢B` propagates **up** to A's ancestors (cpp:2283/2309).

The statistics line (cpp:2689) literally reports the budget split:
`total = n·(n−1)` resolved into `told + derivation(down) + pruned(up) +
pseudo-model-merged + calculated(real tableau)`. Only the last bucket hits the tableau.

**Pseudo-model merge** (`CClassificationClassPseudoModelRoleData`): a pseudo-model is
the *deterministic* fragment of a concept's completion — a concept-label map (each
flagged deterministic) + per-role cardinality bounds (`mLowerAtLeast/mUpperAtMost…`).
`isPseudoModelSubsumerPossible(A,B)` proves `A⋢B` with a **linear sorted-map merge**:
if a *deterministic* concept of B's model is absent in A's ⇒ not subsumed (cpp:1645);
a role cardinality-interval clash ⇒ not subsumed (cpp:1684), recursing into successor
pseudo-nodes. "No" is certain; "maybe" falls through to a real test. **This is the
direct antidote to KM-HT's ~196k backtracks for one concept** — most non-subsumptions
never reach the tableau at all.

### 3. Preprocessing / triggered-implication absorption  — `CTriggeredImplicationBinaryAbsorberPreProcess`
The anti-`⊔`-blowup device. A global `⊤ ⊑ ¬C ⊔ E` (which untriggered would be added to
*every* node — KM's exact `pred_lteq` root-context blowup) is rewritten to a **dormant
implication keyed on `C`**: `trigger(C): C → E` (cpp:4152). It only materialises once
`C` appears in a node label. Variants: equivalence→told-primitive (B1), binary concept
absorption (B2), role-domain absorption (B3), **nominal→ABox** absorption (B4,
`{a}⊑D ⇒ D(a)`). Plus two cheap sound rewrites: **common-disjunct extraction** (hoist
the intersection of all disjuncts as unconditional facts) and **disjunct sorting**
(cheap deterministic disjuncts first, node-generating last — pure reordering).

### 4. Per-test machinery  — `CCalculationTableauCompletionTaskHandleAlgorithm`
- **Backjumping by resolution.** Every fact carries a dependency trackpoint; a clash's
  descriptor chain is rewritten backwards through the deterministic proof DAG
  (`getBacktrackedDeterministicClashedDescriptors`, cpp:7779) until only branch
  decisions remain, then it jumps to the deepest one and cancels its subtree
  (cpp:7085) and writes the learned core to the unsat cache.
- **Branching:** semantic (`A | ¬A`), disjuncts ordered by a **VSIDS-like statistic**
  (`CDisjunctBranchingStatistics`: clashing disjuncts demoted, satisfying ones
  preferred); boolean simplification before any branch (cpp:16562).
- **Deterministic floor:** a strict rule-priority table fully saturates the graph
  deterministically before any OR branch (AND/ALL/IMPL ≫ SOME ≫ OR).
- **Blocking:** anywhere blocking with optimized pairwise SROIQ condition; cheap via a
  candidate hash bucket (by ∃-filler init concept) + an O(1) 64-bit commutative label
  signature reject (`CConceptSetSignature`).
- **Three caches keyed for reuse across the whole classification:** unsat (occurrence
  trie, **superset** lookup, stores clash core); satisfiable-expander (64-bit label
  signature, **exact** lookup, reuses recorded expansion); completion-graph/reuse
  (node-id **subset** lookup into the once-built consistency model).

---

## What KM already has (so we don't reinvent it)

| Konclude mechanism | KM status |
|---|---|
| Non-branching deterministic saturation | **`elc`** EL-completion (one set/concept, shared successors) — but bails (`None`) on any disjunctive head (`elcomplete.rs:298`) |
| Residue "are parked disjunctions satisfied?" check | **canonical-model certificate** `cert_round` (`elcomplete.rs:856+`) — but **whole-ontology all-or-nothing**, not per-concept |
| Backjumping / dependency-directed backtracking | **HT has it** (`tableau.rs` `DepSet`, `Outcome`) |
| Disjunction (conflict) learning | **HT has it** (no-good learning, task #31/#34) |
| Anywhere blocking + label hashing | **HT has it** (task #63) |
| VSIDS + phase saving + restarts | **HT has it**, gated `KM_TAB_*` (task #37) |
| Pseudo-model caching of blocking verdicts | **HT has it** (task #35) — but for *blocking*, not for *classification* non-subsumption refutation |
| QuasiOrder multi-model pruning | **HT has it** (task #62) |
| Polarity-gated absorption | **`KM_ABSORB`** — weaker than triggered-implication absorption |

So the genuine gaps are: **(a) the saturation is all-or-nothing instead of per-concept**;
**(b) no classification-level pseudo-model refutation gate**; **(c) absorption doesn't
trigger-key global ⊔-GCIs**; **(d) no sat-expander cross-test cache**.

---

## Integration plan (prioritised by leverage / risk)

### P1 — Per-concept saturation residue filter  (highest leverage, mostly reuse)
Turn the existing `elc` + certificate from a whole-ontology gate into Konclude's
per-concept three-state filter.
- **Increment 1 (no Lean re-cert):** instead of `elc` bailing on the first disjunctive
  head, let it complete the EL/deterministic part and *park* disjunctive clauses; reuse
  `cert_round` **per concept** to label each named class CLEAN (cert holds → elc's
  subsumer set for it is complete) or INSUFFICIENT (cert violated). Route **only the
  INSUFFICIENT concepts** to the CB engine / HT, seeded with the saturated label;
  CLEAN/CLASHED concepts take the elc answer with no engine call. This is pure routing
  over already-certified machinery → monotone, no re-cert. Expected to convert most of
  near-Horn (7246/7581) to CLEAN and shrink the disjunction-family and central-blowup
  residue dramatically (fewer concepts ever reach the explosive engine).
- **Increment 2 (one small Lean lemma):** add **common-disjunct extraction**
  (`A⊑X ∧ B⊑X ⟹ A⊔B⊑X`) so subsumers hidden inside disjunctions are recovered without
  splitting — shrinks the INSUFFICIENT residue further. The only new soundness
  obligation is the ⊔-distribution lemma.
- KM files: `elcomplete.rs` (parking + per-concept cert), `reasoner.rs` (residue
  routing), `orchestrate/` (wire as a pre-pass before the CB/HT race).

### P2 — Classification-level pseudo-model merge gate  (antidote to 196k backtracks)
For the HT path, before issuing any tableau subsumption test, build a pseudo-model
(deterministic label + per-role cardinality bounds) from each satisfiable concept's
completion and refute `A⋢B` with the linear merge walk; propagate confirmed-down /
refuted-up transitively. KM already builds completion graphs and already has a
pseudo-model cache for blocking — extend it to the classification gate.
- Soundness: refutation-only (it only *skips* tests that would have returned
  non-subsumer) → no re-cert.
- KM files: `tableau.rs` (pseudo-model extraction + merge), HT classify loop.

### P3 — Trigger-keyed binary absorption + common-disjunct hoisting + disjunct sorting (frontend)
Attack the documented `pred_lteq` root-context blowup at its source. For a ⊤-headed
DL-clause with head `¬C ⊔ rest`, move the negated *named* disjunct into the body
(contrapositive): `body=[C], head=[rest]`, recursively. Hoist common disjuncts as
unconditional facts; sort head disjuncts cheap-first.
- Soundness: contrapositive + disjunct sorting are fixpoint-preserving (no re-cert);
  common-disjunct hoisting reuses the P1.2 lemma.
- KM files: `frontend/normalise.rs`, `frontend/preprocess.rs` (extend `KM_ABSORB`).

### P4 — Satisfiable-expander signature cache + two-stage unsat trie  (amortise tests)
Add a 64-bit commutative label signature; cache satisfiable expansions (exact-set
lookup) and unsat cores (superset lookup) and reuse them across the whole
classification. Monotone-safe, no re-cert.
- KM files: `tableau.rs`.

### Ordering rationale
P1 is the architectural fix and reuses the most existing code — do it first and measure
the INSUFFICIENT residue size per ont family. P2 makes whatever residue remains cheap on
the HT path. P3 attacks the same blowup from the frontend (composes with P1). P4 is a
constant-factor amortiser. P1+P3 directly target the live-`∀+⊔` and context-explosion
families; P1 alone should help central blowup and near-Horn.

### Empirical confirmation (optional next step)
Konclude is already deployed on the benchmark host (it produced the gold sigs). Running
it with classification statistics on 5303 / 10702 / 1603 would print the
`told/derivation/pruned/pseudo-model/calculated` budget split and confirm "very few SAT
tests survive" before we invest in the port.
