# KM performance ledger — algorithmic changes and their measured effect

Scope: the ORE-2015 coverage/performance push. Every algorithmic change is listed
with its **measured** effect and the **keep/drop** decision under the governing
metric: *average and median time and memory over the full corpus, not pass-rate.*
Keep a change iff it improves average **or** median wall **or** RSS without a
worse regression elsewhere; drop a change that worsens the average even if it
recovers ontologies.

Decisive measurement = the **average-performance portfolio** (IBEX job 47543510,
584 onts, 240 s / 20 GB, 16 cores; means/medians over the 555 onts every arm
solves). Each arm is a flag combination on top of the rebuilt engine.

## A. The portfolio table (the data the decisions rest on)

| arm | engine + flags | #ok | gold DIFF | mean wall | med wall | mean RSS MB | med RSS MB |
|-----|----------------|----:|----------:|----------:|---------:|------------:|-----------:|
| old        | deployed baseline binary, minimal env            | 555 | 0 | 2.44 | 0.26 | 443 | 31 |
| new        | clauses_cand + SmallVec binary (183c3c8)         | 556 | 0 | 2.40 | 0.25 | 431 | 34 |
| new+seq    | + KM_SEQ_ORDER forced on globally                | 555 | 0 | 2.57 | 0.26 | 439 | 33 |
| new+absorb | + KM_ABSORB + KM_ABSORB_PORTFOLIO                | 558 | 0 | **2.24** | 0.25 | **367** | 31 |
| new+tab    | + KM_TAB_RACE + tableau feature/conv flags       | 557 | 0 | 2.46 | **0.33** | 432 | 32 |
| new+full   | seq + absorb + tab (the prior production stack)  | 559 | 0 | 2.37 | 0.33 | 372 | 30 |

Recoveries vs `old` (0 regressions, 0 gold mismatches in every arm):
`new` → 16444; `new+absorb` → 10908, 16444, 6212; `new+tab` → 16444, 9635;
`new+full` → 10908, 16444, 6212, 9635.

**Pareto winner under the metric: `new+absorb`** — lowest mean wall (2.24),
lowest mean RSS (367), no median-wall tax, +3 onts, gold-clean.

## B. Per-change ledger

Format: change — measured effect — decision.

### Engine / calculus (CB context engine)

1. **clauses_cand precompute + SmallVec head-index postings** (`183c3c8`,
   the `new` binary). Mean wall 2.44 → 2.40, mean RSS 443 → 431, +16444, 0
   regress. **KEEP — new production baseline binary.**

2. **KM_SEQ_ORDER — Sequoia-faithful named-vs-definer literal ordering**
   (`5466c45`). Forced on globally: mean wall 2.40 → **2.57 (slower)**, loses
   16444 (#ok 556 → 555). On the disjunction subset alone it recovers +6
   (5107/6246/6682/10908/11016/11291) gold-clean. **KEEP, but auto-routed
   only** (next item) — never global.

3. **Auto-route KM_SEQ_ORDER by DISJ_INT** (`9aee987`): enable the definer
   ordering iff a clause head holds a disjunction over an internally-introduced
   definer (the only onts that benefit). Full-corpus A/B: same +6, net **−24.6 %
   wall** on the routed subset, 0 regressions, gold-clean. `KM_SEQ_ORDER` /
   `KM_NO_SEQ_ORDER` still force the decision. **KEEP — default behaviour of the
   live binary.** Confirms why arm `new+seq` (global) loses: the ordering is a
   specialist, not a global win.

4. **Clause interning (Pred pipeline + global arena)** (`864...`): peak RSS
   −77 % on memory-bound onts (9944 8.5 → 2.0 GB), output-identical.
   **KEEP — default.**

5. **Complete disjunctive case analysis (same-term literals incomparable)**
   (`901...`): correctness fix (closes a completeness gap). **KEEP — default.**

6. **Backtracking-join Hyper rule + batched propagation + adaptive
   parallel-then-single-thread retry**: throughput/scheduling, fixpoint-preserving
   (no Lean re-cert). Net faster on large onts, memory-aware. **KEEP — default.**

7. **Symmetric-group pruning in the Hyper join; ≥n / ≤n recognition; chain-domain
   recognition; central successor cores hold facts only**: correctness +
   coverage on cardinality/chain onts (16461 etc.), gold-clean. **KEEP — default.**

### Frontend (`ofn`)

8. **Streaming parse + compact DLClause** (`ac153ef`): frontend peak 19.2 → 3.6
   GB on the giant 8737, byte-identical clause output. **KEEP — default
   (resource only, no logic change).**

9. **KM_ABSORB — polarity-gated definitional clausification** (`f706521`):
   guards disjunctive GCIs. +10 ORE coverage standalone (545 → 555). In the
   portfolio (as part of `new+absorb`) it drives mean wall 2.40 → 2.24 and mean
   RSS 431 → 367. **KEEP — enabled in the live config.**

10. **Inverse-role bridge clauses; sound ABox-inconsistency precheck;
    data-property axioms + concrete-domain oracle; EquivalentObjectProperties**:
    correctness fixes (8+ incomplete → agree; 4 unsound → agree; datatype gap
    closed). **KEEP — default.**

### Orchestrator (`owl_classify.py`)

11. **KM_ABSORB_PORTFOLIO — sequential plain-probe-then-absorbed** (deployed):
    runs the absorbed clause set, with the plain set covering the rare absorption
    blow-up (6246). Part of the `new+absorb` win above; recovers 10908/6212/16444.
    **KEEP — enabled in the live config (with `KM_ABSORB`).**

12. **KM_TAB_RACE — lazy/niced label-caching tableau race** (+ KM_TAB_FEAT /
    KM_TAB_CONV / KM_TAB_CACHE / convergence control). Recovers 9635 (and the
    2313/2066/5089 disjunction-family onts when the engine alone times out).
    Cost: a **systematic median-wall tax 0.25 → 0.33 s** (seen identically in
    both `new+tab` and `new+full`) for a net **+1** ontology beyond absorb (9635;
    2313/2066/5089 are already solved by the CB engine in `new+absorb`).
    **DROP from the default** under the avg-time metric. Stays env-gated
    (`KM_TAB_RACE=1` re-enables it; expected effect +9635, −median wall). The
    machinery is sound and validated; it is a coverage specialist, not an
    average-performance win.

13. **Dynamic work-stealing query scheduler** (`7bc8611`): parallel classification
    across named concepts, 8/8 byte-identical. **KEEP — default.**

### EL fast path (`elc`)

14. **Clone-free EL completion hot loop** (`cd60ce3`): 8737 classify 252 → 221 s,
    recovered it in the pipeline; byte-identical. **KEEP — default.**

15. **Skolem-exclusion in EL routing** (`72acb3a`): recovered the giant 16744.
    **KEEP — default.**

16. **EL canonical-model completeness certificate** (`cb508c6`, `KM_ELC_CERT`):
    inert on ORE, sound opt-in for near-EL onts. **KEEP gated, default OFF**
    (no average effect on the corpus).

## C. ht-port (hypertableau port) — research branch, NOT integrated

Branch `ht-port` (12 commits, `engine/src/hypertableau.rs`, gated behind
`KM_HT`, not in the production path). Built to attack the live ∀+⊔ disjunction
family. Each search lever was measured on 5303/9024/2313/2066/5089:

| change | effect | decision |
|--------|--------|----------|
| INCR 1–6: DependencySet, hyperresolution matcher, ∃-expansion, backjumping DFS, incremental propagation | reaches a model in ~20 ms then (pre-fix) bailed to legacy tableau on head Role atoms | foundation |
| **Head role-edge support (ALC-H)** (`d531805`) | recovers 5303 *global* consistency: timeout → 0.06 s (the family's real blocker was a missing role-hierarchy head rule, not search) | the one real win on this branch |
| Model-based classification (`d5fdde3`) | sound; per-concept classification still search-bound (5303: ~196 k backtracks for one concept; 9024: 4922-node model) | correct, no family-level win |
| INCR 7: activity ordering + branch-pick + Luby restarts (`e004246`) | **0 onts recovered**; no measurable effect on the family search | drop (gated OFF) |
| Incremental "watch" disjunction scan (`fc24ae7`) | correct, **slightly slower** on 2313; controls byte-identical | drop (gated OFF) |
| CDCL conflict-clause learning (`400ea8e`) | correct (39 tests, controls byte-identical), **family still times out** — learned no-goods over transient successor nodes go dormant on backtrack, so learning underperforms (matches legacy KM, which also has learning + caching and still fails 5303) | drop (gated OFF) |

**Conclusion:** every standard search lever (ordering, branch-pick, restart,
incremental scan, CDCL learning) is closed with proof; none win on average or
close the family. The branch is banked. Closing the family needs the full
HermiT/Konclude optimisation stack (cross-node label/core caching, model
merging) — months, coverage-only, not an average-performance lever.

## D. Integrated live configuration (post-integration)

Engine binary: **`new`** (clauses_cand + SmallVec, payg-strategy HEAD).
Flags in the production config:

```
KM_ABSORB=1            # polarity-gated absorption (win: mean wall + RSS)
KM_ABSORB_PORTFOLIO=1  # plain-probe then absorbed (win: +3 onts, gold-clean)
# seq ordering: auto-routed by DISJ_INT (no env) — specialist, never global
# KM_TAB_RACE: NOT set — dropped (median-wall tax for +1 ont)
```

Expected vs the prior production stack (`new+full`): mean wall 2.37 → 2.24,
mean RSS 372 → 367, median wall 0.33 → 0.25; coverage 559 → 558 (−9635, which
`KM_TAB_RACE=1` recovers on demand). Gold-clean (0 DIFF) in every measured arm.

Each enabled branch fires on ≥1 ontology: absorption portfolio on 6212/10908/16444;
seq auto-route on 5107/6246/6682/10908/11016/11291; the new-binary path on all.
