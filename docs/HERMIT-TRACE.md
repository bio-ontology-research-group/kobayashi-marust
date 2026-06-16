# How HermiT (and Konclude) solve KM's 26 timeouts — a traced diagnosis

Source data: IBEX reasoner comparison job **47559562** (who solves what) plus a
direct **HermiT classification trace** (job 47561460) that plugs HermiT 1.4.6's
`CountingMonitor` into a classification run and dumps, per ontology, the number
of real tableau satisfiability tests, the total/peak backtracking, node counts,
and blocking counts. The tracer driver is `results/HermitTrace.java`.

## Who solves KM's 26 timeouts

KM's 26: 541, 1603, 2669, 3215, 4604, 5303, 6934, 7246, 7499, 7581, 7914, 9024,
9540, 9635, 9663, 9724, 10621, 10702, 11460, 12141, 12653, 14817, 15491, 15516,
15672, 15803.

| group | onts | solved by | note |
|---|---|---|---|
| **A. HermiT fast (≤6 s)** | 541, 1603, 5303, 6934, 9024, 9635, 10702, 12141, 12653, 15491, 15672 | HermiT 1–6 s, Konclude <1 s | algorithmic — the disjunction family + a few wide/big-model onts |
| **B. HermiT slow (20–470 s)** | 4604, 7499, 7581, 15803 | HermiT + Konclude | wide / large model; HermiT wins by O(n) test count |
| **C. Konclude only** | 3215, 7246, 7914, 9540, 9663, 9724, 10621, 11460, 14817 | Konclude only (HermiT also times out) | central core / context-explosion throughput |
| **D. neither** | 2669, 15516 | nobody gold-clean | SWRL/DLSafeRule; Konclude errors too |

So the portable targets are **A + B** (15 onts HermiT classifies gold-clean).
Group C is Konclude-only and HermiT cannot do it either, so HermiT tracing does
not help there. Group D needs SWRL and has no gold answer.

## The HermiT trace: two distinct mechanisms KM lacks

Decisive columns from `CountingMonitor` (per ontology, over the whole
classification): `tests` = number of tableau satisfiability tests actually run,
`backtracks` = total dependency-directed backtracks, `nodes`/`blocked` = model
size and how much of it blocking folded away.

| ont | classes | **tests** | total backtracks | nodes | blocked | hardest test (bt) | classify ms |
|---|--:|--:|--:|--:|--:|--:|--:|
| 5303 | 95 | 128 | 14458 | 8829 | 6433 | 236 | 680 |
| 10702 | 138 | 172 | 39018 | 36038 | 0 | ~227 avg | 2131 |
| 12653 | 22 | 16 | 785 | 193 | 6 | ~49 avg | 48 |
| 12141 | 280 | 207 | 130 | 3097 | 1364 | <1 | 90 |
| 9024 | 280 | 209 | 132 | 3088 | 1350 | <1 | 70 |
| 1603 | 350 | 187 | 78 | 11470 | 6466 | <1 | 1354 |
| 541 | 60 | 60 | 23 | 4049 | 1674 | <1 | 221 |
| 15672 | 83 | 45 | 40 | 1750 | 46 | ~1 | 754 |
| 6934 | 146 | 71 | **0** | 68784 | 11594 | 0 | 1943 |
| 15491 | 5440 | 2926 | 16 | 41234 | 24702 | 0 | 622 |
| 4604 | **83200** | 65603 | 15 | 133846 | 12126 | 0 | 172426 |
| 1340 (KM-easy baseline) | 3718 | 3721 | 0 | 5965 | 2 | 0 | 103 |

### Mechanism 1 — classification runs ≈ O(n) satisfiability tests, not O(n²) and not full saturation

Look at `tests` vs `classes`. A naive pairwise classifier needs ~n² subsumption
tests; KM's CB engine instead *saturates* (derives everything at once). HermiT
does neither: for 4604 (83,200 classes) it runs **65,603 tests** — a naive
classifier would need ~6.9 *billion*, and saturating 4604 is exactly what blows
KM up. For 15491 (5,440 classes) HermiT runs 2,926 tests vs ~30 M naive. The
test count is roughly *linear* in the number of classes.

This is HermiT's `QuasiOrderClassification`: build the told-subsumer relation,
run **one** saturated model at ⊤ to read off "possible subsumers" (B is a
possible subsumer of A only if B labels A's node in that model), then run real
tableau tests only for the genuinely ambiguous pairs, traversing the partial
order top-down so each confirmed subsumption prunes the rest. The win on the
wide ontologies (4604/15491/6934, group B + part of A) is entirely this: bounded
test count + cheap tests, near-zero backtracking.

KM's CB engine has no equivalent — it derives the whole subsumption set by
saturation, and on these wide / deep-model ontologies the saturation itself is
the timeout.

### Mechanism 2 — each individual test is cheap: precise backjumping + blocking

For the search-bound onts (5303/10702/12653) HermiT *does* backtrack, but very
little: 5303's hardest single test does **236 backtracks**; the whole 5303
classification does 14,458. KM's existing hypertableau port (`ht-port` branch)
does **~196,000 backtracks for a single concept** on 5303 (recorded in
`project_km_family_diagnosis`) — roughly **1000× worse per test**. Same family,
same clauses, the gap is purely search efficiency.

Blocking does heavy lifting for HermiT: on 5303, 6,433 of 8,829 nodes are blocked
(73 %); on 15491, 24,702 of 41,234. Anywhere blocking + dependency-directed
backjumping together keep each test to a few hundred backtracks.

## What this means for KM

KM's `ht-port` branch already has the *structure* of Mechanism 2 — a DFS with
dependency-set backjumping (`!dep_contains(cd, level)` early-return that skips
sibling disjuncts), CDCL no-good learning, anywhere blocking, delta propagation.
What it does not have is HermiT's *effectiveness* (1000× more backtracks per
test) or Mechanism 1 at all (it re-runs a from-scratch `consistent()` per query;
no told-subsumer / one-model possible-subsumer pruning).

## ht-port profile: where KM's tableau actually loses (job 47562165)

Ran the `ht-port` hypertableau (`KM_HT=1 KM_HT_STATS=1`, default config) on the
same onts, 90 s cap. All timed out; the heartbeat at timeout localizes why
(compare to HermiT's whole-classification numbers above):

| ont | concepts | KM nodes | KM depth | KM pending-disj | KM backtracks | HermiT nodes |
|---|--:|--:|--:|--:|--:|--:|
| 5303 | 303 | 536 | 421 | 2,554 | 16,113 | 168 (per test) |
| 12141 | 926 | 2,349 ↑ | 1,499 ↑ | 17,353 | 848 | 27 |
| 9024 | 926 | 7,559 ↑ | 22,174 ↑ | 55,441 | 17,301 | 27 |

The picture is **not** "KM backtracks 1000× more" — on 5303 the backtrack counts
are comparable (16 k vs 14 k). The picture is **the model is unbounded**: HermiT
folds 9024 to **27 nodes** (16 blocked); KM builds **7,559 and climbing**, with a
decision stack 22,174 deep and **55,441 pending disjunctions**. With a model that
large, the disjunction count explodes and the search drowns. Two concrete causes,
both visible in the code:

1. **Anywhere blocking is OFF by default** (`KM_HT_ANYWHERE` unset → only
   ancestor/subset blocking up the predecessor chain). Ancestor blocking cannot
   catch a repeated label on a *sibling* branch, so successors are never folded
   and the model grows without bound. HermiT blocks 73 % of 5303's nodes; KM's
   default config blocks almost none.
2. **The deterministic disjunction scan is O(pending) per step** (`KM_HT_WATCH`
   unset → `next_action_from_pending` rescans all pending each step). On 9024 the
   heartbeat tick reached ~1e9 for 57 k real steps — ~17 k wasted scan-iterations
   per step, exactly `pending`.

This reframes the earlier conclusion in `project_km_family_diagnosis`
("blocking-alone won't transfer; branch count is the killer"): that was measured
on the legacy `tableau.rs` path. On the ht-port engine, **bounding the model
(effective blocking) is the dominant lever** — it is what makes HermiT's branch
count small in the first place. The next experiment (job 47562222) re-runs with
`KM_HT_ANYWHERE=1 KM_HT_WATCH=1` (and a full search-discipline arm) to confirm
the model bounds and the family solves.

## Concrete plan (in leverage order)

1. **Localize the 1000× per-test gap on 5303** by running `ht-port` with
   `KM_HT_STATS` and comparing its backtrack/node/depth profile to HermiT's
   (236 bt, 73 % blocked). Candidates: dependency-set imprecision (a derived
   fact carrying levels it does not truly depend on degrades backjumping toward
   chronological), blocking not firing enough (full-label `label_eq` is far
   stricter than HermiT's core blocking), or branch selection (HermiT's
   activity/most-constrained pick vs ht-port's program order). The trace says
   blocking matters a lot for HermiT, so under-blocking is the leading suspect.

2. **Port Mechanism 1 (QuasiOrderClassification)** on top of whichever model
   engine wins: told-subsumers from the clause set + one saturated ⊤-model →
   possible-subsumer matrix → ordered top-down tests. This is what unlocks the
   wide onts (4604/15491) and slashes the test count everywhere. It is engine-
   agnostic: it can wrap the CB engine's per-query mode or the hypertableau.

3. **Route by fragment**: ALC(H) disjunction-family onts → fixed hypertableau;
   keep CB/EL for everything it already wins. Gate behind a flag, validate
   gold-clean on the recovered onts, then measure average time/mem on the full
   corpus before any default-on (per the governing metric in PERF-LEDGER.md).

Group C (Konclude-only throughput onts) is **out of scope for HermiT porting** —
HermiT times out on them too; they need the central core-growth / memory work
tracked separately.

## Implemented + validated (ht-port branch, 2026-06-16)

Step 1 was carried out and it directly recovers ontologies. Two changes to
`engine/src/hypertableau.rs`:

1. **Effective anywhere-subset blocking** (`compute_blocked`, forward pass, a
   blocked node never blocks). The old anywhere path keyed a hash cache on each
   node's *creation-time* (incomplete) label, so it never fired; the new pass
   does real anywhere blocking. Three modes (`KM_HT_BLOCK`): **1=subset**
   (default — superset label, folds most), 0=core (positive-concept equality),
   2=full equality. Empirically only subset folds enough to terminate.
2. **Incremental disjunction scan + anywhere blocking are now default-on**
   (`KM_HT_NO_WATCH` / `KM_HT_ANCESTOR_ONLY` to revert). The old default
   rescanned all pending disjunctions every step (O(pending)); on 9024 that was
   ~17 k wasted iterations per step.

Measured on IBEX (km-htport build, `tableau_cli` with `KM_HT=1`, default config),
versus the prior all-timeout baseline:

| ont | result | wall | peak RSS | model nodes (was) | gold |
|---|---|--:|--:|---|---|
| 12141 | solved | 8.4 s | 4 MB | 217 (timeout) | **GOLD-CLEAN** |
| 9024 | solved | 111 s | 12 MB | 101 (7,559↑) | **GOLD-CLEAN** |
| 5303 | solved | 0.93 s | 1 MB | 61 (timeout) | incomplete by 1 |

Unit tests: 39 passed / 0 failed. The blocking fold matches HermiT's mechanism
(9024: 7,559→101 nodes; HermiT 27).

**The blocking trade-off (measured).** Folding power: subset > full-eq ≈ core.
Only subset terminates in time. Subset is sound + complete for ALC(H) *without*
transitive roles; with transitivity it can be incomplete — on 5303 it drops one
transitivity-dependent subsumption (`CarbonHydrogenSubstructure ⊑ Hydrocarbon`),
**0 unsound**. Full-equality and core blocking are complete but fold too little
and time out (200 s). So:

- **12141, 9024 are recovered gold-clean today** (no transitive roles → subset is
  complete).
- **5303** is fast but needs a complete-and-folding blocking for transitive roles
  (HermiT's pairwise/core-on-stable-label, or proper transitivity encoding so
  subset stays complete) — the remaining work.

(Note: 12141/9024 do contain `TransitiveObjectProperty` declarations, but their
transitivity is vacuous for the class hierarchy, so subset blocking is complete
on them; the full sweep below skip-routes them anyway under the conservative
transitivity guard.)

## Full-corpus gold sweep with KM_HT routed on (job 47563108)

Routed every corpus ont to the fixed hypertableau **iff** ALC(H) (no number /
inverse / nominals) **and** no transitive roles, comparing to Konclude gold.
`results/ht_route_one.py` + `results/revalidate.py`.

The raw sweep flagged 19 "unsound" onts, but that was a **comparison artifact**:
KM's tableau output carries a `__<sourcefile>` localname-disambiguation suffix
(`birnlex_878__NIF-GrossAnatomy.owl` vs gold `birnlex_878`) and emits
`X ⊑ owl:Thing` / `X ⊑ X`, which the gold sigs filter. Re-validating with proper
canonicalisation (strip `__`, drop owl:Thing/Nothing supers + self-subsumptions),
over the **272 routed onts**:

| outcome | count |
|---|--:|
| **gold-clean** | **250** |
| incomplete (0 unsound) | 9 (8 minor 1–26 missing; 7216 near-total) |
| timeout (240 s) | 12 (all non-transitive ALC(H)) |
| missed inconsistency | 1 (**6720**: KM consistent, gold inconsistent) |
| **spurious-subsumption unsound** | **0** |

- **KM_HT is sound on subsumptions corpus-wide** (0 spurious after
  canonicalisation) — the anywhere-subset blocking fix validated at scale.
- **Not yet a safe production route**: 1 missed inconsistency (6720) + 9
  incomplete (subset blocking is sound but not reliably complete — and
  incompleteness appears on non-transitive onts too, so the transitivity guard
  does not guarantee it).
- **Recovery targets excluded**: all 26 production timeouts carry transitive
  roles → skip-routed → KM_HT recovers **0** as-is. And 5303's transitivity is
  *dropped upstream* (its TInput has 0 composition clauses, `fenced=[]`), so the
  gap is in `ofn`/`ofn_rbox`, not blocking.

Verdict: keep KM_HT **gated OFF**. The fix is sound and gold-clean on the large
majority, but enabling the route today would add the 6720 inconsistency miss and
9 incomplete answers while recovering none of the timeout targets.

### Side experiments (smaller jobs, same session)

- **Mechanism 1** (told-subsumers + transitive closure, `KM_HT_NO_TOLD`):
  gold-clean but **0 speedup** on the family (9024 1:52.8 vs 1:52.2) — the cost
  is a few hard per-test searches, not test count. Helps wide shallow onts, but
  those route to elc.
- **Transitivity encoding** (`cb_to_ht.py` Horrocks–Sattler ∀-propagation,
  `KM_HT_NO_TRANS_ENC`): implemented but inert on 5303 (composition clause
  dropped upstream — nothing to detect). Needs the frontend fix first.
- **Blocking-mode battery on 5303**: only subset terminates; core (positive-eq)
  and full-eq time out even on this tiny ont — sound-and-complete blocking is too
  slow, the central tension.

## Concrete plan (in leverage order)
