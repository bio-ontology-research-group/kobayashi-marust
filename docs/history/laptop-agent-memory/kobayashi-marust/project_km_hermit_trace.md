---
name: project_km_hermit_trace
description: "Traced HOW HermiT solves KM's 26 ORE timeouts (CountingMonitor); two portable mechanisms KM lacks"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-16 (user-directed): traced HermiT 1.4.6 on KM's 26 timeouts to find the
firing feature and port it. Tracer = `results/HermitTrace.java` (plugs HermiT's
`CountingMonitor` into classifyClasses, dumps per-ont tests/backtracks/nodes/
blocked via reflection). Full writeup = `docs/HERMIT-TRACE.md`. Data: IBEX cmp
job 47559562 (who-solves) + HermiT trace job 47561460.

**Who solves KM's 26** (cmp2_res): konclude 24, hermit 15 gold-clean, elk 6.
- A. HermiT-fast (≤6s, ALGORITHMIC): 541 1603 5303 6934 9024 9635 10702 12141 12653 15491 15672
- B. HermiT-slow (20-470s, wide/big-model): 4604 7499 7581 15803
- C. Konclude-ONLY (hermit also times out, throughput/central): 3215 7246 7914 9540 9663 9724 10621 11460 14817
- D. neither (SWRL, konclude errors): 2669 15516
Portable = A+B (HermiT can do them). C is NOT HermiT-portable (it can't either).

**Two mechanisms KM lacks (the "why"):**
1. **O(n) SAT tests, not O(n²)/not saturation** = HermiT QuasiOrderClassification.
   4604: 83200 classes → only **65603 tests** (naive ~6.9B); 15491: 5440 cls → 2926 tests.
   told-subsumers + ONE ⊤-model → possible-subsumer matrix → ordered top-down tests.
   KM's CB engine SATURATES instead → the saturation IS the timeout on wide onts.
2. **Cheap per-test search** = precise dependency-directed backjumping + anywhere
   blocking. 5303 hardest test = **236 backtracks** (whole classify=14458); KM's
   ht-port does **~196k backtracks for ONE concept** (≈1000x worse, see
   [[project_km_family_diagnosis]]). 5303: 73% of nodes BLOCKED (6433/8829).

**ht-port branch status**: HAS the structure for mech 2 (DFS + dep_set backjump
`!dep_contains(cd,level)` early-return, CDCL learning, anywhere blocking, delta
prop) but is 1000x less effective; has NO mech 1 (re-runs consistent() per query,
no possible-subsumer pruning). Anywhere-blocking uses full-label `label_eq` (far
stricter than HermiT core blocking) → leading suspect for under-blocking.

**IMPLEMENTED + VALIDATED (ht-port commit 0cc8745, 2026-06-16).** Profiling
ht-port (KM_HT_STATS) localized the real gap = MODEL FOLDING, not search: the
anywhere-blocking cache was keyed on each node's CREATION-time (incomplete)
label so it NEVER fired → 9024 built 7559 nodes (HermiT folds to 27) → disjunction
explosion (pending 55k) → search drowns. Also the disjunction scan was O(pending)
per step. Fix: real anywhere-blocking forward pass (compute_blocked, m<n, blocked
node never blocks) + default-on incremental scan (KM_HT_NO_WATCH/KM_HT_ANCESTOR_ONLY
revert). KM_HT_BLOCK mode: 1=subset (default, folds most), 0=core (positive-eq),
2=full-eq. RESULT (IBEX, gold=Konclude): **12141 8.4s GOLD-CLEAN, 9024 111s
GOLD-CLEAN (7559→101 nodes), 5303 0.93s incomplete-by-1 (0 unsound)**; 39 tests
pass. Blocking trade-off MEASURED: folding power subset>full-eq≈core; only subset
terminates; subset complete for ALC(H) but incomplete w/ transitive roles (5303
drops CarbonHydrogenSubstructure⊑Hydrocarbon). overturns
[[project_km_family_diagnosis]] "blocking-alone won't transfer" (that was legacy
tableau.rs; on ht-port blocking IS the lever).

**FULL-CORPUS GOLD SWEEP (job 47563108, c7d1af7/11c3a08)**: routed every ALC(H)
non-transitive ont to KM_HT vs Konclude gold. RAW sweep showed "19 unsound" =
COMPARISON ARTIFACT (KM emits `__<sourcefile>` localname suffix + X⊑owl:Thing +
X⊑X that gold filters). CORRECTED (strip __, drop Thing/Nothing supers + self):
over 272 routed onts → **250 gold-clean, 0 spurious-subsumption unsound, 1 missed
inconsistency (6720: KM consistent, gold inconsistent — real bug), 9 incomplete
(8 minor, 7216 near-total), 12 timeout**. So KM_HT is SOUND on subsumptions
corpus-wide (blocking fix validated at scale) but NOT deployable: 6720 + 9
incomplete (subset blocking sound-not-complete, even on non-transitive onts), and
ALL 26 production timeouts are transitive → skip-routed → 0 recovered. KM_HT
stays GATED OFF. Two side experiments (both committed c7d1af7, gated): Mechanism 1
told-subsumers (KM_HT_NO_TOLD) = gold-clean but 0 speedup on family (cost = hard
searches not test count); transitivity encoding in cb_to_ht (KM_HT_NO_TRANS_ENC)
= inert on 5303 bc transitivity DROPPED UPSTREAM (5303 TInput: 0 composition
clauses, fenced=[]; fix is in ofn/ofn_rbox). Blocking battery: only subset
terminates, core+eq time out even on tiny 5303.

**REMAINING**: (1) transitivity-complete folding for 5303-class (pairwise/core-on-
stable-label, or transitivity encoding so subset stays complete); (2) port
QuasiOrderClassification (mech 1) for wide onts 4604/15491; (3) wire routing
(ALC(H) NON-transitive disjunction onts → KM_HT in owl_classify) + FULL gold
sweep before default-on. ht-port binaries/tins cached at /ibex/scratch/hohndor/
km-htport (engine builds ~22s; tin_5303/12141/9024.json; emit2.py bypasses
tab_emit.py's stale dropped/fenced-as-int diagnostic).

**Infra notes**: ws (10.73.11.158) DOWN 2026-06-16 (ssh timeout) → built ht-port
on IBEX at /ibex/scratch/hohndor/km-htport instead. corpus .owl files ARE OWL
functional syntax (ofn parses directly). tab_emit.py = ofn→TInput. Each IBEX ssh
may hit a different login node w/ separate /tmp → scp to /ibex/scratch, not /tmp.
HermiT jar + CountingMonitor at /ibex/scratch/hohndor/km/bench/hermit_cp/.
