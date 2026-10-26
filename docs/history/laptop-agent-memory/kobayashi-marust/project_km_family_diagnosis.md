---
name: project_km_family_diagnosis
description: "2026-06-16 exhaustive diagnosis of the live-∀+⊔ disjunction family + EL-routable onts — every cheap/medium lever closed, only a HermiT-grade port remains"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

## 2026-06-16 UPDATE — root cause of family-via-hypertableau found (overturns "needs CDCL learning")

The KM_HT hypertableau port (branch `ht-port`, commit e004246 + INCR7) does NOT
time out on the family by search. Traced on IBEX (jobs 47554xxx, showboat-style):
- The hypertableau reaches a COMPLETE model (`scan-sat`) for 5303 global
  consistency in **20 ms** (615 ticks, matcher mmax=1 — trivial). Search is fine.
- It then sets `unsupported=true`, returns None, and `run_json` **silently falls
  through to the LEGACY tableau** — which is the thing that times out (the 12s).
- WHY unsupported: `apply_head` bails on **head Role/Eq atoms** (hypertableau.rs
  ~L566). Fragment census (KM_HT_TRACE `TR CENSUS`):
    5303  head_role=6  head_eq=0  disj_with_exists=0  (clauses=878)
    9024  head_role=29 head_eq=0  disj_with_exists=0  (clauses=2714)
    12141 head_role=29 head_eq=0  disj_with_exists=0  (clauses=2722)
  i.e. the ONLY blocker is a handful of **role-hierarchy / role-chain head atoms**
  (`r(x,y)→s(x,y)`, the H in ALC(H)). No equality, no ∃-in-disjunction.

INCR 7 (KM_HT_ORD/PICK/RESTART, activity+Luby, commit e004246) was validated
answer-invariant (35 tests) but recovered 0 on the family — because the engine
bailed BEFORE search. So ordering/learning was never the lever.

DONE (commit d531805): head role-edge support added (apply_head forces head Role
atoms via add_edge + Event::Edge; Eq heads + role/∃-in-disjunction still bail).
Recovers ore_ont_5303 GLOBAL consistency timeout→0.06s. 37→38 tests pass.

DONE (commit d5fdde3): model-based classification — one model per concept, prune
candidate subsumers to its root label (sound+complete, identical output to naive
n², KM_HT_NAIVE escape hatch).

BUT family still not solved — deeper bottleneck found (IBEX 47555719/47557495):
- 5303 PER-CONCEPT consistency check is slow: first {pos(concept1)} check alone =
  44s building a 198-node model (~220ms/node). Global 0.06s was the trivial empty
  model; seeding a concept forces ∃/role structure.
- 9024 worse: nodes=4922, depth=4600, pending=84846, oblig=7709 and GROWING at
  30s (model-construction explosion; blocking not bounding it).
ROOT CAUSE of the slowness: `next_action_from_pending` re-scans ALL pending ground
disjunctions O(pending) on EVERY dfs step. INCR5/6 made PROPAGATION delta-driven
but left the DISJUNCTION SCAN non-incremental → quadratic-plus per model.

DONE (commit fc24ae7): incremental "watch" disjunction scan (KM_HT_WATCH, gated
OFF). Correct (39 tests, controls byte-identical: 2313=13967/2066=980/5089=482
subs in both modes) but NOT a perf win — slightly SLOWER on 2313 (5.2 vs 2.8s),
family still times out. Eager re-dirty (every assert+backtrack) ≠ true 2WL.

FINAL DIAGNOSIS (IBEX 47558627 profile + 47558644 sweep) — the family bottleneck
is now PINNED and it is the **per-concept classification consistency checks**:
- 5303 GLOBAL consistency: 0.06s (trivial, ~1-198 nodes). Not the problem.
- 5303 PER-CONCEPT {pos(a)} check: SEARCH-BOUND. One check = 196,547 backtracks /
  28,980 conflicts / depth thrashing 266↔3870 in 40s, nodes BOUNDED ~200 (so NOT
  node-explosion, NOT disjunction-scan throughput — watch didn't help, ordering
  didn't help). It is classic no-learning DPLL thrashing (backtracks >> conflicts,
  same region re-explored).
- INCR7 search discipline (ORD/PICK/RESTART, 6 configs incl Luby restart) on 5303
  FULL classify: ALL timeout@150s. Ordering/restart do NOT dent it. PROVEN.
- 9024 per-concept is worse (model explosion too: 4922 nodes).

CDCL LEARNING NOW IMPLEMENTED + TESTED (commit 400ea8e, KM_HT_LEARN) AND PROVEN
NOT TO HELP. Decision-clause learning, 2WL, node-uid validity guards; 39 tests
pass, controls identical+same-speed. 5303 full classify STILL times out@150s under
learn / learn+ord2 / learn+restart. ROOT CAUSE (proven): 5303's per-concept search
branches across TRANSIENT successor nodes (depth ~3870 over ~200 created/destroyed
nodes), so learned no-goods referencing them go dormant on backtrack (uid guard
correctly voids them); only root/persistent no-goods survive — far too few. This
is the known tableau-CDCL-vs-SAT-CDCL problem; matches legacy KM (learning +
pseudo-model caching, still fails 5303).

VERDICT: every standard search lever is now CLOSED WITH PROOF — ordering, branch
pick, Luby restart (INCR7), incremental scan (watch), and CDCL learning. None
close the family. Residual needs the FULL HermiT/Konclude stack
(label/concept-keyed core caching transferable across nodes + model merging +
told-subsumers + strong absorption) — months, uncertain ORE payoff, and NOT in
production path (family routed to CB engine). Pragmatic call: bank ht-port work,
pivot to higher-ROI ORE targets (throughput/giants task #52, correctness tail).

BANKED WINS this session (branch ht-port, all tested, NOT yet in production path):
role-edge support (ALC-H fragment, 5303 global 0.06s), model-based classification,
watch infra, full instrumentation. NONE change ORE numbers yet (family is routed
to the CB engine in production, not the hypertableau; HT classify still times out).
Decision point for user: commit to CDCL learning (uncertain) vs bank + stop.

----

2026-06-16 (IBEX, target-check build = pushed 278cbba). Tried to close the
disjunction family (5303/1603/9024/12141/10702) + the 6 "EL-routable" onts
(1603/6934/7246/7581/12653/15803, where KM fails but ELK==gold). EVERY cheap and
medium lever is now CLOSED, with proof — do not retry these:

1. **Caching is disproven for the family.** Flag sweep (job 47551128): existing
   gated levers KM_TAB_LAZY / SEMBR / SUBCACHE / TYPECACHE and all combos ALL
   time out at 120s on the 5 family onts (control 2313 stays SOLVED 7.3s,
   unchanged). The superset-of-UNSAT cache I was going to build is PROVABLY
   subsumed by KM's existing no-good learning (a no-good is a minimal subset of
   an unsat label; full-label superset caching is strictly weaker), and no-goods
   already fire only ~1% on 5303. So caching won't help. KM_TAB_MIN confirmed
   inert (gated, output-identical). See [[project_km_disjunction_split]].

2. **EL routing is unsound here.** elc EXITs 3 on all 6 even with KM_ELC_CERT=1
   (job 47551340). With KM_ELC_DEBUG: the cert COMPILES the residuals then FAILS
   the canonical-model check ("fail at residual clause N") — the ∀/disjunction
   residuals genuinely do NOT hold in the EL canonical model, so the simple
   certificate (I ⊨ all residuals ⇒ EL answer exact) correctly cannot apply.
   ELK=MATCH is an UNSOUND coincidence (ELK drops out-of-EL-profile axioms and
   happens to land on gold); it is NOT a sound shortcut. 7246/7581 are ∀-Horn
   (not EL — EL has no ∀). See [[project_km_el_certificate]].

3. **Anywhere blocking alone won't transfer.** Read HermiT AnywhereBlocking.java
   (/tmp/hermit-src): it's a hash-indexed BlockersCache keyed by node blocking
   signature, global lookup. But KM's cached path is ALREADY the inverse-free
   global-caching analog; its explosion is the NUMBER OF DISJUNCTION BRANCHES
   (~8600 decisions to build ONE model on 5303), not blocking depth.

2026-06-16 CORRECTION (code-level, supersedes the "weak absorption" framing
below). Traced `A ⊑ ∀R.(C⊔D)` through normalise.rs: KM's frontend ALREADY emits
HermiT-equivalent GUARDED disjunctive DL-clauses (A(x)→Q1; Q1(x)∧R(x,y)→Q2(y);
Q2(y)→C(y)∨D(y)), plus KM_ABSORB = Plaisted-Greenbaum gating. HermiT (phillord
fork, /tmp/hermit-src) has NO separate classical absorption pass either — it
relies on exactly this guarded-clause shape. So "port HermiT absorption" would
re-implement what KM has; the clausifier lever is ALREADY pulled. Absorption and
good tableau search are NOT rival root causes — both are levers on the SAME
quantity (disjunctive branch count). The earlier "it's algorithmic not threads"
judgment was right; "weak absorption" mis-LOCALIZED it to the clausifier. The
untamed branching actually lives in the SEARCH: KM's careful tableau path
backtracks CHRONOLOGICALLY (backjumping only in the non-careful incremental
path), has no disjunction learning in the careful path, and blocks only on
ANCESTORS (HermiT: anywhere blocking via hash-indexed BlockersCache). ~8600
branches for ONE model on 5303 = missing backjumping+learning (search WIDTH),
not missing absorption and not blocking DEPTH. => PORT = HermiT's tableau search,
not its clausifier. User confirmed (AskUserQuestion) "HermiT tableau core".
STARTED on branch ht-port (commit 47243c0, INCR 1): engine/src/hypertableau.rs,
distinct module from tableau.rs, ALC(H) fragment. INCR 1 = DependencySet
(HermiT PermanentDependencySet as descending Rc linked list) + Ext clash/extension
manager (facts tagged with justifying DepSet; clash unions the two justifications
so clash DepSet max = backjump target; trail+mark/backtrack_to). Build+6 tests
green on IBEX 47551571 (23 passed). Plan: INCR 2 hyperresolution matcher +
disjunction branching; INCR 3 anywhere blocking + BlockersCache; INCR 4 main loop
(saturate→expand∃→branch→backjump) + wire run_json under KM_HT=1. Build/test on
IBEX (debug partition, target-check, ht_build.sbatch); laptop is edit-only.
Coverage-only (family times out either way → not in the avg-over-solved metric).

2026-06-16 INCR 1-4 DONE (ht-port commits 47243c0/a098a95/e09b925). Full ALC(H)
hypertableau works + is CORRECT: IBEX 47551790 full classify byte-identical
(MATCH, 0 disagreements) to legacy cache tableau on family controls 2313 (13967
subs, 7.2s=legacy), 2066 (980), 5089 (482, HT 0.0s BEATS legacy 9.1s). 15 unit
tests green incl. backjump-skips-irrelevant-branch, unit-prop, blocking-terminates.
BUT 5303/9024/12141 STILL TIMEOUT. Diagnosis (KM_HT_STATS, 47551904): nodes=1-5
(NOT node/blocking blowup), depth grows ~linearly with steps (NOT search-width
thrash / not a backjumping failure), bottleneck = THROUGHPUT — engine re-saturates
the FULL clause set from scratch at every branching step (0.2-1.0s/step), so a
few-hundred-level disjunction dive costs minutes. Backjumping architecture sound.
=> the family is NOT closed yet; next lever is INCR 5 = HermiT delta-old
incremental matching (process only newly-added facts) + fact indexing + incremental/
told-subsumer classify (also fixes 2066's 32s O(n^2)-rebuild loss). This OVERTURNS
nothing in the corrected diagnosis above — confirms the search algorithm is right,
the matching throughput is the remaining gap. Route KM_HT only for ALC(H); 1603/
10702 are number/nominal (out of fragment, fall back to legacy).

2026-06-16 INCR 5 DONE (commits ffa9a44/86429ff): delta-driven propagation
(trigger indexes + event queue + bidirectional flex matcher + in_edges; unit-prop
via cheap per-step disjunction scan). Correctness PRESERVED (MATCH on controls).
Throughput win: 2066 full classify 32s->1.5s (21x). BUT 5303/9024/12141 STILL
timeout. Fine profile (KM_HT_HB=2000, 47552877): 9024 = MONOTONE deep dive
(depth~steps ~3/sec, nodes<=5, little backtrack) => per-step cost is
scan_disjunctions+expand STILL full-scanning ALL clauses every step (delta only
fixed propagate). 5303 = STUCK at step25/depth18 (distinct pathology, single
non-progressing hot path). LONG-TIMEOUT TEST (47552949): 9024 global consistency
TIMES OUT at 900s (15min) — the dive is ~thousands of levels deep; extrapolating
the rate it'd need ~50min monotone => incremental scan (INCR 6a) gives maybe
10-50x, MARGINAL to bring 9024 under 240s; 5303 stall (INCR 6b) is separate and
likely needs learning/ordering. HONEST STATUS: ported hypertableau is a correct,
real engine (sound+complete on family controls, 21x faster classify) but does NOT
yet close the hardest family members; closing them is further multi-session work
(incremental scan + 5303 isolation + cross-branch nogood learning + disjunct
ordering) with uncertain payoff, and it's COVERAGE-ONLY (no avg-metric gain).
Konclude does 5303 in 0.16s — large algorithmic+constant gap remains.

2026-06-16 INCR 6 DONE (commits cdf5ae8/0a68ba7): scan_disjunctions+expand made
incremental via trail-tracked worklists (PendingDisj/Oblig recorded by apply_head
during propagation; backtrack drops post-mark entries; DFS consumes worklists, no
full clause scan/step). Correct (MATCH on controls), 33 tests. Throughput: 2066
full classify 1.5s->0.5s (64x over original 32s). BUT 5303/9024/12141 STILL
timeout. => family is SEARCH-bound (tree size), not throughput. KEY STOP-SIGNAL:
the legacy KM cache tableau ALREADY has the next levers (conflict/no-good
learning, VSIDS, phase-saving, restarts — see [[project_km_disjunction_split]],
[[project_km_absorption]]) and ALSO times out on 5303/9024/12141 (5303 = 8M
dpll/483 depth, still oscillates). So INCR 7 (porting learning+ordering+restarts
into the hypertableau) has LOW expected payoff for closing these — they're beyond
KM's tableau paradigm regardless of engine. Konclude's 0.16s is a deeper
architectural win (its saturation+caching). 2026-06-16 DATA CORRECTION (side-by-side jsonl cmp_res/ont_{5303,9024,12141},
gold=Konclude, 600s): HermiT SOLVES all three SOUNDLY+FAST — 5303 1.9s/238subs
MATCH, 9024 1.2s/908 MATCH, 12141 0.79s/908 MATCH. Konclude 0.1-0.2s MATCH. KM
timeout (CB engine 45GB on 5303). So "beyond the hypertableau paradigm" was WRONG
— HermiT (a hypertableau) does it in ~2s; the mechanism is gettable, continuing
is justified. CRUCIAL: ELK is DIFF on all three (171/813/813 vs gold 238/908/908)
— ELK drops the disjunctions and is INCOMPLETE by 67-95 subsumptions. So the
disjunctions are NOT inert/EL-reducible (reasoning-by-cases over ∀R.(C⊔D) yields
real named subsumptions); the EL cert REFUSING was CORRECT; "ELK solves => CB can
=> EL-exact" is FALSE here. No CB method is both sound+fast (ELK incomplete, KM-CB
45GB). The two sound+fast solvers (Konclude, HermiT) are MODEL-CONSTRUCTION based.
=> universal property = build ONE model + classify against it, NOT eagerly
enumerate the disjunctive consequence closure. The hypertableau port is the right
vehicle; my port's failure is a SEARCH deficiency (no disjunct ordering, no
cross-branch learning, + a stuck perf pathology where nodes=1 yet it crawls),
NOT a paradigm limit. NEXT: disjunct ordering (HermiT sorts disjuncts by
backtrack count) + isolate the stuck pathology (suspect O(depth^2) pending rescan
or a hot loop) + learning; target HermiT's ~2s. REVISED RECOMMENDATION: continue
(was: stop) — HermiT proves ~2s is reachable in-paradigm.

OLD RECOMMENDATION (SUPERSEDED by the correction above; was based on the wrong
belief that no tableau solves these) (given user's PRIMARY
metric = avg time/space, not passrate): STOP the 5303 coverage chase; the
hypertableau is a real deliverable — correct + fast ALC(H) engine that beats the
legacy cache tableau on some onts (5089 0.0s vs 9.2s). Productive next step =
corpus-wide A/B of KM_HT vs legacy on all ALC(H) onts to validate it as a routed
fast classify path (a genuine AVERAGE-perf contribution), not more family
micro-profiling. Branch ht-port, 7 commits 47243c0..0a68ba7.

ROOT CAUSE (original framing, now refined per the correction above): the family's disjunctions are INERT/absorbable for classification
(ELK ignoring them still gets gold), but KM's absorption (KM_ABSORB frontend +
KM_TAB_LAZY) is too weak to neutralize them, so the search explodes exploring
branches that don't matter. Konclude (0.14–0.31s) and HermiT (0.8–6.5s,
hypertableau = same paradigm) win via STRONG ABSORPTION + model-based
classification (build one small model, read off possible-subsumers, targeted
confirmation), not better caching. HermiT/ELK source cloned to /tmp/hermit-src,
/tmp/elk-src for porting study.

THE ONLY REMAINING PATH is a genuine port of HermiT-grade ABSORPTION
(binary/role/partial absorption to make disjunctions deterministic) and/or its
model-based classification strategy — a MAJOR multi-session effort, and
COVERAGE-ONLY (these time out either way → not in the mean-over-solved that the
user's average-time/space metric uses, see [[project_km_threads_vs_algo]]).
26 KM failures total in side-by-side (584 onts): 541 1603 2669 3215 4604 5303
6934 7246 7499 7581 7914 9024 9540 9635 9663 9724 10621 10702 11460 12141 12653
14817 15491 15516 15672 15803.
