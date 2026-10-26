---
name: project_km_ht_learning_dead
description: 2026-06-19 DECISIVE — HT conflict learning is NOT the lever for 5303 (3-arm IBEX diagnostic); the real pathology is depth-16k disjunction branching that no-goods can't prune.
metadata:
  node_type: memory
  type: project
  originSessionId: 17d1eba9-eaa6-4268-97ae-40756c219352
---

2026-06-19: User chose direction "Effective conflict learning (HT)" to crack the
disjunction family. EMPIRICALLY FALSIFIED for 5303 (the only HT-fragment family
member) via a clean 3-arm IBEX diagnostic (build 47654081, job 47654302,
`KM_HT_FORCE=1 KM_HT_MODE=race KM_HT_STATS=1`, 120s each).

Added an UNSOUND diagnostic flag **KM_HT_LEARN_NOSTALE** (field `learn_nostale`
in `Ht`; in `maintain_learned` it replaces the `node_valid(ln,lu)` staleness
guard with `ln < concepts.len()`, so a learned no-good refires regardless of
whether the node id was recreated as a different individual). This is the
THEORETICAL UPPER BOUND on what any conflict-learning scheme can achieve.

3-arm result at ~110-116s timeout checkpoint on ore_ont_5303:
- ARM A (KM_HT_LEARN=1, current SOUND stale-keyed): steps 205795 / backtracks
  118886 / conflicts 56547 / depth 15773 / nodes 1015.
- ARM C (no learning): steps 205795 / backtracks 118886 / conflicts 56547 / depth
  15773 / nodes 1015. **BYTE-IDENTICAL to ARM A** (mtot differs by 10 = noise).
- ARM B (KM_HT_LEARN=1 + NOSTALE, unsound upper bound): backtracks ~105k (-7%),
  but depth 19106 (DEEPER) and nodes 1251 (MORE). Does NOT converge.

**VERDICT:**
1. Current sound stale-keyed learning is **100% INERT** — search identical to
   no-learning. Every no-good is discarded stale before it can refire (no-goods
   key on (node,uid,lit); each branch recreates nodes with fresh uids).
2. The UNSOUND upper bound (max possible refiring) cuts backtracks only ~7% and
   goes deeper, never converging. So building a SOUND stable-keyed learner is not
   worth a major soundness-delicate rearchitecture — its ceiling is ~7%.
3. Root cause confirmed: cross-branch conflicts DON'T transfer (structurally-fresh
   individuals per branch); node-local conflicts already caught by clash detection.
   Matches [[project_km_hermit_konclude_port]] prediction.

**The REAL pathology (the smoking gun): DECISION DEPTH 15773-19106.** The DFS
stacks 15-19 THOUSAND disjunction branch levels with only ~1000-1250 nodes
(blocking IS folding the MODEL fine — 89% blocked, ~110 unblocked). So blocking
works; the problem is purely the live ∀+⊔ disjunction branch tree exploding in
DEPTH. backtracks 118k vs HermiT ~236 = ~500x. This is the CLAUDE.md root cause
"incomparable 2-3-literal disjunctive facts subsumption cannot prune"; HermiT
cracks it via absorption making ∀+⊔ deterministic (KM M1 absorption found 0 to
absorb — positive disjuncts) + dependency-directed backjumping.

**NEXT LEVERS (sound, no Lean, existing flags — no rebuild needed):** measure on
5303 force+race: (a) backjump RATE (memory: only ~1/3 of backtracks are backjumps
⇒ dep-set imprecision; smaller clash deps → collapse deep chains); (b)
KM_HT_BLOCKSKIP (skip branching the 89% blocked nodes' ⊤-disjunctions);
(c) KM_HT_EAGER (fire globals only on unblocked nodes); (d) KM_HT_RESTART
(restarts=0 now; Luby restart to escape deep chains); (e) KM_HT_PICK=1/2 (branch
order). (f) ALT path: route 5303 to the cache-tableau (KM_TAB_CACHE, tableau.rs,
NOT Ht) which already recovers siblings 2313/2066/5089 and ran 5303 3x faster
[[project_km_disjunction_split]] — needs a convergence heuristic.

Baseline stays 564-565 clean / 0 unsound / 0 incomplete (learn_nostale is gated,
default off, and is a DIAGNOSTIC ONLY — do NOT ship; it's unsound).

**FOLLOW-UP flag matrix on 5303 (force+race, jobs 47654446/47654652/47654738-743):**
- **KM_HT_EAGER is the strongest lever found**: fires ⊤-disjunctions ONLY on
  unblocked nodes (blocker covers blocked ones). Cut depth 12954→~1716 and reached
  **qi=81/94 concepts** in 90s (baseline finished 0 concepts — stuck on concept 1).
  BUT at full 240s it STILL times out (subs=0): the hard tail of ~13 concepts eats
  the budget. Per-concept cost is otherwise fine (e.g. concept 290: 2718 backtracks,
  1.7s, sat).
- **All other flags fail**: BLOCKSKIP collapses depth 12954→323 / nodes 837→229 but
  explodes backtracks to 374k of shallow thrash (no concept completes); RESTART
  (135+ restarts) thrashes; PICK1/PICK2 ≈ baseline (depth ~14k). EAGER + {NEGTRIED,
  PICK1, PICK2, PICK2+NEGTRIED, RESTART, NEGTRIED+RESTART} — ALL 6 timeout at 235s.
- **VERDICT: 5303's hard-tail concepts are at a genuine search wall.** No existing
  flag or combination cracks them. EAGER is foundational (gets 81/94) but the tail
  needs NEW machinery (HermiT-grade absorption — KM M1 found 0 to absorb since
  disjuncts are positive — or a major search-convergence rearchitecture). Both
  uncertain, for ONE ontology.
- NB: cb_to_ht DOES have a Horrocks-Sattler transitivity ∀-propagation encoding
  (cb_to_ht.rs 566-609, gate KM_HT_NO_TRANS_ENC) — the plan's "0 composition
  clauses" claim is likely stale; couldn't confirm whether 5303-under-HT is
  incomplete-by-1 because no arm completed.
- NEXT real lever for the WHOLE HT path (sound, no Lean): the O(n²) blocking
  recompute. process_obligations (hypertableau.rs 2754) recomputes compute_blocked()
  (full O(n²) subset scan) EVERY dfs step; on 5303 ~200k steps × ~10^6 = dominant
  per-step cost. Cache/incrementalize → constant-factor HT speedup corpus-wide
  (the "improve averages" half of the mandate), though it alone won't make a
  non-converging search terminate.

**2026-06-19 USER CHOSE "Deep 5303 convergence work".** DECISIVE label-probe
(added KM_HT_LABELPROBE to the Ht heartbeat: distinct positive-label count +
dup_max among live nodes; job 47655436, EAGER force+race):
- **Massive label redundancy in the Ht path**: distinct_lbl is ~15-20% of nodes,
  dup_max (most-duplicated label's copy count) reaches **38-76** (e.g. nodes=1139
  distinct_lbl=203 dup_max=74; nodes=825 distinct_lbl=172 dup_max=69). The Ht DFS
  re-decides each duplicate label's subtree from scratch — it has NO per-label
  SAT caching. ⇒ **MODEL/LABEL SATISFIABILITY CACHING is the lever** (HermiT/
  Konclude's edge; the KM_TAB_CACHE path already has it, the Ht path does not).
- EAGER per-concept shape on 5303: most of the 94 concepts are CHEAP (300-800ms,
  ~800 backtracks) but ~13 TAIL concepts cost ~14s each (concept 195:
  14187ms/12234 bt; concept 233: 13671ms/11882 bt) — these dominate, and they are
  where label redundancy is highest. Backjumps ≈ 29% of backtracks (coarse deps).
- DECISION PENDING on cache+CONV(KM_TAB_CACHE+KM_TAB_CONV: VSIDS+phase+dynrestart+
  no-good-reduction, tableau.rs CacheRun 3237) result on 5303 (job 47655481): if
  it completes/near-completes ⇒ improve THAT path's convergence + route 5303 to it
  (note: orchestrator's cache racer race.rs:100 sets only KM_TAB_CACHE+ORD, NOT
  CONV — a gap). If not ⇒ port per-label SAT caching into the Ht+EAGER path.
  cb_to_ht HAS Horrocks-Sattler trans ∀-prop (cb_to_ht.rs 566), so 5303-under-tab
  may be gold-clean. Cache path is sound for ALCH no-inverse/number/nominals
  (5303's fragment) via greatest-fixpoint subset blocking (Dickson).

**2026-06-19 BREAKTHROUGH — the cache path is the right foundation for 5303.**
Added KM_DUMP_TIN=<path> to spawn_ht (race.rs, before the routability guard):
dumps the cb_to_ht TInput JSON + prints guard fields, so the tableau worker
(`km tableau < tin.json`) can be run STANDALONE with any flags + visible stderr.
- **5303 TInput: clauses=937 dropped=0 fenced=0 nominals=0 inverse=false
  number=false queries=94.** So 5303 is FULLY in the cache-tableau fragment
  (dropped=0!) and PASSES spawn_tableau's guards — the plan's "withheld by
  transitive-role guard / 0 composition clauses" claim is STALE. It IS routable.
- **cache+CONV standalone on 5303 (job 47655574, KM_TAB_CACHE+CONV+STATS):** times
  out BUT with the right structure — depth bounded ~308/325 (vs Ht 16k!),
  **no-good learning FIRES: nghit=135598** (label keys are stable, so learning
  works here — exactly what Ht lacks), restarts=425. PROBLEM: seeds=82808 ≫
  cache=14521 and reduces=0: the 425 Luby/dyn restarts DROP conditional-SAT cache
  entries each time (sat_seed line 4076), forcing re-derivation → 6.1M branches,
  slow monotone progress, no finish in budget.
- HYPOTHESIS being tested (matrix jobs 47655674-679 on the dumped TInput, fast/no
  rebuild): KM_TAB_TYPECACHE (caches CLOSED-type verdict as UNCONDITIONAL — survives
  restarts, collapses the 82k re-explored seeds) and/or KM_TAB_SUBCACHE
  (subsumption-SAT downward closure), both default-OFF, +/- KM_TAB_DYNRESTART=0.
  If a combo COMPLETES 5303 → wire it into the cache racer (race.rs:100 currently
  sets only KM_TAB_CACHE+ORD — NO CONV/typecache/subcache) + route 5303 there.
- Reusable diagnostic: /ibex/scratch/hohndor/km/{tin5303.json, tab_arm.sh}. Run any
  flag combo via `km tableau < tin5303.json` (235s) — no rebuild, no orchestrator.

**2026-06-19 DECISIVE (cache-path mechanism matrix, jobs 47655674-679 on tin5303):**
ALL of {CONV, +TYPECACHE, +SUBCACHE, +both, +both−dynrestart, typecache−CONV}
TIME OUT — AND none even prints `consistent([])=` or `classify 0/94`. **The cache
path is stuck on the GLOBAL CONSISTENCY check (sat_seed([])) — it never reaches the
94 per-concept queries.** prog: node_horn=628 node_disj=115 node_exists=59 uni=87
clash=35. The 65k-109k distinct seeds + 6M branches are ALL spent proving ⊤
consistent. Seed space never saturates (TYPESUB_NORST no-restart still 65k seeds;
TYPE_NOCONV depth=66 nghit=863k but 109k seeds). 
**REFRAME:** 5303's hardness = building ONE consistency model, not the queries.
- **Ht+EAGER is the BETTER foundation**: its ∃-blocking folds the model (~1000
  nodes, 89% blocked) so it FINDS the consistency model and completes 81/94 queries.
  The cache path's per-label decomposition fragments the SAME model into 65k+
  (label,imposed) seeds (same base label × many parent-imposed ∀-clause variants)
  and can't even finish consistency. Model-sharing (Ht) beats label-caching here.
- **Caching + learning + restarts is EMPIRICALLY INSUFFICIENT for 5303.** The cache
  path has WORKING learning (135k-863k nghit, stable keys) + bounded depth (66-308)
  + 425 restarts and STILL can't finish. So the user-chosen "deep convergence work"
  premise (a convergence heuristic will close it) is FALSIFIED — the whole
  convergence toolbox doesn't tame 5303's ~65k-label search. What's missing is
  Konclude-grade saturation/DETERMINISM that avoids branching the positive ⊤-⊔
  disjunctions (Q6∨DNA…) — but M1 absorption finds 0 to absorb (positive). This is
  a major reasoner advance, uncertain, matching the years-long history. CHECKPOINT
  raised to user: invest in that major build, OR ship the EAGER HT improvement
  (advances HT path broadly, doesn't complete 5303) + pivot, OR accept the wall.

**2026-06-19 USER CHOSE "Build Konclude-grade determinism". Diagnosis refined to
the ACTUAL buildable lever:**
- QO tally on 5303 CONFIRMED: queries=94 dead=3 **suff=0** insuff=91 (open med=17
  max=18). Lazy-saturation determinism gives ZERO shortcut — every concept needs
  branching. Structure: 868 clauses, 33 disj heads = **17 GLOBAL ⊤-disjunctions**
  (inherent ⊤⊑A∨B, nothing to absorb — positive) + 16 triggered; 26 binary + 7
  ternary. So lazy-saturation AND absorption forms of "determinism" are N/A to 5303.
- Added KM_TAB_ASSUME_CONSISTENT (tableau.rs, skip consistent([])). RESULT: cache
  path times out on the FIRST per-concept witness (classify 0/94 seeds=0). So the
  cache CDCL can't build EVEN ONE 5303 model — per-label fragmentation hits any
  seed reaching the ∃-structure. HYBRID (cache-CDCL per-concept) is DEAD.
- **The two engines are COMPLEMENTARY**: Ht builds the model (sharing+blocking →
  consistency + 81/94 witnesses) but learning is broken (node-uid keys, 7% ceiling);
  cache path has WORKING learning (135k hits, LABEL-keyed) but can't build the model.
- **THE BUILD (non-falsified, in progress): sound LABEL-keyed UNSAT cache in Ht's
  per-test DFS** (KM_HT_LBLCACHE). The learning-dead result only killed NODE-UID
  keying; LABEL keying (the cache path's proven-effective mechanism) is UNTESTED in
  Ht. A concept-label proven unconditionally UNSAT prunes any node whose label is a
  SUPERSET (sound for ALCH no-inverse — node sat depends only on label; same
  justification as Ht subset blocking + cache path). Attacks the dup_max=76 repeated-
  label redundancy in Ht's hard witnesses. Soundness condition = clash dep must be
  "unconditional" (not caused by outer branch choices) — mirror cache path `tainted`.

**2026-06-19 BUILDS (all gated OFF, 111 tests pass, no regression risk):**
- EAGER STANDALONE = **qi=93/94** on 5303 (full-priority km tableau, 235s; the 81/94
  was niced pipeline). ONE concept short. ~13 hard witnesses @ ~8.8s/16460 bt/966 nodes.
- **KM_HT_SATCACHE**: persistent SAT core-sig pool, blocks nodes w/ prior-SAT sig.
  Sound. RESULT: ZERO effect (model already folded to 966; bottleneck is BRANCHING).
- **KM_HT_WITREUSE**: pseudo-model witness reuse (record SAT models' node labels; a
  query concept present in a prior model is witnessed SAT, label ⊇ its subsumers).
  Sound+complete. RESULT: reused=41 built=53 — FIRES but reuses the CHEAP concepts;
  the ~13 expensive witnesses aren't in earlier models, still rebuilt. Still 93/94.
- **BOTTLENECK = per-witness disjunction search** (16460 bt to FIND each hard model).
  SATCACHE (size) + WITREUSE (dedup) both miss it; learning 7%-capped.
- IN PROGRESS **KM_HT_PHASE**: label-keyed phase saving — warm-start witness disjunct
  choices from the consistency model, persisted across rebuilds. Sound (reorders a
  complete search). The one untried lever AT the bottleneck. If hard-concept backtracks
  drop → 5303 likely solvable; if not → per-witness search irreducible in KM (HermiT
  does it in 236 bt via propagation KM lacks).

**2026-06-19 USER CHOSE "Commit to precise dep-backtracking". KM_HT_DEPSTATS probe
(conflict_out samples) gives the DECISIVE profile on 5303's hard witness:**
**avg_card=5.5 (conflicts are TINY, 2-7 levels) at avg_depth=1243.9, backjump_gap=0
for ALL 60 samples (dep_max always == cur_depth).** This is the TEXTBOOK CDCL
profile: search descends ~1244 decisions deep but each clash is caused by only ~6
of them; it re-derives the SAME tiny conflicts 16460× because learning is broken.
Standard conflict learning records each 6-literal no-good once → never repeats →
this is exactly why HermiT does 236 bt. So the rework IS correctly targeted and the
data says it pays off big. add_concept ALREADY minimizes dep by dep_max (line 362);
raise_clash picks min dep_max. So deps are reasonably tight; the gap is LEARNING the
tiny recurring conflicts with a STABLE key (node-uid keying made them never refire;
NOSTALE gave only 7% because node-IDS of the culprit nodes also differ across
recurrences). NEXT: pin down WHERE the ~6 culprit decision nodes are (low/stable →
node-keyed learning w/ fixed staleness; scattered/recreated → label-keyed needed) —
extended KM_HT_DEPSTATS dumps levels_nodes (needs KM_HT_LEARN=1 to populate
decisions). Then build working conflict learning for these tiny conflicts.

**2026-06-19/20 node-location probe (KM_HT_DEPSTATS + LEARN, dumps levels_nodes):**
the ~6 culprit decisions per conflict MIX recreated deep node-ids (~500-800) with a
few low/stable anchors (0,1,2,3). The deep ids are recreated as different
individuals → node-uid/NOSTALE keying can't recur (explains the 7%). Conflicts span
a parent role-chain (cross-node). ⇒ no-goods MUST be keyed on node LABEL-SIGNATURE.

**BUILD (committed, IMPLEMENTED) — KM_HT_LBLCACHE: signature-keyed conflict learning
in Ht (hypertableau.rs):**
- core_sig(n) = FNV hash of n's sorted POSITIVE concepts (structurally-identical
  nodes share a sig across recreations).
- record_decision now also stores dec_sig[level]=core_sig(n) and inserts
  (sig,lit)->level into cur_choices (the active assignment). unrecord_choice on every
  backtrack path.
- On clash, lng_learn builds a no-good = set of (dec_sig[l], decisions[l].lit) over
  the clash dep's levels; watched by each (sig,lit) in lng_watch; capped 2..24 lits,
  300k clauses.
- In the branch loop, after asserting a disjunct, lng_fired(sig,lit) checks if the
  choice completes a learned no-good (all its (sig,lit) in cur_choices) → returns
  Out::Conflict(dep=levels of matched choices) WITHOUT recursing (prunes the dead
  subtree). Integrated with backjump + negtried.
- lng persists across restarts within a query, cleared per query; cur_choices/dec_*
  reset per Ext rebuild. Heartbeat prints lng=/lng_fires=.
- **SOUNDNESS RISK**: the key ignores the ROLE STRUCTURE connecting cross-node
  conflict nodes (only per-node sigs). Could fire spuriously → wrongly prune → unsound
  (extra subsumptions). MUST validate gold (unsound=0). Test job 47668472 on 5303:
  standalone backtracks+lng_fires AND full classify canon_cmp vs gold. If sound+fewer
  backtracks → win; if unsound → need role-path in the key (structural keying).

**2026-06-20 LBLCACHE RESULT (job 47668472): FALSIFIED.** Build green, 111 tests
pass, mechanism FIRES correctly (lng=734-1336 learned, lng_fires=30-158/window) — but
**hit rate ~0.08%** (lng_fires≈150 vs conflicts≈200k). Sig-keyed no-goods almost never
recur; still times out (backtracks→444k). So conflict learning in ALL forms is now
DEFINITIVELY dead for 5303: node-uid 7%, NOSTALE 7%, label-sig 0.08%. The tiny
conflicts (card 5.5) are structurally near-UNIQUE → nothing recurring to learn.
**ROOT CAUSE redirected to MODEL FOLDING, not learning/backtracking:** HermiT does
5303's hard test in ~150 bt not by learning but by GENERATING few conflicts — its
model folds to ~3 nodes vs KM's ~966 (89% blocked but ~106 UNBLOCKED, each branching
~17 disj). 150-vs-16460 conflicts is downstream of 3-vs-966 nodes. But standard
blocking modes are exhausted: mode0 core=89%/966, mode3 pairwise folds WORSE (2173),
mode2 full-eq folds too little. So the model-folding lever has no obvious untested
mode either. 5303 is a precisely-characterized wall: KM cannot match HermiT's model
folding on this ont with the available blocking, and learning can't compensate
(conflicts don't recur). Mechanisms built this session (all SOUND, gated OFF, 111
tests): KM_HT_EAGER (the only effective one, 93/94 standalone), KM_HT_WITREUSE
(pseudo-model reuse, 41/94), KM_HT_SATCACHE, KM_HT_PHASE, KM_HT_LBLCACHE; diagnostics
KM_HT_DEPSTATS/LABELPROBE/KM_DUMP_TIN/KM_TAB_ASSUME_CONSISTENT. Baseline 564-565
clean / 0 unsound / 0 incomplete untouched.

**2026-06-20 USER CHOSE "Attack model folding". Model-structure probe
(KM_HT_DUMPLABELS on hard concept): the ~85 unblocked node types share an IDENTICAL
18-concept CORE {131,142,172,191,199,210,213,227,230,242,251,257,261,275,279,286,
303,307} and differ only by ONE low "tag" concept (17/43/45/66/11/21/29/39/53/64 =
exclusive-disjunct Qi picks). They're pairwise INCOMPARABLE (31 comparable / 1739
incomparable) → subset blocking correctly can't fold them. node sat is
label-determined (ALC(H) no-inverse).**

**KM_HT_SATFOLD (model folding by SAT-superset completion) — BREAKTHROUGH:**
record full labels of completed clash-free model nodes; before branching, if a node's
label ⊆ a memoed label L, COMPLETE it to L (assert missing concepts) so its
disjunctions are satisfied with NO branching; sound for ALC(H) no-inverse (completion
is downward-independent, can't propagate a clash up, can't turn SAT→UNSAT). **v1
(cache ALL tests' nodes): 5303 standalone RC=0 — FIRST mechanism EVER to COMPLETE
5303 (satfold hits=37239)!** But full classify UNSOUND (km_n=239 gold 238, unsound=10
incomplete=9) — bug: cached query-specific ¬B negatives from {A,¬B} tests + blocked
(non-saturated) labels, reused across tests, inject unentailed concepts → spurious
clashes. **FIX (testing, job 47669096): cache ONLY the global consistency model
(seed []) UNBLOCKED saturated nodes — query-independent genuine individuals.** If
gold-clean → 5303 SOLVED via model folding (the right attack). 111 tests pass both
versions. sat_labels persists across queries (populated once from consistency).

**SATFOLD iterations (all 111 tests pass; baseline untouched):**
- v1 (cache ALL tests' nodes, full pos+neg labels, full completion): 5303 standalone
  COMPLETES (RC=0, FIRST EVER) but full classify unsound=10 incomplete=9. Bug: query
  ¬B negatives + blocked non-saturated labels reused cross-test.
- v1b (cache only consistency seed-[] unblocked): labels=1 hits=0 (seed-[] model too
  sparse) → no folding → timeout. Over-corrected.
- v2 (cache POSITIVE cores of unblocked nodes any test; complete missing positives
  only IF the core respects n's negatives — disjointness check): full classify
  COMPLETES (RC=0) but unsound=22 incomplete=9 (WORSE), standalone times out (concept
  31 = 217s pathological). So positive-core + disjointness is STILL unsound.
- **VERDICT: model folding by SAT-superset completion is the RIGHT ATTACK (it makes
  5303 terminate — first ever) but the completion is UNSOUND (10-22 wrong subs) and
  the fix is subtle (v1→v2 got worse). Needs real debugging: dump a specific wrong
  subsumption (a km-only pair) on 5303 and trace which fold injected the bad fact —
  not more guessing.** Hypotheses for the residual unsoundness: (a) a cached core,
  though clash-free in its origin model, is NOT a standalone-satisfiable type when
  forced at a node reached via a different ∀-context (some negative in the origin was
  load-bearing and isn't reproduced); (b) completion satisfies a disjunction with a
  choice that the node's context actually forbids via a clause not captured by the
  pos-core subset check. Code: hypertableau.rs try_satfold + sat_labels population in
  consistent(); KM_HT_SATFOLD, heartbeat prints satfold labels=/hits=.

**ROOT-CAUSE of SATFOLD unsoundness FOUND (satfold_diff.py on sf_5303.subs):** the 22
unsound pairs are all WRONG EXCLUSIVE-DISJUNCT picks: Carbohydrate/Glucose/Hexose/
Ribose/Pentose/Mono-/Oligo-/Polysaccharide ⊑ Hydrocarbon (carbs aren't hydrocarbons);
AminoAcidSequence/BioMolecularSequence ⊑ NucleicAcid — but the 9 INCOMPLETE pairs show
the truth is ⊑ Peptide. NucleicAcid vs Peptide (and Hydrocarbon vs Carbohydrate) are
EXCLUSIVE disjuncts (⊤⊑A∨B with A+B→⊥). Folding satisfies the disjunction by
committing a node to a cached core that picked the WRONG disjunct: locally clash-free,
but the concept's own DISJUNCTIVE reasoning (AminoAcidSequence⊑Peptide, derived via
branching, not Horn) would force the other. At fold time the node hasn't derived
Peptide yet (disjunctive, not propagated) so nothing forbids NucleicAcid → subset+
disjointness check passes → premature wrong commit → clash-free WRONG model → wrong
subsumers. **CORE PROBLEM: sound folding must distinguish FORCED completions from
CHOICE completions; the subset check can't, because a partial core matches cached
cores of DIFFERENT exclusive types. Folding a node to a superset core is NOT sound
when the superset resolves an exclusive disjunction the node would resolve the other
way.** This is the genuine hard problem. The BREAKTHROUGH stands: SATFOLD makes 5303
TERMINATE (first ever) — model folding is the right attack — but sound completion is
unsolved. Fix ideas (untested): (a) only fold to a core whose disjunct choices are
all ALSO Horn-forced at n (defeats purpose); (b) fold as a CHOICE with a dep + verify
by continuing to derive the node's disjunctive consequences (but the wrong pick is
clash-free, so won't be caught); (c) restrict folding to nodes with NO open
exclusive-disjunction membership ambiguity. Genuinely hard.
