---
name: project_km_5303_perstep_cost
description: "2026-06-20 SOLVED — 5303 completes sound+complete (238/238, CLEAN) via EAGER+NEGTRIED+ORD=2+PHASE in 207s; gap was SEARCH DISCIPLINE (all default-off), not blocking/learning. Parallel classify (KM_HT_PAR) adds margin."
metadata: 
  node_type: memory
  type: project
  originSessionId: 17d1eba9-eaa6-4268-97ae-40756c219352
---

**2026-06-21 SPEED v4 + BUILD-CORE-ONCE KILLED (committed 61cb79f, pushed).**
Two more incr2 refinements, RESULT-IDENTICAL (INCRBLOCK2_CHECK mismatch=0, subs 238,
111 tests): (a) backtrack rebuilds only the affected SUFFIX (track min node whose
label changed → i2_lo, vs full rebuild); (b) i2_recompute clears/retains only
touched posting-list slots (i2_touched + bitmap) vs scanning all 2x|concepts|
slots/pass. **5303: 10s→8s seq, 5s→4s par8.** Blocking STILL ~60% of wall — neither
helped much ⇒ the cost is genuine suffix RECLASSIFICATION (forward propagation on
low-id nodes keeps i2_lo low ⇒ large suffix), not backtrack/clear overhead.
**BUILD-CORE-ONCE (amortize query-independent backbone across the 94 tests) is DEAD
— proved by KM_HT_COREPROBE:** empty-seed (⊤+TBox) model of 5303 = **1 node**;
per-concept models (256-3064 nodes) share **0%** with it. No backbone exists —
every model is 100% derived from its seed concept. Matches HermiT (builds 134 fresh
fast models, 7ms each, NO core-sharing). So the ONLY lever is per-build cost; the
gap is now per-step efficiency (blocking ~60%), HermiT 0.94s ⇒ ~4x off. Further
blocking gains need a different structure (HermiT core-hashing = our mode0/3 which
DON'T fold 5303), so likely near the practical floor for this approach.
**SUFFIX FLOOR PROVEN (KM_HT_STATS i2 diag, committed 89bf52f):** 249k recomputes,
full_rebuilds only 1.3%, avg_suffix=98. RIGOROUS reason it can't be cut result-
identically: subset blocking is a SEQUENTIAL DEPENDENCY (blocked[n]=∃ earlier
UNBLOCKED superset) ⇒ a change at lo can flip every later node ⇒ [lo..nn] is the
MINIMAL correct recompute; lo low because disjunctions resolve on mid-id nodes all
through search (intrinsic). Only ways past: (a) positive-only blocking sig (changes
which nodes block ⇒ ALC+⊔ completeness risk, needs Lean); (b) bitset labels vs
HashMap (large Ext refactor). FINAL FLOOR: 5303 207s→8s seq/4s par (~50x), ~4x off
HermiT. Session commits: 0ee9879 a020013 61cb79f 89bf52f.

**2026-06-20 SPEED v3 — INCREMENTAL ∃-OBLIGATIONS (committed a020013, pushed).**
After blocking, profiling (added prop_us/oblig_us/eager_us/obligloop_us/obl_iters,
KM_HT_STATS classify-prof line) showed the **obligation loop = 72% of wall**:
process_obligations re-scanned EVERY accumulated obligation every pass (**240M
iters / ~933 per pass**, re-running has_rsucc edge-scan). 92% sit on BLOCKED nodes
(skipped) + most rest already discharged = pure rescan. FIX **KM_HT_INCROBLIG** =
two parallel structures: `node_obligs[n]` (node→oblig indices ⇒ gather only
UNBLOCKED nodes' obligs, sorted to index order ⇒ flat-scan-identical) +
`oblig_sat[i]` (skip discharged, cleared on backtrack). node_obligs ALONE = only
−37% (unblocked obligs still re-has_rsucc'd); **node_obligs + oblig_sat = obl_iters
240M→3.1M (76x), loop 25.8s→2.3s (11x)**, RESULT-IDENTICAL (subs 238, set
byte-identical), 111 tests. **5303 standalone: 25s→10s seq, → 5s par8/16.** From
original 207s = ~40x; HermiT 0.94s now ~5x off. Wired ON in race.rs.
GOTCHA that cost 3 cycles: declared `incroblig` on Ext but referenced `self.incroblig`
in process_obligations (Ht) → build FAILED but val script swallowed it → ran stale
binary → bit-identical results fooled me. Use self.ext.incroblig; ALWAYS fail-loud
on build in validation scripts. NEXT frontier: per-pass gather still scans all
nodes (313/pass=80M floor) — maintain incremental unblocked-set; or build-core-once.

**2026-06-20 SPEED v2 — INCREMENTAL SUBSET BLOCKING (committed 0ee9879, pushed).**
Profiled the 23-54s with KM_HT_STATS: blocking was **65% of wall**, and models are
only **~313 nodes (92% blocked) — TIGHTER than HermiT's 690**. So the gap was NEVER
over-expansion (KM folds MORE than HermiT); it was the per-pass `compute_blocked`
RESCAN of all nodes (O(n²)/build). Battery proof (all with EAGER+NEGTRIED+ORD=1):
mode0/mode3 (O(n) hashed core/pairwise) EXPLODE (24684/14631 nodes, timeout) —
**only SUBSET (mode 1) folds 5303**; KM_HT_WITREUSE is INCOMPLETE (subs=236≠238)
AND slower; PHASE no help. So the only lever = make subset blocking cheaper.
FIX = **KM_HT_INCRBLOCK2**: blocking is strictly by an EARLIER node (m<n), so
blocked[n] depends only on nodes ≤n; track `i2_lo`=smallest node whose label
changed (add_concept/new_node/backtrack→lo=0) and recompute only the suffix
i2_lo..nn (frontier sits at high ids ⇒ tiny suffix). `i2_lists` holds UNBLOCKED
nodes only (the prior KM_HT_INCRBLOCK kept ALL nodes → 10x longer lists → slower;
that's why it lost). **RESULT-IDENTICAL**: KM_HT_INCRBLOCK2_CHECK asserts ==full
scan every pass, 0 mismatches across all 94 builds, set byte-identical (238/238).
Blocking 65%→23%. **Standalone 5303: 54s→25s seq, 24s→10s par8, 9s par16.** Wired
ON in race.rs spawn_ht. HermiT 0.94s ⇒ now ~10x off (was 25-50x). NEXT frontier =
the remaining ~77% (propagate+expand+branch); or build-core-once (94 builds rebuild
the identical deterministic backbone — the deepest redundancy, big architectural
change). Corpus regression after deploy.

**2026-06-20 SOLVED.** 5303 classifies **sound + complete** (CLEAN=True, km_n=238
gold_n=238, unsound=0 incomplete=0) in **207s sequential** with the flag combo
**`KM_HT_EAGER=1 KM_HT_NEGTRIED=1 KM_HT_ORD=2 KM_HT_PHASE=1`** (matrix job
47677091 combo I). First ever sound+complete 5303. concept 31 (hard one): 217s →
2.98s. The +1 completeness gap (CarbonHydrogenSubstructure⊑Hydrocarbon) VANISHED
(incomplete=0) — no M7 frontend fix needed.

Lever = **SEARCH DISCIPLINE, all default-OFF**, NOT blocking mode or learning.
Each lever ALONE times out (G=EAGER+NEGTRIED, H=+ORD2, J=+PHASE all RC=124); only
COMBINED: EAGER (fire ⊤-disj only on unblocked = fold) + NEGTRIED (HermiT
startNextChoice: assert ¬D_di after clash so siblings unit-prop; biggest single
lever 217s→7s) + ORD=2 (most-failing-first VSIDS) + PHASE (warm-start from
consistency model). Model-shaping matrix (job 47676928: EAGER±BLOCK=3±TRIGABS±
HARVEST, A–F) ALL timed out — blocking/absorption NOT the lever.

**SPEED CHASE (2026-06-20, user-directed "target single-digit seconds"):**
- **ORD=1 (least-failing-first) is the champion, NOT ORD=2**: concept31 backtracks
  5650→**41** (BEATS HermiT's ~129!). Combo `EAGER+NEGTRIED+ORD=1` = 123s CLEAN.
  ORD direction was the fix (ORD=1 dives to the usually-consistent disjunct first).
- **Inverted-index subset blocking** (hypertableau.rs compute_blocked mode 1, new
  default; old O(n²) scan kept under KM_HT_BLOCK_SLOW): m⊇label(n) iff m in posting
  list of every concept of n → scan only the rarest concept's list. RESULT-IDENTICAL
  (same blocking relation), pure per-step cost fix. **128s→41s single-threaded**,
  CLEAN. The existing O(n) modes (0 core / 2 eq / 3 pairwise) FOLD TOO LITTLE for
  5303 (mode0 times out seq, OOM-aborts parallel) — only SUBSET folds enough, so
  the win had to be making SUBSET cheap, not switching mode.
- **Parallel classify needs 512MB worker stacks** (dfs is recursive; ORD=1 dives
  ~1859 levels deep; 2MB default thread stack → SIGABRT). Fixed via
  Builder::spawn_scoped. Now: seq 43s, par2 44s, par4 36s, par8 34s — **barely
  scales (1.26x)** ⇒ a big SEQUENTIAL component dominates (suspect consistent([])
  global model build, run once before the parallel phases) and/or load imbalance
  from contiguous chunking. Diagnosing job 47678015 (KM_HT_GLOBAL=1 times
  consistency alone + per-concept dt distribution).
- STATE: 5303 sound+complete in **43s seq / 34s par8** (from 207s). 111 tests pass.
  HermiT=0.94s, so still ~36x off; bottleneck now = the one-shot consistency build.

**SPEED CHASE part 2 (2026-06-20 cont.):**
- consistency([]) = 0s (NOT the bottleneck — empty seed = trivial model). Each of
  the 94 per-CONCEPT tests builds its own ~1645-node model. Profiling (block_us
  field, KM_HT_STATS prints block_ms): **compute_blocked was 73% of wall** (87% on
  hardest concept 311). Cost = rebuilding a fresh HashMap<CLit,Vec<Node>> every
  call (×~n calls per model).
- FIX: **reusable concept-id-indexed flat-vector index** (BlockBuf field, RefCell,
  cleared by touched-slot, no hashing/realloc). RESULT-IDENTICAL to O(n²) scan
  (canonical set-equal confirmed; KM_HT_BLOCK_SLOW keeps the old scan). 41s→**23s
  seq**.
- Dynamic work-stealing parallel (AtomicUsize next-index, each worker reuses one
  Ht): par4=**11s** par8=**10s** par16=11s. Flatlines ~10s past 4 threads ⇒
  bounded by longest per-phase task + phase1/phase2 barrier + likely allocator
  contention (Rc DepSets + per-node HashMaps hammered by 8 threads).
- **STATE: 5303 sound+complete in 23s seq / ~10s par8 (from 207s = ~20x). 111
  tests pass. At the single-digit boundary.** HermiT 0.94s → ~10x off.
- Levers built this chase (all in hypertableau.rs): inverted-index subset blocking
  (default mode 1; BlockBuf reusable buffer), parallel classify_parallel
  (KM_HT_PAR=N, dynamic work-stealing, 512MB worker stacks for deep ORD=1
  recursion), KM_HT_BLOCK_SLOW (validation), block_us/block_ms profiling.

**COMMITTED 70f39b1 (pushed).** e2e `km classify ore_ont_5303.owl`: rc=0 225s
CLEAN 238/238 — 5303 PASSES the real pipeline (was timeout). All emelim canaries
+ sampled normals gold-clean (no soundness regression). Search combo
EAGER+NEGTRIED+ORD=1 + KM_HT_PAR=cores wired into race.rs spawn_ht.
**KEY PIPELINE INSIGHT:** the 225s (vs 10s standalone) is the FALLBACK race
WAITING for CB to give up (~225s near timeout) before taking HT's already-ready
answer. For ht_routable onts HT is sound+complete ⇒ switching them to RACE mode
(take first sound answer) would deliver ~10s end-to-end. Separate orchestration
win (race.rs ht_mode), not done yet. Full corpus regression in flight (job
47680368, km classify over all IBEX corpus vs gold).

**INCREMENTAL BLOCKING (KM_HT_INCRBLOCK, gated, validating job 47680441):**
persistent inverted index on Ext (block_index: encoded-lit→nodes), appended in
add_concept fresh-add + popped on Trail::Concept undo (LIFO-correct per lit).
compute_blocked QUERIES it (no per-call rebuild — removes the O(n·label)/call that
was 59-73% of wall). RESULT-IDENTICAL trick: index holds ALL nodes (blocked or
not) — a node is blocked iff ANY earlier node is a superset (blocked supersets'
blockers are transitively supersets too). If validated set-identical + faster,
flip default.

**INCREMENTAL BLOCKING RESULT (job 47680441): CORRECT BUT SLOWER — negative.**
KM_HT_INCRBLOCK validated set-IDENTICAL to the O(n²) scan, but **40s vs the
committed reusable-buffer's 26s** on 5303. Reason: to maintain a persistent index
incrementally it must hold ALL nodes (blocked included; pruning blocked nodes is
the hard cascade problem — blocked status is derived + flips on growth/backtrack).
5303 is ~89% blocked, so all-nodes posting lists are ~10x longer than the
reusable-buffer's unblocked-only lists → queries ~10x slower, outweighing the
saved rebuild. **VERDICT: incremental (all-nodes) is a dead end for heavily-
blocked models; the committed reusable-buffer (unblocked-only rebuild) wins. Keep
KM_HT_INCRBLOCK GATED OFF.**

**541 e2e TIMEOUT — NOT a regression (job 47680709).** 541's HT TInput has
**number=true** (cardinality); standalone HT TIMES OUT in ALL configs — new combo
par8, combo seq, AND old default (no flags) — all 280s. So the wired combo did NOT
slow it; 541 is just not HT-solvable in budget regardless (hard number+disjunction
ont). My changes are clean. NB ht_routable does NOT check `number`, so number=true
onts route to HT (HT handles ALCQ); 541 times out rather than answers, so no
soundness issue manifests, but watch the corpus regression for any unsound/
incomplete from number-routed onts. Corpus regression 47680368: 200 onts in, all
CLEAN.

**RACE-MODE has a SOUNDNESS CAVEAT (do NOT do blindly).** The ~225s pipeline time
= fallback race WAITS for CB to give up before taking HT's ~10s answer. Switching
ht_routable onts to RACE (take first answer) would give ~10s e2e BUT subset
blocking can be INCOMPLETE under transitive roles (the original routing-guard
reason). Fallback only takes HT on CB failure (safe). Race could prefer an
incomplete HT answer OVER a correct CB answer → incompleteness regression. Needs
HT-completeness validated across ALL routable onts first.

NEXT: (1) attack the sequential consistency([]) cost / load-balance chunks (need
diag result). (2) wire winning flags (EAGER+NEGTRIED+ORD=1 [+blocking is default])
ON for HT path + corpus regression (watch emelim canaries 9024/12141/541/11460/
15491/4604/9635 — ORD=1+fast-blocking change their HT search too). (3) test combo
on family siblings routable to HT.

----
(historical — the diagnosis that led here:)

2026-06-20. HermiT ground-truth trace (HermitBlockingCore over all 94 classes of
ore_ont_5303, job 47676952) OVERTURNS the prior "HermiT folds 5303 to ~3 nodes"
belief from [[project_km_ht_learning_dead]].

**HermiT on 5303:** classifies the WHOLE ont in **940ms**, 134 SAT tests, 17341
total backtracks (~129/test). EVERY concept is `saturations=1`. HermiT does NOT
fold to 3 nodes — its hardest concepts (ChromosomalDNA / DNA-RNA chain family)
build **690-node models with 668 blocked** (~97% blocked, ~22 expanding). So the
fold is real but the model is BIG; the point is each step is cheap.

**KM on the hard concept (qi=12, concept idx 31):** 6779 backtracks, 1516 nodes,
**217 s** = ~32 ms PER BACKTRACK vs HermiT's ~1 ms. The gap is **per-step cost**,
not algorithmic.

**Root cause:** default `block_mode=1` is SUBSET blocking = **O(n²)** (no hash,
`compute_blocked` 2676-2694), recomputed once per propagation pass inside
`process_obligations` (2893) — ~2.3M comparisons/pass over 1516 nodes, ×tens of
thousands of passes = the 217s. Pairwise (mode 3) and core (mode 0) are **O(n)
hashed** → ~1000× cheaper per call. Default block_mode comment says "mode 0
default" but code defaults to 1 (subset) — STALE comment.

**Predicted lever:** `KM_HT_BLOCK=3` (pairwise: core(n)+core(pred)+edge, O(n)
hashed, claimed sound+complete under transitive roles for ALC(H) no-inverse) or
mode 0 (core) should crack concept 31 by killing the per-step cost. Also test
whether mode 3 closes the +1 completeness gap (CarbonHydrogenSubstructure ⊑
Hydrocarbon) — if it does, the gap was a subset-blocking artifact, NOT a missing
composition clause (M7 frontend fix unneeded).

Validation in flight: matrix job 47676928 (EAGER ± BLOCK=3 ± TRIGABS ± HARVEST)
on tin5303.json via canon_cmp vs gold (238 subs). SATFOLD is ABANDONED (unsound,
HermiT never uses cached models to commit disjunct choices). NEXT after matrix:
if mode 3 is slow-but-sound, add incremental blocking (don't recompute from
scratch each pass — task #9).
