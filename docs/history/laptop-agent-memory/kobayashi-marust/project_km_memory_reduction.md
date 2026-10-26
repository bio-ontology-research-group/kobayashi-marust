---
name: project_km_memory_reduction
description: "CB-engine memory reduction via interning (Pred pipeline + global clause arena): 9944 peak 8.5->2.0 GB, the lever for 9724/GALEN memout"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

User directive (2026-06-12): reduce CB-engine memory (bit-packing suggested).
Target: [[project_km_completeness_gaps]] 9724/GALEN, which churns >82 GB
single-threaded (unconverged at kill) vs the 20 GB benchmark memcap.

**Diagnosis tool**: KM_MEMSTATS=1 (engine.rs, diagnostics-only) — per-category
byte accounting at fixpoint via capacity()+size_of. On 9944 (8.5 GB peak,
16500 contexts) it showed each derived clause stored 5+ times:
neighbor_pred 11.4M PredClause copies (2.06 GB), pushed_pred full copy per
edge (1.0 GB), succ/pred_pool full copies (0.8 GB), clause_keys full copies
(0.44 GB), max_head duplicate of head (0.39 GB), Msg::Pred carrying cloned
core+clause per queued message.

**Fix = interning/sharing, NOT bit-packing** (bit-packing Lit 16->12B would
save ~25% of literal arrays; interning saved 31x on whole clauses):

- Stage 1 (commit 228067f): engine-level `pred_interned` table for
  back-substituted PredClauses; contexts hold u32 ids; `neighbor_pred_seen`
  dedups duplicate arrivals (real, from pre-/post-growth successors).
  `pushed_pred` keyed by (edge -> pred_pool index). `Msg::Pred` carries
  {to, from, edge_label, pool_idx} (24 B) — sender pool entry + core are
  immutable so apply-time resolution == send-time snapshot.
  Result: 11.37M pred-clause instances -> 387,647 distinct (29x).
  9944: 8.50 -> 4.99 GB, wall 2:58 -> 2:26, output identical.

- Stage 2 (global clause arena): `cc_arena: [Vec<ContextClause>; 2]` split by
  ordering domain ([non-root, root] — same (body,head) has different cached
  max_head under root vs non-root ordering, NEVER cross the domains).
  Content-hash + exact-compare intern (`cc_find`/`intern_cc`).
  Context.worked_off/todo/pred_pool/succ_pool: Vec<u32> arena ids;
  clause_keys: HashSet<u32> (arena id IS the canonical content key);
  head indexes store arena ids (u32). shared_closure/shared_root_closure:
  Vec<u32> — seeding a context shares arena entries instead of cloning the
  full closure per context (8009 root contexts on 9944!).
  back_subsume: ids stable, worked_off.retain + rebuild_head_index(arena).
  saturate pops id, clones ONE transient working copy.
  Result: 6.08M worked_off instances -> 193,012 distinct (31x).
  9944: 8.50 -> 1.99 GB peak (-77%), wall 2:58 -> 1:56 (-35%),
  output identical (315,940 subsumptions exact). 49+16 cargo tests pass.

Both stages are representation/dedup only — derived clause set unchanged, no
Lean re-cert (skipping a duplicate Pred arrival only skips re-deriving
clauses add_clause would dedup).

**Remaining whales on 9944 after both stages** (1378 MB accounted, 2.0 GB RSS):
head_indexes 429 MB (7.7M entries, Vec headers dominate across 16.5k
contexts), neighbor_pred ids 202 MB, pred_interned 162 MB, pushed_pred idx
155 MB. Next levers if needed: smallvec/boxed-slice index lists, u32 packing
of (usize,Term) edge keys, Lit 16->12B bit-pack.

**Validation bar**: byte-identical subsumption set on 9944 vs pre-refactor +
multi-ont batch (12698 disjunctive core, 13912, 2669, 15516, 6720, 14896,
dhv) vs /tmp/km-baseline (ws) on converged runs (fixpoint unique => baseline
comparison valid even though baseline predates churn fixes).

**Sweep status**: 5874 (25M cap) = 546 ok / 42 timeout / 3 memout
(10860, 16303, 16444); 9944 now ok. Correctness vs gold: 544 agree /
1 incomplete / 1 unsound (16461 or 6999 miss=1; 11745 = known parallel
watchdog nondeterminism). The 25M cap REGRESSED passrate vs 5M (550->546):
onts that truncated-early-then-passed now burn 240s. Complete-default kept
per mandate; recover via speed (this memory work also bought -35% wall).

**2026-06-12 arena-binary results (commits 228067f + 06c8dc5, deployed,
sweep 5905 validating):**
- Multi-ont identity batch vs pre-refactor baseline: ALL identical
  (12698-core, dhv, 13912, 6720, 14896/32451 subs; 4 skips = both-binaries
  timeout on live-disjunction family). Output-preservation fully confirmed.
- **16444 (memout since forever): CONVERGES for the first time -- 19:29 wall,
  58.9 GB, sig BYTE-IDENTICAL to Konclude gold (sha 5109eb2f..., 1,189,232
  subsumptions, ore_canon-replicated on ws via /tmp/check16444.py). The
  calculus is CORRECT on it; purely a resource gap (59 GB vs 20 GB cap).**
- 16303: 3.96 GB single-threaded (memory problem GONE) but >30 min wall --
  becomes a timeout, needs speed not memory.
- 9724 (GALEN): arena run ~3x less memory than old (27 GB @ 68 min vs 82 GB
  @ 56 min), still running on ws toward convergence + the
  does-fixpoint-derive-the-77731 question.
- Deployed kobayashi-marust-batch on unimatrix (md5 6820d72d...,
  bak: .bak-prearena). Sweep 5905 = first arena-binary full sweep.

**2026-06-13 RE-CONFIRMED: memory is NOT the lever for the goal (do not pursue).**
Implemented `max_head: Vec<Lit>` -> `max_head_mask: u64` (commit c663a84,
byte-identical, 82 tests). 16444 peak A/B on node005: 66218 MB (batch) ->
66120 MB (mem) = **98 MB / 66 GB = 0.15% saving**. KM_MEMSTATS on 16444
(single-thread, accounted 14.8 GB across 84265 contexts) shows the hotspots are
NOT clauses (cc_arena = 0.3%) but two u32-id collections:
**pushed_pred 45.8% (562 M entries, HashMap<(ctx,Term),HashSet<u32>>)** +
**head_indexes 33.9% (75 M, HashMap<key,Vec<u32>>)**; clause_keys/worked_off/
pools ~15%. pushed_pred is a sparse time-varying subset (an index becomes
sendable on an edge only once the edge accumulates enough pushed predicates),
NOT a prefix, so no hwm-counter collapse; roaring bitmaps could cut it ~8x
(~6.7->0.8 GB) but it's the HOT Pred loop = perf risk.
**DECISIVE: 16444 converges in 19:29 (1169 s) wall vs the 240 s benchmark
timeout — it is ALSO ~5x too SLOW. Even at infinite RAM it times out.** So
the roaring lever cannot recover 16444 (or the other pure-scale memouts, same
shape). Memory work is conceded for the all-pass goal. The productive leads are
(1) KM_SEQ_ORDER disjunction recovery (+3 clean, [[project_km_perf_pivot]]),
and (2) the 3 disjunction-class onts SEQUOIA SOLVES but KM times out
(12141/5303/9024, all gold-clean) — same CB family, so KM has a closable
pruning/redundancy gap there, NOT intrinsic hardness. That is where to dig next.

**Sweep 5905 RESULT (arena binary, deployed): 545 ok / 44 timeout / 2 memout;
correctness 543 agree / 1 incomplete / 1 unsound / 0 both.** vs 5874
(546/42/3): the ONLY status changes are 16303 (memout->timeout: peak 20GB->4.2GB,
memory fixed but now 240s-slow) and 8737 (ok->timeout @ 240.01s, peak 6GB =
ELC-PATH timeout noise, elc untouched by this change; was 205.7s in sweep 5690).
Every CB-engine ont kept identical status -- arena change is status- and
output-neutral on the corpus, zero soundness/completeness regression. Memout
3->2 (16303 escaped). 16444 still memout (59GB converged > 20GB cap) but now
PROVEN calculus-correct. CONCLUSION: memory work shifts the bottleneck from
memory to SPEED -- the freed onts (16303) are slow not big; passrate gain now
needs convergence speed (parallel CB? the arena enables sharing the arena
across query threads) + the genuine completeness gaps (16461 cardinality,
12698/1340 disjunction-scale). NOT more memory.
