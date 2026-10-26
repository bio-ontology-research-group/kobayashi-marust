---
name: project_km_throughput
description: "Characterization of the big-file/giant ORE timeout cluster (user-chosen direction 2026-06-14): frontend is NOT the bottleneck; splits into central-memory-blowup, context-explosion, and large near-Horn derivations. No quick wins; concrete next levers identified."
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-14, branch `disjunction-split`. User chose "throughput/giant onts" as the
residual direction (after both easy +1s — tableau-race and 6246 — were falsified;
see [[project_km_absorption]]). Profiled the 12 big-file (>10MB) timeouts on IBEX
([[feedback_prefer_ibex]]; jobs 47514459 profile, 47514492 growth-curves with
110GB mem so OOM doesn't truncate the curve). Used the deployed `kobayashi-marust-
batch` + `ofn-absorb` (KM_ABSORB=1), KM_PROF/KM_TRACE.

**FINDING 1 — the frontend is NOT the bottleneck.** `ofn` is 1–4.5 s even on the
87 MB ont (7246 = 2.48 s; 132 MB 15803 likewise small). The streaming parse
(CLAUDE.md) works. The wall is the CB ENGINE saturation. Clause counts: 7246=757k,
1194=1.06M, 7581=499k, 4669=527k, 3215=440k, 11460=425k, 9663=301k, 14817=272k,
10621=244k.

**FINDING 2 — the cluster splits into 3 distinct failure modes, NOT one:**
1. **Central memory blowup (the OOM cases): 9663, 4604, 11460.** Under central +
   multi-thread they hit ~25 GB in 13–26 s (no mem cap) and OOM. 9663 with 110 GB:
   central holds only ~1170 contexts but the per-context closure-sharing arenas
   (cc_arena) balloon to **115 GB for ~407k worked-off clauses** (~280 KB/clause —
   the memory is in the central closure structure, not per-clause). In production
   (KM_PAR_MEM_GB=18 cap) these get killed and fall to the LEGACY single-thread
   path, which then times out.
2. **Context explosion: 11460 (108,926 contexts!), and the small-file 6682/7499/
   7914.** Central keys a context per trigger-set core; tens of thousands of cores.
3. **Large near-Horn derivations: 7246 (757k cl, 0 disj heads — PURE HORN),
   7581 (499k cl, 0 disj — PURE HORN), 1194/10621/14817 (few disj).** Run 360 s
   under 110 GB WITHOUT OOM and still don't finish. 9663 legacy: 79,562 contexts,
   worked-off climbing LINEARLY past 5M clauses at guard 2.6M, head mostly ≤1, not
   converging. So these are genuinely large monotone saturations.

**NOT throughput (mis-grouped by file size): 4669 (72,989 disj heads), 3215
(18,323 disj heads)** — these are disjunction-blowup family, belong with
[[project_km_disjunction_blowup]], not here.

**FINDING 3 — no quick wins.** These are large derivations (millions of clauses,
10k–100k contexts) that converge in neither central (memory) nor legacy (time)
within 240 s. This is real reasoner-scaling work, multi-session, like the
disjunction family. The ~33-ont gap to Konclude is uniformly hard across BOTH
residual directions (disjunction convergence AND throughput).

**CANDIDATE LEVERS (next focused work chunk, all sound / fixpoint-preserving / no
Lean re-cert — perf+representation only):**
- **(a) Memory reduction for central — DIAGNOSED, found NECESSARY BUT NOT
  SUFFICIENT (2026-06-14, jobs 47515376/47515409).** Clauses are ALREADY globally
  interned (cc_arena + cc_intern_idx; per-context worked_off stores only u32 ids),
  so the OOM is NOT per-clause duplication. Tested the hypothesis that the OOM is a
  PARALLELISM memory-multiplication artifact (the `_run_engine` docstring: parallel
  central re-derives shared successor contexts per query chunk → multiplies memory):
  **single-thread central on 9663/4604/11460 does NOT OOM** (stays under 115 GB) —
  CONFIRMED the parallel multiplication is the OOM cause. BUT single-thread central
  **STILL TIMES OUT** (>300 s; a MSG_CAP=4M single-thread central run took >10 min
  just to approach 4M guards). 9663 legacy also showed worked_off growing LINEARLY
  past 5M clauses without plateau. So these are genuinely LARGE derivations:
  memory reduction (or single-thread routing) would stop the OOM but the onts would
  STILL time out. **Lever (a) alone recovers 0** — do NOT implement it standalone
  (effort without coverage payoff, the same trap as the tableau-race / 6246 dead
  ends). Recovery needs BOTH a memory fix AND a large throughput/derivation-count
  reduction → multi-session, same tier as the disjunction family. (If memory work
  is ever pursued, first get the KM_MEMSTATS structure breakdown under a MSG_CAP so
  it's targeted; the run is slow so use a guard cap well below OOM.)
- **(b) Horn-saturation throughput** — 7246/7581 are PURE HORN yet time out at
  ~750k/500k clauses. CODE-CHECKED (engine.rs:1462 hyper, 1566 hyper_join): the
  match loop is ALREADY INDEXED — `ont.clauses_cand(&max)` (ontology clauses by max
  pred), `ctx.head_concept_index`/`head_role_index` (worked-off by head IRI), +
  fewest-candidates-first backtracking JOIN (not cartesian product). So the
  "non-indexed O(n^2)" hypothesis is REFUTED; these are genuinely large derivations.
  The visible constant-factor cost is `self.cc_arena[d][cid].clone()` at
  engine.rs:1293 (clones the clause on EVERY work-off iteration — millions of allocs;
  comment says it's needed because the arena entry is shared while `self` mutates).
  Eliminating that clone (e.g. take/swap, or split borrows) is a broad constant-factor
  lever (maybe ~2x) but likely NOT enough alone for onts needing >>240 s. Lower ROI
  than (a).
- **(c) Context dedup / strategy routing** for the 80k–110k-context onts (11460,
  6682, 7499, 7914) — central keys too many cores; needs either coarser core keys
  or a per-f route that doesn't fan out as far. Harder.

## 2026-06-15 KM_CTXSPLIT instrumentation — root vs successor work split (user: "do the shared-successor parallel strategy, beat Konclude")
Added `KM_CTXSPLIT=1` to engine.rs run_for (gated, inert default): splits wall
into root-SEED vs message-FIXPOINT, and worked-off into qroot vs successor
contexts. Single-thread central, bounded KM_MSG_CAP, on IBEX (jobs 4751593x).
**The optimistic "74% parallelizable root work" read at 1M messages was a snapshot
artifact — DO NOT trust early-cap splits.** Real per-ont behaviour:
- **9663** (58,192 queries): 1M msgs = 2.24 GB / 132 s, split 74% root. BUT
  **4M msgs = 115 GB / 2009 s (33 min).** Memory explodes super-linearly in the
  msgfix TAIL (4x msgs -> 50x mem). The blow-up is the successor/central
  core-growth cascade, not N x worker duplication. Needs >4M msgs, never converges.
- **4604**: blows past **110 GB by just 1M msgs** single-thread (OOM-killed before
  printing the split). Pure derivation blow-up, even faster than 9663.
- **11460** (83,482 queries): modest 1.65 GB at 1M, balanced 48% seed / 52% fix,
  PRED-dominated (682k pred vs 318k succ msgs), succ neighbor_pred=100k,
  top_succ_wo=4139. The one with successors that actually receive pred. Unknown if
  it blows later (only 1M measured).
**CONSEQUENCE — shared-successor parallel strategy PARTIALLY FALSIFIED for the
memory cluster (9663/4604):** the wall is an INTRINSIC single-thread memory blow-up
(100+ GB), NOT parallelizable worker duplication. Sharing a read-only base across
query-parallel workers cannot fix a base that is itself 115 GB. Same conclusion as
[[project_km_perf_pivot]] Lever-2 shelve + lever-(a) "necessary-but-not-sufficient".
**The strategy's REAL targets are the TIME-bound, memory-OK near-Horn group**
(7246/7581/1194/10621/14817 — run 360 s under 110 GB WITHOUT OOM): if THOSE are
root-dominated, parallelizing roots over a shared base recovers them with no memory
wall. Measuring CTXSPLIT on them (job 47516320) + MEMSTATS-at-high-cap on 9663/4604
to pinpoint the 115 GB structure (job 47516296). GO/NO-GO pending those.

## 2026-06-15 VERDICT — shared-successor parallel strategy does NOT recover the throughput cluster (FALSIFIED by MEMSTATS; do NOT build the refactor)
MEMSTATS on 9663 (jobs 47516922 caps 800k/1.5M) pinpoints WHERE the memory lives,
and it kills the strategy's premise:
- **cc_arena (the interned clauses) = only 6-8% (~50 MB).** So arena-sharing
  (the lever2 ArenaView/Interner refactor) would buy almost NOTHING here.
- **Memory is ~all PER-CONTEXT bookkeeping: head_indexes 47-55% (the dominant
  cost — per-context HashMap<Iri,Vec<u32>> x3, ~237k tiny HashMaps across 79k
  contexts), then trigger_sets ~11%, clause_keys ~7%, predecessor_edges,
  pushed_succ/pred.** These are inherently per-context.
Consequences (the kill shots):
1. **9663/4604 exceed 20 GB single-thread at convergence** (9663 = 115 GB at 4M
   msgs, NOT converged; 4604 >110 GB by 1M). Single-thread alone is over the 20 GB
   production cap. Parallelism MULTIPLIES per-context memory (total RSS approx
   (0.77 + 0.23*W)*S because roots are 77% and split by W, successors 23% rebuilt
   per worker) -> makes memory WORSE. No sharing helps (arena is only 6-8%).
2. **The premise was wrong:** the heavy work is NOT a shareable successor graph
   rebuilt N times (successors = 23%, tiny contexts top_wo=369). It is the
   per-query ROOT contexts (77%), which are inherently unshareable (one per query),
   plus per-context structure that parallelism duplicates.
3. **7246/7581 (Horn, time-bound) are ruled out by per-STEP cost:** even 150k
   messages take >37 min single-thread (>15 ms/msg; huge contexts, head-index
   scans). Convergence needs millions of msgs; even a perfect 16x speedup stays
   far over 240 s. So root-dominance is moot.
**Same conclusion as [[project_km_perf_pivot]] (Lever-2 shelved, parallelism
inert) and lever-(a) (memory necessary-but-not-sufficient): the throughput cluster
is research-grade — intrinsic-scale derivations (per-context memory over the cap
and/or per-step cost), NOT parallelizable worker-duplication.** Did NOT build the
refactor (would recover ~0; same trap as tableau-race/6246/lever-a).
**The data-justified lever IF this class is ever revisited:** per-context
representation reduction — replace the 79k x3 tiny head-index HashMaps with a
compact structure for small contexts (head_indexes are 47-55% of RAM). Sound
(representation only, no Lean). BUT likely still recovers ~0 (a 3-5x per-context
cut leaves 9663 ~30-80 GB at 4M, still over cap and not converged); it would mainly
speed the smaller members. The REAL fix is algorithmic: tame the central
core-growth cascade that generates millions of clauses (the same root cause as
[[project_km_disjunction_blowup]] core-growth), or a different expansion strategy.
DELIVERABLE this session: `KM_CTXSPLIT` engine instrumentation (gated, inert
default; root-seed vs msgfix time + qroot/succ worked-off split) — kept for future
throughput diagnosis.

State preserved: 554 gold-clean (no engine changes landed this session; the 6246
work-probe was reverted). IBEX has a CURRENT c91a813 build + corpus (~893 onts) for
parallel profiling. Profiling sbatches on IBEX:
`/ibex/scratch/hohndor/km/{profbig,profcurve,ctxsplit,ctxsplit2,memstat,horn}.sbatch`,
outputs in `prof/`. KM_CTXSPLIT engine change is on the laptop working tree (not yet
committed); IBEX engine/ has it built.
Related: [[project_km_memory_reduction]], [[project_km_central_strategy]],
[[project_km_disjunction_blowup]], [[project_km_perf_pivot]].
