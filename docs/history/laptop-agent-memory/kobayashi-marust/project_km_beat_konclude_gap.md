---
name: project_km_beat_konclude_gap
description: "2026-07-05 STRATEGIC REFRAME - the beat-Konclude goal is dominated by a systematic SPEED gap on SOLVED onts, not the 8 timeouts; IBEX panel 48085418 quantifies it"
metadata:
  node_type: memory
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

**2026-07-06 RE-CONFIRMED (IBEX job 48105343, fresh full 584 sweep, snapshot
committed results/benchmarks/2026-07-06-ore-reasoner-cmp/):** reproduces the
213-WIN state. solved km 576/584 (7 genuine timeouts: 541 3215 7914 9663 9724
12653 14817, +10621 contested); **sound+complete 572 MATCH 0 DIFF excl 9
contested** — km correct on EVERY finished ont. NEW precision (medians over
both-solved): km median wall 0.386s vs Konclude 0.272s = **1.30x slower
median**; km median peak 109MB vs 135MB = **0.63x (lighter)**; faster on
214/576, lighter on 366/576, **faster AND lighter (the goal) = 213/576 (37%)**.
Mean wall km 8.92s vs 2.35s (tail-heavy). Speed tail: 6246/15491/12141/9024/
9635/5303 = 225-251s vs Konclude <1s. Mem tail: 5303/9540/9635/12698 ≈ 45GB vs
100-450MB (disjunction family). Confirms the reframe below UNCHANGED; the
session's bridge work (konclude_ht production route) is the aimed-at lever for
the tail but is NOT yet production-ready ([[project_km_bridge_nondeterminism]]).

2026-07-05: ran the full reasoner_cmp panel (IBEX job 48085418, KM vs
konclude/elk/hermit, wall+peak+gold on the same node) to measure the actual
beat-Konclude goal (faster AND less mem AND sound+complete on EVERY ORE ont).

**THE REFRAME (FULL 584-ont panel, authoritative):** the goal is dominated by
a SYSTEMATIC SPEED GAP on onts KM already solves correctly, NOT by the timeouts.
km_vs_konclude.py over all 584 (575 both-ok): **WIN (faster AND less-mem) = 136
(24%); SLOWER = 233; SLOW+MEM = 203; MOREMEM = 1** (=> KM loses speed/mem on
437/575 = 76%); WRONG = 2 (2669+15516 DIFF = SWRL contested-gold, KM CORRECT
per HermiT, gold bogus); FAIL = 9; KONC-FAIL = 0. Soundness is NOT the problem:
573/575 gold-MATCH + the 2 contested = KM sound+complete everywhere it finishes.
Worst slowdowns: 12141 KM 225s vs Konclude 0.17s; 10908 20.6s vs 0.2s; 10702
20.4s vs 0.17s (the nomlink-fixed nominal ont — now correct but the nominal/CB
path is slow); 1016 3.4s vs 0.38s. Many are 10-100x.

FAIL (9, konclude ok): 541, 3215, 7914, 9663, 9724, 10621, 12653, 14817 (my
tracked-8) + **14459** (153MB near-giant, 0 rules so NOT a regression from the
SWRL change; konclude 41s / elk 15s / hermit 190s — genuinely hard). 2669+15516
moved FAIL→contested-correct (they now run + return inconsistent by default).

**The gap is REAL + ALGORITHMIC, not measurement noise.** Clean unloaded ws
head-to-head, ore_ont_1016 (GALEN SHIF(D), 32739 subs): KM 3.38s / 1.0GB vs
Konclude 0.38s / 172MB = ~9x slower, ~6x more mem. KM_TIMING breakdown: frontend
0.40s, CB engine ~2.3s (CB slot @2.77s), total 3.32s. 1016 is el_rbox_safe=true
but the TBox is SHIF(D) (functional + datatype) so elc correctly bails →
CB+HT race → the CB engine's ~2.3s IS the gap. Not a routing bug; it is
CB-engine saturation efficiency vs Konclude's decade-optimized engine
(lazy saturation + signature-keyed successor cache + descriptor-driven firing,
see [[project_km_konclude_saturation_engine]]).

**Implication for the goal:** closing the 8 remaining timeouts (541 3215 7914
9663 9724 10621 12653 14817) still leaves KM LOSING on ~140 onts for being
slower. The dominant lever is CB-engine (and HT) THROUGHPUT: interning,
Horn-clause indexing, context dedup, lazy ∀-extension, successor-signature
caching (levers already mapped in [[project_km_throughput]],
[[project_km_memory_reduction]], [[project_km_konclude_saturation_engine]]).
This is multi-session engine-optimization work, not flag-flips.

**Session wins that DID land:** [[project_km_swrl_rules]] default-on (+2 tracked
timeouts 2669/15516, sound, corpus-inert via rules_active gate); role automaton
mechanism complete+tested in konclude_ht ([[project-km-role-automata-port]],
6a7a67e) but NOT yet wired to production (14817 still times out; clause-level
EDGE_COMPOSE/CHAIN_UNFOLD both blow up on transitive-edge closure, confirming
the state-automaton is needed).

**Profiling localisation (1016, KM_STATS, single-thread CB = 5.18s / 230MB;
parallel 2.3s; Konclude 0.38s):** contexts=4683 (3088 root + 1595 succ),
root_wo_total=396048, succ_wo_total=294719, propagate=11801, pred_checks=569956,
succ_scans=548119, hyper_calls=658882, saturate=818923. The hot path is the CB
saturation rules — the r-Pred nested scan (engine.rs:2961-3109, pred_pool ×
edges, already freshness-guarded but carries completeness guards that warn of
livelock on ABox-heavy onts like 10594) + r-Succ + Hyper. ~1.1M pred/succ scans
+ 659k hyper calls for 3088 roots / 32739 subs. Konclude's 0.38s ⇒ KM does
~14x the work-per-answer. Next-session optimization MUST be data-driven (need
perf — NOT on ws, build a profiling binary or add fine counters) + Lean re-cert
for any derivation change + full-corpus output-identity. NO safe blind hot-loop
edit exists (risks the soundness KM currently achieves on 100% of finished onts).
Race note: lazy-HT-spawn (defer the fallback HT subprocess until CB misses a
short budget) is tempting for overhead but CONFLICTS with the fast_certify
early-harvest (race.rs:896, SHOQ/QO arms harvested after a short budget while CB
still runs — those recover 7581/9540 and NEED HT running in parallel). Only the
plain-fallback (non-fast_certify) onts could lazy-spawn safely.

**KM_PROF_TIME per-rule profiler LANDED (1c60145 + d6455e3):** set KM_PROF_TIME
+ KM_STATS to get per-phase cumulative wall time in the CB saturation. Zero-cost
when off (thin `_inner` wrapper = cached-bool branch + direct call; verified
5.09s vs 5.10 baseline). Complete 1016 breakdown (single-thread CB, 5.25s):
pred_local 810ms (15.4%) | add_clause 654ms (12.5%) | hyper 345ms (6.6%) |
propagate 320ms (6.1%) | subsume 94ms (1.8%) = 42% localised; the other ~58% is
message-handling back-substitution (apply_succ/apply_pred pred_payload Vec
allocs) + the saturate-loop machinery (clause.clone 0.5%, max_head().collect
per clause, the pred/succ pool feed). **KEY: NO single phase dominates** — the
cost is distributed, so the ~14x gap is systemic algorithmic efficiency, NOT a
hot-spot. Largest single target = pred_local (r-Pred local resolution, 15%) but
even zeroing it leaves ~11x. Next: instrument apply_succ/apply_pred + the pool
feed to close the 58% gap, then the real work is Konclude's lazy ∀-extension +
signature-keyed successor caching (systemic, multi-session, needs byte-identity
+ Lean re-cert).

**Cheap-optimization hypotheses RULED OUT by direct measurement (1016,
single-thread CB = 5.18s):** (1) per-call env::var in saturate/trigskip cached
to struct fields at new() — committed, output-identical, but WALL UNCHANGED
(5.18→5.10s, within noise; getenv is a cheap array scan). (2) clause.clone() at
saturate top — throwaway timer measured 690767 clones = 25.5ms = 0.5% of
runtime, NOT the bottleneck (ContextClause Vecs are small). So the 5.2s is
spread across the genuine reasoning rules (hyper unification, fwd/back
subsumption checks, add_clause) — inherent CB-saturation work, ~14x Konclude.
CONCLUSION: no single hot spot, no cheap fixpoint-preserving win. The gap is
algorithmic (Konclude's lazy ∀-extension + signature-keyed successor caching +
descriptor-driven firing). Real optimization needs those techniques ported
(large) + proper profiling (perf/valgrind NOT on ws — must build a profiling
binary or add per-rule cumulative timers) + full-corpus byte-identity + (if
derivations change) Lean re-cert. The CB engine is already indexed
(hyper: clauses_cand + head_concept/role_index + backtracking join), interned
(pred_interned + cc_intern_idx), and freshness-guarded — it is MATURE, not
naively slow.

**2026-07-06 NEW MEASUREMENTS (1016, ws, post-8796e2f build):** (1) Thread
scaling: KM_THREADS=1/2/4/8/16/34 → user 5.0/6.4/8.4/11.4/15.0/22.7s, mem
229/275/351/465/633/861MB, wall 5.2/3.4/2.4/1.7/1.4/1.0s. Duplication is
LINEAR: each extra worker engine re-pays ~0.54s (≈11% of single-thread work =
the shared upper-taxonomy core it rebuilds). Even ideal shared-graph
parallelism → wall ~1s straggler floor + 229MB base vs Konclude 0.38s/172MB —
the CB engine needs ~13x CPU AND ~1.5x memory to WIN this family; parallel
mode can't close it. (2) Certified-elc (KM_ELC_CERT default 2, already racing)
BAILS on 1016: repair model completes (150 residual clauses, 209 additions)
but the 209 additions are FORCED (no provenance entries) → refinement can't
ban anything (new_bans=0) → 1546/3088 subjects undetermined > residue cap 64 →
exit 3. Both polarity seeds produce IDENTICAL models, so the cross-model
intersection eliminates nothing. Cert lever capped ~2x here even if the cap
were raised (residue = half the subjects). (3) Whole-run phase timers landed
(0fbd175): parse 47ms / build 11ms / saturate 5252ms / extract 4ms / write 2ms
— the run IS saturation. CONCLUSION UNCHANGED + sharpened: beat-Konclude on
the solved-slower band = port Konclude's engine (konclude_ht) to production.
NEXT BRICK CHOSEN: bridge.rs — TInput/HtClause (cb_to_ht output, reverse-
Skolemized ∃/∀ form) → OntologyArenas (CCATOM/CCIMPL/CCOR/CCSOME/CCALL
concepts, the classify_test Env encoding generalised), keeping konclude_ht
test-only until verdict-parity vs tableau.rs on synthetics + small ORE onts.

**PORTFOLIO CB-ARM ABSORPTION FIX — LANDED (e7771ae, 2026-07-06):** the REAL
root cause of the portfolio speed/memory tax was NOT the elc process — it was
that race_adaptive_vs_elc ran its CB arm via run_engine_adaptive on the ABSORBED
clause set directly, while cb_stack runs CB via race_absorbed_plain (8s PLAIN
probe, then absorbed). On onts where absorption makes CB harder (1082),
absorbed-only = 44s/8.7GB vs plain-probe 2.9s/130MB. Fix: portfolio CB arm now
calls race_absorbed_plain (same as cb_stack) when absorb on. Output-IDENTICAL,
1390 tests. Measured: 1082 4.94s/2198MB→3.91s/677MB; 11502 1.56s/307MB→
1.32s/66MB (now beats Konclude 173MB). **PANEL 48086814 CONFIRMED corpus-wide vs
baseline 48085418: WIN 136→166 (+30, 24%→29%); SLOWER 233→216; SLOW+MEM 203→190;
FAIL 9→8 (14459 the 153MB near-giant RECOVERED); 0 unsound, 0 regressions.** The
single biggest beat-Konclude improvement of the session. Remaining 8 FAIL: 541
3215 7914 9663 9724 10621 12653 14817.

**IN-PROCESS FRONTEND FAST PATH — LANDED (d01dc0c), PANEL-CONFIRMED +47 WIN.**
Panel 48088964 vs 48086814: WIN 166→213 (+47), SLOWER 216→153, FAIL 8→8, 0
unsound. CUMULATIVE this session (absorbed-plain + in-process frontend, vs
baseline 48085418): **WIN 136→213 (+77), 24%→37% beat-Konclude on BOTH
speed+mem; timeouts 9→8.** Side effect: +16 SLOW+MEM/MOREMEM = speed-losses
shifting category (the in-process parse peak on the larger sub-2MB onts tips
their memory) — NOT WIN→loss. TUNABLE: lowering IN_PROCESS_OFN_MAX (2MB) toward
~512KB would drop those 16 memory shifts while keeping the trivial-ont WINs
(<200KB); needs a re-panel to confirm the WIN/mem tradeoff. addresses the
near-tie lever below. classify forked the ofn subprocess even for trivial onts (standalone
ofn <10ms but classify frontend ~50ms = fork/exec of the 4.4MB binary + clause/
meta file round-trip). Fix: onts < 2MB run the frontend IN-PROCESS via
ofn_to_clauses (same fn), write the clauses file, return Meta. Output byte-
identical; memory-safe (2MB cap keeps the giants' multi-GB transient parse peak
in the subprocess; small-ont transient is tens of MB, freed before the engine).
Opt out KM_NO_INPROC_OFN. Measured ~30% faster on trivial onts (5966 0.11→0.07s;
2672 0.20→0.14s), 1390 tests. Panel 48088964 measuring the WIN gain (was 166 in
48086814; the ~125 near-tie onts are the target).

**NEXT LEVER — fixed-overhead on near-tie onts (panel 48086814 SLOWER
analysis):** of 216 SLOWER onts, 125 are within 2x of Konclude and the closest
~10 are ratio 1.00 (km 0.1405s vs konc 0.1404s — losing by <1ms on trivial
~0.14s onts). km_vs_konclude.py counts ties as SLOWER (`wall >= konc`), so KM
must be STRICTLY faster. These trivial onts are dominated by KM's FIXED OVERHEAD:
km classify RE-EXECS the frontend `ofn` as a SUBPROCESS (fork+exec + clause-JSON
serialize→file→deserialize), plus the racing subprocess spawns, where Konclude
parses in-process. On ws a trivial ont is frontend@0.02s + engine@0.05s. Cutting
the frontend subprocess (run ofn IN-PROCESS as a library call for small onts)
could shave the few ms that flip ~30-50 near-tie onts to WIN. Risk: the
orchestrator is built around subprocess workers for memory isolation; an
in-process fast path for small onts needs care. Untested — a real opportunity.

**C++ KONCLUDE FALLBACK — investigated, NOT viable (also can't dev on ws).** The
ws-local Konclude (~/konclude-build/Release/Konclude) FAILS on the ORE files
("all parsers failed" → hangs in Precomputing); only the harness's static build
(bench/reasoners/Konclude-v0.7.0-1138-...-Static-Qt5.12.10) parses them. So a
fallback can't even be dev/tested on ws. Plus owlxml output (km has no parser)
and it yields ties not WINs. Full reasoning:
The user's "call Konclude directly where necessary" cannot mean spawning the C++
binary as a km arm: (1) the raw ORE .owl files DON'T parse in Konclude directly
("all parsers failed" — the harness uses a specific static build
Konclude-v0.7.0-1138 + NFS-bundled libpcre.so.3); (2) Konclude outputs OWLXML
(harness FMT["konclude"]="owlxml"), and km's frontend parses functional syntax
NOT owlxml — a whole new parser needed; (3) even if wired, km=Konclude+spawn
overhead = SLOWER not WIN (delegation never beats). **konclude_ht DISJUNCTION BLOCKER PINPOINTED (01860b7, tested).** Added 3
end-to-end disjunction classification tests to classify_test.rs; 2 pass
(both-branches-close A<=B|C,B<=D,C<=D=>A<=D; all-branches-unsat), the negative
control (#[ignore]) EXPOSES a real UNSOUNDNESS: konclude_ht's OR-branching uses a
CHRONOLOGICAL backtrack (try_backtrack_or_branch, u02) that only works when a
failed disjunct clashes AT INSERT-TIME. When a disjunct causes a DOWNSTREAM
derivation (B<=D derives D, D clashes with probe ~D), the backtrack advances to
the next disjunct but does NOT undo that derivation → clash persists → open
branch falsely closed → FALSE subsumption. This is THE core blocker for
konclude_ht on the ORE disjunction family. Fix = dependency-directed backjump
with completion-graph state restore (arena truncate_to + databox watermark, the
unported Unit 28/30 tracking lines) OR per-disjunct state fork. Both are the
documented multi-session branching-subsystem work. FEASIBILITY confirmed for the
mutation-trail path: the label set is a REMOVABLE HashMap<Cint64,...>
(satellites.rs:369 concept_des_dep_map; has insert_concept but NO remove yet —
add one) and there's an existing ConceptLabelSetModificationTag (satellites.rs:218).
So a sound backtrack IS buildable: (a) trail label-set adds in
add_concept_to_individual (u36.rs:475), remove on backtrack; (b) trail edge/node
creates (∃ rule) — arena truncate_to (substrate.rs:142) rewinds allocations but
the successor-hash references need explicit removal; (c) OrBranchPoint records the
trail watermark at push; try_backtrack_or_branch (u02:180) undoes past it before
adding the next disjunct. Guard: if only label-adds happened, sound; successor-
creating branches need (b). Soundness-CRITICAL — build + unit-test each mutation
type; do NOT rush. This is the standalone multi-session track.

**SOUND-BACKTRACK FIX LANDED (2026-07-06, commit 8796e2f, pushed).** 1393
tests green incl. the un-ignored negative control. The label-only restore was
NOT enough — it flipped the two POSITIVE disjunction tests to failing. Debug
trace (KM_HT_DBG-style eprintln, since removed) showed why, and it's a lesson
for the whole branching subsystem:
- The label set, the node's ConceptProcessingQueue, and trigger-reapply firing
  are COUPLED state. Restoring only the label set left the queue with stale
  branch-1 descriptors AND wiped derivations that consumed-from-queue trigger
  descriptors had produced; nothing re-derived them → false fixpoint → branch
  falsely open. FIX = snapshot label set + ConceptProcessingQueue as a PAIR at
  OR-push, restore both (both are cheap value types; queue = 15 priority-slot
  linker heads).
- Queue snapshot validity argument: con proc descriptors are arena-allocated,
  NEVER pooled/reused, and an existing descriptor's intrusive next link is only
  written when that descriptor is itself (re)inserted → a push-time head still
  addresses exactly the push-time chain.
- SECOND bug was in the TEST HARNESS: is_unsatisfiable re-seeds all GCIs per
  pass and broke on stable concept COUNT — but a backtrack SWAPS one disjunct
  for another (count unchanged) and the restore wipes that pass's re-seeded
  GCI descriptors. Added algo.or_backtrack_count (bumped on every advance/pop
  in try_backtrack_or_branch); harness now breaks only on stable count AND no
  backtrack in the pass.
- Reminder why the harness re-seeds at all: apply_implication_rule's
  addConceptToReapplyQueue install is W3-DEFER (unported) — an absent trigger
  does NOT register a reapply, so GCIs only re-fire via re-seeding. The
  faithful condensed-reapply install is a later port unit.
Same-node disjunction is now SOUND end-to-end in konclude_ht; successor-creating
disjuncts still fall back to chronological behaviour (node_count_at_push guard)
and need the task-fork/Unit-28/30 work. FIRST brick of the branching subsystem
DONE.

**DEEPEST FINDING (why no bounded slice exists): a concept ADD is not a single
mutation.** add_concept_to_individual (u36.rs:518-546) on a real add does FIVE
coupled things: (1) insert into the label-set HashMap, (2) add_blocking_core_
concept (521), (3) set_individual_node_concept_label_set_modified flag (527),
(4) add_concept_preprocessed_to_processing_queue (531), (5) apply reapply-queue
(540). Undoing just the label HashMap leaves the processing queue + blocking core
polluted → still unsound/buggy. AND the state is MIXED: arena-allocated (rewound
by truncate_to) vs HashMap/queue (need explicit snapshot). So the sound backtrack
MUST be a COORDINATED save/restore of the whole completion-graph state at each
branch point (arena watermarks + databox db1 save/restore + per-node HashMap
snapshots), wired into try_backtrack_or_branch. That coordination — not any single
undo — is the multi-session subsystem. db1 save/restore is ported (process/db1.rs)
but NOT wired into the OR-backtrack; that wiring + the HashMap snapshots is the
concrete next-session build. The role-automaton
(6a7a67e) is done; OR-backtrack state-restore is the next port piece, now
precisely tested (un-ignore subsumption_via_disjunction_one_branch_open when fixed).

So "call Konclude" = use the
RUST PORT (konclude_ht) as the fallback — the actual beat-Konclude vehicle
(in-process Rust, no JVM, could match/beat C++). That is the multi-session path,
blocked on the structural(CCSOME/CCALL)-vs-clausal(skolemized DL-clause) frontend
mismatch: konclude_ht needs a STRUCTURAL frontend (or de-skolemization); km's
parse.rs AST is structural and could feed it, but wiring AST→OntologyArenas→
classify is the large port (role-automaton piece DONE, 6a7a67e).

**ht_budget_s=225 lever — NOT a WIN lever, has DIFF risk, do NOT lower blindly.**
The SLOW+MEM worst onts (6246 240s/32GB, 5303/9635/12141/9024 ~225s/6-45GB) all
hit exactly ht_budget_s=225 (config.rs:172): CB is DOOMED, so km waits the full
225s budget then takes HT's (complete, gold-MATCH) answer. 5303's HT actually
finishes at 13s. BUT even 13s is ~100x Konclude's 0.12s, so lowering the budget
only cuts km's WASTE (225s→15s, memory too) — it does NOT create WINs (km stays
far slower than Konclude on these). AND lowering it risks DIFF: onts where CB
finishes in [new_budget, 225s] with a COMPLETE answer but an INCOMPLETE HT would
flip MATCH→DIFF (HT is incomplete on live-disjunction; the 225s budget is the
safety margin). DIFF = losing the sound+complete requirement (the one part MET).
So the budget is a robustness knob, not a beat-Konclude lever. The disjunction
onts are unbeatable without Konclude's algorithm: both km CB (blows up) AND km
HT (13s) are 100-1000x Konclude's 0.12s. THIS is the systemic gap — the ONLY
path to WIN on them is porting Konclude's disjunction/tableau efficiency
(dependency-directed backtracking + caching), i.e. finishing konclude_ht.

**THE WIN COUNT IS NOISY (±20-30) — do NOT chase near-ties with micro-opts.**
Panels: in-process-frontend 213, lazy-HT-grace 184, CB-first-reorder 178 — the
HT-timing changes all land ~180 while the SAME-fragment in-process code measured
213. With ~200 onts near-tie at the 0.1-0.4s measurement floor, a few ms of
node contention (80 concurrent array tasks) flips 20-30 WINs run-to-run. So the
WIN metric only reliably resolves STRUCTURAL changes (absorbed-plain +30,
in-process frontend +47 — large, real). Sub-10ms orchestration tweaks are lost
in the noise AND risk the delicate race path. True WIN value is ~190-213. LESSON
for next time: to move WIN reliably, make changes bigger than ±25 (systemic CB
efficiency on the FAR onts, or structural), NOT near-tie micro-timing. The
CB-first reorder (8b57730) was output-correct + tests-green but measured 178
(<=213, within/below noise) so REVERTED (0c3ae62); its concurrent spawn_ht
convert may also slow CB on disjunction onts.

**CB-FIRST REORDER (8b57730) — REVERTED (0c3ae62), see noise note above.** The CORRECTED form of
lazy-HT: race_cb_vs_ht called spawn_ht (fork/exec 4.4MB + read+convert ~5-15ms)
BEFORE spawning the CB thread, delaying CB's start. Fix = spawn CB thread FIRST,
then spawn_ht immediately (NO grace). CB unblocked; HT NOT deferred (so
fast_certify not hurt, unlike the 0.5s-grace lazy-HT). Output-preserving,
1390 tests, 9540 recovery solves (57.8s). If panel WIN <= 213 (no gain), the
5-15ms saving is below the panel's measurement floor — revert or accept.

**LAZY-HT (grace version) — REGRESSED -29 WIN, REVERTED (ab7d7cb → 2107e37).
Do NOT retry the GRACE-DELAY form.** Panel 48089881 vs 48088964: WIN 213→184 (-29),
SLOWER 153→273, SLOW+MEM 203→117. My safety analysis was WRONG: HT IS the fast
winner on fast_certify (SHOQ/QO) onts — those are harvested WHILE CB is still
running (CB slow), so the 0.5s grace delayed 29 winning onts → SLOWER. Same
failure mode as lazy-elc (the arm is the fast winner on some onts). The memory
DID improve (SLOW+MEM/MOREMEM -91: not spawning HT saves memory) but those onts
still lose speed, so no new WINs; net -29. LESSON: any lazy-spawn of a racing
arm that can win FAST on some fragment is a net loss — the near-tie speed gain
is offset by delaying that arm's fast wins. The near-tie overhead must be cut
WITHOUT delaying HT (e.g. spawn HT cheaper/async, or an in-process HT fast path),
not by deferring it. Original (flawed) analysis below (for reference):

**NEXT LEVER (DONE above) — lazy-spawn the HT arm (race_cb_vs_ht), grace-delay
like the tableau race.** After the in-process frontend, panel 48088964 still has 153
SLOWER, 90 of them <=1.5x and the closest at ratio 1.00 (5665 km 0.1018s vs konc
0.1018s — losing by <0.1ms). Residual fixed overhead = the EAGERLY-spawned HT
subprocess (spawn_ht at race.rs:891), wasted on trivial onts where CB wins
instantly (~5-10ms of the 0.1s). Fix = spawn CB first, grace-delay (mirror
race_cb_vs_tableau lines 145-162 / cfg.tab_race_delay), spawn_ht ONLY if CB
misses the grace. SAFE (unlike lazy-elc): HT is NEVER the fast winner over a
finishing CB — fallback mode always prefers CB, and fast_certify (SHOQ/QO)
harvests only matter on CB-SLOW onts (grace elapses → HT spawns → harvest after
budget, negligibly delayed). Keep reserved=n-1 threads on CB (unchanged) to
minimise the refactor; only defer the spawn. Delicate concurrent code (the
recovery-critical race) — validate output-identity + a fast_certify recovery
(7581/9540) + the near-tie speedup before committing; revert if anything is off
(cheap, done twice). Potential +40-90 WIN.

**LAZY-ELC — TRIED TWICE, WRONG, do NOT retry.** Deferring the elc racer until
CB misses a budget (KM_LAZY_ELC_S) REGRESSES onts where elc is the FAST winner:
KM_TIMING on 1082 shows EAGER elc wins at 0.97s (elc is fast on EL-safe onts),
LAZY defers it → CB slot at 13s. There is a genuine SPEED/MEMORY TRADEOFF with
no clean win: CB-only 1082 = 2.9s/130MB (wins mem vs Konclude 371MB, but
slower); elc-portfolio = 0.97s/677MB (wins speed, loses mem). To beat Konclude
on 1082 needs BOTH → neither config does it. This is the crux: many onts have
one KM config winning speed and another winning memory, but not one winning
both. Real fix = make CB itself both fast AND lean (the systemic saturation
efficiency work), OR make the leaner arm (CB-only) also faster than Konclude.

**Earlier (superseded) hypothesis — lazy-spawn alone does NOT fix it
(measured 2026-07-06):** the default portfolio races CB + HT + certified-elc
CONCURRENTLY. On the many onts CB solves alone, running CB-ONLY
(KM_NO_ELC_PORTFOLIO=1 KM_NO_HT_RACE=1 → cb_stack) is 8-14x LESS peak memory
AND faster, output-IDENTICAL: 11081 3.35s/1171MB→1.64s/85MB; 12405
1.18s/477MB→0.55s/38MB; 11502 1.59s/310MB→1.12s/26MB; 10778 6.19s/2683MB→
4.69s/210MB; 10248 11.81s/4146MB→7.92s/481MB (7 of 7 SLOW+MEM onts tested).
Since CB's answer is always taken when CB finishes, the arms are pure resource
tax on CB-solvable onts. BUT: adding a gated lazy-elc spawn to
race_adaptive_vs_elc (KM_LAZY_PORTFOLIO_S, spawn elc only after CB misses a
budget) MADE IT WORSE (1082 4.64s/2227MB→11.65s/3944MB) and was REVERTED. Root
cause: race_adaptive_vs_elc runs CB via run_engine_adaptive (parallel-first,
reserved threads) which itself behaves differently from cb_stack's CB — so the
6GB in the lazy path is elc still spawning because CB-in-portfolio is SLOWER
(thread reservation) than CB-only, missing the budget. The real fix needs the
portfolio to run CB via the SAME lean path as cb_stack (full threads, no
parallel-first blowup) before spawning arms — i.e. reconcile
run_engine_adaptive-in-portfolio vs cb_stack thread/memory behaviour, then
lazy-spawn BOTH arms. NOT a quick change; needs corpus validation (must not
regress the giant/disjunction/fast_certify recoveries the portfolio exists for:
15803, 6212, 8737, 7581, 9540, 5303). NOTE: race.rs ALREADY lazy-spawns the
TABLEAU arm after tab_race_delay (race_cb_vs_tableau) — the elc portfolio should
mirror that pattern but reconcile the CB path first.

Panel infra: IBEX /ibex/scratch/hohndor/km, reasoner_cmp.sbatch (account
pi-hohndor, partition batch, 584-ont array prof/cmp_onts.txt), km_vs_konclude.py
aggregator. Build via build_all.sbatch (builds km+ofn+elc+tableau_cli, NOT just
kobayashi-marust). ws has Konclude at ~/konclude-build/Release/Konclude for
local head-to-head (but ws load makes sub-second wall noisy; use -o file for
/usr/bin/time capture, konclude spews warnings to stderr).

## 2026-07-07 — KONCLUDE SPEED BAR MEASURED (ws, -w8, reframes the bridge role)

Direct ws timing of Konclude on the two bridge-target onts:
- ore_ont_12653: **0.11 s / 23 MB**, 42 subsumptions.
- ore_ont_541:   **0.05 s / 33 MB**.

Implications for the "beat Konclude" goal:
1. The bridge (faithful Rust port) is NOT a speed play. On 12653 it takes
   ~1.0 s (10x Konclude) via per-subject fresh saturations; on 541 it
   THRASHES (no termination) where Konclude finishes in 50 ms. A faithful
   port of the same algorithm cannot out-run tuned C++ Konclude by
   construction — at best comparable, realistically slower.
2. 541 is an ont where PRODUCTION km TIMES OUT (240 s) but Konclude does
   0.05 s. So the gap is not "km slightly slower" — km FAILS where
   Konclude is trivially fast. The bridge SHOULD match Konclude here (same
   algorithm) but thrashes because it lacks Konclude's PERFORMANCE
   mechanisms: absorption of ∀-in-body (so the definer-introduction
   disjunction is not global) and LAZY definer recognition (deterministic
   ∀-satisfaction check instead of a ⊤→Def∨∃R.¬C branch on every node).
   These are the same guarded-definer / lazy-recognition levers already
   identified for 541 (see [[km-bridge-disjunction-probe]]). They are
   REQUIRED for the bridge to compete, not optional.
3. Strategic: the bridge is a SOUNDNESS/COMPLETENESS tool for the hard
   timeout family; to make it FAST it needs Konclude's absorption + lazy
   recognition ported (big work). For the 213/576 onts where production km
   already dominates (faster+lighter), the lever remains CB/HT throughput,
   not the bridge. Beating Konclude on the ~363 onts where Konclude is
   0.05-0.5 s is the genuinely hard majority of the goal.

## 2026-07-07 — DIRECT ws HEAD-TO-HEAD (production km vs Konclude -w8)

| ont   | km time | km RSS   | Konclude time | Konclude RSS | verdict |
|-------|---------|----------|---------------|--------------|---------|
| 1016  | 1.77 s  | 1082 MB  | 0.42 s        | 91 MB        | km LOSES 4x slower, 12x heavier |
| 12653 | TIMEOUT (>240s) | — | 0.11 s        | 23 MB        | km LOSES (times out) |
| 541   | TIMEOUT (prod) | —   | 0.05 s        | 33 MB        | km LOSES (times out) |

Sobering reality for the "beat Konclude on EVERY ont" goal: on the onts
measurable on ws, production km is 4-10x SLOWER and 3-12x HEAVIER than
Konclude, or times out. Konclude is 0.05-0.5 s on everything tried. The
213/576 "dominating" onts from baseline job 48105343 must be a specific
harder subset (likely memory-heavy / CB-favourable onts where Konclude
takes seconds) — none of the onts currently on ws are in that winning
set; they are all the HARD cases where km struggles.

Consequence: the bridge (this session) is not a path to the goal — even
if it made 12653 sound+complete in ~1 s (via production wiring), that is
still 10x Konclude's 0.11 s, so it would NOT be "faster". A faithful
Rust port of Konclude's algorithm cannot beat tuned C++ Konclude on
speed; at parity it is slower. The only onts where km can win are those
where its DIFFERENT algorithm (CB saturation, clone-free EL, low peak
memory) genuinely out-performs Konclude's tableau — the 213 subset. To
grow that set the lever is CB/HT engine throughput + memory, NOT the
konclude_ht port. The goal as stated (beat on EVERY ont, incl. ones
Konclude does in 50 ms) may be unreachable for a same-algorithm port and
needs the CB engine to be the primary vehicle.

## 2026-07-07 — in-process CB engine: +25 goal-wins, IBEX A/B confirmed (b2f58fd)

Extended the in-process elc fork-elimination to small NON-EL onts
(`try_inproc_engine` runs Reasoner::{new,saturate,subsumptions} as a
library call, skipping the engine-worker fork + stdin round-trip;
byte-identical). Controlled IBEX A/B (same nodes, shared Konclude,
faster+lighter `<=`, both solved):
- OFF:     576 solved, 218 faster+lighter+sound WINS
- safe-ON: 576 solved, **243 WINS**  => **+25, ZERO solved regression**

CRUCIAL LESSON — the discipline that caught a false result:
1. The naive single panel showed 272 vs a "318 baseline" and LOOKED like a
   regression. It was NOT comparable (different-day run). ALWAYS A/B on the
   SAME panel era (km ON vs km OFF, shared Konclude) to isolate a change —
   the near-tie band is single-rep ±30 noise.
2. The first version (8847b85, budgeted-detach) gave +54 winning BUT −2
   SOLVED: on the CB memory-blowup family (internal definer disjunctions,
   9635→45GB) the detached-on-overrun worker fought the forked fallthrough
   for memory and OOM-ed 9635/12698. A winning-set gain that DROPS solved
   onts is a correctness regression — reject it.
3. Fix (b2f58fd): gate on `Reasoner::has_internal_definer_disjunction()`
   (now pub) — the exact blow-up signature. Only bounded-memory onts run
   in-process, so a lingering worker can't OOM. Non-definer fast onts win
   (3260 0.12→0.02s byte-identical); definer onts decline + fall through
   (9635 solves 225s byte-identical). Restores 576 solved, keeps +25.

Snapshot: results/benchmarks/2026-07-07-inproc-engine-safe/. The lever for
MORE wins remains: the ~150 lighter-but-slower onts (km already <=Konclude
mem, loses on time) — fork-elimination flips the fork-dominated ones;
deeper wins need CB/HT engine throughput + the 45GB disjunction memory
(interning) and the 8 timeouts. Konclude bar is 0.05-0.5s on most onts, so
"beat on EVERY ont" stays very hard; km currently wins a large minority.

## 2026-07-07 — frontend from_slice fix: +30 more wins (cumulative session +55)

Profiling an engine-bound ont (10073: km frontend 19s vs Konclude 4s total)
found the cost was NOT the algorithm but serde_json::from_reader(File::open)
on the 21MB --meta file (473k iri_map entries) — the unbuffered-reader trap.
Read-then-from_slice: 10073 frontend 19s->5s, total 27s->13s, peak unchanged,
SEMANTICALLY IDENTICAL. Fixed frontend_run.rs:137 (meta) + race.rs spawn_ht
clause reads; LEFT parse_out (engine worker stdout) on from_reader (it streams
the giants' 100s-of-MB output without RSS blowup). Commit 2b8f224.

Three-way IBEX A/B (shared Konclude, same nodes, all solved=576):
  OFF 218 -> in-proc-engine 243 (+25) -> +from_slice 273 (+30)
= **cumulative +55 goal-wins this session, ZERO solved regression** (37.8% ->
47.4% of 576). faster 218->294; km lighter on 425/576 (74%) so SPEED is the
binding constraint. Snapshots: results/benchmarks/2026-07-07-inproc-engine-safe/
+ .../2026-07-07-frontend-slice/.

NEXT throughput levers (the ~150 remaining lighter-but-slower onts):
1. ofn subprocess still ~5s producing 21MB meta — is the meta reducible?
   (pipeline may only need declared/named classes, not all 473k IRIs); the
   clausification may over-expand (6MB clauses from 41MB ont).
2. CB engine race ~8s on 10073 — engine throughput (interning per
   project_km_memory_reduction also helps the 45GB disjunction family).
3. Hard tail: 8 timeouts + 45GB disjunction memory. Konclude 0.05-0.5s bar
   on most onts keeps "beat EVERY ont" very hard; km wins a growing minority.
LESSON: profile before optimizing — the biggest win this session was a
1-line serde perf bug (from_reader->from_slice), not a feature. And the panel
NUMBERS themselves were understated by that bug on large onts.
