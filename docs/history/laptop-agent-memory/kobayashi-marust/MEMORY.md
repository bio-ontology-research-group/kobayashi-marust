# Memory index

## Current (2026-07-11)
- [Plan to solve 7914/9663/9724 documented in repo (docs/SOLVE-7914-9663-9724.md); Stage 0 DONE](project_km_solve_7914_9663_9724.md) — konclude_ht OR-pipeline + saturation port; failing bind-variable test = wrong expectation (mNextVariableID inits 1) fixed, suite 1450/0; Konclude delays every OR (152 delay vs 64 fork) + resolves deterministic → Stage 1a (OR planning pipeline: initializeORProcessing/planORProcessing/executeORBranching) is primary lever

## Current (2026-07-10)
- [Ext wrong clashes FIXED (c116a9c): polarity-blind implication trigger watch; 541 ext-ON now SOUND with 6-9/59 answered; 12653 "regression" = not a regression](project_km_saturation_first.md) — task #24 wave 3: watch-side insert_concept_reapplication_return_triggered checked positive presence only (C++-faithful, but the bridge's implication() also emits negative-presence triggers) → +E satisfied a ¬E trigger on resolved ext nodes → (¬E∧Q_6→Q_12)→(Q_12→¬E) clash; fix = thread wanted polarity (=!linker.negated); reproducer 0/20 wrong (was 8/8), FIRST sound nonzero family coverage, KM_HT_SAT_EXT stays opt-in (541 saturation 0.4→40s + variance); bisect CLOSED: plain-bridge 12653 poison-defer is BY DESIGN since 7a01372 complete-or-defer (the 10-20s "plain closes" memories = pre-7a01372 era; cont-19 17s = COW+DDB probe harness); debug aids KM_SAT_CLASH_TRACE / KM_SAT_ADD_TRACE / SAT-SUBJ/NAME/CONCEPT dumps landed; suite 1424/1424
- [Saturation-node coupling LANDED opt-in KM_HT_SATCACHE=1 (1b57b9d+bf282e8); ddmin done = 13-axiom ext reproducer](project_km_saturation_first.md) — task #24 wave 2: u17/u22/u08 expand-from-saturation + caching-blocking + ∃-absorption live, saturation runs ON the probe env + arenas carried through resets (adopt_saturation_state_from); OPT-IN because coupled probes poison EARLIER (12653 subj 1 vs 14) until the ext-resolve refinement lands; KM_HT_SATURATION alone ≡ plain (verified); ext wrong-clash reproducer = ws:~/km-frontend/ddmin541/minimal.owl (13 axioms, inverse-role ∀-closure shape); suite 1424/1424
- [Precise ATMOST test + queue-misroute fix LANDED (8481c9b+76cc6e0); family still 0; next = satnode cache into probes](project_km_saturation_first.md) — task #24 wave 1: full isCriticalATMOST port (collect+mergeability+ancestor marks) + label-merging-problematic completion + BTreeMap succ map + 5 tests (1420/1420); BUG: s03 CCT_DISJUNCTION/EQCAND were 4/5 vs Konclude 2/3 → all OR criticals defered by the VALUE stub; post-fix or=1843/1234 genuinely critical → criticality path exhausted, lever = wiring cache/satnode.rs into probes; ext-ON wrong clashes persist post-BTreeMap (ddmin on ws PID 3940386); ws incident: km-timeout harnesses MUST killpg (orphans drove load to 730)

## Current (2026-07-09)
- [Saturation-first LANDED opt-in (18c9a46); sound = extensions OFF; family coverage 0](project_km_saturation_first.md) — task #23: KM_HT_SATURATION=1 wires saturation before probes; 5 port bugs fixed (stub checkNextCriticalConcepts infinite loop, linker-pool cycle, [identity] super-role sweep s06-s10, conservative critical flips, root-⊤ on probe roots = default-path under-detected-unsat fix); 12653: 0.06s 0/21 answered (family all critical-deferred); 541 extensions ON = UNSOUND (11-13 wrong unsat, Cell/Organism/Atom; gold #UNSAT empty; nondeterministic) → bisect pinned successor-EXTENSION machinery → default now ext-OFF (KM_HT_SAT_EXT opt-in); next levers = precise ATMOST test + merging enqueue, W6-DEFER extension bodies + HashMap→BTreeMap + pollution audit
- [Unsat-cache CLOSED: functional (1c931e7), verdict = ZERO REUSE on family (cont-19 final)](project_km_bridge_disjunction_probe.md) — bug 1: bridged concepts lacked TERMINOLOGY (u22 rejected all lines; fix = stamp sweep); bug 2: write-slot ring had ONE slot → wait_cache_write_prepared spins forever after first write (gdb-proven; Konclude = workers+2; fix = ring 3 + bounded rescan → skip-not-hang); post-fix measurement: overhead ~ZERO (12653 17.2s with vs 17.0s without), 27,984/87,449 lines written, 0 HITS on 12653/541 — family nogood lines carry seed+branch atoms, never recur as label subset → cache cannot prune the family (valid negative; earlier "tax"/"null" were the deadlock); Konclude's family speed = saturation+absorption, NOT its unsat cache; KM_HT_UNSATCACHE correct+cheap+OFF; NEXT LEVER = saturation-first probe answering (12 ported saturation units in front of bridged_unsat)
- [Complex-qualifier choose-trigger = suspected KONCLUDE BUG; KM keeps eager choose](project_km_atmost_rest_port.md) — hook installed on PARENT queue for SUCCESSOR-side triggers, single writer, no fallback reader → deferred successors permanently skipped by ≤n; signature = wrong-SAT on non-atomic qualifiers; candidate explanation for contested-gold 8941 family; queue semantics settled (per-node label set, tag-keyed, pos+neg merged, drains on add to holding node)
- [Unsat-cache wiring + Arc-COW hash satellites (cont-18)](project_km_bridge_disjunction_probe.md) — 1fc2618: dormant cache wired live (handler install, reset carry, read probes at Konclude rule points, u21 read gate on unrestored_advance_count==0); counters on handler (9c03476); Arc-COW extended to role_succ/distinct/succ_role hashes; suite 1409/1409 × 4 modes

## Current (2026-07-08)
- [Bridge complete-or-defer RESTORED; bridge arm net -1, keep OFF (cont-17)](project_km_bridge_disjunction_probe.md) — 7a01372: unrestored advances phantomize ∃-successors → poison defers SAT; control panel ATTRIBUTED: KM_HT_BRIDGE=1 flips exactly 7581 ok→timeout, closes nothing; baseline 576/584, open set = 541 3215 7914 9663 12653 14817 10621 9724; km wins BOTH medians (0.21s/33MB vs 0.25s/135MB), 356/576 faster+lighter; snapshot results/benchmarks/2026-07-08-bridge-panel/
- [Per-node COW + choose-trigger LANDED; COW opt-in](project_km_atmost_rest_port.md) — 0c5848f: label sets + proc queues Arc-COW (O(1) journal save, deep copy on write = Konclude task-fork shape); all-atomic choose-trigger deferral; DECISIVE (cowddb-48445184): COW and COW+DDB both >600s vs plain 10s defer on all 4 → residual = SEARCH VOLUME, not restore cost
- [At-most resume port (KM_HT_ATMOST_REST)](project_km_atmost_rest_port.md) — task #20: incremental link scan via edge watermark, persistent candidate lists, distinct-clique init clash, static rest-carrying reapply; suite-validated; value GATED behind per-node COW (poison bail fires first)
- [u29 DDB wrong-UNSAT FIXED: leftover poisoning (cont-16)](project_km_bridge_disjunction_probe.md) — 7c521cb: gate WHOLE clashedBacktracking on unrestored_advance_count==0; COW+DDB never trips it (production combo); found by ddmin 264→5 axioms

## Current (2026-07-07)
- [Bridge phantom card-def root-caused + 12653 plain GOLD-CLEAN (cont-13/14)](project_km_bridge_disjunction_probe.md) — 84e38bf: absorption-only delivery of card_defs; oracle green all 6 modes; 12653 plain missing=0 spurious=0
- [Session +55 goal-wins (218→273)](project_km_beat_konclude_gap.md) — in-proc engine +25 (b2f58fd) + frontend serde from_reader→from_slice +30 (2b8f224, 10073 frontend 19s→5s); 47.4% of 576; LESSONS: profile first, A/B same-panel-era, solved-drop = regression
- [Bridge 541 soundness fixed](project_km_bridge_disjunction_probe.md) — a4a3ae6: u08 ∀-reapply dropped dep track point → wrong root-cancel; fixed via create_all_dependency threading

## Current (2026-07-06)
- [Bridge vs disjunction timeouts](project_km_bridge_disjunction_probe.md) — 12653 SOLVED 1.0s + DDB-green (93e62e4: 5 dependency-spine gaps); u29 DDB behind KM_HT_DDB
- [In-process elc fast path](project_km_inproc_elc.md) — small EL-safe onts skip worker forks via elcomplete::classify library call; byte-identical, KM_NO_INPROC_ELC opt-out
- [ORE baseline 2026-07-06](project_km_beat_konclude_gap.md) — 48105343: sound+complete (572 MATCH 0 DIFF excl 9 contested); faster+lighter 213/576
- [Bridge nondeterminism CLOSED](project_km_bridge_nondeterminism.md) — 5099d52: 10 faithful-port gaps fixed; 30/30 deterministic

## Current (2026-07-05)
- [Beat-Konclude gap REFRAME](project_km_beat_konclude_gap.md) — goal DOMINATED by systematic SPEED gap on solved onts, not the 8 timeouts; lever = CB/HT throughput
- [SWRL default-on (+2 timeouts)](project_km_swrl_rules.md) — 0d20dd1: KM_HT_RULES rule-gated default-on; closes 2669+15516 correct-inconsistent
- [Role-automata port LIVE (14817)](project_km_role_automata_port.md) — 6a7a67e: automaton end-to-end in konclude_ht; NOT production-wired
- [10702 nomlink fix](project_km_10702_nomlink_fix.md) — {a}⊑∃R.{b} nomlink clauses added → 587/587 MATCH
- [Card default-on + 541 CARD_FN](project_km_card_default_on.md) — card+recog DEFAULT-ON (+1603/9540/7499); KM_HT_CARD_FN functional→≤1
- [2026-07-05 panel baseline](project_km_panel_2026_07_05.md) — 571/584 ok, 0 unsound; ALWAYS set KM_BIN in reasoner_cmp.sbatch
- [12698 named-set fix](project_km_12698_named_fix.md) — 03cdb8b: HT arms passed EMPTY named to cb_to_ht
- [Speed: adaptive polling + race verdict](project_km_speed_polling.md) — f05bccd poll backoff killed ~0.2s floor; race mode UNSAFE default

## Hard rules (user feedback)
- [ws: no orphaned km processes](feedback_ws_no_orphans.md) — clean by PID after every session; timeout+setsid ORPHANS the child; never name-based sweeps while other legs run
- [IBEX login nodes: no compute](feedback_ibex_login_no_compute.md) — build+sweep via Slurm; kill orphans by PID via node jump
- [no benchmark hardcoding](feedback_no_benchmark_hardcoding.md) — never condition on ont ids; general structural rules only
- [build before benchmark](feedback_build_before_benchmark.md) — small synthetic unit tests first; unit tests on ws not IBEX login
- [port from Konclude](feedback_port_from_konclude.md) — PORT from Konclude source, do NOT invent; blocking = isLabelConceptOptimizedBlocking
- [measurement reporting](feedback_measurement_reporting.md) — passrate + avg AND median time/mem + gold split sound vs complete
- [Konclude NOT gold where it fails](feedback_konclude_not_gold.md) — validate via HermiT/ELK consensus
- [Prefer IBEX for compute](feedback_prefer_ibex.md) — ssh dragon, pi-hohndor, batch; rsync→cargo mtime gotcha: touch src before build
- [KM benchmark versioning](#) — dated snapshots under results/benchmarks/, never overwrite; docs/CONTESTED-GOLD.md defines gold rule

## Timeout-family diagnosis (active)
- [SWRL DL-safe rules (2669/15516)](project_km_swrl_rules.md) — ABox as nominal nodes + rules as HtClauses; both correctly inconsistent
- [Faithful Konclude number-port](project_km_konclude_number_port.md) — cardinality non-folding = disjunction-family wall (landed + default-on)
- [Card-recognition non-convergence](project_km_card_recognition_nonconverge.md) — unguarded ⊤→Q∨NQ EM branches every node; fix = guarded recognition (in CARD_RECOG)
- [r-Succ completeness gap (7914)](project_km_rsucc_gap.md) — transitive+inverse under-detected-unsat; fix = edge-conditioned forward push + Lean re-cert; GATED
- [Giants taxonomy + full sweep](project_km_giants_taxonomy.md) — never-completes=8; ∀-saturation vs disjunction split; use ore_canon for sweep scoring
- [14817 transitive automaton](project_km_14817_transitive_automaton.md) — fix = Konclude role-automaton ∀-propagation
- [Konclude saturation engine](project_km_konclude_saturation_engine.md) — descriptor-driven firing + signature-keyed successor cache + lazy ∀-extension
- [SHIQ-completion build](project_km_shiq_build.md) — P2.1 sound-∀ DONE (KM_HT_QO_SHIQ); crux = incremental mode-3 blocking
- [Throughput cluster](project_km_throughput.md) — 12 big-file timeouts; levers = interning, Horn indexing, context dedup
- [Memory reduction](project_km_memory_reduction.md) — interning: 9944 peak 8.5→2.0GB output-identical; KM_MEMSTATS

## Landed features (validated)
- [7581 QoSat + router sweep](project_km_router_sweep_7581.md) — gold-exact via INVCHAIN+GFCERT+short-QO-budget (16e6749); deep detail [project_km_7581_qosat.md](project_km_7581_qosat.md)
- [5303 SOLVED + FAST](project_km_5303_perstep_cost.md) — 207s→5s via KM_HT_INCRBLOCK2 + KM_HT_INCROBLIG; gotcha: fail-loud builds
- [elc EL++ completion (ELK-guided)](project_km_elc_elxx.md) — 8737 63→22s; ws binaries don't run on IBEX (glibc); ofn takes ont PATH + --meta
- [Absorption portfolio](project_km_absorption.md) — KM_ABSORB_PORTFOLIO default-on (+9 ORE gold-clean)
- [Seqorder win (+6)](project_km_seqorder_win.md) — KM_SEQ_ORDER strictly dominates base
- [Hybrid CB/HT](project_km_hybrid_cb_ht.md) — monotone-safe fallback; routing guard = lossless cb_to_ht
- [Pure-Rust port](project_km_rust_port.md) — owl_classify.py → typed Rust km binary (orchestrate/)
- [Datatypes](project_km_datatypes.md) — data-property axioms un-dropped + concrete-domain oracle (1e168e4)
- [Nominals CB](project_km_nominals_cb.md) — Phases 0–3 + Lean cert; pending perf before default-on
- [Cardinality recognition](project_km_cardinality_recognition.md) — 16461 fixed (fd94c7e)
- [Central strategy](project_km_central_strategy.md) — central expansion + closure sharing (554→562 ok)
- [Giant routing](project_km_giant_routing.md) — all 3 giants recovered (15059/16744/8737)
- [EL certificate](project_km_el_certificate.md) — sound+complete near-EL routing
- [Contested gold (use HermiT)](project_km_contested_gold.md) — HermiT right on all 4 contested onts; docs/CONTESTED-GOLD.md
- [Unsound diagnosis](project_km_unsound_diagnosis.md) — all 4 "unsound" were GOLD bugs

## Dead ends (proven, don't retry)
- [QO dead-end](project_km_qo_deadend.md) — KM_HT_QO strict -2 → gated off
- [HT learning DEAD](project_km_ht_learning_dead.md) — conflict learning inert on 5303; pathology = decision depth 15k+
- [HermiT+Konclude port (gated M1/M3/M6)](project_km_hermit_konclude_port.md) — trigger-absorption/harvest/pairwise inert on 5303
- [Family diagnosis (shortcuts closed)](project_km_family_diagnosis.md) — caching/EL-cert/anywhere-blocking disproven; path = absorption + model-based classification
- [Threads vs algorithm](project_km_threads_vs_algo.md) — Konclude's edge algorithmic (-w1≈-w8); KM parallel amplifies memory
- [Disjunction blowup](project_km_disjunction_blowup.md) — ordered resolution FALSIFIED; needs case-splitting/tableau convergence
- [5303 diagnosis](project_km_5303_diagnosis.md) — subset-blocking incompleteness for ALC+⊔, NOT transitivity
- [HT search gap](project_km_ht_search.md) — EAGER refuted; MODELPRUNE net-negative → off
- [Ablation router](project_km_ablation_router.md) — 569 = flag ceiling; throughput giants are NEAR-EL (extend elc)
- [Disjunction split (Dir B+C)](project_km_disjunction_split.md) — KM_TAB_CACHE recovers 2313/2066/5089; residue = search convergence

## History / infra
- [Konclude study](project_km_konclude_study.md) — Konclude is LAZY (saturation decides ~95%, tableau on residue); docs/KONCLUDE-STUDY.md
- [HermiT trace](project_km_hermit_trace.md) — O(n) SAT tests (QuasiOrder) + cheap per-test search; docs/HERMIT-TRACE.md
- [IBEX env](project_km_ibex_env.md) — ssh dragon, pi-hohndor, batch; /ibex/scratch/hohndor/km/{engine,harness,gold,corpus}; km-dev = dev tree
- [Config union](project_km_config_union.md) — union of 48 configs = 572/587; 15 never-pass
- [Completeness gaps](project_km_completeness_gaps.md) — map of OWL2-DL gaps; fixed equiv-prop + disjunction ordering
- [Perf pivot + sweeps 5941-6016](project_km_perf_pivot.md) — KM complete since 2026-06-13; Lean certs sorry-free; sweep history in [project_km_sweep6016.md](project_km_sweep6016.md), [project_km_sweep5976.md](project_km_sweep5976.md), [project_km_sweep5941.md](project_km_sweep5941.md), [project_km_all_pass.md](project_km_all_pass.md)
- [SHIQ hypertableau plan](project_km_shiq_ht.md) — Ht ALC(H)→SHIQ; Phase 3 card merge landed
- [Full flag sweep](project_km_flag_sweep.md) — per-ont flag-toggle sweep infra under /ibex/.../km/qofull
