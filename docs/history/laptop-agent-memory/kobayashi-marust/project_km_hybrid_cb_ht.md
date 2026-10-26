---
name: project_km_hybrid_cb_ht
description: "Hybrid CB/HT main reasoner — HT fills CB's coverage gap; monotone-safe fallback design + head-to-head data"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-17 (user: "HT solves onts CB cannot; build a hybrid that picks the best
engine from the ontology; sweep each option, decide later"). Built the hybrid
CB/HT route into the main pipeline. Commit **5f166fd** on payg-strategy (local,
NOT pushed).

**Head-to-head (h2h_analyze.py over IBEX cmp2_res CB + sweep_ofn HT):** BOTH 429,
CB_ONLY 129, HT_ONLY **4**, NEITHER 22; union 562. HT_ONLY = **4604, 9635, 11460,
15491** — the central-blow-up / context-explosion onts CB times out on (task #52);
HT classifies them gold-clean. HT also FASTER on 45/429 both-solve (6246 252s->
0.01s, 868 79->9.8s). [[project_km_throughput]] [[project_km_central_strategy]]

**HT correctness RESOLVED (canon-faithful, engine/py/ht_check.py, job 47570686).**
The old flat-set loc() comparison was WRONG: gold sigs are ore_canon.canonicalize
output (transitive closure + SCC + is_internal). Comparing HT through the SAME
canon over 47 suspects + controls:
- HT is **SOUND** (unsound=0 everywhere — no wrong-positive subsumption). The old
  "3 unsound" were loc() slash-localname + _hasValue datatype-surrogate artifacts.
- Most "incomplete" were a runner bug: real classes named Q_Fever / _MGI:101757 /
  __adipocyte... wrongly filtered (is_internal must filter the INTERNAL name with
  the named_iri escape, then map to IRI — NOT filter the IRI). Fixed -> GOLD_CLEAN.
- HT **incomplete on a real subset** (6433, 8864, 12009, 5566, 7216, 8982, 6817,
  15098, 14312): the 5303 disjunction/multi-parent family (subset-⊆ blocking
  incomplete for ALC+⊔). NO structural rule separates HT-complete (15491, clean
  WITH disjunctions) from HT-incomplete (8982, incomplete WITH disjunctions) ->
  cannot predict completeness -> must NOT replace a CB answer with HT. [[project_km_5303_diagnosis]]
- 6 DIFF_consistency (13912/443/6720/7052/8941/15288) all gold-INCONSISTENT,
  caught upstream by the CB abox_inconsistent precheck (+datatype oracle) BEFORE
  any engine -> never reach HT in the real pipeline.

**Routing guard (general, NO ont ids):** HT routable iff cb_to_ht conversion is
lossless (dropped==0, fenced==[]) AND no inverse AND no nominals. ALCQ number
restrictions ARE routed (9635 number-ont gold-clean). Datatype/hasValue is opaque
to cb_to_ht (surrogate concepts, dropped stays 0) so HT is incomplete there
(5940/8135) — harmless because HT is only a CB-failure fallback. [[feedback_no_benchmark_hardcoding]]

**Design — monotone-safe hybrid** (owl_classify _spawn_ht + _race_cb_vs_ht,
KM_HT_RACE): CB is the Lean-certified engine, HT single-threaded on one reserved
core (KM_THREADS-1), niced.
- KM_HT_MODE=fallback (DEFAULT, safe): CB preferred whenever it finishes; HT used
  only on CB error / KM_HT_BUDGET_S (225s) timeout. CANNOT regress a CB-solved ont,
  only fills the coverage gap. Zero-regression by construction.
- KM_HT_MODE=race (speed): first valid finisher wins; risks taking HT-incomplete
  answer on a CB-fast ont (the sweep measures the cost).

**Build:** ht-port = payg-strategy + 3 files ONLY (hypertableau.rs new,
tableau.rs +53 KM_HT dispatch, cb_to_ht.py +45); CB engine core IDENTICAL. So
brought those 3 onto payg-strategy directly (gated, inert default). Builds clean
on IBEX $KM/engine (13.9s). tableau_cli.rs unchanged (KM_HT dispatch lives in
tableau.rs:3877). Smoke PASS: base 1420/33 MATCH; race 9635 MATCH (HT wins fast);
fallback(budget5) 9635 MATCH (HT fills) + 1420 MATCH (CB wins, HT ignored).

**SWEEP RESULT (587 onts, 240s/20GB, gold byte-clean; commit b007303):**
base **558**, fallback **562 (+4: 4604 9635 11460 15491, 0 regressions)**, race
559 (+3, -2). **DECISION: KM_HT_MODE=fallback is the new main hybrid** — monotone
guarantee held exactly. Race strictly worse (loses 11460: race takes HT only if
HT finishes before the wall, niced HT slowed by CB memory pressure misses it,
fallback's KM_HT_BUDGET_S gives the full window; regresses 868/8486 large-closure
onts = kill-CB-mid-serialise + canon under racer pressure trips wrapper; transient,
re-runs clean). FIXED a core-reservation bug: os.cpu_count() returns the whole
node on Slurm -> oversubscribed; now derives from configured KM_THREADS.

Commits on payg-strategy (LOCAL, not pushed): 5f166fd (HT route) + b007303
(results+fix). Build $KM/engine on IBEX (13.9s). Sweep driver hybrid.sbatch
(--export ARM=base|fallback|race), aggregator hyb_agg.py, results
$KM/hybrid/{arm}/res/.

DEPLOY: add KM_HT_RACE=1 (KM_HT_MODE=fallback default) + KM_TAB_BIN to prod env.
NOTE base here=558 (auto.sbatch: KM_ABSORB=1, DISJ_INT auto) vs deployed 564
(+ absorption portfolio); the +4 are central-blowup timeouts the portfolio
doesn't target (task #52 4604/11460) so compose additively. Confirmation sweep
under full portfolio config = the productionisation step (NOT yet run).
