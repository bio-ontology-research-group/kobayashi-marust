---
name: project_km_absorption
description: "Absorption portfolio (KM_ABSORB_PORTFOLIO) DEPLOYED+validated sweep 6524: 545->554 gold-clean (+10/-1). 6246 NOT plain-probe recoverable (premise FALSIFIED on IBEX: 6246-plain OOMs/times out in every config on current binaries) = genuine timeout; task #40 closed; work-probe edit reverted. No easy +1 left; gap to Konclude ~33 all hard."
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-14, branch `disjunction-split`. Session goal: close the ORE gap to
Konclude (587) staying sound+complete. Did Tier 1 (tableau search heuristics)
then Tier 2 (frontend absorption). Tier 2 is the win.

## Tier 2 — frontend absorption (THE WIN), commit f706521
Polarity-gated definitional clausification (Plaisted-Greenbaum) in
`engine/src/frontend/normalise.rs`, gated `KM_ABSORB` (default OFF). Extends the
existing polarity pre-pass to And/Or/Not definers: emit `Q -> C` only if C occurs
positively, `C -> Q` only if negatively; unseen (e.g. ABox) -> both (conservative).
Kills the unguarded excluded-middle `⊤ -> Q ∨ A` for every reified negation that
never sits on a subclass LHS (the disjointness idiom `X ⊑ ¬A`), and turns an LHS
disjunction into Horn. **Why it's sound+complete for classification:** synthetic
definers are never query targets (only named concepts are queried), so their
polarities are fixed by the ontology.

**Sweep 6304 (KM_ABSORB=1, tableau race off) vs 545 baseline (6274): 555 ok / 34
timeout / 1 memout, gold table 0 unsound / 0 incomplete / 0 both.** 11 recoveries:
1340, 3905, 14450 (fully de-disjuncted: 104/106/106 -> 0 disj heads), 12698, 16303,
**16444 (the long-standing memout)**, 2397, 4205, 6212, 7775, **8737 (a giant)**.
**1 regression: ore_ont_6246** 0.35s/78MB -> 18.5GB OOM/timeout — dropping the
PG-redundant AND def directions (`Q->A,Q->B` for abstract⊓endurant etc.) on a
DOLCE covering+disjointness TBox perturbs the CB engine into a blow-up. Net +10.

**NOT yet default-on / deployed** because of the 6246 cliff (and unknown risk on
non-corpus onts). Options to capture safely: (a) absorbed/plain PORTFOLIO race
(first sound finisher wins -> +11/-0 = 556, both verdict-equal) — cleanest, ~2x
frontend+engine; (b) fix the 6246 blow-up (diagnose why dropping redundant AND
def clauses explodes the engine — likely routing/context perturbation, the 39
dropped clauses are 38 (1,1) AND-def + 1 (0,2) Not excluded-middle); (c) just
default-on accepting -1. Deployed artifacts on unimatrix: `~/bench/km/ofn-absorb`,
`~/bench/ore_harness/ore_km_absorb.sbatch`, results `res_kmabsorb_*.jsonl` +
`ore_out_kmabsorb/`. New ofn built at `~/km-build/engine/target/release/ofn`.

## Portfolio DEPLOYED + validated — sweep 6524 (the chosen deployment, +9 net)
User chose option (a) absorbed/plain portfolio. Implemented `KM_ABSORB_PORTFOLIO`
in `owl_classify.py` (`_race_absorbed_plain` + `_ofn_clauses_file`), run
**SEQUENTIALLY** not concurrently: the concurrent version blew the 20 GB memcap (7
memouts, cancelled sweep 6338 — legit absorbed runs already hit ~18 GB so a second
engine alongside is fatal). Sequential design: probe the PLAIN clause set first for
`KM_ABSORB_PROBE_S` (8 s) at full cores; if it finishes, return; else discard and
run the ABSORBED set with the full budget. One engine resident at a time.

**Sweep 6524 vs 545 baseline: 554 ok / 34 timeout / 2 memout; gold 554 agree / 0
unsound / 0 incomplete / 0 both (FULLY CLEAN).** +10 recovered (1340, 2397, 3905,
4205, 6212, 7775, 12698, 14450, 16303, 16444); **-1 regressed: 6246**. Net +9
(545->554), NOT the +11/-0 (556) target. The 2 memouts (10860, 15491) were already
not-ok in baseline (not regressions).

**Why 6246 still missed:** the probe is WALL-CLOCK so node-load sensitive. 6246
plain is ~0.35 s on an idle compute node (node004) but pathologically slow under
contention / on the head node. In 6524 it landed on node007, the 8 s probe missed,
the absorbed path ran and blew to 18.6 GB -> SIGKILL/timeout. NEXT FIX = a cheap
STATIC plain/absorbed router (decide from the clause set up front, e.g. detect the
DOLCE covering+disjointness signature, route 6246-likes to plain) instead of a
timed race; widening KM_ABSORB_PROBE_S is the crude alternative but it delays the
genuinely absorbed-only onts (16444 was 78 s absorbed). Deployed: `~/bench/km/py/
owl_classify.py` (portfolio), `~/bench/km/ofn-absorb`, sbatch `ore_km_pf.sbatch`
(KM_ABSORB=1 + KM_ABSORB_PORTFOLIO=1), results `res_kmpf_*.jsonl` + `ore_out_kmpf/`.
Committed: owl_classify.py portfolio code on `disjunction-split`.

## Tier 1 — tableau VSIDS+phase+restart (gated infra, NOT a coverage win), commit 926ea64
`KM_TAB_VSIDS` / `KM_TAB_PHASE` / `KM_TAB_RESTART` on the cache tableau's per-node
DPLL. Pure search-order, no Lean. 2313 byte-identical under all combos. Reduces
distinct seeds ~26% + 5x more no-goods on 5303 but recovers 0 ORE timeouts: only 7
of 45 timeouts are cache-eligible (ALCH, ≤20k cl) and all are walled by the
**∃-chain seed-space explosion** (depth ~483, ~31k incomparable successor labels),
not per-node propositional search. Per-seed restart is the wrong granularity
(restarts a node's DPLL, not the chain). The other 38 timeouts are giants + number/
nominal onts outside the cache fragment. Lesson: the cache tableau is an ALCH
specialist; the coverage gap lives mostly OUTSIDE its fragment -> the CB engine
(absorption + future ordered resolution) is the high-leverage place.

## Race exonerated (commit fc627c8 hardens it anyway)
Faithful same-node/same-binary A/B: KM_TAB_RACE 0 vs 1 identical (541: 240.1 vs
240.0). The "18 ok->timeout" was vs the STALE 564 baseline (CLAUDE.md); the real
recent baseline is **545** (Jun 12-13 correctness commits: chain-domain default-on
cost 2313+8737, datatypes, cardinality — see [[project_km_sweep6016]]). Hardened
race = engine-first + lazy/niced tableau (KM_TAB_RACE_DELAY=30, nice 19).

## 6246 IS NOT PLAIN-PROBE RECOVERABLE — premise falsified (2026-06-14, IBEX)
DEFINITIVELY MEASURED on IBEX ([[feedback_prefer_ibex]], unimatrix was saturated
by array 6531): 6246-PLAIN (KM_ABSORB=0, **636 clauses**, generated by both the
deployed `ofn-absorb` and a fresh c91a813 `ofn`) does **NOT** classify quickly on
EITHER the deployed `kobayashi-marust-batch` OR a fresh c91a813 build, in ANY
config tried — 16-thread central = **OOM 23 GB / ~1 min**; legacy 1-thread
no-central = **timeout 200 s**; central-1-thread / default / KM_CHAIN_DOMAIN=0
variants = **all timeout 70 s** (jobs 47513966, 47514038, 47514085). So the
CHANGELOG/earlier "6246-plain = 0.35 s / 78 MB" is **NOT reproducible** on the
current binary — it must have been a much older engine or a different measurement.
**Consequence:** the absorption-portfolio plain probe (wall-clock OR the proposed
work-based / static router) **cannot recover 6246** — there is no fast plain run to
catch. 6246 is a GENUINE timeout in the 554 set, not a node-variance near-miss; the
intended target was always +9/556 fiction, real is **554**. Task #40 CLOSED
not-viable. A work-based-probe edit to `_race_absorbed_plain` was built, deployed,
measured, and **REVERTED everywhere** (it could not help 6246 and its raised 30 s
wall ceiling risked regressing the +10 absorbed family). Deployed owl_classify.py
restored to the 554-clean version (`.bak.workprobe` backup on unimatrix).

NB this also flags a possible **branch-engine regression**: the c91a813
(disjunction-split) engine OOMs 6246-plain under central just like km-batch — when
the branch engine is eventually deployed, re-check it does not regress onts that
km-batch handles.

## NEXT
The wiring-the-tableau-race and 6246 "easy +1"s both EVAPORATED under measurement
this session: (a) the Dir C cache path's wins (2313/2066/5089) are ALREADY ok via
CB in the 554 sweep, so KM_TAB_RACE recovers 0 NET today; (b) 6246 plain is not
fast (above). So there is **no easy +1** on the board. The gap to Konclude (~33,
587 vs 554) is all genuinely hard: the live-disjunction family (5303/1603/12141 —
cache-tableau OSCILLATES, needs convergence control [[project_km_disjunction_split]]),
out-of-fragment number/nominal disjunction (10702/9540/10860), context explosion
(6682/7499/7914), and throughput-bound big-file/giant onts (1194/7246/8737...).
CB-side ordered resolution is REFUTED for the covering-disjunction subfamily
([[project_km_disjunction_blowup]]). Realistic next lever = cache-tableau
convergence heuristic for the in-fragment 5303 subfamily (sound, no Lean re-cert),
but it is research-grade and has resisted 5+ techniques.
