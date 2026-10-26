---
name: project_km_all_pass
description: "GOAL: all 592 onts pass (no timeout/memout). 47-ont failset; CERT HYBRID recovers 8 incl 3524+15703 (no reasoner passes those); portfolio (3-way race) + partial certificates + KM_QUERIES residue landed (698a385..); pf sweep 6066 validating; remaining ~38 = closure-bomb CB work (ordered resolution)"
metadata:
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

**GOAL (2026-06-12): every benchmark ontology ok — no timeout, no memout.**
Baseline sweep 6016: 545 ok / 45 to / 1 mo (+3524 recordless) = 47 failures
(`~/bench/ore_jobs/failset.txt`, failchunk_*.txt).

**Failset anatomy** (cross-reasoner: sequoia ok on only 10/47; elk "ok" on
45 but sig-AGREES with gold on only 18 — the elk-agreeing are near-EL):
- ~17 onts hit the 18 GB parallel watchdog; ST-first experiment (res_st1_*):
  ZERO recoveries — these are real engine limits, not scheduling.
- 720 s experiment (res_t720_*): only 7775 (285 s) + 12698 (370 s) finish
  within 3x budget → the rest are exponential for the current engine.
- konclude itself fails 5 of the failset (1194 memout, 4669 to, 10860 err,
  15703/3524 no record).

**THE CERT HYBRID (landed 698a385, f-up commits same session):**
1. `KM_ELC_CERT=2` extended: skolem terms as PINNED vars (filler-node
   interpretation), at-most repairs by NODE MERGING (union-find + witness
   mirrors, equalities modulo repr), greedy disjointness-avoiding choices,
   per-(node,clause,disjunct) BANS with banned-aware chronological blame,
   dead-witness conflicts (blame at newly-dead nodes), refinement passes.
2. **PARTIAL certificates**: per-subject criterion → `unresolved` residue
   (elc exit 4, KM_ELC_RESIDUE_CAP=64); engine `KM_QUERIES=a,b,...`
   classifies only those; owl_classify merges.
3. **Portfolio** `KM_ELC_PORTFOLIO=1`: 3-way race (full adaptive engine vs
   certified elc vs partial+targeted-residue engine), first sound answer
   wins, losers killed (`_LIVE_ENGINES` registry + `_RACE_WON` event;
   elc output to temp file — pipes deadlock on giant answers).

**RESULTS so far**: certificate fully passes on 8 of the failset —
**3524 + 15703 (NO benchmarked reasoner passes these!)**, 15803, 4205,
6212, 6682, 7246, 7775 — all gold-superset-verified (missing=0; exact sig
equality via the pf sweep 6066, res_pf_*.jsonl / ore_out_pf, RUNNING —
binaries ofn-dt + kobayashi-marust-p3(md5 changes; has KM_QUERIES) +
elc-cert + deployed owl_classify; NOTE chunks 0-1 started before the last
redeploy).

**REMAINING ~38 after the sweep confirms:**
- elk-DISAGREEING (24: 10702, 9540, 1603, 12653, 5303, 541, 2669, 5107,
  15672, 9663, 7914, 15516, 14817, 10908, 7499, 6246, 9024, 9635, 11460,
  12141, 12698, 2313, 4604, 10621, 3215, 9724): genuine non-EL consequences;
  cert correctly refuses (⊥-conflicts) → need the DEEP CB work
  (ordered resolution / Sequoia ordering, Lean re-cert;
  see project_km_disjunction_blowup). 12698 at 370 s is the closest.
- elk-agreeing but uncertified (11016 family: 11016, 11291, 1340, 14450,
  16303, 16444, 3905, 6934, 4669, 10908?): closure-bomb onts where even
  1-query CB can't saturate (shared TBox closure dominates) and the model
  search doesn't converge (needs DPLL-grade search in the cert).
- 1194, 7581, 9724: cert times out within 100 s budget (portfolio gives full
  window — may flip in the sweep). 10860: memout (konclude errors on it).

**Tooling**: cert batch test = `/tmp/cert_batch.sh` on unimatrix (logs
/tmp/cert_batch*.log); failset experiments via
`ore_harness/ore_{st1,t720,km_pf}.sbatch`.
