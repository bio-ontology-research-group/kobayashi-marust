---
name: project_km_qo_deadend
description: "QuasiOrderClassification (KM_HT_QO) port does NOT crack the disjunction family — proven by the qo-tally diagnostic; 5303 is 0/94 sufficient, others' global model won't even build."
metadata: 
  node_type: memory
  type: project
  originSessionId: 17d1eba9-eaa6-4268-97ae-40756c219352
---

2026-06-19: The QuasiOrderClassification (QO) port in `hypertableau.rs`
(`quasi_order_classify`, +1265 lines, gated `KM_HT_QO`, wired default-ON in
`orchestrate/race.rs` `spawn_ht`) was built to crack the live ∀+⊔ disjunction
family the way Konclude does: ONE non-branching global shared-node saturation
(disjunctions parked, common-consequence "harvest" through parked disjuncts),
then read sat/unsat + possible-subsumers off that single model, running a real
residue SAT test ONLY for "insufficient" concepts (those still anchoring open
parked disjunctions). The Konclude premise: ~95% of concepts are decided for
free, only a few need the expensive test.

**That premise is FALSE for this family.** Added `KM_HT_QO_TALLY` diagnostic
(counts dead/suff/insuff per ont without bailing on the first residue test).
Results (build on IBEX `/ibex/scratch/hohndor/km`, job 47644078):
- **5303**: global model builds, but `queries=94 dead=3 suff=0 insuff=91`,
  median **17** / max 18 open disjunctions per insufficient concept. EVERY
  concept needs a full branching residue SAT — zero QO leverage. The 22 global
  ⊤-disjunctions saturate every node, so no concept is ever "sufficient".
- **10702 / 1603 / 12653 / 541**: the non-branching global park-saturation
  itself does not finish in 120s (the ∃-chain / transitive blow-up the code
  comments at ~line 1090 already warn about). QO can't even build the shared
  model.

**QO recovers nothing new**: 9024/12141/541 already pass via `ht_emelim`
(the 565 baseline). The residue DFS `qo_branch_dfs` is naive chronological
backtracking (depth-64 cap, hit in 314ms on 5303 concept-1) — strictly WEAKER
than the `Ht::classify` it falls back to (which has restarts/learning/backjump).
The prior "residue hits the depth cap" note was a red herring: it bails because
the search is structurally hard, not because the cap is mistuned.

**Regression risk of default-ON QO**: for onts where the global saturation
never terminates in budget, default-ON QO burns the whole HT budget on a doomed
model BEFORE it can fall back to the `Ht::classify` that previously worked — so
an ont `ht_emelim` recovered via the HT arm could regress ok→timeout. HT is
fallback-only (runs only when CB fails), so the blast radius is the ~22-27 hard
onts, but the risk is real. Confirms [[project_km_5303_diagnosis]] and
[[project_km_family_diagnosis]]: this family needs HermiT-grade absorption +
model-based classification (major, coverage-only), not QO.

User decision 2026-06-19: run a full ORE validation sweep of QO-default-ON vs
the 565 baseline (`km classify`, 2 arms qo/noqo, job 47644343), THEN decide
keep-vs-gate-off; meanwhile consolidate 565 + document (this note). NB the IBEX
`ore_runone.py --reasoner km` drives `owl_classify.py`, NOT the Rust
`km classify` where QO lives — QO sweeps must call `km classify` directly
(see `qo_validate.sbatch`).

**VERDICT (sweep 47644343, 587 onts x 2 arms): gate QO OFF.** qo arm and noqo
arm differ on EXACTLY 2 onts: 9024 and 12141 both go GOLD_CLEAN (noqo) →
incomplete-by-623-subsumptions (qo). QO recovers 0, regresses 2, adds 0 new
unsound, no timeout change. So default-ON QO = strict -2. Gated OFF: `config.rs`
`ht_qo` now opt-IN (`KM_HT_QO` env), was opt-out (`KM_NO_HT_QO`). All QO code
(`quasi_order_classify`, `QoSat`, `KM_HT_QO_TALLY`) kept behind the flag, inert
by default; HT path reverts to validated `Ht::classify`. CAVEAT: the
`qo_validate.sbatch` naive-localname gold comparison over-counts absolute DIFFs
(reports 492/494 clean + "53 unsound" vs the true 565/0 — it does not replicate
ore_canon); only the qo-vs-noqo DELTA is trustworthy (identical comparison both
arms). For absolute correctness numbers use the ore_canon harness, not this
sweep.
