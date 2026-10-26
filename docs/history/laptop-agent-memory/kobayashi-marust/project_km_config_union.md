---
name: project_km_config_union
description: KM passes 572/587 ORE with SOME deployed config; 15 never-pass (~13 vs correct gold); HT-emelim arm targets the disjunction-family subset
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-17. "How many ORE onts can KM pass with SOME config?" Answered by
aggregating gold-MATCH across all ~48 historical config dirs on unimatrix
(`~/bench/ore_out_*`, gold = `ore_out/konclude__*.sig.gz`; script
`/tmp/union_agg.py`, run ON unimatrix per no-heavy-laptop rule).

**UNION of gold-MATCH across all deployed configs: 572 / 587.**
Best single config: `ore_out_kmbatch` = 565. Then kmabsorb 555, kmpf/seqfull 554,
kmcentral 548, pf 546, dt 545.

**Never passed by ANY deployed config (15):** 7581, 2669, 15516, 7499, 3215,
5303, 9724, 7914, 9663, 10621, 1603, 14817, 15491, 9540, 10702.
- 2669 + 15516 are CONTESTED GOLD (genuinely inconsistent per HermiT; Konclude
  gold wrong) [[project_km_contested_gold]] — they "never pass" only vs a wrong
  oracle. True never-pass vs correct gold ≈ 13.
- 5303 / 10702 / 1603 / 9540 are the live-∀+⊔ disjunction family
  [[project_km_disjunction_blowup]] — NOT in any deployed config's union, but the
  new **KM_HT_EMELIM** arm folds them to HermiT model size (+14 MATCH in the HT
  panel) [[project_km_ht_search]]. So the union RISES once HT-emelim is counted —
  this is the gap the comprehensive single-node bigsweep measures.
- 9663 / 9724 / 15491 / 7581 / 7246-class = central core-growth / context
  explosion [[project_km_throughput]], genuinely hard.

**bigsweep gotcha (cost a full run):** the single-node comparison driver
`/ibex/scratch/hohndor/km-incr/bigsweep.py` builds the corpus path from GOLDSIG
keys that RETAIN `.owl` (gold files are `konclude__ore_ont_N.owl.sig.gz`). The
original `abspath = corpus/%s.owl % ont` produced a DOUBLE `.owl`
(`ore_ont_N.owl.owl`) → every reasoner errored; ht arm passed `N.owl` to
ht_runone (wants bare `N`) → no_owl. Job 47597201 ran the broken script and
produced 4696 all-error rows; because the driver is RESUMABLE this poisons reruns
(they skip "done" cells). Fix: `abspath = corpus/%s` (ont already has .owl) +
`ht id = ont.replace("ore_ont_","").replace(".owl","")`. ALWAYS validate one cell
per runner (BIGSWEEP_LIMIT=4) before the long run. Validated green 2026-06-17;
resubmitted as 47599034 (2-day, one exclusive node).
