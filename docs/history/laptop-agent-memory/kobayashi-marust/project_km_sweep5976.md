---
name: project_km_sweep5976
description: "Sweep 5976 (KM_CHAIN_DOMAIN=1) FINAL: 543 ok/46 to/2 mo; vs gold 542 agree / 0 UNSOUND / 1 incomplete (6999 = the known DATATYPE gap, identical pre-flag) / 0 both — first clean correctness table within SROIQ-sans-datatypes; chain-domain landed DEFAULT ON (KM_NO_CHAIN_DOMAIN opts out); cost 2313+8737 ok->timeout"
metadata:
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

**Sweep 5976 (2026-06-12, KM_CHAIN_DOMAIN=1, res_chaindom_*.jsonl,
~/bench/ore_out_chaindom): 543 ok / 46 timeout / 2 memout (591 records).
Correctness vs Konclude gold: 542 agree / 0 unsound / 1 incomplete / 0 both.**

- **0 UNSOUND for the first time** — [[project_km_unsound_diagnosis]] 11745
  confirmed fixed at full scale (ok, unsat=1592, sig gold-equal).
- The 1 incomplete is **ore_ont_6999**, missing exactly 1 sub
  (`Distortion_Type_Affine`) — the known DATATYPE gap
  ([[project_km_completeness_gaps]]), byte-identical in the pre-flag config
  (old kmbatch sig also missing 1). NOT a chain-domain regression. Within
  SROIQ-minus-datatypes the table is **0 unsound + 0 incomplete**.
  (Sweep 5941's "0 incomplete" claim differed because that comparison used a
  different ok-set; 6999's gap is long-standing.)
- Regressions vs 5941 baseline (545 ok): ore_ont_2313 and **ore_ont_8737 (the
  recovered giant, ~206 s before)** go ok→timeout under the extra chain-domain
  clauses; +1 memout. Honest resource limits.
- **LANDED DEFAULT ON** (frontend/mod.rs): `KM_NO_CHAIN_DOMAIN` opts out.
  Rationale: completeness mandate + d3a0e1e precedent. The sweep validated
  exactly this config corpus-wide before the flip.
- Current laptop source state: default-on flip + nominal Phase 2 (Nom/Join/(*))
  in progress on branch payg-strategy — see [[project_km_nominals_cb]].
