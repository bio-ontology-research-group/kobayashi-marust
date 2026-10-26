---
name: project_rust_frontend
description: "Rust ofn normalisation frontend (KM) — built, validated, env-gated in owl_classify; benchmark in progress"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

Ported the Python OWL normalisation frontend (parse + moose SROIQ normalise +
augment + domain/range + collision-safe IRI registry) to Rust to kill the
45-100s Python parse+normalise on large ORE ontologies. Lives in the
`kobayashi-marust` repo on branch `payg-strategy`.

- New binary `ofn` (`engine/src/bin/ofn.rs` + `engine/src/frontend/*.rs`, ~2100
  lines); shared modules refactored into a lib (`kobayashi_marust`) so reasoner
  + frontend share the `json_io` serde types. `ofn <file.ofn>` emits
  `{clauses, iri_map, named, declared, el_rbox_safe}`.
- `owl_classify.py` is env-gated: `KM_RUST_FRONTEND=1` (+ `KM_OFN_BIN`) sources
  clauses/iri_map/named/el_rbox_safe from `ofn`; `is_el` + EL completion stay in
  Python (port them later — that's phase 2b "Rust EL completion", needed for
  completion-bound onts like ore_ont_7868 whose Python completion is >15min).
- **Validated:** 51/51 named-concept classification equality vs Python (incl. 8
  entailment-forcing discriminators for forall-intro / exact / negated-Self);
  identical 246221 clause count on real 22MB ore_ont_7868; owl_classify
  byte-identical both ways on ore_ont_394 (1433 subs) and 935 (110593, EL+chain).
  Speed: ofn 2.8s vs Python 13.65s on 7868 (ws). Harnesses:
  `engine/py/compare_frontends.py` (reasoner-free --canon structural) and
  `compare_classify.py` (engine, run on ws). Note the --canon check has
  skeleton-tie false-positives (5/43); classification equality is the real gate.
- Build/validate on `ws`, benchmark on unimatrix — see [[feedback_no_heavy_laptop]].

Verified coverage progression (payg-strategy, gold=Konclude 587):
- 5008 baseline: ok=516, unsound=14
- 5068 (chain routing + full_iri): ok=**534**, unsound 10, agree 508
- 5110 (full sweep, KM_RUST_FRONTEND=1): ok=**544**, timeout 27, memout 20,
  agree 519, incomplete 15, unsound 10, both-disagree 0, median wall 0.754s
  (was 1.149s). Net +10: Rust FE recovered ~13 timeouts but its higher memory
  (max peak 18.6GB vs 20GB cap) pushed ~3 onts to memout.
- Job 5098 targeted (57 size-bound): 12 recovered, ALL 12 gold-AGREE (0 unsound,
  0 incomplete) incl. 14.8M-subsumption giants 868/9674/10689.

Gap to 587 = 43: 27 timeout (completion-bound EL → Rust EL completion phase-2b;
CB-engine-bound NOT_EL → engine scaling) + 20 memout (FE memory tradeoff;
reduce ofn memory or raise memcap). 10 unsound are mostly gold-disagreement
(Konclude vs HermiT differ on 12 onts; only ore_ont_3978 genuine per
[[project_km_ore_rerun_cur]]). Related: [[project_km_el_routing]], [[project_km_sroiq_program]].
