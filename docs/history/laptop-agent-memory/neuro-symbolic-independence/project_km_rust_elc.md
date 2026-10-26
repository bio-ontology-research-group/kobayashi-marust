---
name: project_km_rust_elc
description: Rust EL++ completion (elc binary) + zero-copy ofn hand-off — recovers EL-completion-bound ORE timeouts; remaining EL onts are frontend-bound
metadata: 
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

Phase 2b of the KM coverage push (see [[project_rust_frontend]]): ported the
Python EL fast path to compiled Rust so the large EL ontologies that time out in
`moose.elpp.completion` classify under the 240s ORE budget. Branch
`payg-strategy`, `kobayashi-marust` repo.

- `engine/src/elcomplete.rs`: faithful port of `el_route.to_nf` (EL-membership
  router, fires only when every clause maps onto NF1-NF7) + the ELK worklist
  saturation. Names interned to u32; FxHash (rustc-hash algo, no dep) on all
  integer-keyed maps/sets; read-only `Idx` split from mutable `State` so the hot
  loop iterates index slices without per-item clones.
- `engine/src/bin/elc.rs`: reads `{"clauses":[...]}` stdin, emits
  `{subsumptions,inconsistent,dropped}`, exit 3 if not EL (caller falls back to
  context engine). Compiled twin of `el_route.py.__main__`.
- `ofn --meta <path>`: zero-copy hand-off — clauses-only to stdout (engine/elc
  stdin shape), side data {iri_map,named,declared,el_rbox_safe} to the meta file.
  `owl_classify` (when KM_RUST_EL set) reads only the small meta and streams the
  clause file straight into elc/engine; the clause set never enters Python (the
  3x JSON round-trip dominated wall on big onts). Default ofn output unchanged
  (byte-identical, verified on 7868: 246221 clauses).
- `owl_classify.py`: KM_RUST_EL gates elc + zero-copy. KM_ELC_BIN / KM_OFN_BIN
  point at the binaries. Validated: `engine/py/compare_elc.py` 15/15 differential
  vs Python el_route over a battery of every NF (chains, transitivity, k>2
  conjunction, multi-bottom, backward-bottom).

Deploy: build on ws (`~/km-frontend/kobayashi-marust`), relay binaries via laptop
to unimatrix `~/bench/km/{ofn,elc}` (ws can't scp unimatrix directly). See
[[feedback_no_heavy_laptop]].

Verified on unimatrix (240s/20GB budget, zero-copy pipeline):
- ore_ont_2828 (28MB): 54s, 415396 subs = gold. RECOVERS (was timeout).
- ore_ont_10750 (132MB): 226s; ore_ont_1012 (139MB): 235s. RECOVER (thin margin).
- ore_ont_15280 (159MB) 254s, 13482 (170MB) 270s, 1559 (375MB) >300s: STILL over
  budget. ore_ont_15059 (550MB): memout 17.7GB+.
- elc per se is fast (2828 saturation 67s->23.65s after FxHash+split). The
  remaining 4 EL onts are now FRONTEND-bound: flat (0 subs), so the 250-300s is
  the `ofn` parse/normalise/augment, which is superlinear on 150MB+ files. Next
  lever = optimise the Rust frontend (would also help the frontend-bound NOT_EL
  memouts 16744/8737/4205). 15059/16744 (550MB) are also memory-bound regardless.

**RESULT (full KM re-run, jobs 5147 + 5177-fix, KM_ENGINE_BIN=par-cur):
ok 544 -> 550 (+6), timeout 27->22, memout 20->19, error 0.** Per-ont diff vs
5110: 6 RECOVERED, 0 REGRESSED. All 6 are EL completion-bound timeouts now ok &
gold-agreeing (agree 519->525, incomplete still 15, unsound still 10 — no new
unsound/incomplete): ore_ont_2828, 10750, 1012, 13482, 15280, **1559** (375MB,
1.73M subs). On the faster compute nodes (node002-007) 13482/15280/1559 came in
under 240s even though my login-node test showed 254-300s+. Median wall
0.754->0.583s, median peak (common) 20.55->19.1MB. Only EL ont still failing:
ore_ont_15059 (550MB, memout, frontend-bound).

BUG FOUND+FIXED mid-run: zero-copy sets clauses=None, but the routing did
`elif el_route.is_el(clauses) and rbox_safe` — Python evals is_el(None) first,
crashing to_nf on every NON-EL ont (RBox not EL-safe). Regressed 146 onts to
error in job 5147. Fix: when KM_RUST_EL, only attempt elc (if rbox_safe) else
straight to engine; Python el_route branch only in non-rust-el mode. Re-ran the
146 (job 5177, errchunk_*, res_kmelc_fix*.jsonl which sort-overwrite the bad
records). Aggregate: ore_aggregate_kmelc.py (ore_out_kmelc, res_kmelc_*.jsonl).

Gap to konclude 587 now 37 (22 timeout + 19 memout). Next lever = optimise the
Rust ofn frontend (the remaining big EL onts + several NOT_EL memouts are
frontend parse/normalise/augment-bound, superlinear on 150MB+ files).
