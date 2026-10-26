---
name: project_km_sweep6016
description: "Sweep 6016 FINAL (datatypes+chaindom+Phase2 engine, ofn-dt/kobayashi-marust-p2): 545 ok/45 to/1 mo; vs gold 545/0/0/0 — FIRST FULLY CLEAN TABLE, datatypes included; 0 regressions, 2397+8737 recovered; nominal A/B 15/15 gold-agree (in flight); 3524 runaway fixed via KM_EMIT_CLAUSES"
metadata:
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

**Sweep 6016 (2026-06-12, res_dt_*.jsonl, ore_out_dt; binaries
~/bench/km/ofn-dt md5 5ce67c3d + kobayashi-marust-p2 md5 fe55244e):
545 ok / 45 timeout / 1 memout (591 records; 3524 none — see below).
VS KONCLUDE GOLD: 545 agree / 0 incomplete / 0 unsound / 0 both.**

- **THE FIRST FULLY CLEAN CORRECTNESS TABLE, NO EXCLUSIONS**: every
  completed ontology byte-equal to gold, datatypes included (6999 agrees).
  Config = chain-domain default + datatype axioms+oracle + Phase-2 nominal
  engine (inert without KM_NOMINALS).
- Zero status regressions vs sweep 5976; recoveries: 2397 and **8737 (the
  giant) timeout→ok** → net +2 ok.
- **3524 stdout-runaway recurred** (driver 195 GB RSS on node005, killed by
  verified PID mid-sweep): ROOT FIX = derived-clause echo now gated behind
  KM_EMIT_CLAUSES (engine main.rs; rust_context.py sets it — the only
  consumer). Future sweeps won't hit it; 3524 still needs its own run to
  see if it now completes (no gold either way).
- **Nominal A/B** (KM_NOMINALS=1, ~60 gold-comparable nominal onts,
  res_nom_ab.jsonl/ore_out_nom, unimatrix head, KM_THREADS=4 nice 15):
  in flight; at 28 onts: 15 ok ALL gold-agree, 0 disagreements, 13 timeouts
  (slow head node + nominal perf cost — cross-check vs base statuses when
  done; 10702-family are base timeouts anyway). This is the default-on gate.
- 10594 nominal-mode livelock fixed (announcement guard, 1ad0af6): 192 s,
  faster than Phase-1 engine, identical published output.

GOAL STATE: SROIQ calculus complete (all ALCHOIQ Table-3 rules), tested
(Example 3 + 6 nominal + 3 datatype probes, HermiT-verified), Lean-certified
(soundness all rules + ground-fragment completeness, sorry-free); datatypes
done and corpus-validated. See [[project_km_nominals_cb]],
[[project_km_datatypes]], [[project_km_sweep5976]].
