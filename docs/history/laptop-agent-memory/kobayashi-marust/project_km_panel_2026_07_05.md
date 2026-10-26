---
name: project-km-panel-2026-07-05
description: "2026-07-05 IBEX 4-reasoner panel baseline - km 571/584 ok, 0 unsound, 2 incomplete; the definitive gap list for the beat-Konclude goal"
metadata: 
  node_type: memory
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

2026-07-05 IBEX same-node panel (600s/56GB, jobs 48048742 build + 48051005 array),
snapshot committed 4fcb2df at results/benchmarks/2026-07-05-ibex-panel/.
KM ran as the pure-Rust `km classify` (KM_BIN in reasoner_cmp.sbatch — the old
Python fallback is DEAD on IBEX, ~/moose/.venv deleted; always set KM_BIN).

Results: konclude 584 ok / elk 584 / hermit 559 / **km 571 ok, 13 timeout,
0 unsound, 2 incomplete** (10702 wine-nominals 23 missing subs; 12698 84 missing,
38.8GB peak — suspect parallel-blowup fallback path). km wall med 0.61s vs
konclude 0.29s (constant ~0.3s spawn overhead; 357/571 within 0.5s delta);
km peak med 131MB BEATS konclude 138MB but avg 1008 vs 531 (heavy tail:
102 onts >2x konclude mem; worst 9635=45GB, 6246=34GB, 15491=21GB — the
~225s walls are parallel-first-then-ST-retry under KM_PAR_MEM_GB=44).

13 timeouts: 10621 12653 14817 15516* 1603 2669* 3215 541 7499 7914 9540 9663
9724 (*contested SWRL gold). Goal levers by size: (1) 80 onts >5s slower —
algorithmic; (2) memory tail = parallel watchdog config + central blowup;
(3) 13 timeouts = disjunction/cardinality family [[project-km-konclude-number-port]]
+ r-Succ [[project-km-rsucc-gap]] + SWRL stage 2; (4) WIN count only 34 — the
0.3s overhead band must eventually close to beat Konclude on EVERY ont.
