---
name: project_km_threads_vs_algo
description: "IBEX probe settling \"is Konclude faster due to C++/libboost threads?\" — NO, it's algorithm; + KM parallel-path memory amplification finding"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-15 IBEX thread-scaling probe (job 47545446, results/thread_probe.sbatch,
/ibex/scratch/hohndor/km/thr_res/). Ran Konclude `-w1` vs `-w8` and KM 1- vs
8-thread on 11 hard onts spanning all three KM failure modes.

**VERDICT — Konclude's edge is NOT threads/libboost, it is algorithm.**
Konclude `-w1` ≈ `-w8` on EVERY ont (1→8 threads buys a fraction of a second on
small onts, 0–15% on big ones; on 7581 `-w8` is *slower*). Konclude solves 5303
in 0.16s on ONE thread; KM times out at 200s on eight (~1250× gap, fully
algorithmic). The live-disjunction family (5303/1603/9024/12141/10702) is TINY
for Konclude (0.15–0.24s, ~120MB) — not hard, just hard *for saturation*.
Rust threads ≈ C++ threads (rayon work-stealing = TBB); real gap = tableau +
caching/backjumping + compact data structures (the latter is where Rust idiom
can cost clones → our interning/arena work).

**NEW LEVER — KM parallel path AMPLIFIES MEMORY catastrophically on hard onts.**
t1→t8 peak RSS: 1603 79MB→42GB, 5303 168MB→42GB, 9663 1.5GB→42GB, 11460
7.5GB→42GB (42GB = the 48GB memcap, i.e. OOM-killed/timeout). Single-thread
stays small (just slow); 8-thread blows to the cap. Work-stealing scheduler
launches multiple concurrently-exploding queries that each grab memory, and the
KM_PAR_MEM_GB=40 watchdog doesn't downshift before the cap. STRICT REGRESSION:
on any memory-bound ont we are worse parallel than serial. This hurts the
average (mean mem) the user cares about — see [[project_km_perf_pivot]] avg
framing. Fix candidates: (a) downshift the RSS watchdog faster / lower default;
(b) cap concurrent in-flight queries by estimated width; (c) serial-first for
onts flagged explosion-prone. NB control ont 1340 parallel is FINE (0.69 vs
1.73s, mem flat) — amplification is specific to exploding onts.

Probe also reconfirms: disjunction family small+easy → route to caching tableau
([[project_km_disjunction_split]] recovers 2313/2066/5089 already; needs
convergence for 5303/1603/9024/12141). Konclude binary on IBEX:
bench/reasoners/Konclude-v0.7.0-1138.../Binaries/Konclude, thread flag `-w N|AUTO`,
needs LD_LIBRARY_PATH=bench/reasoners/libs (bundled libpcre).
