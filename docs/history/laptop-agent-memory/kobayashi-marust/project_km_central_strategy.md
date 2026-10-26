---
name: project_km_central_strategy
description: "Central expansion strategy + closure sharing landed (KM 554->562 ok on ORE); the residual soundness gap it exposed"
metadata:
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-10, branch payg-strategy. Three engine/frontend wins landed to close
the ORE passrate gap to Konclude (587 ok). New baseline: **KM 562 ok / 25
timeout / 4 memout**, agree-vs-gold 549, incomplete 7, unsound 5,
both-disagree 1. (Was 554/34/3, agree 544 before this session.)

Commits (newest first):
- `89c761a` **central expansion strategy = default**. Successor contexts keyed
  by their pushed trigger set as *core* (Core rule `-> p`) instead of one
  empty-core context per function symbol with hypotheses (`p -> p`). Collapses
  the growing-hypothesis-conjunction blow-up (`Q1(x)∧...∧Qk(x) -> D(x)`) that
  caused disjunction/role-chain timeouts. `KM_NO_CENTRAL` restores per-`f`.
  +8 ok (recovers 11 incl. memouts 10781/6682), +5 agree.
- `9887115` **cross-context closure sharing** (`shared_closure` non-root +
  `shared_root_closure` root, `seed_worked_off`). Computes the facts+TBox
  closure once per ordering and seeds it into every context (8-15x measured
  dup). 0 sig diffs vs baseline (validated sweep 5421). `KM_NO_SHARE` disables.
- `e975b6a` **dead inverse-bridge pruning** (frontend). 0 correctness change.

**Soundness gap the user accepted ("Land central, track soundness gap")**: the
central strategy itself is subsumption-sound (the 6 clean new agreements prove
it). The both-disagree 0->1 and unsound 4->5 are from TWO newly-finishing onts
exposing KM's PRE-EXISTING unsat under-detection (NOT invented subsumptions):
- `13912`: KM finds 1 unsat class, gold 33 (also a HermiT-vs-Konclude
  gold-sanity disagreement, so gold itself suspect here).
- `11745`: KM 1178 unsat vs gold 1593.
Same bucket as the open per-class unsat misses ([[project_km_unsound_diagnosis]]):
7901 (datatype empty range), 8941 (ALC ∀), 15516/2669 (degenerate gold).

**Regressed to non-finishing under central** (passed before): `12141` memout,
`6423` timeout, `6934` timeout, `9024` memout. **Recovery: central->legacy
fallback in `owl_classify._run_engine_adaptive`** — first attempt = central
under RSS cap (KM_PAR_MEM_GB=18) AND wall cap (KM_CENTRAL_TIME_CAP, default
200s, set just above the 182s slowest central-OK ont); on oom/timeout/fail,
retry single-threaded with KM_NO_CENTRAL=1 (legacy per-f, proven complete,
classifies these in 1-90s). 9024/12141 recover via the mem watchdog (~90s);
6423/6934 (legacy 1-2s!) need the TIME cap to abort central early. Speed-bound
onts finish on attempt 1, never hit the fallback. Deployed
`~/bench/km/py/owl_classify.py` (backup `.bak.precentralretry`).

Remaining timeout modes central did NOT fix (still blow up): `5303` (message
cascade), `10702` (disjunctive worked-off explosion), `10860`, `1603`, `9540`.
Giants `8737`/`16744` still time out -- see [[project_km_giant_routing]] (sound
EL-routing relaxation landed `e59d7fa` but doesn't fire on them; needs
concept-level relevance).

**Fallback landed `8b8e3c9` (KM_CENTRAL_TIME_CAP default 190s + RSS watchdog).
Validated full sweep 5518: 562 ok / 27 timeout / 2 memout, soundness IMPROVED
to 552 agree / 6 incomplete / 4 unsound / 0 both-disagree** (7901 fix moved it
incomplete->agree; no new unsoundness). The fallback DETERMINISTICALLY recovers
9024/12141 (true >20GB OOM) and 6423/6934 (240s spinners) -> all 4 ok. But ok
stayed at 562 because 4 borderline onts (11311/11745/6682/7127) flipped ok->not:
these are MEMORY BLOWUPS in the PARALLEL central engine that the RSS watchdog
catches mid-blowup (peaks 18.5-20GB), then the slow single-threaded legacy
retry races the 240s wall. Their ok/timeout is parallel-nondeterminism noise at
the mem boundary, NOT caused by the fallback (same 18GB watchdog as the central
baseline). **Raising KM_PAR_MEM_GB 18->19 makes it WORSE** (verified job 5554:
11311/11745 -> 19.5GB/timeout, 6682 -> 20GB memout) because more headroom = more
parallel exploration before fallback = less wall left for legacy. So keep
KM_PAR_MEM_GB=18. Real fix for these = faster/lower-mem legacy or central not
blowing up = engine work. ORE ok-count is ~562 +/- 4 run-to-run on these
borderline onts.

Deployed binaries on unimatrix: `~/bench/km/kobayashi-marust-batch` (= central
default), backups `.bak.preshare` (sharing-only) and `.bak.preshare2`. Baseline
sigs for diffing: `~/bench/ore_out_kmbatch_base5391`. Central aggregator:
`~/bench/ore_harness/ore_aggregate_central.py` (reads res_kmcentral/ore_out_kmcentral).
