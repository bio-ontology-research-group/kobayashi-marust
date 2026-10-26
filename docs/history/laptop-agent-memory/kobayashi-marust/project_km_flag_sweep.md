---
name: project_km_flag_sweep
description: 2026-06-24 full per-ont per-flag ORE sweep on IBEX (job 47760983) to crack the 21 timeouts
metadata: 
  node_type: memory
  type: project
  originSessionId: f75fe881-cb21-41f6-8110-ddbbedcc36b5
---

Goal: find which currently-default-OFF strategy flag cracks which of the ~21 KM
timeouts (router baseline = 561 ok / 21 timeout, see [[project_km_7581_qosat]]).
User-directed: per-ontology IBEX job, Konclude first then each flag toggled
individually, 600s/config, record pass/fail + time + mem.

**IBEX job 47760983** (submitted 2026-06-24). Layout under
`/ibex/scratch/hohndor/km/qofull/`: `qo_full_runone.sh` (per-ont driver, runs all
12 configs via harness `ore_runone.py`), `qo_full_sweep.sbatch`
(array 0-586%150, batch partition, 18 cpus/32G/3.5h), `ontlist.txt` (587 gold
onts), `res/<ont>.jsonl` (one row/config: status+wall_s+peak_mb+config+flags),
`out/<config>/km__<ont>.owl.sig.gz` (canon sigs), `qo_full_agg.py` (aggregator:
per-config panel + recovery matrix vs gold). Harness sources from scratchpad
copies on the laptop.

Fresh `km` built on IBEX from current payg-strategy HEAD (router present):
`KM_BIN=/ibex/scratch/hohndor/km/engine/target/release/km`,
`KM_ENGINE_BIN=.../kobayashi-marust` (standalone engine worker — DO NOT point
KM_ENGINE at the multi-call `km`, it needs the `engine` subcommand). IBEX engine
clone was STALE (no router); always rsync laptop engine/src + touch before build.

12 configs: konclude, km_base(control), km_qo_router(KM_HT_QO_ROUTER=1),
km_seq_order(KM_SEQ_ORDER=1), km_tab_race(KM_TAB_RACE=1 → engages caching
tableau), km_ht_race(KM_HT_MODE=race), km_ht_blockskip(+KM_HT_BLOCKSKIP),
km_ht_incr(+INCRBLOCK2+INCROBLIG), km_ht_eager(+EAGER+NEGTRIED), km_split
(KM_SPLIT=1), km_qo(KM_HT_QO=1), km_combo(router+seq_order+tab_race). KM_SEQ_ORDER
is AUTO by default (force with =1). HT-search levers only bite where the HT arm
runs; in race mode they can return incomplete on disjunction onts → aggregator
compares sigs to gold (match/incomplete/unsound), never trusts status=ok alone.

Aggregate when done: `ssh dragon 'module load python/3.11.0; python3
/ibex/scratch/hohndor/km/qofull/qo_full_agg.py'`.

**RESULT (job 47760983, ok/timeout — the agg correctness columns had a double-.owl
gold-path bug, fixed in-place):** konclude 587; km_qo_router & km_combo **570**
(+2 = 7581+16444, both gold-exact via probes); km_qo 569; km_base/seq_order/
tab_race/ht_race/ht_incr/ht_eager 568; km_split 561. So `KM_HT_QO_ROUTER` is the
ONLY lever that recovers throughput onts; the disjunction/HT-search flags crack
none of the 9 throughput timeouts.

**THROUGHPUT FAMILY DIAGNOSIS (2026-06-24, full trace+profile → docs/THROUGHPUT-
SATURATION.md).** The 9 are SRIQ/SHIF/SROIQ/SHOIN/SHI/SOIF(D) — all have S/R
(transitive/chains) + inverse-via-bridges; none transitivity-free. 9724 is pure
Horn-SHIF (disj=0) yet times out. Konclude clones at ~/Public/software/Konclude.
ROOT CAUSE: KM's QoSat defers `≤`(Eq-heads) + inverse to a per-concept / complete-
tableau path; fine when residue is a small tail (7581 kp_miss=0) but COLLAPSES
here — inverse pervasive (9724: 2.5M reversed edges, kp_miss=66M) makes 88% of
concepts insufficient → global pass never certifies → falls to ~23k per-concept
saturations → 299M edge pops → timeout. Transitivity is ALREADY encoded smartly
(`__trans__` P-concept ∀-propagation, raw R∘R⊑R dropped) — NOT the cause.
LANDED (gated, default off, sound): `KM_HT_QO_CARD` — Eq-heads mark anchor
INSUFFICIENT + continue (Konclude deferral) instead of bailing the whole pass;
critical-∀ records its node; per-node CLEAN split wired into qo_classify_kpset +
qo_classify_global_fwd (emit clean concepts iff residue empty). Measured 12% clean
on 9724 → residue too big without the real fix. REAL FIX (multi-session, Lean
re-cert, same class as 7581 QoSat): P1 backward-∀ inverse (no reversed-edge
materialisation), P2 in-pass cardinality bound+merge, P3 per-node emit + residue
verify. See [[project_km_throughput]] (prior diagnosis) — this REFINES it to the
exact mechanism. NOT solved this session; needs the global-saturation re-arch.

**SESSION 3 (2026-06-24, commits 090a273 + 9182ed3, docs Session-3 section).**
Built BOTH user-requested ports (gated, 131 tests pass): **port #2
`KM_HT_QO_INVCHAIN`** (compose purely-virtual inverse role away inside multi-role
chain bodies, drop bridge — composes 395 roles on 9724, 2 on 7914) + **port #1
`KM_HT_QO_RESIDUE`** (complete affected concepts on the already-built shared model:
one global completion to harvest candidate extras + per-subtree `A⊓¬B` verify via
checkpoint/rollback; `residue_tainted` defers any concept whose verify touches a
∀/cardinality insuff node; gated sound to pure-disjunction). Plus tunable
`KM_HT_QO_RES_MS`/`_DEPTH`, affected-concept forward-base emit, `KM_HT_QO_RESIDUE_
FORCE` diagnostic. **EMPIRICAL VERDICT: neither port solves the family alone.** The
dominant blocker is ∀-shared-filler pollution (`qo_insufficient`, apply_head
critical-ALL): 9724 = 34012/37251 nodes; 7914 only 173 nodes + 67 ⊔ but still sets
the flag. Isolated `km tableau` on a `KM_DUMP_TIN` TInput (no CB): 7914 fast QO arm
= **55 s / 512 MB** and correctly emits the 10509 clean concepts, but FORCE
(unsound) emits 190539 vs gold 141517 (~49k spurious from polluted affected
labels, phase1 sat=false). Complete HT classify (sound, non-shared fillers) on all
17680 concepts TIMES OUT at 150 s even w/ PAR=8+HORNFAST+WITREUSE (277 MB). Pincer:
lazy pass unsound (∀ pollution), complete pass too slow (per-concept SAT count);
no cheap prune for the over-approximation. THE lever = **Konclude lever C**: make
the single shared saturation sound for ∀ via completion-graph semantics
(non-shared / pairwise-blocked successors) instead of shared role-keyed fillers, so
`qo_insufficient` never fires and one pass classifies. = SHIQ-completion re-arch of
`saturate_global`/`ensure_filler`/`apply_head` (the project_km_shiq_ht Phase-3
work), larger than #1/#2, not yet built. To run the isolated arm: dump TInput via
`KM_DUMP_TIN=tin.json km classify <ont>` then `km tableau < tin.json` with
`KM_HT=1 KM_HT_FORCE=1 KM_HT_QO=1 ...` (KM_HT=1 is REQUIRED or it runs legacy
tableau).
