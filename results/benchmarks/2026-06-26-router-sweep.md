# ORE 2015 router sweep — 2026-06-26 (point-in-time snapshot)

Full-corpus sweep at **120 s** wall, **20 GB** memcap, on unimatrix01
(nodes 002–007, parallel-packed: `--cpus-per-task=8 --mem=22G`, KM_THREADS=8,
KM_PAR_MEM_GB=16). **Rough-but-fast** numbers (memory under node contention is
noisy; the ranking and recoveries are stable). Harness: `router_runone.py`
(per-ont `/proc`-poll peak over the whole process group, identical to the
authoritative `ore_runone.py`) + `router_sweep_par.sbatch` +
`fast_soundness.py`, all under `~/bench/ore_harness/` on unimatrix01.

Three **router modes** of the one `km classify` binary:
- **default** — production routing (all arms on; fallback mode, CB preferred,
  HT/QO/SHOQ answer only via the sound CERTIFY_ONLY arms or on CB failure).
- **cb** — CB family only (engine + elc + absorb); tableau/QO/SHOQ arms OFF
  (`KM_NO_HT_RACE`, `KM_NO_HT_QO_ROUTER`, `KM_NO_HT_SHOQ`).
- **ht** — tableau-preferred RACE (`KM_HT_MODE=race`; HT competes from t=0).

## Coverage + time/memory (ok-status onts)

| mode | ok | timeout | wall mean | wall median | peak mean | peak median | peak max |
|------|----|---------|-----------|-------------|-----------|-------------|----------|
| default | 560 | 30 | 6.5 s | 0.98 s | 662 MB | 107 MB | 16.4 GB |
| cb      | 556 | 34 | 6.1 s | 0.79 s | 458 MB | 75 MB  | 16.4 GB |
| ht race | 566 | 24 | 6.4 s | 0.97 s | 642 MB | 107 MB | 16.5 GB |

(592 onts total; the 5 with no `.owl`/no Konclude gold are excluded by the
runner. No memout at 120 s — the giants time out first.)

## Soundness / completeness vs gold (ok onts only; `fast_soundness.py`)

Oracles: **Konclude** (full) and **HermiT** (239-ont subset, the harder/expressive
onts where divergence matters). ELK is **not** a soundness oracle for non-EL onts
(it drops non-EL axioms; e.g. it cannot see 8941/10621 inconsistency), so it is
excluded from the soundness table. Contested gold (Konclude proven wrong —
15516, 2669, 8941, 13912, 10621 — see `docs/CONTESTED-GOLD.md` +
`results/contested-cores/`) is flagged `*` and adjudicated by HermiT.

| mode | vs Konclude (agree / unsound / incomplete) | vs HermiT (agree / unsound / incomplete / cons-mismatch) |
|------|--------------------------------------------|----------------------------------------------------------|
| default | 558 / **0** / 2 (12698, 10702) | 225 / **0** / 2 (10702, 13503) / 2 (8135, 5940) |
| cb      | 556 / **0** / **0**            | 223 / **0** / 1 (13503) / 2 (8135, 5940) |
| ht race | 561 / **0** / 5 (15098, 12009, 6817, 12698, 10702) | 228 / **0** / 3 / 2 |

**Headline: 0 unsound in every mode vs both Konclude and HermiT.** The soundness
property holds across the whole corpus.

## Routing conclusions

1. **CB is sound+complete on everything it solves** (cb: 0 unsound, 0 incomplete
   vs Konclude) and is the lightest (75 MB median). It is the correct default
   engine; route to it first.
2. **`ht` RACE mode is unsafe**: it solves the most (566) but the HT arm wins
   races on 3 onts (15098, 12009, 6817) where it is INCOMPLETE — it returns a
   strict subset of the gold subsumptions (the ALC+⊔ subset-blocking
   incompleteness). Racing HT from t=0 trades completeness for coverage, which
   violates the no-incomplete rule. **Keep fallback mode**, where HT answers only
   via the sound CERTIFY_ONLY QO/SHOQ arms (certify-or-defer) or after CB fails.
3. The `default` 2 incomplete (12698, 10702) are pre-existing (this snapshot's
   default column is the OLD binary, before the 7581 fix below); both are known
   hard onts (10702 = live ∀+⊔ disjunction family; 12698 = 84 missing subs, to
   investigate).

## Recovery landed this session: 7581 (gold-exact)

`ore_ont_7581` (Horn-ALCHQ, 498 724 clauses, 72 989 concepts) **timed out** in
the production route (regressed in sweep 7419). Traced via the Konclude-ported
QO/KPSet certify funnel: it deferred on **"4 residual inverse bridges
(composition not total)"**. Three gaps, all closed (faithful to Konclude; no new
algorithm):
- the qo arm composed only single-role-body bridges → added `KM_HT_QO_INVCHAIN`
  + `KM_HT_QO_INVONEWAY` (one-way + chain-consumed bridge composition, already
  ported in `compose_inverse`) so all 4 bridges compose ⇒ **0 residual**;
- the CERTIFY_ONLY router deferred without trying the clean global-forward
  certify → added `KM_HT_QO_GFCERT`: `qo_classify_global_fwd` returns `Some` ONLY
  when the forward closure is complete (card-split `res==0` or 0 residual
  bridges), sound+complete by construction, else defers;
- the fallback race gave the QO arm the full 225 s budget, so its **certified-at
  -20 s** answer was never harvested within the wall → the QO arm now uses the
  SHORT (SHOQ) budget like the other certify-or-defer arm.

Validated **GOLD-EXACT**: 565 317 subsumptions, 0 unsound, 0 incomplete,
consistent — identical to Konclude gold. Classifies in 35 s (ws) / 78 s
(unimatrix under load), 6.3 GB. 152 cargo tests pass.

### Validation sweep (job 7550, fixed binary, mode `defaultfix`, full corpus)

| | ok | recovered | regressed | vs Konclude unsound | vs Konclude incomplete | vs HermiT unsound |
|-|----|-----------|-----------|---------------------|------------------------|-------------------|
| defaultfix | 561 | **[7581]** | **[]** | **0** | 2 (10702, 12698 — both pre-existing) | **0** |

Exactly one recovery (7581), **zero regressions**, **zero new unsound, zero new
incomplete**. The 2 incomplete are byte-identical to the pre-fix default column,
so they are not introduced by this change. 152 cargo tests pass. The fix is the
production default (CERTIFY_ONLY arm, sound+complete-or-defer).

## Production-budget recheck (240 s) — true miss set

The 120 s sweep over-counts timeouts: many onts finish in 120–240 s. Re-running
the 29 default-mode 120 s-timeouts at the **production 240 s** budget (job 7580;
NB the sbatch appended all tasks to one file, so a few jsonl lines were
corrupted — the authoritative signal is the written `.sig.gz`):

**9 pass at 240 s, all GOLD-EXACT (0 unsound, 0 incomplete vs Konclude):**
868, 5303, 7409, 9024, 9635, 9674, 10689, 12141, 16462 (incl. three 14.8 M-subs
giants and the disjunction-family 5303 @ 238 subs). So they are budget artifacts,
not misses. (Speed note: 5303 — solved in ~5 s in a prior session — now takes
~225 s; a speed regression to investigate, correctness intact.)

⇒ production-budget coverage ≈ **570 ok** (561 @120 s + 9) and the **true
Konclude-solvable miss set is ~17** (excluding the 3 contested 2669/15516/10621
where Konclude's gold is wrong):

| class | onts | mechanism needed |
|-------|------|------------------|
| throughput giants (SRIQ/SHIF) | 7499, 7914, 9663, 9724, 14817 | **port #2**: Konclude per-creation-role ALL-concept extension + copy-on-conflict successors (inverse-∀ over-defer) |
| disjunction family (live ∀+⊔) | 541, 1603, 4669, 9540, 10860, 12653 | Konclude pseudo-model merge + small per-test completion graphs |
| CB memory/throughput blowups | 1194, 3215, 6212, 6246, 15491, 16444 | CB memory reduction / lazy saturation |

## Contention caveat — the packed sweep over-reports memory-bound timeouts

The fast parallel sweep packs ~6 onts/node with KM_THREADS=8–10. KM's parallel
path amplifies memory ([[project_km_threads_vs_algo]]), so memory-bound onts time
out under contention but classify within budget when run alone. Confirmed on ws
(single-ont, KM_THREADS=8): **6212 ok in 129 s, 15491 ok in 226 s** — both were
"timeouts" in the packed sweep. The amplifier is **thread count**, not just
co-tenancy: an exclusive recheck at **KM_THREADS=16** (job 7609) STILL timed out
15491, while **KM_THREADS=8** classifies it in 226 s — more threads = more
resident memory ([[project_km_threads_vs_algo]]). 6246 passes even at 16 threads
(109 s, 18.4 GB). So 6212 / 15491 / 6246 are **memory/thread artifacts, not
algorithmic misses**; the actionable lever is the routing/config one — downshift
threads (or route by clause count to fewer threads) for memory-bound onts so the
RSS watchdog does not tip them over budget. The only genuine CB-memout in this
class is **16444** (~20 GB). The true ALGORITHMIC miss set is therefore the
giants + disjunction family below, NOT the CB-blowup list.

**Thread-count experiment (exclusive, 240 s; job 7609 @16 thr vs 7628 @8 thr).**
At KM_THREADS=16 only 6246 recovers; at **KM_THREADS=8** both 6246 (218 s) and
**15491** (226 s, 15.2 GB) recover, and 6212 is ok @8 (129 s, ws) — fewer threads,
less resident memory. The giants and disjunction family do NOT recover at 8
threads (they need the deep ports). ⇒ routing memory-bound onts to ~8 threads
closes **6212 + 15491** (+2). Lowering the global default needs a full-corpus
no-regression check first (throughput giants may want 16 for speed); the safe form
is a structural router (clause-count / RSS-growth) or an adaptive half-thread retry
tier in `run_engine_adaptive` (today it jumps 16→1, no middle tier). Both are sound
(CB is sound+complete at any thread count); pending the validation sweep.

## Residual Konclude-solvable misses (the throughput giants + disjunction family)

Still timing out at 120 s, all converging on Konclude inverse-∀ handling
(**port #2**, `docs/LEVER-C-CACHE.md`) or the disjunction family's pseudo-model
/ expander cache:
- **giants** 9724, 7914, 9663, 14817, 7499 (SRIQ/SHIF, inverse + cardinality):
  the forward QO pass certifies the bulk but the inverse-∀ into shared fillers
  over-defers (9724: clean 2816 / affected 20320 of 23136). Needs the
  per-creation-role ALL-concept extension + copy-on-conflict successors.
- **disjunction family** 1603, 541, 9540, 12653, 10702, 5303: live ∀+⊔, needs
  Konclude's pseudo-model merge + small per-test completion graphs.
