# 2026-06-18 — KM CB+HT optimization ablation (full ORE-2015 corpus)

Point-in-time snapshot. **KM only** (CB engine + HT + elc), 587 gold ontologies
(giants included), one config per optimization toggled against `base`, to see
which levers help **globally**.

- **Params**: 240 s timeout, 18 GB watchdog (`KM_PAR_MEM_GB`), 8 threads, IBEX
  `km-rustport` build (HEAD `6207bae`).
- **Gold**: Konclude with the `ore_canon` Thing≡Nothing fix; comparison uses the
  **same `ore_canon.canonicalize(text,"json")`** the gold signatures were built
  with (SCC/equivalence + Thing/Nothing canonicalisation), on km's native JSON
  output. (A first pass using `--lines` + a naive localname split produced a
  spurious `unsound=56` artifact on ~46 onts; corrected here.)
- **Job**: IBEX array `47628106` (8 configs × 24 chunks).

## Panel (per standing rule: ok / gold-clean / unsound / incomplete / timeout + avg & median wall & peak-mem)

| config | n | ok | gold-clean | unsound | incomplete | timeout | wall mean | wall med | mem mean (MB) | mem med (MB) |
|---|---|---|---|---|---|---|---|---|---|---|
| base | 587 | 558 | 558 | 0 | 0 | 29 | 3.15 s | 0.22 s | 430 | 24 |
| absorb | 587 | 558 | 558 | 0 | 0 | 29 | 4.32 s | 0.23 s | 431 | 24.5 |
| elcport | 587 | 561 | 561 | 0 | 0 | 26 | 2.96 s | 0.32 s | 595 | 71 |
| tabrace | 587 | 558 | 558 | 0 | 0 | 29 | 2.93 s | 0.24 s | 425 | 25 |
| ht | 587 | 562 | 562 | 0 | 0 | 25 | 5.07 s | 0.23 s | 544 | 25 |
| **ht_emelim** | 587 | **566** | **565** | **0** | **1** | **21** | 6.52 s | 0.22 s | 582 | 26.5 |
| ht_contra | 587 | 562 | 562 | 0 | 0 | 25 | 4.95 s | 0.23 s | 544 | 25 |
| ALL | 587 | 561 | 561 | 0 | 0 | 26 | 2.98 s | 0.31 s | 603 | 73 |

`ht_emelim`'s 1 incomplete = ore_ont_5303 (the known incomplete-by-1 from EMELIM
dropping a negative ∃ consequence); it is **sound** (0 unsound), so monotone-safe.

Config flags:
- `base` = CB adaptive + auto-EL routing + auto-seqorder (no portfolios/races)
- `absorb` = `KM_ABSORB_PORTFOLIO` · `elcport` = `KM_ELC_PORTFOLIO` · `tabrace` = `KM_TAB_RACE`
- `ht` = `KM_HT_RACE` + `KM_HT_MODE=fallback` (monotone-safe) · `ht_emelim` = ht + `KM_HT_EMELIM` · `ht_contra` = ht + `KM_HT_CONTRA`
- `ALL` = absorb + elcport + tabrace + ht + emelim

## What helps, globally (gold-clean delta vs base)

| config | net | gains | losses |
|---|---|---|---|
| absorb | +0 | — | — |
| tabrace | +0 | — | — |
| ht | +4 | 11460, 15491, 4604, 9635 | — |
| ht_contra | +4 | 11460, 15491, 4604, 9635 | — |
| elcport | +3 | 11460, 15803, 4604, 6212, 7246 | 16744, 8737 (giants) |
| ALL | +3 | (= elcport) | 16744, 8737 |
| **ht_emelim** | **+7** | 11460, 12141, 15491, 4604, 541, 9024, 9635 | — |

**Union gold-clean across all configs: 568** (base 558 → +10 reachable by routing).

## Findings

1. **`ht_emelim` is the global winner: +7, no losses, no unsound, lowest timeouts
   (21).** Recovers the central-blowup cluster (11460/4604/9635/15491) *and* folds
   several disjunction-family onts gold-clean (12141/9024/541). Median time/mem
   essentially unchanged (0.22 s / 26.5 MB); only the *mean* wall rises (6.5 s)
   because the HT fallback arm spends budget on the hard tail.
2. **Blanket-`ALL` is *worse* than `ht_emelim` alone (561 vs 565)** — turning
   everything on drags in `elcport`, whose elc memory-race regresses two giants
   (16744, 8737). A **router beats blanket-on**: use `ht_emelim` everywhere, and
   `elcport` only for non-giant central onts it uniquely recovers (15803/6212/7246)
   → approaches the 568 union.
3. **`elcport` +5 unique central recoveries but −2 giants** ⇒ deploy behind a
   giant-exclusion guard, never globally.
4. **`absorb` and `tabrace` are now +0** — their historical gains are already
   subsumed by the current `base` (auto-seqorder + central strategy). Droppable.
5. **`KM_HT_CONTRA` is neutral** (+4, identical to plain `ht`): the contrapositive
   enrichment neither helps nor hurts at corpus scale — consistent with the
   measured finding that 5303-class blow-up is structural, not per-disjunction.
   Stays gated/default-off.
6. KM remains fast on the bulk: median wall 0.22–0.32 s, median peak 24–73 MB
   across all configs.

## Update — EMELIM completeness fix (commit `554fc87`)

The one incomplete above (5303 under `ht_emelim`) was EMELIM dropping the
excluded-middle of a complementary pair whose negated side drives a consequence
(`¬Q⊑∃hasComponentPart.Q17`), silently losing one subsumption. Fix: EMELIM keeps a
pair unfolded when a member both drives a consequence and is **not** independently
Horn-derivable (so the consequence would be lost by the drop). Re-swept `ht_emelim`
and `ALL` with the fix (faithful canon, job `47635072`):

| config | gold-clean | unsound | incomplete | timeout | wall mean | wall med | mem mean | mem med |
|---|---|---|---|---|---|---|---|---|
| base | 558 | 0 | 0 | 29 | 3.15 s | 0.22 s | 430 | 24 |
| **ht_emelim (fixed)** | **564** | **0** | **0** | **23** | 5.61 s | 0.23 s | 551 | 25 |
| ALL (fixed) | 561 | 0 | 0 | 26 | 7.02 s | 0.68 s | 605 | 65 |

`ht_emelim` delta vs base: **+6** (11460, 12141, 15491, 4604, 9024, 9635), 0 losses,
**0 incomplete corpus-wide**. The fix moves 5303 (incomplete→timeout) and 541
(clean-fold→timeout, its consequence side is not Horn-derivable) to honest
timeouts — one ont traded to remove all incompleteness. Union now 567.

## Deployable recommendation (post-fix)

`base + ht_emelim` = **564 gold-clean, 0 unsound, 0 incomplete, 23 timeout**,
monotone-safe and now **fully sound + complete** (no incomplete route). Add a
**giant-exclusion router for `elcport`** (+15803/6212/7246 without the −2 giant
regression) to chase the 567 union. Do **not** deploy blanket-`ALL`.

## Update — combined router wired + made default (commits `99a71d8`, `896e3be`)

The recommendation above is now implemented and the default. `classify()` runs a
**combined router**: when the elc-portfolio and HT-race arms are both on, HT races
against the inner (CB-adaptive vs certified-elc) portfolio rather than bare CB, so
one pass reaches the *union* of both recovery sets (fixing the mutual-exclusion that
made blanket-`ALL` lose ht_emelim's gains). A **giant-exclusion guard** (`>100 MB`)
keeps the 3 giants off the OOM-prone concurrent race.

Router sweep (job `47636078`, faithful canon):

| config | clean | unsound | incomplete | timeout | wall mean | wall med | mem mean | mem med |
|---|---|---|---|---|---|---|---|---|
| base | 558 | 0 | 0 | 29 | 3.15 s | 0.22 s | 430 | 24 |
| ht_emelim | 564 | 0 | 0 | 23 | 5.61 s | 0.23 s | 551 | 25 |
| **router** | **565** | **0** | **0** | **22** | 4.98 s | 0.36 s | 553 | 72 |

Router vs base: **+7** (`11460, 12141, 15491, 4604, 7246, 9024, 9635`), **0 losses**,
strict superset of `ht_emelim` (picks up `7246` via the giant-guarded elcport arm).
It lands at 565 vs the theoretical 567 union — `15803`/`6212` (elcport-only central
recoveries) do not survive the combined race; a residual, not a regression.

The router config was then made the **default** (opt-out via `KM_NO_ELC_PORTFOLIO` /
`KM_NO_HT_RACE` / `KM_NO_HT_EMELIM`; `ht_mode` already defaults to `fallback`). A
**no-env-flag confirmation sweep** (job `47636367`) reproduces the router exactly:

| config | clean | unsound | incomplete | timeout |
|---|---|---|---|---|
| **default (no flags)** | **565** | **0** | **0** | **22** |
| router (explicit flags) | 565 | 0 | 0 | 22 |

set-identical (+0/−0). **`km classify` now ships the +7 router out of the box,
sound + complete, monotone-safe.**
