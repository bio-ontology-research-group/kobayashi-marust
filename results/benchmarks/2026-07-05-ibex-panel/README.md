# 2026-07-05 IBEX side-by-side panel (KM vs Konclude vs ELK vs HermiT)

Point-in-time snapshot. 584 ORE-2015 ontologies, one array task per ontology,
all four reasoners run SEQUENTIALLY on the SAME node (600 s / 56 GB ceiling),
recording actual wall_s + peak_mb + canonical signature vs Konclude gold.

- KM build: payg-strategy `b8ad70a` + konclude_ht module (fmt-only core diffs),
  built on IBEX (job 48048742, 1375 tests green). KM ran as the pure-Rust
  `km classify` multi-call binary (KM_BIN), 16 threads, KM_PAR_MEM_GB=44,
  KM_ABSORB=1, KM_ABSORB_PORTFOLIO=1, KM_TAB_RACE=1.
- Panel jobs: 48050937 (validation 0-2), 48051005 (0-583).
- Files: `panel_2026-07-05.txt` (aggregate), `kmvskonc_2026-07-05.txt`
  (per-ont gap lists), `cmp_res_2026-07-05.tgz` (raw per-ont jsonl).
- The earlier same-day run where KM had 584 errors (dead ~/moose venv on the
  old Python fallback path) is archived on IBEX as `cmp_res_2026-07-05_run1_kmfail`;
  its konclude/elk/hermit numbers are valid.

## Headline

| reasoner | ok/584 | gold MATCH | unsound | incomplete | wall med/avg (s) | peak med/avg (MB) |
|----------|--------|-----------|---------|------------|------------------|-------------------|
| konclude | 584 | 584 (gold) | - | - | 0.29 / 2.05 | 138 / 531 |
| elk      | 584 | 527 | - | - | 0.77 / - | 250 / - |
| hermit   | 559 | 553 | - | - | 1.75 / - | 716 / - |
| **km**   | **571** | **569** | **0** | **2** (10702: 23 subs, 12698: 84 subs) | 0.61 / 7.30 | **131** / 1008 |

km avg/med on the 571 both-ok onts; km peak median BEATS Konclude (-36.5 MB median delta).

## Gap to the beat-Konclude goal (per-ont, both-ok, gold-MATCH)

- WIN (faster AND less mem AND correct): 34
- wall delta bands (km - konclude): <0.5s: 357, 0.5-1s: 55, 1-5s: 79,
  5-30s: 64, 30-100s: 9, >100s: 7
- Memory tail: 102 onts with km peak > 2x konclude AND > 500 MB.
  Worst: 9635 (45.1 GB vs 57 MB), 12698 (38.8 GB), 6246 (33.9 GB),
  15491 (21.2 GB), 15672 (13.9 GB). The ~225 s walls on 9635/6246/9024/12141/
  15491 are the parallel-first-then-ST-retry pattern under the 44 GB watchdog.

## KM failures (13 timeouts; Konclude solves all)

10621, 12653, 14817, 15516*, 1603, 2669*, 3215, 541, 7499, 7914, 9540, 9663, 9724
(* = contested gold: 15516/2669 are the SWRL onts, genuinely inconsistent per
docs/CONTESTED-GOLD.md; Konclude's 0.2 s "ok" parses away the rules.)

## Incomplete (2, zero unsound)

- 10702 (wine/nominals): 23 missing, all `X ⊑ FrenchWine`-style.
- 12698: 84 missing (CHEBI-style ids), peak 38.8 GB - likely the ST-retry
  after parallel blowup produced a truncated/fallback result path.
