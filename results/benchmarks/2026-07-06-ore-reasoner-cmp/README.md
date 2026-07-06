# ORE-2015 head-to-head: km vs Konclude (2026-07-06)

Same-node, sequential, directly-comparable wall/peak for every reasoner on each
ontology. IBEX Slurm job `48105343` (`reasoner_cmp.sbatch`, 584 onts, 600 s /
56 GB ceiling, `pi-hohndor`/`batch`). km = the shipping pipeline
(`km` orchestrator, auto-router on, `KM_ABSORB_PORTFOLIO`, `KM_TAB_RACE`). Gold =
Konclude 300 s/16 GB signature. `per_ont.csv` has the raw per-ont numbers;
`aggregate.txt` is the full breakdown.

## Headline

| axis | result |
|------|--------|
| **solved** | km 576/584, Konclude 584/584 (7 genuine km timeouts + 1 contested) |
| **sound + complete** | km **572 MATCH, 0 DIFF** excluding the 9 contested-gold onts — km is correct on every ontology it finishes |
| **median wall** | km 0.386 s vs Konclude 0.272 s → km **1.30× slower** (median) |
| **mean wall** | km 8.92 s vs Konclude 2.35 s (km tail-heavy) |
| **median peak** | km 109 MB vs Konclude 135 MB → km **0.63× (lighter)** |
| **faster than Konclude** | 214/576 both-solved |
| **lighter than Konclude** | 366/576 both-solved |
| **faster AND lighter (the goal)** | **213/576 (~37%)** |

## Reading of the goal ("faster + lighter + sound + complete on EVERY ont")

- **Correctness is met.** 0 disagreements with valid gold; every km failure is a
  timeout, never a wrong answer.
- **Memory is a narrow win** on the median (0.63×) and on 64 % of onts, but has a
  catastrophic tail: `5303 / 9540 / 9635 / 12698` peak ≈ **45 GB** vs Konclude
  100–450 MB (the live-disjunction family).
- **Speed is the dominant gap.** km is slower on 362/576 onts, median 1.30×. The
  worst tail: `6246 / 15491 / 12141 / 9024 / 9635 / 5303` take **225–251 s** where
  Konclude finishes in **< 1 s**. This confirms the reframe: the goal is dominated
  by the systematic per-ont speed gap on SOLVED onts, not the handful of timeouts.

## The 7 genuine unsolved (km timeout, Konclude ok)

`541, 3215, 7914, 9663, 9724, 12653, 14817` (plus `10621`, contested — Konclude's
gold is wrong there; km's unsat work is correct-but-expensive).

## Contested-gold exclusion

`2669, 15516, 10860, 10906, 12451, 13129, 10621, 8941, 13912` — Konclude's gold is
wrong or unparseable (SWRL/`DLSafeRule`, functional-datatype unsat, or the
`Thing≡Nothing` canon bug). See `docs/CONTESTED-GOLD.md`. km disagreeing with
Konclude on these is correct, so they are excluded from the soundness count.
