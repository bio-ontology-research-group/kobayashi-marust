# ORE-2015 km vs Konclude — in-process CB engine (safe, definer-gated)

Paired `km vs konclude` panel on IBEX after the in-process CB engine fast
path for small non-EL onts (commit `b2f58fd` on `payg-strategy`). Compares
to the in-process-elc morning baseline `../2026-07-06-inproc-elc/`.

Konclude numbers are shared from the same-era `cmp_res_inproc` run; km
numbers are the A/B pair below, both on the same IBEX nodes/config.

## The A/B (winning = faster AND lighter, `<=`, both solved; sound = gold MATCH)

| variant | both-solved | km faster | km lighter | **WIN (goal)** |
|---|---|---|---|---|
| in-process engine **OFF** | 576 | 218 | 425 | **218** |
| in-process engine **ON (safe)** | 576 | 244 | 423 | **243** |
| Δ | 0 | +26 | −2 | **+25** |

**+25 more ORE ontologies where km is provably faster AND lighter AND
sound/complete than Konclude, with zero solved-count regression.**

## What it does

For small non-EL ontologies the forked engine-worker `fork`/`exec` +
clause-JSON stdin round-trip dominates the wall on the near-tie band (km
already lighter than Konclude there, tying or narrowly losing on time).
`try_inproc_engine` runs `Reasoner::{new,saturate,subsumptions}` as a
library call instead — byte-identical output, minus the fork overhead.

## Why "safe" (the definer gate)

The first version (commit `8847b85`) budgeted-detached the in-process
worker on overrun. On the CB memory-blowup family (internal definer
disjunctions, e.g. `ore_ont_9635` → 45 GB) the lingering detached thread
fought the forked fallthrough for memory and **OOM-ed two previously-solved
onts** (9635, 12698): that A/B was 272 winning but only 574 solved (−2).

The fix gates the path on `Reasoner::has_internal_definer_disjunction()` —
the exact blow-up signature. Only bounded-memory onts saturate in-process,
so a worker still running at the budget cannot OOM the fallthrough; blow-up
and overrun onts take the forked adaptive/HT path unchanged (keeping HT
recovery for e.g. 5303). This restores **576 solved** while keeping +25 of
the win. Validated byte-identical on ws: 3260 (non-definer) 0.12s→0.02s;
9635 (definer) declines, falls through, solves 225s identical.

## Cumulative goal standing

- morning baseline (pre in-process): 213/576 winning
- + in-process elc (`../2026-07-06-inproc-elc/`): 318/576 (that panel's era)
- this A/B, same-era: OFF 218 → safe-ON **243** (+25 from the CB engine path)

The panel-to-panel absolute counts shift with node/load (single-rep,
near-tie band ±30); the controlled A/B here isolates this change's effect
at **+25 winning / 0 solved-regression**.
