# Card default-on confirmation (2026-07-05)

KM-only 584-ont IBEX sweep run with the **default** config — no `KM_HT_CARD`
or `KM_HT_CARD_RECOG` in the environment, exercising the new code defaults
(build 48080117 base binary, panel job 48076591; per-ont result files under
IBEX `cardef_res/`).

## Result

- **574 ok / 573 gold-MATCH / 1 DIFF (10702) / 0 MATCH→DIFF regressions.**
- Recovers, by default, the three cardinality timeouts: **1603 (21.6 s),
  9540 (21.0 s), 7499 (92.5 s)** — all 240 s timeouts at the 571-ok baseline.
- The single DIFF (10702) is the pre-existing nominal + transitive-role
  incompleteness, unchanged from baseline (sound, incomplete by 23).

This reproduces the explicit-env card panel (48067625: 573 MATCH) with no
environment set, confirming the default flip is behaviorally identical.

## Unsolved by default (10, was 13)

| ont | class | recoverable |
|-----|-------|-------------|
| 541 | functional + disjunction | `KM_HT_CARD_FN` recovers it (21 s gold-exact) but panel 48080229 found the flag net-negative (572 vs 573 MATCH; regresses 1016 to DIFF + 7581 to timeout) → kept gated OFF |
| 2669, 15516 | SWRL DL-safe rules | **opt-in `KM_HT_RULES`** (KM correctly inconsistent; contested gold — HermiT agrees) |
| 14817 | transitive role chains | needs Konclude role-automaton ∀-propagation |
| 10621, 12653 | datatype cardinality | needs concrete-domain oracle in HT |
| 3215 | large disjunctive EL-safe-RBox | hard |
| 7914, 9724 | heavy SRIQ number | HT unsound (shared-filler ∀); CB memory |
| 9663 | CB central 115 GB blowup | memory tail |

## Delta from baseline (polling panel, card off)

| metric | baseline (4793c20) | card default-on (7fa2358) |
|--------|--------------------|-----------|
| ok | 571 | 574 |
| gold-MATCH | 570 | 573 |
| DIFF | 1 (10702) | 1 (10702) |
| unsolved | 13 | 10 |
