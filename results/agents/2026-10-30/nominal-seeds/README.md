# Nominal seeds: object guard for the native bridge (2026-10-30)

Agent `nominal-seeds`, branch `fix/v155-nominal-seeds` off development/v1.5.5
(f41b1af4). Change and argument: docs/NOMINALS-CB.md, "Object guard for the
native bridge (2026-10-30)"; Lean: lean/ContextCalculus/ObjectGuardRestriction.lean.

Binaries (scratch `.work/agent-scratch/nominal-seeds/`, not committed):
`km.base` = f41b1af4 (sha256 9626fc74…), `km.final` = 38173913 minus a
comment-only edit (sha256 f4e3bffc…), `cargo build --release`, workstation
under load 50 to 110.

Files
- `seeds-final-auto.tsv`: gen_nomdata.py --no-inverse 2000-2399, automatic
  route, 60 s, 3 workers, HermiT gold (nominal-coverage `diff_run.py`).
  366 ok / 34 timeout / 0 wrong (base, nominal-coverage
  `seeds-reverted-head-auto.tsv`: 275 / 125 / 0). No ok answer lost.
- `remaining-33.tsv` + m2296: remaining timeouts with the bridge's defer
  reason under the guard (`g3-defer.tsv`: forced `ht_bridge` with
  `KM_BRIDGE_OBJECT_GUARD=1`, all 125).
- `fresh3-{base,final}.tsv`: seeds 7000-7199, 60 s: 142/58/0 -> 181/19/0.
- `rules2-*`, `sorts2-*`: rule probes (7 ok, 8 refused, identical) and sorts
  fixtures (33/33 ok on auto, nominals, certified_nominals), both binaries.
- `r3f-*.tsv`: R3 motif sets, automatic route, km.final: tpl 1999 ok /
  1 timeout, tpl2 1000 ok, rand (partial, 3115 of 4000 at 10 s under load)
  6 wrong, all six also wrong on km.base (r1536, r1866, r2408, r2564, r3777,
  r1600 known). These sets have no data property, so the guard cannot apply.
- `times-{base,final}.tsv`: 112 nominal ORE inputs of the paired design half,
  automatic route, 300 s, two streams side by side (`ore_time.sh`):
  both answer 108, signatures identical, sum 830.5 vs 831.3 s, mean ratio
  0.966, median 0.985.
- `og-auto.tsv`, `tools/objguard.py`, `tools/kmog.sh`: the yield experiment
  that preceded the code (source-level rewrite on the 125, km fixm4): 77 ok,
  48 timeout, 0 wrong.
- `bridge_merge_min.ofn` (+ HermiT json): pre-existing bridge wrong answer
  (misses Q1 ⊑ A on ht_bridge and auto at f41b1af4), found while testing a
  withdrawn repeated-assertion change; `tools/minbridge.py` reduced it.
- `m2000-hyper-product.txt`: KM_TRACE_HYPER_PRODUCT on the 2-axiom m2000
  reduction (CB ground-context joins of about 9 M combinations per Hyper).
