# Bridge nominal merges (2026-10-30/31)

Agent `bridge-nominal-merge`, branch `fix/v155-bridge-nominal-merge`.
Defects, fixes and exactness arguments: docs/HYBRID-CB-HT.md section 10.

## Binaries (scratch `.work/agent-scratch/bridge-nominal-merge/`, not committed)

- `km.before`: development/v1.5.5 at 0e1bd99a, `cargo build --release`,
  sha256 c5c6bbe2...dbcc.
- `km.after`: this branch merged with 0e1bd99a (merge commit 227e2951 plus
  the four fix/test/doc commits), sha256 21c97526...e834e.
- Oracle: HermiT 1.4.3.456 (`.work/agent-assets/2026-10-28-scratch/oracle`).
- Konclude 0.7.0-1138 (`~/konclude-build/Release/Konclude classification`):
  `konclude/` holds its outputs; it misses `Q1 <= A` on bridge_merge_min and
  r2730 and does not finish r3086 within 60 s.

Workstation under load 70 to 140 on 56 cores during all runs.

## Files

- `gen_merge.py SEED OUT [--no-inverse]`: seeds around the pattern
  (nominal subsumptions between enumerations, enumeration assertions,
  functional and inverse-functional roles forcing merges, role assertions
  among merged individuals, universal/existential restrictions on them,
  query classes `Qi = {o}` / `Qi <= {o}`), no repeated axiom. Seeds 0 to
  1999 (1000 to 1499 and 0 to 499 with inverse roles).
- `gen-{before,after}.tsv`: those 2,000 seeds, routes `ht_bridge` and auto,
  30 s, `diff_run.py` of r3-unannounced. Before 1,751 ok / 22 WRONG / 227
  ERR (bridge declined) on ht_bridge and 1,934 / 22 / 44 TIMEOUT on auto;
  after 1,769 / 0 / 231 and 1,956 / 0 / 44. Changes: 39 WRONG to ok, 4 WRONG
  to declined (g545, g789, g1344, g1551), g789 auto WRONG to TIMEOUT, one
  timeout to ok.
- `r3-{tpl,tpl2,seeds}-{before,after}.tsv`: R3 motif sets (tpl, tpl2 20 s;
  random seeds 10 s), both routes. tpl 1,929 / 71 declined and tpl2 968 / 32
  declined on the bridge, identical; 0 wrong before and after. Random seeds:
  bridge 3,133 ok / 7 WRONG / 860 ERR before, 3,134 / 0 / 866 after; auto
  3,554 / 7 / 439 before, 3,558 / 0 / 442 after. Five formerly correct bridge
  answers now decline (r1164, r281, r947, r2627, r2970; stop inside
  `merge_individual_node_into`), see the doc section. `r3recheck-after.tsv`:
  the automatic route on those at 120 s.
- `alc/`: the 2026-10-29 bridge seed sets (700 ALCHIQ seeds, fresh 300 from
  `gen_alc.py` 1000-1299), `eval.py` of cb-inverse-top, 60 s: identical
  counts before and after (auto: 694 ok / 1 WRONG (621) / 3 TIMEOUT and 295 /
  2 WRONG (1014, 1022) / 3; bridge: 654 ok / 43 DECLINE / 1 TIMEOUT and 279 /
  18 / 3). The three automatic-route wrong answers are missed
  inconsistencies on 0e1bd99a; the nominal-seeds binary (38173913) answers all three correctly
  (`counts-base` in scratch), so they come from a change between 38173913
  and 0e1bd99a, not from this branch.
- `times-{before,after}.tsv`: 112 nominal ORE inputs of the paired design
  half (`r3-unannounced/ore-design-nominal.txt`), automatic route, 300 s,
  both streams side by side (`r3-unannounced/ore_time.sh`). 106 answered by
  both, all signatures identical; sum 1,132.5 s before, 1,009.8 s after;
  mean ratio 1.011, median 0.979. ore_ont_699 answered before in 295 s and
  timed out after; rerun at 900 s: identical output, 450 s before, 350 s
  after.
- `tools/`: `chain2.sh` (the whole before/after chain), `r3sets.sh`,
  `alc.sh`.

## Reproduce

Generate seeds with `gen_merge.py` into the scratch `seeds/`, then
`tools/chain2.sh` (paths are absolute to this workstation).
