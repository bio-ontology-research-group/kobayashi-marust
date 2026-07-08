# 2026-07-08 KM_HT_BRIDGE A/B panel (IBEX jobs 48395663 bridge-on / 48398378 control)

584-ontology ORE panel, same-era Konclude re-measure, 240s timeout.
Tree state: payg-strategy 7a01372 (bridge complete-or-defer: unrestored-advance
poison + early-bail; binaries built by job 48395021).

## Headline (control = production config, bridge OFF)
- km 576/584 ok; gold: 1158 MATCH, 2 DIFF (= contested 2669/15516, km right
  per docs/CONTESTED-GOLD.md), 8 NOSIG (the timeouts). Sound + complete on
  every solved ontology.
- vs Konclude on the 576 solved-by-both: wall avg/med 5.86/0.21 s vs
  1.84/0.25 s; peak mem med 33 MB vs 135 MB; km faster+lighter on 356/576
  (62%). km now wins BOTH medians.
- open set (8): 541 3215 7914 9663 12653 14817 10621 9724
  (9635 + 7499 now solve at baseline; 10621/9724 are the current tail).

## Bridge-on delta (KM_HT_BRIDGE=1)
- exactly ONE status flip vs control: ore_ont_7581 ok -> timeout (the bridge
  arm's defer overhead on a near-limit ontology). No closures: 12653's
  067aaa4-era closure is traded back because its probes take unrestored
  advances and the poisoned classification defers (10s early-bail).
- win-rate unchanged (358/575 vs 356/576).

## Recommendation
Keep KM_HT_BRIDGE OFF in production until per-node COW localization lands
(un-defers 12653's probes and removes the poison bail on the disjunction
family); the wiring itself is validated (defers are cheap and sound).

## At-most resume port (371f38f, KM_HT_ATMOST_REST, same day)
- suite 1407/1407 with the flag ON (dev-tree job 48398448); bridge probe A/B
  on 3215/541/12653: identical times both modes - the poison bail fires
  before the at-most machinery is exercised, so the rest port's throughput
  value is gated behind the same per-node COW work.
