# Checkers-on suite summary

Inputs: 1781. Off-mode answers against cached HermiT gold: {'ok': 491}.

## Mode `on`

| outcome | runs |
|---|---:|
| accepted | 34 |
| rejected | 231 |
| cannot_check | 1014 |
| over_budget | 380 |
| no_answer | 122 |

`over_budget`: the unchecked run answered, the checked run hit the time limit (certificate generation or checking); `no_answer`: no answer in either run, or the checked run failed for another reason.

Wall time on the 1045 inputs both modes answer: off 2372.5 s, on 2753.1 s (ratio 1.16).

Answers that differ from the unchecked run: 0

### Per family

| family | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| bridge | 0 | 3 | 97 | 0 | 0 |
| cardinality | 0 | 5 | 96 | 0 | 0 |
| data | 0 | 0 | 75 | 0 | 25 |
| fixture | 6 | 9 | 164 | 1 | 6 |
| nominal | 0 | 0 | 72 | 0 | 28 |
| ore | 28 | 214 | 445 | 379 | 28 |
| rule | 0 | 0 | 65 | 0 | 35 |

### Per route (off run)

| route (off run) | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| - | 0 | 0 | 3 | 0 | 6 |
| certified_card_nominals | 0 | 0 | 1 | 0 | 0 |
| certified_card_proxy_abox | 0 | 0 | 0 | 0 | 1 |
| certified_nominals | 0 | 0 | 186 | 1 | 65 |
| elc | 31 | 209 | 0 | 347 | 6 |
| ht_bridge | 0 | 0 | 188 | 0 | 0 |
| ht_rules | 0 | 0 | 68 | 0 | 37 |
| manual | 0 | 0 | 88 | 0 | 1 |
| mirror_private | 0 | 0 | 1 | 0 | 0 |
| production_all | 3 | 22 | 479 | 32 | 6 |

### Per checker (events)

| checker | accepted | rejected | cannot_check |
|---|---:|---:|---:|
| cb-source-production-taxonomy-check | 3 | 9 | 0 |
| cb-source-taxonomy-cert-check | 3 | 0 | 0 |
| cb:none | 0 | 0 | 230 |
| elc-cert-check | 34 | 435 | 0 |
| ht:none | 0 | 0 | 1280 |

### Cannot-check reasons (events)

| family | reason | events |
|---|---|---:|
| ht | HT checkers not enabled (set KM_LEAN_CHECKERS_HT=N); the HT answer is unchecked | 1280 |
| cb | nominal mode: certified CB would use the unordered regime, which is incomplete with nominals | 199 |
| cb | typed source declined: normalized clause N has no certified typed-source constructor | 18 |
| cb | CB event N has no standalone production derivation (pred) | 6 |
| cb | live CB publication has no blocked saturation | 6 |
| cb | CB event N has no chronological proof (unproved) | 1 |

### Rejections

| family | input | checker message |
|---|---|---|
| bridge | `g337.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g429.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g621.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g11.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g215.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g233.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g266.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g269.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `fwd_atmost1_two_inv_preds_sat.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `fwd_atmost2_q_pred.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `fwd_atmost2_q_pred_local.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `fwd_atmost2_u_pred.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed1241.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed210.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `graph_data_rules.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `lean_el_v3_mixed.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `inconsistent.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10004.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10056.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10088.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10123.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10134.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10160.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10162.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1017.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10275.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10309.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10350.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10355.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10407.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10431.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10516.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10536.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11009.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11010.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11014.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11133.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1117.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11316.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11362.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11497.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11522.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11619.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11694.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11792.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12097.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1211.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12118.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1212.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_12281.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12379.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12397.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12415.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12764.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12776.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12965.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13053.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13204.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13298.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13398.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13413.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1346.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13474.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13530.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13578.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13755.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13872.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14031.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14123.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14128.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1420.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14258.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14396.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14518.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14574.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14826.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14840.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14863.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14901.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14909.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_1494.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15222.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15231.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15292.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1537.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15397.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15399.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15407.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15741.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15860.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15932.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15950.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15968.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15985.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16054.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16076.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16166.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16268.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16299.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16312.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16351.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16501.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16626.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16703.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16806.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16821.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1967.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2022.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2036.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2038.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2066.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_22.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2266.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2377.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2378.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2440.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2496.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_253.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2569.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2608.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2646.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2662.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2672.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2713.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2753.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2876.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_316.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3241.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3263.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_330.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3313.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3349.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3418.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3515.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3550.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3635.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3780.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3884.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3909.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3910.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3936.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3978.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4035.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4074.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4182.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4260.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4382.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4383.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4388.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4527.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_457.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4652.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4655.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4671.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4767.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4798.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4856.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5057.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_508.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5080.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5089.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5090.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5193.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5197.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5213.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5216.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5255.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5266.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_544.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5485.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5492.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5550.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5596.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_5665.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5932.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5966.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5978.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6102.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_6149.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6207.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_630.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_637.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6409.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6461.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6566.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6696.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6796.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6817.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6905.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_703.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7188.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7216.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7220.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7226.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_725.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7270.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7364.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7482.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7488.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7576.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7833.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7894.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7995.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8021.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8135.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8169.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8175.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8187.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8298.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8502.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_869.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8744.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8759.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8806.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8933.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8937.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_894.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8974.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9031.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9154.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_928.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9462.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9509.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9598.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9617.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9646.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9673.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9695.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9772.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9854.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9857.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |

## Mode `ht`

| outcome | runs |
|---|---:|
| accepted | 34 |
| rejected | 365 |
| cannot_check | 662 |
| over_budget | 595 |
| no_answer | 125 |

`over_budget`: the unchecked run answered, the checked run hit the time limit (certificate generation or checking); `no_answer`: no answer in either run, or the checked run failed for another reason.

Wall time on the 696 inputs both modes answer: off 1031.7 s, ht 1862.9 s (ratio 1.81).

Answers that differ from the unchecked run: 0

### Per family

| family | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| bridge | 0 | 62 | 34 | 4 | 0 |
| cardinality | 0 | 63 | 37 | 1 | 0 |
| data | 0 | 0 | 68 | 7 | 25 |
| fixture | 7 | 50 | 95 | 28 | 6 |
| nominal | 0 | 0 | 70 | 2 | 28 |
| ore | 27 | 190 | 293 | 553 | 31 |
| rule | 0 | 0 | 65 | 0 | 35 |

### Per route (off run)

| route (off run) | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| - | 0 | 0 | 2 | 0 | 7 |
| certified_card_nominals | 0 | 0 | 0 | 1 | 0 |
| certified_card_proxy_abox | 0 | 0 | 0 | 0 | 1 |
| certified_nominals | 0 | 0 | 176 | 10 | 66 |
| elc | 30 | 174 | 0 | 383 | 6 |
| ht_bridge | 0 | 0 | 134 | 54 | 0 |
| ht_rules | 0 | 0 | 68 | 0 | 37 |
| manual | 0 | 0 | 63 | 25 | 1 |
| mirror_private | 0 | 0 | 0 | 1 | 0 |
| production_all | 4 | 191 | 219 | 121 | 7 |

### Per checker (events)

| checker | accepted | rejected | cannot_check |
|---|---:|---:|---:|
| cb-source-production-taxonomy-check | 45 | 78 | 0 |
| cb-source-taxonomy-cert-check | 43 | 0 | 0 |
| cb:none | 0 | 0 | 834 |
| elc-cert-check | 33 | 619 | 0 |
| ht:none | 0 | 0 | 1257 |

### Cannot-check reasons (events)

| family | reason | events |
|---|---|---:|
| ht | compact bridge output cannot bypass HT certification | 1160 |
| cb | nominal mode: certified CB would use the unordered regime, which is incomplete with nominals | 366 |
| cb | typed source declined: normalized clause N has no certified typed-source constructor | 227 |
| cb | live CB publication has no blocked saturation | 189 |
| ht | HT Lean certification requires the global consistency route | 90 |
| cb | CB event N has no standalone production derivation (pred) | 47 |
| ht | HT Lean certification has no certified hypertableau route for this input | 5 |
| cb | CB event N has no chronological proof (unproved) | 4 |
| ht | HT Lean certification requires a complete clause projection (dropped=N, fenced=N) | 2 |
| cb | CB event N has no standalone production derivation (unproved) | 1 |

### Rejections

| family | input | checker message |
|---|---|---|
| bridge | `g313.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g321.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g325.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g329.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g337.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g341.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g345.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g349.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g357.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g361.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g365.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g369.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g373.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g377.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g381.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g385.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g389.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g393.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: standalone CB local trace omits its claimed result (exit status: 1); cb-source-production-taxonomy-c |
| bridge | `g405.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g409.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g413.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| bridge | `g421.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g429.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g441.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g445.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g449.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g465.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| bridge | `g477.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g481.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g485.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g489.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g493.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g501.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g509.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g517.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| bridge | `g521.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g525.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g533.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| bridge | `g537.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g541.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g549.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g553.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g557.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| bridge | `g565.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g569.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| bridge | `g581.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g589.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| bridge | `g597.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g605.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g609.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| bridge | `g613.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g617.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g621.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| bridge | `g625.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g629.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g637.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g649.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g661.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g677.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g681.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| bridge | `g693.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| bridge | `g697.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `dd.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g101.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g104.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g107.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g11.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g110.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g116.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g122.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g125.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g128.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g131.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g134.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g140.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g146.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: standalone CB local trace omits its claimed result (exit status: 1); cb-source-production-taxonomy-c |
| cardinality | `g152.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g155.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g158.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g167.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g170.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g173.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g179.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g188.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g191.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g197.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g20.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g203.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g206.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g209.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g215.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g218.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g221.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g233.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g236.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g239.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g248.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g26.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g260.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g263.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g266.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g269.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g275.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g278.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g281.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g287.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g29.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g290.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: ContextCalculus.CBSourceProductionTaxonomyWire.WireDocument.proof: ContextCalculus.CBStandaloneConte |
| cardinality | `g299.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g32.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g35.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g38.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g41.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g47.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g5.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g50.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g62.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g65.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g68.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g8.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g83.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g86.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g89.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| cardinality | `g92.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| cardinality | `g95.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `fwd_atmost2_q_pred.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `fwd_atmost2_q_pred_local.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `fwd_atmost2_u_pred.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `inv_atmost1_q_pred.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `inv_atmost1_q_pred_class.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `inv_atmost2_q_pred.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `inv_atmost2_q_pred_sat.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `inv_atmost2_u_pred.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `inv_atmost2_u_pred_guarded.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed1241.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `clause_or_definer_fallback.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `clause_top_conjunction_inconsistent.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `min67_atmost0_definition.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `min_atleast0_gci.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `min_atmost1_definition.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed100.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed111.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed112.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed118.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed153.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed166.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed170.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed171.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed176.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed178.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: decoded CB ontology differs from the allocated verified source encoding (exit status: 1); cb-source- |
| fixture | `seed199.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed207.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed210.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed223.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed238.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed253.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed264.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed273.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed275.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed281.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed292.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed47.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed67.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); cb-source-production-taxonomy-check: source-bound shared-production CB taxonomy rejected: standalone CB local trace omits its claimed result (exit status: 1); cb-source-production-taxonomy-c |
| fixture | `seed87.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed94.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed1045.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed1189.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed1212.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed528.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `seed599.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `integral_datatype_cells.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `inverse_predecessor_transitivity.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `lean_el_v3_mixed.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| fixture | `inconsistent.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| fixture | `saturated_inverse_universal_model.ofn` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10004.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10026.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10056.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_10088.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_10123.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10134.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_10160.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_10162.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_1017.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_10275.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10309.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_10350.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_10355.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_10516.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_10536.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11009.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11010.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_11014.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_11133.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_1117.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11291.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11316.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11362.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11522.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_11694.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_11792.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_12097.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12107.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1211.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12118.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1212.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_12379.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_12382.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12397.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12415.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_12764.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_12965.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13204.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13398.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13413.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1346.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13474.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_13578.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_13872.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14123.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_14128.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_1420.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14258.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14396.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_14518.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_14826.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_14840.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_14863.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_14909.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_15222.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_15231.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15292.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_1537.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15399.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_15407.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_15741.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15791.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15860.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15950.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_15968.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_15985.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_16054.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16268.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_16299.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_16312.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_16351.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_16501.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_16626.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_16806.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_1967.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_1988.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2022.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2036.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2038.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2066.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_22.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2266.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2378.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_2496.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_253.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2569.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_2608.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2646.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_2652.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_2713.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_2753.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_2876.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_316.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_3241.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3263.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_330.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3313.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3341.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3349.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_3418.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_3515.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_3550.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_3635.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_3685.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3884.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3909.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_3910.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3936.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_3978.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4035.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4182.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4260.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4382.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_4383.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4527.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_457.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4652.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4655.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4671.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_4767.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_4798.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_4856.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_4897.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5057.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_508.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5080.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_5089.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_5090.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_5197.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_5213.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5216.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5255.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_5266.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5404.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_544.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5485.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_5492.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5550.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5596.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_5665.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_5669.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5932.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5966.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_5978.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6102.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_6149.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6207.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_6246.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_630.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_637.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_6409.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_6461.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6696.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6817.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_6981.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7188.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7226.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_725.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_7270.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_7364.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_7482.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7488.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7576.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_7833.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7894.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_7995.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_8169.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_8175.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8187.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_8298.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_8502.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8662.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_869.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_8744.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8806.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_8933.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_8937.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_894.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_8974.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_9031.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_9054.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9154.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_928.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9462.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9509.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9598.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_9617.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_9772.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |
| ore | `ore_ont_9854.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is |
| ore | `ore_ont_9857.owl` | elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1); elc-cert-check: ELC certificate rejected: trace is unsound or materialization is not closed (exit status: 1) |

