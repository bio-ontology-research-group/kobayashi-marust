# Checkers-on suite summary

Inputs: 1781. Off-mode answers against cached HermiT gold: {'ok': 519}.

## Mode `on`

| outcome | runs |
|---|---:|
| accepted | 535 |
| rejected | 0 |
| cannot_check | 1135 |
| over_budget | 21 |
| no_answer | 90 |

`over_budget`: the unchecked run answered, the checked run hit the time limit (certificate generation or checking); `no_answer`: no answer in either run, or the checked run failed for another reason.

Wall time on the 1669 inputs both modes answer: off 3876.0 s, on 6335.0 s (ratio 1.63).

Answers that differ from the unchecked run: 0

### Per family

| family | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| bridge | 1 | 0 | 99 | 0 | 0 |
| cardinality | 4 | 0 | 97 | 0 | 0 |
| data | 0 | 0 | 75 | 0 | 25 |
| fixture | 9 | 0 | 176 | 0 | 1 |
| nominal | 0 | 0 | 74 | 0 | 26 |
| ore | 521 | 0 | 523 | 21 | 29 |
| rule | 0 | 0 | 91 | 0 | 9 |

### Per route (off run)

| route (off run) | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| - | 0 | 0 | 3 | 0 | 8 |
| certified_card_nominals | 0 | 0 | 1 | 0 | 0 |
| certified_card_proxy_abox | 0 | 0 | 0 | 0 | 1 |
| certified_nominals | 0 | 0 | 185 | 1 | 62 |
| elc | 494 | 0 | 73 | 19 | 4 |
| ht_bridge | 0 | 0 | 192 | 0 | 0 |
| ht_rules | 0 | 0 | 96 | 0 | 9 |
| manual | 0 | 0 | 88 | 0 | 1 |
| mirror_private | 0 | 0 | 1 | 0 | 0 |
| production_all | 41 | 0 | 496 | 1 | 5 |

### Per checker (events)

| checker | accepted | rejected | cannot_check |
|---|---:|---:|---:|
| cb-source-production-taxonomy-check | 5 | 0 | 0 |
| cb-source-taxonomy-cert-check | 5 | 0 | 0 |
| cb:none | 0 | 0 | 205 |
| elc-cert-check | 533 | 0 | 0 |
| elc:none | 0 | 0 | 96 |
| ht:none | 0 | 0 | 1149 |

### Cannot-check reasons (events)

| family | reason | events |
|---|---|---:|
| ht | HT checkers not enabled (set KM_LEAN_CHECKERS_HT=N); the HT answer is unchecked | 1149 |
| cb | nominal mode: certified CB would use the unordered regime, which is incomplete with nominals | 188 |
| elc | ELC certificate would hold N derived facts, above KM_LEAN_CHECK_MAX_ELC_FACTS=N; the ELC answer is unchecked | 76 |
| elc | residual clauses do not hold in the EL canonical model; no ELC certificate applies | 20 |
| cb | typed source declined: normalized clause N has no certified typed-source constructor | 14 |
| cb | CB event N has no chronological proof (unproved) | 1 |
| cb | CB event N has no standalone production derivation (pred) | 1 |
| cb | live CB publication has no blocked saturation | 1 |

## Mode `ht`

| outcome | runs |
|---|---:|
| accepted | 596 |
| rejected | 0 |
| cannot_check | 916 |
| over_budget | 178 |
| no_answer | 91 |

`over_budget`: the unchecked run answered, the checked run hit the time limit (certificate generation or checking); `no_answer`: no answer in either run, or the checked run failed for another reason.

Wall time on the 1511 inputs both modes answer: off 2652.3 s, ht 5890.8 s (ratio 2.22).

Answers that differ from the unchecked run: 0

### Per family

| family | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| bridge | 22 | 0 | 76 | 2 | 0 |
| cardinality | 24 | 0 | 76 | 1 | 0 |
| data | 0 | 0 | 70 | 5 | 25 |
| fixture | 20 | 0 | 138 | 27 | 1 |
| nominal | 0 | 0 | 72 | 2 | 26 |
| ore | 529 | 0 | 394 | 141 | 30 |
| rule | 1 | 0 | 90 | 0 | 9 |

### Per route (off run)

| route (off run) | accepted | rejected | cannot_check | over_budget | no_answer |
|---|---:|---:|---:|---:|---:|
| - | 0 | 0 | 3 | 0 | 8 |
| certified_card_nominals | 0 | 0 | 0 | 1 | 0 |
| certified_card_proxy_abox | 0 | 0 | 0 | 0 | 1 |
| certified_nominals | 0 | 0 | 177 | 9 | 62 |
| elc | 494 | 0 | 69 | 23 | 4 |
| ht_bridge | 0 | 0 | 141 | 51 | 0 |
| ht_rules | 0 | 0 | 96 | 0 | 9 |
| manual | 0 | 0 | 65 | 22 | 2 |
| mirror_private | 0 | 0 | 0 | 1 | 0 |
| production_all | 102 | 0 | 365 | 71 | 5 |

### Per checker (events)

| checker | accepted | rejected | cannot_check |
|---|---:|---:|---:|
| cb-source-production-taxonomy-check | 55 | 0 | 0 |
| cb-source-taxonomy-cert-check | 55 | 0 | 0 |
| cb:none | 0 | 0 | 740 |
| elc-cert-check | 544 | 0 | 0 |
| elc:none | 0 | 0 | 421 |
| ht:none | 0 | 0 | 1206 |

### Cannot-check reasons (events)

| family | reason | events |
|---|---|---:|
| ht | compact bridge output cannot bypass HT certification | 1110 |
| cb | nominal mode: certified CB would use the unordered regime, which is incomplete with nominals | 365 |
| elc | residual clauses do not hold in the EL canonical model; no ELC certificate applies | 330 |
| cb | typed source declined: normalized clause N has no certified typed-source constructor | 231 |
| ht | HT Lean certification requires the global consistency route | 94 |
| cb | live CB publication has no blocked saturation | 92 |
| elc | ELC certificate would hold N derived facts, above KM_LEAN_CHECK_MAX_ELC_FACTS=N; the ELC answer is unchecked | 91 |
| cb | CB event N has no standalone production derivation (pred) | 47 |
| cb | CB event N has no chronological proof (unproved) | 4 |
| ht | HT Lean certification requires a complete clause projection (dropped=N, fenced=N) | 2 |
| cb | CB event N has no standalone production derivation (unproved) | 1 |

