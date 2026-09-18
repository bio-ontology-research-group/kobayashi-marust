# Incremental reasoning comparison

This report describes the supplied audited evidence. It does not establish release certification or completion of any missing experiments.

Warmups are excluded from timing summaries. Times below are whole-process history wall times, including runtime startup, parsing, reasoning, canonicalization and output. They support an end-to-end service comparison, not an inference-only cross-interface speedup. Konclude starts a fresh process per state; the other fresh arms reconstruct reasoning state inside a persistent runtime.

Java extract_s measures taxonomy extraction; hashing and writing signatures occur afterward and are included in whole-process wall time. KM canonicalize_s similarly excludes subsequent signature writing. Raw supervisor status remains in attempts.tsv; direct timeout/unsupported/parse-error evidence, when supplied, appears in separate failure_kind and verdict fields. A parser rejection is not automatically labelled unsupported.

Each main history has 251 states and five planned measured repetitions. Reported timing uncertainty is the observed minimum–maximum range with sample count, not a confidence interval. Failed and unverified histories remain in every denominator; timing medians use only independently verified complete histories. Pilot/control inputs are explicitly labelled and do not count as main evaluation.

| Evidence | Phase | Terminal attempts / planned (including warmup) | Measured correct / observed |
|---|---|---:|---:|
| v1.4.0 | measured | 1188 / 1188 | 495 / 990 |
| v1.4.0 | measured | 324 / 324 | 135 / 270 |
| v1.4.1 | measured | 288 / 288 | 90 / 240 |

Execution completeness includes terminal errors, timeouts and unsupported attempts. Correct completion additionally requires complete outputs and equality to independently agreeing fresh HermiT and JFact references on exactly the same source-history manifest. Missing/stale measurements do not prove terminal execution; optional scheduler receipts can establish termination but cannot establish correct output.

The pure DL panel is mfomd/zfa/mro, alongside EL mmo/hao/vto. TO and uberon retain their original denominators under DL+rules stress: they contain 25 and 3 SWRL rules respectively. Unknown profiles remain unverified.

| Evidence / stratum | Case | Reasoner / arm | Terminal / planned | Correct / planned | Correct history wall median [min–max] s (n) | Correct peak median MiB | Outcomes |
|---|---|---|---:|---:|---|---:|---|
| v1.4.0 / DL_plus_rules_stress | to-n1 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n1 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n1 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n1 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n1 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n1 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n1 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"parse_error": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n1 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n1 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n10 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n10 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n10 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n10 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n10 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n10 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n10 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"parse_error": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n10 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n10 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n100 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n100 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n100 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n100 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n100 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n100 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n100 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"parse_error": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n100 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | to-n100 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n1 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n1 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n1 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n1 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n1 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n1 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n1 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"memout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n1 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n1 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n10 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n10 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n10 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n10 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n10 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n10 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n10 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"memout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n10 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n10 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n100 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n100 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n100 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 1, "timeout": 4} |
| v1.4.0 / DL_plus_rules_stress | uberon-n100 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 1, "timeout": 4} |
| v1.4.0 / DL_plus_rules_stress | uberon-n100 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n100 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n100 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"memout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n100 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / DL_plus_rules_stress | uberon-n100 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | hao-n1 | elk / fresh | 5 / 5 | 5 / 5 | 258 [240–282] (5) | 739 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | elk / session | 5 / 5 | 5 / 5 | 195 [183–200] (5) | 742 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | hermit / fresh | 5 / 5 | 5 / 5 | 247 [245–255] (5) | 716 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | hermit / session | 5 / 5 | 5 / 5 | 249 [249–254] (5) | 717 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | jfact / fresh | 5 / 5 | 5 / 5 | 3.18e+03 [3.01e+03–3.56e+03] (5) | 2.15e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | jfact / session | 5 / 5 | 5 / 5 | 3.54e+03 [3.23e+03–3.79e+03] (5) | 2.15e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | km / fresh | 5 / 5 | 5 / 5 | 240 [201–252] (5) | 128 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | km / session | 5 / 5 | 5 / 5 | 281 [262–316] (5) | 125 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | konclude / fresh | 5 / 5 | 5 / 5 | 212 [210–214] (5) | 105 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | openllet / fresh | 5 / 5 | 5 / 5 | 2.42e+03 [2.23e+03–2.67e+03] (5) | 2.21e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | openllet / session | 5 / 5 | 5 / 5 | 2.59e+03 [2.37e+03–2.73e+03] (5) | 2.22e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | whelk / fresh | 5 / 5 | 5 / 5 | 508 [456–572] (5) | 1.11e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n1 | whelk / session | 5 / 5 | 5 / 5 | 488 [452–527] (5) | 807 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | elk / fresh | 5 / 5 | 5 / 5 | 207 [205–225] (5) | 738 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | elk / session | 5 / 5 | 5 / 5 | 156 [155–167] (5) | 767 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | hermit / fresh | 5 / 5 | 5 / 5 | 249 [245–259] (5) | 719 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | hermit / session | 5 / 5 | 5 / 5 | 250 [249–254] (5) | 721 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | jfact / fresh | 5 / 5 | 5 / 5 | 2.92e+03 [2.6e+03–3.23e+03] (5) | 2.16e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | jfact / session | 5 / 5 | 5 / 5 | 3.01e+03 [2.54e+03–3.09e+03] (5) | 2.15e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | km / fresh | 5 / 5 | 5 / 5 | 204 [203–212] (5) | 136 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | km / session | 5 / 5 | 5 / 5 | 265 [260–272] (5) | 131 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | konclude / fresh | 5 / 5 | 5 / 5 | 208 [207–209] (5) | 99.8 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | openllet / fresh | 5 / 5 | 5 / 5 | 2.89e+03 [2.66e+03–3.3e+03] (5) | 2.23e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | openllet / session | 5 / 5 | 5 / 5 | 2.95e+03 [2.64e+03–3.27e+03] (5) | 2.24e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | whelk / fresh | 5 / 5 | 5 / 5 | 576 [572–582] (5) | 1.15e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n10 | whelk / session | 5 / 5 | 5 / 5 | 574 [558–608] (5) | 811 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | elk / fresh | 5 / 5 | 5 / 5 | 263 [260–267] (5) | 743 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | elk / session | 5 / 5 | 5 / 5 | 219 [214–224] (5) | 867 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | hermit / fresh | 5 / 5 | 5 / 5 | 253 [249–262] (5) | 714 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | hermit / session | 5 / 5 | 5 / 5 | 258 [256–265] (5) | 717 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | jfact / fresh | 5 / 5 | 5 / 5 | 3.25e+03 [3.08e+03–3.5e+03] (5) | 2.16e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | jfact / session | 5 / 5 | 5 / 5 | 3.08e+03 [2.73e+03–3.55e+03] (5) | 2.15e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | km / fresh | 5 / 5 | 5 / 5 | 245 [190–246] (5) | 154 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | km / session | 5 / 5 | 5 / 5 | 328 [242–330] (5) | 135 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | konclude / fresh | 5 / 5 | 5 / 5 | 174 [171–176] (5) | 111 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | openllet / fresh | 5 / 5 | 5 / 5 | 3.42e+03 [3.04e+03–4.29e+03] (5) | 2.23e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | openllet / session | 5 / 5 | 5 / 5 | 3.25e+03 [3.15e+03–4.47e+03] (5) | 2.23e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | whelk / fresh | 5 / 5 | 5 / 5 | 548 [544–560] (5) | 1.15e+03 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | hao-n100 | whelk / session | 5 / 5 | 5 / 5 | 551 [542–571] (5) | 810 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | elk / fresh | 5 / 5 | 5 / 5 | 52.3 [51.2–53] (5) | 698 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | elk / session | 5 / 5 | 5 / 5 | 46.4 [44.2–47.8] (5) | 688 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | hermit / fresh | 5 / 5 | 5 / 5 | 49.6 [45.5–51.4] (5) | 696 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | hermit / session | 5 / 5 | 5 / 5 | 48.8 [47.3–49.8] (5) | 693 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | jfact / fresh | 5 / 5 | 5 / 5 | 51.9 [49–55.3] (5) | 868 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | jfact / session | 5 / 5 | 5 / 5 | 53.6 [51.5–55.9] (5) | 823 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | km / fresh | 5 / 5 | 5 / 5 | 17.6 [17.5–17.8] (5) | 29.1 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | km / session | 5 / 5 | 5 / 5 | 20.3 [20.2–20.5] (5) | 29.1 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | konclude / fresh | 5 / 5 | 5 / 5 | 120 [116–121] (5) | 52.8 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | openllet / fresh | 5 / 5 | 5 / 5 | 74 [73.4–74.2] (5) | 697 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | openllet / session | 5 / 5 | 5 / 5 | 73.3 [71.7–74.7] (5) | 698 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | whelk / fresh | 5 / 5 | 5 / 5 | 77.1 [76.8–78.6] (5) | 717 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n1 | whelk / session | 5 / 5 | 5 / 5 | 79.4 [76.9–82.2] (5) | 703 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | elk / fresh | 5 / 5 | 5 / 5 | 50 [47.2–51.2] (5) | 698 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | elk / session | 5 / 5 | 5 / 5 | 47.5 [45.3–48.4] (5) | 702 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | hermit / fresh | 5 / 5 | 5 / 5 | 52.6 [50.3–53.7] (5) | 701 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | hermit / session | 5 / 5 | 5 / 5 | 52.2 [48.4–53.7] (5) | 692 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | jfact / fresh | 5 / 5 | 5 / 5 | 49.3 [47.9–50.8] (5) | 856 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | jfact / session | 5 / 5 | 5 / 5 | 50.6 [49.5–52.4] (5) | 825 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | km / fresh | 5 / 5 | 5 / 5 | 17.2 [17.1–17.2] (5) | 29.3 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | km / session | 5 / 5 | 5 / 5 | 19.6 [19.3–19.9] (5) | 29.5 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | konclude / fresh | 5 / 5 | 5 / 5 | 215 [149–262] (5) | 52.5 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | openllet / fresh | 5 / 5 | 5 / 5 | 77.4 [75.8–78.2] (5) | 700 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | openllet / session | 5 / 5 | 5 / 5 | 81.6 [77.2–82.4] (5) | 694 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | whelk / fresh | 5 / 5 | 5 / 5 | 83 [81.4–83.8] (5) | 716 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n10 | whelk / session | 5 / 5 | 5 / 5 | 81.8 [80.7–85.6] (5) | 710 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | elk / fresh | 5 / 5 | 5 / 5 | 53.3 [52.2–55.7] (5) | 690 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | elk / session | 5 / 5 | 5 / 5 | 57 [56–60] (5) | 776 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | hermit / fresh | 5 / 5 | 5 / 5 | 47.8 [44.2–51.1] (5) | 686 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | hermit / session | 5 / 5 | 5 / 5 | 46.7 [45.8–49.8] (5) | 693 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | jfact / fresh | 5 / 5 | 5 / 5 | 76.7 [64.2–82.9] (5) | 848 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | jfact / session | 5 / 5 | 5 / 5 | 78 [70.4–88.4] (5) | 832 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | km / fresh | 5 / 5 | 5 / 5 | 15.6 [15.6–15.7] (5) | 29.3 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | km / session | 5 / 5 | 5 / 5 | 18.3 [18–18.4] (5) | 29.7 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | konclude / fresh | 5 / 5 | 5 / 5 | 118 [118–119] (5) | 47.5 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | openllet / fresh | 5 / 5 | 5 / 5 | 76.2 [74.9–78] (5) | 698 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | openllet / session | 5 / 5 | 5 / 5 | 80.8 [76.9–84.6] (5) | 701 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | whelk / fresh | 5 / 5 | 5 / 5 | 78.6 [76.4–80] (5) | 703 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | mmo-n100 | whelk / session | 5 / 5 | 5 / 5 | 79.5 [78.3–81.9] (5) | 708 | {"verified_correct": 5} |
| v1.4.0 / OWL2EL | vto-n1 | elk / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n1 | elk / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n1 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n1 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n1 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n1 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n1 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n1 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n1 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n1 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n1 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n1 | whelk / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n1 | whelk / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n10 | elk / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n10 | elk / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n10 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n10 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n10 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n10 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n10 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n10 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n10 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n10 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n10 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n10 | whelk / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n10 | whelk / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n100 | elk / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n100 | elk / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n100 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n100 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n100 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n100 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n100 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n100 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n100 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.0 / OWL2EL | vto-n100 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n100 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n100 | whelk / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / OWL2EL | vto-n100 | whelk / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n1 | hermit / fresh | 5 / 5 | 5 / 5 | 114 [112–115] (5) | 715 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n1 | hermit / session | 5 / 5 | 5 / 5 | 113 [113–116] (5) | 700 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n1 | jfact / fresh | 5 / 5 | 5 / 5 | 104 [102–107] (5) | 880 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n1 | jfact / session | 5 / 5 | 5 / 5 | 107 [101–112] (5) | 839 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n1 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n1 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n1 | konclude / fresh | 5 / 5 | 5 / 5 | 117 [117–118] (5) | 52.3 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n1 | openllet / fresh | 5 / 5 | 5 / 5 | 125 [122–132] (5) | 725 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n1 | openllet / session | 5 / 5 | 5 / 5 | 128 [126–130] (5) | 718 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n10 | hermit / fresh | 5 / 5 | 5 / 5 | 117 [113–120] (5) | 720 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n10 | hermit / session | 5 / 5 | 5 / 5 | 119 [114–126] (5) | 713 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n10 | jfact / fresh | 5 / 5 | 5 / 5 | 99 [93.4–108] (5) | 876 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n10 | jfact / session | 5 / 5 | 5 / 5 | 109 [98.6–110] (5) | 839 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n10 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n10 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n10 | konclude / fresh | 5 / 5 | 5 / 5 | 115 [115–115] (5) | 57.5 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n10 | openllet / fresh | 5 / 5 | 5 / 5 | 98.3 [95.2–102] (5) | 722 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n10 | openllet / session | 5 / 5 | 5 / 5 | 103 [102–106] (5) | 727 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n100 | hermit / fresh | 5 / 5 | 5 / 5 | 120 [116–122] (5) | 749 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n100 | hermit / session | 5 / 5 | 5 / 5 | 124 [118–131] (5) | 707 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n100 | jfact / fresh | 5 / 5 | 5 / 5 | 101 [99.5–111] (5) | 878 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n100 | jfact / session | 5 / 5 | 5 / 5 | 105 [100–111] (5) | 849 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n100 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n100 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n100 | konclude / fresh | 5 / 5 | 5 / 5 | 118 [117–118] (5) | 49.6 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n100 | openllet / fresh | 5 / 5 | 5 / 5 | 125 [118–126] (5) | 723 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mfomd-n100 | openllet / session | 5 / 5 | 5 / 5 | 126 [118–128] (5) | 712 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | mro-n1 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n1 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n1 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n1 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n1 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n1 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n1 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 2, "unverified": 3} |
| v1.4.0 / pure_OWL2DL | mro-n1 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n1 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n10 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n10 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n10 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n10 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n10 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n10 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n10 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 2, "unverified": 3} |
| v1.4.0 / pure_OWL2DL | mro-n10 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n10 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n100 | hermit / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n100 | hermit / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n100 | jfact / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n100 | jfact / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n100 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n100 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n100 | konclude / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 1, "unverified": 4} |
| v1.4.0 / pure_OWL2DL | mro-n100 | openllet / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | mro-n100 | openllet / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n1 | hermit / fresh | 5 / 5 | 5 / 5 | 313 [306–338] (5) | 720 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n1 | hermit / session | 5 / 5 | 5 / 5 | 311 [305–315] (5) | 723 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n1 | jfact / fresh | 5 / 5 | 5 / 5 | 1.29e+03 [1.28e+03–1.32e+03] (5) | 1.34e+03 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n1 | jfact / session | 5 / 5 | 5 / 5 | 1.29e+03 [1.21e+03–1.3e+03] (5) | 1.31e+03 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n1 | km / fresh | 5 / 5 | 5 / 5 | 346 [336–349] (5) | 129 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n1 | km / session | 5 / 5 | 5 / 5 | 653 [638–662] (5) | 152 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n1 | konclude / fresh | 5 / 5 | 5 / 5 | 191 [191–193] (5) | 97.6 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n1 | openllet / fresh | 5 / 5 | 5 / 5 | 402 [383–425] (5) | 744 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n1 | openllet / session | 5 / 5 | 5 / 5 | 411 [405–440] (5) | 749 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n10 | hermit / fresh | 5 / 5 | 5 / 5 | 336 [316–361] (5) | 722 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n10 | hermit / session | 5 / 5 | 5 / 5 | 329 [316–369] (5) | 728 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n10 | jfact / fresh | 5 / 5 | 5 / 5 | 1.49e+03 [1.25e+03–1.64e+03] (5) | 1.34e+03 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n10 | jfact / session | 5 / 5 | 5 / 5 | 1.43e+03 [1.41e+03–1.63e+03] (5) | 1.31e+03 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n10 | km / fresh | 5 / 5 | 5 / 5 | 325 [323–328] (5) | 133 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n10 | km / session | 5 / 5 | 5 / 5 | 393 [389–396] (5) | 148 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n10 | konclude / fresh | 5 / 5 | 5 / 5 | 203 [202–204] (5) | 91.1 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n10 | openllet / fresh | 5 / 5 | 5 / 5 | 425 [418–426] (5) | 742 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n10 | openllet / session | 5 / 5 | 5 / 5 | 418 [412–426] (5) | 746 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n100 | hermit / fresh | 5 / 5 | 5 / 5 | 347 [331–371] (5) | 721 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n100 | hermit / session | 5 / 5 | 5 / 5 | 350 [336–374] (5) | 727 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n100 | jfact / fresh | 5 / 5 | 5 / 5 | 1.43e+03 [1.32e+03–1.52e+03] (5) | 1.34e+03 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n100 | jfact / session | 5 / 5 | 5 / 5 | 1.46e+03 [1.31e+03–1.51e+03] (5) | 1.32e+03 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n100 | km / fresh | 5 / 5 | 5 / 5 | 359 [349–394] (5) | 132 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n100 | km / session | 5 / 5 | 5 / 5 | 388 [354–406] (5) | 146 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n100 | konclude / fresh | 5 / 5 | 5 / 5 | 198 [195–199] (5) | 97.7 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n100 | openllet / fresh | 5 / 5 | 5 / 5 | 396 [387–405] (5) | 747 | {"verified_correct": 5} |
| v1.4.0 / pure_OWL2DL | zfa-n100 | openllet / session | 5 / 5 | 5 / 5 | 401 [387–403] (5) | 755 | {"verified_correct": 5} |
| v1.4.1 / DL_plus_rules_stress | to-n1 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / DL_plus_rules_stress | to-n1 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / DL_plus_rules_stress | to-n10 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / DL_plus_rules_stress | to-n10 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / DL_plus_rules_stress | to-n100 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / DL_plus_rules_stress | to-n100 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / DL_plus_rules_stress | uberon-n1 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / DL_plus_rules_stress | uberon-n1 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / DL_plus_rules_stress | uberon-n10 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / DL_plus_rules_stress | uberon-n10 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / DL_plus_rules_stress | uberon-n100 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / DL_plus_rules_stress | uberon-n100 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / OWL2EL | hao-n1 | km / fresh | 5 / 5 | 5 / 5 | 204 [200–235] (5) | 129 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | hao-n1 | km / session | 5 / 5 | 5 / 5 | 268 [256–278] (5) | 126 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | hao-n10 | km / fresh | 5 / 5 | 5 / 5 | 181 [180–182] (5) | 136 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | hao-n10 | km / session | 5 / 5 | 5 / 5 | 227 [226–229] (5) | 131 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | hao-n100 | km / fresh | 5 / 5 | 5 / 5 | 209 [199–253] (5) | 141 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | hao-n100 | km / session | 5 / 5 | 5 / 5 | 269 [269–319] (5) | 134 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | mmo-n1 | km / fresh | 5 / 5 | 5 / 5 | 18.3 [17.9–21.5] (5) | 29.6 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | mmo-n1 | km / session | 5 / 5 | 5 / 5 | 21.2 [20–22.6] (5) | 29.5 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | mmo-n10 | km / fresh | 5 / 5 | 5 / 5 | 15.6 [15.5–15.7] (5) | 29.1 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | mmo-n10 | km / session | 5 / 5 | 5 / 5 | 17.9 [17.9–18] (5) | 29.7 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | mmo-n100 | km / fresh | 5 / 5 | 5 / 5 | 15.5 [15.4–15.6] (5) | 29.2 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | mmo-n100 | km / session | 5 / 5 | 5 / 5 | 18.1 [17.8–18.1] (5) | 29.4 | {"verified_correct": 5} |
| v1.4.1 / OWL2EL | vto-n1 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.1 / OWL2EL | vto-n1 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.1 / OWL2EL | vto-n10 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.1 / OWL2EL | vto-n10 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.1 / OWL2EL | vto-n100 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.1 / OWL2EL | vto-n100 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"unverified": 5} |
| v1.4.1 / pure_OWL2DL | mfomd-n1 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / pure_OWL2DL | mfomd-n1 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / pure_OWL2DL | mfomd-n10 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / pure_OWL2DL | mfomd-n10 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / pure_OWL2DL | mfomd-n100 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / pure_OWL2DL | mfomd-n100 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"error": 5} |
| v1.4.1 / pure_OWL2DL | mro-n1 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / pure_OWL2DL | mro-n1 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / pure_OWL2DL | mro-n10 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / pure_OWL2DL | mro-n10 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / pure_OWL2DL | mro-n100 | km / fresh | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / pure_OWL2DL | mro-n100 | km / session | 5 / 5 | 0 / 5 | not available | not available | {"timeout": 5} |
| v1.4.1 / pure_OWL2DL | zfa-n1 | km / fresh | 5 / 5 | 5 / 5 | 356 [354–368] (5) | 131 | {"verified_correct": 5} |
| v1.4.1 / pure_OWL2DL | zfa-n1 | km / session | 5 / 5 | 5 / 5 | 673 [672–686] (5) | 152 | {"verified_correct": 5} |
| v1.4.1 / pure_OWL2DL | zfa-n10 | km / fresh | 5 / 5 | 5 / 5 | 296 [284–308] (5) | 134 | {"verified_correct": 5} |
| v1.4.1 / pure_OWL2DL | zfa-n10 | km / session | 5 / 5 | 5 / 5 | 373 [358–374] (5) | 150 | {"verified_correct": 5} |
| v1.4.1 / pure_OWL2DL | zfa-n100 | km / fresh | 5 / 5 | 5 / 5 | 306 [295–311] (5) | 133 | {"verified_correct": 5} |
| v1.4.1 / pure_OWL2DL | zfa-n100 | km / session | 5 / 5 | 5 / 5 | 314 [304–315] (5) | 146 | {"verified_correct": 5} |

Konclude retained-session deletion/exchange is unsupported by the deployed OWLlink API. Only its fresh arm is planned; this capability limitation is explicit rather than a successful incremental result. JFact session discrepancies remain incorrect even when its fresh arm agrees with the independent reference.

Paired speedups are fresh/session ratios only within one reasoner, one source history and one repetition, where both arms are independently correct. `paired-speedups.tsv` keeps whole-process history wall and each API interval separate; it never combines unlike Java inference and KM request/response intervals.

| Evidence | Case | Reasoner | Verified wall-time pairs | Fresh/session median [min–max] |
|---|---|---|---:|---:|
| v1.4.0 | hao-n1 | elk | 5 | 1.33 [1.31–1.41] |
| v1.4.0 | hao-n1 | hermit | 5 | 0.983 [0.975–1.02] |
| v1.4.0 | hao-n1 | jfact | 5 | 0.932 [0.84–1.01] |
| v1.4.0 | hao-n1 | km | 5 | 0.836 [0.638–0.959] |
| v1.4.0 | hao-n1 | openllet | 5 | 0.952 [0.909–0.977] |
| v1.4.0 | hao-n1 | whelk | 5 | 0.998 [0.983–1.17] |
| v1.4.0 | hao-n10 | elk | 5 | 1.33 [1.32–1.38] |
| v1.4.0 | hao-n10 | hermit | 5 | 0.997 [0.97–1.03] |
| v1.4.0 | hao-n10 | jfact | 5 | 1.04 [0.853–1.11] |
| v1.4.0 | hao-n10 | km | 5 | 0.781 [0.765–0.791] |
| v1.4.0 | hao-n10 | openllet | 5 | 0.971 [0.888–1.12] |
| v1.4.0 | hao-n10 | whelk | 5 | 1.01 [0.952–1.03] |
| v1.4.0 | hao-n100 | elk | 5 | 1.19 [1.16–1.23] |
| v1.4.0 | hao-n100 | hermit | 5 | 0.984 [0.964–1] |
| v1.4.0 | hao-n100 | jfact | 5 | 1.05 [0.986–1.19] |
| v1.4.0 | hao-n100 | km | 5 | 0.747 [0.744–0.785] |
| v1.4.0 | hao-n100 | openllet | 5 | 1.07 [0.865–1.12] |
| v1.4.0 | hao-n100 | whelk | 5 | 0.993 [0.961–1.01] |
| v1.4.0 | mmo-n1 | elk | 5 | 1.13 [1.1–1.2] |
| v1.4.0 | mmo-n1 | hermit | 5 | 1.02 [0.962–1.06] |
| v1.4.0 | mmo-n1 | jfact | 5 | 0.968 [0.887–1.05] |
| v1.4.0 | mmo-n1 | km | 5 | 0.865 [0.857–0.877] |
| v1.4.0 | mmo-n1 | openllet | 5 | 1 [0.992–1.03] |
| v1.4.0 | mmo-n1 | whelk | 5 | 0.979 [0.934–1] |
| v1.4.0 | mmo-n10 | elk | 5 | 1.03 [0.993–1.13] |
| v1.4.0 | mmo-n10 | hermit | 5 | 1.01 [0.966–1.09] |
| v1.4.0 | mmo-n10 | jfact | 5 | 0.946 [0.939–1.01] |
| v1.4.0 | mmo-n10 | km | 5 | 0.875 [0.866–0.885] |
| v1.4.0 | mmo-n10 | openllet | 5 | 0.959 [0.924–0.992] |
| v1.4.0 | mmo-n10 | whelk | 5 | 1 [0.974–1.02] |
| v1.4.0 | mmo-n100 | elk | 5 | 0.932 [0.921–0.939] |
| v1.4.0 | mmo-n100 | hermit | 5 | 1.02 [0.954–1.03] |
| v1.4.0 | mmo-n100 | jfact | 5 | 0.96 [0.868–0.984] |
| v1.4.0 | mmo-n100 | km | 5 | 0.856 [0.85–0.87] |
| v1.4.0 | mmo-n100 | openllet | 5 | 0.965 [0.886–0.978] |
| v1.4.0 | mmo-n100 | whelk | 5 | 0.989 [0.933–1.02] |
| v1.4.0 | mfomd-n1 | hermit | 5 | 1.01 [0.961–1.02] |
| v1.4.0 | mfomd-n1 | jfact | 5 | 1 [0.926–1.03] |
| v1.4.0 | mfomd-n1 | openllet | 5 | 0.988 [0.947–1.05] |
| v1.4.0 | mfomd-n10 | hermit | 5 | 0.984 [0.932–1] |
| v1.4.0 | mfomd-n10 | jfact | 5 | 0.97 [0.902–0.994] |
| v1.4.0 | mfomd-n10 | openllet | 5 | 0.953 [0.926–0.982] |
| v1.4.0 | mfomd-n100 | hermit | 5 | 0.969 [0.923–1.03] |
| v1.4.0 | mfomd-n100 | jfact | 5 | 0.971 [0.949–0.999] |
| v1.4.0 | mfomd-n100 | openllet | 5 | 0.987 [0.967–0.997] |
| v1.4.0 | zfa-n1 | hermit | 5 | 1 [0.988–1.07] |
| v1.4.0 | zfa-n1 | jfact | 5 | 1.01 [0.991–1.09] |
| v1.4.0 | zfa-n1 | km | 5 | 0.528 [0.523–0.532] |
| v1.4.0 | zfa-n1 | openllet | 5 | 0.975 [0.931–1.01] |
| v1.4.0 | zfa-n10 | hermit | 5 | 1.02 [0.979–1.04] |
| v1.4.0 | zfa-n10 | jfact | 5 | 0.967 [0.869–1.16] |
| v1.4.0 | zfa-n10 | km | 5 | 0.825 [0.82–0.835] |
| v1.4.0 | zfa-n10 | openllet | 5 | 1.01 [0.998–1.03] |
| v1.4.0 | zfa-n100 | hermit | 5 | 0.986 [0.92–1.08] |
| v1.4.0 | zfa-n100 | jfact | 5 | 1.01 [0.909–1.05] |
| v1.4.0 | zfa-n100 | km | 5 | 0.986 [0.884–1.01] |
| v1.4.0 | zfa-n100 | openllet | 5 | 1 [0.987–1.01] |
| v1.4.1 | hao-n1 | km | 5 | 0.761 [0.72–0.918] |
| v1.4.1 | hao-n10 | km | 5 | 0.799 [0.792–0.802] |
| v1.4.1 | hao-n100 | km | 5 | 0.76 [0.69–0.942] |
| v1.4.1 | mmo-n1 | km | 5 | 0.894 [0.803–1.01] |
| v1.4.1 | mmo-n10 | km | 5 | 0.87 [0.866–0.879] |
| v1.4.1 | mmo-n100 | km | 5 | 0.856 [0.85–0.868] |
| v1.4.1 | zfa-n1 | km | 5 | 0.529 [0.525–0.537] |
| v1.4.1 | zfa-n10 | km | 5 | 0.819 [0.789–0.825] |
| v1.4.1 | zfa-n100 | km | 5 | 0.974 [0.966–0.989] |

Java session means an existing OWLReasoner object receives manager changes and flush calls; it does not prove retained inference. ELK and Whelk are enrolled only on the EL stratum. KM reuse evidence comes from its explicit receipts.

| Evidence | Case | KM exact rebuilds | EL delta receipts | Meaningful updates | Reused fixpoints |
|---|---|---:|---:|---:|---:|
| v1.4.0 | to-n1 | 0 | 0 | 0 | 0 |
| v1.4.0 | to-n10 | 0 | 0 | 0 | 0 |
| v1.4.0 | to-n100 | 0 | 0 | 0 | 0 |
| v1.4.0 | uberon-n1 | 0 | 0 | 0 | 0 |
| v1.4.0 | uberon-n10 | 0 | 0 | 0 | 0 |
| v1.4.0 | uberon-n100 | 0 | 0 | 0 | 0 |
| v1.4.0 | hao-n1 | 0 | 1250 | 1250 | 1250 |
| v1.4.0 | hao-n10 | 0 | 1250 | 1250 | 1250 |
| v1.4.0 | hao-n100 | 0 | 1250 | 1250 | 1250 |
| v1.4.0 | mmo-n1 | 0 | 1250 | 1250 | 1250 |
| v1.4.0 | mmo-n10 | 0 | 1250 | 1250 | 1250 |
| v1.4.0 | mmo-n100 | 0 | 1250 | 1250 | 1250 |
| v1.4.0 | vto-n1 | 0 | 1250 | 1250 | 1250 |
| v1.4.0 | vto-n10 | 0 | 1250 | 1250 | 1250 |
| v1.4.0 | vto-n100 | 0 | 1250 | 1250 | 1250 |
| v1.4.0 | mfomd-n1 | 650 | 0 | 190 | 190 |
| v1.4.0 | mfomd-n10 | 360 | 0 | 0 | 0 |
| v1.4.0 | mfomd-n100 | 80 | 0 | 0 | 0 |
| v1.4.0 | mro-n1 | 0 | 0 | 0 | 0 |
| v1.4.0 | mro-n10 | 0 | 0 | 0 | 0 |
| v1.4.0 | mro-n100 | 0 | 0 | 0 | 0 |
| v1.4.0 | zfa-n1 | 1250 | 0 | 0 | 0 |
| v1.4.0 | zfa-n10 | 1250 | 0 | 0 | 0 |
| v1.4.0 | zfa-n100 | 1250 | 0 | 0 | 0 |
| v1.4.1 | to-n1 | 0 | 0 | 0 | 0 |
| v1.4.1 | to-n10 | 0 | 0 | 0 | 0 |
| v1.4.1 | to-n100 | 0 | 0 | 0 | 0 |
| v1.4.1 | uberon-n1 | 0 | 0 | 0 | 0 |
| v1.4.1 | uberon-n10 | 0 | 0 | 0 | 0 |
| v1.4.1 | uberon-n100 | 0 | 0 | 0 | 0 |
| v1.4.1 | hao-n1 | 0 | 1250 | 1250 | 1250 |
| v1.4.1 | hao-n10 | 0 | 1250 | 1250 | 1250 |
| v1.4.1 | hao-n100 | 0 | 1250 | 1250 | 1250 |
| v1.4.1 | mmo-n1 | 0 | 1250 | 1250 | 1250 |
| v1.4.1 | mmo-n10 | 0 | 1250 | 1250 | 1250 |
| v1.4.1 | mmo-n100 | 0 | 1250 | 1250 | 1250 |
| v1.4.1 | vto-n1 | 0 | 1250 | 1250 | 1250 |
| v1.4.1 | vto-n10 | 0 | 1250 | 1250 | 1250 |
| v1.4.1 | vto-n100 | 0 | 1250 | 1250 | 1250 |
| v1.4.1 | mfomd-n1 | 650 | 0 | 190 | 190 |
| v1.4.1 | mfomd-n10 | 360 | 0 | 0 | 0 |
| v1.4.1 | mfomd-n100 | 80 | 0 | 0 | 0 |
| v1.4.1 | mro-n1 | 0 | 0 | 0 | 0 |
| v1.4.1 | mro-n10 | 0 | 0 | 0 | 0 |
| v1.4.1 | mro-n100 | 0 | 0 | 0 | 0 |
| v1.4.1 | zfa-n1 | 1250 | 0 | 0 | 0 |
| v1.4.1 | zfa-n10 | 1250 | 0 | 0 | 0 |
| v1.4.1 | zfa-n100 | 1250 | 0 | 0 | 0 |

Reuse totals cover observed measured-session receipts, including partial/incorrect attempts; they describe mechanism, not verified performance. `retained_backend` alone is not evidence of inference reuse.

Downloads: [attempts](attempts.tsv), [summaries](summary.tsv), [paired speedups](paired-speedups.tsv), [speedup ranges](paired-speedup-summary.tsv), [source/runtime provenance](provenance.tsv).

| Evidence | Audit SHA-256 | Runtime SHA-256 values |
|---|---|---|
| v1.4.0 | `5524d552d8df1860841e94aad17cc68618018680b74894bb367d692ce1a14045` | `06f85fd8e6cc647f7436b8a13da13a4d0b03b2df1d1184394ebe885f29c65867`, `43671b4a4ea06a24834183b5c55cdb3830fe1c96d33ffe56b32a5167d6f0319f`, `5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3`, `59a7dc34d874c0dd9fb752594eb8d55b611e70d3cf7e839d581d7c366a5dd99c`, `7ffc442f2966667a488479a748502276136445c8e44ffd9e8498873a401cb3d4`, `ddc30d2f9013b371b5c4ec19c0623c91ecc1b2dbdc172ded9002fd238903d09a`, `e5ce43b18ee9e8ada9ce9cc2a7cea35f6658d56089b3d4caa4bb9bfec2fce55b` |
| v1.4.0 | `5077ce21bac88fc3961a252014dcc3da3adf85b76296fa9ba1987af233cfa17c` | `06f85fd8e6cc647f7436b8a13da13a4d0b03b2df1d1184394ebe885f29c65867`, `43671b4a4ea06a24834183b5c55cdb3830fe1c96d33ffe56b32a5167d6f0319f`, `5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3`, `59a7dc34d874c0dd9fb752594eb8d55b611e70d3cf7e839d581d7c366a5dd99c`, `ddc30d2f9013b371b5c4ec19c0623c91ecc1b2dbdc172ded9002fd238903d09a` |
| v1.4.1 | `e7bd1b642fe11b00545f1f36d50384e7ecfed609a1e050480d553f8e2eb8316d` | `680d9002583468e7c68115bf67cb60b89e420339db4c6aa22b5ca802206c8629` |
