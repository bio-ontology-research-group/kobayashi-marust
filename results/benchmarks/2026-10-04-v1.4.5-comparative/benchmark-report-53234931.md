# v1.4.5 comparative benchmark evidence

This document summarizes recorded outcomes. Release approval and correctness adjudication are separate. Missing audits and failed measurements remain visible; raw output production is not a correctness result.

Measurements use one CPU, a 20 GiB memory limit, and 240 seconds per classification, update, or justification generation. Independent justification verification has a separate 240-second limit.

**Classification coverage**

The unchanged corpus contains 1920 inputs. Admission and raw measurement status appear together below. Invalid-input refusals are retained.

| Method | checks_passed:executed_unvalidated | checks_passed:memout | checks_passed:process_error | checks_passed:timeout | invalid_input:executed_unvalidated | invalid_input:process_error | invalid_input:timeout |
| --- | --- | --- | --- | --- | --- | --- | --- |
| elk | 1701 | 0 | 0 | 7 | 211 | 0 | 1 |
| hermit | 1540 | 0 | 14 | 154 | 191 | 1 | 20 |
| jfact | 1238 | 0 | 35 | 435 | 173 | 0 | 39 |
| km | 1594 | 0 | 44 | 70 | 0 | 212 | 0 |
| konclude | 1697 | 5 | 0 | 6 | 210 | 0 | 2 |
| more | 1584 | 0 | 44 | 80 | 57 | 151 | 4 |
| openllet | 1411 | 0 | 22 | 275 | 169 | 0 | 43 |
| rustdl | 1585 | 5 | 1 | 117 | 208 | 0 | 4 |
| sequoia | 630 | 0 | 1032 | 46 | 0 | 211 | 1 |
| whelk | 1647 | 0 | 0 | 61 | 206 | 0 | 6 |


**Classification comparisons with KM**

Each cost row uses the same valid inputs for both reasoners and requires full semantic agreement. Unknown consistency is not promoted to agreement. Times and memory are medians; ratios are medians of per-case right/left ratios, not ratios of independent medians. All baseline pairs remain in the JSON report.

| Phase | Left | Right | Paired cases | Left s | Right s | Time right/left | Left MiB | Right MiB | Memory right/left |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
|  | elk | km | 1368 | 4.746 | 0.6108 | 0.1055 | 164.3 | 24.07 | 0.1427 |
|  | hermit | km | 1476 | 4.84 | 0.5443 | 0.08465 | 166.4 | 23.62 | 0.1331 |
|  | jfact | km | 1069 | 5.173 | 0.1976 | 0.02798 | 171.7 | 15.62 | 0.08535 |
|  | km | konclude | 1589 | 0.6906 | 0.2636 | 0.6288 | 26.38 | 45.62 | 2.348 |
|  | km | more | 0 | n/a | n/a | n/a | n/a | n/a | n/a |
|  | km | openllet | 1344 | 0.3464 | 4.794 | 17.69 | 20.44 | 170.8 | 8.704 |
|  | km | rustdl | 1195 | 0.6717 | 0.3121 | 0.5945 | 24.46 | 24.5 | 0.8383 |
|  | km | sequoia | 627 | 0.6115 | 7.375 | 13.11 | 23.85 | 254.2 | 12.75 |
|  | km | whelk | 1334 | 0.5654 | 6.198 | 13.62 | 23.87 | 193.4 | 8.155 |


**Incremental coverage**

The panel retains 80 ontologies, five revisions, and three repetitions. Cold means a fresh process. Retained means the same session; it does not establish internal reuse. The JSON report includes actual KM reuse receipts and unknown reuse for interfaces that do not expose it.

| Method | canonicalized_requires_comparison | engine_refusal_or_error | memout | not_run_after_session_failure | ok | preparation_failed | process_error | timeout | validation_error | worker_exited_before_revision_completed |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| elk-cold | 1156 | 0 | 0 | 0 | 0 | 15 | 0 | 29 | 0 | 0 |
| elk-retained | 1155 | 0 | 0 | 24 | 0 | 15 | 0 | 6 | 0 | 0 |
| hermit-cold | 1065 | 0 | 0 | 0 | 0 | 15 | 15 | 105 | 0 | 0 |
| hermit-retained | 1065 | 0 | 0 | 96 | 0 | 15 | 0 | 21 | 0 | 3 |
| jfact-cold | 795 | 0 | 0 | 0 | 0 | 15 | 15 | 375 | 0 | 0 |
| jfact-retained | 795 | 0 | 0 | 312 | 0 | 15 | 0 | 75 | 0 | 3 |
| km-cold | 1149 | 0 | 0 | 0 | 0 | 15 | 15 | 21 | 0 | 0 |
| km-retained | 1031 | 3 | 6 | 121 | 0 | 15 | 0 | 24 | 0 | 0 |
| konclude-cold | 1170 | 0 | 15 | 0 | 0 | 15 | 0 | 0 | 0 | 0 |
| konclude-retained | 1164 | 0 | 3 | 15 | 3 | 15 | 0 | 0 | 0 | 0 |
| more-cold | 1076 | 0 | 0 | 0 | 0 | 15 | 19 | 90 | 0 | 0 |
| openllet-cold | 923 | 0 | 0 | 0 | 0 | 15 | 53 | 209 | 0 | 0 |
| openllet-retained | 907 | 0 | 0 | 222 | 0 | 15 | 0 | 44 | 0 | 12 |
| rustdl-cold | 808 | 0 | 15 | 0 | 0 | 15 | 15 | 120 | 227 | 0 |
| sequoia-cold | 435 | 0 | 0 | 0 | 0 | 15 | 705 | 45 | 0 | 0 |
| whelk-cold | 1139 | 0 | 0 | 0 | 0 | 15 | 0 | 46 | 0 | 0 |
| whelk-retained | 1135 | 0 | 0 | 40 | 0 | 15 | 0 | 10 | 0 | 0 |


**Incremental comparisons with KM**

Initialization is reported separately from the four update revisions. Pairing uses identical source, revision, and repetition, and requires full agreement. Pairwise agreement alone does not adjudicate a disagreement with an independent reference; all comparison outcomes remain in the JSON report.

| Phase | Left | Right | Paired cases | Left s | Right s | Time right/left | Left MiB | Right MiB | Memory right/left |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| initialization | elk-cold | km-cold | 189 | 5.851 | 0.8715 | 0.1354 | 172.7 | 26.72 | 0.157 |
| initialization | elk-cold | km-retained | 174 | 4.387 | 0.6541 | 0.1093 | 164.4 | 46.48 | 0.2825 |
| initialization | elk-retained | km-cold | 189 | 6.39 | 0.8715 | 0.1255 | 178.6 | 26.72 | 0.1496 |
| initialization | elk-retained | km-retained | 174 | 4.911 | 0.6541 | 0.09623 | 168.9 | 46.48 | 0.2761 |
| initialization | hermit-cold | km-cold | 207 | 4.596 | 0.5776 | 0.09256 | 165.1 | 23.14 | 0.1378 |
| initialization | hermit-cold | km-retained | 195 | 3.881 | 0.4099 | 0.09372 | 162 | 30.23 | 0.1934 |
| initialization | hermit-retained | km-cold | 207 | 4.829 | 0.5776 | 0.08899 | 167.8 | 23.14 | 0.1315 |
| initialization | hermit-retained | km-retained | 195 | 4.255 | 0.4099 | 0.08768 | 163.6 | 30.23 | 0.1917 |
| initialization | jfact-cold | km-cold | 135 | 4.321 | 0.1326 | 0.02877 | 158.5 | 13.75 | 0.07603 |
| initialization | jfact-cold | km-retained | 138 | 4.332 | 0.1685 | 0.0309 | 159.4 | 15 | 0.08135 |
| initialization | jfact-retained | km-cold | 132 | 4.777 | 0.1206 | 0.02465 | 163.9 | 13.44 | 0.07463 |
| initialization | jfact-retained | km-retained | 135 | 4.83 | 0.1469 | 0.02701 | 164 | 15 | 0.07914 |
| initialization | km-cold | km-retained | 207 | 0.3704 | 0.4291 | 1.077 | 20.31 | 36.88 | 1.307 |
| initialization | km-cold | konclude-cold | 228 | 0.8285 | 0.3229 | 0.584 | 24.37 | 49.84 | 2.227 |
| initialization | km-cold | konclude-retained | 225 | 0.8715 | 0.8535 | 1.733 | 24.38 | 60.94 | 2.929 |
| initialization | km-cold | more-cold | 0 | n/a | n/a | n/a | n/a | n/a | n/a |
| initialization | km-cold | openllet-cold | 175 | 0.2265 | 4.202 | 21.02 | 17.19 | 165.6 | 8.542 |
| initialization | km-cold | openllet-retained | 173 | 0.2254 | 4.437 | 22.21 | 16.88 | 164.3 | 8.812 |
| initialization | km-cold | rustdl-cold | 161 | 0.9051 | 0.4656 | 0.5424 | 28.14 | 30.48 | 0.9125 |
| initialization | km-cold | sequoia-cold | 87 | 0.8715 | 8.541 | 11.47 | 28.75 | 308.1 | 11.59 |
| initialization | km-cold | whelk-cold | 185 | 0.8956 | 7.073 | 11.22 | 26.72 | 198.8 | 7.577 |
| initialization | km-cold | whelk-retained | 185 | 0.8956 | 7.705 | 12.09 | 26.72 | 195.9 | 7.714 |
| initialization | km-retained | konclude-cold | 210 | 0.4827 | 0.2115 | 0.5873 | 38.59 | 36.85 | 1.236 |
| initialization | km-retained | konclude-retained | 207 | 0.5484 | 0.367 | 1.265 | 39.69 | 48.66 | 2.162 |
| initialization | km-retained | more-cold | 0 | n/a | n/a | n/a | n/a | n/a | n/a |
| initialization | km-retained | openllet-cold | 169 | 0.2899 | 3.873 | 15.78 | 21.77 | 163.6 | 6.975 |
| initialization | km-retained | openllet-retained | 168 | 0.2808 | 4.189 | 16.92 | 20.26 | 163.2 | 7.178 |
| initialization | km-retained | rustdl-cold | 149 | 0.7912 | 0.3052 | 0.4881 | 53.38 | 25.09 | 0.5853 |
| initialization | km-retained | sequoia-cold | 78 | 0.7763 | 7.287 | 12.81 | 80.05 | 283 | 4.842 |
| initialization | km-retained | whelk-cold | 170 | 0.7474 | 5.138 | 12.85 | 41.39 | 189.9 | 4.547 |
| initialization | km-retained | whelk-retained | 170 | 0.7474 | 5.519 | 13.58 | 41.39 | 191.9 | 4.53 |
| updates | elk-cold | km-cold | 757 | 5.797 | 0.8818 | 0.1379 | 173.2 | 26.77 | 0.1579 |
| updates | elk-cold | km-retained | 696 | 4.252 | 0.8197 | 0.143 | 164.7 | 67.37 | 0.4293 |
| updates | elk-retained | km-cold | 756 | 1.428 | 0.8793 | 0.6067 | 197 | 26.74 | 0.1334 |
| updates | elk-retained | km-retained | 696 | 0.8366 | 0.8197 | 0.7034 | 188.1 | 67.37 | 0.376 |
| updates | hermit-cold | km-cold | 822 | 4.552 | 0.5629 | 0.08703 | 164.3 | 23.14 | 0.1389 |
| updates | hermit-cold | km-retained | 780 | 3.895 | 0.4331 | 0.1091 | 161.8 | 40.47 | 0.2676 |
| updates | hermit-retained | km-cold | 822 | 1.056 | 0.5629 | 0.4151 | 183.6 | 23.14 | 0.1144 |
| updates | hermit-retained | km-retained | 780 | 0.7987 | 0.4331 | 0.5855 | 177.5 | 40.47 | 0.2218 |
| updates | jfact-cold | km-cold | 534 | 4.273 | 0.1328 | 0.02812 | 161.1 | 13.44 | 0.07396 |
| updates | jfact-cold | km-retained | 552 | 4.293 | 0.1701 | 0.03245 | 165.2 | 17.66 | 0.09944 |
| updates | jfact-retained | km-cold | 510 | 0.4161 | 0.1093 | 0.2177 | 182.5 | 13.23 | 0.06379 |
| updates | jfact-retained | km-retained | 528 | 0.4564 | 0.1683 | 0.256 | 183.6 | 17.46 | 0.08659 |
| updates | km-cold | km-retained | 803 | 0.375 | 0.4641 | 1.255 | 21.88 | 48.07 | 1.627 |
| updates | km-cold | konclude-cold | 906 | 0.7844 | 0.2493 | 0.5673 | 24.37 | 47.11 | 2.231 |
| updates | km-cold | konclude-retained | 880 | 0.8589 | 0.5101 | 1.143 | 24.82 | 112.9 | 3.635 |
| updates | km-cold | more-cold | 0 | n/a | n/a | n/a | n/a | n/a | n/a |
| updates | km-cold | openllet-cold | 697 | 0.2275 | 4.193 | 20.98 | 18.12 | 162.7 | 8.523 |
| updates | km-cold | openllet-retained | 683 | 0.2224 | 0.6943 | 3.146 | 17.19 | 181.3 | 10.97 |
| updates | km-cold | rustdl-cold | 647 | 0.8932 | 0.4518 | 0.5379 | 28.14 | 30.35 | 0.8674 |
| updates | km-cold | sequoia-cold | 348 | 0.8849 | 8.432 | 11.17 | 28.46 | 310 | 11.44 |
| updates | km-cold | whelk-cold | 747 | 0.8976 | 7.095 | 10.76 | 27.25 | 200.8 | 7.626 |
| updates | km-cold | whelk-retained | 743 | 0.8923 | 2.53 | 3.31 | 26.94 | 236.1 | 9.186 |
| updates | km-retained | konclude-cold | 821 | 0.6456 | 0.1973 | 0.4355 | 55.51 | 36.88 | 0.9443 |
| updates | km-retained | konclude-retained | 798 | 0.47 | 0.2551 | 0.8651 | 51.14 | 67.16 | 2.205 |
| updates | km-retained | more-cold | 0 | n/a | n/a | n/a | n/a | n/a | n/a |
| updates | km-retained | openllet-cold | 672 | 0.2985 | 3.972 | 15.95 | 31.5 | 162.3 | 5.147 |
| updates | km-retained | openllet-retained | 661 | 0.2879 | 0.6766 | 2.392 | 31.25 | 181.1 | 6.066 |
| updates | km-retained | rustdl-cold | 592 | 0.9585 | 0.1962 | 0.4165 | 79.49 | 24.99 | 0.4586 |
| updates | km-retained | sequoia-cold | 312 | 1.011 | 7.327 | 10.87 | 131.6 | 281.4 | 3.077 |
| updates | km-retained | whelk-cold | 687 | 0.9513 | 5.181 | 10.59 | 64.96 | 190.6 | 2.883 |
| updates | km-retained | whelk-retained | 683 | 0.9073 | 1.376 | 2.557 | 64.96 | 209.7 | 4.196 |


**Justification coverage**

The frozen panel contains 80 ontologies. Preparation failures and sources without eligible inferred queries are not replaced.

| Ontology outcome | Count |
| --- | --- |
| eligible_queries | 42 |
| no_eligible_inferred_queries | 14 |
| query_preparation_failed | 24 |


| Method | adapter_or_validation_error | generation_error | generation_timeout | verified_evidence_intact |
| --- | --- | --- | --- | --- |
| elk | 6 | 0 | 0 | 366 |
| hermit | 0 | 0 | 0 | 372 |
| jfact | 0 | 9 | 9 | 354 |
| km | 0 | 18 | 18 | 336 |
| konclude | 0 | 0 | 123 | 249 |
| more | 0 | 0 | 108 | 264 |
| openllet | 0 | 0 | 0 | 372 |
| rustdl | 0 | 0 | 3 | 369 |
| sequoia | 0 | 156 | 9 | 207 |
| whelk | 9 | 0 | 45 | 318 |


**Justification comparisons with KM**

Cost pairs require independently verified source membership, entailment, and subset-minimality for both results on the same source, query, and repetition. Generation cost is separate from verification.

| Phase | Left | Right | Paired cases | Left s | Right s | Time right/left | Left MiB | Right MiB | Memory right/left |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
|  | elk | km | 333 | 3.024 | 0.07511 | 0.02153 | 128.3 | 9.062 | 0.06617 |
|  | hermit | km | 336 | 2.635 | 0.07603 | 0.02602 | 116.3 | 9.062 | 0.07419 |
|  | jfact | km | 327 | 3.714 | 0.07438 | 0.01799 | 155.3 | 8.438 | 0.05518 |
|  | km | konclude | 249 | 0.04511 | 15.79 | 320.5 | 8.125 | 136.5 | 16.81 |
|  | km | more | 264 | 0.04543 | 12.14 | 237.9 | 8.125 | 110.7 | 13.61 |
|  | km | openllet | 336 | 0.07603 | 2.8 | 38.71 | 9.062 | 117.5 | 13.27 |
|  | km | rustdl | 336 | 0.07603 | 0.04291 | 0.7464 | 9.062 | 5.312 | 0.6296 |
|  | km | sequoia | 207 | 0.04474 | 22.86 | 494.2 | 7.812 | 213 | 26.87 |
|  | km | whelk | 309 | 0.07348 | 2.621 | 52.91 | 8.438 | 122.7 | 15.02 |


**Verified support sizes and verification costs**

These descriptive medians cover each reasoner’s verified cases, which may differ. Use the paired table above for generation-cost comparisons.

| Reasoner | Verified cases | Median logical axioms | Median verification s |
| --- | --- | --- | --- |
| elk | 366 | 3 | 3.084 |
| hermit | 372 | 3 | 5.006 |
| jfact | 354 | 3 | 3.047 |
| km | 336 | 3 | 3.072 |
| konclude | 249 | 2 | 2.882 |
| more | 264 | 2 | 2.841 |
| openllet | 372 | 3 | 3.026 |
| rustdl | 369 | 3 | 2.976 |
| sequoia | 207 | 2 | 2.918 |
| whelk | 318 | 3 | 2.954 |


**Preparation costs**

Shared preparation is reported once per source or module, separately from all repetitions. Reused reference stages retain their original timing. No costs are silently amortized.

The report includes 124 modules, totaling 24018681 bytes. The JSON supplement retains individual source/module sizes and all preparation receipts. The following totals include recorded failures and are not added to each repetition.

| Stage | Recorded stages | Timed stages | Total recorded s | Maximum recorded MiB |
| --- | --- | --- | --- | --- |
| Konclude classification conversion | 1920 | 1920 | 2.593e+04 | 2348 |
| Konclude update conversion | 395 | 395 | 6497 | 1993 |
| MORe module consistency preparation | 124 | 124 | 357.8 | 185.8 |
| frozen HermiT reference | 71 | 71 | 1161 | 2143 |
| query compile | 80 | 80 | 213.5 | 107.9 |
| query modules | 71 | 71 | 9616 | 1201 |
| update preparation including compilation | 80 | 80 | 3885 | 4576 |


**Outstanding evidence review**

| Panel | Recorded issues requiring review |
| --- | --- |
| classification | 5798 |
| incremental | 12018 |
| justification | 0 |


Issue counts include missing evidence, preparation failures, and disagreements as recorded by each reporter. They do not replace inspection of individual outcomes.


**Selected measurement runs**

Each panel is checked against the selected runs it actually consumes. Original JSON reports retain their complete historical run sets; rerunning one panel does not relabel another panel’s evidence.

| Run-set field | Selected artifact or job |
| --- | --- |
| classification | 53200614 |
| classification_km | 53234829 |
| classification_konclude | 53201252 |
| inventory | artifact-inventory-v145-global-dependency.json |
| justifications_external | 53203745 |
| justifications_java | 53201375 |
| justifications_km | 53234831 |
| justifications_native | 53201976 |
| justifications_whelk | 53204206 |
| queries_preparation | 53201195 |
| retained_konclude | 53214508 |
| updates_java | 53201374 |
| updates_km | 53234830 |
| updates_konclude | 53202853 |
| updates_native | 53201456 |
| updates_preparation | 53201177 |
| updates_whelk | 53204205 |

**Input report hashes**

| File | SHA-256 |
| --- | --- |
| classification-report-v4-full-global-dependency-53234888.json | 640d6458f54986e94a281c1a885553cc300355ddd94550cf49ce4a35b03ec4d3 |
| updates-report-v5-full-global-dependency-53234889.json | 559a03d9635cd257ec776e6200b9b0153f80693d9fd345f8082f3e7c447369f1 |
| justification-report-v4-full-global-dependency-53234890.json | 8ccf0ed781bbd973522cb756dbaab3a5de7f5cee1623eb7c1dc154c2bac0cc9d |
| preparation-report-v2-full-global-dependency-53234930.json | 7ef57afbe843057e0c6c9ecd5a0f3077bde89f0db71cbd484f9a534041228f14 |
| run-set-global-dependency.json | 9c9a27c6645573907f8fb873ef4fa2ae2b4588e2f6aa62f7b5639f12fbf60853 |
