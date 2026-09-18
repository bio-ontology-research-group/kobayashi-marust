# Justification comparison

VALIDATION ONLY: fixture/partial evidence; not main performance.

Scheduled: 234 attempts (195 measured, 39 warmups). Extraction terminal: 234/234. Independently verified with normalization and bindings: 234/234.
Matrix execution complete: True. Integrity issues: 0. Semantic success is separate from execution completeness.

| Source | Track | Bound | Arm | Scheduled measured | Terminal | Verified | Timing eligible |
|---|---|---:|---|---:|---:|---:|---:|
| EARLY-REVIEW-baseline | module | 1 | elk-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 1 | hermit-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 1 | hermit-library | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 1 | jfact-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 1 | jfact-library | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 1 | km-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 1 | km-native | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 1 | konclude-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 1 | openllet-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 1 | openllet-library | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 1 | whelk-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 10 | elk-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 10 | hermit-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 10 | hermit-library | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 10 | jfact-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 10 | jfact-library | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 10 | km-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 10 | km-native | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 10 | konclude-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 10 | openllet-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 10 | openllet-library | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 10 | whelk-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 100 | elk-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 100 | hermit-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 100 | hermit-library | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 100 | jfact-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 100 | jfact-library | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 100 | km-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 100 | km-native | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 100 | konclude-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 100 | openllet-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 100 | openllet-library | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-baseline | module | 100 | whelk-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-final | module | 1 | km-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-final | module | 1 | km-native | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-final | module | 10 | km-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-final | module | 10 | km-native | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-final | module | 100 | km-common | 5 | 5 | 5 | 5 |
| EARLY-REVIEW-final | module | 100 | km-native | 5 | 5 | 5 | 5 |

## Paired process wall times

Each ratio is peer wall time divided by KM wall time. Values above1 favor KM on the stated matched cases. A case enters only if all five measured repetitions have compatible, independently verified outputs. The summary uses the median of these five-repetition case medians; incomplete cases stay in the denominator.

| Track | Bound | KM mechanism | Peer mechanism | Complete cases / expected | Median ratio | Case ratio IQR |
|---|---:|---|---|---:|---:|---:|
| module | 1 | km-common | elk-common | 1 / 1 | 1.175 | 0 |
| module | 1 | km-common | hermit-common | 1 / 1 | 1.037 | 0 |
| module | 1 | km-common | hermit-library | 0 / 1 | NA | NA |
| module | 1 | km-common | jfact-common | 1 / 1 | 1.678 | 0 |
| module | 1 | km-common | jfact-library | 0 / 1 | NA | NA |
| module | 1 | km-common | konclude-common | 1 / 1 | 1.348 | 0 |
| module | 1 | km-common | openllet-common | 1 / 1 | 1.177 | 0 |
| module | 1 | km-common | openllet-library | 0 / 1 | NA | NA |
| module | 1 | km-common | whelk-common | 1 / 1 | 1.087 | 0 |
| module | 1 | km-native | elk-common | 1 / 1 | 35.04 | 0 |
| module | 1 | km-native | hermit-common | 1 / 1 | 29.22 | 0 |
| module | 1 | km-native | hermit-library | 1 / 1 | 29.68 | 0 |
| module | 1 | km-native | jfact-common | 1 / 1 | 47.24 | 0 |
| module | 1 | km-native | jfact-library | 1 / 1 | 45.93 | 0 |
| module | 1 | km-native | konclude-common | 1 / 1 | 38.78 | 0 |
| module | 1 | km-native | openllet-common | 1 / 1 | 33.14 | 0 |
| module | 1 | km-native | openllet-library | 1 / 1 | 32.66 | 0 |
| module | 1 | km-native | whelk-common | 1 / 1 | 30.58 | 0 |
| module | 10 | km-common | elk-common | 1 / 1 | 1.176 | 0 |
| module | 10 | km-common | hermit-common | 1 / 1 | 0.9957 | 0 |
| module | 10 | km-common | hermit-library | 0 / 1 | NA | NA |
| module | 10 | km-common | jfact-common | 1 / 1 | 1.623 | 0 |
| module | 10 | km-common | jfact-library | 0 / 1 | NA | NA |
| module | 10 | km-common | konclude-common | 1 / 1 | 1.447 | 0 |
| module | 10 | km-common | openllet-common | 1 / 1 | 1.113 | 0 |
| module | 10 | km-common | openllet-library | 0 / 1 | NA | NA |
| module | 10 | km-common | whelk-common | 1 / 1 | 1.075 | 0 |
| module | 10 | km-native | elk-common | 1 / 1 | 35.34 | 0 |
| module | 10 | km-native | hermit-common | 1 / 1 | 29.14 | 0 |
| module | 10 | km-native | hermit-library | 0 / 1 | NA | NA |
| module | 10 | km-native | jfact-common | 1 / 1 | 48.36 | 0 |
| module | 10 | km-native | jfact-library | 0 / 1 | NA | NA |
| module | 10 | km-native | konclude-common | 1 / 1 | 42.72 | 0 |
| module | 10 | km-native | openllet-common | 1 / 1 | 33.1 | 0 |
| module | 10 | km-native | openllet-library | 0 / 1 | NA | NA |
| module | 10 | km-native | whelk-common | 1 / 1 | 31.31 | 0 |
| module | 100 | km-common | elk-common | 1 / 1 | 1.204 | 0 |
| module | 100 | km-common | hermit-common | 1 / 1 | 0.9705 | 0 |
| module | 100 | km-common | hermit-library | 0 / 1 | NA | NA |
| module | 100 | km-common | jfact-common | 1 / 1 | 1.661 | 0 |
| module | 100 | km-common | jfact-library | 0 / 1 | NA | NA |
| module | 100 | km-common | konclude-common | 1 / 1 | 1.467 | 0 |
| module | 100 | km-common | openllet-common | 1 / 1 | 1.127 | 0 |
| module | 100 | km-common | openllet-library | 0 / 1 | NA | NA |
| module | 100 | km-common | whelk-common | 1 / 1 | 1.05 | 0 |
| module | 100 | km-native | elk-common | 1 / 1 | 35.23 | 0 |
| module | 100 | km-native | hermit-common | 1 / 1 | 29.13 | 0 |
| module | 100 | km-native | hermit-library | 0 / 1 | NA | NA |
| module | 100 | km-native | jfact-common | 1 / 1 | 49.4 | 0 |
| module | 100 | km-native | jfact-library | 0 / 1 | NA | NA |
| module | 100 | km-native | konclude-common | 1 / 1 | 44.03 | 0 |
| module | 100 | km-native | openllet-common | 1 / 1 | 33.09 | 0 |
| module | 100 | km-native | openllet-library | 0 / 1 | NA | NA |
| module | 100 | km-native | whelk-common | 1 / 1 | 31.53 | 0 |

Per-case latency median, min/max, IQR and MAD are in [cases.tsv](cases.tsv); all outcomes and support counts are in [attempts.tsv](attempts.tsv). Runtime and source hashes are in [runtime-bindings.tsv](runtime-bindings.tsv).

## Preparation outcomes

| Source | Ontology | Fragment | Status |
|---|---|---|---|
| EARLY-REVIEW-baseline | mmo | EL | prepared |
| EARLY-REVIEW-baseline | hao | EL | prepared |
| EARLY-REVIEW-baseline | vto | EL | prepared |
| EARLY-REVIEW-baseline | mfomd | pure_DL | prepared |
| EARLY-REVIEW-baseline | to | DL+rules | preparation_unavailable |
| EARLY-REVIEW-baseline | uberon | DL+rules | preparation_unavailable |

## Reading the files

Only repetitions 1–5 enter case dispersion and paired ratios; repetition 0 is a filesystem-cache warmup in a fresh process. Full ontologies and STAR modules, extraction mechanisms and bounds remain separate. Limit 1 end-to-end wall time measures user-facing first-justification latency; Java internal first/extraction times are retained only as diagnostic columns and are never mixed with native wall time.

Timeouts, resource failures, errors, missing attempts and verification failures are counted explicitly. A timeout is censored at the recorded wall limit, never a zero-time or zero-support success. False positive-query responses are ineligible. Unknown library enumeration is never treated as complete. Native occurrence counts and normalized distinct logical-support counts remain separate; duplicate inflation excludes bounded-enumeration timing comparisons.

Per-case TSV records median, min/max, IQR and median absolute deviation over eligible repetitions, alongside the required five-repetition denominator. Paired ratios use only matching query/source/repetition/track/bound and compatible completed support targets. They compare common extractors, or native KM against the named service; they do not pool mechanisms. No pooled conditional median is presented as an overall speed winner.

artifacts.tsv lists frozen task, audit, normalization and driver-receipt hashes. Driver manifests bind source code, compiled classes, runtime JARs and native binaries. Matrix completeness does not certify calculus correctness or establish a release gate.
