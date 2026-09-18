# Selected justification comparison

The final comparison contains 7,650 measured attempts on five prepared ontologies, five queries per ontology, full and STAR-module tracks, bounds 1/10/100, and five measured repetitions. ELK and Whelk cover only the three EL ontologies. TO, Uberon and MRO preparation failures remain in panel.tsv; they are not silently replaced.

The archive contains 13,680 attempts including warmups, baseline KM and superseded common-driver runs. The comparison_selected column removes superseded attempts. Selecting final KM removes a further 1,500 measured baseline KM attempts, leaving the 7,650 below.

| Service | Measured | Correct | Timeout | Error |
|---|---:|---:|---:|---:|
| elk-common | 450 | 300 | 150 | 0 |
| hermit-common | 750 | 517 | 233 | 0 |
| hermit-library | 750 | 710 | 40 | 0 |
| jfact-common | 750 | 450 | 299 | 1 |
| jfact-library | 750 | 710 | 40 | 0 |
| km-common | 750 | 373 | 362 | 15 |
| km-native | 750 | 675 | 0 | 75 |
| konclude-common | 750 | 431 | 287 | 32 |
| openllet-common | 750 | 450 | 300 | 0 |
| openllet-library | 750 | 668 | 82 | 0 |
| whelk-common | 450 | 290 | 160 | 0 |

Correct means the returned supports passed the independent subset, entailment, deletion-minimality and logical-normalization audit. It does not establish complete enumeration. Errors remain errors, including KM internal worker deadlines reported as errors and Konclude unsupported-input/parse errors.

Native, library and common-extractor services are separate comparisons. Full versus module and each bound remain separate in the detailed report. Counts above summarize coverage only; they do not establish an overall performance ranking. Paired wall-time ratios admit only verified, compatible support targets and cases with all five measured repetitions. Ratios above one favor KM on those admitted cases.

The corrected KM and Konclude common-driver cohorts ran later. Scheduling caps changed after capacity checks. Cache state and shared-resource contention can affect these phase-separated timings; cohort revisions are retained in paired-wall.tsv. These runs are not interchangeable repetitions.

Parent review independently checked selected-key uniqueness, final KM selection, input identity, cohort provenance, eligibility, all 12,300 paired rows and case-median ratios. See parent-comparison-review.json and review-final-justification.py. The raw reports remain unchanged.

## Memory measurements

selected-memory-cases.tsv summarizes sampled peak process-tree RSS for all
1,530 selected cases, preserving source, ontology, query, track, bound and service.
Each case retains its five-attempt denominator and execution counts. Separate
columns describe all positive observations and only verified eligible attempts.
Seven recorded zero samples are treated as unavailable measurements, not zero
memory use. Raw values remain unchanged in attempts.tsv. Sampling can miss brief
peaks; this is not an operating-system high-water mark. There are 1,082 cases
with five verified positive samples. Conditional summaries must be read with
coverage; failed attempts are not evidence of memory efficiency.
