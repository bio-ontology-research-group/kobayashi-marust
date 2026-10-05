# v1.4.5 benchmark results: counts and times

**Limits: 240 seconds per attempt, 20 GiB memory, one CPU.** Times below are
wall-clock seconds. “Average” is the arithmetic mean; “median” is the middle
recorded time. Both use only the verified solved attempts in that row.

For classification and updates, **verified solved** means a complete audited
answer with known consistency that agrees with at least one different full-DL
reasoner (KM, HermiT, Konclude, Openllet, or JFact). Complete outputs without
that corroboration appear only in the output column. This conservative count
does not incorporate separate case-specific proofs or treat unknown consistency
as agreement. For justifications, solved means independently verified source
membership, entailment, and subset-minimality.

Failed and timed-out attempts remain in the denominators. The successful
subsets differ between reasoners, so read the times together with the solved
counts; a low average alone does not imply better overall coverage.

### Classification

The corpus contains **1,920 inputs: 1,708 pass the input checks and 212 are
invalid**. The table counts the 1,708 admitted inputs; invalid-input refusals
are reported separately and do not count as solved ontologies.

| Reasoner | Complete outputs | Verified solved / attempts | Average time (s) | Median time (s) |
|---|---:|---:|---:|---:|
| KM | 1,594 | 1,591 / 1,708 | 10.892 | 0.691 |
| ELK | 1,701 | 1,411 / 1,708 | 11.971 | 4.777 |
| HermiT | 1,540 | 1,539 / 1,708 | 15.764 | 4.988 |
| JFact | 1,238 | 1,101 / 1,708 | 17.430 | 5.208 |
| Konclude | 1,697 | 1,655 / 1,708 | 2.923 | 0.269 |
| MORe | 1,584 | 0 / 1,708 | n/a | n/a |
| Openllet | 1,411 | 1,402 / 1,708 | 16.335 | 4.890 |
| RustDL | 1,220 | 1,212 / 1,708 | 5.139 | 0.331 |
| Sequoia | 630 | 629 / 1,708 | 18.676 | 7.375 |
| Whelk | 1,647 | 1,380 / 1,708 | 17.705 | 6.198 |

MORe produces taxonomy outputs but its adapter does not establish consistency,
so these outputs do not enter the verified column. KM's three uncorroborated
outputs are ORE 1194, 3794, and 4669; the full evidence includes the separate
adjudications for 3794 and 4669. They are excluded by the same automatic
corroboration rule used for every reasoner in this summary.

### Incremental reasoning

**80 sources × four updates × three repetitions = 960 update attempts per
method.** One source failed preparation; its 12 update attempts remain in the
denominator. Repeated runs count separately, so these are update attempts,
not 960 distinct ontologies. Initialization is excluded from the table and
reported separately in the full summary.

Fresh-process rows restart the reasoner for each revision. Retained-session
rows keep the process running across revisions. RustDL, MORe, and Sequoia have
fresh-process results only.

| Reasoner | Mode | Complete outputs | Verified solved / attempts | Average time (s) | Median time (s) |
|---|---|---:|---:|---:|---:|
| KM | Fresh process | 918 | 906 / 960 | 13.066 | 0.784 |
| KM | Retained session | 821 | 821 / 960 | 16.276 | 0.646 |
| ELK | Fresh process | 925 | 769 / 960 | 14.670 | 5.655 |
| ELK | Retained session | 924 | 768 / 960 | 6.778 | 1.274 |
| HermiT | Fresh process | 852 | 852 / 960 | 17.664 | 5.006 |
| HermiT | Retained session | 852 | 852 / 960 | 10.532 | 1.370 |
| JFact | Fresh process | 636 | 564 / 960 | 14.172 | 4.324 |
| JFact | Retained session | 636 | 540 / 960 | 12.988 | 0.474 |
| Konclude | Fresh process | 936 | 936 / 960 | 4.147 | 0.318 |
| Konclude | Retained session | 930 | 896 / 960 | 10.517 | 0.542 |
| MORe | Fresh process | 862 | 0 / 960 | n/a | n/a |
| Openllet | Fresh process | 739 | 727 / 960 | 13.142 | 4.620 |
| Openllet | Retained session | 725 | 713 / 960 | 5.624 | 0.911 |
| RustDL | Fresh process | 647 | 647 / 960 | 6.203 | 0.452 |
| Sequoia | Fresh process | 348 | 348 / 960 | 14.992 | 8.432 |
| Whelk | Fresh process | 912 | 768 / 960 | 22.214 | 6.847 |
| Whelk | Retained session | 908 | 764 / 960 | 14.557 | 2.286 |

A retained process does not guarantee internal reuse. Of KM's 948 prepared
post-initialization attempts, 206 used incremental updates and 615 rebuilt
exactly; 121 were skipped after session failure and six timed out. The 12
completed cold KM update outputs on ORE 1194 lack an independent reference and
are excluded from the verified count. Fresh and retained rows can solve
different subsets; their separate averages are not a paired speedup measure.

### Initialization of the incremental workload

80 sources × three repetitions = 240 attempts per method, including the three
attempts lost to the preparation failure. These times are separate from the
four later updates.

| Reasoner | Mode | Complete outputs | Verified solved / attempts | Average time (s) | Median time (s) |
|---|---|---:|---:|---:|---:|
| KM | Fresh process | 231 | 228 / 240 | 13.053 | 0.828 |
| KM | Retained session | 210 | 210 / 240 | 15.376 | 0.483 |
| ELK | Fresh process | 231 | 192 / 240 | 14.201 | 5.379 |
| ELK | Retained session | 231 | 192 / 240 | 15.798 | 6.050 |
| HermiT | Fresh process | 213 | 213 / 240 | 17.581 | 5.020 |
| HermiT | Retained session | 213 | 213 / 240 | 17.859 | 5.377 |
| JFact | Fresh process | 159 | 141 / 240 | 14.234 | 4.341 |
| JFact | Retained session | 159 | 138 / 240 | 17.777 | 4.842 |
| Konclude | Fresh process | 234 | 234 / 240 | 4.053 | 0.323 |
| Konclude | Retained session | 234 | 231 / 240 | 15.217 | 0.633 |
| MORe | Fresh process | 214 | 0 / 240 | n/a | n/a |
| Openllet | Fresh process | 184 | 181 / 240 | 13.313 | 4.594 |
| Openllet | Retained session | 182 | 179 / 240 | 12.263 | 4.688 |
| RustDL | Fresh process | 161 | 161 / 240 | 6.342 | 0.466 |
| Sequoia | Fresh process | 87 | 87 / 240 | 15.093 | 8.541 |
| Whelk | Fresh process | 227 | 191 / 240 | 21.268 | 5.800 |
| Whelk | Retained session | 227 | 191 / 240 | 21.931 | 6.521 |

### Justifications

**124 queries × three repetitions = 372 attempts per reasoner.** These queries
come from 42 of the 80 selected sources; 24 sources failed preparation and 14
had no eligible query. Those sources were not replaced. Times measure
justification generation; independent verification has its own 240-second
limit and is reported separately.

| Reasoner | Verified solved / attempts | Average time (s) | Median time (s) |
|---|---:|---:|---:|
| KM | 336 / 372 | 0.268 | 0.076 |
| ELK | 366 / 372 | 3.516 | 3.094 |
| HermiT | 372 / 372 | 3.184 | 2.796 |
| JFact | 354 / 372 | 5.913 | 3.754 |
| Konclude | 249 / 372 | 30.109 | 15.791 |
| MORe | 264 / 372 | 30.529 | 12.140 |
| Openllet | 372 / 372 | 3.323 | 2.836 |
| RustDL | 369 / 372 | 1.636 | 0.043 |
| Sequoia | 207 / 372 | 36.786 | 22.856 |
| Whelk | 318 / 372 | 7.315 | 2.659 |

### Validation and detailed evidence

The measured v1.4.5 candidate passed 2,835 Rust tests (8 ignored), 31 Java
tests, plugin installation checks, all four Lean certification gates without
`sorryAx`, and 68 benchmark-harness tests. The detailed reports retain failed
measurements, raw disagreements, preparation costs, and verification costs.
Earlier 592-input ORE benchmark results used different panels and validation
rules and should not be compared directly with these totals.

## Reproduce and inspect the summary

The [JSON summary](benchmark-counts-times.json) includes every counted attempt,
its wall time, whether it was corroborated, reference names, and receipt hashes.
The [aggregation script](summarize_counts_times.py) reads the existing frozen
audit and measurement metadata; it does not rerun any reasoner:

```sh
python3 summarize_counts_times.py /path/to/v145-comparative-20261004 new-summary.json
```

The output path must not already exist. The JSON records the source-report
hashes and exact counting rule. Times are recomputed from individual measured
wall times, not reconstructed from previously published ratios.

See the [original detailed comparison report](benchmark-report-53234931.md)
for paired comparisons, preparation costs, verification costs, and workload
provenance. All original measurements and audits remain unchanged.
