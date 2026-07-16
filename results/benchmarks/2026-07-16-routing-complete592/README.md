# Complete ORE routing matrix, 2026-07-16

The frozen `c229366f` matrix contains all 592 ORE ontology panels and all 28
rows per panel (16,576 measurements). Every panel passed the atomic structural
validator. The 13 panels lost in the original sharded run were repaired by
Slurm array job `48975292`; every procedure ran in a separate 20 GB Slurm step
on the same Intel Xeon Gold 6248 node as the rest of its panel.

Frozen provenance:

- KM binary SHA-256:
  `c229366fcc9efbfec729f5a7dcc1a5f1ef9b12fe41f433b67282930bf18a92f6`
- runner SHA-256:
  `3b1d2a878cae0e79f66de34fed4cd5c9dce1e457c958a5ce10d579217549c9d0`
- profile corpus SHA-256:
  `882135553516746e06698f02f1d402c0060eaeaae84d011e724787bf8929dd72`
- CPU: Intel Xeon Gold 6248, 16 allocated CPUs per panel
- timeout: 240 seconds per route
- memory cap: 20,480 MB per route

`route-performance.csv` and `route-performance.json` report pass rate and
average, median, and p95 wall time and peak RSS. Time and memory distributions
use successful (`status=ok`) rows, following the repository benchmark rule.
The successful-row count must therefore be read with every average.

## Main comparison

| route | ok / 592 | wall avg s | wall med s | memory avg MB | memory med MB |
|---|---:|---:|---:|---:|---:|
| Konclude 16 threads | 588 | 2.129 | 0.264 | 738 | 245 |
| Konclude 1 thread | 588 | 2.483 | 0.265 | 590 | 143 |
| ELK | 579 | 1.995 | 0.824 | 611 | 349 |
| HermiT | 545 | 13.196 | 1.851 | 1,392 | 745 |
| KM CB absorb 16 | 536 | 4.442 | 0.273 | 1,139 | 133 |
| KM CB absorb 8 | 537 | 5.882 | 0.317 | 879 | 105 |
| KM CB absorb 1 | 517 | 11.367 | 0.419 | 420 | 67 |
| KM CB plain 16 | 537 | 4.643 | 0.319 | 1,136 | 138 |
| KM CB plain 8 | 536 | 5.839 | 0.317 | 872 | 109 |
| KM CB plain 1 | 517 | 11.403 | 0.429 | 425 | 69 |
| KM trigger 16 | 537 | 4.698 | 0.325 | 1,158 | 134 |
| KM trigger 8 | 537 | 6.013 | 0.317 | 896 | 104 |
| KM trigger 1 | 518 | 11.835 | 0.461 | 433 | 70 |
| KM ELC | 392 | 3.075 | 0.263 | 296 | 35 |
| KM ELC certificate | 467 | 3.111 | 0.215 | 267 | 30 |
| KM lean | 487 | 10.402 | 0.509 | 358 | 68 |
| KM nominals | 479 | 7.740 | 0.367 | 971 | 146 |
| KM sequence on | 537 | 4.464 | 0.312 | 1,136 | 138 |
| KM sequence off | 526 | 4.608 | 0.320 | 1,112 | 136 |
| KM HT bridge | 505 | 4.921 | 0.266 | 475 | 48 |
| KM HT full | 518 | 4.796 | 0.266 | 464 | 44 |
| KM HT features | 399 | 11.731 | 0.421 | 575 | 111 |
| KM HT general | 378 | 12.284 | 0.469 | 606 | 128 |
| KM HT rules | 537 | 4.899 | 0.320 | 1,215 | 139 |

The specialist `ht_qo`, `ht_shoq`, `ht_card`, and `card_fn` routes accept only
14, 19, 8, and 10 ontologies respectively. Their averages are present in the
CSV but are not corpus-level competitors.

## Strict correctness audit

The strict analyzer verified 592 result files, no missing or duplicate rows,
one CPU model, one KM binary, one runner, valid route provenance, and the
expected 587 Konclude-gold plus five no-Konclude-gold contract.

It deliberately returned exit code 2 because none of the five no-gold
ontologies could be independently adjudicated by HermiT in this run:

- 10860: unsupported
- 1194: timeout
- 15703: error
- 3524: error
- 4669: timeout

The benchmark and performance comparison are complete. Correctness claims for
those five remain explicitly unadjudicated; a `nogold` result was not promoted
to a match. The complete strict audit output is retained in
`strict-analysis-audit.log`.
