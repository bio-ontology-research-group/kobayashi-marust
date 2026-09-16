# v1.4.0 release validation

The benchmark audit, all four production certification gates, and the Rust
and plugin regression checks pass for this release.

## Tested source and binary

- Engine commit: `edb1721`.
- Source archive SHA-256:
  `211852a77a8b90a0e710910500cabe4f7b1bd1ced7f35a28d79c846eee91077d`.
- Binary SHA-256:
  `ddc30d2f9013b371b5c4ec19c0623c91ecc1b2dbdc172ded9002fd238903d09a`.
- IBEX build: `51947351`; automatic sweep: `51947388`.
- Evidence root: `/ibex/scratch/hohndor/km/v140-release-final-20260916/`.
- Limits: 240 seconds per input, 20 GiB process-tree memory, 16 allocated CPUs
  on Intel Xeon Gold 6248 nodes.

The audit verifies 592 unique results, 592 matching checkpoints, and 592
completion markers from the pinned binary. All statuses are `ok`: 588 retained
signature matches, two adjudicated consistency disagreements (2669 and 15516),
and two inputs without retained external full-taxonomy gold (10860 and 1194).
No semantic field differs from the accepted integrated sweep `51341068`.
ORE1194 completes in 127.7150 seconds at 16,840.31 MiB. This establishes
completion, not external gold agreement. ORE10860 has an independently checked
inconsistency argument. Full contemporary Uberon remains an open task.

## Comparison

| Reasoner | Tested version / commit | Completions used | Mean time (s) | Median time (s) | Mean peak RSS (MiB) | Median peak RSS (MiB) |
|---|---|---:|---:|---:|---:|---:|
| KM | v1.4.0; `edb1721`; binary `ddc30d2f…8903d09a` | 592/592 | 1.4765 | 0.1046 | 206.29 | 22.59 |
| ELK | 0.6.0 | 531/592 | 1.5208 | 0.7520 | 493.33 | 234.30 |
| Konclude | v0.7.0-1138; `0002e8063540` | 587/592 | 3.2765 | 0.2814 | 559.90 | 76.87 |
| Sequoia | 0.6.1-alpha; `c5248ec7be30` | 339/592 | 7.3704 | 2.5371 | 2207.35 | 536.15 |
| HermiT | 1.4.6.519-SNAPSHOT | 557/592 | 13.1172 | 1.8782 | 1331.72 | 714.22 |

KM includes all 592 completions with the validation limitations above. Baselines
use their retained correct-completion subsets from the
[v1.3.0 comparison](https://github.com/bio-ontology-research-group/kobayashi-marust/blob/v1.3.0/README.md#ore-2015-benchmark).
They were not rerun for this release. These are different populations, not
paired per-ontology speedups. Time is reasoner wall time; memory is peak
process-tree RSS. Output validation and cleanup occur outside that interval.

Machine-readable evidence: [summary](summary.json), [comparison](comparison.tsv),
[per-ontology rows](per-ontology.tsv), [build receipt](build-receipt.tsv),
[audit program](audit.py), [build job](ibex-build.sbatch), and
[sweep job](ibex-sweep.sbatch). [Validation summary](validation.json) records
the certification and test results. Release assets include the raw benchmark
records, checkpoints, logs, and semantic reference rows in `baseline-results/`,
plus validation logs and a SHA-256 manifest.

The semantic reference is the final routing replay documented in
[`../2026-09-04-v14-frontend-allocation/README.md`](../2026-09-04-v14-frontend-allocation/README.md).
Its raw result directory is retained locally under
`../v1.4/.work/artifacts/v14-final-routing/extracted/full-sweep/results` relative
to the release worktree. This release's metrics use the fresh 240-second run.

## Release checks

The initial routing gate caught batch ABox elision reaching incremental
sessions, which then rebuilt instead of retaining their positive-EL state.
Commit `edb1721` preserves complete typed ABox data during incremental
normalization and restores the caller's environment. The strengthened
regression checks the actual retained backend and an inconsistent add/remove
cycle. All 18 focused incremental-source tests pass. The final binary received
its own complete sweep after this fix.

All four production Lean gates pass on the final production source: ELC, HT,
CB, and automatic routing, including incremental and explanation publication.
The captured axiom audits reject `sorryAx` and report only `propext`,
`Classical.choice`, and `Quot.sound`.

The general Rust library suite passes 2,405 tests, with eight intentional
ignores and 22 native-checker tests filtered as in CI. The certification gates
run their checker-dependent tests with the required native executables. All
13 remaining integration targets pass (59 tests). A source-scanning guard was
corrected to recognize the static `OnceLock` initializer already present in
the completion context; its regressions still reject uncached reads. That
test-only change does not alter the benchmarked production code.

The plugin has passed 31 tests, packaged-bundle
verification, and a stock Protégé 5.6.6 installation smoke using the exact IBEX
binary. The smoke exercises native classification, a retained non-buffering
update, and a source-axiom explanation.

The native Linux x86-64 archive requires glibc 2.34 or newer. The source
release contains Lean sources and the certification gates. Certification
scope is described in the main README.
