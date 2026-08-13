# Positive-EL ABox routing candidate

Candidate commit `e9cb3d1` extends the source-certified EL route to positive
ABoxes only when `positive_el_abox_materializable` is true. The orchestrator
first decides ABox consistency against the completed EL model; the atomic EL
worker then validates and classifies the source-certified EL terminology.
Nominals, identity constraints, non-EL constructors, and uncertified ABoxes
continue to fail closed to the production portfolio.

## Source binding

- Candidate commit: `e9cb3d1`
- Release-source test repair: `4cd0baf` (test-only; production binary unchanged)
- IBEX-native candidate binary SHA-256:
  `6dc20602cb531f5a19bc688da5ce4b2e74da18bec95d858574c43128488a42a1`
- Source archive SHA-256:
  `fedccde87a2970ecc21dab4faeef3f13492dec3375ce5de89b24a11ec49bd1df`
- Baseline release: `v0.2.6` at commit `6e6a86f`
- Baseline binary SHA-256:
  `7ac98a33a26579d9a2e3abaf95dfd8fba44e2dc842db1d12ce65144dd1a5c0f1`
- CPU: Intel Xeon Gold 6248 at 2.50 GHz
- Per-classification limits: 240 seconds and 20 GiB

Slurm job `50081319` built the candidate from the hash-checked source archive
on IBEX. The workstation artifact was rejected before classification because
it required GLIBC 2.39; failed panel jobs `50081234` and earlier scheduling
attempts provide no accepted measurements.

## Complete changed-route panel

Job `50081491` ran paired baseline and candidate classifications for all 38
ontologies predicted to change from `production_all` to `elc`. Pair order was
reversed by array parity. The harness required exact binary hashes, the
expected route transition, terminal checkpoints, a `match` verdict, and
equality of every semantic result field.

All 38 pairs passed, producing 76 result records and 76 checkpoints with no
temporary files:

| Metric | v0.2.6 | Candidate | Change |
|---|---:|---:|---:|
| Mean wall time | 15.4353 s | 11.2102 s | -27.4% |
| Median wall time | 9.0430 s | 5.2555 s | -41.9% |
| Mean peak RSS | 2,234.36 MiB | 1,425.40 MiB | -36.2% |
| Median peak RSS | 1,542.80 MiB | 637.64 MiB | -58.7% |

`paired-results.tsv` and `panel-summary.json` retain the accepted aggregate.

The issue #3 pigeonhole regression was separately rerun against the candidate.
Its profile remains uncertified for this route, selects `production_all`, and
classification reports `consistent: false` with no dropped clauses.

The complete locked release suite at `4cd0baf` passes with 1,959 tests passed,
8 ignored, and no failures. Rebuilding the production binary after the
test-only repair preserves the pre-repair workstation binary SHA-256 exactly.

## Full sweep

Strict 592-ontology Slurm job `50081854` completed with one
result/profile/checkpoint triple per ontology and no temporary files. Both
validators passed:

- 591 `ok`; ORE1194 remains the sole fail-closed `error`.
- Zero semantic or coverage regressions against v0.2.6.
- Exactly 38 `production_all` to `elc` route changes.
- Independent debug semantic sweep `50082018` reproduced the same complete
  semantic comparison.

| Metric | v0.2.6 | Candidate |
|---|---:|---:|
| Mean wall time | 5.1787 s | 5.3111 s |
| Median wall time | 0.2467 s | 0.2485 s |
| Mean peak RSS | 720.08 MiB | 666.29 MiB |
| Median peak RSS | 42.02 MiB | 42.64 MiB |

The 38 changed ontologies themselves saved 119.58 summed wall seconds and
30,823 MiB of summed peak RSS. The 553 unchanged successful ontologies were
197.80 summed seconds slower in this independent candidate run, which outweighed
the changed-route timing gain. Because three of four full-sweep aggregate
metrics did not improve, this candidate was not released by itself. Its code is
retained in the broader `2a32741` candidate, which adds another 60 exact ELC
route changes before repeating the release gate.
