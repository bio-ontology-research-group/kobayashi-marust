# Certified flat-taxonomy EL routing

KM now recognizes source ontologies whose logical axioms consist only of
nonempty, flat named-class `SubClassOf` edges and routes them directly to the
exact EL completion worker. External expressivity labels can conservatively
overstate these inputs. The source predicate changes scheduling only: `elc`
independently validates the normalized clause fragment and declines instead of
publishing an answer outside its supported fragment.

The runtime change was benchmarked from candidate commit `703a713` and promoted
to `main` as `eae74e8`. Commit `88ea6fc` updates the explanation integration
test to accept the atomic EL route selected for its flat source subsets.

## Verification

- Source archive SHA-256:
  `3943e8eae1d37cf587ddf2e5d3e7eb06a7ab424832f8dde4cbeab61adf6552ed`
- Source-bound build job: `50069310`
- Candidate binary SHA-256:
  `ae603062a79c90424a667f4ba607b81713627d171b6a4aeb9e6ae1347e04c7ea`
- Complete automatic-route sweep: jobs `50069311`, `50069732`, `50069757`,
  `50069835`, and `50069871`, resumed from validated checkpoints
- Constrained ORE15846 replacement: job `50070685`
- Lower-family exact EL panel: job `50067083`
- Large-family exact EL panel: job `50065528`

The strict audit found 592 unique result rows, profiles, and checkpoints; one
candidate binary; no temporary outputs; and the collision-sensitive ORE4669
full-IRI fingerprint
`a482e066a22110df593bf3a4c1fdd0ef4404f7141903b2101b85aae49811cb30`.
Coverage remains 591/592: 588 exact retained-gold matches, two adjudicated
consistency mismatches, one no-gold completion, and only ORE1194 failing
closed. Exactly 68 routes change from `production_all` to `elc`. Status,
verdict, signature, consistency, subsumption count, unsatisfiable-class count,
and discrepancy counts are unchanged for all 592 ontologies.

The release suite passed with 1,955 library tests, eight intentionally ignored,
all integration tests, and no failures.

## Performance

All 68 changed ontologies were measured through exact EL completion on Intel
Xeon Gold 6248 nodes. Every result matched the automatic candidate signature.
Combining those changed-route measurements with the unchanged v0.2.3 Gold-6248
rows gives the hardware-calibrated release comparison:

| Metric | v0.2.3 | Candidate | Change |
|---|---:|---:|---:|
| Mean wall time | 5.8647 s | 5.7851 s | -1.36% |
| Median wall time | 0.2756 s | 0.2547 s | -7.58% |
| Mean peak RSS | 801.66 MiB | 781.08 MiB | -2.57% |
| Median peak RSS | 42.63 MiB | 41.27 MiB | -3.19% |

The complete automatic-route sweep used several CPU families to accelerate the
semantic gate. Its raw aggregate is 5.4383 seconds mean wall, 0.2734 seconds
median wall, 767.32 MiB mean peak RSS, and 38.64 MiB median peak RSS. Those raw
figures are retained for reproducibility but are not used for the release's
comparison against v0.2.3.

[`automatic-results.tsv`](automatic-results.tsv) records the complete
automatic-route sweep and has SHA-256
`c8fcdb9670a8ba77df6e924b98360587301529f41359b08ad7a3e5c9ae2e267a`.
[`gold-calibrated-results.tsv`](gold-calibrated-results.tsv) records the 591-row
Gold-6248 comparison and has SHA-256
`5da2f121582e0b7781e07fcce59f631813a34aabf5caa40875bce0ea922a5bf9`.
[`summary.json`](summary.json) contains the machine-readable aggregates.
