# ORE 1194 backward-subsumption mutation profile

This instrumentation-only run splits backward subsumption into candidate
selection, exact filtering, removed-worked discovery, active mutation,
worked/pending retention, and worked-off head-index deletion. It used the exact
two-thread CB route with a 225-second central cap and failed closed after
234.2621 seconds at 12,904.30 MiB. It published no taxonomy and leaves coverage
at 591/592.

## Provenance

- Instrumentation commit: `07802468135cf121c3cecfc6260c4bf0909970f2`
- Source archive SHA-256:
  `9eca2447d6227d321eb618857d9d07f80b69620106334d2a33e0a258a583449d`
- IBEX build job `49856985`, with `BUILD_COMPLETE`
- Binary SHA-256:
  `dcdabd642b428c050ddcd88463c33d3ed800932bb800caea6cabbe1db27cbcda`
- Profile job `49857041`, with checkpoint and `TASK_COMPLETE`
- Immutable root:
  `/ibex/scratch/hohndor/km/profile-0780246-backsub-mutation-20260802`

## Final 600,000-iteration checkpoint

| backward-subsumption phase | cumulative ms |
|---|---:|
| select rarest posting and materialize candidates | 429.4 |
| dense screen and exact strengthening filter | 168.9 |
| scan `worked_off` to discover removed worked clauses | 28,074.5 |
| active-index/key/mask mutation | 6,877.8 |
| retain survivors in `worked_off` and `todo` | 30,082.1 |
| delete removed worked clauses from head indexes | 6,623.8 |

Candidate discovery and exact subsumption together cost only 0.60 seconds.
Repeated whole-list discovery and retention scans cost 58.16 seconds, 77% of
the measured 75.27-second backward-subsumption phase. This explains why the
allocation-free candidate did not help and selects stable worked-off slots plus
generation-tagged pending entries: both permit O(1) logical removal while
preserving survivor order and re-add-at-the-end semantics.
