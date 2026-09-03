# v1.4 source-nominal-free nominal-route HT scheduling

This milestone recovers three strict time-and-memory residuals by scheduling a
complete, one-worker general-hypertableau probe before exact nominal-aware CB
saturation. The automatic route remains fail closed: `ht_general` must consume
the complete normalized input and return a complete classification, or the
orchestrator restores the unchanged exact nominal route.

The source-feature predicate contains no ontology identity. It applies only
after automatic routing selected `nominals` or `certified_nominals`, requires a
small assertion-bearing profile with no source `ObjectOneOf`, imports, or
rules, and excludes the separately measured one-worker exact-CB envelope. Its
projection over all 592 retained source profiles is exactly ORE 2860, 5564,
9557, and the already-strict collateral control 13383.

## Validation

Commit `5629b4e12bf7982d42c863652c1bdca31373b28a` passed three focused release
tests:

- source-shape bounds and independent invalidators;
- absence of ontology identifiers in the gate;
- exact four-member projection over all 592 retained profiles.

This is a scheduling-only change. It does not modify a calculus rule, derived
set, or completeness condition, so the existing Lean calculus certificate is
unchanged.

An exploratory complete-route panel first ran six routes over ORE 2860, 5564,
and 9557, five repetitions each. Array `51258117` produced 90/90 checked
records; one-worker general HT was then repeated in array `51258643`, producing
15/15 gold-matching results. A four-worker-count collateral panel on ORE 13383
produced 20/20 gold-matching results in array `51258597`. The exploratory
archive has 378 checksum-manifest entries; the `SHA256SUMS` file itself hashes
to `51d7abdff7c689250f47bd11c05e82c479ecd1a20a12c387d79f294e7d7ad915`.

Build job `51259121` compiled the pinned commit from source archive SHA-256
`786e50730af0486f7996a8e444a8a8569cafb138454b0223c6a1dbd79c9857c9`.
The deployment checker accepted binary SHA-256
`7161ebb7a8dd9788e58d0ea083c2633570312d23ae2828f39ed9a24ebbf2132c`.
Automatic-route array `51259177` then produced 40/40 result files, 40/40
checkpoints, 40/40 `TASK_COMPLETE` markers, and no failure artifact. Every run
selected `ht_general` and matched the retained Konclude signature.

| ontology | observations | median wall (s) | wall target (s) | median peak (MiB) | peak target (MiB) | strict result |
|---|---:|---:|---:|---:|---:|---|
| ORE 2860 | 10 | 0.0772 | 0.1017 | 10.29 | 36.23 | pass |
| ORE 5564 | 10 | 0.0460 | 0.0713 | 10.16 | 33.55 | pass |
| ORE 9557 | 10 | 0.0460 | 0.0705 | 8.12 | 28.18 | pass |
| ORE 13383 | 10 | 0.0611 | 0.1014 | 10.00 | 21.05 | pass |

The production archive contains 127 checksum-manifest entries, including the
pinned source archive, build receipt, scripts, raw results, checkpoints, and
Slurm logs. Its `SHA256SUMS` file hashes to
`74efd56d91454a99c85ae9330372d0694e54a1e32e9f1d6c40e9e6349e54a68b`.

ORE 13383 was already a strict win and remains one. The other three results
raise the evidence-composite score from 521/589 to **524/589**, leaving 65
comparable strict-performance residuals. Correctness coverage remains 592/592.
