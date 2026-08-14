# v0.2.21 subset-blocking benchmark

This directory records the evidence for the v0.2.21 automatic-route release.
The tested implementation is commit `cb5c59b`.
The strict candidate binary was
`08d0fcd50d524bb6991fe350af440c5f2729ef516c8989a81236687cf66bd410`.
All end-to-end measurements used exclusive Intel Xeon Gold 6248 nodes, a
240-second timeout, and a 20-GiB process-tree memory cap.

## Change

Incremental subset blocking retains the dependency-bearing concept maps as the
authoritative labels and additionally maintains dense encoded-literal bitsets.
The hottest blocker check now performs contiguous word subset tests instead of
about 17 hash-table probes per candidate. The bitsets exist only when
incremental mode-1 subset blocking is active, so other tableau modes and all
non-tableau routes retain their prior allocation layout.

The optimization changes only the representation used to evaluate the same
label-subset predicate. It does not alter rules, branch order, dependencies,
blocking eligibility, or the derived result, and therefore does not require a
Lean calculus re-certification.

## Focused validation

Exact ORE6934 pair `50480341` preserved byte-identical output and identical
search work: 467,280 steps, 467,276 blocking calls, 586 full rebuilds, and an
average recomputed suffix of 764 nodes. Wall fell from 123.09 to 73.15 seconds,
peak RSS from 3,082,604 to 2,985,812 KiB, and measured blocking time from
105.136 to 54.422 seconds. Eight-route panel `50480342` also produced
byte-identical output for every input.

An attempted expansion of the in-process CB route was separately rejected:
strict sweep `50482294` detected incomplete signatures for ORE1016 and
ORE11623 and a 2.35-GiB peak increase on ORE15491. None of that experiment is
present in v0.2.21.

## Strict sweep

Independent strict sweep `50483032` produced exactly 592 result rows,
profiles, and checkpoints. It validates the binary hash, CPU model, selected
route, terminal status, collision-sensitive full-IRI fingerprints, and
checkpoint identity for every task.

Relative to v0.2.20 sweep `50473463`:

| metric | v0.2.20 | v0.2.21 candidate | change |
|---|---:|---:|---:|
| mean wall, s | 3.954087 | 3.897291 | -1.44% |
| median wall, s | 0.1910 | 0.1897 | -0.68% |
| mean peak RSS, MiB | 443.371 | 443.222 | -0.034% |
| median peak RSS, MiB | 36.43 | 35.94 | -1.35% |

Coverage and adjudication remain unchanged: 591 successful classifications,
588 gold matches, two established consistency mismatches, one independently
adjudicated no-gold result, and ORE1194 as the sole fail-closed error. The
comparator reports zero behavior regressions.

## Files

- `automatic-results.tsv`: all 592 strict rows
- `summary.json`: strict aggregate and binary identity
- `comparison-v0.2.20.json`: frozen release comparison

The complete serial Rust release suite passes, including the issue #3
pigeonhole regression.
