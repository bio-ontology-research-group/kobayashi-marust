# ORE6934 incremental-blocking investigation

This capsule targets mean ORE wall time after v0.2.11. ORE6934 is one of the
largest contributors to KM's remaining wall-time gap against Konclude.

## Profile

IBEX job `50435635` used the v0.2.11 binary SHA-256
`d19938110369da96167feddf2a257550bf80aca1793afd40154d18d303663f8e`
on an Intel Gold 6248 node. The automatic `nominal_ni_abox` route matched the
frozen Konclude signature in 118.13 seconds at 3,087,668 KiB. The HT profile
reported:

```text
steps=467280 block_ms=100108(89%) prop_ms=7668(6%) expand_ms=3696(3%)
i2 calls=467276 full_rebuilds=586 avg_suffix=764
phase1 queries=143 reused=89 built=54 phase2_tests=42
```

This establishes incremental subset blocking as the dominant cost. Search had
only four backtracks, so branch-order changes are not the relevant lever.

## Rejected candidates

### Bloom prefilter

A 256-bit, two-hash necessary-condition filter rejected blocker candidates
whose labels could not be supersets. Every possible hit still used the existing
exact concept-map test, so the blocking relation and output were unchanged.
Build job `50435709` produced binary
`0c527e03c0a2bd45e3cb53cbdd03659205e9abeb5c702d825d9ffa663ad80b03`.
Exact-gold panel `50435807` measured:

| Arm | Wall | Peak RSS | Verdict |
|---|---:|---:|---:|
| v0.2.11 | 117.4564 s | 3048.18 MiB | exact match |
| Bloom candidate | 177.6285 s | 3143.87 MiB | exact match |

Rebuilding the filter over the changing suffix dominated any saved exact
lookups. The candidate was rejected and removed.

### Move the blocking snapshot instead of cloning it

This candidate temporarily moved the already-computed blocked-node vector into
the obligation pass and restored it before return, avoiding an allocation and
vector clone on every pass. Build job `50435917` produced binary
`09466a7c1aa810f3a1e68b2f6b048df67637033edab0daed4f214c3455eeef57`.
The first pair (`50436086`) was 1.37% faster, but the three-pair confirmation
`50436234` showed that result was noise:

| Arm | Mean wall | Median wall | Mean peak RSS |
|---|---:|---:|---:|
| v0.2.11 | 116.4038 s | 116.5936 s | 3052.92 MiB |
| move candidate | 116.6207 s | 116.8593 s | 3050.21 MiB |

The candidate was rejected because mean wall regressed 0.19%.

### Move plus clean-snapshot shortcut

A follow-up skipped posting-list truncation when no blocking input changed.
Build job `50436625` produced binary
`31a1a70a1061f55519952a54221f8d837e3ef246f163ac768dba9ad0981649c6`.
Exact-gold panel `50436731` measured 115.3815 seconds / 3050.46 MiB for
v0.2.11 and 118.0624 seconds / 3051.49 MiB for the candidate. The 2.32% wall
regression rejected the combination. It was fully removed.

These results rule out per-pass auxiliary filters and snapshot ownership as
useful levers. A future ORE6934 improvement must reduce the 467,276 blocking
passes or the average 764-node dirty suffix structurally, rather than adding
work around the existing pass.
