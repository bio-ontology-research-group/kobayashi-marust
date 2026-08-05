# ORE1194 inverse-closed upper-bound probe

This experiment tested whether a compact, root-local upper abstraction could
certify the six unresolved `UBREL_0000002` candidates left by the staged
ORE1194 route. It is rejection evidence. No experimental code from this route
is enabled in the default classifier.

## Hypothesis and semantic control

The earlier role-signature quotient considered only the root's ordinary
forward cone. That is not an upper bound in the presence of forced inverses: a
physical edge from an outside node into the cone can become an outgoing logical
edge, and NF4 can propagate its consequences back to the root.

The isolated branch added a focused regression containing exactly this shape:
root to child, outside to child, a forced inverse from child to outside, and two
NF4 steps returning a goal concept to the root. The old local quotient misses
the goal. The corrected implementation keeps the least root cone closed under
ordinary outgoing edges and incoming physical edges for roles with explicit
forced-inverse clauses. The focused regression and the release library check
passed on the workstation.

The experimental commits are `89756ee`, `bd47e58`, and `7c19f7e` on branch
`codex/1194-sat-share`. They remain isolated because the real-ontology gate
below rejected the approach.

## Reproducibility

- Remote root: `/ibex/scratch/hohndor/km/1194-global-upper-20260805`
- Input size: 270,429,794 bytes
- Input SHA-256: `f66944b70b68b3b582d662288b9f6a54d2d782c567d4592481f51330c5a524c2`
- Source archive SHA-256: `f0568831291e2c542fc452dc26f7a4855120721ea26a5b0137e5b549803ea874`
- IBEX-built binary SHA-256: `0ac59536f568a389ef225666d29c1d6ce201962b8acbbed7213bdb3abb9d50e4`
- Build job: `50051959`, completed successfully in 4:52, MaxRSS 3,601,720 KiB
- Gate job: `50051960`, diagnostic exit 3 in 2:59, batch MaxRSS 3,836,260 KiB
- Timed reasoner run: 2:57.57 wall, MaxRSS 3,829,048 KiB

The first submitted gate used a workstation binary and failed immediately
because IBEX provides an older glibc. That was a deployment sanity failure, not
a reasoning result. The recorded gate builds from the checksummed source archive
on an IBEX compute node and verifies both input size and binary availability
before starting the reasoner.

## Result

The exact root-local repair converged as intended:

```text
initial violations=245 clauses=3
round 1 added_edges=245 remaining=3701
round 2 added_edges=3701 remaining=806
round 3 added_edges=806 remaining=0
total added_edges=4752 root_labels=806->2743
```

Closing reachability under forced inverses then made the supposedly local upper
model effectively global:

```text
KM_ELC_TWO_BLOCK_UPPER rounds=9 contexts=4
root_labels=254776 other_labels=710000 roles=123 elapsed=15.802
lower_named=217 upper_named=17449 extras=17232
```

An upper set with 17,232 extra named candidates cannot certify the six residual
negatives. The process therefore deferred and emitted no accepted
classification result.

## Decision

Do not merge this upper-bound route. Exact inverse closure demonstrates that
node reachability is too broad for a useful ORE1194 negative certificate. A
future certificate must preserve candidate-specific dependency or model
distinctions instead of quotienting the inverse-closed node cone.

The demonstrated automatic coverage remains **591/592**. General default-route
performance work can proceed independently; ORE1194 should be revisited only
with a sharper candidate-specific construction or after broadly useful
optimizations materially change the exact route's cost.
