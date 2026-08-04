# ORE 1194 compressed-overlay NF3 census

This experiment evaluates the compressed virtual-label certificate checkpoint
`2481459` on the retained 1,062,240-clause payload for ORE ontology 1194. The
candidate is isolated on branch `codex/fable-1194-cardinality`; none of its
reasoning changes are enabled in production.

## Contract and tests

- Input: `/tmp/1194.clauses.json`, 257 MB.
- Route: `elc` with `KM_ELC_CERT=2`.
- Limit: 240 seconds and 20 GiB, swap disabled.
- Acceptance: a complete taxonomy only; timeout, memory exhaustion, and partial
  output fail closed.
- Focused release suite: 50 passed, 0 failed.

The first production gate timed out after 240 seconds and emitted zero bytes.
It reached the virtual-label closure with 78,367,893 lower-model concept facts,
43,891,310 physical edges, and 11,856,511 virtual memberships over 150,190
concepts. Peak observed RSS during the overlay was about 13.4 GiB.

## Exact NF3 work census

A measurement-only build replaced each per-source NF3 membership probe with a
bitmap difference against the existing reverse-edge bucket. It counted the
candidate and genuinely absent edges without changing which edges were sent to
`State::add_edge`. The synthetic NF3/NF4 equivalence test passed.

Before the 20-GiB cgroup killed the diagnostic, it had processed 4,200 virtual
NF3 rule applications:

| Measure | Count |
|---|---:|
| candidate edges | 328,886,881 |
| already present | 288,481 |
| genuinely missing | 328,598,400 |
| missing fraction | 99.912% |

The bitmap screen therefore cannot close 1194. The cost is not repeated hash
probing of existing edges. The certificate is attempting to materialise more
than 328 million new edges, and it had not finished the virtual NF3 queue when
memory was exhausted.

## Decision and next implementation

Keep the compressed-label checkpoint isolated. Do not merge the bitmap screen:
it preserves semantics but does not improve the production result.

The next candidate must retain NF3 consequences as a compressed role relation,
keyed by `(role, fixed target)` with a bitmap of sources. It must:

1. compute NF4 and bottom consequences directly from source bitmaps;
2. close role hierarchy exactly and fail closed when an unsupported role-chain
   composition touches a virtual relation;
3. expose virtual pairs to every bound and unbound role-atom path in the
   residual checker;
4. preserve inverse-view semantics, quotient merges, and the full-model
   acceptance check;
5. remain isolated until focused equivalence tests and the real 1194 gate pass.

This is a measured structural requirement, not a claim that ontology 1194 is
closed. Production automatic coverage remains 591/592.

## Virtual-relation checkpoint

The first implementation of that design is preserved at `7438703` on the
isolated `codex/fable-1194-cardinality` branch. It adds:

- fixed-target NF3 relations with Roaring source bitmaps;
- exact role-hierarchy lifting;
- ordinary and reciprocal NF4 closure over virtual pairs;
- a compact physical-label transpose for reciprocal intersections;
- selective virtual-label transposition only at actual NF3 targets;
- residual role membership and dense domain/range checks over the overlay;
- fail-closed rejection when role chains are present.

The focused virtual NF3/NF4 test passes. The production-contract gate still
times out and emits zero bytes, so the checkpoint is not eligible for `main`.
At 240.81 seconds it had processed 3,000 virtual concept keys, represented
644,535,890 role pairs, and peaked at 14,438,252 KiB. This is a large advance
over physical materialisation, which exhausted 20 GiB after 328.6 million
missing edges, but closure still does not drain within the benchmark limit.

The next optimization should share the repeated dense source bitmap across
virtual concept and role buckets, then batch the thousands of NF4 conclusions
that receive that same source set. The current implementation keeps each
bitmap independently, so its CPU and memory costs grow with the number of
logically identical extensions even though their contents are compressed.
