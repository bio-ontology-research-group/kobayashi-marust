# Compact predecessor-clause intern postings

Commit `be09cfa` changes the global predecessor-clause content-hash buckets
from heap-allocated `Vec<u32>` values to KM's 16-byte inline `Posting`
representation. Most buckets contain one or two candidate IDs. Hash collisions
still traverse candidates in insertion order and still require exact clause
equality, so interning, rule scheduling, derivations, and the saturation
fixpoint are unchanged. Promoted main commit `8d0cb8e` has the same source tree.

## Workstation gates

The release library suite passed with 1,954 tests, eight intentionally ignored,
and no failures. Two alternating ORE9944 pairs emitted the same output SHA-256,
`97a95bbfc29dd4c7228f20740a5c0d886ee196a113b1154d785759ca5d90168f`.
The candidate's two local runs used 5,848,352 and 5,897,152 KiB peak RSS,
versus 5,980,372 and 5,903,736 KiB for the baseline; wall was neutral to
slightly faster. Baseline and candidate both failed closed with zero output on
ORE1194.

## Source-bound IBEX gates

- Candidate commit: `be09cfa`
- Source archive SHA-256:
  `18bdd610bf5e16f62eac266f76154a874ca5cb3ac5209a91a11a293a5cb72576`
- Build job: `50058329`
- Binary SHA-256:
  `44b3a572bf781564fd2737556bf4f8d4d34847a73c30c77db8086619906452da`
- Ten-ontology panel: `50058474`
- Resumable 592-ontology sweep: `50058521`

The strict audit verified 592 unique result rows, profiles, checkpoints, array
indices, and terminal receipts; one binary identity; no temporary outputs; and
ORE4669's collision-sensitive full-IRI fingerprint
`a482e066a22110df593bf3a4c1fdd0ef4404f7141903b2101b85aae49811cb30`.
Coverage remained 591/592: 588 matches, two established consistency disputes,
one established no-gold case, and only ORE1194 failing closed. There were zero
status, verdict, signature, selected-route, consistency, or taxonomy-count
differences from the `4254fbb` production baseline.

Across the 591 successful classifications, mean wall improved from 5.930799 to
5.901556 seconds (0.49%) and mean peak RSS from 806.238 to 802.248 MiB (0.49%).
Median peak RSS improved from 42.52 to 42.22 MiB. Median wall was 0.2718 versus
0.2537 seconds; this independently scheduled tiny-runtime statistic is noisy
and does not contradict the removed allocations or the improved aggregate
wall time.

[`automatic-results.tsv`](automatic-results.tsv) contains all 592 rows and has
SHA-256
`8bce2e740e5f53dc9452ad35e69570d7ee764955a50e60776b328126eb6467bf`.
