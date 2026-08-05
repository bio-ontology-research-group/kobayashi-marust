# Canonical predecessor-conclusion merging

Commit `cbcc541` linearly merges already canonical predecessor-rule bodies and
heads in the staged local and arriving joins. It omits only the resolved
provider literal and constructs the resulting clause without sorting it again.
Premise order, result antichain filtering, rule scheduling, derivations, and the
saturation fixpoint are unchanged. Promoted main commit `86bf83c` has the same
source change.

## Workstation gates

The release library suite passed with 1,954 tests, eight intentionally ignored,
and no failures. The targeted predecessor oracle passed all eight tests. Two
alternating ORE9944 pairs emitted the identical output SHA-256
`97a95bbfc29dd4c7228f20740a5c0d886ee196a113b1154d785759ca5d90168f`;
mean wall improved about 2.7% and mean peak RSS improved about 27 MiB.

## Source-bound IBEX gates

- Candidate commit: `cbcc541`
- Source archive SHA-256:
  `e68ad102be954d11e3f5fb06da4367db4605f7ffeb60a73c86460f0ad360c7dc`
- Build job: `50061158`
- Binary SHA-256:
  `4b2c3229e900c78d8b8e41f9559cf8f26699648dfe435e5a1322160e5e2093ca`
- Serialized ten-ontology panel: `50061724`
- Resumable 592-ontology sweep: `50062331`

The strict audit verified 592 unique result rows, profiles, checkpoints,
ontology indices, and terminal receipts; one binary identity; no temporary
outputs; and ORE4669's collision-sensitive full-IRI fingerprint
`a482e066a22110df593bf3a4c1fdd0ef4404f7141903b2101b85aae49811cb30`.
Coverage remains 591/592: 588 matches, two established consistency disputes,
one established no-gold case, and only ORE1194 failing closed. There are zero
status, verdict, signature, selected-route, consistency, or taxonomy-count
differences from the compact predecessor-index baseline.

Across the 591 successful rows, mean wall improves from 5.901556 to 5.864671
seconds (0.625%) and mean peak RSS from 802.2477 to 801.6618 MiB (0.073%).
Independently scheduled tiny-runtime medians are 0.2756 seconds and 42.63 MiB,
versus 0.2718 seconds and 42.22 MiB in the prior sweep. The same-node hard
panel improves mean and median wall and peak RSS, including ORE9944 at 8.100
seconds and 8,042.04 MiB versus 8.306 seconds and 8,286.25 MiB.

[`automatic-results.tsv`](automatic-results.tsv) contains all 592 rows and has
SHA-256
`3d5692322a5a4e7ec74529c8f3315ddd34859e1ec0d2eaa1407bb8cced342b8c`.

