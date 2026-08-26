# v22 sparse-Horn cutoff and RBox panel

Candidate v22 lowers the source-size and class-count profitability cutoffs for
the source-certified sparse-Horn route.  It also admits ordinary role
inclusions and role chains only when no existential-left (NF4) rule can turn
their edges into a named-class conclusion.  A 500,000-name upper cutoff was
tested and rejected because it caused a second full source pass on ORE16008;
that cutoff is not present in the follow-up candidate.

- Source capsule SHA-256: `438ee4f22439d75fd7781e67041e67318be620fd039948e005113f254afaf4f4`
- IBEX binary SHA-256: `abf815996bfdb18d3ff6813e1f1af49bccba5c40932b39b27cd7bf267678c7be`
- Build job: `50877224`
- Focused array: `50877225`
- Baseline: v20 binary `33b536962de62789387d98479d9d4f5d28edc142eb9e7260e9805eb7d79b2c97`

All focused outputs are byte-identical.  ORE6477 changes route and falls from
approximately 7.25 seconds and 757 MiB to 0.28 seconds and 28 MiB.  ORE5519
retains the v21 gain.  ORE6223 remains on its established route because its
disjointness uses native `DisjointClasses` syntax; the follow-up candidate
normalizes that syntax to the already checked pairwise bottom rules.

The defensive upper cutoff regressed ORE16008 from approximately 3.0 to 4.5
seconds by declining after one full source pass.  The follow-up removes it.
This v22 artifact is therefore diagnostic evidence and is not a release
candidate.

Lean theorem `sub_iff_classProjection_of_no_bottom` certifies the RBox-elision
boundary.  Its direct file check reports only `propext` and no `sorryAx`.
