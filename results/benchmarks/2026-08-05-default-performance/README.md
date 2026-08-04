# Consolidated default-route production sweep

This sweep validates source commit `02e6200`, which includes the accepted
compact taxonomy representation, fixed hypertableau output-pair handoff, and
default serial hypertableau model reuse and counterexample pruning. Its source
archive has SHA-256
`9bc2540caf545fbb8bc68f980475835ef164aba637d4b425c5f5b911c56e2e90`.
IBEX build job `50047329` produced binary SHA-256
`3acef3c43d46b69a6ce9cd9b7d4f6ef4508ed74d8b8f1e92c31eac7ce04e9219`.

Sanity job `50047758` and source-bound arrays `50048482` and `50048483`
completed at
`/ibex/scratch/hohndor/km/release-02e6200-auto-20260805`. The strict audit
verified all 592 terminal rows, checkpoints, profiles, production route traces,
task-to-ontology identities, exact binary hashes, completion logs, and
collision-sensitive full-IRI fingerprints, with no temporary artifacts. Every
route and semantic result matched the preceding `9ee269e` sweep.

Coverage remained 591/592: 591 successful rows and the existing ORE1194 error.
Verdicts remained 588 matches, the established consistency disagreements on
ORE2669 and ORE15516, one no-gold row (ORE10860), and ORE1194's error.

Across the 591 paired successes relative to `9ee269e`, mean wall fell from
6.0082 to 5.8006 seconds (3.46%) and mean peak RSS fell from 823.32 to 819.95
MiB (0.41%). Median wall moved from 0.2523 to 0.2538 seconds (+0.59%), and
median peak moved from 42.13 to 42.77 MiB (+1.52%). Relative to the earlier
`abe2759` sweep, mean wall improved 0.33% and mean peak RSS improved 0.05%.
The source-isolated 70-ontology panel remains the clearest evidence for model
reuse and pruning: total wall improved 15.36% with all outputs exact.

The complete per-ontology result table is
[`automatic-results.tsv`](automatic-results.tsv). The build and sweep scripts
in this directory pin the source archive, result root, and binary identity.
