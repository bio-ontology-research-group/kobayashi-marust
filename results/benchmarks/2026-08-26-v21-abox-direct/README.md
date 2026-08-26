# v21 positive-ABox direct-route panel

Candidate v21 extends the sparse-Horn source certificate to named assertions
on blank nodes and simple positive existential class assertions.  An
existential assertion is accepted only when the source has no
existential-left (NF4) rule that could feed a named conclusion.  Named class
assertions remain grouped by individual for disjointness-clash checks.

- Source capsule SHA-256: `944591e7648a76ba09422cc9a5f49c9d4caf82022277b1f695f9b7915561c68f`
- IBEX binary SHA-256: `ed763a1700f5b4abcc42f1ba8be27a17c5609c3131ede1d03eaf84e019eff95e`
- Build job: `50876935`
- Focused arrays: `50876946` and `50877006`
- Baseline: v20 binary `33b536962de62789387d98479d9d4f5d28edc142eb9e7260e9805eb7d79b2c97`

All three alternating same-node pairs for every tested ontology produce
byte-identical output.  ORE5519 changes route and falls from approximately
5.97 seconds and 366 MiB to 1.25 seconds and 68 MiB.  ORE3560 and ORE7246
retain the direct route, while ORE6477, ORE10073, ORE11315, ORE9400, and
ORE9499 retain their established routes.  The latter controls show no material
regression.

This panel is focused evidence only.  The extension must be included in a
fresh strict 592-ontology sweep before release.
