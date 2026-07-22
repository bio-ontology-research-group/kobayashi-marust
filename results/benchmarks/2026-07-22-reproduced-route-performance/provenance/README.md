# Provenance index

This directory binds the source, binaries, public route surface, benchmark
drivers, and Slurm execution records used by the 2026-07-22 full panel.

- `build-receipt.json` records source revisions, toolchains, build jobs, and
  every executable SHA-256.
- `binaries.sha256`, `baseline-runtime-files.sha256`,
  `konclude-runtime-files.sha256`, and `sequoia-files.sha256` bind the runtime
  inputs.
- `km-*.json` contains the source revision, variant type, and binary hash for
  each frozen KM optimization stage or clean ablation.
- `ablate-*.patch` and `ablation-patches.sha256` preserve the exact reverse
  patches used to build the clean current-main ablations.
- `km-routes.txt` is the output of the hash-pinned frozen `km-main routes`
  binary. Its 35 names exactly equal the public-route rows in
  `full-panel-contract.tsv`.
- `array-driver-files.sha256` binds the primary per-ontology driver.
- `supplemental-giant-driver-files.sha256` binds the narrowly gated full-IRI
  runner for ontologies 3524 and 15703, including its unchanged primary-runner
  dependency.
- `final-aggregation-driver-files.sha256` binds the fail-closed aggregator that
  accepts those two supplemental task identities and no others.
- `giant-postprocessing-attempts.tsv` records every failed or diagnostic
  local-name post-processing attempt and identifies whether it contributed a
  published measurement.
- `slurm-accounting.tsv.gz` records final accounting for the build, smoke,
  primary array, supplemental array, diagnostic, and aggregation jobs.

The top-level `full-panel-receipt.json` rehashes the manifests and generated
outputs and records every invariant checked before publication.
