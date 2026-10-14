# Production and diagnostic build profiles

The earlier single-worker sweep uses binary ba955555af71. Its retained dense-data-standard-check.json explicitly records production_profile=true, and its build-log hash matches /tmp/agent/km-v150-diagnostics/dense-data-standard-build.log. Cargo's production profile sets opt-level=3, lto=true, codegen-units=1 and panic=abort.

Recent finite-role-index, IRI-cache and snapshot-reuse builds used diagnostic overrides CARGO_PROFILE_RELEASE_LTO=false and CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16. The source changes and their measured results remain recorded, but comparing those binaries with the production single-worker baseline does not isolate a source-code regression. The build profile is a confounder, not a demonstrated explanation of the entire difference.

Same-node job 53333094 independently verified all twenty results. The large 6948 slowdown from the separate sweeps did not reproduce: both arms took about 31 seconds. The 16680 slowdown did reproduce: baseline 162.163/165.666 seconds versus indexed 177.999/203.106 seconds. Its phase trace places the added time inside the HT worker. These runs compare different source snapshots and build profiles; they cannot attribute the difference to finite-role indexing alone.

build_unique_states_production.py now builds the pinned current source with the production settings, records the exact command, compiler version, source hashes, binary hash and build log. A fresh production-profile classification sweep is required before comparing this candidate against release acceptance targets. The diagnostic sweeps remain diagnostic evidence, with every failure retained.
