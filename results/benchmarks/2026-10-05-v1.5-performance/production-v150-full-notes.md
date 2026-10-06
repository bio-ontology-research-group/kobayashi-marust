# Production-profile full candidate sweep

Job 53334551 measures binary 78312a61ce89 over all 1,920 frozen inputs, preserving the admission inventory, 240-second classification limit, 20-GiB memory limit, one CPU and independent taxonomy audit. Its source includes finite-role indexing, the IRI cache, and within-call classifier snapshot reuse. All four source certification gates passed without sorryAx. Three local correctness checks also have independently corroborated answers.

The build command and compiler version are recorded in unique-state-production-build.json. The verbose compiler invocation confirms opt-level=3, panic=abort, lto and codegen-units=1. This matches the repository's production settings and removes the diagnostic-profile confounder in the earlier candidate sweeps.

The classification runner now records the audit watchdog's status, process exit code, elapsed time and peak memory. It keeps the existing 600-second/20-GiB audit limit. This observability change responds to the unexplained canonicalization failure on 10689 in diagnostic sweep 53332943; that failure remains unverified in its original results.

No release approval follows from submission. Full verified coverage, mean and median runtime still need to beat each required competitor, and the independent incremental objective remains unmet. The snapshot-reuse paired timings are mixed and do not yet establish an isolated speedup.
