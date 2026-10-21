# KM 1.5.1 release and benchmark protocol

Version 1.5.1 adds source-level incremental reuse and OWLAPI row-delta
publication. The [API guide](INCREMENTAL-REASONING.md) documents requests,
responses, rollback, retained work, and fallback. This release does not claim
that the default source session resumes backend saturation.

## Exact implementations

| Benchmark arm | Version | Source commit | Build |
|---|---|---|---|
| Candidate native, retained and fresh | KM 1.5.1 | `4dd7995b5def62bb8f9140dd2be62b671816f71b` | Release, mimalloc, no PGO |
| Final candidate OWLAPI adapter | KM 1.5.1 | `11db48ce73029227c7a28b9ad5e2e2a25189cc2a` | Maven, JDK 17.0.20.1+1 |
| Released retained and fresh | KM 1.5.0 | `d95f0b840a433b5b43c4eff48092e8b600bca8de` | Published profile-use executable |

The final release commit adds documentation and publication/evidence tooling;
its Rust, vendored parser, and Lean sources must match the native candidate
commit above, and its Java sources must match the final adapter commit. The annotated `v1.5.1` tag and `build-completion.json` identify
the exact final source commit. No abbreviated commit serves as a source binding.

- Candidate native SHA-256:
  `5ee715d66e391e561e188c735a8fa6a0aaabc4383e7d8bd243b52495b2cac3a8`.
- Released native SHA-256:
  `1dbc0dd92170abcd70e948fa2dc2d9d13d5c72076bcff9ad7a664921188e5900`.
- Candidate Protégé JAR SHA-256:
  `8ffdfbc4d3e947afe1b03d86a17bb9d57ff5f73b12acfc01b1f2d00f5e2cabb9`.

The Java adapters are compiled from the respective source commits, with class
manifests in the benchmark bindings. The v1.5.0 tag's POM still says 1.4.5;
its exact source commit, rather than that stale package label, identifies the
baseline adapter. The v1.5.1 JAR declares 1.5.1. Historical Konclude, ELK,
HermiT, Sequoia, and RustDL tables elsewhere in the repository are separate
experiments and are not baselines for these incremental results.

## Frozen experiment

Each of 80 ontologies has nine source revisions: initialization and eight
updates. Every revision is measured in four arms, with five paired repetitions
and counterbalanced order, through both the public CLI and OWLAPI paths.
The input selection SHA-256 is
`d51dff7640b82a84ccf22857532817c39c1952c9b6c7e2acd00ad4df6ab246e7`.
The final report also binds the expanded revision hashes and input plan.

Execution uses IBEX Slurm compute allocations, one CPU of the Intel Xeon Gold
6248 class, 20,480 MiB memory, and a 240-second per-request limit. Slurm reserves
24 GiB for the driver and worker together. Original arrays are 54015525 (CLI)
and 54015526 (OWLAPI). Fifteen tasks encountered exhausted project storage;
recovery arrays 54048085 and 54048086 use separate output directories and the
same binaries, inputs, drivers, limits, and machine class. The original failed
attempts remain evidence. Recovery replaces only those infrastructure-failed
case measurements in the final timing table.

The original OWLAPI panel used the adapter at
`4dd7995b5def62bb8f9140dd2be62b671816f71b` (JAR SHA-256
`4931544c2662352cdf96799d01d7f52822535961d7b8cd3df3c91ae224e4ab03`).
ORE 12351 exceeded the initialization limit in candidate fresh repetition 3.
The final adapter avoids sorting the full entity signature on both the live
ontology and its detached rendering snapshot. It reuses the snapshot signature
and includes ontology-annotation entities from the imports closure. The full
ORE 12351 serialized source remains byte-identical, including annotations.
All 76 Java tests pass after this change.

Array 54083337 revalidated all 80 OWLAPI cases with the final adapter. Each
array task runs one complete four-arm repetition. Task `5*i+r` selects case
`i` and repetition `r`; arm order, inputs, per-request limits, and machine class
remain unchanged. The final report combines all five repetitions only when
all their terminal records and bindings are available. It retains the original
panel and its timeout as separate evidence. CLI measurements continue to use
the identical native executable; the Java-only change does not alter them.

The signature-fix panel completed ORE 12351, but exposed timing losses on
ORE 9724 and a partial baseline answer on ORE 15703. An IBEX control measured
8.75 seconds of supervisor CPU during 15.03 seconds of monitoring a sleeping
worker. The OWLAPI driver scanned the whole node process table twice per tick
while sharing its one allocated CPU with the reasoner.

The final OWLAPI panel uses arrays 54101655 (the two affected cases) and
54101937 (the other 78 cases). Its monitor reads the worker's cgroup and nested
cgroups, reuses each membership snapshot, and retains full-table fallback and
final subreaper cleanup. The time and memory caps, binaries, Java adapters,
inputs, five repetitions, and balanced arm orders remain unchanged. Every arm
uses the corrected monitor. The original and signature-fix panels remain
separate evidence, including their failed attempts. CLI measurements retain
their original harness; the correction changes only the OWLAPI measurements.
See the [monitor investigation and frozen runtime](../results/benchmarks/2026-10-14-v1.5.1-incremental/release-preparation/monitor-scope-fix-20261020/README.md).
The release report supplies completed results and exact evidence hashes.

For each update, compute the median of five paired retained/fresh ratios,
not the ratio of unrelated aggregate medians. The per-cell target is strictly
below 1.0. Initialization is reported separately and included in the whole
session. Whole-session medians are compared against both the candidate fresh
sequence and the released fresh sequence; candidate retained versus released
retained is also reported.

- CLI: end-to-end request/update wall time.
- OWLAPI acceptance: `apply_flush_ns + taxonomy_publish_and_cleanup_ns`.
- OWLAPI additional reporting: harness `parse_ns` and end-to-end wall time.

The harness loads each revision file in both OWLAPI arms. That work is outside
the reasoner-only metric, but its measured cost can vary; it is never assumed
to cancel. For example, the completed original run measured an end-to-end
ratio above 1.0 for ORE 10053 update 8 despite a reasoner-work ratio below 1.0.
The final report retains that distinction.

All 80 cases and 640 update cells per path remain in the denominator. A timeout,
missing repetition, missing semantic identity, or failed cleanup is not a
passing cell. Results with five complete paired measurements are also reported
as a separately labelled comparable subset. No aggregate substitutes for a
failed individual cell.

## Correctness and certification

For each measured revision, compare canonical taxonomy hashes and consistency
across all four arms. Retained/fresh agreement does not independently establish
OWL correctness, so the 1,920-input source/correctness audit and Lean gates
remain separate checks. The corpus audit of the implementation completed
1,661 answers identical to v1.5.0, with 212 invalid-input refusals, 34 timeouts,
and 13 admitted process errors. It had two fewer completions than v1.5.0.
ORE 10949 and 15687 completed in isolated reruns with identical output; the
original timed-run coverage counts remain unchanged.

Run all four production Lean gates from the exact final commit before tagging,
and reject any `sorryAx`. Pre-release receipts for the implementation recorded
502 passing gate tests, 3,094 Rust CI-recipe tests, 75 Java tests, and six
transaction fixtures. These implementation receipts do not replace the final
commit's certification receipt.

The parallel literal Rust suite needs care: checker-dependent tests fail
without their Lean executables, and existing tests mutate process-wide
configuration. The CI recipe runs ordinary tests serially and the gates run
the checker-dependent tests with the actual checkers. The release evidence
preserves both the literal run and the CI/gate results.

## Reproducing and inspecting the release

Build the tagged source using `cargo build --locked --release --features
mimalloc --bin km` in `engine/`. Reproduce the JAR with Maven in `protege/`.
Compiler and JDK versions, build commands, checksums, and source comparisons
are recorded in the release receipt. Rebuilding in a different toolchain or
path need not reproduce the measured executable's exact bytes.

The release attaches:

- `km-v1.5.1-linux-x86_64`: the measured native executable.
- `kobayashi-marust-protege-1.5.1.jar`: the measured adapter package.
- `km-v1.5.1-certified-source.tar.gz`: the exact final source archive.
- `BENCHMARKS.md`: final results, including per-case timings and failures.
- `build-completion.json`: machine-readable results and certification bindings.
- `SHA256SUMS`: checksums of the other five files.

Download all files into one directory and run `sha256sum -c SHA256SUMS`.
The annotated tag binds the manifest by its HTTPS location and SHA-256.
GitHub Actions checks the manifest, exact source commit, filenames, sizes,
and file hashes before uploading to a new draft. It publishes only after all
uploads succeed. An existing release or draft requires inspection rather than
automatic replacement. No GitHub credential is stored in the source tree.
