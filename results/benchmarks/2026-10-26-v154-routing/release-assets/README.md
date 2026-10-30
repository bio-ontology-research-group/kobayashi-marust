# Release assets for tag v1.5.4 (commit 80c8f82a)

Prepared on 2026-10-30 in `.work/v154-release-assets-80c8f82a/` (not in
the repository), before the maintainer's decision on G8's mean bound
(`docs/V1.5.4-STATUS.md`, "Release decision"). If the tag is replaced, the
assets are rebuilt; the checksums here then no longer apply.

| Asset | Source |
|---|---|
| `km-v1.5.4-linux-x86_64` | `.work/pgo-v154/km-pgo-use-bfd`, the profile-guided build of the tag linked through the glibc wrapper (receipt `pgo-use-bfd-build.json`); the binary measured on the held-out half |
| `kobayashi-marust-protege-1.5.4.jar` | `mvn -o -B -Dkm.bin=<km-pgo-use> package` in the gate clone at the tag (`.work/gates-4dd7995b/src/protege`); 76 tests, 0 failures (`.work/v154-release-cert/logs/mvn-package-from-tag.log`) |
| `km-v1.5.4-certified-source.tar.gz` | `git archive --prefix=kobayashi-marust-1.5.4/ v1.5.4`, gzip -n -9 |
| `BENCHMARKS.md`, `build-completion.json` | `build-assets.py` (this directory) from the local copies of the Ibex run records (`.work/v154-release-cert/data/`) and the gate, Rust, Java and PGO receipts |
| `SHA256SUMS`, `manifest.json` | `build-assets.py` |

`build-completion.json` records `authorized_performance_exception: null`
and G8's mean as not met (1.172 against 1.10); it is filled or the tag is
replaced after the decision. `SHA256SUMS-80c8f82a` and
`manifest-80c8f82a.json` are copies of the generated files.
