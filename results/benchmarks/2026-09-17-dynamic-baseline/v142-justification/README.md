# v1.4.2 runtime, validation and justification evidence

The private 1.4.2 source archive differs from the 1.4.1 candidate only in the KM
package versions in Cargo.toml and Cargo.lock. All 334 archive members have
identical metadata; the other file contents, including 254 Rust source files,
are byte-identical. The source worktree remains at version 1.4.1.

- Source archive SHA-256: `37bb4b1b184033ec249d3044a6a72c3460bbf3e78d443d94d5accfbd8b9631e1`.
- Binary SHA-256: `705cac1500018d18018ca4d5482a7451e836091b26648453824afa4b36d16fdb`.
- Build job: 51983793.

The earlier equivalence receipt binds 689 unchanged source and gate hashes.
Subsequently, all four certification gates were also run separately against
version 1.4.2 and passed. The
[final native-gate receipt](../v142-native-gates-source-manifest.json) binds 755
unchanged files. The [general Rust suite](../v142-general-rust-suite.json)
passes 2,407 library and 59 integration tests; the 22 checker-dependent
exclusions pass within the native gates. Eight ignored tests remain excluded.

Public gate 51984225 passes 18 cases and retains the known unsupported manual
route for a duplicate assertion. Earlier harness job 51983988 tried an
unavailable --version flag; its failure log is preserved. The replacement
verifies reasonerVersion through an explanation report. Explanation control
array 51983989 and independent audit 51984004 pass all 30 cases. These runtime
controls precede staging 51984100 and the final measured runs.

Final arrays 51984134 and 51984137 use the frozen original 240 and ZFA 60 tasks,
with unchanged common extraction code, Java classes and runtime bindings.
Their only arms are native and common-driver KM 1.4.2. They retain one warmup,
five measured repetitions, full-ontology and module tracks, and bounds 1/10/100.

The [final ZFA audit](final-pure-dl-audit/README.md) is complete. All 360 planned
attempts are accounted for: 270 independently correct and 90 timed out,
including warmups. The 300 measured attempts contain 225 correct and 75 timeout
outcomes. All timeouts occur in the full-ontology common-driver arm. There are
no reported integrity errors or duplicate logical supports. These results are
one panel, not the completed comparison.

The [original-panel array and audit 51984145](final-original-audit/README.md)
are complete: 1,200 measured attempts contain 825 correct results, 270 timeouts
and 105 errors. A common-driver stream-closing defect identified in HAO errors
requires isolated validation and corrected comparison runs before publication.
Comparison job 51984639 also requires baseline audits 51982402 and 51982764.
The separate 592-ontology exact-binary regression is complete, with unchanged
semantic outputs; see [ORE evidence](../../2026-09-17-dynamic-fixes/v142-ore/summary.json).
Release publication and the full comparison tables remain pending.

Immutable remote roots are justification-v142-original,
justification-v142-pure-dl and justification-comparison-v1 under
`/ibex/scratch/hohndor/km/dynamic-benchmark-20260917`.
