# Incremental public taxonomy reuse

The bridge source session now keeps its mapped public taxonomy and remaps only
subjects whose internal rows changed. It checks exact correspondence when seeding
from batch output, and falls back to full mapping when correspondence, mapping
metadata, completeness, or consistency conditions do not hold. A changed public
identity rebuilds every internal alias that maps to it. Refusal leaves the old
public result untouched. The change does not alter any inference rule or derived
internal taxonomy.

The focused suite passes 26 tests, both normally and with experimental source
module reuse enabled; the typed incremental suite passes 14 tests. Differential
mapping tests cover 1,024 old/new row combinations, alias collisions, hidden
subjects, unsatisfiability, row deletion, and unchanged rows. Guard tests cover
changed mapping metadata, dropped/unresolved outputs and global inconsistency.

Two repetitions of five revisions of ORE9944 preserve exact fresh answers in
both source-module and full-input modes. Source-module updates beat fresh
reasoning on 4/8 attempts (the small edits), while the four larger edits remain
slower. Full-input updates beat fresh reasoning on 0/8 attempts. These are local
diagnostics, not release acceptance. Initialization is included separately in
each raw receipt. The changed-public-row trace records 52 remapped rows out of
8,008 on the larger edits; the small edits leave the published taxonomy unchanged.

The publication phase in the first module repetition takes 0.126, 0.146, 0.182
and 0.195 seconds. Other preparation and classification costs still dominate.
Do not infer an end-to-end improvement over earlier binaries from unmatched
historical timings. The v1.5.1 all-case requirement remains unmet.

See `incremental-publication-validation.json` for the immutable binary hash,
test-log hashes, and every retained/fresh timing pair; the two `*-updates.json`
receipts preserve source hashes and actual reuse counts. Exact-source Lean gate
results are recorded separately in `incremental-publication-certification-receipt.json`.
