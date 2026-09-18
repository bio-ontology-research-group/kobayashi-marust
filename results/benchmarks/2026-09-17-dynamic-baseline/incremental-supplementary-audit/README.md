# Supplementary incremental baseline audit

This evidence covers ZFA and MRO, each with update sizes 1, 10 and 100,
251 states per history, one warmup and five measured repetitions. Each history
has nine arms: KM, HermiT, JFact and Openllet session/fresh, plus Konclude fresh.
KM here is the v1.4.0 baseline. Final v1.4.1 results belong to a separate cohort.

The 324 attempts comprise 173 completed histories and 151 timeouts. Excluding
warmups leaves 270 attempts: 145 completed histories and 125 timeouts. All ZFA
histories completed; MRO contributes most incomplete histories. Timeouts remain
in the denominator and are not classified as taxonomy disagreements.

The structural review found no mismatch across 81,324 available state/reference
digest comparisons. This count includes warmups, both fresh references and
reference self-comparisons; it is not a count of independent test cases. The
45,104 retained state records contain producer-generated canonical taxonomy
digests. Under the frozen methodology, these hashes cover complete sorted
full-IRI taxonomies, consistency and unsatisfiability. Full outputs were retained
for pilot validation; main-run disagreements require targeted full-output
reruns. No digest disagreement was found in this supplementary cohort. Agreement
on completed states does not prove correctness of uncompleted states.

Evidence files record successive checks:

- `main-audit.json.gz` and `main-audit.md.gz`: audit from Slurm job 51982376
  after benchmark array 51982375 finished.
- `parent-structural-review.json` and `review-structure.py`: exact case,
  repetition and arm coverage, state counts, fixed limits, manifest associations
  and available digest comparisons.
- `provenance.tar.gz` and `parent-provenance-review.json`: panel, auditor,
  driver sources and six input manifests, checked against all 324 measurement
  source hash maps.
- `parent-payload-verification.json`, its verifier and job 52012191 log:
  independent hashes of all 1,506 input files and five runtime binaries/jars,
  matched against manifests and measurement runtime receipts.

Earlier review receipts describe checks still pending at the time they were
written. The later payload receipt closes input/runtime hashing; it does not
convert digest records into independently retained full taxonomies. These files
document supplementary baseline coverage, not the final combined benchmark or
an overall performance ranking.

The uncompressed audit SHA-256 is
`5077ce21bac88fc3961a252014dcc3da3adf85b76296fa9ba1987af233cfa17c`.
The provenance archive SHA-256 is
`6b45960c50b8accb4c55b5874766f6c10074d2b4ccbaa84622e0212a63dee112`.
