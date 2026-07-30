# Range-bearing separated ABox restoration

The automatic `production_all` route regressed on `ore_ont_1034.owl` and
`ore_ont_2237.owl` after the positive-EL ABox certificate was broadened beyond
the normalized cert-off EL consumer. Both ontologies have positive role
assertions plus property ranges. The normalized EL core retains range clauses
as residuals, so its materialization certificate declined at runtime.

The source certificate now excludes property ranges. This does not discard
the ontologies: their independent positive ABox/TBox-separation certificate
remains true, so `production_all` uses that exact consistency result and the
EL-safe TBox classification. The change is feature-driven and contains no
ontology identity.

Source commit: `6e3ba24b503d112b649e4a885c3dc858737e5a52`.

Source archive SHA-256:
`702e9fe546d734f6c10b0767aa3f83c5c876fcefad09bfd09665891242afa657`.

Local validation:

- the full serial release suite passes: 1,797 library tests, eight ignored,
  all integration tests, and zero failures;
- `1034` and `2237` both select `production_all`, complete locally, and return
  a consistent empty named-class taxonomy and empty unsatisfiable-class set,
  matching the shape of their frozen Konclude signatures;
- a focused source-profile regression test proves that a positive role ABox
  with a range cannot claim the cert-off EL materialization certificate.

IBEX build job `49642950` completed. The resulting binary SHA-256 was
`437ad33456fdcfe539f684f541bd6a27a36c4a585e526f5d7703ae4562545662`.
Dependent focused exactness array `49642951` passed all five cases:

- `1034`: `production_all`, 0.0406 s, 8.12 MB, exact;
- `2237`: `production_all`, 0.0411 s, 7.61 MB, exact;
- `1579`: `production_all`, 12.0655 s, 1,000.77 MB, 56,782 pairs, exact;
- `3377`: `production_all`, 36.6645 s, 2,649.50 MB, 4,490,309 pairs, exact;
- `6999`: `certified_nominals`, 0.2999 s, 92.60 MB, one unsatisfiable class,
  exact.

The focused gate is accepted. Count `1034` and `2237` as restored by this
feature-driven route. A complete source-bound sweep remains necessary before
updating the production headline.
