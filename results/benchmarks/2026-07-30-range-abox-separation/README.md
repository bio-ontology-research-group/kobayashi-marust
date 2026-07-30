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

The IBEX focused gate must prove exact frozen-signature equality before this
restoration is counted in production coverage.
