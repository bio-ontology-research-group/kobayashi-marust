# Draft reply to GitHub issue #4 (QUDT): for the maintainer's approval, not posted

Thank you for the report and the merged QUDT Turtle file.

**The crash is fixed.** The panic came from the OWL functional-syntax writer
of the vendored horned-owl 1.4.0, which sliced strings by character count
instead of byte index and broke inside the degree sign in a QUDT literal.
The fix (one function in the vendored crate, plus UTF-8 fixtures and a test
for RDF/XML, Turtle and OWL/XML input) is on the v1.5.4 branch as commit
`88c3ff67` and will ship with v1.5.4.

**Classification itself is still too slow, and we do not consider that
closed.** Measured on 2026-10-29 with the current v1.5.4 head (`9cf7c2cd`),
one core, `km classify --lines qudt-merged.ttl`:

- Turtle conversion and frontend: 0.5 s. Profile SHOIF(D).
- The ontology carries 6,124 data-property assertions on its individuals.
  The Konclude-derived hypertableau bridge, which is the fast route for
  ontologies with nominals and individuals, does not yet model data-property
  assertions, so it declines after 2.2 s.
- The router then uses the exact nominal consequence-based route
  (`certified_nominals`). That route carries all 6,124 assertions but does
  not finish within 1,800 s.

So v1.5.4 will answer QUDT correctly when it finishes, but not in a time
anyone would wait for. The missing piece is native data-value reasoning in
the nominal route (and in the bridge's ABox conversion); that work is
scheduled for v1.5.5 and this issue will stay open until QUDT classifies in
reasonable time, exactly, with no dropped axioms.

If you need a classification of QUDT before then: v1.5.4 reports exactly what
it did not represent in the `DROPPED` line, so a run with the data-property
assertions removed from the input is an honest TBox-only classification; it
is not what you asked for, and we will not call it a fix.
