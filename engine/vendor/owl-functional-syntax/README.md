# OWL functional syntax grammar

The four `upstream-grammars/*.pest` files are copied unchanged from Horned-OWL 1.4.0,
upstream commit `33c60d69526165b3dd687770e389d6e353223bfa`:
https://github.com/phillord/horned-owl

They retain the upstream LGPL-3.0 license. `COPYING` and `COPYING.lesser` are
copied from that distribution. The small Rust wrapper is distributed under
the same license.

This package exposes grammar validation without constructing Horned-OWL's
ontology model. In particular, syntactically valid large cardinalities must
not be converted to the model's `u32`. It accepts OWL functional syntax plus
DL-safe rules, and excludes description-graph extensions. Passing this
parser does not establish the OWL 2 DL global restrictions or DL-safety of
the rule evaluation strategy; KM checks those separately.

The production `grammars/` copies suppress unnecessary Pest parse-tree output:
ordinary rules are silent except `OntologyDocument`, `DGRule`, and `DGAxiom`;
compound-atomic rules become atomic. Rule expressions and atomic whitespace
semantics are unchanged. This avoids retaining per-character IRI parse nodes
for the entire ontology. Differential tests compare acceptance against the
unchanged upstream grammar; description-graph rejection remains explicit.

KM also corrects `AtomDataProperty` to use `IArg DArg`, rather than the
upstream `DArg DArg`: SWRL data-valued properties relate an individual to
a data value. See https://www.w3.org/submissions/SWRL/#2.1 . The unchanged
upstream copies retain the original rule for provenance. Dedicated tests
cover named and variable subjects and reject literal subjects.

KM corrects `RFC3987_IriPathEmpty` to the empty string. RFC 3987 section 2.2
defines `ipath-empty = 0<ipchar>` as zero characters; the upstream expression
instead consumes a literal `0` and one path character. Tests admit empty-path
absolute IRIs with optional query/fragment and continue to reject relative
IRIs and malformed escapes. The upstream provenance copy is unchanged.
