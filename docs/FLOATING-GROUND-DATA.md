# Ground floating-point data values

The ground-data projection admits xsd:float and xsd:double literals using
separate canonical IEEE bit keys. Numeric lexical forms pass an explicit
XML Schema grammar check before Rust rounds to the respective IEEE format.
Whitespace normalization accepts only XML whitespace. INF, -INF, +INF and
NaN use explicit handling; NaN gets one canonical value key per datatype.
The numeric sign bit remains present for zero. All existing whole-source
admission checks remain in force.

OWL 2 functionality compares value identity, not floating-point numeric
equality: +0 and -0 are distinct, and float/double are separate value spaces.
Source: https://www.w3.org/TR/owl-syntax/#Floating-Point_Numbers .
The existing functional model-extension proof applies unchanged. The new
FloatingDataIdentity module proves signed-zero and cross-primitive clashes
under that proof's owner-compatibility contract. This does not mechanize
Rust's lexical-to-IEEE parser; that trusted frontend boundary is covered by
lexical unit tests, independent reasoner comparisons and source-bound corpus
validation. Those end-to-end checks are required before promotion.

Status: experimental. Standalone scanner unit tests and identity lemmas pass;
classification integration, independent references and full gates are pending.

## Reference checks

HermiT and Openllet agree on six of eight fixtures (12 complete checks),
including signed zero, rounding aliases, NaN, and opposite infinities.
HermiT correctly rejects a shared functional value across float/double;
Openllet reports that case consistent. Both reject the +INF spelling.
The expected outcomes remain specification-bound: OWL 2 section 4.2 makes
float/double spaces disjoint, and the normative XSD 1.1 section 3.3.4.2
explicitly admits +INF. OWL 2's 2012 change log makes XSD 1.1 required.
These reference discrepancies are retained in the evidence, not counted as
agreements. See https://www.w3.org/TR/xmlschema11-2/#float and
https://www.w3.org/TR/owl-syntax/#Changes_Since_Recommendation .
