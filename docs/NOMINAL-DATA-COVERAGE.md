# Nominal data assertion coverage

A numeric assertion interacting with a datatype restriction can affect both
consistency and class subsumption through a nominal. The nominal CB frontend
previously recorded these assertions as unsupported but still emitted a clause
set without them. A zero dropped-clause count did not establish source coverage.

Before nominal clausification can publish a usable result, every omitted data
assertion must now have the existing exact redundancy or functional-string
projection certificate. Otherwise the frontend returns an explicit coverage
error. A proved base inconsistency remains a complete answer and takes priority.
This changes admission only; no calculus derivation or ordering changes.

Four numeric regression fixtures check positive and negative facet membership,
with both disjointness and a named class equivalent to an individual. Openllet
2.6.5 confirms the positive clash and positive-only nominal subsumption that
KM previously missed. All four now refuse rather than publish incomplete results.
Controls retain complete answers for redundant data and proved base clashes.

This is a coverage guard, not numeric-rule support. Exact data assertion
normalization and the full benchmark admission audit remain necessary.

All four certification gates pass. The full 592 gold panel contains 573
matches, 15 new explicit refusals, two missing gold files and the same two
contested consistency cases. The refusals are retained as failures; exact
data handling must restore coverage before a complete benchmark release.
