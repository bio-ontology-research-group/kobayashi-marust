# Boolean inclusion clashes before unsupported rules

Ontology 10906 declines because one rule has a data-property atom. Both HermiT
and JFact classify the original source as inconsistent in 2–3 seconds. A
four-axiom subset already proves the clash: an asserted B is an arm of a union
equivalent to N, N is a subclass of A, and A is disjoint from B. KM's named
ABox precheck previously missed the entailed B-to-N edge.

The precheck now extracts necessary named inclusions by distributing unions
on the left and intersections on the right. Equivalences contribute both
inclusion directions. Intersections on the left and unions on the right do
not produce individual named edges. The existing graph closure and disjoint
membership check consume these sound edges; full clausification is unchanged.

Unsupported-rule errors are deferred until the source ABox clash checks.
Only a proven base inconsistency suppresses the error. Additional rules cannot
restore a model of an inconsistent base. Consistent controls with unsupported
rules still decline.

The Lean module BooleanABoxClash proves the two Boolean projection steps,
equivalence directions, path composition, asserted disjointness clash and
inconsistency under additional constraints. All six lemmas introduce no
axioms; source-to-model binding remains the precheck's explicit obligation.
They are audited in CBCertificationSurface.

All 13 focused ABox unit tests and two end-to-end tests pass. The first unit
run exposed an old allocation-gate oracle that expected no edges from
G equivalent to A intersection B. The oracle remains unchanged; the test now
explicitly requires exactly the two new entailed edges in addition to its
original expected projection. Both Boolean polarity controls are retained.
All four CB, HT, routing and ELC certification gates pass. The 22-ontology
rule panel changes only ontology 10906: declined becomes a complete
inconsistency result in 0.078 seconds. Every other status and successful
output hash is unchanged. Full 592-ontology gold and 1,920-ontology standard
budget regression runs remain in progress; this candidate is not released.
