# ORE 10860 rule/ABox adjudication

This package records the direct adjudication of `ore_ont_10860.owl` (source
SHA-256
`480139a6018bc4eb0d35e47edf00a6d257dd87137c1d0f93a27021cf154f4a2d`).
The ontology is inconsistent under its DL-safe rules. Konclude's rule-free
answer is not valid gold for this input because Konclude does not evaluate the
source SWRL rules.

## Explicit inconsistency witness

The source contains a named situation with an unqualified exact-cardinality
restriction `=1 hasR2RRelation`, plus an existing
`hasR2RRelation(..., equalRelation)` assertion. One DL-safe rule has a complete
explicit named-ABox match for that situation and derives
`hasR2RRelation(..., notEqualRelation)`. The two targets are explicitly listed
in a `DifferentIndividuals` axiom. The rule body includes a
`DifferentIndividualsAtom` whose two bindings have asserted types
`Hospitalization_Department` and `OutPatient_Clinic`; those classes are
explicitly disjoint. The two distinct role fillers contradict the unqualified
exact-cardinality-one assertion.

`ore_ont_10860_unsat_core.ofn` retains only this witness. IBEX HermiT job
`49718396` rejected the core with `InconsistentOntologyException`, independently
confirming the contradiction.

## Rejected sandwich experiments

The first experiment removed all rules and asserted every possible rule head
for every named individual. Konclude job `49718040` found that stronger
ontology inconsistent, so it could not establish consistency by sandwiching.
The per-head array `49718059` and the exact-zero-cardinality exclusion variant
also became inconsistent. These are retained as negative experimental evidence,
not as the adjudication.

## KM certificate

KM now performs a fail-closed finite named-ABox rule match. It accepts a clash
only when all of the following are explicit in the parsed source:

- an unqualified `ObjectExactCardinality(1 R)` assertion on the rule-head
  subject;
- a complete match for every supported body atom;
- an existing `R` assertion for the same subject; and
- provable inequality between the existing and derived targets, either from
  `DifferentIndividuals` or from explicitly disjoint asserted named types.

Unsupported data/builtin atoms and unbound equality guards produce no witness.
Qualified cardinalities are rejected. Synthetic negative controls revoke each
essential premise. On the full frozen 10860 source, plain default
`km classify` returns `consistent:false` in 0.03 seconds at 10.7 MiB on the
workstation. IBEX production array `49721626` completed all 592 ontologies.
Audit `49734184` accepted all terminal rows, checkpoints, production route
traces, and the frozen binary identity. The automatic 10860 row selects
`ht_rules` and completes in 0.0403 seconds at 10.31 MiB. The final sweep has
587 exact Konclude-signature matches, the adjudicated 2669 and 15516
consistency mismatches, adjudicated 10860 `ok/nogold`, one 1194 error, and one
4669 timeout. The retained audit receipt is [`audit-49734184.out`](audit-49734184.out).
