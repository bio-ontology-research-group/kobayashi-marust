# Certified separable-ABox elision candidate

This candidate builds on the exact named-hierarchy route. It operationalizes
the existing `positive_abox_tbox_separable` source certificate: when automatic
routing selects ELC, the frontend removes the certified-irrelevant positive
ABox AST before clausification and skips redundant ABox side analyses.

The certificate already proves that the accepted ABox is consistent and cannot
alter a public TBox subsumption. Inputs with bottom, disjointness, complement,
number restrictions, active nominals, datatypes, rules, imports, universal-role
constraints, unsafe identity/functionality interaction, or an unrecognized
axiom fail closed and retain the established path. Set
`KM_NO_SEPARABLE_ABOX_ELISION=1` for a same-binary differential baseline.

Release evidence requires exact full-IRI signatures, consistency, unsatisfiable
classes, route traces, and lower wall/RSS measurements on every affected ORE
ontology, followed by the full 592-ontology gate.
