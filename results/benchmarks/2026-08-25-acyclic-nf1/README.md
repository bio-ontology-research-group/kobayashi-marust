# Acyclic NF1 taxonomy closure candidate

This candidate replaces the general EL hash-set worklist only when the
normalized ontology contains an acyclic graph of NF1 named-class inclusions.
It excludes bottom conclusions, TOP premises, residual clauses, role axioms,
all other EL normal forms, and checker-backed publication. Cyclic or otherwise
ineligible inputs use the unchanged completion engine.

The candidate computes the least transitive closure in reverse topological
order. Each output pair is retained once in a sorted integer vector. The
`KM_ELC_NO_ACYCLIC_NF1=1` switch provides a same-binary baseline.

Primary targets are the million-class ORE taxonomies 8486, 9674, and 10689;
ORE868 is included as a bottom-bearing fallback control. Controlled timing
uses three alternating same-binary pairs on exclusive Intel Gold 6248 nodes.

## Native build and functional smoke

IBEX build job `50840426` passed both focused tests and produced release binary
SHA-256 `1a0624f9ca9fc1f892887ff44bd5b63f9d1f2791ba3aeb99cf8281d6a3f5fe3b`.

Nonexclusive smoke job `50840554` ran a same-binary differential on ORE10689.
Both arms matched the retained gold signature
`be6be6663ffd9721606bf3cb61308789c55c28ffbe8d4ba2d85d0ee60b7fcc0f`
with 14,809,043 subsumptions. The general worklist baseline took 29.2012
seconds at 1813.34 MiB; the acyclic-NF1 candidate took 27.6322 seconds at
1813.78 MiB. This is a 5.37% wall reduction. The 0.44 MiB peak difference is
measurement-neutral and does not establish a memory change. Because the node
was shared, these figures prove activation and semantic identity, not the
release performance claim.

Exclusive Gold-6248 array `50840430` is the controlled performance gate.
