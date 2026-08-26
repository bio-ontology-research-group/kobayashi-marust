# Medium pure existential-leaf source route

This candidate extends the proved direct existential-leaf route to Functional
Syntax sources between 4 and 32 MiB. It recognizes the complete source in one
allocation-free pass and publishes an empty taxonomy only when every logical
class axiom has shape `A SubClassOf exists r.B` and the remaining logical
content is a positive role box. The existing `flatNF1Leaf_sub_iff_flatReach`
and `flatNF1Leaf_has_model` theorems specialize to an empty NF1 graph, proving
the empty taxonomy and consistency verdict.

The candidate remains provisional. Binding evidence requires exact retained
signatures for every selected ontology, fallback controls that measure the
extra lexical pass, and a complete sweep showing that aggregate miss overhead
does not exceed the gains.

Local focused test
`pure_leaf_screen_proves_empty_taxonomy_without_a_graph` passes. Isolated IBEX
build job `50846606` completed from a 246-file source manifest and produced
binary SHA-256 `413d500c27c78afa9718489ee48296a75b98b0649dcdd217461313bb6b300275`.
Dependent exact-signature array `50846607`
contains fourteen medium pure-leaf sources and three fallback controls
(ORE868, ORE3836, and ORE7499). No timing claim is made before those records
complete and pass their checkpoint, binary-hash, and retained-gold checks.

Array `50846607` completed all seventeen records with terminal checkpoints,
the pinned binary hash, and exact retained-gold signatures. Thirteen medium
sources select `flat_nf1`: ORE269, 5815, 7256, 7343, 7831, 8145, 8557, 13902,
13964, 14508, 15099, 16559, and 16684. Their summed wall time is 1.0392 seconds
and summed process-tree peak RSS is 56.59 MiB. The retained v0.2.36 records for
the same thirteen inputs total 7.3650 seconds and 1,095.49 MiB, so this
hardware-unconstrained functional evidence saves 6.3258 seconds and 1,038.90
MiB. ORE15178 safely declines and follows ELC; its 0.3435-second, 87.44-MiB
record is effectively flat against the retained 0.3312-second, 87.02-MiB
measurement.

The controls remain exact. ORE868 follows ELC and ORE7499 follows the certified
cardinality proxy. ORE3836 is accepted by the already-present large flat-NF1
route, so it is not evidence about the new medium threshold. A complete sweep
must measure the added lexical-screen cost on every other 4–32 MiB miss before
the medium extension can be integrated.
