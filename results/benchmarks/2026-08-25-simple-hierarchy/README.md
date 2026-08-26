# Rejected named-hierarchy candidate

This directory records the first v1.1.0 performance candidate based on v1.0.0
commit `ef9e9893dcfa8794be630afd47b34ceca86c1c2f`. The candidate adds an exact,
complete-answer-or-defer source route for Functional Syntax ontologies whose
logical content consists only of named `SubClassOf` and `EquivalentClasses`
axioms.

Release claims require all of the following evidence:

1. an IBEX-native release build with a recorded binary SHA-256;
2. byte-identical full-IRI classifications versus v1.0.0 for every ontology
   accepted by the route;
3. no status, consistency, unsatisfiable-class, or taxonomy regressions in a
   full 592-ontology sweep;
4. same-node performance measurements for affected ontologies; and
5. complete aggregate comparison against the frozen external reasoner panel.

The candidate was rejected and removed from the v1.1 source. Focused job
`50838916`, task 0, tested ORE868. Both v1.0.0 and the candidate selected `elc`,
matched the same full-IRI signature
`be6be6663ffd9721606bf3cb61308789c55c28ffbe8d4ba2d85d0ee60b7fcc0f`,
and took 30.6156 s and 29.7128 s respectively. The source-level recognizer did
not see Functional Syntax because the ORE corpus input reaches format
conversion later in the pipeline. The remaining array tasks were canceled.
This route therefore offered no benchmark benefit at its insertion point and
is not part of the retained candidate.
