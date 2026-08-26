# Positive empty-source projection

This candidate recognizes a strict line-oriented OWL Functional Syntax
fragment before constructing the general OWL syntax tree. Its TBox contains
only `A SubClassOf E`, where `E` is an existential or an intersection made
only of such leaves. Existential fillers may contain nested positive named,
existential, and intersection expressions. Its ABox contains only positive
class assertions. Full IRIs are mandatory. Built-in top and bottom classes and
roles, imports, annotations, role assertions, negative expressions, malformed
input, and nesting of 256 levels or more all decline before publication.

`ContextCalculus/PositiveEmptySource.lean` proves two semantic obligations for
this recursive expression grammar:

- every accepted source is satisfiable; and
- after all positive ABox assertions are included, named subsumption holds
  exactly when the two queried names are equal.

`ContextCalculus/ELFlatNF1.lean` independently proves the corresponding result
for the normalized simple existential-leaf fragment. The executable recognizer
has positive grammar tests and adversarial decline tests, including bottom
fillers, bottom roles, top subclass sources, and bottom declarations.

The route was initially gated through `KM_POSITIVE_EMPTY_SOURCE=1` while the
following promotion gates ran:

1. a source-bound IBEX build;
2. a complete 592-source acceptance census;
3. exact candidate-versus-established output on every accepted source and
   representative decline controls; and
4. the complete 592-ontology correctness and performance sweep.

The frozen source archive has SHA-256
`1a715e82fad239b96a005c84e696e0b32de8d1b7c7e0ba0d84378ffeef6e9a16`.

The complete census produced 592 terminal rows, no temporary artifacts, and
exactly 15 accepted ontologies: `1012, 1306, 2046, 2253, 4033, 4557, 5602,
5760, 6233, 7993, 9768, 10750, 13482, 14216, 15280`.

Exact panel job `50864972` passed all 15 accepted cases and nine controls in
three arms: frozen v5, v7 with the route disabled, and v7 with it enabled.
Job `50865106` then passed two additional above-threshold miss controls,
ORE3377 and ORE7246. All 26 answers are byte-identical. Exactly the 15 census
members emit `route=positive_empty_source`; all 11 controls retain their prior
route. Across the accepted set, v7-off used 25.80 seconds and 3,818.0 MiB of
summed peak RSS, while v7-on used 3.27 seconds and 55.6 MiB. The two large miss
controls showed no material wall or memory penalty.

The source route is therefore enabled by default in the combined candidate.
The complete 592-ontology correctness and aggregate-performance sweep remains
the final promotion and release gate.
