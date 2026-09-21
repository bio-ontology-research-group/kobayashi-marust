# Native SameIndividual seeds

The typed frontend and the legacy native ABox installer retain source equality, but the Konclude bridge builds its seeds from the source metadata. It previously installed DifferentIndividuals and omitted SameIndividual. This allowed a positive assertion and its negative assertion on equal owners to appear consistent, including with all saturation caches disabled.

The bridge now installs each equality as positive nominal assertions in both directions. Ordinary nominal completion performs the merge and preserves both labels. Source coverage validates both equality endpoints before construction. This works with anonymous source identifiers and does not impose unique names.

NativeSameIndividualSeeds proves that the bidirectional nominal seed obligations have exactly the equality semantics, and that contradictory assertions on equal owners have no model. It does not certify Rust lookup, queue processing, or cache behavior. Runtime regressions cover cached and uncached completion, a satisfiable unequal-owner control, invalid endpoints, and the frontend CLI fixture in process and in a subprocess. All certification gates and reference benchmark checks remain required before release.

The sparse empty-role model certificate assigns distinct elements to source names. It now verifies every SameIndividual obligation against that assignment. Nontrivial source equalities decline this witness and continue through ordinary completion; the implementation does not assume they are inconsistent. A regression combines SameIndividual and DifferentIndividuals under a nonempty, satisfiable TBox.
