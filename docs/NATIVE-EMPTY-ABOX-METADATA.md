# Empty ABox coverage metadata

NominalAboxMeta::is_empty decides whether metadata must be serialized. Its complete flag must survive the wire boundary even when the ontology has no individuals or assertions. The native bridge mistakenly reused this predicate to detect nominal semantics, then rejected a complete empty ABox for having no individuals.

The bridge now checks semantic collections, nominal identifiers, and unsupported-input records directly. It ignores only the standalone coverage boolean when all content is absent. Nonempty assertions, equality, inequality, role facts, nominal identifiers, and unsupported records still require full coverage. No calculus rule, scheduling, or derivation changes. The regression compares the entire TBox result with and without empty complete metadata and checks that unsupported content still declines. Benchmark admission and zero-dropped/reference validation remain required.
