# Ground data projection

This candidate preserves the object-model consequences of ground string-valued
data properties with ranges, domains, and simple subproperty inclusions. It
materializes every inherited domain as a class assertion before normalization.
Each literal must belong to every inherited range. Atomic string/top ranges
and finite string enumerations are admitted. Literal nodes are never added to
the object domain.

`GroundDataProjection.exact_model_extension` constructs a separate data edge
relation from the source facts closed under subproperties. It proves both
model directions with arbitrary object theory and arbitrary owner aliases.
The standalone Lean proof passes without axioms. The frontend keeps original
source counts and separately accounts for each projected domain assertion,
including accepted duplicates. Source data coverage is cleared only when the
whole observed data ABox passed this projection.

The admission test declines functionality, negative data assertions, keys,
rules, imports, data restrictions in object concepts, escaped strings, custom
literal types, builtin data properties, and object/data-property name reuse.
These need additional exact semantics; they are not ignored. Datatype prefix
rebinding also declines. The existing coverage error remains the fallback.

This is a development candidate. Full certification, targeted reference
comparison, and benchmark regression checks are required before promotion.
It does not repair the existing general datatype-to-object encoding used by
DataHasValue or quantified datatype expressions.

Frozen source v2 validation completed: all four certification gates (CB, HT,
routing, ELC) passed, as did the Rust integration test and both unit tests.
The six fixtures passed all 36 auto/nominal/general and in-process/isolated
checks. HermiT and Openllet independently confirmed each expected answer.
Original ontologies 1555, 9557, and 10781 now exactly match the gold taxonomy
and unsatisfiable set, in 0.1663, 0.0734, and 3.9217 seconds respectively in
the targeted comparison. Full 592-input and 1920-input regressions are running;
this does not establish completion of the extended benchmark.
