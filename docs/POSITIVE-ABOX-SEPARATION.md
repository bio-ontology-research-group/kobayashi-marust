# Positive-ABox separation certificate

## Result

KM may omit an ABox during named-class classification only when the source
profile carries `positive_abox_tbox_separable: true`. This is a semantic
certificate with a fail-closed syntactic checker. It is not a decision-tree
prediction and cannot be learned from corpus agreement.

The certificate closes the assertion-heavy ORE ontologies 10697 and 15725.
Their exact nominal runs reached KM's 190 second internal cap under every
tested schedule. The default automatic route now selects `cb_plain16` and
matches the retained Konclude signatures exactly:

| Ontology | Auto route | Wall on `ws` | Peak RSS | Canonical pairs | Signature SHA-256 |
|---|---:|---:|---:|---:|---|
| 10697 | `cb_plain16` | 0.9152 s | 161.57 MB | 506 | `7ef5274bff5da1265da9caf1bf27fbebeeb483aef1ef0c5042648b1408918a22` |
| 15725 | `cb_plain16` | 0.7212 s | 123.62 MB | 774 | `42436eeb45b30ea78e04c949ee44ed2b01fd517c889e603da4aa5afe491dbba3` |

Both comparisons report zero extra pairs, missing pairs, extra or missing
unsatisfiable classes, and no consistency difference. ORE 15846 is deliberately
not certified. It contains nominals, equality and inequality assertions, and
disjointness, so it remains on the exact nominal route even though proxy CB
happens to agree with Konclude on this one corpus input.

## Konclude diagnosis

Konclude does not repeat the entire assertion closure inside every class test.
Classification depends on consistency precomputation through
`COntologyProcessingStepVector`. In
`CTotallyPrecomputationThread`, individual saturation and the all-assertion
individual are processed once. The method
`isAllAssertionIndividualSaturationSufficient` accepts that result only when
the relevant saturation status is completed, non-clashed, and not marked
insufficient.

Official Konclude trace job 48947466 measured the boundary directly:

| Ontology | Parse | Preprocess | Consistency precompute | Class classification |
|---|---:|---:|---:|---:|
| 10697 | 1,144 ms | 380 ms | 1,211 ms | 3 ms |
| 15725 | 859 ms | 287 ms | 540 ms | 2 ms |
| 15846 | 1,664 ms | 1,317 ms | 16,164 ms | 80 ms |

KM's exact nominal calculus currently constructs and saturates one complete
ground context in every independent query engine. Diagnostic job 48946944 ran
10697, 15725, and 15846 with central single-thread scheduling and fixed
per-function scheduling at 1, 8, and 16 threads. All 12 runs reached the 190
second internal cap or the 240 second harness limit. The problem is repeated
ABox computation, not thread assignment.

## Exact source contract

The checker first requires at least one ABox axiom and a successful parse in
KM's supported functional-syntax grammar. It then requires every top-level
axiom to belong to this whitelist:

- declarations and annotation axioms;
- `SubClassOf` and `EquivalentClasses`;
- object subproperty and property-chain inclusions, property equivalence,
  inverses, transitivity, symmetry, reflexivity, functionality, inverse
  functionality, domain, and range;
- data subproperty, data-property equivalence, and data-property domain;
- positive class, object-property, and data-property assertions.

Imports and every unlisted or unknown axiom fail closed. Inner class and role
expressions must additionally contain none of the following:

- `owl:Nothing`, `owl:bottomObjectProperty`, or
  `owl:bottomDataProperty` in a logical position;
- complement, class or role disjointness, asymmetry, or irreflexivity;
- minimum, maximum, or exact cardinality;
- a nominal, has-value expression, equality or inequality assertion, or
  universal role;
- a datatype constructor, data range, functional data property, datatype
  definition, or key;
- a negative assertion or DL-safe rule.

Bare positive data assertions are allowed. Data ranges and constraints are
not. Functional and inverse-functional object properties are allowed because
all named individuals may denote the same object in the certificate model.

The implementation records explicit bottom-class and bottom-role counts. This
matters because positive-looking syntax such as `A SubClassOf owl:Nothing` or
an assertion on `owl:bottomObjectProperty` is a negative constraint even when
there is no complement constructor.

## Proof

Write the ontology as a TBox/RBox `T` and ABox `A`.

First construct a one-object interpretation `P`. Its object domain is
`{p}`. Interpret every named class as `{p}`, every object property as
`{(p,p)}`, and every named individual as `p`. Interpret each permitted data
property as relating `p` to the values of all asserted literals. The accepted
positive class constructors evaluate to the full object domain. Every accepted
class axiom therefore holds. All accepted role inclusions, chains, inverses,
domain and range axioms, symmetry, reflexivity, and transitivity hold. Object
functionality and inverse functionality hold because the object domain has one
element. Every positive assertion holds by construction. The excluded
constructors are exactly those that can invalidate this model. Thus `P` is a
model of `T ∪ A`, proving consistency.

Now suppose `T` does not entail a named-class subsumption `C SubClassOf D`.
There is a model `M` of `T` with an element in `C` but not in `D`. Form the
disjoint union of the object domains of `M` and `P`, keep each object-property
relation inside its original component, and interpret the ABox individuals in
the `P` component. The whitelisted nominal-free constructors are local to a
component, and their axioms are preserved by this union. Functionality,
inverse functionality, reflexivity, transitivity, symmetry, and role chains
are also preserved. Nominals and the universal role are excluded precisely
because they would connect the components. The witness from `M` remains in
`C` and outside `D`, while the `P` component satisfies `A`. Therefore
`T ∪ A` does not entail the subsumption either.

The converse is immediate because `T` is a subset of `T ∪ A`. Hence `T` and
`T ∪ A` have exactly the same named-class taxonomy, and an independently
complete TBox mechanism is sound and complete for the classification request.

## Routing and validation

The source profiler emits schema version 2 with
`positive_abox_tbox_separable`, `bottom_occurrences`, and
`bottom_role_occurrences`. The hard semantic gate runs before the generated
performance tree:

- certified positive ABoxes enter the same independently complete EL/CB tree
  as the nominal-free core;
- every other ABox selects `nominals`;
- rules remain on their separate exact rule contract.

The post-whitelist optimized test suite reports 1,516 passed, 0 failed, and 7
ignored. Automatic-route regressions 148, 178, and 11016 all remain
certificate-false and match their Konclude signatures exactly. ORE 15846 is
also certificate-false. A fresh schema-2 profile sweep and the final paired
automatic-route sweep run on IBEX after the independent-mechanism matrix.

This change does not alter any CB inference rule or derived fixpoint. It adds a
source theorem and dispatches a certified input to the existing complete TBox
calculus, so it does not require Lean re-certification.
