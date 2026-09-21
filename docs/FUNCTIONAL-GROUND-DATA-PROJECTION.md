# Functional ground data projection

This candidate extends the ground-data model projection to functional data
properties. Each distinct admitted value of a functional property gets an
integer identifier. Owners receive private positive or negative class labels
for that identifier's bits. Two owners with different values therefore cannot
merge. Owners with equal values may merge, and different properties use
separate labels. The number of assertions grows with facts times the bit width,
not with pairs of owners. None of the private labels is a public class IRI.

The source recognizer closes assertions under subproperties, validates inherited
ranges, and materializes domains as in the non-functional projection. It admits
strings, booleans, and integers whose lexical forms and values satisfy the
supported integer datatype restrictions. Integer values outside i128 and other
datatypes decline. Integer aliases such as `+001` and `1` share a value, while
string `1` and integer `1` do not. Boolean `true` and `1` share a value.
Quoted-string decoding follows the two escape forms in the
[OWL functional syntax grammar](https://www.w3.org/TR/owl-syntax/#Integers,_Characters,_Strings,_Language_Tags,_and_Node_IDs).

FunctionalGroundDataProjection proves exact extension of the object model to
a data model, equivalence of functionality and compatible owner values, and
existence of private bit predicates exactly when owner values are compatible.
These model lemmas introduce no axioms. The bounded bit-code injectivity lemma
uses Lean's standard propext and Quot.sound through natural-number bit lemmas;
it introduces no new axiom or admission. The implementation checks the bit
capacity and uses distinct ordered-map keys to assign identifiers.

The projection also requires three runtime invariants. Complement elimination
must preserve definitions referenced by the separately installed native ABox.
The CB ground context must instantiate universal facts on named individuals.
The bridge's saturation cache must not claim completed equality handling when
a positive foreign nominal has no corresponding merge metadata. Such entries
remain incomplete and ordinary completion decides their equalities.

The eight reference fixtures agree with HermiT and Openllet. All 48 targeted
runs pass across automatic, nominal and general-HT routes in both process
modes. The source-bound Lean checker accepts generated ground-fact evidence,
including duplicate elimination and removal of false head literals. Full
certification gates and corpus regression checks remain required before
promotion. Ontology 4572 has 98,867 data assertions; the exact projection emits
98,867 domain assertions and 1,201,087 private bit assertions.

## Disjoint positive bit markers

The next candidate replaces each signed bit assertion by a positive marker
for its polarity, with a disjointness axiom between the two markers. It adds
no excluded-middle axiom. Unrelated objects can remain outside both markers;
objects with asserted values still receive every bit of their value code.
The Lean theorem `compatible_iff_disjoint_bit_model` proves that these
constraints have exactly the same owner compatibility condition. The existing
model-extension and bounded-code injectivity theorems complete the argument.
This encoding targets avoidable global branching observed on ontology 4572.
Performance and full certification results are pending.
