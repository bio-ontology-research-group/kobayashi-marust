# Checked padding types: isolated coverage experiment

The decimal-only candidate still refused ontology 12566 because its blank
data-node interpretation violated `Tangible-Thing = not Intangible-Thing`.
A source-GCI witness search can assign ordinary classes to the added nodes
instead of requiring every ordinary class to be empty there.

`DatatypePadding.lean` proves five supporting theorems. Adding a disjoint
carrier with no object-role edges preserves class-expression truth on the
original objects, including negation and qualified minimum/maximum cardinality.
On the added carrier, expressions reduce to a padding evaluation. The extended
TBox holds exactly when both the original objects and the padding nodes satisfy
every GCI. The axiom audit reports only `propext` and `Quot.sound`, no `sorryAx`.

These are conditional forward-extension theorems. Data restrictions are
abstract atoms whose interpretation remains a premise. They do not establish
the source-to-expression translation, concrete datatype interpretation,
nominal/RBox obligations, reverse transport from an arbitrary completion model,
or executable source binding. Those obligations remain before production
admission or addition of this path to the certification boundary.

The runtime experiment remains in the detached integral-decimal worktree at
base `2032f765`, together with the integral-decimal literal patch. It is enabled
only by `KM_EXPERIMENTAL_DATA_PADDING`. It tries an ordinary-class seed, closes
atomic superclass implications, then independently checks every source axiom.
Datatype-bearing axioms are included: a positive class that activates an
existential cannot be assigned to an edgeless node. Search is bounded and
incomplete; failure still declines the bridge. Other admission guards remain.

All 74 datatype-focused tests passed, including a new case in which both
possible class assignments activate missing datatype existentials and must
therefore be rejected. The experiment patch and exact source manifest are
recorded without changing production admission.

A local 30-second, 20-GiB, one-CPU diagnostic on the unchanged original 12566
completed in 0.240 seconds. Its full taxonomy and known consistency agree with
Konclude, HermiT, Openllet, and JFact. This contrasts with the decimal-only
candidate's 235-second internal deadline failure, but the local instrumented
time is not a release benchmark and is not added to full-corpus solved counts.

IBEX job 53330046 tests the same eight coverage-tail inputs under the original
240-second, 20-GiB, one-CPU limits, with independent output auditing. Its binary
is pinned and its inventory explicitly records the uncertified experiment.
The production finite-role-index sweep 53329459 continues independently.

The eight-case diagnostic completed: 12566 and 13799 independently verified,
three process errors, and three timeouts. The other six failures remain in the
record. The first experimental binary predates the role-clause guard below;
its result is not a production certificate.

## Role and concrete-data obligations

`DatatypePaddingRoles.lean` adds 14 checked statements covering role inclusion,
inverse roles, chains, functionality, disjointness, irreflexivity, domains,
ranges, singleton nominals, and guarded assignments. It explicitly proves that
the edgeless extension is not reflexive. A second concrete counterexample shows
why guarding only role-head endpoints is insufficient: an unguarded body class
can hold only on the padding carrier and activate a new role conclusion.

The isolated witness search now rejects a role-headed clause unless every
variable in both its body and head is covered by a role premise. This includes
variables in class, existential and equality atoms. Separate existing data-role
guards still enforce permitted endpoint uses. No existing production guard was
weakened. The new check is necessary for this construction; it is not claimed
to establish every remaining source obligation by itself.

`DatatypePaddingData.lean` adds seven checked transport lemmas for actual
two-sorted data roles and value-range predicates: existential and universal
restrictions, qualified minimum/maximum cardinality, and their edgeless padding
interpretations. Both new modules use only `propext`, with no `sorryAx`.
Binding frontend datatype names to the intended value predicates remains an
explicit obligation, as does reverse transport of arbitrary completion models.

All 74 datatype tests passed after tightening the experimental role guard.
The new binary still recovers 12566 in a bounded local diagnostic (0.197 s),
agreeing with Konclude, HermiT, Openllet and JFact. The 13799 control also passes
with independent agreement (0.132 s). These times are local diagnostics. The
patch, source manifest and answer receipts are separate from the original
experiment, preserving its immutable provenance. Production admission and
release solved counts remain unchanged.

## Executable source-GCI witness checking

`DatatypePaddingCheck.lean` adds an executable Boolean evaluator and three
checked theorems: evaluator equivalence, complete-list GCI-check equivalence,
and the resulting conditional TBox extension. The axiom audit reports only
`propext` and `Quot.sound`, with no `sorryAx`.

`DatatypePaddingWitnessCheck.lean` reads the original Rust `source_axioms`
array and checks every entry against a supplied class valuation. It expands
equivalences in both directions and disjointness as a negative conjunction.
The caller cannot select a subset of axioms. It validates constructor shapes
and all nested fillers, including fillers whose value does not affect an
edgeless node. It rejects negative cardinalities, universal roles, unknown
constructors, direct uninterpreted datatype predicates and unexpected axiom
fields. Nominals and self restrictions are evaluated only for padding truth;
their lowering does not claim object-side semantic equivalence.

`check_data_padding_witness.py` is the required entry point. It rejects
duplicate JSON keys before Lean's map parser can erase them, checks private
byte-identical snapshots, rebuilds imported proof modules, and records source,
witness, checker and toolchain hashes. This binds execution to the supplied
typed document; it does not prove that the document includes every original
OWL axiom or that the decoder agrees with Rust and OWL semantics.

The 12566 witness passes all 311 source axioms, expanded to 324 implications.
The blank 13799 control passes all 230 source axioms, expanded to 247
implications. Both witness files and execution receipts are retained.
The diagnostic reader is separate from production admission. The source
decoder correspondence proof, concrete datatype/value binding, complete
RBox/ABox obligations and reverse model transport remain required before
promoting the experimental path. No benchmark case is counted as newly solved
on the strength of this padding check alone.
