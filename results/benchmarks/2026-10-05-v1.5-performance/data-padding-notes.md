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
