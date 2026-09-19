# General HT source ABox coverage

The general HT adapter previously supplied nominal concept ids without the
native ABox. Those ids enable singleton merging but do not create roots for
existing individuals. A class assertion with an existential data restriction
therefore lost its global effect: automatic classification returned consistent
while the unchanged nominal CB route correctly found a contradiction.

Both in-process and isolated general HT now install the complete typed ABox
through the existing source-bound installer, including source equality
components. Installation failure defers to the unchanged nominal CB route.
Retained general HT uses the same installer. A certified TBox-only projection
remains exempt because its ABox has a separate consistency certificate.

The nominal CB frontend also rejects unrepresented data assertions without an
exact omission certificate. This admission guard is necessary until native
data-assertion normalization can replace the old omission. It is a known
coverage reduction and this combined candidate must not be released as a full
benchmark recovery yet.

No inference rule changes. Existing HypertableauNativeABoxProjection and its
source-bound decision and taxonomy wire proofs cover the native construction;
all four certification gates and full benchmark checks are still required.
Four datatype fixtures exercise positive/negative consistency and nominal
class subsumption through automatic and forced general HT, in-process and
isolated execution. Incremental preparation has a direct existing-individual
clash regression as well as the previous add/remove reuse test.

The retained-state regression exposed a second coverage mismatch: source
statistics count duplicate occurrences, while the rich AST stores a set.
Ontology::add now records accepted duplicate class, role and negative-role
assertions, and the coverage check includes those counts. No unparsed axiom
receives credit. ABoxOccurrenceAccounting proves duplicate-constraint and
membership-set model equivalence. The first frozen candidate and failed test
log are retained; the revised candidate must pass the original reuse test.

Validation of frozen source v2 completed: CB, HT, routing, and ELC
certification gates passed, as did the 16 route/process fixture executions,
the data coverage regressions, and six incremental/general HT unit tests.
The full benchmark and 592-input reference comparison are still running.
The combined candidate exposes further omitted-data cases (148, 960, 3050)
that the former general adapter admitted. These remain coverage work, not
successful fixes. The separate data-sort diagnostic also confirms an existing
literal/object-domain conflation against HermiT and Openllet. Neither issue is
resolved by this ABox-instantiation repair; this branch is not a release.

A later diagnostic exposed an opt-in consistency-probe lifecycle bug: a declined
probe left KM_HT_GLOBAL and KM_HT_REQUIRE_MASKED_DISJOINT_UNION_SHAPE set.
The isolated fallback on 7499 returned an empty taxonomy with dropped=0.
EnvironmentGuard now restores both flags, preserving any caller values.
The regression runs in a private test process and checks absent, 0, and 1
initial values. Its before-change control fails; both the actual-source
standalone test and the full Cargo regression pass. Frozen v3 then completed
7499 through the same declined-probe path in 176.4324 seconds, with the exact
reference-validated output hash. This changes environment lifetime, not any
inference rule. The opt-in projection still retains its existing admission
checks and remains opt-in.
