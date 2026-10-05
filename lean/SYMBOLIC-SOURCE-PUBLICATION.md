# Symbolic cardinality source path

The automatic classifier selects this source path for rule-free inputs of at
most 64 MiB containing an object cardinality of at least 128. The token scan is
a scheduling hint; complete source admission remains mandatory. The explicit
`KM_SYMBOLIC_SOURCE_BRIDGE` override selects the same path for diagnostics, and
`KM_NO_SYMBOLIC_SOURCE_BRIDGE` disables automatic selection. This entry keeps
number restrictions symbolic during frontend normalization. The ordinary
clausal expansion can allocate quadratically many distinctness constraints
before a reasoner starts. This path transfers bounds through source-expression
provenance to the native completion bridge instead.

`SymbolicFrontendResult` prevents accidental ordinary CB/EL consumption.
Its `source_bridge_input` method checks bound/definer correspondence, complete
source coverage, symbol tables and typed ABox installation. Active or unsupported
rules decline this rule-free worker. The resulting native input must have zero
dropped clauses. Existing bridge admission and datatype checks remain in force.

The classifier releases the frontend clause storage before native reasoning.
Only a complete native result reaches output mapping. Public classes retain
their full IRIs, including declared names resembling internal markers. Generated
concepts are hidden. Native global inconsistency, a frontend inconsistency flag,
or an unsatisfiable asserted class produces an inconsistent result with empty
taxonomy fields. A worker decline produces an error, not a partial taxonomy.

`NativeCardinalityNormalization` proves the minimum/maximum complementary
definition correspondence. These theorems are conditional on complete matching
source provenance; they do not certify arbitrary frontend data structures.
CB and HT surfaces audit them. The routing release gate also requires these
audits, the symbolic handoff/worker regression, output-mapping regression and
`symbolic_source_classification` command-line tests.

Requested HT runtime certification is explicitly rejected by this experimental
entry until its source-bound publication evidence is implemented. Its tests
check that requesting a certificate cannot silently select the ordinary native
answer instead. Automatic-selection CLI tests enforce the same boundary.

Avoiding frontend expansion does not guarantee fast completion reasoning.
Original 15687 passes the checked handoff and datatype admission with zero drops
but its diagnostic native run still reaches the 240-second limit. Integrated
benchmark execution, validation of default routing, exact-tag production gates
and the full corpus comparison remain separate release obligations.

Successful completion-node initialization now materializes an empty concept
queue when none exists. Otherwise the scheduler repeatedly interprets absence
as unfinished initialization, starving pending cardinality work. This changes
queue bookkeeping only: inherited/pending descriptors remain intact. The
routing gate requires the queue-level regression and the CLI contradiction
and satisfiable-neighbor tests.

An automatic symbolic decline restores the attempt's environment and continues
through the ordinary classifier, preserving its existing coverage. Explicit
symbolic requests and requested HT runtime certificates still report rejection.
A universal-role fixture exercises native decline followed by successful
ordinary classification; the scheduling hint never authorizes a partial result.
