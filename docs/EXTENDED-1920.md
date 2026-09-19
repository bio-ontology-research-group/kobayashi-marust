# Extended 1,920-input completion work

The target is complete classification of every original input, with soundness,
completeness and Lean certification. The v1.4.3 panel completes 1,829 inputs;
79 deadlines, two resource failures and ten syntax declines remain. Increased
resources and experiments do not themselves establish correct completion.

## Resource policy

`KM_RESOURCE_WORKER_MEM_GB` supplies a positive finite RSS limit in GiB for
CB workers and the HT racer. Unlike route-specific `KM_PAR_MEM_GB` and
`KM_HT_MEM_GB`, it survives automatic route normalization and fallback.
Without the explicit resource setting the historical defaults remain intact.
An invalid value emits a warning and retains the route defaults.

This is a per-worker watchdog threshold, not an aggregate reservation. Concurrent
workers, the frontend, output buffers and supervisor also consume memory. Keep
an external Slurm allocation/process-group cap and leave headroom for those
processes. The current investigation stays within the user's 256 GB / six-hour
maximum per ontology. Short diagnostic limits precede larger allocations.

The change affects when a worker is interrupted. It changes neither source
normalization, calculus rules, fragment admission nor acceptance of a completed
answer. Exhaustion still returns failure; it never licenses partial taxonomy
publication. Existing source publication theorems apply to the same accepted
worker results. Exact-source certification gates and experimental semantic
checks remain mandatory before promoting the change. The frozen resource-only
commit `faee067` passed its regression and all four CB, HT, routing and ELC
certification gates. Four diagnostic 64 GiB worker-limit reruns still failed;
the override repairs resource control but does not establish extra coverage.

## Remaining semantic support

The source inventory includes inverse-role chains, datatype SWRL rules and
SQWRL query built-ins. Inverse roles must survive both clause normalization and
typed RBox metadata. Rule handling requires a stated semantics and a proved
conservative projection or complete implementation; deleting unsupported rules
is not a solution. The source inventory and failed attempts remain evidence.

The [SWRLAPI SQWRL semantics](https://github.com/protegeproject/swrlapi/wiki/SQWRL#semantics-of-sqwrl)
describes query operators as observers that cannot write results back into the
ontology. This suggests a conservative classification projection for rules
whose entire head consists of recognized query operators. It does not justify
ignoring arbitrary SWRL built-ins or mixed logical heads. Initial lexical
inventory finds 94 candidate query-only heads among 95 rules in input 15753;
a structural check and Lean model-preservation proof are still required.

## Inverse-chain implementation under validation

Chain operands and super-roles now use the same converse proxy convention as
inverse restrictions. Each proxy adds both implication clauses through the
existing `InverseRoles` normalizer, and an `Inverse` record next to the typed
chain. Source names in the reserved internal namespace are escaped by the IRI
registry. Binary chains are alpha-renamed so their shared variable is central; role
orientations and implications remain unchanged.

`InverseRoleChainNormalization.theory_consequences_preserved` proves both
projection and expansion for an entire chain theory, including shared proxies
and inverse heads. It requires realization only for symbols used by each chain.
The CB certification surface now imports and audits this theorem. The proof
uses only propositional extensionality, with no `sorryAx`. The Rust symbol
encoding and parser remain part of the explicit frontend trust boundary;
structural and end-to-end tests check that correspondence. Full validation of
this implementation and the three original inputs remains pending.

The ABox regression found a second issue: preprocessing removed raw binary chain
axioms even when ground positive and negative role assertions were retained.
Recognition encodings alone did not expose the entailed ground edge. The nominal
ABox stream now retains the original normalized chain implications. This adds
source axioms back to the stream; it does not alter their semantics. Runtime
regression and source-bound certification of this change are pending.

Input 15687 contains cardinalities of one million. The ordinary clausifier
expands pairwise distinctness quadratically and attempted a 240 GiB allocation
before reasoning. This requires a certified compact cardinality treatment for
its actual fragment, not a larger worker watchdog or weakened cardinality.

Retaining raw chains alone did not fix the regression: the CB loader rejected
non-central chain bodies and ground negative-role bodies. Binary chain joins
now use `x` for the shared endpoint. A ground negative assertion `not R(a,b)`
is loaded as `R(x,b) -> x != a`, preserving the original JSON for source
certificates. `centered_binary_chain` and `negative_role_guard` prove both
equivalences in Lean without axioms, including non-distinct individual names.
A direct clause-level replay detected the contradiction with zero dropped
clauses. The full frontend-to-worker regression is being rerun.

## Frozen inverse candidate v3 validation

All four CB, HT, routing and ELC gates passed on the frozen engine/Lean source
manifest. The three inverse-chain regressions pass with zero dropped clauses.
The unit suite passes when default-mode tests and the 21 tests requiring real
checker exports run in their respective environments (2,435 executed; eight
existing ignored tests). All integration groups, binary tests and doc tests
pass in their required checker environments. A global checker export is not a
valid configuration for every default-mode fixture, and parallel environment
mutation can disturb the two transitive-chain unit tests; failed diagnostic
runs are retained beside the successful configured runs.

On IBEX, 2738 completes in 26.3 seconds and exactly matches Konclude's 639,802
relations. Input 2874 completes in 88.9 seconds and exactly matches 648,538
relations and all 4,804 unsatisfiable classes. Both use zero dropped clauses.
Input 8250 now parses, but its CB classification reaches the 550-second
diagnostic deadline. HermiT and JFact complete its reference classification;
Konclude crashes, and that failed attempt remains recorded.

The standard 1,920-input and separate 592-input gold regressions are ongoing.
At the first 475-input standard checkpoint, 38 successful raw output hashes
changed only because fewer clauses are dropped; their semantic results were
identical. At the 521-input gold checkpoint, every status and signature matched
the released baseline, including its known contested-gold and no-gold cases.
These partial checks are not evidence that the full completion goal is met.

A separate rule/nominal witness also invalidates the general assumption that
DL-safe rules cannot affect class subsumption: with Thing equivalent to {a},
the rule Person(x) -> Adult(x) entails Person <= Adult. The existing rule-free
taxonomy stage misses that consequence. Rule-aware taxonomy or a proved
separability condition is required; query-head projection alone will not fix it.


## Unary DL-safe rule normalization

A strict all-rules check recognizes class-only rules with one shared variable.
The frontend replaces each with an equivalent inclusion whose antecedent is
guarded by the union of source named-individual nominals. Every head conjunct
becomes an inclusion. Anonymous source individuals and fresh query witnesses
stay outside the guard; aliases require no unique-name assumption. Mixed or
unrepresented rules prevent the transformation entirely. Original source rule
counts remain recorded beside `normalized_unary_rules`.

The normalized inclusions enter nominal-aware taxonomy classification. The old
rule-consistency shortcut is bypassed for fully normalized rules, so anonymous
individuals are not accidentally treated as DL-safe names. The Lean module
`DLSafeUnaryRuleNormalization` proves the rule and theory equivalences without
axioms. Seven runtime regressions pass. Six original rule ontologies also
match independent HermiT consistency, full-IRI subsumption and unsatisfiable
class results exactly, with zero dropped clauses. All four certification gates
are running against frozen rules-source-v1; completion is not yet claimed.

The inverse-v3 gold regression has now completed all 592 inputs with unchanged
statuses and signatures. At the 1,193-input standard checkpoint, no previously
successful input was lost and 2738 changed from declined to complete. All 96
changed successful JSON outputs differ only in the dropped-clause counter.
The resource probe also completed 16511 with an exact Konclude comparison;
1194 and 2574 still need independent confirmation, and 7192 is newly awaiting
comparison. These resource runs are separate from the standard benchmark.


The final unary-rule source adds a raw-source separability check for class-only
pointwise TBoxes. Its fresh-point Lean theorem proves that an unnamed class
counterexample can be adjoined without changing any source rule instance.
Such inputs keep the retained rule backend. Nominal, universal-role, datatype,
role and anonymous-individual cases remain outside this shortcut. Both original
incremental-source regressions and all seven unary-rule regressions pass, as
do all four certification gates. Six original rule sources exactly match
HermiT, and a nominal-rule incremental add/remove/re-add audit restores and
retracts the expected taxonomy consequence. The earlier unconditional route
change failed the incremental gate; those assertions were preserved.

The inverse-v3 standard sweep is complete: 1,830 ok, 80 deadlines, three errors,
and seven declines. No v1.4.3 success was lost. All 147 changed successful
outputs differ only in their dropped-clause counters, with equal consistency,
taxonomy and unsatisfiable-class results. The separate 592 gold panel remains
unchanged. The final rule-source validation also preserves every status and signature in
the 592-input gold panel. An exhaustive source scan finds 22 rule-bearing
inputs in the 1,920-input corpus; their standard-budget panel has 13 ok,
seven declines and two deadlines, with unchanged statuses and byte-identical
outputs relative to inverse-v3. The remaining unsupported rule forms and
resource failures are still open.
