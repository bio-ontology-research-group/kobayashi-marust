# Nominal ABox/TBox projection investigation

The v0.2.36 profile spends 94.0218 wall-seconds and 18,189.34 MiB of summed
process-tree peak RSS on the nine representative nominal-route ontologies
ORE148, ORE1790, ORE3050, ORE6765, ORE7474, ORE8322, ORE8480, ORE8999, and
ORE16462.

Diagnostic array `50844724` removed only top-level ABox axioms from a temporary
copy of each Functional Syntax source, then classified the retained TBox with
the unchanged KM binary. All nine runs were checkpointed `status=ok` results
whose full-IRI signatures, consistency verdicts, unsatisfiable classes, and
subsumption counts matched the original retained gold. The contended diagnostic
run consumed 32.5457 wall-seconds and 1,905.73 MiB of summed peak RSS. This is
evidence for an optimization opportunity, not a sound route: deleting an ABox
without proving full-ontology consistency would be incomplete on inconsistent
inputs.

The intended route contract is the standard disjoint-union argument. For a
nominal-free, universal-role-free TBox, an exact consistency witness for the
full ontology can be disjointly united with any TBox countermodel while all
named individuals are interpreted in the witness component. Therefore a
consistent ABox cannot add a TBox subsumption. Inputs with a concept-level
nominal, universal role, key, import, incomplete source partition, or an
uncertified global-consistency result must decline to the v1.0 route.

Array `50844958` forced the existing `ht_general` worker into exact global
consistency mode. Eight representatives completed consistently in 0.16–1.19
seconds with 22.78–127.04 MiB peak RSS. ORE16462 did not finish economically:
it has only two ABox axioms over a roughly 50-MB TBox and was cancelled after
167 seconds. The composed prototype therefore applies a source-level minimum
of eight ABox axioms and a three-second exact-worker budget. A timeout or
structural refusal kills and reaps the exact child and falls through unchanged
to the v1.0 route.

The opt-in prototype uses `KM_ABOX_DISJOINT_UNION_CHECK=1`. It first runs the
exact full-ontology consistency worker. An inconsistent verdict is already a
complete classification. A consistent verdict authorizes one recursive
frontend pass that removes the ABox while preserving every source-signature
class, including classes mentioned only in the ABox. The source gate excludes
concept-level nominals, the universal role, keys, imports, and rules. It is not
enabled by default and cannot be released before the disjoint-union theorem is
formalized and the source-to-theorem gate is checked.

`HypertableauDisjointUnionABoxProjection.lean` now proves the semantic core:
given an exact full-ontology model and model amalgamation that preserves the
ABox witness component and every requested public concept predicate in an
arbitrary TBox-model component, ABox-relative and TBox-only subsumption are
equivalent for those public concepts. This distinction is necessary because
native ABox proxy concepts are internal singletons and must remain false in
the countermodel component. The stronger all-concept theorem remains as a
corollary. Both the module target and repository import check without
`sorryAx`; the theorem surfaces report only `propext`, `Classical.choice`, and
`Quot.sound`. This deliberately does not yet certify the executable source
screen; the remaining proof obligation is that every admitted source TBox
constructs the required public-concept disjoint-union amalgamation and that
the requested taxonomy signature contains no internal proxy.

The next proof layer is now constructive. Lean defines a masked disjoint union
that retains the witness interpretation on its left component, retains the
countermodel interpretation on its right component, makes all cross-component
roles false, and masks native singleton proxies only on the right. It proves
that masked-disjoint-union closure plus public/proxy signature separation
implies the required `ModelAmalgamationFor`. The executable frontend now checks
that no native singleton proxy occurs in `named`; ordinary assertion markers
remain public because they carry no singleton constraint. The remaining proof
boundary is reduced to masked-disjoint-union closure for the source-admitted
TBox fragment.

The module target and the repository-level `ContextCalculus.lean` import both
build successfully. The source gate conservatively rejects every concept-level
nominal, including `ObjectOneOf` and `ObjectHasValue` nested in domain/range
positions; named individuals occurring only in the ABox do not trigger that
TBox exclusion.

Isolated candidate build `50845209` passed the focused source-gate and ABox-only
query-signature regressions. Its source-manifest SHA-256 is
`e08c768451f3fdb82c13b6d28f5efc7da331a2606ed5bbe493edd631c0d54583` and
the installed binary SHA-256 is
`2f3aa924949fd1ae5f2461a3d5b3a163f71e0ad5fef9f0726eef373d56a31aa1`.
Dependency array `50845308` performs order-balanced same-binary comparisons of
the opt-in and unchanged paths on the nine representatives, requiring exact
retained-gold signatures and identical classification metadata in every arm.
Unconstrained functional array `50845332` uses the same binary to establish
correctness promptly; only `50845308` supplies publication-quality Gold-6248
performance measurements.

All nine `50845332` rows matched gold, including the ORE16462 threshold control,
but rejected this implementation as a performance candidate. It reparses and
renormalizes the source after consistency succeeds, producing 10.59–71.49-
second contended runs and a 171.0081-second panel sum instead of the 0.23–3.87-
second TBox diagnostics. Exactness alone is not a v1.1 gate. Gold pair
`50845308` was therefore cancelled before allocation.

Candidate v2 removes that duplicated frontend. Its first pass retains the
complete typed ABox for the exact global check while suppressing only the
duplicated nominal CB clauses, yielding the TBox-only worker view in the same
normalization. A successful check continues on that view immediately. A
timeout or structural refusal sets a one-call decline marker and recursively
rebuilds the untouched v1 nominal input. Focused regression coverage requires
the precheck view to retain the typed individual while emitting no individual
term in its classification clauses. Build `50845460` and dependent functional
array `50845461` were discarded because the allocation began during the final
source synchronization. Replacement `50845494` was then cancelled before
completion when review found that the reused TBox view also had to seed
undeclared ABox-only query classes. The finalized source includes regressions
for that signature case and for subthreshold inputs retaining the complete v1
nominal view. Its remote source tree is write-protected; build `50845528` and
dependent functional array `50845529` were cancelled during the final
adversarial source review. That review closed two additional fail-open gaps:
conditionally nested `ObjectOneOf`/`ObjectHasValue` expressions now reject the
disjoint-union gate, and the process-wide environment guard restores both
internal verdict markers after reusable library calls. After verifying the
remote source layout and write-protecting it again, replacement build
`50845623` exposed a compile error in a newly added recursive test helper and
failed before installing a binary. Its dependent functional array `50845624`
was cancelled after Slurm marked the dependency unsatisfiable. No result from
that pair is performance evidence.

Candidate v3 fixes only that test helper and states the subthreshold contract
at the correct boundary: the ordinary typed nominal ABox remains complete and
the selected source route remains off ELC. The frontend does not promise that
those individuals already occur in its normalized TBox clause vector because
the exact nominal workers consume the separate typed `nominal_abox` channel.
The corrected focused test passes locally. The v3 remote source tree was
write-protected and excluded build artifacts.

Build `50845955` then failed closed before binary installation because its
frozen package omitted the two repository-level `tests/completeness-gaps`
fixtures referenced by compile-time `include_str!` calls. Array `50845956` was
cancelled without running. Candidate v4 adds that complete fixture directory
to the immutable source manifest; it makes no Rust or Lean logic change from
v3. Build `50846066` and its after-success functional array `50846067` are the
current authoritative pair; neither may be used as evidence until the build
receipt and all nine exact terminal rows pass their embedded checks.
The frozen v4 manifest covers 299 files and has SHA-256
`43e0618069c36339c3bfcaf8cb54f637fd193f6c68f83fc862b6eb169f10f276`;
the manifest explicitly contains both external mini7914 fixtures.
Build `50846066` completed all three focused release-mode test invocations and
installed binary SHA-256
`69fe6f20b41d688c63032e093087032a64d39152ef4f6417d77dd12be44b5b35`.
Array `50846067` completed nine unique results and nine checkpoints with no
temporary outputs. Every row is `status=ok`, matches its retained full-IRI
gold signature, and uses the pinned v4 binary. The contended functional panel
consumed 170.0891 summed wall-seconds and 8,083.00 MiB summed peak RSS; those
values do not show the expected performance benefit and are not a controlled
comparison. Order-balanced, same-binary Gold-6248 array `50846429` is the
binding performance gate.

Phase trace array `50850193` localized the v4 regression before its output
shape assertion failed. The exact consistency probe entered the nominal route
after 0.07 seconds on ORE148 and 0.67 seconds on ORE8480, but did not leave the
engine block until 12.63 and 66.66 seconds. Review showed that
`run_ht_only_bounded` performs its synchronous CB-to-HT conversion before its
worker timeout starts, and that the global-consistency caller unnecessarily
passed every public class as a taxonomy query. `KM_HT_GLOBAL` computes full
ontology consistency before returning and never reads that taxonomy query
universe.

The next isolated candidate therefore passes an empty taxonomy query set to
the exact global-consistency worker while preserving the complete clause,
RBox, cardinality, source-axiom, and typed ABox input. This is an
implementation-level allocation reduction, not a logical projection: query
classes are classification requests and are not ontology assertions. The
candidate must still pass all focused tests, nine retained-signature functional
gates, and controlled Gold comparisons before the opt-in route can be enabled.

Review then rejected the first empty-query build (`50850323`, cancelled with
its dependent array `50850324`) before it produced evidence. The ordinary
`ht_general` arm intentionally omits typed native-ABox installation. In the
one-pass projection input, duplicate ground nominal clauses are also
suppressed, so that version could have checked only TBox consistency. The
corrected probe sets a dedicated full-ontology flag that installs the complete
typed ABox while still passing zero taxonomy queries. Its pure routing
predicate is regression-tested in both the ordinary general and global-native
cases.

The first corrected package (`50850372`–`50850374`) was cancelled before
allocation when review found that the dedicated internal flag also had to be a
registered routing key so reusable-library calls restore it. The replacement
source-bound build `50850392` included that lifecycle fix, but was cancelled
before allocation when a second review found two more full-ABox requirements:
the global check must bypass the taxonomy-only atomic-ABox certificate, and it
must enable exact `SameIndividual` collapsing. The replacement synthetic gate
uses two disjoint asserted classes on source individuals connected by
`SameIndividual`, so it detects omission of either the typed ABox or equality
merging. Source-bound build `50850416` feeds that fail-closed gate (`50850417`),
which alone releases the nine-ontology panel (`50850418`). No result is evidence
until every dependency and embedded assertion passes.

Build chain `50850416`–`50850418` was cancelled before allocation after local
edition-2021 parsing rejected an accidental Rust-2024 let-chain. The equivalent
edition-2021 control flow is frozen in build `50850436`; equality-sensitive
inconsistency gate `50850437` controls panel `50850438`.

That chain was cancelled during compilation after review showed that the
synthetic test could still pass through the ordinary v1 fallback. The final
gate now enables an opt-in conductor trace and requires the exact line
`KM_DISJOINT_UNION result=inconsistent`; a decline or worker error cannot pass.
Source-bound build `50850469` controls this direct-verdict gate (`50850470`),
which controls the nine-ontology panel (`50850471`).

Before that build completed, the certification audit rejected the optimized
forced HT search as a release oracle outside its validated ALC(H) route. The
replacement sets `KM_HT_TOTAL_GLOBAL`: it restores the same exact role-chain
clause view used by proof-carrying publication, checks complete TInput coverage,
and obtains the verdict from KM's exhaustive global decision search rather than
from optimized tableau classification. A timeout still declines to v1.

Build `50850544` failed closed in the focused frontend regression before it
installed a binary. The precheck had removed source ABox axioms before
constructing the typed native-ABox payload, so the payload contained zero
individuals. Its dependent jobs did not run and provide no evidence. The
corrected one-pass frontend normalizes the complete source once, retains its
typed ABox metadata, suppresses only duplicate ground clauses from the TBox
worker view, and seeds ABox-only public classes in the projected taxonomy
signature. The isolated regression and the complete six-test disjoint-union
group pass locally. Environment-sensitive tests in that module now share a
mutex, eliminating process-environment races observed when the focused group
ran concurrently.

The replacement immutable v8 chain is build `50851107`, direct-verdict gate
`50851108`, and 49-ontology eligible exact-signature array `50851109`. The
array covers every successful v1.0.0 ontology admitted by the current source
gate; ORE1194 remains reserved for the final full-592 control because its v1
baseline is the sole fail-closed error. No v8 result is evidence until its
dependency, source manifest, binary hash, terminal checkpoint, route trace,
and retained full-IRI signature checks all pass.

Build `50851107` completed in 9 minutes 52 seconds with exit code zero. It
passed all five focused release-mode groups (6 disjoint-union, 1 route
isolation, 43 routing, 13 flat-route, and 47 mirror tests), emitted
`BUILD_COMPLETE`, and installed binary SHA-256
`5707b3c4483a3789befd026a11ac8cda9688f7b4c8bf39e8f5dba5196ca9b107`.
An independent post-job hash matches its receipt. Gate `50851108` is released
from its dependency and scheduler-pending; array `50851109` remains correctly
blocked on that gate.

Gate `50851108` subsequently failed before executing KM because the v8 harness
package omitted the 630-byte `inconsistent-abox.ofn` fixture. Its output is
only `cp: cannot stat`; it produced no trace or classification, and dependent
array `50851109` ran no tasks. The fixture is now staged with matching local
and remote SHA-256
`1188d698e28993b07dbcea2d9bdabed1ce1b941195d610746b199008802d4e08`.
The unchanged binary is being rechecked by gate `50851379`; replacement panel
`50851380` is held by `afterok:50851379`.

The Lean closure boundary is now compositional rather than one opaque
whole-ontology premise. `Clause.MaskedDisjointUnionClosed` states the exact
property required of one normalized clause, and
`Interp.maskedDisjointUnionClosed_of_all_clauses` lifts a certificate for every
member to the complete ontology. The singleton equivalence supports
checker-facing clause proofs. The module builds with four Lean threads; both
new theorem surfaces report only `propext` and no `sorryAx`. The remaining
proof work is a fail-closed syntactic recognizer for the connected normalized
clause shapes emitted by the admitted source fragment.

Gate `50851379` executed the corrected v8 binary but declined before
publication because the native-ABox exhaustive decision required
`KM_HT_LEAN_ROOTED_ORDINARY_PRODUCTION_RUN_CHECKER`. Setting that publication
checker would also activate the complete HT certification protocol and demand
the full checker suite, so neither the decline nor its fallback answer counts
as evidence for the new route. Dependent panel `50851380` ran zero tasks.

The v9 candidate gives the decision-only total-global route a separate
`KM_HT_TOTAL_GLOBAL_ROOTED_ORDINARY_RUN_CHECKER` boundary. The same Lean
executable checks the complete rooted production run, but this variable does
not accidentally request the unrelated taxonomy and publication bundle. The
checker was rebuilt locally with four Lean threads. Local source-bound testing
on `inconsistent-abox.ofn` now emits the required direct trace
`KM_DISJOINT_UNION result=inconsistent` in 0.09 seconds at 72,876 KiB peak RSS.
Replacing the checker with `/bin/false` makes the route decline, after which
the unchanged v1 fallback still returns the correct inconsistent result.

Immutable v9 build `50852155` uses a source snapshot whose modified
`hypertableau.rs` SHA-256 is
`8e7a3b8ffa54a2ba39b4f2ff0f4097f65baaafba0ef0f6b91199192bfa136585`.
The staged Lean executable is independently hash-bound as
`b86a5c40bc31f58b9c82a86149ceee25499d769173c2b26844dfc7a589045d5b`.
Direct-verdict gate `50852156` is held by that build, and the complete
49-ontology eligible panel `50852157` is held by the gate. Every panel task
checks both binary and checker identities before classification.

Gate `50852156` completed successfully and emitted
`INCONSISTENT_ABOX_GATE_COMPLETE`; its direct trace requirement therefore
proves that v9 obtained the equality-sensitive inconsistent verdict from the
new total-global path rather than from fallback. Panel `50852157` is released.
Its first eight tasks (ORE443, 1325, 1340, 1555, 1902, 2313, 2361, and 2678)
all produced terminal checkpoints and exact retained signatures; the remaining
tasks are scheduler-pending. These are functional records, not yet a complete
or controlled performance result.

The connected-clause proof obligation is now discharged in Lean.
`Clause.MaskedComponentLocal` states exactly the conservative executable
contract: every concept mentioned in a body or head is outside the private
proxy mask, and every clause variable is reachable from one root through the
undirected body role/equality graph. The new
`Clause.maskedDisjointUnionClosed_of_maskedComponentLocal` theorem proves this
condition sufficient for masked disjoint-union closure, including concept,
role, existential, equality, and empty-head clauses. The ontology-level
corollary composes those clause certificates with the existing amalgamation
and taxonomy-projection theorem. The complete default Lean build succeeds
without `sorryAx`; the new theorem surfaces use only Lean's standard
`propext` and `Quot.sound` axioms.

Rust now mirrors this contract with a fail-closed clause screen and focused
tests for connected role chains, equality connectivity, disconnected head
variables, private proxies, and variable-free clauses. All five tests pass,
as does the separate test ensuring that the decision-only checker variable
cannot activate the full publication bundle. This post-v9 source is not yet a
benchmark artifact: its remaining release obligation is to bind the exact
wire-decoded clause/proxy payload to the proved predicate before building the
next immutable candidate.

The v9 execution strategy is rejected on performance. Thirty-one completed
rows have exact terminal/checkpoint pairs but produce zero wall-time wins
against the same immutable v1.0.0 rows. Their paired wall delta is +526.0645
seconds and their summed peak-RSS delta is +5,137.99 MiB. The consistency
precheck is therefore not an economical precursor to ordinary TBox
classification, even though both components are exact. Array `50852157` was
cancelled after those 31 results; completed evidence is retained, and pending
tasks consumed no allocation. The semantic theorem remains available for a
future route that can reuse a consistency result already computed for another
purpose, but automatic routing must not enable this standalone precheck.
