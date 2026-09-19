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

## General object-only atomic ABox projection candidate

12128 has 220,948 class assertions and an object-only TBox with inverse roles,
functionality, universals and disjunction. The existing atomic projection was
restricted to positive EL even though `KMAtomicABoxPublication` proves its
model construction for any TBox closed under disjoint union.

The new raw-source whitelist also admits ordinary object-only SROIQ without
nominals, the universal role, keys, imports or rules. Datatype constructors and
data properties stay outside this extension. The existing independent observer
must still establish complete atomic assertion coverage and at most one class
per semantic individual. Every asserted class remains a satisfiability query;
any unsatisfiable asserted class makes the final ontology inconsistent. A
worker that drops clauses cannot publish a projected result. No consistency
assumption is inferred merely from the syntactic whitelist.

The proof obligations are the existing `atomicSatisfiable_iff_classes` and
`nativeAtomic_taxonomy_exact`, built by the routing certification gate. New
coverage and semantic regressions, all four gates, and the real-input replay
must pass before this candidate is accepted.

The 12128 source has 220,948 class assertions over four classes, with exactly
one class per individual. Of those individuals, 220,931 use anonymous labels.
The original absolute-IRI screen rejected these labels. The revised screen
also accepts simple unescaped anonymous labels in their document-local
namespace. Shared labels still share a class constraint, and prefixed or
relative named-individual spellings remain outside the multi-class shortcut.
The Lean `scopedIndividual_injective` theorem proves that injective maps for
the named and anonymous namespaces combine when their identifier ranges are
disjoint; it introduces no axioms. The existing full-model construction then
applies without a unique-name assumption.

The revised source passes 28 focused unit tests and four integration tests.
Four original anonymous-individual sources exactly match HermiT consistency,
full-IRI taxonomy and unsatisfiable-class output, with zero dropped clauses.
The frozen atomic-source-v1 passed all four certification gates. The revised
atomic-source-v2 has passed all four certification gates. Corpus validation
is pending. The first 12128 diagnostic failed before this label
fix. A separate diagnostic established that its CB fallback reaches the
25-million-message safety limit. Raising that limit to 250 million still
failed to finish within 600 seconds and is not an accepted fix.
