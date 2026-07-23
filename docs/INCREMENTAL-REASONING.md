# Incremental reasoning

KM provides an exact stateful classifier over its EL++ fast path and the
normalised clause fragment accepted completely by the consequence-based (CB)
worker. The general API supports additions, removals, and atomic replacements.
It never returns a stale classification or the partial result of a declined CB
run.

## Exactness contract

`IncrementalClassifier` accepts the same normalised `JClause` representation
as `km elc` and `km engine`. It chooses a backend for every committed snapshot:

- A pure EL++ snapshot uses the incremental EL completion store. Addition-only
  transactions retain its completed subsumption relation and role graph.
- Every snapshot outside pure EL++ uses a fresh CB fixpoint. This includes
  disjunction, equality, nominal clauses when `KM_NOMINALS=1`, and the
  supported number-restriction normal forms.
- Every transaction containing a removal uses an exact rebuild. It may route
  from CB back to EL when the remaining clause set is pure EL++.

CB saturation state does not yet expose dependency-safe insertion or deletion
operations. KM therefore records CB updates as `exact_rebuild` instead of
pretending that it reused state. `IncrementalChange` reports the backend before
and after a transaction, the strategy, and the retained or newly built fact
counts.

The CB worker can soundly drop an unsupported clause and can stop at a resource
backstop with a sound but incomplete result. Those outcomes are not valid
incremental snapshots. The general API rejects them as `UnsupportedClauses` or
`IncompleteFixpoint`, respectively, and leaves the preceding revision live.
Every accepted result consequently has `dropped == 0` and an empty
`unresolved` list.

This contract covers the direct normalised-clause inputs of the exact CB
worker. It does not accept orchestration side channels such as `rbox`,
`cardinalities`, rules, definers, or source-axiom metadata. The JSONL command
parser rejects unknown fields so that side data cannot be ignored silently.
Normalise the complete source ontology with stable generated names before
opening a session.

## Clause identity and transactions

The initial clauses receive ids `1..N` in input order. Each accepted addition
receives a monotonically increasing id, and an id is never reused after its
clause is removed. Failed transactions allocate nothing.

`add_clauses` adds one transaction, `remove_clauses` removes ids, and
`apply_change` combines both in one revision. A combined change first builds
and validates the complete candidate snapshot, then commits its deletion and
addition halves together. This matters when changing one source axiom alters
several generated normal-form clauses.

All three operations are atomic. Unknown ids, duplicate removal ids,
unsupported clauses, and incomplete saturation leave the revision, clause
union, id allocator, and classification unchanged. Empty transactions are
no-ops and do not advance the revision.

The frontend must keep generated function and definer names stable. Do not
normalise each source-level addition independently. Either use a stable OWLAPI
integration or re-normalise the full source union, remove every obsolete
normalised-clause id, and add every replacement clause in one `apply_change`.

## Why EL reuse is correct

OWL entailment is monotone under axiom addition, so every fact in the old EL++
fixpoint remains entailed after an accepted addition. KM rebuilds the compact
normal-form indexes for the enlarged clause union, retains the old closure,
clears only the derived NF4 propagation index, and replays all retained
subsumptions and edges once. New rule matches enter the ordinary completion
worklist, which runs until empty.

There is one normalisation corner in which the compact EL rule set is not
monotone. A Skolem role half initially maps to `A ⊑ ∃R.⊤`; a later filler
half changes it to `A ⊑ ∃R.B`. KM compares the old and new direct
normal-form sets. If an old form disappears, it completes that EL transaction
from Init and reports `exact_rebuild`.

This reaches the same least fixpoint as fresh EL++ classification of the union:
the retained facts are a subset of the new closure, every new rule sees every
retained premise during replay, and the existing monotone completion loop
recursively processes every new conclusion.

The CB fallback invokes the existing batch `Reasoner` on the complete candidate
clause union. It publishes the result only after saturation reaches a fixpoint
and only when no clause was dropped. No completion rule or calculus derivation
changed, so this feature does not require Lean re-certification.

## Rust API

```rust
use kobayashi_marust::incremental::IncrementalClassifier;

let mut reasoner = IncrementalClassifier::new(initial_clauses)?;
let addition = reasoner.add_clauses(new_clauses)?;
let added_ids = addition.added_clause_ids;

let replacement = reasoner.apply_change(&added_ids, replacement_clauses)?;
let entailed = reasoner.is_subsumed_by("urn:example:A", "urn:example:B");
let classification = reasoner.result();
# Ok::<(), Box<dyn std::error::Error>>(())
```

`IncrementalElClassifier` remains available as the lower-level,
addition-only EL++ API. Its existing method and error contracts are unchanged.

## JSONL session

`km incremental` keeps one session on standard input and standard output. Send
one compact JSON object per line:

```json
{"op":"init","clauses":[...]}
{"op":"add","clauses":[...]}
{"op":"remove","clause_ids":[2,3]}
{"op":"change","remove_clause_ids":[4],"add_clauses":[...]}
{"op":"is_subsumed_by","sub":"urn:example:A","sup":"urn:example:B"}
{"op":"classify"}
{"op":"stats"}
```

`init` starts or replaces the session at revision 0 and returns every assigned
clause id. `add`, `remove`, and `change` return an `IncrementalChange`. A failed
command emits an error record and leaves the preceding revision active.
`classify` returns the exact current result. `is_subsumed_by` returns `null`
when the subject is absent from the current concept signature, which
distinguishes an unknown name from a known, non-entailed subsumption.

The `backend` field is `el` or `cb`. The `strategy` field is `el_delta`,
`exact_rebuild`, or `no_op`. Applications can therefore measure when a session
benefits from retained EL state without inferring reuse from latency.

## Current performance boundary

Addition-only EL++ transactions reuse the closure and report exact retained and
new subsumption and edge counts. CB additions, all removals, and all mixed
replacement transactions currently have batch CB or batch EL cost. The session
still preserves parsed normalised clauses, stable identity, atomicity, and an
already materialised answer between updates, but it does not claim faster CB
saturation.

A targeted single-thread IBEX microbenchmark gives a scale check for the EL
path, not an ORE or corpus claim. The initial snapshot contained 10,000
independent `A_i ⊑ B_i` clauses and the transaction added `B_0 ⊑ C`. Across
five release-build repetitions, the median incremental transaction took
14.8 ms and reported 50,000 reused subsumption facts plus four new facts. A
fresh `km elc` process over the 10,001-clause union took 72.6 ms median, a
4.90× end-to-end ratio. The fresh measurement includes process startup, input
parsing, and result serialisation, so it does not isolate saturation speed.
IBEX job `49338646` records the measurements.

Reproduce the same synthetic shape after a release build with:

```sh
cd engine
python3 prof/incremental_microbench.py target/release/km 10000 5
```

Dependency and provenance sets are the next prerequisite for safe CB deletion
and finer-grained CB insertion. Any such optimisation must continue to compare
every updated snapshot against fresh batch classification and must fall back to
an exact rebuild whenever its invalidation proof is insufficient.
