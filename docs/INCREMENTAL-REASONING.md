# Incremental reasoning

KM provides an initial, sound addition-only incremental classifier for the
EL++ fast path. It retains the completed subsumption relation and role graph
between ordinary transactions instead of starting classification from an empty
state.

## Supported semantics

`IncrementalElClassifier` accepts the same normalised DL-clause values as
`km elc`. The initial snapshot and every accepted transaction must map entirely
to KM's EL++ normal forms NF1 through NF7, including role inclusions, role
chains, reflexive roles, and paired existential clauses. Each transaction adds
axioms monotonically.

KM does not expose axiom removal in this API. Removing an axiom can invalidate
arbitrarily many derived facts and requires dependency tracking that the EL++
store does not yet carry. A caller that needs removal must construct a new
classifier from the revised ontology snapshot. KM also rejects non-EL clauses,
including disjunction and equality, without changing the live session.
Certificate-assisted near-EL classification is intentionally excluded because
a later addition can invalidate a certificate that passed for an earlier
snapshot.

The clause frontend must keep generated symbol names stable. Do not normalise
each source-level addition in isolation. Either submit clauses produced by a
stable OWLAPI integration or re-normalise the full source union and translate
the genuinely new normalised clauses.

## Why reuse is correct

OWL entailment is monotone under axiom addition, so every fact in the old EL++
fixpoint remains entailed after an accepted update. KM rebuilds the compact
normal-form indexes for the enlarged clause union, retains the old closure,
clears only the derived NF4 propagation index, and replays all retained
subsumptions and edges once. New rule matches enter the ordinary completion
worklist. Saturation continues until the worklist is empty.

There is one normalisation corner in which the compact rule set is not
monotone. A Skolem role half initially maps to `A ⊑ ∃R.⊤`; a later filler
half changes it to `A ⊑ ∃R.B`. KM compares the old and new direct normal-form
sets. If an old form disappears, it safely completes that transaction from
Init instead of retaining the old canonical top edge. The update receipt marks
this with `reused_fixpoint: false`.

This reaches the same least fixpoint as a fresh EL++ classification of the
union: the retained facts are a subset of the new closure, every new rule sees
every retained premise during replay, and the existing monotone completion
loop recursively processes every new conclusion. No completion rule or
calculus derivation changed, so this feature does not require Lean
re-certification.

## Rust API

```rust
use kobayashi_marust::incremental::IncrementalElClassifier;

let mut reasoner = IncrementalElClassifier::new(initial_clauses)?;
reasoner.add_clauses(new_clauses)?;
let entailed = reasoner.is_subsumed_by("urn:example:A", "urn:example:B");
let classification = reasoner.result();
# Ok::<(), Box<dyn std::error::Error>>(())
```

An addition is atomic. On error, the revision, input clause union, and completed
state remain unchanged. `IncrementalUpdate` reports whether the prior fixpoint
was reused, plus retained and newly derived subsumption and edge counts.

## JSONL session

`km incremental` keeps one session on standard input and standard output. Send
one compact JSON object per line:

```json
{"op":"init","clauses":[...]}
{"op":"add","clauses":[...]}
{"op":"is_subsumed_by","sub":"urn:example:A","sup":"urn:example:B"}
{"op":"classify"}
{"op":"stats"}
```

`init` starts or replaces the session. A failed `add` emits an error record and
leaves the preceding revision active. `is_subsumed_by` returns `null` when the
subject is absent from the current concept signature, which distinguishes an
unknown name from a known, non-entailed subsumption.

## Next steps

The next useful layers are stable source-axiom identifiers in the frontend,
dependency/provenance sets for correct deletion, and a general-CB incremental
store. The current API draws a strict boundary around the fragment for which KM
can already prove update equivalence to fresh completion. It also retains both
the normalised clause union and the completed state, so large-session memory and
transaction latency still need corpus-scale measurement before this becomes a
default route.
