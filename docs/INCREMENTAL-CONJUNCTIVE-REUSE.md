# Experimental conjunctive incremental reuse

`KM_INCREMENTAL_CONJUNCTIVE=1` enables the experimental dependency analysis for
source-level bridge sessions. It is off by default. This is not a release
performance or certification claim.

The source guard admits positive Horn TBoxes with role inclusions, chains and
inverses, but excludes individuals, rules, datatypes, cardinalities,
functionality, disjunction, complement expressions, universal restrictions and
self restrictions. The bridge also rejects the optimization when its typed
side fingerprint, IRI mapping or public query signature changes, or the prior ontology is
inconsistent. Role-bearing deltas use the established fallback.

For each public query, the analysis seeds that query's concept and all top
concepts. Typed role domains and ranges are global seeds. Every role and
equality premise is treated as available; term identities and locations are
forgotten. A clause activates its head concepts only when all its concept
premises are reachable. The analysis computes this closure over the union of
both normalized revisions. A changed clause invalidates a query only when
all of that clause's concept premises are reachable. Empty concept bodies
invalidate every query. The bounded bit matrix falls back above 64 MiB, and
inputs with more than 500,000 combined clauses also fall back.

## Preservation argument and remaining proof work

In the admitted Horn fragment, a positive concept fact can arise only from
the query seed, a global premise, or a rule application. Induction on such
applications places every generated concept predicate in the abstraction:
forgetting role premises and term locations only enlarges the reachable set.
The union of the old and new rules provides this bound for either revision.
Thus a changed clause with an unreachable concept premise cannot participate
in the query's derivation in either revision. Removing or adding those inactive
clauses preserves its Horn closure and any disjointness clash. The same
argument covers cyclic or unbounded derivations through their finite prefixes.

This argument depends on the source guard and coverage of typed initial
premises. The implementation has exhaustive small propositional-Horn tests
for unchanged-query satisfiability and entailments, plus a real-source
comparison. These tests do not replace a Lean publication-boundary audit or
full update-corpus validation. Those remain required before promotion.

## Partial-result merge contract

The bridge may emit incidental source-closure rows for subjects outside the
requested subset. Such a row need not contain that subject's complete
taxonomy. Only requested affected subjects may replace retained rows.
Overwriting unrelated rows lost 9,227 pairs in the first ORE 9944 diagnostic;
restricting replacement restored exact agreement with the full-rebuild result.

For ORE 9944's one-axiom removal and restoration, the prototype retains 8,004
of 8,008 public query rows and rebuilds four. Its larger edit still falls back:
definer renumbering changes about 27,000 normalized clauses and changes the
typed fingerprint. Timing comparisons against fresh reasoning, repeated cluster
measurements, broader fragment coverage, and the certification boundary remain
unfinished. No case is removed from the release acceptance workload.

## Stable source-expression diagnostic

A separate diagnostic now lowers source-level `Name`, `And`, and `Exists`
expressions into stable abstract predicates. Conjunction requires every child;
existential expressions and their fillers activate each other in an abstraction
that treats every role as available. Source subclass/equivalence/disjointness
axioms become Horn rules. The union of old and new source theories determines
which changed axioms can activate for a public query. This does not modify
normalization or authorize retained production rows.

For ORE 9944, the large edit removes 32 source axioms. The abstraction marks
2,180 queries as affected and leaves 5,828 potentially reusable. Fresh complete
classifications change 52 query rows, all inside the affected set. For the
single-axiom edit it marks four queries; no public taxonomy row changes.
The raw domain/range IDs change, but their name-resolved content and the other
observed typed side fields remain identical. These observations motivate
stable source dependencies and semantic side-state comparison. Before using
this in production, the source metadata must account for every premise,
all `TInput` fields need explicit treatment, and proof and broader measurements
remain required. See `source-activation-*.json` and
`probe_source_activation.py` in the v1.5 performance evidence directory.

## Abstract Lean proof

`lean/ContextCalculus/IncrementalHornActivation.lean` proves that a bound
closed under both Horn rule sets contains every derivable fact, and that an
inactive symmetric difference preserves every derivation and positive Horn
entailment. The derivable facts form the least model. A clash may be represented
as a distinguished atom. The routing gate builds and audits all five theorems;
the gate passes without `sorryAx`. This does not yet prove the OWL lowering,
typed-state completeness or Rust bit-matrix correspondence. It is a component
of the required certification boundary, not certification of the optimization.

## Source-model locality proof

`lean/ContextCalculus/IncrementalSourceLocality.lean` now proves the model
argument for atomic classes, top, bottom, conjunction, and existential
restrictions. Restrict a model by interpreting inactive atomic classes as
empty while retaining every role relation. Structural activation establishes
that active expressions keep their interpretation and inactive expressions
become empty. Inactive added or removed inclusions then preserve every named
subsumption and query satisfiability for an active query. Arbitrary fixed
role-only constraints remain valid because roles do not change.

The proof has four axiom-audited theorems and no `sorryAx`. Class-valued role
domains/ranges, ABoxes, and other typed side constraints are not silently
covered by its role-only premise. Complete source coverage, the exact lowering
of n-ary conjunction/equivalence/disjointness, and the activation algorithm's
closed-set certificate remain integration obligations.

The Rust `source_affected` diagnostic uses structural source-expression keys
across both snapshots, so generated definer names and numeric concept IDs do
not participate in change detection. It reuses the bounded bit-matrix analysis
and is compiled only for tests. It does not authorize production reuse or
alter the current fallback. Finite relational-model tests exercise existential
restrictions, conjunction, equivalence, disjointness, and global top premises.
