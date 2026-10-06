# Experimental conjunctive incremental reuse

`KM_INCREMENTAL_CONJUNCTIVE=1` enables the experimental dependency analysis for
source-level bridge sessions. It is off by default. This is not a release
performance or certification claim.

`KM_INCREMENTAL_SOURCE_LOCALITY=1` enables the newer source-expression path
described below. It is also off by default and is disabled when HT runtime
certification is requested. Its first measured updates retain more work but
are still slower than fresh reasoning; it is not ready for promotion.

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

With normalized-clause analysis, ORE 9944's one-axiom removal and restoration retain 8,004
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

The source proof also treats unchanged background constraints and proves
domain/range preservation when their named classes are globally active.
ABoxes and other typed side constraints are not silently covered by these
premises. Complete source coverage, the exact lowering
of n-ary conjunction/equivalence/disjointness, and the activation algorithm's
closed-set certificate remain integration obligations.

The Rust `source_affected` analysis uses structural source-expression keys
across both snapshots, so generated definer names and numeric concept IDs do
not participate in change detection. It reuses the bounded bit-matrix analysis
and is connected only to the explicit source-locality option. Finite relational-model tests exercise existential
restrictions, conjunction, equivalence, disjointness, and global top premises.

## Typed side-state audit

The guarded `positive_source_side_fingerprint` exhaustively destructures
`TInput`. A future field therefore requires an explicit decision. It compares
supported side constraints through unique concept and role names, allowing
numeric reindexing and private definer churn without changing public meaning.

| Fields | Diagnostic treatment |
|---|---|
| Rule metadata, nominals, ABox payloads, cardinality definitions, dropped/fenced input | Decline reuse admission when present |
| Queries | Compare public named classes; reject duplicate names or invalid indices |
| Roles, chains, transitivity | Resolve indices to unique names; preserve chain operand order |
| Domains and ranges | Resolve role/class names; require public named class endpoints |
| Inverse and cardinality-projection flags | Retain exact values |
| Clauses, source axioms, definers, projection certificates | Outside this side key; require independent source coverage and locality validation |

On ORE 9944's larger edit, the raw fingerprint differs but the name-resolved
key is identical. Mutation tests distinguish changed domains, reversed chain
operands and inverse flags, and reject unsupported payloads or invalid indices.
This is necessary but insufficient for reuse. The caller must also require an
unchanged source RBox: role hierarchy and inverse constraints can live in
clauses rather than these side vectors.

## Source coverage and first retained execution

The source-locality path reparses each admitted source through a strict axiom
inventory and compares every normalized TBox axiom with the retained metadata.
It currently requires expanded entity IRIs and sources at most 8 MiB. Unknown
constraints, imports, keys, rules, ABoxes and unsupported class constructors
decline this path. Both revisions must retain the same IRI map and complete
RBox, and the typed source arrays must match their frontend counterparts.
The typed-side key independently checks the supported unchanged constraints.
An uncertain check uses the existing rebuild path.

The first actual five-revision ORE 9944 session exactly matches fresh results.
It retains 8,004 rows on each small edit and 5,828 on each larger edit, but
updates take 1.995–2.087 seconds while fresh processes take 1.600–1.652 seconds.
These are local diagnostics, not a release benchmark. All four updates fail
the requested speed criterion. See `source-locality-updates-first.json` in the
v1.5 performance evidence directory.

The bridge still rebuilds the entire native environment and computes full
source closure before restricting taxonomy probes. A source-locality module
estimate retains 656/16,569 axioms for the four affected small-edit queries,
and 7,828/16,538 for the 2,180 affected large-edit queries. Rebuilding an exact
module is the next candidate optimization. Source rendering, complete RBox
preservation, projection certification, and fresh-answer validation must
precede its use; no module is currently substituted into classification.

## Rendered module and retained-row merge diagnostic

The bounded Python renderer now tests actual modules on all four ORE 9944
updates. It accepts only declaration-covered, collision-free expanded names,
positive source expressions and a restricted one-axiom-per-line fixture. It
keeps every role axiom and declaration. Before testing a module, it reconstructs
all source TBox axioms from the typed metadata and requires the resulting full
classification to equal the original fresh answer.

Both repetitions of all four module classifications preserve every affected
answer. Replacing only affected subjects in the previous complete result also
reproduces the entire fresh answer, including the two restoration updates.

| Revision | Selected source axioms | Module classification (s) | Full reconstructed control (s) | Python preparation (s) |
|---|---:|---:|---:|---:|
| Single-axiom removal | 656 | 0.251–0.254 | 1.630–2.001 | 0.692 |
| Restoration | 657 | 0.273–0.280 | 1.670–1.674 | 0.684 |
| 32-axiom removal | 7,828 | 0.886–0.890 | 1.645–1.680 | 0.764 |
| Restoration | 7,887 | 0.904–0.926 | 1.606–1.677 | 0.716 |

Row merging adds 0.018–0.024 seconds. These are local diagnostic measurements,
not end-to-end update times. They exclude the original frontend normalization,
affected-query discovery, retained-session protocol and some serialization.
Preparation already consumes most of the large-edit gain. No production route
or default changes. The next implementation must reuse parsed source and
activation state, measure the complete update path, and finish the publication
boundary proofs before promotion. The full receipts and script hashes are in
`results/benchmarks/2026-10-05-v1.5-performance/source-locality-module-render-validation.json`.
