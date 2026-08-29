# Incremental reasoning

KM provides an exact stateful classifier over its EL++ fast path, the
normalised clause fragment accepted completely by the consequence-based (CB)
worker, and an explicitly selected direct-clause hypertableau (HT) fragment.
The general API supports additions, removals, and atomic replacements. It never
returns a stale classification or the partial result of a declined worker run.

## Exactness contract

`IncrementalClassifier` accepts the same normalised `JClause` representation
as `km elc` and `km engine`. It chooses a backend for every committed snapshot:

- A pure EL++ snapshot uses the incremental EL completion store. Addition-only
  transactions retain its completed subsumption relation and role graph.
  Removals and replacements retain every dependency component disconnected
  from the changed clauses and re-complete only affected components.
- Every snapshot outside pure EL++ uses the CB engine. Ordering-stable monotone
  additions retain its completed context graph and resume saturation. This
  includes disjunction, roles, equality and supported cardinality forms, plus
  nominal clauses when `KM_NOMINALS=1`.
- A caller can explicitly select `IncrementalBackend::Ht`, or set
  `"backend":"ht"` on a JSONL `init`. This direct HT arm admits only clause
  state carried completely by `JClause`. It caches global, class
  satisfiability, and pair-countermodel probes.
- CB removals and replacements rebuild only dependency components reached from
  changed concepts, roles, functions, individuals, or auxiliary constants.
  Taxonomy rows in disconnected components remain live. A change spanning the
  whole dependency graph, a symbol-free clause, or an inconsistent prior or
  affected component uses an exact rebuild. A removal may also migrate from CB
  back to EL when the remaining clause set is pure EL++.
- HT removals and replacements use dependency-directed probe invalidation.
  Monotonic verdicts and probes in disconnected signature components remain
  reusable; every other probe runs fresh before commit.

The retained CB path deep-forks the completed engine, extends its ontology
indexes, replays every active worked-off premise through Hyper, then sends all
new conclusions through the ordinary equality, Factor, Join, Succ, Pred, and
message-fixpoint paths. It commits the fork only after a complete fixpoint.
`IncrementalChange` reports this as `cb_delta`, with retained subsumption and
context-edge counts. A failed fork leaves the preceding revision unchanged.

Some insertions deliberately cross a proof boundary and report
`exact_rebuild`:

- A new body occurrence changes a Su/Pr trigger bit for an existing symbol.
  Trigger membership participates in literal ordering, so the retained arena's
  cached maximal-head masks no longer describe that ordering.
- A new internal-definer disjunction changes the automatic
  `KM_SEQ_ORDER` route, unless an explicit environment override already fixes
  the route.
- A new unconditional equality between named individuals changes the
  deterministic equality quotient applied before fresh context construction.
- A new fact about a named individual would need the historical per-context
  individual-mention set used by demand seeding; the current retained graph did
  not record that history before the fact existed.
- A new direct `C -> bottom` clause changes the static `nothing` signature used
  while fresh maximal-head masks are built.
- A later input individual would reuse an id range already occupied by a fresh
  additional nominal.
- `KM_SPLIT`, `KM_ROOT_ORDERED`, or `KM_QUERIES` selects a one-shot route whose
  state is not represented by one reusable default context graph.
- A CB removal or replacement reaches every component, or cannot establish a
  symbol dependency boundary. KM does not retract individual context clauses
  inside an affected component; it classifies that component afresh and splices
  it with retained disconnected rows.

These cases remain supported exactly. They construct and validate a fresh
candidate and expose that choice in the receipt instead of claiming reuse.

The direct HT backend has a narrower fail-closed input gate because the
incremental transport currently carries clauses, not the typed side state used
by production OWL routing. It rejects ground individuals and auxiliary
constants, inverse and builtin universal roles, datatype concepts, role chains,
transitivity, nominals/ABox state, route fences, dropped clauses, and
side-cardinality descriptors. Ordinary disjunctive clauses, simple roles,
Skolem existentials, universals represented directly in clauses, and direct
equality forms remain eligible. A rejected initial snapshot or update returns
`RequestedBackendUnsupported` without changing a live revision.

The CB worker can soundly drop an unsupported clause and can stop at a resource
backstop with a sound but incomplete result. Those outcomes are not valid
incremental snapshots. The general API rejects them as `UnsupportedClauses` or
`IncompleteFixpoint`, respectively, and leaves the preceding revision live.
Every accepted result consequently has `dropped == 0` and an empty
`unresolved` list.

This contract covers the lower-level direct normalised-clause API. The
source-level transport described next owns the complete ontology and never
silently omits an orchestration side channel.

## Complete-source session and OWLAPI lifecycle

`km incremental-source` accepts one complete flattened OWL Functional Syntax
document per transaction. It reruns the full frontend and automatic router,
computes a duplicate-preserving normalized-clause delta, and commits the new
classification atomically. Its JSONL operations are:

```json
{"op":"init","functional_syntax":"Ontology(...)"}
{"op":"replace","functional_syntax":"Ontology(...)"}
{"op":"classify"}
{"op":"stats"}
```

For ELC and clause-complete CB routes without typed ABox, cardinality, or rule
state, the source session retains `IncrementalClassifier` and reports an
`el_delta` or `cb_delta` when that adapter accepts the change. The `ht_rules`
route has a typed adapter: while the TBox, public signature, and routing side
channels remain fixed, it retains the completed TBox taxonomy and updates only
the DL-safe-rule/ABox consistency problem. Monotonic consistency verdicts are
reused directly; other rule/ABox changes rerun the smaller typed consistency
probe without rebuilding the taxonomy. Its receipt reports normalized-clause
and rule deltas and uses `ht_delta`.

The exact `nominals` and `certified_nominals` CB fallbacks also retain this
state when the frontend proves the nominal payload complete and no RBox,
cardinality, or rule side channel remains. Under `KM_NOMINALS=1`, the frontend
has emitted the ground ABox and singleton-defining clauses consumed by the
batch CB worker, so the retained engine resumes the same clause fixpoint.
Unsupported nominal metadata fails this gate closed. Ordering-stable additions
report `cb_delta`. Removals and replacements retain disconnected taxonomy
components and rebuild only the affected component; changes without such a
component boundary rebuild exactly.

The automatic positive-EL ABox route also has a typed adapter. It translates
named individuals into the same fresh EL root concepts used by batch
classification and retains that complete materialization. Additions replay the
existing completion graph. Removals and replacements preserve dependency
components disconnected from the changed translated clauses and re-complete
the affected region. The public TBox taxonomy and the ABox consistency verdict
come from this one exact fixpoint, and accepted reuse reports `el_delta`.
Identity contradictions and changes outside the positive-EL source certificate
fail closed to exact automatic classification.

The ordinary HT, quasi-order, bridge, and first-class cardinality routes retain
typed probe state rather than projecting their inputs down to clauses. The
cardinality adapter carries first-class minimum/maximum definitions, RBox
metadata, and complete native individuals through every transaction. It admits
inverse roles only after the same normalized number-role separation certificate
as batch classification, and repeats the complete-ABox, role-automata,
datatype, dropped-clause, and route-fence gates before committing. Changes to
typed side state invalidate the dependent probes; disconnected class probes
remain reusable. Unsupported negative-role ABox state and a failed certificate
take the visible exact-classification fallback instead of publishing a partial
HT answer.

The proxy-card ABox route retains the same cardinality TBox probes while
recomputing its small concrete-ABox certificate for each source revision. The
certificate closes asserted positive role edges under admitted Horn role rules
and chains, checks that every resulting public type already follows from the
exact TBox taxonomy, rejects unsatisfiable asserted classes, and removes its
internal extra queries before publication. A rejected certificate leaves the
previous revision live and proceeds through exact automatic classification.

The nominal/number-restriction ABox route retains its typed HT probes and
completed satisfiable models. Every revision reconstructs the same nominal
bridges, cardinality definitions, RBox, native individual assertions, and
supported inverse-functional equality clause used by batch classification.
Negative object-property assertions become guarded clash clauses instead of
being dropped from the incremental transport. A retained SAT model is accepted
only after replay reaches a complete clash-free model and the no-blocking
nominal-introduction certificate still finds no number-role edge to a
non-successor. If either preparation or this post-replay check declines, KM
runs the exact automatic fallback and does not claim a meaningful update.

Typed automatic families whose dedicated adapter declines take a visible
`exact_rebuild` safety fallback. The receipt sets
`meaningful_incremental_update=false` for that fallback. This remains
transitional: v1.3 is not complete until every automatic typed route has a
retained-state adapter and demonstrates a meaningful update.

The rules adapter fails closed to an exact rebuild when terminology, names,
IRI ownership, RBox state, cardinality descriptors, definers, or normalized
source TBox axioms change. A session initialized in an inconsistent state has
no published taxonomy to retain, so a later consistency-restoring removal also
rebuilds unless the session previously retained a consistent taxonomy.

The Protégé reasoner keeps one `incremental-source` subprocess for its OWLAPI
lifetime. `BUFFERING` changes remain invisible until `flush()`;
`NON_BUFFERING` changes commit when OWLAPI delivers them. A native failure
leaves the preceding Java hierarchy intact, and `interrupt()` forcibly stops
the active native request. The Java bridge serializes the complete imports
closure in memory, so each native transaction sees one source snapshot rather
than a sequence of independently normalized axioms.

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

## Why retained CB insertion is correct

OWL entailment and the CB calculus are monotone under clause addition. Every
old context clause therefore remains entailed by the enlarged ontology. The
new ontology clauses are indexed before every active old maximal-head premise
is replayed through Hyper. Hyper resolvents enter the same todo queues used by
a fresh run, so local equality, Factor, Join, Succ, Pred, and recursive
inter-context messages process every new consequence to quiescence. New facts
are seeded into every existing context, new named concepts receive ordinary
query roots, and shared TBox closures are invalidated and recomputed before
they seed a future context.

The preflight rejects changes that would invalidate an old ordering or term-id
cache. Within the accepted boundary, retained clauses form a subset of the new
fixpoint, every new rule match is enumerated, and saturation is monotone and
confluent. The resumed and fresh engines consequently reach the same semantic
fixpoint. This changes scheduling and state ownership, not a calculus rule, so
it does not require Lean re-certification.

The exact-rebuild fallback invokes the existing batch `Reasoner` on the
complete candidate clause union. Both paths publish only after saturation
reaches a fixpoint and only when no clause was dropped.

## Why HT reuse is correct

HT classification consists of one global consistency probe, one
satisfiability probe per named class, and confirmation probes of
`A ∧ ¬B`. The incremental adapter retains the Boolean verdict and, for a
satisfiable global or per-class probe, an opaque completed graph. Pair probes
retain their verdict but not another full graph, avoiding quadratic graph
retention. The adapter applies only the following reuse laws:

- Under addition, an old UNSAT probe stays UNSAT.
- Under removal, an old SAT model remains a model.
- A probe in a signature component disconnected from every changed clause has
  the same verdict.
- A replacement gets no monotonic shortcut; affected probes run fresh.

The dependency graph connects every concept, role, and Skolem-function symbol
that co-occurs in one clause, then closes through both the old and candidate
clause sets. A changed empty-body or top-body clause marks every query affected.
This makes deletion and replacement conservative: an imprecise component
merely causes extra fresh probes.

For monotone additions, the adapter can do more than reuse a Boolean verdict.
If the new concept table, role table, and compiled clause vector retain the old
ones as exact prefixes, it clones the old clash-free graph, erases historical
branch dependencies and worklists, and replays every retained node, concept,
and role edge through the new trigger indexes. A completed replay is a new SAT
witness. A replay clash, restart, unsupported boundary, or incompatible layout
proves nothing: the adapter discards that attempt and runs the ordinary fresh
exhaustive HT probe. It never converts a failed model extension into UNSAT.

The complete candidate backend and taxonomy are built before the session
mutates its clause store, revision, or id allocator. If any required fresh
probe defers, the entire transaction fails and the prior revision remains
usable. This changes scheduling and evidence reuse, not an HT inference rule,
so it does not require Lean re-certification.

## Rust API

```rust
use kobayashi_marust::incremental::{IncrementalBackend, IncrementalClassifier};

let mut reasoner = IncrementalClassifier::new(initial_clauses)?;
let addition = reasoner.add_clauses(new_clauses)?;
let added_ids = addition.added_clause_ids;

let replacement = reasoner.apply_change(&added_ids, replacement_clauses)?;
let entailed = reasoner.is_subsumed_by("urn:example:A", "urn:example:B");
let classification = reasoner.result();

let mut ht_reasoner = IncrementalClassifier::new_with_backend(
    direct_ht_clauses,
    Some(IncrementalBackend::Ht),
)?;
let ht_change = ht_reasoner.apply_change(&obsolete_ids, replacement_clauses)?;
# Ok::<(), Box<dyn std::error::Error>>(())
```

`IncrementalElClassifier` remains available as the lower-level EL++ API.
`add_clauses` performs monotone replay, while `replace_clauses` accepts a
complete candidate plus the changed clauses and performs dependency-component
retraction. Its error contract remains fail-closed.
`classify_ht_fresh` is the direct HT differential oracle.

## JSONL session

`km incremental` keeps one session on standard input and standard output. Send
one compact JSON object per line:

```json
{"op":"init","clauses":[...]}
{"op":"init","backend":"ht","clauses":[...]}
{"op":"add","clauses":[...]}
{"op":"remove","clause_ids":[2,3]}
{"op":"change","remove_clause_ids":[4],"add_clauses":[...]}
{"op":"is_subsumed_by","sub":"urn:example:A","sup":"urn:example:B"}
{"op":"classify"}
{"op":"stats"}
```

`init` starts or replaces the session at revision 0 and returns every assigned
clause id. Omit `backend` for EL-first/CB-fallback routing; use `ht` to require
the direct hypertableau fragment. `add`, `remove`, and `change` return an
`IncrementalChange`. A failed command emits an error record and leaves the
preceding revision active.
`classify` returns the exact current result. `is_subsumed_by` returns `null`
when the subject is absent from the current concept signature, which
distinguishes an unknown name from a known, non-entailed subsumption.

The `backend` field is `el`, `cb`, or `ht`. The `strategy` field is
`el_delta`, `cb_delta`, `ht_delta`, `exact_rebuild`, or `no_op`. HT receipts
report reused subsumption pairs and completion-graph edges; `reused_fixpoint`
is true only when at least one SAT graph completed replay. Applications can
therefore measure retained-state use without inferring it from latency.

## Current performance boundary

EL++ additions reuse the completion closure, while component-local removals
retain completed labels and edges outside the changed dependency component.
Ordering-stable CB additions reuse the completed context graph and report
retained answer and context-edge counts. Component-local CB removals and mixed
replacements retain disconnected taxonomy rows while rebuilding the affected
component. The resulting CB snapshot remains exact, but no longer owns a full
retained context graph, so a later insertion may rebuild unless another
component-local retraction applies. Explicit HT sessions retain probe evidence
across all three transaction kinds, and stable-layout additions can replay
completed graphs. The CB insertion and HT implementations currently deep-clone
retained state to provide failure atomicity; this trades memory and copy time
for a simple, auditable commit boundary. Dependency-aware copy-on-write remains
future work. Changes whose dependency component spans the complete ontology
deliberately report an exact rebuild.

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

A separate retained-CB scale check used 500 independent two-edge class chains
plus one named disjunction (1,001 initial clauses), then inserted one
ordering-stable `B_0 -> Delta` clause. Across five single-thread release runs,
the median `cb_delta` transaction took 3.14 ms and reported 1,500 retained
subsumption pairs plus two new pairs. A fresh `km engine` process over the
1,002-clause union took 25.67 ms median, an 8.18x end-to-end ratio. As above,
the fresh time includes process startup, input parsing, and serialization, and
this synthetic measurement is not an ORE-wide performance claim. IBEX job
`49340574` records the measurement. The complete retained-CB revision passed
the full release suite in IBEX job `49340558` (1,620 passed, 8 ignored, 0
failed).

Reproduce that shape with:

```sh
cd engine
python3 prof/incremental_cb_microbench.py target/release/km 500 5
```

Dependency and provenance sets are the next prerequisite for safe CB deletion
and a cheaper failure-atomic fork. Every retained revision is differentially
tested against a fresh `km engine` process across disjunction, role propagation,
equality/cardinality, and nominal cases. Further optimisations must preserve
that oracle and fall back to an exact rebuild whenever their invalidation proof
is insufficient.

The HT regression suite independently covers monotone model replay,
dependency-local deletion and replacement, a replay clash that must fall back
to a fresh probe, existential completion-edge reuse, global
inconsistent-to-consistent deletion, JSONL selection, and rollback after an
unsupported update. Every committed revision is compared with both a fresh HT
classification and a fresh CB classification, modulo the standard convention
that `A -> owl:Nothing` replaces redundant superclass pairs for an
unsatisfiable class.
