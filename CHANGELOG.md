# Changelog

All notable changes to the kobayashi-marust reasoner. Newest first.

> **How each once-failing ontology was solved — diagnosis, mechanism,
> validation — is documented per-ontology in
> [`docs/SOLVED-ONTOLOGIES.md`](docs/SOLVED-ONTOLOGIES.md).** Keep that file
> updated whenever an ontology flips to solved.

## [unreleased] — CB engine scaling (ORE 2015 coverage push)

### Process-tree memory watchdog: always publish a terminal row (2026-07-17)

The production sweep enforced the 20 GB reasoner cap by polling the reasoner
*process group* every 40 ms and killing it on the sample. On the fast-blowup
giants (ore_ont_3524, ore_ont_15703) a giant can allocate several GB between two
samples, so real RSS crossed the 28 GB Slurm hard limit before the poller ever
observed 20 GB. The cgroup OOM-killer then fired, and under Slurm's
`memory.oom.group` it took the whole step, the Python supervisor included, so no
memout row was ever written. The sbatch sanity check then failed under `set -e`
and the array task stayed permanently unfinished on those ontologies.

New `oracle/ore/tree_watchdog.py` replaces the group poller with a watchdog that
enforces the same 20 GB measured cap without giving the reasoner more memory:

- Measurement is over the full process *tree* (descendants by PPID) unioned with
  the process group, so a worker that leaves the group via `setsid` still counts
  toward the cap. `/proc/<pid>/stat` is parsed relative to the final `)` so a
  `comm` holding spaces or parentheses no longer mis-indexes RSS.
- The cgroup's own accounting (`memory.current` on v2, `memory.usage_in_bytes`
  on v1) is read every tick as a race-free backstop, using the reasoner's growth
  since start so a shared cgroup baseline does not false-trip. It stops the run
  as a memout at cap plus a small supervisor headroom, well below the 28 GB hard
  limit, before the kernel OOM-killer can reach the supervisor.
- The supervisor lowers its own `oom_score_adj` and raises the reasoner's, so in
  the non-group cgroup case the kernel prefers the reasoner as victim.
- On a trip the terminal row is checkpointed to a durable, attempt-independent
  path *before* the kill. `production_full_sweep.sbatch` salvages that checkpoint
  (same attempt, or a later array attempt) so a genuine 20 GB blow-up publishes
  its memout row once and is never retried forever. An unsolicited SIGKILL near
  the cap now reads back as a memout, not an error, and the frozen runner always
  prints exactly one terminal JSON row.

Validated by `oracle/ore/test_tree_watchdog.py` (12 synthetic cases: tree-walk
beats the group poller on a setsid escapee, robust stat parsing, cgroup v1/v2
delta accounting, SIGKILL of a SIGTERM-ignoring child, timeout, and an
end-to-end runner run that emits one memout row plus a matching durable
checkpoint). The measured cap and `--mem` allocation are unchanged.

### Absorb the production portfolio's CB fallback clause set (2026-07-17)

`ore_ont_10908` is exact under the isolated `cb_absorb_portfolio16` route
(208.2 s, 1,071 MB, gold-exact 6001/6001 subsumptions; the completed follow-up
array in `results/benchmarks/2026-07-16-routing-complete592`) but times out
under the bootstrap-selected `production_all` route. Both routes run the same
always-on CB fallback (`race_absorbed_plain` inside `race_adaptive_vs_elc`),
so the gap is not the orchestrator — it is the clause set the frontend hands
that fallback.

Root cause: the frontend clausifier's polarity-gated absorption
(`normalise.rs`, `Clausifier::absorb`) reads *only* `KM_ABSORB`. It Horn-ifies
LHS disjunctions and drops the unguarded `⊤ → Q ∨ A` excluded-middle clauses,
shrinking the live-disjunction blow-up at source — this is the mechanism the
2026-06-21 ablation named the "dominant lever" (recovers 6212, 10908, 15491,
16444; 0 unsound, 0 incomplete, 0 regressions). `cb_absorb_portfolio16` sets
`KM_ABSORB=1`. `production_all` set only `KM_TRIGGER_ABSORB=1`, which leaves the
`absorb` flag off, so its CB fallback saturated the un-absorbed excluded-middle
clause set and hit the 240 s wall on exactly the disjunction family the absorbed
route closes. `KM_TRIGGER_ABSORB` alone drives the Konclude bridge, not the CB
clause encoding.

Fix (ontology-independent, no ontology identity): `production_all{,8,1}` now
carry `KM_ABSORB=1` alongside `KM_TRIGGER_ABSORB=1`, so the CB fallback is fed
the identical disjunction-shrunk clause set `cb_absorb_portfolio16` uses. The
two absorptions compose rather than conflict: `source_axioms` (the bridge's
native Konclude terminology) are recorded from the original NNF axioms gated
purely on `KM_TRIGGER_ABSORB` (`normalise.rs:1264-1306`), so polarity absorption
never changes what the bridge sees, and `mark_subclass_polarity` was already
written to keep triggered antecedents from recreating excluded-middle clauses
under `KM_ABSORB`. The card arm reads the `cardinalities` metadata (unaffected
by `KM_ABSORB`), and the CB engine is sound+complete on any equisatisfiable
encoding, so admitting absorption adds no unsound/incomplete risk. Focused
routing tests pin the composition
(`production_bundles_absorb_the_cb_fallback_clause_set`,
`automatic_sriq_route_absorbs_the_cb_fallback`).

Lean re-certification is NOT required. `KM_ABSORB` is a frontend clausification
choice, not CB-calculus logic (AGENTS.md: "the frontend is not calculus logic").
It changes which equisatisfiable clause set the engine receives, not the
saturation rules, ordering, redundancy, or what the engine derives from a given
clause set; the transform is already corpus-validated verdict-preserving. The
IBEX gate is a `production_all` A/B on the disjunction-absorption family versus
the frozen matrix, confirming the recovery and no bridge/card regression.

### Exact OWL top and bottom recognition (2026-07-17)

The functional-syntax frontend now recognizes `owl:Thing` and `owl:Nothing`
only from their standard OWL names and full IRIs. A user class in another
namespace whose local name is `Thing` or `Nothing` remains an ordinary named
class. Parsing, RBox analysis, and profile routing use the same exact test.

### Lower frontend and EL completion peaks (2026-07-17)

The frontend releases the source document before serializing its owned clause
result. Pure-EL completion releases normal-form vectors after their indexed
copies have been built and before saturation. These ownership changes do not
alter clauses, rule indexes, or derivations.

### konclude_ht bridge: stop dropping colon-localname classes from the universe (2026-07-17)

The Konclude completion bridge builds its classification universe (the set of
real named classes eligible as subjects and candidate supers) by excluding
frontend-synthetic markers and builtin vocabulary via
`orchestrate::cb_to_ht::is_internal` (`bridge.rs::bridged_classify`). That
predicate treated ANY name containing a `:` as internal. A real class whose
localname legitimately contains a colon — a URN class IRI such as
`urn:example:Foo` (for which `short` strips no `#`/`/`), or a colon-bearing
fragment such as `#Part:Whole` — was therefore silently excluded from the
universe: it was dropped as a candidate super (`subs.retain`,
`saturation_known_pairs.retain`, the `known_subsumers` filter), so no
subsumption `X ⊑ ThatClass` was ever emitted, and the drop was counted as
neither unsound nor incomplete. That is exactly the kind of silent
approximation the project forbids.

The colon clause is a proxy for builtin vocabulary (`owl:Thing`,
`rdfs:Literal`, `xsd:integer`, …). Konclude never approximates these classes
away, and the frontend's own internal-name predicate
(`frontend::iri::reserved_internal_prefix`) is prefix-based, not colon-based.
`is_internal` now excludes a colon name only when its prefix is a reserved
vocabulary prefix (`owl`/`rdf`/`rdfs`/`xsd`/`xml`) — exactly the builtins the
heuristic intends to catch — via the new `is_reserved_vocabulary_curie` helper.
The `Nothing`/`owl:Nothing` handling (owned by `is_bottom`) is unchanged.

Soundness/completeness: the change is a strict narrowing of the exclusion set,
so it can only ADD real classes back to the universe, never remove one; it
introduces no new subsumption test verdict. Every builtin the old clause caught
uses a reserved prefix, so the ORE corpus (no class has a non-reserved-prefix
colon localname) is byte-identical. The fix touches only the HT-bridge feeder
(`cb_to_ht`), not the production CB engine output path. New unit test
`is_internal_excludes_markers_and_builtins_but_keeps_colon_localname_classes`.
See `docs/BRIDGE-UNIVERSE-COLON-CLASSES.md`.

### Protégé 5.6 plugin refresh (2026-07-16)

The Protégé plugin now targets the Maven-published Protégé 5.6.6 API and OWL
API 4.5.29, uses the pure-Rust `km` executable without the legacy Python/moose
fallback, and reports version 0.2.0. It flattens the loaded imports closure
before classification, maps results using complete IRIs rather than ambiguous
local fragments, captures subprocess diagnostics, and enforces a configurable
timeout. Headless regression tests cover imports and duplicate local names.
The plugin guide now includes complete installation and runtime configuration
instructions for Linux, macOS, and Windows.

### Standard OWL syntax input adapter (2026-07-16)

`km classify`, `km profile`, and `km features` now accept OWL functional
syntax, OWL/XML, RDF/XML, and Turtle. The adapter detects the syntax from file
content and extension, with `--format` and `KM_INPUT_FORMAT` overrides for
ambiguous inputs. OWL/XML and RDF serializations pass through Horned-OWL's
structural ontology model before entering KM's existing functional-syntax
frontend, so every route continues to consume the same normalized clause
contract.

The adapter fails closed when RDF-to-OWL mapping is incomplete and when an
ontology contains unresolved imports. This prevents KM from silently
classifying a partial ontology. Native functional-syntax benchmark inputs keep
their existing direct path. Cross-syntax tests check that a simple subclass
ontology produces equivalent normalized clauses in OWL/XML, RDF/XML, and
Turtle. See `docs/INPUT-FORMATS.md` for the interface and licensing details.
### konclude_ht bridge: accept deterministic subsumers without a pair probe (2026-07-16)

The Konclude completion bridge's non-deterministic subject verification
(`bridge.rs::classify_one`) probed EVERY candidate subsumer with a full
`bridged_unsat(s ⊓ ¬c)` satisfiability test, including candidates that the
completion model already proved to be *deterministic* subsumers. That re-runs an
expensive probe for a subsumption that is already entailed.

Konclude never tests deterministic subsumers. Its satisfiability-message
analyser extracts the root node's branch-independent label concepts
(`branching_tag <= max_deterministic_branch_tag`,
`create_root_class_subsumption_message`) as a `TellClassSubsumption` message and
records them directly through `add_subsuming_concept_item`; only the
possible-subsumption MAP is scheduled for pair tests. The port already delivers
and processes that message (`process_class_subsumption_message`), so on a
non-authoritative subject the item's `subsuming_concept_item_set` holds exactly
those certain subsumers — but the pairwise loop could not see them, because
`candidate_state` reads the possible map, not the subsumer set.

New `SynchronousKPSetClassState::certain_subsumer(subsumed, subsumer)` reads that
subsumer set, and the pairwise loop accepts a certain subsumer directly (records
the pair, skips the probe) before the `candidate_state` / `pseudo_model_refutes`
/ `bridged_unsat` cascade. This mirrors the trust the authoritative read-off
already grants deterministic label positives (same file, the `authoritative`
branch pushes them with no probe). It is recorded like an authoritative
subsumer rather than routed through `interprete_subsumption_result`, so budget
retries recompute idempotently and no classifier propagation state is mutated.

Soundness/completeness: the extraction is branch-tag gated, so `s ⊑ c` holds in
every model of `s` — accepting it is sound, and no possible subsumer is dropped
(those still take the full probe). Default ON with `KM_HT_NO_DET_SUBSUMER=1` as a
disable hatch for a corpus A/B against the probe-every-pair path. Likely to help
the deep-hierarchy `∀ + ⊔` timeout family, where each non-deterministic subject
carries many deterministic supers that were being re-probed. See
[`docs/DETERMINISTIC-SUBSUMER-SHORTCUT.md`](docs/DETERMINISTIC-SUBSUMER-SHORTCUT.md).

Tests: `classifier/mod.rs::certain_subsumer_reads_recorded_deterministic_subsumer_set`
(certain subsumer accepted; not visible to `candidate_state`; directional;
self- and out-of-range pairs fail closed). No Lean re-certification: this is
bridge classification bookkeeping, not CB-calculus logic, and derives no new
subsumption a full probe would not have confirmed.

### Restore the additive production cardinality arm (recovers 7499 / 9540) (2026-07-16)

The 2026-07-15 "fence named HT specialists" change set the production portfolio
(`PRODUCTION_ALL`, `KM_MECHANISM=portfolio`) to `KM_HT_ONLY=certified`, which
`specialist_route_allows` narrowed to the Konclude bridge arm alone. That was
correct for policy-LEAF eligibility (the isolated `ht_card` specialist, where CB
never runs, is incomplete on ore_ont_10702 and must stay out of the learned
tree). But it also silenced the first-class cardinality arm as a CB-guarded
FALLBACK inside the production race, regressing ore_ont_7499 and 9540 back to
240 s timeouts. Those two had been recovered by the pre-fence default
(`KM_HT_CARD` on, job 48067625: 573 gold-MATCH) precisely because the card arm
runs under `race_cb_vs_ht` fallback mode, where CB is authoritative: the arm's
answer is taken ONLY when the certified CB engine times out, and the number
rules are sound, so it can only ever replace a CB timeout.

`specialist_route_allows(Some("certified"), ...)` now admits `card_candidate` in
addition to `bridge_candidate`. This is strictly the additive fallback arm, not
a policy leaf — `sriq_policy_eligible` still excludes `HtCard`, so the routing
tree cannot select the isolated card procedure. SHOQ and QO stay bridge-only
under certified: their incomplete onts (10702 / 15098) could otherwise emit a
wrong taxonomy on a CB timeout. The inverse+nominal onts on which the card route
is incomplete (10702) never become `card_candidate` because `cb_to_ht::convert`
refuses the card transform under inverse (no `card_defs` emitted), so this does
not expose that incompleteness. 15672 needs the SHOQ arm, which is entangled
with 10702's incompleteness, so it is left for a separate SHOQ-scoped change.

`KM_HT_BRIDGE_ONLY` was extended (via the new `bridge_only_worker` gate) so that
a certified worker carrying BOTH a bridge and a card arm no longer forces
bridge-only: a bridge defer now hands off to the card fallback instead of
exiting empty, matching the pre-fence single-worker behaviour. The
`card_candidate` gate is factored into `card_candidate_from` so the exact
production gate is exercised on a reduced cardinality probe. This changes only
procedure eligibility and worker composition, not any CB-calculus derivation, so
it requires no Lean re-certification. Unit tests assert the certified env bundle
keeps the card arm live, the `certified` admittance, the bridge/card hand-off,
and that a synthetic `≥2 R.C` restriction converts to a `card_def` and passes
the gate.

### Restore the validated DL-safe rule consistency precheck (2026-07-16)

The `ht_rules` procedure (named route, matrix row, and the automatic
semantic-fragment gate for rule-bearing input) lost its short-circuit on ORE
2669 and 15516: instead of the validated 0.17 s "inconsistent" verdict, both
drove a full engine run to the 240 s timeout. Root cause: the KPSet checkpoint
(`592462b`) threaded `Some(&input.rbox)` into `rules_consistency`'s
`cb_to_ht::convert` call while updating the signature. The rbox side channel
carries the source inverse-role records, and those arm the
`nominal+inverse(SHOI/SHOIQ)` classification fence, which cleared the
`__nom__` ABox seeds the consistency check exists to create. The rules
tableau then started with no roots, trivially answered "consistent", and the
rule-detected inconsistency fell through to the long CB path. Both ontologies
declare inverse roles, so the precheck never fired.

Two-part fix, both sound. First, `rules_consistency` passes `rbox = None`
again — the exact validated 2669/15516 configuration; inverse/subrole/
domain/range semantics still reach the tableau through the frontend's bridge
clauses inside the clause set, so a detected clash remains a real clash.
Second, the fence in `cb_to_ht::convert` no longer unseats nominal seeds when
`rules_active`: the fence protects classification consumers (the fast Ht has
no sound nominal+inverse completion), while the rule seeds' only consumer is
the consistency verdict, which short-circuits solely on a clash — every
tableau step is a sound consequence, so a clash is real regardless of the
fragment; a "consistent" verdict merely falls through to normal
classification. Rule-free ontologies are byte-identical (`rules_active`
requires actual rules), so the corpus blast radius is exactly the SWRL onts.

Validated on the workstation: 2669 and 15516 return `consistent=false` in
0.12–0.17 s / ~19 MB again through `--route ht_rules`, `auto`, and `manual`;
the synthetic consistent-rule control falls through and classifies its
taxonomy correctly. New tests: `cb_to_ht` unit tests (rule seeds survive an
inverse rbox and the production verdict detects the clash; the fence still
clears classification nominals without rules), a route-provenance test
(exactly `ht_rules` plus the composed portfolios keep `KM_NO_HT_RULES`
unset), and `engine/tests/rules_route.rs` end-to-end fixtures with inverse
roles (short-circuit only on inconsistency, taxonomy fall-through, automatic
route provenance). The `KM_RULES_CONSISTENCY` worker block is refactored into
`tableau::rules_consistency_verdict` so the tests exercise the production
entry without the env gate.

Rule-bearing ORE 10860 stays an honest decline, now in 0.01 s: it carries 17
`DLSafeRule` axioms and exactly 4 use SWRL built-ins (`BuiltInAtom` time/date
comparisons, with `DataPropertyAtom` operands) outside every supported rule
shape, matching the profile corpus record of 4 unsupported rule axioms. The
frontend's exact rule contract rejects the ontology
(`parsed 13 of 17`) rather than silently dropping rules, per the fail-closed
policy in docs/ROUTING.md; its gold remains unadjudicated
(docs/CONTESTED-GOLD.md: HermiT cannot parse it).

### Restore the proven KPSet bridge stack on the automatic route (2026-07-16)

The routing snapshot made `auto` the classify default whenever `KM_ROUTE` is
unset, with a bootstrap generated tree whose only leaf was `cb_plain16`. Route
normalization removes every routing key before installing the selected bundle,
so the deployed production environment (`KM_TRIGGER_ABSORB=1`, the 30 s /
0-retry bridge probe budgets, the 180 s saturation budget — exactly the
2026-07-13 ORE 3215 closure configuration) was silently erased before the
frontend ran. Without `KM_TRIGGER_ABSORB` at normalisation the frontend emits
no `source_axioms`, the source-TBox bridge candidate gate fails, and
classification degrades to the plain-CB fallback that times out on the
bridge-closed terminologies (541, 12653, 7914, 3215, 9663, 9724). The typed
`ht_bridge` and `production_all` routes themselves reproduce the closure
end-to-end (verified on a 3215-shaped SHI fixture: trigger absorption, the
saturation pre-pass, and both KPSet prepare/verify phases run, output equal to
CB); the break was confined to the default/auto path that the harness uses.

The bootstrap tree now selects `production_all` — the exact corpus-validated
production sweep configuration (574 ok / 508 exact Konclude matches, zero
gold-match regressions) — and `production_all{,8,1}` are policy-eligible for
the SRIQ core: `KM_HT_ONLY=certified` admits only the bridge's
complete-answer-or-defer path, the EL portfolio answers only on a passing
certificate, and the always-running CB engine keeps the CB-preference winner
rule, so the composition has a complete-procedure contract. The isolated
`ht_bridge` measurement row stays policy-ineligible (a defer under
`KM_MECHANISM=ht` has no in-process fallback). Focused tests pin the proven
closure environment to the production and bridge bundles
(`production_bundles_normalize_to_the_proven_3215_closure_environment`),
require the automatic SRIQ route to reach the bridge stack
(`automatic_sriq_routing_reaches_the_proven_bridge_stack`), and cover the
scheduler's immediate harvest of a finished bridge answer under trigger
absorption (`bridge_answers_are_harvested_immediately_under_trigger_absorption`,
a pure-function extraction of the race budget) alongside the existing 50,000
active-class synchronous-bridge thread reservation test.

### Root-context ordered resolution with refutation residue readout (2026-07-16, gated)

Direction A of docs/DISJUNCTION-SPLITTING.md, narrowed to the smallest sound
and complete step and implemented behind `KM_ROOT_ORDERED` (default OFF;
`1` = root contexts, `all` = every context). Same-term concept literals get a
total order (internal definers above named, iri tie-break), which restricts
Hyper to the ordering-maximal disjunct and tames the incomparable-disjunction
product closure that drives the live `∀ + ⊔` timeout family (CB-only members
10702, 15672, 6934, 9540). The known `KM_ORDERED_ALL` incompleteness — an
entailed named unit trapped non-maximal behind an unresolvable maximal
sibling — is repaired by reduction to the order-robust unsat readout: for
every named concept `B` a fresh inert complement guard `B ⊓ __notb__B ⊑ ⊥`
is injected, and every named concept occurring ordering-maximal in a query
root's worked-off heads that is not already a unit is decided by saturating
the `{A(x), NotB(x)}` context in the same engine and reading `⊥`. The
candidate set is provably complete (a refutation must fire the guard against
a NotB-free clause with `B(x)` maximal, which mirrors into `A`'s own
saturation). The nominal-enumeration shortcut is disabled under the ordered
modes (its ground-context unit readout is only validated in the default
regime). Focused synthetic tests cover the trap in both interning orders,
chained trapped supers, exclusive global disjunctions, unsat queries,
disjunction over a successor, refutation-negative candidates, and
subsumption-map equality with the default engine; the full lib suite passes
(1529/0). This CHANGES CALCULUS DERIVATIONS, so it stays gated until the
Lean obligations O1–O3 and a full corpus A/B are discharged — see
docs/ROOT-ORDERED-RESOLUTION.md.

### Separate provably positive ABoxes from TBox classification (2026-07-16)

The procedure matrix found assertion-heavy ORE 10697, 15725, and 15846 where
the exact nominal CB route reached its 190 second central cap. Direct tests of
the same calculus with per-function scheduling at 1, 8, and 16 threads also
timed out at 240 seconds on all three. This rules out a scheduler-only fix. KM
currently builds and saturates the complete ground context inside every query
engine.

Konclude instead separates ABox consistency precomputation from class
classification. Its `CTotallyPrecomputationThread` saturates individuals and an
all-assertion individual, accepts the result only when its direct and indirect
status is completed, non-clashed, and sufficient, and reuses the precomputed
state for classification. Official Konclude diagnostic job 48947466 confirms
this boundary: on 10697 and 15725, precomputation takes 1,211 ms and 540 ms,
while class classification takes only 3 ms and 2 ms. On 15846 the corresponding
times are 16,164 ms and 80 ms.

Profile schema 2 now records bottom-class and bottom-role occurrences and a
fail-closed `positive_abox_tbox_separable` certificate. The certificate accepts
only positive assertions with no negative constraint, number restriction,
nominal, universal role, rule, key, or datatype constraint. A one-element
all-positive interpretation proves consistency. Disjoint-union preservation
for nominal-free SRIQ without the universal role proves that such an ABox
cannot add a TBox subsumption. Certified inputs use the same independently
complete EL/CB decision tree as the TBox core; every other ABox remains on the
exact nominal calculus. This is a source-level proof gate, not empirical
routing. The checker uses an explicit safe-axiom whitelist: imports, unknown
axioms, and every functional-syntax axiom that the frontend could otherwise
skip fail closed.

The post-whitelist optimized `ws` suite passes 1,516 tests with 0 failures and
7 ignored. Default `auto` selects `cb_plain16` for 10697 and 15725. Their
canonical signatures match Konclude with zero differences in 0.9152 seconds at
161.57 MB and 0.7212 seconds at 123.62 MB, respectively. Default-auto
regressions 148, 178, and 11016 stay on the exact nominal gate and remain
gold-exact. Ontology 15846 is intentionally not certified because it contains
nominals, equality and inequality assertions, and disjointness. See
`docs/POSITIVE-ABOX-SEPARATION.md` for the contract and proof.

### Separate source entities from generated concepts (2026-07-16)

The first post-148 matrix audit found one real completeness family after
discarding four canonicalizer false positives. ORE 8864, 12009, and 6817 were
missing only rows whose source class local names begin with `__`, including
`__adipocyte_glucose_uptake`, `__SyndromeDeBuckley`, and
`__hydroxy_proline_MI_0149`. These are explicitly declared OWL classes. KM's
engine historically recognized generated concepts by string prefixes, so it
mistook those legal source classes for auxiliaries, omitted their query
contexts, and returned otherwise sound but incomplete classifications.

Sequoia represents source symbols and generated definers as different typed
symbols. KM now preserves the same distinction at its frontend boundary.
Registry-owned source names beginning with `Q_`, `__`, `_aux`, `aux_`, or
`def_` receive a collision-safe `km_src_` internal spelling. Generated symbols
are constructed after parsing and never pass through that registry. The
existing inverse IRI map restores the exact public IRI in the classification,
including when a real source name already uses the escaped spelling. The
superseded Python frontend mirrors the same encoding so it remains a valid
orchestration oracle.

Production `cb_plain16` on `ws` now matches frozen Konclude gold exactly for
8864 (6,094 pairs), 12009 (10,509), and 6817 (2,431), with no extra or missing
pairs and no unsatisfiability or consistency difference. The 148 nominal
closure and its 178/11016 regressions retain their exact signature hashes. The
release suite reports 1,515 passed, 0 failed, and 7 ignored. Portable Bullseye
binary `c229366fcc9efbfec729f5a7dcc1a5f1ef9b12fe41f433b67282930bf18a92f6`
repeats all six exact comparisons on an IBEX Intel Gold 6248 node in job
48946056. Full 592-ontology, 28-arm matrix job 48946164 uses only this binary
in 50 isolated shards. This changes frontend symbol encoding, not a CB
inference rule or the derived fixpoint, so it requires no Lean
re-certification.

### Exact nominal classification closes ore_ont_148 (2026-07-16)

The production `nominals` route now closes ore_ont_148 in 54.69 seconds at
3,029,400 KB on `ws`. Its canonical signature contains all 21,037 Konclude
pairs, zero extra and zero missing pairs, no unsatisfiable-class difference,
and the same consistency result. The signature SHA-256 is
`10ef79ea10318d5197169737fc59d7d5771162a452a2e4e1a74a7a0ca880d944`.
The route selects the winning schedule itself; the validation command did not
supply `KM_STATIC_SCHED`.

The exact failure localized to `Cryosphere`. Its universal `hasSubstance.Ice`
restriction meets `Hydrosphere ⊑ hasSubstance value Water`, making the
completed `Water` nominal label query-dependent. One incoming eight-premise
Pred clause had six exact providers per premise and repeatedly materialized
`6^8 = 1,679,616` Cartesian resolvents. A long-lived dynamic worker also mixed
several independently conditioned nominal tasks in one ground context. This
matches Konclude's reason for copying the consistency-test nominal label into
separate influenced saturation tasks.

KM now follows Sequoia's exact maximal-head predicate and term indexes and its
complete active redundancy semantics, represented as exact rarest-head
postings plus explicit todo checks. Pred computes the same strengthening
antichain incrementally after each left-deep join dimension. The equivalence is
algebraic: if partial `P` strengthens `Q`, then `P ∪ R` strengthens
`Q ∪ R` for every remaining completion `R`. The `nominals` route assigns
one fixed query slice per Engine, bounding influenced labels per ground
context; `KM_NOMINAL_DYNAMIC=1` retains the general scheduler for A/B tests.
All three changes preserve the inferred fixpoint and require no Lean
re-certification.

A separate certified optimization recognizes exact finite nominal
enumerations only when both union directions, singleton equalities, and ground
facts are present. It completes the ground sameAs/type fixpoint and intersects
the enumerated labels, matching Konclude's completed nominal-label reuse. This
keeps ore_ont_11016 exact at 265/265 in 0.74 seconds and ore_ont_178 exact at
56/56 in 0.23 seconds; it is inert on ore_ont_148, which has no
`ObjectOneOf`. The release suite reports 1,513 passed, 0 failed, and 7 ignored.
The first portable binary
`bf2875c9c234017a47881dc9b25086c8fdf6c2a673a869fb0ebbb48b142691f8`
passes the IBEX exact-signature smoke in job 48943813: 148 takes 53.7969 seconds
at 2,985.21 MB, 178 takes 0.2687 seconds at 40.94 MB, and 11016 takes 0.5875
seconds at 190.62 MB. Matrix job 48943875 was cancelled after its early audit
exposed the source/generated symbol collision documented above. Corrected
binary `c229366f…` repeats the three exact signatures in IBEX job 48946056;
148 takes 53.3149 seconds at 2,956.60 MB. Closure must not be confused with the
outstanding greater-than-20-percent performance gap to Konclude. See
`docs/SOLVE-148.md`.

### Fence named HT specialists from the incomplete general racer (2026-07-15)

The procedure-matrix audit found that `ht_qo`, `ht_shoq`, `ht_card`, and
`ht_bridge` enabled their named specialist but silently fell through to the
unrestricted general HT racer when the specialist's structural candidate was
absent. General HT is a useful explicit measurement arm, but it is known
incomplete on part of ALC+disjunction and is excluded from policy learning.
Allowing the same algorithm under a policy-eligible specialist name could make
a source-profile tree generalize an empirically exact row into an incomplete
classification.

The audit also rejected empirical success as a completeness certificate. QO
race is incomplete on 15098, 7216, and 7901; the SHOQ and first-class
cardinality routes are incomplete on 10702; and the historical tableau has no
full-fragment completeness contract. Those procedures remain benchmark and
manual options, but they cannot become learned-policy leaves.

Every policy-eligible named bundle now starts with `KM_HT_ONLY=certified`, which
admits only the Konclude completion bridge's complete-answer-or-defer path.
Named specialists narrow execution to
`KM_HT_ONLY=qo|shoq|card|bridge`; `spawn_ht` returns to certified CB when the
requested candidate is absent. A bridge-only worker also exits on bridge defer
instead of falling through to the legacy tableau, even when the input is
otherwise legacy-HT routable. The unrestricted measurement route explicitly
sets `KM_HT_ONLY=general`, and every individual option remains available in
manual mode. Unit tests cover every discriminator and the route bundles.
This changes only safe procedure eligibility, not any inference rule, so it
requires no Lean re-certification.

### Make the historical tableau procedure measurable again (2026-07-15)

The all-procedure audit found that `KM_TAB_RACE=1` no longer reached the
legacy label-caching tableau on ordinary non-giant inputs. The later certified
EL portfolio wrapped the entire CB stack, while the tableau is composed only
inside that stack. Explicit tableau selection now suppresses that outer EL
portfolio, and the named `tab_race` bundle supplies `KM_TAB_FEAT=1` and disables
the unrelated outer HT racer. A unit test fixes this precedence boundary.

An isolated 9635 probe then established a second, intentional boundary. The
modern converter rejects the input before spawning a worker because it combines
inverse roles and number restrictions, producing the explicit
`inverse+number(SHIQ)` soundness fence. This supersedes the old 9635 legacy-race
claim; the newer certified cardinality and Konclude-bridge paths own SHIQ. An
opt-in `KM_TAB_DUMP_TIN` plus `KM_TAB_TRACE` diagnostic now records the exact
pre-fence tableau input and reasons without changing routing. On the current
in-fragment witness 6246, the named route and its explicit option bundle both
return the complete 322-pair gold signature in 30.95–31.07 seconds on IBEX job
48889958. These changes only alter procedure composition and diagnostics, not
any calculus derivation, so they require no Lean re-certification.

### Restore source-TBox bridge routing for complex domains/ranges (2026-07-15)

The new all-procedure routing matrix exposed that `ore_ont_541` timed out in
every triggered-bridge arm even though the Konclude bridge kernel still
classified its exact input immediately. The failure was at the procedure gate.
Exact source-RBox provenance added `complex-domain` and `complex-range` fences
for the legacy clause-reconstructed tableau. `spawn_ht` reused those fences for
the source-terminology bridge and declined to spawn it.

The bridge gate now accepts those two fences only when triggered absorption
carried a nonempty normalized source TBox and source-TBox mode is enabled. In
that case the bridge builds Konclude's native domain/range concepts directly;
without source provenance the same inputs remain fenced. Other fence reasons,
including unsupported RBox constructs, remain rejected. The actual production
race again classifies 541 in 0.25 seconds at 53 MB and 12653 in 0.15 seconds at
18 MB on `ws`. A focused test proves the source-only fence distinction. This
changes orchestration eligibility, not CB-calculus derivations, so it requires
no Lean re-certification.

### Saturation-aware cardinality successors close ore_ont_14817 (2026-07-15)

`ore_ont_14817` now completes through production `km classify` and matches
Konclude exactly: 1,184,692 subsumptions on both sides, zero extra, zero
missing, no unsatisfiable-class difference, and the same consistency result.
The final Rust 1.85 Bullseye binary has SHA-256
`c7c3eefe49ac95a7feaa7c1b70ada2ae65b820097cbe0456b0ab4be82c61ba07`.
IBEX production-sweep job 48853569 task 518 finished in 56 seconds at
3,365,116 KB. An independently traced full run matched in 195.16 seconds at
4,234,340 KB.

The fixed 9724 binary saturated 48,642 of 58,364 active subjects but timed out
on the 9,722-subject completion residue. Exact ports of Konclude's live
satisfiable-expander cache, 80-rule task boundary, cache commits, retired-pool
release, pointer-like label signatures, and KPSet touched-candidate ordering
made the tail measurable. They did not close it. Subject 85031,
`UBERON_0014672`, still produced 72,670 disjunction replacements in 51 seconds
and deferred.

A trusted Konclude trace, built by relinking the native IBEX objects and
recompiling only the instrumented completion object, handled that subject in
125 ms. Konclude saturation-expanded its first six root successors as three
cardinality-created pairs. KM created the corresponding successors 1001
through 1006 without saturation expansion and began its nine expansion events
at successor 1007. Queue and label tracing independently showed that the
subsequent repeated work was real restored-branch exploration, not duplicate
insertion or accidental requeueing.

The source divergence was exact. Konclude's `applyATLEASTRule` creates an
`ATLEAST` dependency and calls the full `createDistinctSuccessorIndividuals`
path. Production Rust instead called the reduced
`ht_create_distinct_successors` helper, bypassing saturation replay and cache
establishment for every `≥ n R.C` successor. Rust already contained the full
constructor in `completion/u35.rs`; `completion/u08.rs::apply_atleast_rule` now
uses it with the complete signed indirect-super-role list, dependency, pending
clash propagation, low-level nominal handling, and final successor queueing.

The repaired subject expands the missing six successors and records only 300
disjunction replacements over its complete 14.66-second run. A permanent
production-path test constructs `≥2 R.C`, gives `C` a completed saturation
label containing an additional `D`, and proves that both distinct successors
receive explicit `C` and saturation-only `D`. The release suite passes 1,480
tests with 0 failed and 7 ignored.

Full 592-ontology IBEX job 48853569 used the same final binary for every task.
It reports 575 completed, 17 timeout, and 515 exact Konclude matches, compared
with 574, 18, and 514 in the 9724 baseline. The only changed ontology is
14817, from timeout to exact. No previously exact ontology or disagreement
count regressed. The complete C++ correspondence and reproduction record are
in `docs/SOLVE-14817.md` and
`results/benchmarks/2026-07-14-14817-closure/`. These changes affect the
Konclude-compatible completion implementation and cache lifecycle, not the CB
calculus or its fixpoint, so they do not require Lean re-certification.

### Konclude intrusive free-list representation closes ore_ont_9724 (2026-07-14)

`ore_ont_9724` now completes through production `km classify` and matches
Konclude exactly: 457,090 canonical non-self subsumptions on both sides, zero
extra, zero missing, and the same consistency and unsatisfiable-class results.
The final Rust 1.85 Bullseye binary has SHA-256
`8071a4d0d7b35476f8c4d65a749e8fef71279e23dedd1ade4aba405f327078f9`.
IBEX production job 48798145 finished in 24.72 seconds at 8,091,788 KB. Its
independent task in full-sweep job 48799766 matched again in 23 seconds at
8,092,216 KB.

The preceding result was sound but partial, with 3,325 missing pairs at the
fixed saturation budget. A 1,200-second exact-input run recovered only one
pair and reached 24,555,236 KB. It never reached completion-side ATMOST
merging, which disproved the plan-start cardinality hypothesis. Instrumented
Konclude with one worker finished in 10.46 seconds, constructed 33,422
saturation items against KM's 33,678 seeds, and performed 6,853,425
concept-add attempts. The close input shape plus single-worker completion
localized the gap to KM's saturation implementation cost.

An initial exact alignment replaced owned implication-trigger suffixes with
non-owning operand cursors, eliminated persistent allocation for Konclude's
stack-local initial descriptor, used pointer-like integer hashing for role ids,
consolidated backward-role bucket mutation, and changed temporary propagation
chains to constant-time LIFO stacks. That candidate reduced peak memory but
still ended with the same 3,325 missing pairs.

Four live worker samples at 30, 90, 160, and 220 seconds then showed the same
stack: `memcpy` under `release_role_saturation_process_linker`, called from
`process_successor_functional_concepts_extensions`. Konclude's
`CProcessingDataBox.cpp:1849-1869` maintains
`mRemRoleSatProcessLinker` as an intrusive free list. Release prepends a linker
to the head, and acquire removes that head, both in constant time and LIFO
order. KM's collapsed `Vec` stored the head at index zero and implemented the
same logical order with `insert(0)` and `remove(0)`, shifting the entire growing
list on every operation.

Collapsed allocation free lists now store their logical head at the Vec tail.
Konclude's prepend/head-pop operations become Rust `push`/`pop`, preserving the
exact reuse order in O(1). Diagnostic getters reverse the internal vector to
retain the C++ head-to-tail view. The same representation is used for adjacent
concept, status-update, and individual-node `mRemaining*` free lists with the
same Konclude constructor pattern. Ordinary live traversed chains keep their
existing layout. The exact normalized input changes from 3,325 missing after
240 seconds to a complete match in 32.15 seconds.

Release validation is 1,475 passed, 0 failed, and 7 ignored. IBEX array job
48799766 attempted all 592 ORE ontologies at 240 seconds and 20 GB each. It
reports 574 completed, 18 timeout, and 514 exact Konclude matches, up from 511.
No prior exact ontology regressed and no disagreement count increased. Exactly
three results changed, all from incomplete to exact: 1016 recovers 2,510
missing pairs, 11623 recovers 3,423, and 9724 recovers 3,325.

The full causal record and reproduction artifacts are in
`docs/SOLVE-7914-9663-9724.md` and
`results/benchmarks/2026-07-14-9724-closure/`. These are fixpoint-preserving
storage, cursor, hashing, and lookup changes inside the Konclude-compatible
hypertableau port. They do not alter the CB calculus or require Lean
re-certification.

### Native RBox links and role-specific saturation successors close ore_ont_9663 (2026-07-14)

`ore_ont_9663` now completes through production `km classify` and matches
Konclude exactly: 725,040 non-self subsumptions on both sides, zero extra, zero
missing, and the same consistency and unsatisfiable-class results. The
promoted Rust 1.85 Bullseye binary has SHA-256
`dbc35ea3f19c5de9ef447ce274edeb69aeacd91867f3e4d51eaf879b6533e825`.
IBEX gate job 48797088 task 0 finished in 52.75 seconds at 3,189,032 KB. The
independent 9663 task in full-sweep job 48797094 matched again in 47 seconds at
3,147,948 KB.

The baseline was sound but incomplete: 685,932 pairs, zero extra, and 39,108
missing. Of those, 39,087 were 13,029 subjects each missing
`BFO_0000004`, `BFO_0000002`, and `BFO_0000001`. The first missing boundary
was the source RBox. Konclude stores object-property domains and ranges
directly on `CRole`, while KM's source-TBox bridge discarded their normalized
clause copies without constructing the native links. `TInput` now carries
explicit `role_domains` and `role_ranges` provenance from the frontend. Source
mode installs exactly those pairs on the role and inverse role, then suppresses
the concept-bearing clausal copies. It does not infer RBox provenance from a
guarded clause shape, because ordinary class-expression clausification can
produce the same shape. This first causal port reduced the miss from 39,108 to
633 pairs.

The residual witness combines `A ⊑ ∃r.B`, `B ⊑ ∃s.C`,
`r∘s ⊑ t`, and `Domain(t,D)`. KM's role-chain automaton was structurally
correct, but saturation reused the ordinary filler item. That node had already
initialized without role `s`, so it never loaded the generated range
propagation that carries `D` back to `A`.

The decisive change ports
`CTotallyPrecomputationThread.cpp:2057-2074` and
`CTotallyOntologyPrecomputationItem.cpp:731-739`. The seed builder now applies
Konclude's `hasRoleRanges` test over signed indirect super roles. When it holds,
KM interns a separate saturation item keyed by `(role, filler, polarity)`, uses
that item during dependency ordering, stores it in the restriction's
existential-successor reference, and initializes both ontology-side and
process-side items with the role. `createSuccessorForConcept` then reads the
same existential-specific item before its ordinary filler fallback. The
ordinary `(filler, polarity)` path remains unchanged for roles without ranges.
An adjacent exact port now also reports valid named concepts on intermediate
saturation substitute nodes; its isolated candidate did not alter 9663.

The final saturation phase answers 385 unsatisfiable and 57,385 satisfiable
subjects directly and sends 422 insufficient subjects to completion, with no
defer. Konclude reported 423 insufficient nodes, which independently confirms
that the repaired boundary is the one exercised by the ontology. Release
validation is 1,474 passed, 0 failed, and 7 ignored.

IBEX array job 48797094 attempted all 592 ORE ontologies and reports 574 ok,
18 timeout, and 511 exact Konclude matches, up from 508 exact matches in the
3215 baseline. No previously exact ontology regressed. Ontologies 8730, 11978,
and 9663 become exact, while 11745 improves from 15,350 extra and 1,213 missing
to one extra and zero missing. The already-open 9724 remains sound but partial:
its fixed-budget result moves from 3,140 to 3,325 missing pairs because the
exact port constructs 7,714 additional role-specific items generated by role
automata. Both variants stop at the 180-second outer-queue cap; instrumented
Konclude completes that work in 9.84 seconds. This records a remaining 9724
performance problem, not a false inference or regression of a solved ontology.

The detailed causal record and reproduction artifacts are in
`docs/SOLVE-7914-9663-9724.md` and
`results/benchmarks/2026-07-14-9663-closure/`. These changes construct the
Konclude-compatible terminology and saturation inputs. They do not change the
CB calculus or its derived clause set, so they do not require Lean
re-certification.

### Konclude KPSet phase barrier closes ore_ont_3215 (2026-07-13)

`ore_ont_3215` now completes through production `km classify` and matches
Konclude exactly: 3,923,171 pairs on both sides, zero extra, zero missing, no
unsatisfiable-class difference, and the same consistency result. Final IBEX
smoke job 48790271 finished in 129 seconds at 5,351,252 KB. Its independent
task in full-sweep job 48790295 matched again in 120 seconds at 5,357,524 KB.

The first exact KM/Konclude divergence was terminology shape. KM treated every
frontend definer as an active class and attached 18,323 implications to common
condition `C047449`; its saturation label grew to approximately 18,000 concepts,
while Konclude's matching label had 3. The bridge now follows Konclude's active
class set and source terminology representation, including the exact binary
trigger absorber mechanics: over-use complexity penalty, cached trigger-pair
reuse, decreasing complexity/address order, reusable left-deep implication
chains, and rounded-average disjunctive trigger complexity. Common-disjunct
extraction now uses reusable dense signed-concept sets instead of cloning large
visited sets.

After that repair, saturation finished in about 31 seconds and already held the
positive taxonomy, but KM still timed out on redundant classification work.
Instrumented Konclude gave the decisive counts: 54,974 class items, 36,651
directly derived satisfiability results, 18,323 completion satisfiability jobs,
18,323 callbacks, and zero calculated pairwise subsumption tests. Source
inspection localized the difference to the all-satisfiability-jobs barrier in
`COptimizedKPSetClassSubsumptionClassifierThread::createNextSubsumtionTest`.
Konclude waits for every model callback, builds an `owl:Thing`-rooted sparse
propagation graph, compares all completed child/parent possible maps, and only
then allows pair scheduling. KM had ported the local message handlers but
interleaved each subject model with pair tests while the propagation graph was
still empty.

The synchronous classifier now has the same two phases. Prepare runs every
residue model and delivers its deterministic, possible-subsumer, and
pseudo-model messages. A single global barrier then builds the propagation
graph and recursively invalidates parent candidates absent from completed child
maps. Verify examines only candidates that remain unknown. On 3215 this
propagates 202,002 false candidates and schedules zero pair jobs.

Supporting hot-path changes retain the same saturation fixpoint: integer-keyed
label hashing, a pre-allocation exact-duplicate descriptor check that preserves
the opposite-polarity clash path, an O(1) LIFO process-linker free list, and
cached diagnostic gates. The production race also now limits the speculative
CB fallback to one thread only for faithful synchronous bridges with at least
50,000 active classes. A controlled IBEX run showed the reason: the exact bridge
finished in 137 seconds with one CB competitor but exceeded 240 seconds when
the fallback occupied 15 cores. Smaller bridge races and all winner/fallback
semantics remain unchanged.

Release validation is 1,468 passed, 0 failed, 7 ignored. The final 592-ontology
IBEX sweep reports 574 ok / 18 timeout and 508 exact matches, compared with 569
/ 23 and 499 exact matches in the preceding feature sweep. No gold-matching
ontology regressed. In addition to 3215, 11315, 12414, 4054, 4755, 7127, 7581,
8068, and 8864 become exact matches. The detailed causal record and
machine-readable aggregate are in `docs/SOLVE-3215.md` and
`results/benchmarks/2026-07-13-3215-closure/`.

Controlled IBEX job 48790909 reran the nine changed correctness cases with the
preceding and final binaries under identical flags. All nine binary pairs
completed, with eight exact-match improvements, one reduced disagreement, and
zero exact-match regressions. This confirms the correctness changes separately
from full-sweep node timing.

These changes do not alter the CB calculus or its derived clause set, so they
do not require Lean re-certification. They change faithful terminology
construction, completion-classifier bookkeeping, fixpoint-preserving storage,
and race scheduling outside the Lean-certified core.

### Konclude equivalent-non-candidate hand-off closes the 5303 regression (2026-07-13)

The first 592-ontology IBEX sweep of the 7914 feature stack exposed one real
same-configuration regression: `ore_ont_5303` lost exactly
`CarbonHydrogenSubstructure ⊑ Hydrocarbon`. A controlled old-binary versus
candidate-binary run reproduced `match → incomplete(1)`. The entailment follows
from the named molecular-group hierarchy, the carbon and hydrogen component
existentials, `hasComponentPart ⊑ hasProperPart`, and the `Hydrocarbon`
equivalent definition.

The completion model was not incomplete. A direct pair test returned true, but
the nondeterministic root read-off did not contain `Hydrocarbon`. Konclude does
not restrict possible subsumers to that root label. Its binary absorber keeps
non-absorbed equivalent definitions available through the TBox
`mEquivConNonCandidateSet`; its satisfiability analyser filters that live set and
emits `CClassificationInitializePossibleClassSubsumptionMessageData`; the KPSet
classifier installs and schedules the surviving pairs.

KM had already ported each downstream data structure and message handler, but
the production bridge broke both hand-offs. It retained the three source
definitions (`eq=0/3`, including `Hydrocarbon`) as `CCEQ` without registering
them, then invoked the older analyser wrapper with an empty local map. The
targeted port now:

1. takes Konclude's non-candidate branch for a source `CCEQ` that cannot be
   fully absorbed (the optional partial-equivalence candidate optimization is
   not materialized by this bridge);
2. calls the live-ontology equivalent-non-candidate analyser wrapper; and
3. refreshes the synchronous subject candidate list from the delivered KPSet
   possible map before pair verification.

The real 5303 production trace now shows subject 7 receiving the initialization
message, scheduling `CarbonHydrogenSubstructure v Hydrocarbon`, and confirming
the pair true. `production_has=true` while the deliberately weaker raw read-off
remains false, which isolates the repair to Konclude's classification pipeline.
The environment-independent regression
`source_absorber_registers_unabsorbed_equivalent_non_candidate` covers the
source-preprocessing invariant. This is classification bookkeeping, not a
change to the CB calculus, so no Lean re-certification is required.

Final IBEX job 48737778 attempted all 592 ontologies: 569 ok, 23 timeout, with
499 exact Konclude matches. Relative to the immediately preceding
feature-enabled sweep, 5303 is the only signature change and improves from one
missing pair to exact. The 18-ontology same-flags panel reports zero
old-versus-final changes. A one-run 9663 timing difference did not reproduce:
the pre-fix feature binary and final binary both timed out at a 300-second
diagnostic cap with nearly identical memory.

### ore_ont_7914 closed by exact Konclude descriptor-chain port (2026-07-13)

`ore_ont_7914` now completes and matches Konclude exactly. The full run checks
all 93 completion residues, returns 141,517 subsumptions against the same
141,517 in gold, and has 0 extra, 0 missing, no unsatisfiable-class difference,
and no consistency mismatch. Slurm job 7936 finished in 2:30.56 at 18,882,684
KB. Targeted jobs 7934 and 7935 separately close the two prior false-positive
families. Final release validation on `ws`: 1,460 passed, 0 failed, 7 ignored.

The OR planning, OR-only dependency, and satisfiable-cache ports first changed
7914 from timeout to a terminating but unsound result with 29 extra
subsumptions. Cache tracing then found a precise contradiction: KM classified
branch-derived CCAND concept 45405 as nondeterministic, but replayed it from the
associated expansion cache as deterministic. Instrumented Konclude stored only
the corresponding branch-tag-1 descriptors as nondeterministic.

The final cause was a missing line in the Rust port of
`CReapplyConceptLabelSet::insertConceptGetClash`. Konclude prepends every new
descriptor with
`mConceptDesLinker = conceptDescriptor->append(mConceptDesLinker)`; KM replaced
the label head without linking the new descriptor to the old head. The severed
newest-first chain made the faithfully ported cache partition fallback wrap to
the head and duplicate a nondeterministic descriptor into the deterministic
suffix. `completion/u36.rs` now sets the new descriptor's `next` field to the
previous head before insertion. This is the exact C++ invariant, with no
ontology or concept conditional. The associated-cache allowance also now
matches Konclude's constructor default of one nondeterministic expansion.

Permanent tests cover production descriptor insertion, nondeterministic cache
prefix/suffix splitting, OR-only dependencies, and branch-open model read-off.
The full causal record, traces, source references, and job table are in
`docs/SOLVE-7914-9663-9724.md` and
`results/benchmarks/2026-07-13-7914-closure/`. Final IBEX job 48737778 ran a
Bullseye-linked binary over all 592 ORE pool ontologies at 240 seconds and 20
GB each. The final binary matched 7914 in its 78-second smoke task and in the
full sweep. No gold-matching ontology regressed in the corpus run, and the
same-flags controlled panel found no old-versus-final change.

### Source-terminology bridge solves 541 and 12653 in production (<1 s, 2026-07-10)

The disjunction-family blocker was not another completion-rule gap. Konclude
absorbs the normalized ontology concept graph before clausification, while KM's
bridge reconstructed that graph but still presented every generated definer and
recognition clause as an independent GCI. On the two target ontologies this was
the difference between Konclude processing 23/10 residual GCIs and KM processing
647/501 HT clauses.

The frontend now carries an env-gated normalized source-TBox side channel under
`KM_TRIGGER_ABSORB`. The bridge ports the relevant
`CConcreteOntologyUpdateBuilder` and
`CTriggeredImplicationBinaryAbsorberPreProcess` behavior:

- named-left inclusions become direct `CCSUB` unfoldings;
- pristine equivalent definitions use `CCEQ`, with fully triggerable
  definitions converted to `CCSUB` plus a reverse binary implication;
- property domains/ranges become role links rather than GCIs;
- only structural-left residuals reach full/partial binary GCI absorption.

The resulting preprocessing counters match Konclude: 541 has equivalence
absorption 1/2 and 22 absorbed residual GCIs (23 total before range movement);
12653 has 1/1 and 9 absorbed residual GCIs (10 total). The remaining search
correctness issue was sibling isolation: PathOfLength4 was falsely UNSAT under
the old mutable in-process OR stack, but SAT under complete branch-epoch COW,
matching Konclude's one-calculation-task-per-alternative behavior. COW is now
the trigger-absorption default. Saturation runs in an independent task unless
explicit satcache coupling is requested, and classification seeds its known
subsumers from the deterministic source `CCSUB` closure before verifying only
the residual candidates. The old reversed-disjunct second-model heuristic is
not used for source terminology.

`KM_TRIGGER_ABSORB=1` now enables the certified bridge racer and harvests its
sound+complete answer immediately (or receives no answer on defer). Release
measurements on `ws`, through `km classify`:

| Ontology | Wall | Peak RSS | Gold comparison |
|---|---:|---:|---|
| ore_ont_541 | 0.86 s | 428 MB | 164/164 local-name pairs, 0 missing, 0 spurious |
| ore_ont_12653 | 0.08 s | 9 MB | 10/10 pairs, 0 missing, 0 spurious |

541 emits 166 full-IRI pairs because it correctly distinguishes two different
classes both locally named `ProcessQuality`; projection to the ORE gold's local
names gives the exact 164-pair set. Default frontend JSON remains byte-identical
with the flag off. Validation: 1433 passed, 0 failed, 7 ignored.

### Saturation-first probe answering, waves 1-3 (`18c9a46` .. `c116a9c`, 2026-07-09/10)

The confirmed lever for the disjunction/cardinality timeout family (541, 12653,
...): Konclude decides ~95% of subsumption tests by its approximation
saturation before any tableau search. The 12 ported saturation units are now
WIRED in front of the bridge's completion probes, opt-in `KM_HT_SATURATION=1`
inside the `KM_HT_BRIDGE` arm (`18c9a46`): production config, per-
(concept,polarity) seeds, budgeted run (`KM_HT_SATURATION_BUDGET_S`, discard
on overrun), and `CPrecomputedSaturationSubsumerExtractor`-style consumption
(CLASHED = unsat-certain; completed and not INSUFFICIENT = sat-certain with
the exact subsumer row; residue unchanged to the probes). Five port bugs were
fixed on the way in, plus a default-path root-top fix (bridge probe roots were
created without TOP, silently weakening bottom-rule clash detection).

Wave 1 (`8481c9b` + `76cc6e0`): the precise ATMOST criticality test (collect +
simple/detailed mergeability + ancestor INSUFFICIENT marking replaces the
node-poisoning substitute) and a critical-queue misrouting fix. The s03
file-local CCT_DISJUNCTION/EQCANDIDATE tags were 4/5 but Konclude's enum is
2/3, so every OR critical was routed into the always-defer VALUE stub queue
and the precise OR test never ran. Found via per-type SAT-STATS counters.
After both fixes the family criticals are decided by the real tests and are
genuinely critical: the criticality-test path is exhausted as a lever.

Wave 2 (`1b57b9d` + `bf282e8`): the saturation-node coupling into the
completion probes, Konclude's production completion profile (expand created
successors from saturated labels, caching-blocking from saturation, and the
generating-existential absorption that terminates tree growth at cached
nodes). Saturation runs on the probe env; `reset_probe_env` carries the ~43
saturation arenas across probe resets (`adopt_saturation_state_from`).
Opt-in `KM_HT_SATCACHE=1` on top of `KM_HT_SATURATION=1`: measured on 12653,
coupled probes poison-defer at subject 1 vs 14 plain, because without the
extension-resolving refinement the replayed labels under-approximate
forall-restricted successors and caching fails to establish exactly where it
matters. Becomes profitable once `getSaturationResolvedIndividualNodeExtension`
is ported.

Wave 3 (`c116a9c`): the successor-EXTENSION machinery's wrong clashes (541
ext-ON: 11-13 satisfiable classes answered UNSAT-certain, nondeterministic)
ROOT-CAUSED via a 13-axiom ddmin reproducer and fixed. The watch-side
implication trigger check (`insert_concept_reapplication_return_triggered`)
faithfully ported the C++ positive-presence-only test, which is safe in
Konclude because absorption only builds positive-presence triggers, but the
bridge's clause encoding also emits negative-presence triggers; a label
carrying +C then satisfied a want-not-C trigger and a contrapositive
implication chain manufactured a clash on resolved extension nodes. Fix:
thread the wanted presence polarity (the inverse of the stored linker
negation, matching the already-polarity-aware insert-side reapply check).
Validation: reproducer 0/20 wrong (was 8/8); 541 extensions-ON three runs 0
wrong and 6-9 of 59 family subjects answered SAT-certain, the first sound
nonzero saturation coverage on the family; suite 1424/1424. `KM_HT_SAT_EXT`
stays opt-in: the extension fixpoint costs ~40s on 541 (vs 0.4s off) with
run-to-run coverage variance (HashMap-ordered succ-extension maps vs
Konclude's sorted CPROCESSMAP). Env-gated diagnostics kept:
`KM_SAT_CLASH_TRACE` (all CLASHED-set sites, indirect propagation edges,
implication executions), `KM_SAT_ADD_TRACE=<concept>` (backtrace on watched
adds), extended `KM_SAT_DEBUG` dumps (subject/name/concept tables).

Also closed: the suspected "plain bridge no longer closes 12653" regression is
NOT a regression. Bisect (1c931e7 / 18c9a46 / 8481c9b / HEAD) shows the
permanent poison-defer at every point; the recorded 10-20s plain closes date
from before `7a01372` restored the complete-or-defer contract (unrestored
advances poison SAT verdicts by design), and the 17s figures were COW+DDB
probe-harness measurements. The production baseline (bridge off) never
regressed.

### Unsat-cache learning: functional, zero reuse on the family (`1fc2618`, `9c03476`, `1c931e7`)

Konclude's nogood store (occurrence unsatisfiable cache) wired live into the
bridge: handler install, carry across probe resets, read probes at Konclude's
rule points, write counters. Two bugs made it real: bridged concepts carried
no TERMINOLOGY so the u22 validity guard rejected every line (fix: terminology
stamp sweep in bridge_tinput), and the write-slot ring had ONE slot so the
first write deadlocked the C++ concurrent-reader wait protocol in-process
(gdb-proven; Konclude sizes workers+2; fix: ring of 3 plus bounded rescan that
skips the write instead of hanging). Post-fix verdict: overhead ~zero (12653:
17.2s vs 17.0s in the COW+DDB probe harness) but 0 read hits on 12653/541 —
the family's nogood lines carry seed and branch-specific atoms and never recur
as a label subset, so this mechanism cannot prune the family (valid negative;
Konclude's family speed is saturation + absorption, not its unsat cache).
`KM_HT_UNSATCACHE` stays opt-in. Also in this arc: Arc-COW extended to the
remaining map-bearing node satellites (role_succ / distinct / succ_role
hashes).

### Bridge correctness campaign + production wiring (2026-07-06 .. 07-08)

The bridge went from "solves 12653 in a harness" to a production-wired,
complete-or-defer arm of `km classify`:

- **Production route + env reuse** (`ca772f1`, `067aaa4`): read-off soundness
  gate, one bridged env per classification with per-probe resets
  (byte-identical A/B vs fresh envs), universe filter, per-subject defer.
- **COW branch epochs** (`d5603a0`, `7549697`, `0c5848f`): complete
  per-alternative state restore via epoch journal + arena watermarks; 541
  probes collapse 1M+ chronological backtracks to 435; later localized to
  per-node Arc-COW label sets + processing queues (O(1) journal save, deep
  copy on write = Konclude's task-fork shape). Decisive measurement: the 541
  residual is SEARCH VOLUME, not restore cost.
- **DDB (dependency-directed backjumping)** made trustworthy: taint-loss root
  cause (`2a869e8` DetLink back-edges), wrong root-cancels closed by trigger
  deps (`93e62e4`), and the u29 wrong-UNSAT root-caused to leftover poisoning
  and gated on `unrestored_advance_count == 0` (`7c521cb`, found by ddmin
  264 -> 5 axioms).
- **Soundness fixes**: at-most polarity + nondeterministic merge branching +
  choose rule (`1497954`), ALL-rule dependency threading (541 spurious
  unsatisfiability, `a4a3ae6`), phantom card-defs delivered absorption-only
  (`84e38bf`, closed the whole COW oracle-anomaly family), read-off search
  bounded by the probe budget (`42a8b74`, `1d188d6`).
- **Complete-or-defer restored** (`7a01372`): unrestored advances phantomize
  existential successors, so the poison now defers SAT verdicts instead of
  trusting them. This is why 12653's plain-bridge close from the `067aaa4` era
  now defers by design.
- **At-most resume port** (`371f38f`, `KM_HT_ATMOST_REST`): Konclude's
  branchingMergingProcRest state machine (incremental link scan via edge
  watermark, persistent candidate lists, distinct-clique init clash).
- **Panel verdict** (`6ac4a31`, results/benchmarks/2026-07-08-bridge-panel/):
  KM_HT_BRIDGE=1 flips exactly one ontology ok->timeout and closes nothing,
  so the bridge arm stays OFF in production. Baseline 576/584 ok; km beats
  Konclude on BOTH medians (0.21s/33MB vs 0.25s/135MB), faster AND lighter on
  356/576.

### Orchestration speed wins: +55 beat-Konclude goal-wins (2026-07-07)

- **In-process CB engine** for small non-EL ontologies (`8847b85`, gated on
  no-internal-definer-disjunction `b2f58fd`): +25 wins (IBEX 48105343 era
  snapshots).
- **Frontend meta/clauses parsed with `from_slice` instead of `from_reader`**
  (`2b8f224`): serde's reader path was the bottleneck; ore_ont_10073 frontend
  19s -> 5s; +30 wins.
- **Blank-node meta filter** (`14af873`): `_:genid` nodes excluded from
  named/iri_map; WIN 272 -> 284, solved 576 held.

### konclude_ht bridge solves ore_ont_12653 sound+complete in 1.0 s (`d64e78b`)

ore_ont_12653 (production 240 s timeout, disjunction + qualified-cardinality
family) classifies missing=0 spurious=0 via the ported Konclude algorithm.
Three coverage ports (domain/range at link install, inverse-role hierarchy on
concrete inverse-role objects with both-polarity closure, first-class
qualified `≥n/≤n` from `card_defs`) plus a pairwise `bridged_unsat` fallback
for nondeterministic subjects. Validation: konclude_ht suite 1208/1208;
ore_ont_1016 read-off regression identical (32712/32739, spurious=0).
Instrumented diagnosis of the rest of the family: ore_ont_541 is pure
chronological-backtrack thrashing (nodes=4 flat, ~2^56 branch space) and needs
the u29 dependency-directed-backjumping port; ore_ont_7914 is model explosion
(46k nodes) and needs blocking/lazy-∀. Full recipes:
`docs/SOLVED-ONTOLOGIES.md`.

Follow-up (same day): model read-off soundness gate. `or_backtrack_count == 0`
is NOT a determinism witness — a drive can open OR branch points and commit to
first disjuncts without clashing, polluting the root label (86 spurious
subsumptions measured on ore_ont_3215). Read-off is authoritative only when
NO branch point was opened (`or_branch_open_count`); nondeterministic subjects
degrade to candidate extraction + exact pairwise verification.

### In-process frontend fast path for small onts (+47 beat-Konclude WINs)

`classify` forked the `ofn` subprocess even for trivial ontologies, where the
standalone parse is < 10 ms but the classify frontend phase is ~50 ms — the
fork/exec of the 4.4 MB binary plus the clause/meta file round-trip. On the ~125
near-tie onts (KM losing to Konclude by < 1 ms on ~0.14 s totals) that fixed
overhead was the whole margin. Onts under 2 MB now run the frontend IN-PROCESS
(`ofn_to_clauses` directly, same function the subprocess runs), writing the
clauses file and returning the meta — byte-identical output. Memory-safe: the
2 MB cap keeps the giants' multi-GB transient parse peak isolated in the
subprocess; the small-ont transient is tens of MB and is freed before the engine
runs. Opt out with `KM_NO_INPROC_OFN`.

Full IBEX panel (job 48088964) vs the absorbed-plain panel (48086814): **WIN
166 → 213 (+47); SLOWER 216 → 153; FAIL 8 → 8; 0 unsound.** Cumulative across
both orchestration fixes this cycle (vs the pre-fix baseline 48085418): **WIN
136 → 213 (+77), 24% → 37% beating Konclude on both speed AND memory; timeouts
9 → 8.** The +16 SLOW+MEM/MOREMEM shift is speed-losses changing category (the
in-process parse peak on the larger sub-2 MB onts), not WIN→loss regressions.

### Portfolio CB arm uses the absorbed-plain path (+30 beat-Konclude WINs, −1 timeout)

The certified-elc portfolio ran its CB arm via `run_engine_adaptive` on the
ABSORBED clause set directly, while `cb_stack` (the non-portfolio default) runs
CB via `race_absorbed_plain` — an 8 s PLAIN (un-absorbed) probe, then the
absorbed set. On onts where absorption makes the clause set harder for CB, the
absorbed-only run is far worse (ore_ont_1082: CB 44 s / 8.7 GB in the portfolio
vs 2.9 s / 130 MB via absorbed-plain). The portfolio CB arm now uses
`race_absorbed_plain`, the same path `cb_stack` uses. Same sound+complete engine
on output-preserving clause encodings, so the CB answer is unchanged; the elc
racing is untouched, so the portfolio's recoveries are preserved.

Full IBEX panel (job 48086814, all 584 onts, KM vs Konclude wall+peak+gold) vs
the pre-fix baseline (48085418): **WIN (faster AND less memory) 136 → 166 (+30);
SLOWER 233 → 216; SLOW+MEM 203 → 190; FAIL 9 → 8 (ore_ont_14459, a 153 MB
near-giant, recovered); 0 unsound, 0 regressions.** Example flips: 11502
1.56 s/307 MB → 1.32 s/66 MB (now beats Konclude 173 MB). The remaining 8 FAILs
(541, 3215, 7914, 9663, 9724, 10621, 12653, 14817) plus the 2 contested-correct
(2669, 15516) are unchanged.

### SWRL DL-safe rules default-on, rule-gated (+3 ORE: 2669, 15516, 10906)

Three ORE timeouts are SWRL ontologies KM already solved correctly but only
under the opt-in `KM_HT_RULES` flag. The flag is now DEFAULT-ON (opt out with
`KM_NO_HT_RULES`), with the whole feature gated on ACTUAL DL-safe-rule
presence so it is provably inert on every rule-free ontology:

- Frontend `collect_rules` runs by default but returns empty on a rule-free
  ont, so `ht_rules` stays false and the clause output is byte-identical.
- `cb_to_ht` derives `rules_active = ht_rules && !rules.is_empty()`, which now
  gates the ABox-nominal seeding, the ground-fact interception, and — the old
  blocker to default-on — the emelim suppression. On a rule-free ont emelim
  still runs exactly as before.
- The rules-consistency check short-circuits ONLY on a detected inconsistency
  (⊥ subsumes all ⟹ the empty-subsumption verdict is complete). A CONSISTENT
  rule ontology falls through to normal classification so its hierarchy is
  still computed; DL-safe rules range only over named individuals and cannot
  change a TBox subsumption, so the fall-through is sound + complete.

Validation — all 6 corpus onts carrying `DLSafeRule`, default vs
`KM_NO_HT_RULES`: **2669** (240 s timeout → inconsistent, 0.17 s), **15516**
(→ inconsistent, 0.16 s), **10906** (→ inconsistent) all now correct
(genuinely inconsistent; HermiT agrees, gold wrong — see
`docs/CONTESTED-GOLD.md`); 13129 consistent 83 subs == 83 subs (identical, no
regression); 12451 and 10860 unchanged timeouts. +3 recoveries, 0 regressions,
1390/1390 unit tests green.

### HT: first-class cardinality route default-on (+3 ORE) and functional-role tagging (+1, gated)

The Konclude-port first-class `≥n`/`≤n` number rules (`KM_HT_CARD`) and the
propagation-based `≤n` recognition (`KM_HT_CARD_RECOG`, with SHIQ non-shared ∀
handling and mode-5 blocking) are now DEFAULT-ON; opt out with `KM_NO_HT_CARD` /
`KM_NO_HT_CARD_RECOG`. Validation: full 584-ont km-only IBEX panel with the
flags (job 48067625) — 574 ok, 573 gold-MATCH, 1 DIFF (10702, pre-existing
nominal incompleteness), 0 MATCH-to-DIFF regressions; recovers **ore_ont_1603
(21.7 s), 9540 (20.8 s), 7499 (82.5 s)**, all previously 240 s timeouts. A
default-config confirmation panel (48076591) reproduces the result with no env
set. A 156-pair flag-portfolio sweep (48066078: 13 timeout onts x 12 configs)
established these are the only flag-recoverable timeouts besides the contested
SWRL pair (15516/2669 via `KM_HT_RULES`, correct-but-gold-wrong; kept opt-in
since enabling it also disables complementary-definer elimination globally).

`KM_HT_CARD_FN` (new, opt-in): the frontend additionally tags
`FunctionalObjectProperty(R)` as a first-class global `⊤ ⊑ ≤1 R.⊤` — a fresh
universal marker concept asserted as a ⊤-fact with a max-CardMeta whose marker
and filler are that concept, so the HT `≤n` merge folds functionality instead
of branching over the raw `R(x,y0) ∧ R(x,y1) → y0 = y1` Eq clause (which is
kept: the CB engine consumes it, and it is redundant-but-sound on the HT).
**ore_ont_541: timeout in every prior config → 21 s, gold-exact.** Kept gated
OFF: its own 584-ont corpus panel (48080229) found the flag NET-NEGATIVE —
572 gold-MATCH vs 573 for the default (card without CARD_FN), because tagging
every functional-role ontology card-routable regresses ore_ont_1016
(MATCH → DIFF, a correctness break on 1016's functional roles) and ore_ont_7581
(MATCH → timeout, the extra markers + emelim-disable push it over budget) to
recover only 541. So 541 is not cleanly recoverable this way; CARD_FN remains a
diagnostic opt-in, not a default.

Also: `transitive_close_subs` now closes the confirmed subsumption relation at
the HT worker's serialization boundary (both the Ht and legacy-Tableau paths).
Phase 2 tests only candidates from one captured model root label plus a
told-clause closure, so an inferred (domain/range-derived, non-told) subsumer
absent from that model could yield `A ⊑ B` and `B ⊑ C` without the entailed
`A ⊑ C`. Closing is unconditionally sound (subsumption is transitive; the pass
only adds entailed pairs). Benchmark-inert (the ORE harness canonicalisation
already closes) but makes the raw JSON output correct on its own.

Diagnosis note: ore_ont_7499's apparent 3297-pair incompleteness against gold
is a localname-collision artifact, not a reasoning gap — the ontology carries
one axiom in the `purl.org/obo/owl/CHEBI#` namespace while the BFO upper
hierarchy lives in `purl.obolibrary.org/obo/CHEBI_...` with no bridging axiom;
KM correctly keeps the namespaces distinct and matches gold after localname
canonicalisation (same artifact class as ore_ont_12698's residual 18).

### HT/QoSat: QO hybrid router (`KM_HT_QO_ROUTER`) — sound certify-or-defer race arm

Wires the validated hybrid certify path into production as a structurally-routed,
sound certify-OR-DEFER race arm behind one flag (default off):
- `quasi_order_classify` gains a certify-only mode: a structural pre-gate defers
  when the clause set has no inverse bridge, and after the kpset attempt it defers
  (no funnel) when it cannot certify — emitting an answer ONLY when kpset certifies
  (sound+complete by construction).
- The tableau worker, in certify-only mode, returns no answer on a deferral (no
  fallback to branching/legacy tableau) so the orchestrator's CB engine decides.
- `spawn_ht` detects inverse BRIDGE clauses (cb_to_ht reports `inverse=false` for
  that encoding) and routes only faithful, nominal-free, inverse-bridge onts to the
  hybrid+certify-only arm; non-inverse HT-routable onts keep their normal branching
  path. The CB-vs-HT race runs in "race" mode so the fast certify beats a CB that
  would time out.
- The router runs the certify arm in correctness-aware FALLBACK mode (CB preferred
  whenever it finishes; certify taken only when CB errors/exceeds `KM_HT_BUDGET_S`).
  This is necessary because the kpset certify is NOT a guaranteed completeness
  oracle — on ore_ont_15098 it reports `kp_miss=0` but yields 939 where the truth
  is 951; fallback keeps CB's correct 951, race mode wrongly let the faster
  incomplete certify win. Sound regardless of the gap: the certify is relied on
  only where CB produces no answer at all (e.g. 7581's timeout).
- Router-mode corpus sweep (unimatrix job 7369, real production pipeline, only
  `KM_HT_QO_ROUTER=1`): **561 ok / 559 clean / 21 timeout; 0 regressions vs
  baseline.** 7581 recovered (565317=gold, 0/0, 166 s); 15098 km=951=gold (CB wins);
  the 2 gold-gaps (11745 +5/-1, 6999 −1) are pre-existing (parallel artifact /
  datatype gap, identical to baseline). 21 timeouts are the known-hard
  disjunction-family / giant set the hybrid does not target. 131 tests pass.

### HT/QoSat: corpus validation of the hybrid (0 regressions) + INVCOMPOSE trigger-rebuild fix

Full ORE-2015 sweep (unimatrix job 7322) comparing the HYBRID
(INVCOMPOSE+FPROP+SAT+KPSET) vs PRIOR-2a (funnel alone), both forced-QO + VERIFY,
each ont scored vs Konclude gold AND vs the other config (582/592):
- **0 regressions** — the hybrid is never worse than prior-2a on any ont.
- **7581 recovered** — hybrid 565317 = gold (0/0) in 32.7 s; prior-2a times out.
- All 14 gold-gap onts are `agree = true` (identical output in both configs) —
  pre-existing QO limitations (unsat under-detection, partial answers, the 6999
  datatype gap), CB-handled in production, not introduced by this change.
- Cost: 3 large CB-territory onts (11395, 3905, 3377=4.49M subs) time out where
  prior-2a finishes ~110 s — INVCOMPOSE+SAT overhead ⇒ the hybrid must be ROUTED
  to its Horn-inverse certify fragment, not blanket-enabled.
- Bug found+fixed by the sweep: INVCOMPOSE swapped `self.clauses` without
  rebuilding the Ht tableau triggers → per-concept verify panicked on ore_ont_10127
  (`fire_anchor_concept` out-of-range). Fixed by `rebuild_triggers` (98077ba);
  10127 now gold-exact.

### HT/QoSat: hybrid certifies 7581 sound+complete in 31s (4x) — `fprop` + `fcheck` + `sat` + `kpset`

Closed most of the 126s → Konclude-~10s gap. The key was Konclude's G1 (a filler
label is never read as a named subsumer) realised via `sat_mode` separate
per-(concept,role) filler nodes, plus a forward-broadcast store for the composed
inverse clauses.

- **`fprop` (`KM_HT_QO_FPROP`)** — forward-broadcast mirror of `prop` for
  head-on-TARGET Horn NF4 (the shape `compose_inverse` emits). FIXES the
  `KM_HT_QO_INVCOMPOSE` divergence: the composed clauses re-fired per edge; now
  they broadcast once per (source, role) and converge at forward-only cost.
- **`fcheck` (`KM_HT_QO_FCHECK`)** — composed clauses in containment-CHECK mode.
  Established that WRITING the composed head to a SHARED filler over-derives
  (1.34 GB), so the inverse head must not be written as a subsumer (Konclude G1/G3).
  Sound but, at filler granularity, defers (1581 false insufficiencies on shared
  fillers); reachability routing recovers nothing (0/72989, dense graph).
- **Hybrid `INVCOMPOSE + FPROP + SAT + KPSET`** — the sound+complete fast path.
  Composable inverse consumers (110k of ~110k on 7581) become forward clauses
  written to SEPARATE filler nodes (sound — named self-nodes stay inverse-clean,
  G1); residual non-composable bridges are kpset containment-checked; certify iff
  `kp_miss = 0`. A `count_inverse_bridges` guard makes the bare write path defer
  (not silently drop) on any residual bridge.
- **Measured ore_ont_7581 (ws):** `QOKP certified sound+complete (kp_miss=0)`,
  **31.3 s / 1.0 GB, km = 565317 = gold, 0 unsound / 0 incomplete.** 4x faster
  than the 126 s pseudo-model-merge path, within ~3x of Konclude's ~10 s, lowest
  memory of any path. All gated (default off), 131 tests pass. Remaining gap is
  constant-factor (saturation throughput + ~43k extra filler nodes), not a missing
  mechanism. Next: corpus regression (unimatrix) before default-on routing.

### HT/QoSat: 2b levers 1 & 2 toward Konclude ~10s — both quick forms REFUTED (findings)

Two attempts to close the 126s → ~10s gap (the 90-104s is building 63 real
`consistent(A)` pseudo-model tableaux; per-A timing shows a few are intrinsically
slow, 45-64s, large DETERMINISTIC inverse expansions).

- **Lever 2 — inverse re-encoding (`KM_HT_QO_INVCOMPOSE`, `compose_inverse`).**
  Resolves each bidirectional inverse bridge into its single-role consumers as
  forward clauses, drops the bridges (sound: resolvents; real ∃-edges untouched;
  130 tests pass). 7581's part_of/has_part inverse is bidirectionally load-bearing
  and all ~110k consumers are single-role NF4, so it applies cleanly. **Net-negative:
  the gate saturation DIVERGES** — the reversed-edge NF4 (`∃r.D⊑E`, head-on-source)
  is `prop`-optimised (computed once per (filler,role), broadcast), but the composed
  forward-∀ clause (head-on-target) re-fires per edge. So avoiding reversed edges is
  strictly slower; the reversed-edge + `prop` encoding is the efficient one and the
  shared-filler write is intrinsic to the inverse regardless of encoding. Kept gated
  (default off) as a documented negative result.
- **Lever 1 — faster models.** `KM_HT_PAR=48` ≈ `PAR=16` (103s vs 104s) — not
  thread-bound (allocator/memory contention; RSS 2.5→6.7 GB). The candidates provably
  require the exact tableau (the inverse-augmented saturation over-approximates so it
  can't refute a candidate; forward under-approximates so it can't confirm). The only
  real lever is a satisfiable-expander cache made sound under inverse (KM's
  `KM_HT_SATCACHE`/`SATFOLD` are the no-inverse versions) — the substantial remaining
  port. The certified 126s under-budget result stands.

### HT/QoSat: 2b P2 — pseudo-model merge certifies 7581 sound+complete UNDER budget (`KM_HT_QO_PMMERGE`)

Port of the concept part of Konclude's pseudo-model refutation
(`isPseudoModelSubsumerPossible`,
`COptimizedKPSetClassSubsumptionClassifierThread.cpp:1626`). For each tight
inverse-only candidate `(A,B)` from the verify funnel, instead of the blowing-up
`consistent(A ⊓ ¬B)`, build ONE satisfiability model of `A` (`model_root_pos` =
`consistent(&[A])`, far easier than `A ⊓ ¬B`) and **refute `A ⊑ B` iff `B` is
absent from that model's root label** — sound (`B` false in a real, inverse-aware
model of `A` ⇒ `A ⋢ B`). Survivors (B present, undecided) fall through to the full
tableau; refuted candidates are dropped with no tableau test. Gated, default off;
130 cargo tests pass (new: `pmmerge_model_root_refutes_nonsubsumer`).

**Result on ore_ont_7581 (ws): SOUND + COMPLETE + CERTIFIED, UNDER the 240s
budget.** `565317 = gold, 0 unsound / 0 incomplete`, **129s / 2.5 GB** (vs 2a's
**244s**, over budget). The pseudo-model merge refuted **all 177** tight candidates
→ **0 survivors → 0 `consistent(A ⊓ ¬B)` tableau tests** — the hard inverse blowups
that wrecked 2a are never reached (verify stage 0.37s). This is the first time KM
certifies 7581's completeness within budget rather than trusting the forward-only
result.

Remaining gap to Konclude (~10s): the pseudo-model pre-filter spends ~90s building
63 full `consistent(A)` models. Baking the result-identical incremental
blocking/obligation speedups into the model-builder workers (`set_fast_tableau`)
shaves only ~7s — the cost is intrinsic model size. Building the pseudo-model from
the (forward) saturation instead would be **unsound** (the forward label
under-approximates inverse-entailed subsumers; "B absent ⇒ A⋢B" would refute real
subsumptions on load-bearing-inverse onts). Konclude itself builds pseudo-models
from per-concept SAT completions and fast-paths them with a cached ⊤-saturation;
KM's `KM_HT_SATCACHE` is sound only for ALC(H) no-inverse, so it cannot fast-path
7581. The genuine levers to ~10s are a sound inverse-aware fast-sat cache, or a
cb_to_ht inverse encoding that avoids materialised reversed edges. See
`docs/KPSET-PLAN.md`.

### HT/QoSat: 2b Phase A — Konclude G2/G3 inverse-criticality containment check (`KM_HT_QO_KPSET`)

Port of Konclude's saturation criticality
(`isCriticalALLConceptDescriptorInsufficient`,
`CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp:3451) into
`QoSat`. Gated, default off; zero baseline risk (129 cargo tests pass, incl. two
new KPSet tests; the forward-only and verify paths are untouched).

The mechanism (Konclude G2 "from a successor propagate status, never labels" / G3
"insufficient → tableau"): KM now KEEPS the inverse-bridge clauses (materialises
the back-edges, recorded in `inv_edges`), but every concept-head write whose
firing matched an inverse back-edge becomes a **containment check** rather than a
write — `kp_check_head` / `kp_write`, deferred to the saturation fixpoint
(`kp_finalize`, Konclude's `checkCriticalIndividuals` post-pass). The would-be
operand is never added to the shared model; if the target already carries it (the
forward closure forced it) the check passes, otherwise `kp_insufficient` is raised.
Because nothing is written across a reversed edge, the cross-concept shared-filler
conflation (the 6.5M spurious facts on 7581) cannot form.

**Result (ore_ont_7581, ws):** the inverse-AWARE pass no longer blows up — whole
`km classify` runs at forward-only cost (**37s / 1.0 GB**, vs the old
inverse-augmented **111s / 6.5M-fact** pollution), and it is SOUND (never
over-derives; unit tests + gold-exact fallback, 565317 = gold, 0 unsound / 0
incomplete).

**It does not yet CERTIFY 7581.** `kp_miss = 929558` over `inv_edges = 898356`:
KM's cb_to_ht encodes inverse roles as materialised reversed edges, and the 129k
`∃r2.D ⊑ E` clauses fire across them at SHARED fillers, producing ~930k
predecessor-dependent consequences that are not forward-present (all spurious,
since NOINV = gold). The containment check correctly refuses to write them, but the
single global `kp_insufficient` bool is too coarse — one miss at any shared filler
defers the whole classification — so KPSet defers and the pipeline falls back to the
gold-exact forward-only result. Reaching Konclude's insufficient ≈ 0 needs the other
half of the port (study doc P2): **per-node insufficiency** (certify the CLEAN
concepts) + **per-concept possible-subsumer tracking with pseudo-model-merge
refutation** (`isPseudoModelSubsumerPossible`) to prune the spurious possibles
before any tableau test. See `docs/KPSET-PLAN.md`.

### HT/QoSat: verify funnel 2a — structural suspect selection + parallelism (511s → 244s)

Two speedups to the `KM_HT_QO_VERIFY` certification funnel, both sound, both gated:

1. **Structural suspect selection** replaces the inverse-augmented global pass that
   selected suspect concepts (measured **111s** on 7581) with an O(nodes+edges) scan
   of the forward model: a concept is a suspect iff its forward closure can reach an
   edge on an inverse-having role — the only way inverse can affect its
   classification (the `r⁻` back-edge is created from a forward `r`-edge). Sound
   over-approximation; **111s → 0.03s** (flags all 72,989 concepts on 7581, which is
   fine — they funnel to the cheap per-concept stage). `KM_HT_QO_GLOBALSEL` restores
   the old inverse-global selection.
2. **Parallel work-stealing** (per-thread `QoSat` / `Ht`, the `classify_parallel`
   pattern, `KM_HT_PAR`) for the per-concept inverse de-conflation (**~330s → 7.7s**)
   and the candidate verification.

Net on 7581: **511s → 244s**, sound+complete (gold-exact: all 177 tight candidates
verify as non-subsumptions, result = forward `L` = gold).

**Remaining wall (the lever for 2b).** Candidate verification is still ~226s even on
16 threads — only ~1.5× from parallelism — because the 177 tight candidates are the
HARD inverse-dependent pairs and a few of their `consistent(A ⊓ ¬B)` complete-tableau
tests blow up (~hundreds of seconds each), the same complexity as the original 7581
problem; parallelism cannot shrink a single slow test. Deciding those in a sound
*saturation* instead of the blowing-up tableau is exactly Konclude's KPSet (G1/G2/G3)
— see `docs/KPSET-PLAN.md`. So 2a brings the certified path to the budget edge and
confirms the KPSet extension (2b) is necessary, not optional, for fast+certified.

### HT/QoSat: sound+complete verify funnel (correct, but bounded by inverse-saturation cost)

Adds a sound+complete certification path behind `KM_HT_QO_VERIFY` on top of the
forward-only global gate, plus the measurements that show why certified-complete is
*not* fast on 7581. The funnel (`qo_classify_global_fwd` verify-prep):

1. forward-only global pass → sound subsumer lower bound `L` (10s, gold-exact);
2. one inverse-augmented global pass SELECTS suspect concepts (those whose
   inverse-augmented closure exceeds `L`) — a sound superset of the concepts whose
   true classification could differ from forward-only;
3. a per-concept (single-seed) inverse saturation runs ONLY on the suspects and
   de-conflates each to its TIGHT candidate set (single-seed avoids the
   cross-concept filler conflation that bloats the global set);
4. the caller confirms each tight candidate with the complete tableau
   `consistent(A ⊓ ¬B)`. Result = `L ∪ confirmed` = sound + complete.

On 7581 the funnel is correct — it collapses the **6.5M** global candidate pairs
(across 10635 suspects) down to **177** tight candidates, all of which verify as
non-subsumptions (forward-only is complete here). Verification itself is cheap
(measured ~0.02–0.26s per candidate; the 560s in the prior per-concept VERIFY was
the saturations, not the verifies).

**But the certified path is >280s on 7581, and the cause is fundamental.** The
inverse-augmented saturation pollutes catastrophically: the global inverse pass
alone takes **111s** (vs 10s forward-only) building a 6.5M-fact model, and the
per-concept inverse saturations *thrash* (16M edge-ops for a single 71-node
concept). KM's inverse handling reads a shared filler's runtime *label* across
back-edges (an EL backward-link read), so inverse back-edges blow up propagation.
Forward-only (which drops those edges) is the only fast saturation. **The necessary
lever for fast+certified on inverse onts is a sound, efficient inverse saturation
(Konclude's KPSet G2: from a successor propagate only status flags, never labels) —
a substantial algorithm extension, not a routing tweak.** Gated off
(`KM_HT_QO_VERIFY`), zero impact on the 568 baseline. See project_km_7581_qosat.

### HT/QoSat: single-pass forward-only QO gate — 7581 saturation matches Konclude

The per-concept forward-only gate (below) decided 7581 by running one single-seed
saturation **per concept** — 73k saturations, ~109s. `qo_classify_global_fwd`
replaces that with **one** forward-only global saturation seeding every concept as
its own self-node (shared `∃`-fillers), then reads each concept's subsumers off its
own self-node label. This is Konclude's architecture
(`CCalculationTableauApproximationSaturationTaskHandleAlgorithm` = one
approximation saturation; `CPrecomputedSaturationSubsumerExtractor` = subsumers
from a concept's own node). Tried first under `KM_HT_QO_PC`; falls through to the
per-concept gate only when the global pass cannot cleanly decide (a parked
disjunction, `∀`/range filler pollution `qo_insufficient`, or an out-of-fragment
bail). Same soundness/completeness profile as the per-concept gate (sound always;
complete when inverse is non-load-bearing — true for 7581).

Measured on `ws` (same hardware as Konclude):

| | wall | peak RSS | vs gold |
|---|---|---|---|
| Konclude v0.7 | 9.7s | 2.5 GB | — |
| KM QO saturation core (`km tableau` on the TInput) | **10.3s** | 0.69 GB | gold-exact |
| KM end-to-end `km classify` (CB disabled) | **24s** | 1.0 GB | 565317=565317, 0/0 |

So the QO saturation core **matches Konclude** (10s vs 9.7s) at *lower* memory;
end-to-end is 24s (8.6s frontend + 10s saturation + ~5s I/O of the 174 MB output)
versus Konclude's 9.7s. 127 cargo tests pass; 7581 byte-exact to gold.

**Why not a certified-complete verify pass (measured, not done).** Forming the
inverse-only candidate set from a *global* inverse-augmented pass is infeasible: on
7581 the inverse global saturation over-derives **6.5M** spurious candidates
(cross-concept shared-filler pollution), so the complete-tableau verify cannot
finish. A per-concept inverse pass bounds the candidates (~177) but costs one
saturation per concept (~109s) plus a tableau test per candidate (~3s) ≈ 600s — not
Konclude-competitive. A cheap *structural* certificate ("the reversed roles are
never read by a rule body") also fails: 7581's reversed roles are consumed 100k+
times yet contribute nothing (NOINV = gold). So certified completeness under
load-bearing inverse stays the open problem; forward-only is shipped as sound (and
complete on the inverse-inert fragment that includes 7581).

**Harness note.** The Rust orchestrator reads `KM_ENGINE` for the engine-binary
override, not `KM_ENGINE_BIN` (config.rs:84). Scripts/docs that set
`KM_ENGINE_BIN=/bin/false` to disable CB were silently running the real CB engine,
which (on 7581, a CB timeout) starved the niced HT racer and made fallback wait out
`ht_budget_s` (225s) before taking HT's ready answer — the apparent ~238s. With the
correct `KM_ENGINE=/bin/false`, CB errors in 0.25s and the QO answer flows at 24s.

### HT/QoSat: forward-only per-concept gate makes 7581 sound + complete (gold-exact)

`ore_ont_7581` (73k-concept Horn-ALCHQ giant, a CB-engine timeout) now classifies
through the per-concept QoSat gate **sound and complete, byte-exact to Konclude
gold**: `km = 565317, gold = 565317, unsound = 0, incomplete = 0` (validated
end-to-end via `oracle/ore/ore_canon.py`). The gate was previously complete but
produced 106 spurious subsumptions. Behind `KM_HT_QO_PC` (opt-in, not in the
default config), so zero impact on the 568 baseline. 127 cargo tests pass.

**Root cause (pinned, supersedes the earlier range / cardinality / canon-artifact
theories).** The tableau input carries 4 inverse-bridge clauses (a single role
head with arguments swapped versus a body role, `r1(x,y) → r2(y,x)`, encoding the
declared inverse pairs). These create model-specific reversed back-edges
(`filler → r2 → root`); the 129286 NF4-backward clauses then read the shared
concept-node's runtime label across those back-edges, deriving seed-specific
consequences as global subsumers (`b ⊑ ∃r2.D` holds only because `root → r1 → b`
in that one model). This is the shared-filler-in-cycle pollution, attributed to
inverse — there are only 4 range clauses, so range was never the cause. Proof:
dropping the inverse-bridge clauses yields gold exactly, so 7581's inverse is
declared but non-load-bearing (removing it loses zero real subsumptions).

**Fix.** `QoSat::new_opts(clauses, skip_inverse)`: `skip_inverse` drops the
inverse / symmetric bridging clauses. The shared-node saturation may read a
successor's runtime label only across genuine forward `∃`-edges, never across an
inverse back-edge, so forward-only is sound (monotone: dropping clauses never
over-derives) and complete whenever inverse is non-load-bearing.
`qo_classify_perconcept` returns the forward-only result by default. With
`KM_HT_QO_VERIFY` it also runs the inverse-augmented saturation (a complete
superset) and confirms each inverse-only candidate `(A,B)` with the complete
tableau `consistent(A ⊓ ¬B)` — sound + complete + general — but the per-candidate
full tableau is too slow on a 73k giant, so verify stays opt-in. Also ports
Konclude's per-creation-role range folding (`range_class` / `filler_node` /
`node_range`, fillers keyed by `(concept, range-class)`; test
`qopc_range_no_cross_role_pollution`); sound and reduces to the old behaviour when
no range clauses exist, though inert on 7581.

This matches Konclude's saturation (verified against its source):
`getRoleSuccessorALLConceptExtensionData(creationRole)` is per-creation-role
range folding, `isCriticalALLConceptDescriptorInsufficient` is the insufficiency
residue, and KM's defect was the G2 violation (reading a successor's label,
model-specific across inverse back-edges).

Open: 7581 runs ~283 s on `ws` (saturation ~109 s; the rest is frontend parse of
the 37 MB OWL), over the 240 s budget there; the benchmark-host timing is not yet
confirmed. Forward-only is sound everywhere but silently incomplete if inverse is
load-bearing on some other `KM_HT_QO_PC`-routed ont, so a cheap sound completeness
check (the full-tableau verify is too slow) is the remaining work.

### Hypertableau toward SHIQ: sound inverse + functional-merge primitive, two routing-gate fixes, and the Konclude saturation diagnosis (foundations, gated)

Groundwork for solving the disjunction / SROIQ family (`ore_ont_1603, 12653,
16444, 7581, 6934, 9540, 10702, 10908, 15672`) by extending the `Ht`
hypertableau from ALC(H) toward SHIQ, following HermiT's calculus and Konclude's
saturation architecture. Everything here is **gated** (`KM_HT_NUMBER`,
`KM_HT_FORCE`), **zero production impact**, and validated by unit tests; no
ORE coverage change yet — this lands the validated base plus the diagnosis that
re-targets the remaining work.

**Inverse roles in `Ht` — sound, unit-tested.** The `cb_to_ht` inverse bridging
clauses (`r(x,y) → r⁻(y,x)`) already propagate through the existing
`role_triggers → fire_anchor_edge → HeadItem::Edge` path; the prior "inverse is
inert" assumption was wrong about the mechanism. Two tests
(`inverse_role_propagates_universal_back`, `inverse_role_consistent_without_clash`)
confirm `∀r⁻` propagates back along the materialised inverse edge with no
over-propagation. `in_edges` now carries a `DepSet` (the shared structural change
for inverse soundness and node merging).

**Qualified-number node merge (≤n / functional).** Replaced the `apply_head`
`Eq`-head soundness bail with a node-merge primitive (`Ext::merge_into` +
`resolve` + `Trail::Merge`, modelled on HermiT's `MergingManager`): the victim's
concept label and incident edges are copied onto the lower-id survivor under the
union dependency, trail-recorded so backtracking undoes the whole merge; merged
victims are excluded from obligation expansion and blocking. A single `Eq` head
(functionality / ≤1) is a unit merge; multi-`Eq` (≤n, n≥2) still bails soundly.
Three tests (`functional_merge_forces_clash`, `functional_merge_consistent_when_compatible`,
`merge_inverse_existential_terminates`). A gated `RMF_STEP_CAP` bounds the body
matcher so an explosive join falls back soundly to CB instead of hanging.

**Two routing-gate fixes (the reason nothing reached `Ht` before).**
- `tableau.rs` `run_json` had a second in-fragment gate
  (`!inp.number && !inp.inverse && nominals.is_empty()`) independent of the
  `race.rs` routing guard, so every inverse/number ont fell through to the legacy
  tableau (which hangs on real ORE onts) and never reached `Ht`/QoSat. It now
  honours `KM_HT_FORCE`, so the engine actually runs on inverse/number onts for
  measurement.
- `QoSat` (the non-branching saturator) capped at `QO_NODE_CAP = 8000` nodes,
  tuned for the tiny 5303-family. Since QoSat seeds one shared node per concept,
  this bailed instantly on a real ontology (7581 has 72 989 concepts) → fell back
  to the per-concept branching classify, which hangs. The cap now scales with the
  concept count.

**Diagnosis (Konclude trace of 7581).** Konclude classifies 7581 in 5.6 s with
expressiveness `SRIF` (inverse + functional + chains + transitivity; no qualified
cardinality, no nominals): "*ontology has been sufficiently saturated, extracting
data for classification*" + 525 ms classification, i.e. essentially **zero**
tableau tests — the non-branching saturation is sufficient. With the two gates
fixed, KM's QoSat now runs on 7581 and is **bounded** (~73k nodes, no divergence)
but **too slow** (naive worklist + an `O(nodes)` match scan for unbound-source
role atoms; ~860k pending edges). It is a scale/efficiency problem, not soundness
or termination. The next lever is to make QoSat's saturation edge-indexed — the
same ELK backward-link-propagation optimisation already in `elc` — or to extend
`elc` to SRIF and route such onts there.

### QoSat saturation made edge-indexed (the elc backward-link optimisation, ported)

Removes the two `O(nodes)`/`O(#role-clauses)` scans that made QoSat diverge at
the 73k-node scale the 7581 diagnosis identified, porting the exact two index
structures `elc` already uses for ELK backward-link propagation. **Result-identical
by construction** (same clauses fire, same matches found — only located without
the full scans), so it is purely a speed change; gated paths (`KM_HT_QO`,
`KM_HT_HARVEST`) keep their semantics.

- **Incoming-edge index (`QoSat::in_edges`).** `match_body`'s unbound-source role
  case (`r(x, tn)` with `tn` bound, `x` free) scanned all nodes
  (`for sn in 0..label.len()`) to find predecessors of `tn` — `O(#nodes)` per
  match, the dominant cost on transitive / role-chain onts. It now reads
  `in_edges[tn]` (the `(role, source)` list maintained alongside `out_edges`),
  so predecessor enumeration is `O(in-degree)`. The index is trail-recorded and
  rolled back with its out-edge (residue-test DFS stays consistent).
- **Role-keyed clause firing (`QoSat::role_clause_trig`).** The edge worklist
  cloned the entire `role_clauses` list and fired every one on each new edge.
  Role clauses are now indexed by the exact role(s) in their body, so an `r`-edge
  fires only clauses mentioning `r` (a clause without `r` cannot anchor — a
  guaranteed no-op), and clones a tiny per-role bucket instead of the whole list.

New test `qosat_edge_index_role_chain` drives both paths through a transitive
`r`-chain (`A ⊑ ∃r.B, B ⊑ ∃r.G, r∘r ⊑ r, r(x,z) ⊓ G(z) ⊑ H`) and asserts the
closure is unchanged (`H` derived at `node(A)`). Also removed the per-node
`self.global.clone()` in the node-drain loop (an `O(#nodes × |global|)`
allocation), result-identical.

**Measurement (IBEX, 7581, `KM_HT_FORCE`+`KM_HT_QO`, CB isolated).** This
re-targets the prior diagnosis. With the indexes in, 7581 QoSat saturation still
does **not** converge in 420 s (≈1 GB, CPU-bound). Split drain-loop counters
(`QODRAIN`/`QONODE`/`QOEDGE`) show the run never leaves the **literal**
(concept-clause) propagation phase: one `QODRAIN` tick (2M lit-pops), **zero**
node-loop or edge-loop pops. So the role/edge phase the indexes optimise is not
even reached within budget — 7581's wall is the `O(#seeded-nodes × concept-clause
fires)` volume of saturating one shared node for each of its 72 989 concepts
against 455 583 clauses, upstream of the indexed edge phase. The edge index is
correct and necessary (and a clean win on transitive/role-chain onts that *do*
reach the edge phase), but it is not by itself the 7581 lever. The genuine next
lever is architectural, not more saturation indexing: don't seed + saturate 73k
independent nodes — either extend `elc` to SRIF and route such onts to its
told-subsumer single pass, or make the gate per-concept (saturate only the
concept under test). This is the saturation core Phase 5's lazy per-concept gate
needs; the indexing is a prerequisite, the node-count is the remaining work.

### Two attempts at a Konclude-fast 7581 saturation: per-concept QoSat gate (sound, too slow) + elc inverse edges (fast, UNSOUND, reverted)

Following the edge-index measurement (the all-nodes saturation never reaches the
edge phase on 7581), both architectural options the prior entry named were built
behind flags and measured head-to-head on 7581 (IBEX, CB isolated, gold compare).

**Per-concept QoSat gate (`KM_HT_QO_PC`) — sound, kept, too slow.** Instead of one
global saturation seeding all 72 989 concepts, classify by running one fresh
single-seed QoSat saturation per query concept and reading its subsumers off
(`QoSat::reset` reuses the clause indexes; `complete_roles` re-fires role clauses
for guard-after-edge completeness; `node_cap` raised). Clash ⇒ unsat; sufficient ⇒
exact subsumers; insufficient / `Eq`-head ⇒ defer to fallback (sound). Five unit
tests. **Result: timeout** at 280 s (1.78 GB) — the trace never logs even a
5000-concept progress tick in 200 s (< 25 concepts/s), because per-concept
saturation with no told-subsumer sharing re-walks shared sub-closures (≈ O(N²) on
deep hierarchies). Sound but not the lever; kept gated for the per-concept residue
path it still enables.

**elc inverse-role edges (`KM_ELC_SRIF`) — fast but UNSOUND, reverted.** Recognised
inverse bridges `R(x,y)→S(y,x)` as an inverse map and materialised the reversed
edge `(d,S,c)` for each `(c,R,d)` so the existing backward-link / chain / hierarchy
rules fire on inverse edges. **Result: 66 s but wrong** — the EL saturation derives
`⊤⊑⊥` (declares 7581 inconsistent; gold is consistent, 565 k subsumptions). Root
cause: the EL completion rules (R⊥-edge, NF4, NF7) assume an edge `(c,R,d)` came
from an existential `c ⊑ ∃R.d`; a materialised inverse edge breaks that invariant,
so a `⊥` filler propagates back unsoundly. Naive edge reversal is not a sound
encoding of inverse roles in the shared-context model. **Reverted** (`80001cc`);
sound ELI needs a separate backward-concept propagation channel (Kazakov's
consequence-based Horn-SHIQ calculus) — a larger effort.

**Verdict for 7581: neither wins as built** — the per-concept gate is sound but
too slow, the elc inverse extension is fast but unsound. Both were flag-gated and
off by default, so neither changed corpus behaviour (the per-concept gate stays in,
gated; the elc inverse path is reverted). The real lever remains a sound, shared
(told-subsumer) ELI saturation — efficiency of elc with the soundness of the CB
engine — not a quick variant of either.

### Routing: EL-safe giants retry the repair certificate before CB — recovers 15803 + 6212 (565 → 567)

A head-to-head against ELK and Konclude on our 22 remaining failures (their
recorded `peak_mb`/`wall_s` in the bigsweep) showed that **8** of them ELK
classifies *correctly* (gold-match) in seconds at <3 GB while KM times out — and
two, **15803** and **6212**, are EL-safe **>100 MB giants**. For giants the
`elc`-portfolio is suppressed (racing CB and `elc` concurrently OOMs on a
>100 MB ont), so an EL-safe giant with a non-EL TBox residual (a covering
disjunction here) fell to *bare* `elc` with the certificate **off**, bailed
before saturating, and went to the CB engine — which blows up to 18 GB and times
out at 240 s.

Fix (`orchestrate/mod.rs`): when the bare-`elc` attempt on an EL-safe giant
returns "not EL", **retry `elc` with the repair certificate** (`KM_ELC_CERT=2`),
bounded by the existing `elc_force` wall (100 s) and RSS (14 GB) budgets, before
falling through to CB. When the canonical EL model certifies the residual — an
inert / covering disjunction whose EL answer is already complete, exactly what
ELK computes by dropping the non-EL axioms — `elc` answers soundly in EL time and
memory. The retry runs `elc` alone (sequential), so it does not reintroduce the
concurrent-race OOM the giant suppression avoids; the pure-EL giants (8737,
16744, no residual) solve on the first attempt and are untouched.

Result (full `km classify`, default config, gold = Konclude):
- 15803: 240 s timeout / 18 GB → **20.7 s / 1.26 GB, gold-clean** (2 432 194 subs)
- 6212: 240 s timeout / 18 GB → **76.8 s / 1.24 GB, gold-clean** (243 963 subs)
- 8737 / 16744: unchanged, gold-clean.

The other 6 ELK-correct failures (1603, 12653, 6934, 10908, 16444, 7581) are
`el_rbox_safe=False`: their residual is an uncheckable shape (nominals / inverse)
on which the certificate bails, or it saturates then fails — they remain CB/HT
work. The other 14 of the 22 are cases where ELK only *approximates* (drops the
non-EL axioms and disagrees with gold), so they are not EL-recoverable. Note: on
the genuine EL giants KM now uses **less** memory than ELK (8737: ELK 16.4 GB JVM
vs KM 5.5 GB).

### `elc` ELK backward-link propagation + parse-tree discard — 8737 classify 63s → 22s, peak 9.7GB → 5.5GB

Ported ELK's core EL++ saturation optimisation (the *backward-link propagation*
join, "The Incredible ELK" §5) into `elc`, after mapping the ELK Java source
(`ContextImpl`, `SubsumerBackwardLinkRule`, `SubsumerPropagationRule`,
`PropagationFromExistentialFillerRule`). Both changes are **result-identical**
(113 tests pass; 8737 and 16744 both gold-clean, 0 unsound / 0 incomplete).

**Backward-link propagation (time).** After the filler-label indexing, the
Edge-NF4 rule still rescanned `role_supers(r) × nf4_label[d]` per edge — 4.33B
hashmap *probes* on 8737 (`KM_ELC_PROFILE`), most of them missing. ELK instead
keeps, per context, a *propagation* store keyed by role. `elc` now maintains
`prop[(d, r)] = {E : ∃r.X⊑E, X∈label[d]}` keyed by the **exact** edge role
(role-subsumption is already handled by the pre-existing edge-lift, which
materialises every super-role edge as its own worklist item). A new edge `(c,r,d)`
fires `prop[(d,r)]` with a single hashmap lookup; a new filler-subsumer at `c`
registers its conclusions into `prop[(c,·)]` and fires the exact-role backward
links already at `c`. Each (backward link, propagation) pair fires exactly once,
whichever is created second — the same join ELK's two rules perform. Edge-rule
hashmap lookups collapse from **4.33B to 23M** (one `prop.get` per edge); the old
`(role,filler)->[sup]` index is removed. **8737 classify 63s → 22.4s.**
A propagation-Set dedup (ELK's `propagatedSubsumers_` is a Set) was implemented
and measured: bucket-duplication on 8737 is <0.5%, so it only added a `contains`
cost — reverted.

**Parse-tree discard (memory).** ELK drops the OWL parse tree once axioms are
indexed; `elc` was holding the full input — millions of `JClause`, each owning
`String` IRIs — alive through saturation (the `&[JClause]` borrow kept it pinned
in `run_elc`). `to_nf` already interns the EL part into `nfs` (u32-keyed) and
clones the non-EL part into the residual, so the original clause set is dead from
there. `classify` now takes the clauses **by value** and drops them right after
`to_nf`, before saturation, so the parse tree never coexists with the peak
saturation state. **8737 peak RSS 9.7GB → 5.5GB (−43%)**, 16744 likewise; the
explicit dealloc adds a few seconds of allocator work on the giants (the OS would
otherwise reclaim it at process exit) but the giants sit far under the 240s
timeout, and the headroom matters under the parallel memcap.

### `elc` NF4 saturation: filler-label indexing — 8737 classify 84s → 63s

Profiling `elc` on the EL giant 8737 (the slowest EL-routed ORE ont) showed the
saturation is entirely NF4 (`∃R.D⊑E`): the Edge rule scanned **8.6 billion**
`(super_role, d_super)` probes (the whole subsumer label `sub_super[d]` per edge)
and the Sub rule another **1.68 billion** (`KM_ELC_PROFILE` counters; `perf` is
unavailable on the cluster). NF2/NF7 were zero.

ELK only ever propagates over *existential fillers*, so the label entries that can
fire NF4 are exactly the ones that are NF4 fillers. Two changes, both
**byte-identical** (113 tests, same 409836 subjects on 8737):
- **Edge rule** scans `nf4_label[d]` — the maintained subset of `sub_super[d]`
  whose members are NF4 fillers (`is_filler` set once at init; the subset is
  appended in `add_sub`) — instead of the full label. 8.64B → 4.33B probes (about
  half of 8737's label entries are not fillers).
- **Sub rule** is gated on the new subsumer `d` actually being an NF4 filler
  (`nf4_by_filler`), so the predecessor scan runs only when it can fire, not on
  every Sub item. 1.68B → 505M.

8737 classify **84.3 s → 63.3 s (−25%)**, no result change. (An earlier attempt
that iterated the NF4 axioms per edge instead was *slower* — 8737 has many NF4
axioms per role — and was discarded; the filler-label subset is `⊆ sub_super[d]`,
so it is never worse than the original.) A gated `KM_ELC_PROFILE` prints the
per-rule scan counters.

### EL++ reflexive roles in the EL completion (`elc`) — ELK-guided

Native support for `ReflexiveObjectProperty` in the EL fast path, so ontologies
whose only non-EL RBox feature is reflexivity route to `elc` instead of the CB
engine. Studied ELK's source first (`liveontologies/elk-reasoner`): it normalizes
`Reflexive(R)` to `⊤ ⊑ ∃R.Self` and decomposes that into a self-loop link at every
context (`IndexedObjectHasSelfDecomposition`), letting the ordinary composition /
range rules fire over it.

The port mirrors that semantics by **seeding self-edges**: `to_nf` parses the
frontend's reflexive fact `[] → R(x,x)` into a `reflexive_roles` set (instead of
dumping it to the residual), `build_idx` closes it up the role hierarchy
(`R(x,x) ∧ R⊑S ⟹ S(x,x)`), and `classify_inner` adds a self-edge `(C,R,C)` at
every satisfiable concept node. Every existing rule (NF4 `∃R.D⊑E`, NF7 `R∘S⊑T` in
**both** chain positions, ⊥-edge, role-lift) then fires through the normal
fixpoint — no new rule logic. Because a materialized self-edge feeds NF7 in both
directions, this also covers the reflexive-role-plus-chain case ELK marks only
partially supported.

Routing: `rbox.rs` splits the old shared `"reflexivity"` fence into
`ReflexiveObjectProperty` (now EL-safe, admitted by `el_rbox_safe` /
`el_rbox_safe_relaxed`) and `IrreflexiveObjectProperty` (the `R(x,x)→⊥` constraint,
still fenced to CB).

Validation: 2 new `elc` unit tests (NF4 elimination + reflexive∘chain), full suite
113/113. On the ORE corpus the change is confined to the 13 reflexive ontologies —
4 newly route to `elc` (10326, 13078, 8298, 869). The 2 *scored* ones are
gold-clean **byte-identical** (8298 12200/12200 subs, 869 12224/12224; 0 unsound /
0 incomplete) and now finish in ~0.25 s / 42–65 MB on `elc`. Full-corpus
regression sweep: 0 unsound / 0 incomplete (the 9 remaining reflexive onts keep
their CB routing unchanged).

### HT speed: blocking refinements + the per-build floor — 5303 10s→8s seq, 5s→4s par

Two more refinements to incremental subset blocking (`KM_HT_INCRBLOCK2`), both
result-identical (`KM_HT_INCRBLOCK2_CHECK` asserts equality with the full scan every
pass: 0 mismatches over all ~250k recomputes; subs 238/238; 111 tests):
- backtrack now rebuilds only the affected **suffix** — track the smallest node
  whose subset-blocking label changed (a concept removed, or the node removed) and
  set `i2_lo` to it, instead of forcing a full rebuild (`i2_lo = 0`) every backtrack.
- `i2_recompute` clears/retains only the posting-list slots that ever received an
  entry (`i2_touched` + a dedup bitmap), instead of scanning the whole
  `2x|concepts|` slot table on every pass.

Standalone 5303: 10s → 8s single-threaded, 5s → 4s on 8 threads. Corpus-clean
(5303 + the emelim canaries + sampled normals, 0 unsound / 0 incomplete).

**Two larger levers investigated and ruled out — with data:**
- **"Build the deterministic core once, clone per test"** (HermiT/Konclude-style
  amortization of a query-independent backbone). `KM_HT_COREPROBE` shows the
  empty-seed (⊤+TBox) model of 5303 is a **single node**, and the per-concept
  models (256–3064 nodes) share **0%** of their nodes with it — every model is
  100% derived from its own seed concept, so there is no backbone to amortize.
  Consistent with the HermiT trace (it builds 134 fresh models in 0.94s, ~7ms each,
  with no core-sharing). Not viable here.
- **Cutting the blocking suffix further.** `KM_HT_STATS` reports
  `calls / full_rebuilds / avg_suffix`: 249k recomputes, only 1.3% full rebuilds,
  avg suffix 98 nodes. The suffix is already minimal: subset blocking is a
  *sequential dependency* (`blocked[n]` = does any earlier UNBLOCKED node's label
  contain n's), so a change at position `lo` can flip every later node and
  `[lo..nn]` is the smallest correct recompute. `lo` stays low only because the
  live-disjunction family resolves ⊤-disjunctions on mid-id nodes throughout the
  search — intrinsic, not an artifact. Cutting further would need a different
  blocking *signature* (positive-only — changes which nodes block, an ALC+⊔
  completeness risk) or bitset labels (a large `Ext` refactor), not a cheaper
  recompute.

Net for the live ∀+⊔ family's canonical member: **ore_ont_5303 went from a 207s
timeout to ~4s** (parallel) across this work, all sound + complete + result-identical
to the reference search; HermiT (~0.94s) is ~4x off, the practical floor for the
sound+complete subset blocking that this fragment requires (the cheaper core-hashing
modes explode on it).

### HT speed: incremental ∃-obligations (KM_HT_INCROBLIG) — 5303 10s seq / 5s par

With blocking fixed, profiling (`KM_HT_STATS` now splits the per-test wall into
block / prop / expand) put **72% of the wall in the obligation loop** of
`process_obligations`: it re-scanned EVERY accumulated ∃-obligation on every
saturation pass — 240M iterations on 5303 (~933 per pass), each re-running
`has_rsucc` (an out-edge scan). 92% of obligations sit on blocked nodes (skipped
every pass) and most of the rest were already discharged — pure rescan.

Two parallel structures make the loop incremental:
- `node_obligs[n]` indexes a node's obligation positions, so a pass gathers only
  the obligations of currently-UNBLOCKED nodes (the few that can expand), processed
  in index order so the expansion sequence — and the result — matches the flat scan.
- `oblig_sat[i]` marks an obligation discharged (a successor exists), so even among
  unblocked nodes a satisfied obligation is skipped without an edge rescan. Both are
  pruned/cleared on backtrack (a removed edge can un-satisfy one → re-verify).

Together the obligation loop drops from **240,853,407 to 3,155,424 iterations
(76x)** and from 25.8s to 2.3s (11x). Standalone 5303: **25s → 10s single-threaded,
~5s on 8/16 threads**; RESULT-IDENTICAL (subs 238/238, set byte-identical to the
flat scan), 111 tests pass. From the original 207s timeout this is ~40x; HermiT
(~0.94s) is now ~5x off. Wired ON in `orchestrate/race.rs` `spawn_ht`.

### HT speed: incremental subset blocking (KM_HT_INCRBLOCK2) — 5303 25s seq / ~10s par

Profiling the solved-but-slow 5303 (KM_HT_STATS) located the residual cost
exactly: **blocking recompute was 65% of the per-test wall**, and the models are
only ~313 nodes, 92% blocked — **tighter than HermiT's 690-node models**. So KM
was never over-expanding (it folds more than HermiT); the gap was that
`compute_blocked` rescanned every node on every saturation pass (O(n²) per build).
A battery (all under the EAGER+NEGTRIED+ORD=1 combo) confirmed the only viable
lever: the O(n)-hashed blocking modes (core / pairwise) explode the model
(24684 / 14631 nodes, timeout) — **only subset blocking folds 5303** — and
`KM_HT_WITREUSE` is both incomplete (236 ≠ 238) and slower. So subset blocking had
to be made cheap, not swapped out.

`KM_HT_INCRBLOCK2` does exactly that. Blocking is strictly by an EARLIER node
(`m < n`), so `blocked[n]` depends only on nodes `<= n`. Tracking `i2_lo` = the
smallest node id whose label changed since the last compute (a fresh
`add_concept`, a new node, or a backtrack → 0) means a recompute re-evaluates only
the suffix `i2_lo..nn` in id order — a forward pass equal to a full pass because
every node `< lo` is unchanged. In tableau the frontier (label growth + new nodes)
sits at high ids, so the suffix is usually tiny. The posting lists hold only
**unblocked** candidate blockers (the prior `KM_HT_INCRBLOCK` kept all nodes and
was slower on heavily-blocked models).

**Result-identical** to the full scan: `KM_HT_INCRBLOCK2_CHECK` asserts equality
on every pass — 0 mismatches across all 94 5303 builds, output set byte-identical
(238/238 gold-clean), 111 tests pass. Blocking dropped 65% → 23% of wall;
standalone 5303 **54 s → 25 s single-threaded, 24 s → 10 s on 8 threads, 9 s on
16**. Wired ON in `orchestrate/race.rs` `spawn_ht` alongside the search combo
(respecting env overrides). HermiT is ~0.94 s, so KM is now ~10x off (from
~25-50x); the remaining cost is propagation + expansion (the next frontier).

### ore_ont_5303 SOLVED: sound + complete via HT search discipline + fast blocking

`ore_ont_5303` (the canonical ALC(H) member of the live ∀+⊔ disjunction family,
KM's longest-standing timeout) now classifies **sound + complete** — 238/238
subsumptions byte-equal to Konclude gold, unsound=0 incomplete=0 — for the first
time. Standalone HT: **207 s → 23 s single-threaded → ~10 s on 8 threads.** The
+1 completeness gap (CarbonHydrogenSubstructure ⊑ Hydrocarbon) vanished under the
new search; no frontend / transitivity fix was needed.

The gap was never algorithmic — HermiT classifies all of 5303 in ~0.94 s (traced:
134 SAT tests, ~129 backtracks/test). It was **search discipline that KM had but
left OFF by default**, plus a per-step blocking cost:

- **Search combo (the lever).** `KM_HT_EAGER` (fire ⊤-disjunctions only on
  unblocked nodes) + `KM_HT_NEGTRIED` (HermiT startNextChoice: assert ¬D_di after
  a disjunct clashes so siblings unit-propagate) + `KM_HT_ORD=1` (least-failing-
  first disjunct order). Each is inert alone; together they cut the hard concept
  from 6779 backtracks to **41** (fewer than HermiT). Wired ON for the HT racer in
  `orchestrate/race.rs` (respecting explicit env overrides). Sound + complete:
  these reorder / unit-propagate a complete search, never changing SAT/UNSAT.
  Model-shaping levers (pairwise blocking, trigger absorption, harvest) and
  contrapositive determinism were measured and do NOT crack 5303 — search
  ordering does. Conflict learning / QO / SATFOLD remain dead-ends
  (`docs/5303-ATTEMPTS.md`).

- **Inverted-index subset blocking (per-step cost).** `compute_blocked` mode 1
  (subset, the only mode that folds the family enough) was an O(n²) pairwise scan
  recomputed every propagation pass — ~73 % of the per-test wall. Replaced with a
  posting-list intersection over a **reused, concept-id-indexed flat buffer**
  (`BlockBuf`, no per-call HashMap alloc/hashing): a node is blocked iff it
  appears in the posting list of every concept of an earlier unblocked node, so
  only the rarest concept's list is scanned. **Result-identical** to the O(n²)
  scan (canonical set-equal confirmed; old scan kept under `KM_HT_BLOCK_SLOW`).
  114 s → 23 s on 5303; speeds every HT-routed ont.

- **Parallel classify (`KM_HT_PAR=N`).** `Ht::classify`'s 94 per-concept SAT
  tests + Phase-2 confirmations now run across N worker threads via dynamic
  work-stealing (shared atomic index; each worker builds its own `Ht`, 512 MB
  stack for the deep ORD=1 recursion). Set-identical to sequential (a true
  subsumer is in every model's root label; Phase 2 confirms), no Lean re-cert
  (a scheduling change over the same search). The HT racer defaults `KM_HT_PAR`
  to the core count; `nice` keeps it yielding to CB on CB-winning onts.

No soundness regressions: the emelim canaries (9024/12141/541/11460/15491/4604/
9635) and sampled normals stay gold-clean. Lean re-certification deferred (HT and
`cb_to_ht` are not the certified CB calculus).

### QuasiOrderClassification (KM_HT_QO): validated as a dead-end for the disjunction family, gated OFF

The QO driver (`hypertableau.rs::quasi_order_classify` + `QoSat`, ~1265 lines)
ports the Konclude/HermiT architecture both trace docs identify as the reason
Konclude solves the live ∀+⊔ family in <0.2 s: ONE non-branching global
shared-node saturation (disjunctions parked, never case-split; common-disjunct
consequences harvested deterministically), then sat/unsat + possible-subsumers
read off that single model, with a real residue SAT test ONLY for the
"insufficient" concepts that still anchor open parked disjunctions. The premise
is that ~95% of concepts are decided for free.

**That premise is false for this family — proven, not assumed.** Added the
`KM_HT_QO_TALLY` diagnostic (counts dead/sufficient/insufficient per ont without
bailing on the first residue test). On the target onts (IBEX job 47644078):

- **5303**: global model builds, but `queries=94 dead=3 suff=0 insuff=91`,
  median 17 / max 18 open disjunctions per insufficient concept. EVERY concept
  needs a full branching residue SAT test — zero QO leverage. The 22 global
  ⊤-disjunctions saturate every node, so no concept is ever "sufficient".
- **10702 / 1603 / 12653 / 541**: the non-branching global park-saturation
  itself does not terminate in budget (the ∃-chain / transitive blow-up).

**Validation sweep (job 47644343, 587 onts × 2 arms over `km classify`):** arm
`qo` (default-on) vs arm `noqo` (`KM_NO_HT_QO`) differ on exactly 2 onts — 9024
and 12141 both go gold-clean → incomplete-by-623-subsumptions under QO. QO
recovers 0, regresses 2, introduces 0 new unsoundness, no timeout change. So
default-on QO is a strict −2.

**Decision: gated OFF.** `orchestrate/config.rs` `ht_qo` is now opt-IN
(`KM_HT_QO` env), was opt-out (`KM_NO_HT_QO`); the HT racer reverts to the
validated `Ht::classify` (the 565 gold-clean baseline). All QO code stays behind
the flag, inert by default, kept for the record. Build green, 111 lib tests pass.
Confirms the structural diagnosis (`project_km_5303_diagnosis`,
`project_km_family_diagnosis`): this family needs HermiT-grade absorption +
model-based classification, not the QO harvest. The naive `qo_branch_dfs`
residue search (chronological backtracking, depth-64 guard) is itself strictly
weaker than the `Ht::classify` it falls back to.

### Live-disjunction family (5303): decision-on-demand + contrapositive enrichment (in progress, all gated default-off)

Attack on the live ∀+⊔ family (5303/10702/1603/9540). Two mechanisms added, both
sound clause-level enrichments, gated, default-off (no production impact, no Lean
re-cert until empirically validated):

- **`KM_HT_DOD`** (`tableau.rs`): DPLL-style unit propagation over disjunctions —
  inside the saturation fixpoint, a fired disjunction whose disjuncts are all
  refuted but one asserts that survivor deterministically (sound resolution, dep =
  body ∪ refuting deps), one with all refuted clashes; only ≥2-open disjunctions
  branch. The branch loop also skips refuted disjuncts (deps folded into the
  no-good). `KM_HT_CONTRA` companion: contrapositive Horn clauses for clash clauses
  (`A⊓B⊑⊥ ⇒ A→¬B, B→¬A`) so negative literals propagate and feed unit propagation.

- **Key finding:** `run_json` (`tableau.rs:4482`) routes every ALC(H) KB to
  `hypertableau::Ht`, not the legacy `Tableau`, whenever `KM_HT=1` (always set by
  the orchestrator). The family runs on `Ht`. `Ht` already implements
  decision-on-demand (`eval_disj`: Clash/Unit/Branch) plus `KM_HT_WATCH`,
  `KM_HT_NEGTRIED`, `KM_HT_EAGER`, but a clash clause only `raise_clash`es when
  both literals are present — `Ht` never derives the negatives its unit-propagation
  needs. The contrapositive generator was therefore ported into **`Ht::new`**
  (`hypertableau.rs`, `KM_HT_CONTRA`); the `tableau.rs` DOD/CONTRA remain for the
  out-of-fragment fallback. Build green, 111 lib tests pass.

- **Konclude divergence trace:** `docs/konclude-trace-5303.md` (showboat,
  verify-clean) traces Konclude vs KM from source on 5303: Konclude keeps one
  shared node per concept (not model-size), parks disjunctions and never splits
  (harvesting subsumers via common-disjunct extraction), and SAT-tests only the
  INSUFFICIENT residue (~5%); KM's HT builds a model-sized graph and case-splits.
  CONTRA/DOD make individual disjunctions cheaper but do not change that structural
  blow-up — empirical CONTRA×WATCH/NEGTRIED/EAGER measurement on `Ht` underway.

### Hybrid CB/HT main reasoner: KM_HT hypertableau fills CB's coverage gap (monotone-safe)

The ported HermiT-style hypertableau (`hypertableau.rs`, `KM_HT`, driven via
`cb_to_ht`) is sound on its routable fragment (lossless conversion, no inverse,
no nominals; ALCQ allowed) and classifies central-blow-up / context-explosion
ontologies the CB engine times out on. Verified gold-clean through the *same*
`ore_canon.canonicalize` that produces the gold signatures (`engine/py/ht_check.py`):
HT is sound everywhere (no wrong subsumption) but incomplete on the live
disjunction family, with no structural rule separating its complete from its
incomplete onts — so it can never safely replace a CB answer.

`owl_classify` gains `_spawn_ht` + `_race_cb_vs_ht` (gated `KM_HT_RACE`). CB is
the certified primary on one fewer core; the HT racer (single-threaded, niced)
fills only CB's gap:

* `KM_HT_MODE=fallback` (default): HT's answer is used only on a CB failure /
  `KM_HT_BUDGET_S` timeout — monotone, cannot regress a CB-solved ontology.
* `KM_HT_MODE=race`: first valid finisher wins (faster, but can take an
  HT-incomplete answer).

Full ORE sweep (587 onts, 240 s / 20 GB, gold byte-clean; jobs 47570890 /
47571283 / 47571284): base 558, **fallback 562 (+4: ore_ont_4604 9635 11460
15491, 0 regressions)**, race 559 (+3, 2 regressions). Fallback deployed as the
new main hybrid; race not used. HT engine brought from the `ht-port` branch (3
files; CB core unchanged), all gated/inert by default. See `docs/HYBRID-CB-HT.md`.

### Tableau race un-shadowed by the absorption portfolio + gate relaxation for faithfully-encoded number/inverse/nominals (KM_TAB_FEAT)

Side-by-side ORE benchmark (Konclude/ELK/HermiT/KM, one ont per job, all
reasoners sequential on the same IBEX node, 600 s / 56 GB) showed KM and HermiT
time out on DISJOINT sets: 17 onts time out KM but HermiT solves (the live ∀+⊔
disjunction family), 12 time out HermiT but KM solves (near-Horn throughput).
Attacking the HermiT-solves-KM-does-not set surfaced two issues:

1. **The tableau racer was dead in production.** Routing was
   `if KM_ABSORB_PORTFOLIO and KM_ABSORB: _race_absorbed_plain(...)` /
   `elif KM_TAB_RACE: _race_cb_vs_tableau(...)` — mutually exclusive, and the
   production config sets both absorb flags, so `KM_TAB_RACE` was never reached.
   `_race_cb_vs_tableau` now takes an `engine_run` callable and the absorb
   portfolio runs *inside* the tableau race (the tableau is lazy/niced/
   single-threaded, so it costs ~nothing on onts the engine finishes fast).
2. **The race gate deferred on any number/inverse/nominal flag**, even when
   cb_to_ht encoded the feature losslessly (`dropped==0`, `fenced==[]`).
   `KM_TAB_FEAT` lets the tableau race those when nothing was dropped; soundness
   is validated by gold comparison.

Diagnosis of the 15 gold-having targets (none out-of-fragment — all
`dropped==0, fenced==[]`): with the race reached + gate relaxed, **9635 is
recovered gold-clean** (0.4 s, 159 subsumptions, byte-identical to Konclude
gold). The other 14 still time out at 600 s: KM's cache tableau does not
converge on them (5303/9024: 4–5 M dpll steps, depth 400–760, 1000+ restarts;
1603/12653/15672: number/nominals route to the non-cache careful/expand path
which does not terminate). Closing those needs HermiT-grade tableau search
(anchored/pairwise blocking + dependency-directed backjumping), not a gate flag.

### Cache-tableau convergence control — Glucose dynamic restart + no-good DB reduction (KM_TAB_CONV)

Targets the live `∀ + ⊔` disjunction family (5303, 1603, 12141, 10702, 9540, …):
onts the cache tableau reaches but where the DPLL search *oscillates* and never
converges (5303: ~8 M dpll steps, depth 483, still times out). The machinery
that should help — Luby restarts, VSIDS, phase saving — already existed but was
gated off and "recovered 0", because two things were missing:

1. **Unbounded no-good store.** `learn_cap` defaulted to 2 000 000 and
   `check_nogood` runs on *every* DPLL step over the watch lists, so the store
   itself made each step super-linear. Added **size/quality-based DB reduction**
   (`maybe_reduce`): once the store passes `reduce_at` (30 000), keep all "glue"
   (size ≤ 2) lemmas plus the shortest half and rebuild the watch index. Sound —
   a no-good is an entailed lemma, so dropping it only loses pruning.
2. **Pure-Luby restarts fight the deep ∃-chain cache.** A fixed schedule
   restarts mid-chain and discards the conditional pseudo-model cache, forcing a
   full re-walk. Replaced with a **Glucose dynamic restart** (`note_conflict`):
   restart when the *recent* conflict quality (proxied by reason size, smaller =
   better) is materially worse than the global average — the oscillation
   signature — **unless the search is currently deep** (the blocking rule: it is
   building a large model, so do not throw the deep chain's cache away just as it
   converges). Driven off *every* resolved conflict, tainted or not, so it
   engages on the imposed-disjunction (∀+⊔) family where global learning rarely
   fires; VSIDS activity + phase saving still accumulate across restarts to
   redirect the fresh search.

`KM_TAB_CONV=1` bundles the stack (VSIDS + phase + dynamic restart + reduction);
individual flags (`KM_TAB_DYNRESTART`, `KM_TAB_REDUCE`, `KM_TAB_VSIDS`,
`KM_TAB_PHASE`, tunables `KM_TAB_DYN_MARGIN`/`_BLOCK`/`_WIN`, `KM_TAB_REDUCE_AT`)
still override. All of it is pure search-order / redundant-lemma management — it
cannot change the SAT/UNSAT verdict — so no Lean re-cert. Reached in the pipeline
via the existing `KM_TAB_RACE` cache racer (which inherits the job env). Default
OFF pending the IBEX A/B (disjbase vs disjconv, jobs 47529537/8).

### Auto-route KM_SEQ_ORDER by DISJ_INT — self-selecting Sequoia ordering (+6, net faster, gold-clean)

Commit `9aee987`. Rather than ship `KM_SEQ_ORDER` default-on (which taxes
near-Horn onts — 6423 went 6 s → 126 s forced), the engine now decides per
ontology. `Reasoner::saturate` computes **DISJ_INT** (does any clause head hold
≥ 2 concept literals with ≥ 1 internal/normaliser definer?) and calls
`calc::set_seq_order_auto`, enabling the Sequoia definer ordering only when
DISJ_INT ≥ 1. Env still wins: `KM_SEQ_ORDER` forces on, `KM_NO_SEQ_ORDER` forces
off. Both orderings are complete (named concepts stay mutually incomparable
either way), so the router only selects the faster validated regime — no Lean
delta beyond the definer-ordering follow-up already noted below.

Why DISJ_INT is the right feature (`results/seqorder-routing-20260615.txt`,
full-corpus DISJ_INT × regression wall-deltas): `KM_SEQ_ORDER` only changes
derivation when same-term literals include internal definers, so it helps exactly
the onts with definer-disjunctions and merely adds `is_internal` overhead on the
rest. The rule keeps all +6 recoveries and 7/11 speedups, avoids 27/28 slowdowns
(incl. the 6423 +120 s outlier, DISJ_INT = 0 → off); only 18/540 passers route on.

Confirmed two ways on IBEX (new binary, 83 cargo tests pass):
- **Auto sweep, no env flag** (47522857, 587 onts): **546 MATCH, 0 DIFF**,
  gained the same +6 (5107 6246 6682 10908 11016 11291), lost none — set
  *identical* to forced-on. `results/auto-route-confirm-20260615.txt`.
- **Same-sweep base(forced-off) vs auto A/B** (47523500, 2×587, same nodes):
  base 540 / auto 545 MATCH, both 0 DIFF, lost none; on the 540 both-pass onts
  **auto is net −24.6 % wall** (1968 s vs 2610 s) — it captures the
  disjunction-ont speedups while routing pure-Horn onts off (6423 back to 13 s).
  10908 (~190 s) is borderline: ok in the dedicated sweep at 133 s, timed out
  under the heavier 2-arm contention here; base misses it too, so not a
  regression. `results/auto-route-AB-20260615.txt`.

Combination round 2 (47521666, `results/combo2-20260615.txt`): `seqorder` ×
{corecap, earlyunsat, unitsfirst, split, tabrace} recovered **0** of the 29
hardest remaining onts — the residual (disjunction-convergence + throughput
memory) is algorithmically hard, not reachable by composing these performance
levers. (The memory levers do reduce RSS — corecap/units/split flip 15491/10860
memout→timeout — just not enough to finish.)

Deploy: the auto-routing binary is the deliverable (no config change needed —
auto is the default). ws was down this session, so it was built on IBEX; a
production rollout means deploying the rebuilt binary to unimatrix and a
confirmation sweep.

### KM_SEQ_ORDER regression sweep: +6, zero regressions, gold-clean (deploy gate PASSED)

The portfolio (below) found `KM_SEQ_ORDER` recovers +6 onts. Before deploy, the
open risk was whether the Sequoia ordering regresses any currently-passing ont
(memory had it OOMing 5303). Regression sweep (IBEX job 47520358, 1174 jobs = 2
arms × 587 gold onts, 240 s / 20 GB, `KM_ABSORB=1`; raw =
`results/regress-seqorder-20260615.txt`, script `…-20260615.sbatch`):

| Arm | GOLD=MATCH | NOSIG | DIFF (unsound) |
|---|---|---|---|
| base       | 540 | 47 | 0 |
| seqorder   | 546 | 41 | 0 |

- **GAINED** (seqorder ok, base not): 5107 6246 6682 10908 11016 11291
- **LOST / regressed** (base ok, seqorder not): **NONE**

`KM_SEQ_ORDER` **strictly dominates** base on the full gold corpus: +6, 0
regressions, 0 unsound (every one of its 546 answered onts is byte-identical to
Konclude). 5303 stays a non-ok in both arms (it is in neither MATCH set), so its
known OOM is not a regression. This is the strongest validation available — not
just "no regression vs KM base" but "matches the gold reasoner on every ont it
answers." **Verdict: deploy `KM_SEQ_ORDER=1` in the production config** (expected
554 → 560 on the unimatrix pipeline; production sweep validates at scale).

Soundness/completeness note (`engine/src/calc.rs:481`): `KM_SEQ_ORDER` keys the
literal order on named-vs-auxiliary (Sequoia's `ContextLiteralOrdering`): named /
query concepts stay mutually incomparable at the bottom (the unrestricted
`CompletenessProp` regime the Lean proof certifies, so the forward `⊤→B(x)`
readout remains complete), and only internal definers are totally ordered above
(ordered resolution, resting on Sequoia's published SROIQ-classification
completeness). The definer-ordering restriction is the one piece not covered by
KM's current Lean proof; a follow-up Lean cert of ordered resolution on definers
is warranted, but the corpus-wide gold-clean result is decisive empirical backing.

### Candidate portfolio vs the 36 failing onts (branch `portfolio-candidates`, IBEX)

Method (user-directed): instead of deep-diving one improvement, implement several
gated candidates in one binary and race them — and the existing flags — against
the exact failing set on IBEX, gold-compared at 240 s / 20 GB, then combine the
winners. Self-validating: a wrong arm shows as GOLD=DIFF, never a false win.

Failing set = the 36 onts where Konclude=ok but KM≠ok in sweep 6524 (554 ok / 34
timeout / 2 memout): 10621 10702 10860 10908 11016 11291 11460 1194 12141 12653
14817 15491 15516 15672 15803 1603 2669 3215 4604 4669 5107 5303 541 6246 6682
6934 7246 7499 7581 7914 8737 9024 9540 9635 9663 9724.

New gated candidates (all default OFF/inert; commit `31764e0`):
- `KM_CORE_CAP=K` — cap the central successor core size; excess fact triggers
  ride back as `p→p` hypotheses (completeness-safe), bounding the core-growth
  cascade (the shared root cause of the throughput and disjunction blow-ups).
- `KM_SEED_FROM_SUBSET` — seed a grown-core successor from its (subset-core)
  predecessor-in-the-chain instead of re-deriving; sound, fixpoint-preserving.
- `KM_TODO_UNITS_FIRST` — work off empty-body (fact) clauses first; confluent.
- `KM_EARLY_UNSAT` — clear a context's todo once it derives ⊥ (subsumes all).

Portfolio arms (14): base, corecap4, corecap8, seedsubset, unitsfirst,
earlyunsat, combo(all 4), nocentral(ST), highcap(MSG_CAP=200M), split, seqorder,
notrigskip, threads16, tabrace(cache tableau).

**Results (IBEX job 47519642, all 504 jobs complete; raw =
`results/portfolio-20260615.txt`, script = `results/portfolio-20260615.sbatch`):
9 GOLD=MATCH, 0 GOLD=DIFF (zero unsound across the whole grid), 495 NOSIG.**
6 distinct onts recovered out of 36:

| Ont | Recovered by | Fastest wall | Base |
|---|---|---|---|
| 5107  | seqorder, combo, unitsfirst | 28 s  | timeout |
| 6246  | seqorder (137 s), tabrace (31 s) | 31 s | timeout |
| 6682  | seqorder | 24 s  | timeout |
| 10908 | seqorder | 197 s | timeout |
| 11016 | seqorder | 1 s   | timeout |
| 11291 | seqorder | 1 s   | timeout |

Per-arm recovery count: **seqorder = 6** (all of them), combo = 1, unitsfirst = 1,
tabrace = 1 — and every non-seqorder win is a subset of seqorder's. So the entire
portfolio collapses to a single lever: **`KM_SEQ_ORDER` recovers +6, gold-clean.**
The four new candidate flags (corecap/seedsubset/unitsfirst/earlyunsat) recover
nothing seqorder doesn't, and corecap/highcap/threads16/notrigskip recover 0.
`seqorder` also flips 2 base memouts into the converged set (base: 2 memout / 33
timeout → seqorder: 1 memout / 6 ok / 29 timeout), so total-order resolution both
bounds memory and converges faster on these. 11016/11291 finish in 1 s, meaning
base's per-context ordering was the entire problem there, not the instance size.

`KM_SEQ_ORDER` overturns the prior 6246 verdict (memory had it as a "genuine
timeout, not recoverable"; total-order resolution cracks it at 137 s, 31 s under
the cache-tableau race). 8737 reports STATUS=error in every arm — it is a giant
absent from the IBEX corpus (already `ok` in production via `elc`), not a failure.

Caveat before deploy: `KM_SEQ_ORDER` is known to OOM 5303, so it cannot go
default-on without a regression check on the 554 currently-passing onts. Next step
is a full-corpus sweep with `KM_SEQ_ORDER=1`; if it regresses passers it ships as a
router/race (run on the failing tail only, additive-by-construction like
`KM_ABSORB_PORTFOLIO`), otherwise default-on. Either way the +6 are sound (every
recovery is byte-identical to Konclude gold).

Why this replaced the shelved single-candidate work: the shared-successor parallel
strategy was **measurement-falsified** this session (`KM_CTXSPLIT` diagnostic,
commit `2674a11`). On 9663 the clause arena is only 6–8 % of memory; ~half is
per-context `head_indexes` across ~79k contexts, and single-thread central exceeds
20 GB at convergence (115 GB at 4M messages), so query parallelism only multiplies
per-context memory. The cluster is intrinsic-scale, not parallelizable-duplication.

### Absorption portfolio deployed + validated: sequential plain/absorbed (545 → 554, gold-clean)

`KM_ABSORB_PORTFOLIO` (in `owl_classify.py`, gated; enabled in the `kmpf` sbatch
alongside `KM_ABSORB=1` and the `ofn-absorb` frontend) runs the absorbed clause
set as the primary and, *sequentially* (one engine resident at a time, to respect
the 20 GB memcap), probes the plain clause set first for `KM_ABSORB_PROBE_S` (8 s)
to catch the absorption-cliff cases before committing to the absorbed run. A
concurrent race is ruled out by memory: legitimate absorbed runs already reach
~18 GB, so a second engine alongside blows the cap (the concurrent variant caused
7 memouts in cancelled sweep 6338).

Validation sweep **6524** (sequential portfolio) vs the 545 baseline:
**554 ok / 34 timeout / 2 memout**, gold table **554 agree / 0 unsound /
0 incomplete / 0 both** — fully gold-clean at corpus scale. **+10 recovered**
(1340, 2397, 3905, 4205, 6212, 7775, 12698, 14450, 16303, **16444**); **−1
regressed: ore_ont_6246**. Net **+9 (545 → 554)**.

6246 is the lone miss and the gap to the intended +11/−0: its plain run is
sub-second on an idle node but pathologically slow under contention, and the
8 s wall-clock probe landed on a busy node (node007), missed, took the absorbed
path, and blew to 18.6 GB / timeout. The probe is wall-clock so it is node-load
sensitive; the clean fix is a cheap static plain/absorbed router (decide from the
clause set, not from a timed race) rather than widening `KM_ABSORB_PROBE_S` (which
would delay the genuinely absorbed-only onts). The 2 memouts (10860, 15491) were
already not-ok in the baseline, not regressions. The portfolio is verdict-equal by
construction (absorption is equisatisfiable; whichever clause set answers first is
sound + complete).

### Frontend absorption: polarity-gated definitional clausification (+10 ORE coverage, 545 → 555)

`KM_ABSORB` (default off) extends the clausifier's polarity pre-pass to And/Or/Not
definers and emits only the definition direction the concept's polarity needs
(Plaisted-Greenbaum): `Q → C` only when C occurs positively, `C → Q` only when it
occurs negatively; unseen concepts (e.g. ABox assertions) keep both directions.
This drops, at the source, the unguarded excluded-middle disjunction `⊤ → Q ∨ A`
emitted for every reified negation that never appears on a subclass LHS (the
disjointness idiom `X ⊑ ¬A`), and turns an LHS disjunction into Horn rules.

Measured (`ofn`, on vs off): ore_ont_1340 104 → 0 disjunctive heads, 3905 106 → 0,
14450 106 → 0 (fully Horn); residual disjunctions are genuine RHS disjunctions and
are untouched (5303 38 → 37, so 5303 still times out — needs CB ordered resolution).

Validation sweep 6304 (`KM_ABSORB=1`, tableau race off) vs the 545 baseline:
**555 ok / 34 timeout / 1 memout**, gold table **0 unsound / 0 incomplete / 0 both**
(verdict-preserving confirmed at corpus scale — the synthetic definers are never
query targets, so their polarities are fixed by the ontology). 11 recoveries
(1340, 3905, 14450, 12698, 16303, **16444 the long-standing memout**, 2397, 4205,
6212, 7775, **8737 a giant**); 1 regression: **ore_ont_6246** goes 0.35 s/78 MB →
18.5 GB OOM/timeout — dropping the (PG-redundant) AND def directions on a DOLCE-
style covering+disjointness TBox perturbs the CB engine into a blow-up. Net +10.
Kept gated pending a safe deployment (absorbed/plain portfolio for +11/-0, or a
fix for the 6246 cliff) — see memory `project_km_absorption`.

### Tableau Tier-1 search heuristics: VSIDS + phase saving + Luby restarts (gated; not a coverage win)

`KM_TAB_VSIDS` / `KM_TAB_PHASE` / `KM_TAB_RESTART` (all default off) add CDCL-style
search control to the label-caching tableau's per-node DPLL. Pure decision-order /
redundancy, so no Lean re-cert; 2313 stays byte-identical under every combination.
Empirically they reduce distinct-seed count ~26 % and learn 5× more no-goods on
ore_ont_5303 but recover none of the 7 cache-eligible ORE timeouts: their wall is
the ∃-chain seed-space explosion (depth ~483, tens of thousands of incomparable
successor labels), not per-node propositional search. Kept as gated infrastructure;
the live-disjunction family needs disjunction reduction at the source (absorption,
above) or CB-side ordered resolution.

### CB-vs-tableau race hardened: provably zero-cost to the engine

`_race_cb_vs_tableau` now starts the engine first at full cores and spawns the
tableau lazily off the critical path (`KM_TAB_RACE_DELAY`, default 30 s) at
`nice 19`, with robust cancellation. An ontology the engine finishes within the
delay pays zero tableau cost. (A faithful same-node/same-binary A/B showed the
prior race was already net-neutral on the sweep, exonerating it as a regression
cause; the apparent 18-ont drop vs the stale 564 baseline was the Jun 12-13
correctness commits, not the race.)

### Direction C cache path: taint-aware learning + incremental pruning + pseudo-model caching (recovers ore_ont_2313)

Profiling the label-caching tableau (`KM_TAB_CACHE`) on the live-∀+⊔ family
(ore_ont_5303) pinned the wall: a deep ∃-chain (∃-depth 96 → 226+) of
*incomparable* node labels, where (a) no-good learning was disabled at exactly
those nodes and (b) blocking-SAT seeds were recomputed endlessly (cache stuck
~200 against 100k+ seed evaluations). Four sound, gated optimisations, validated
set-identical to the trusted `expand_inc` on 19 in-fragment ORE ontologies (0
wrong answers, 0 panics); commits `dbb474a`, `8231873`.

- **Taint-aware global learning at imposed nodes** (the key algorithmic lever).
  Learning was gated to `key.imposed.is_empty()`, which switches it off at every
  deep ∃-chain node (all carry imposed universals). Replaced with per-literal
  taint propagation in `close_dep`: a derived literal is tainted iff its
  derivation used an imposed (node-specific) clause, and a conflict is learned
  globally iff its whole derivation is untainted (provable from the TBox alone) —
  sound even under imposed constraints, which a coarse "any imposed fired" flag
  would wrongly forbid. `succ_conflict` and `first_disj` report taint;
  `local_search` threads it. On 5303 this breaks the hard-stop at ∃-depth 96 and
  the search advances to 144+ (no-goods 166 → 800+).

- **Pseudo-model caching of blocking-SAT verdicts.** The `used: bool` blocking
  flag became `block_level: usize` = the shallowest stack level any blocking in a
  subtree relied on (`blocked()` returns the deepest blocking ancestor for
  locality). (1) *Self-contained*: a subtree that only blocks on itself-or-deeper
  (`block_level >= own level`) is a self-contained finite cyclic model → cache
  unconditionally. (2) *Conditional*: a seed satisfiable only by blocking on an
  ancestor at level i is cached in a `cond` map valid while that ancestor is on
  the stack (purged on its pop) — every lookup then happens inside the ancestor's
  subtree, which is discarded if it fails. This caches the deep chain whose
  verdicts depend on a stable shallow ancestor, turning re-search into hits.

- **Incremental eager ∃-pruning** (`KM_TAB_EAGER`, default on). The eager
  successor check ran ~59 `build_succ` calls at every one of >1M DPLL steps. A
  step adding no *trigger* literal (one that can change an obligation or fire a
  universal) leaves obligations + successors unchanged, so the rescan is skipped.
  Plus a per-role uni index for `build_succ`. ~1.77x throughput on 5303.

- **Disjunct ordering** (`KM_TAB_ORD`, default 0 = program order). Floats vacuous
  `∀r.L` markers first (`ORD=1`). Measured: program order beats the shallow-model
  bias on 5303 (depth 363 vs 96); pure reordering, set-identical.

**Results (cache path, ord=0):** RECOVERS **ore_ont_2313** — a live-∀+⊔ family
timeout — finishing with 13967 subsumptions **byte-identical to the Konclude gold
signature**. Recovers ore_ont_2066 and ore_ont_5089 (previously timed out on the
cache path). 5303 runs ~3x faster (2.5M → 8M DPLL/280s, ∃-depth 483) but still
does not finish — the search accelerates and deepens yet oscillates rather than
converging (590k no-good hits); 1603, 12141 also still time out. The family is
not fully closed within budget: the residue is Konclude-grade search control, not
a missing soundness/completeness mechanism. Diagnostics: `KM_TAB_HB`,
dpll/depth/cache counters. `engine/py/tab_emit.py` emits a cached TInput from an
ontology for standalone cache-path tuning.

### Direction C: label-caching (global-caching) tableau (`KM_TAB_CACHE`, gated OFF)

A from-scratch rewrite of the tableau's non-careful (ALCH, no inverse / number /
nominals) path from a single global DFS over one shared completion graph into a
**label-keyed global-caching** decision procedure (Goré–Nguyen). The motivating
fact: in ALCH without inverse roles, a node's satisfiability depends ONLY on its
concept label, so a label proven (un)satisfiable stays so wherever it recurs — the
result caches across every node AND across every classify query. `expand_inc`'s
no-good learning could not exploit this because its no-goods were over node-
INSTANCE `(node, literal)` decisions (commit 16ec50b, measured insufficient).

Design (in `tableau.rs`, behind `KM_TAB_CACHE`; `build_cprog` falls back to the
complete `expand_inc` on any clause outside the recognised shapes, so soundness is
never at risk):
- **Two levels.** Level 1 (per node, transient, never cached): a propositional
  DPLL over the node's disjunctions. Level 2 (cached across nodes + queries): the
  satisfiability of each ∃-successor *seed* (its filler plus the universals
  propagated onto it), keyed by `CKey`.
- **`∃r.C ⊑ D` internalisation.** The someValuesFrom-on-LHS clauses
  `r(x,y) ∧ C(y) → D(x)` (82 of them in ore_ont_5303) become the disjunction
  `D ⊔ ∀r.¬C`, the universal disjunct represented as a synthetic marker concept
  carrying a `Uni` that pushes `¬C` to the node's r-successors when chosen.
- **Sound cycle handling without an SCC pass.** UNSAT seeds are always cached
  (sound: unsat under optimistic blocking ⇒ unsat in every context); a SAT verdict
  is cached only when its witness used no on-stack blocking (`used == false`) — a
  genuine finite model, sound to reuse anywhere.
- **Eager ∃-pruning** (every active obligation's successor checked at every DPLL
  level, sound because a partial node-set imposes fewer universals), **subset
  blocking** over the ancestor stack (sound GFP blocking for ALCH; Dickson's lemma
  bounds every ∃-chain), and a **semi-naive indexed `close()`** (Horn closure fires
  only clauses a newly-derived literal triggers; ~50× over the naive scan).

**Correctness validated:** 16 tableau unit tests pass through the cache path; on 5
real ALCH ORE ontologies (ore_ont_11949/9509/10309/13503/2485) the cached
classification is **set-identical** to the validated `expand_inc` output (132 / 81
/ 6 / 113 / 1 subsumptions). No regression to the default build (66 + 16 tests).

**Conflict-directed backjumping + label-based no-good learning (per-node DPLL).**
`local_search` now tracks, for every derived literal, the set of source concept
literals (seed-base + disjunction decisions) it depends on (`cdep`, maintained on a
trail so branches undo in place instead of cloning the working set). On a clash —
complementary pair, ⊥-clause, or an unsatisfiable ∃-successor — the conflict is
that source-literal reason. When asserting a disjunct `d` yields a conflict not
mentioning `d`, the choice was irrelevant and the search backjumps past the whole
disjunction. When every disjunct of a node fails, the resolved conflict
(`guard ∪ ⋃(conf_i \ {d_i})`) is learned as a no-good. Crucially these no-goods
range over CONCEPT LITERALS, not node instances, so one no-good prunes EVERY node
whose label contains it — the cross-node generalisation the earlier
`(node, literal)` learning (16ec50b) lacked. Learning is restricted to nodes with
no imposed clauses (where the derivation is node-independent), keeping it sound.
Validated: 16 tableau tests + the 5 real ALCH onts still set-identical to
`expand_inc` (a trail-undo bug that briefly produced unsound extra subsumptions on
ore_ont_9509/10309 was caught by the A/B and fixed — a clashing literal must be
trailed before the early return). Measured on ore_ont_5303: learning fires hard
(134 no-goods, ~9.7k prune hits) yet the ontology still times out — the search
backtracks through an exponential per-node region at ∃-depth ~226 that learning
prunes but does not eliminate, and smaller no-goods (`KM_TAB_LEARN_MAX=64`)
generalise better than large ones. The production-stack optimisations are in place
and sound but do not close this family within budget; this is the 5th technique to
reach the same wall.

**Recovery of the live-`∀ + ⊔` timeout family = 0** (honest negative result). On
ore_ont_5303 the checker builds a genuinely deep ∃-chain (>1000 successors) whose
labels are pairwise incomparable, so subset blocking rarely fires — the same
deep-model wall that already makes 5303 a timeout for `expand_inc` itself. The
per-node propositional search (120 disjunctions on the ⊤ node) is partly tamed by
eager pruning but the combined depth × width is not. On three other ALCH onts
(8937 / 1420 / 4856) the cached path is *slower* than `expand_inc` (deep-recursion
+ eager re-checking underperform the global DFS), so it is not a strict win and
stays gated OFF. The architecture is sound, validated, and the foundation for a
caching tableau; closing the gap to Konclude on this family needs the full
production-reasoner stack (dependency-directed backjumping + label-based learning
inside the per-node DPLL, smarter blocking), a multi-session engineering effort
rather than an algorithmic gap. This is the 4th approach (CB resolution, CB
splitting, tableau no-good learning, caching tableau) to hit the same wall on this
family; KM stays sound + complete on everything it finishes.

### Direction B: disjunction case-splitting (`KM_SPLIT`, increment 1, gated OFF)

The algorithmic lever for the live-`∀ + ⊔` timeout family (the largest timeout
group, out of parallelism's reach). Design: docs/DISJUNCTION-SPLITTING.md.
Instead of unrestricted resolution on incomparable disjunctions (the blow-up),
classify a query by semantic case splitting: branch on a derived fact-disjunction
`⊤ → l1(x) ∨ … ∨ lk(x)`, intersect the forced units over the open branches, and
close a branch on `⊥`. Each branch runs the tame ordered-resolution closure (a
per-thread `BRANCH_ORDERED` total order); the fallback runs the complete
(unordered) regime — ordered resolution alone is incomplete (the `KM_ORDERED_ALL`
verdict), so the two must be separated per-run, not by a process-global flag.

`classify_assume(query, assume)` runs a branch closure on a fresh engine
(isolation by construction) and reads `ClosureFacts` (forced units, split-point
disjunctions, `⊥`). A **conservative completeness guard** sets `foreign` →
fall back to the complete default engine whenever ANY context holds a
disjunction that is not a query-context body-empty concept-on-x fact-disjunction
(a conditional/role/equality disjunction, or a successor-context disjunction):
the total order could hide a forced unit there and the propositional-on-x driver
does not split it. So `KM_SPLIT` is **SOUND + COMPLETE on every ontology** — the
recovered fragment is the queries whose only nondeterminism is concept
disjunctions on `x` over Horn successors; everything else falls back.

Validation (66+16 tests; A/B vs the default engine):
- **14/14 byte-identical** on the finishable small onts (the guard only ever
  increases fallback, and fallback == default).
- **ore_ont_13383: identical**, where split fully classifies all 368 queries
  with **0 fallback** — the splitting itself (not the fallback) yields the
  correct complete answer on a real named-disjunction ontology.
- Honest correction: an earlier pre-fix run appeared to "solve" 5107 — that was
  the incomplete ordered *fallback* finishing fast with WRONG answers; with the
  per-run ordering fix 5107 correctly falls back to the complete engine.
- **Recovery on the disjunction timeout family: 0** (5107, 5303, 12698, 2313,
  …). Their hard nondeterminism is at the successor/conditional level, so they
  either fall back (→ complete-engine timeout) or the per-branch closure itself
  times out. Recovering them needs **structural splitting** — splitting
  disjunctions inside successor contexts and conditional disjunctions, with
  branch-scoped messaging — which is increment 2 (the genuinely multi-session,
  Lean-cert'd core). Direction A (ordered + selection + residue readout) layers
  on increment 2.

Increment 1 lands the correct splitting machinery and the soundness+completeness
guard; it is a no-op on the benchmark (falls back on the hard family) and stays
default OFF.

**Increment 2 — structural splitting (`d57e30d`).** Generalises the split from
query-root fact-disjunctions to disjunctions in ANY context, keyed by the
context's core (`branch_decisions: core → assumed disjunct facts`, seeded when a
context with that core is created; cores are deterministic given the decisions,
so the same successor context arises and gets the same seed across the
fresh-engine-per-branch runs). This is how a disjunct is assumed in a SUCCESSOR
context — the structure the live-`∀ + ⊔` family actually has (`A ⊑ ∀R.(C ⊔ D)`).
SOUNDNESS guard `chain_unique_contexts`: split only contexts reachable from a
root by single successor edges — the central strategy merges contexts by core,
so a context reached by ≥2 edges represents successors that could pick disjuncts
independently and a shared split would force them to agree (unsound). Everything
else (non-chain-unique, role/eq/non-central disjunctions) falls back.

Validation: 66+16 tests; **14/14 byte-identical** A/B; 13383 identical. SOUND.
Recovery on the timeout family: still **0**.

**Increment 3 — unit-propagation mode + the measured ceiling of lazy splitting
(`079da53`).** The Hyper resolvent builder, under the split regime, suppresses
resolvents that combine ≥2 derived disjunctions (the fact×fact multiplication),
so a branch's per-context clause population stays tame and exhaustive splitting
recovers the suppressed derivations. Sound (14/14 A/B; 13383 identical, full
split / 0 fallback). But it still recovers **0** of the timeout family, and the
node-rate + fixpoint instrumentation shows WHY — two failure modes, both fatal
to *lazy* splitting (saturate to fixpoint, THEN read + split disjunctions):
- 5303/5107/12698/10702: the per-query closure (saturate + inter-context
  message fixpoint) does not complete (<100 split nodes, no progress markers in
  40 s) — the blow-up is in computing the closure ITSELF, before any disjunction
  is available to split. Splitting on top of a closure that never finishes can't
  help.
- 2313: the split loop completes but all 1688 queries fall back (disjunctions in
  non-chain-unique contexts, which the soundness guard refuses to share-split) →
  the complete default engine then times out.

Conclusion: recovery requires splitting **interleaved** with saturation (decide
before the closure explodes) — an incremental decision trail with backtracking —
which fights the monotone append-only arena (retraction). That architecture is a
hypertableau, and the measurement **tilts the Direction C verdict toward a
dedicated/standalone tableau** rather than retrofitting interleaved retraction
into the CB engine. Increments 1–3 land the sound splitting machinery + the
unit-prop component a future interleaved version reuses; all gated `KM_SPLIT`
OFF, no benchmark change.

### Parallel-speed work: dynamic query scheduler (landed) + the parallelism ceiling

Speed push aimed at the timeout tail, learning from Konclude (whose two main
speed sources are aggressive parallelism + lazy tableau-with-caching for
nondeterminism). Findings, with a thread-scaling probe (job 6227, node005,
KM_THREADS ∈ {1,8,16}, 480 s / 220 GB) partitioning the failures by family:

**Lever 1 — dynamic work-stealing query scheduler (LANDED, `7bc8611`).**
The old parallel path split the named concepts into `threads` static
contiguous chunks, one fixed engine each; when the hard query concepts cluster
in the named ordering they land in one chunk and serialise the whole run
(measured on ore_ont_12141). Replaced with `threads` long-lived engines
draining a shared atomic cursor in guided-size grabs (large early for low
contention + intra-engine cross-query context sharing, shrinking to 1 at the
tail), so a finished worker steals the next. Pure scheduling change — each
engine is independent and a query's subsumers don't depend on co-classified
queries (run_for contract), so the partition-independent union is confluent:
no Lean re-cert. `KM_STATIC_SCHED` restores the old path for A/B. Validated:
66+16 cargo tests; subsumptions byte-identical across KM_THREADS=1 / dynamic-8
/ static-8 on 8 onts (16461, 16076, 7270, 7482, 10019, 8169, 13018, 9635).
Also split `apply_pred` into `pred_payload` (reads only the immutable sender)
+ `apply_pred_payload` (mutates only the target) — output-neutral, isolates
the one sender/target aliasing read as a precondition for a future parallel
message-apply phase.

**Lever 2 — intra-saturation parallelism: scoped, then shelved as low-ROI.**
Konclude parallelises the saturation itself; KM only parallelises *across
queries*. The missing piece (concurrent context saturation) is the only lever
for "one giant saturation" onts that query-parallelism can't split. But two
facts make it a poor investment under the real benchmark limits (240 s, 20 GB):

- *Cost:* the saturation core touches the shared arena + intern tables
  directly across ~70 sites (only 6 are the `&[ContextClause]` slice
  signatures; the rest are `saturate`/`add_clause`/`hyper`/`intern_cc`/
  `cc_find` reaching `self.cc_arena` directly). True parallel saturation means
  parameterising that whole core over an arena+intern abstraction (each worker
  sees committed-global ++ its-own-new clauses) or a locked concurrent context
  graph — a multi-session, Lean-adjacent refactor needing iterative validation.
- *Payoff (probe 6227 + memory facts):* the speed-recoverable set is ~1 ont.
  - 12141 + the disjunction family: timeout at 1/8/16 threads, and 8/16
    threads **explode to ~204 GB** — parallelism-resistant *and*
    memory-explosive; needs the algorithmic lever (ordered resolution /
    tableau / BCP), not threads.
  - 16444 (59 GB) and 9724/GALEN (27 GB): both **over the 20 GB memcap**, so
    they are memouts regardless of speed.
  - 16303: th=1 and th=16 both timeout at an **identical 4.93 GB peak** — the
    textbook family-B signature (query-parallelism completely inert; one giant
    saturation). The lone genuine intra-saturation target: fits the memcap but
    needs ~8–10× scaling to clear 240 s.

  Conclusion: bank Lever 1; **shelve Lever 2** (multi-session core refactor,
  memory-neutral, reaches ~1 ont); the productive next lever is the
  disjunction family's algorithmic fix (the largest timeout group, provably
  out of parallelism's reach).

### Sweep 6016: the first fully clean correctness table (datatypes included)

Full sweep with the datatype layer + chain-domain default + Phase-2 engine
(binaries `ofn-dt` / `kobayashi-marust-p2`): **545 ok / 45 timeout /
1 memout; vs Konclude gold 545 agree / 0 incomplete / 0 unsound /
0 both-disagree** — every completed ontology byte-equal to gold, with no
exclusions (ore_ont_6999's datatype gap closed). Zero status regressions vs
sweep 5976 and two recoveries (ore_ont_2397, ore_ont_8737 timeout → ok), so
the new clauses cost nothing net. The 3524 giant's stdout-runaway recurred
mid-sweep and is now fixed at the root (`KM_EMIT_CLAUSES` gating below).

### Nominal-mode r-Pred announcement guard (10594 livelock fix)

The Phase-2 per-source r-Pred path let body-empty ground clauses pass the
body-discharge check vacuously, spraying every ground fact to every context
with a root edge (ore_ont_10594, ~1900 individuals: 3.5M+ Pred messages,
ok → timeout under `KM_NOMINALS`). Restored the announcement guard (an edge
per mentioned individual) with additional nominals (id ≥ `nom_base`) exempt —
they are exactly what Nom conclusions carry and what no context can have
announced. 10594: timeout → 192 s, now faster than the Phase-1 engine on the
same host with identical published output.

### Datatypes: data-property axioms + a concrete-domain oracle

Closes the datatype gap (the last incomplete-vs-gold ontology): ore_ont_6999
is now byte-equal to gold — `Distortion_Type_Affine ⊑ =2 affc2` with
`Functional(affc2)` is correctly unsatisfiable. Two layers, both frontend
(no calculus change, no Lean re-cert needed):

1. **Axiom translation** (`parse.rs`; previously every `Data*` axiom was
   dropped): functionality → role functionality, sub/equivalent/disjoint
   data properties → the role counterparts, ranges → `∀p.__dt__D`,
   `DatatypeDefinition` → concept equivalence. Unqualified data cardinalities
   now count ALL successors (`⊤` filler — the old `__dt__val` filler made
   `≤ n` blind to `DataHasValue` successors). Complex ranges are keyed by
   canonical text (one shared `__dt__opaque` could invent subsumptions
   between different facet restrictions) and typed literals are re-glued
   with their `^^datatype` / `@lang` suffix (the tokeniser splits them off,
   which collapsed same-lexical different-type values).
2. **Pairwise oracle** (`frontend/datatypes.rs`): for the `__dt__` concepts
   occurring in the clause set, decide — per the OWL 2 datatype map — value
   membership, value (in)equality (exact rationals across the decimal tower
   and dyadic float/double, strings, booleans), range subsumption and
   disjointness (integer-tower bounds, string-family tower, partition
   disjointness, interval separation), and finite covers (boolean, DataOneOf,
   small integer intervals): `__dt__D(x) → ⋁ __dt__val__vᵢ(x)`, which with
   value disjointness gives finite-range counting through the engine's
   ordinary equality reasoning. Every relation is emitted as a plain concept
   clause; unknown decisions emit nothing (the old sound abstraction).
   `KM_NO_DATATYPES` disables the oracle pass for A/B.

82 cargo tests pass (5 new oracle tests). Full-corpus validation sweep
pending; built and validated on unimatrix while ws was unreachable.

### Nominals Phase 2+3: Join, r-Succ (*), the Nom rule, and Lean certification

Completes the ALCHOIQ calculus implementation behind `KM_NOMINALS` (Table 3 of
arXiv:1805.01396; design + status in `docs/NOMINALS-CB.md`):

- **Nom** (additional nominals): in the ground context, a hyper-match with
  `σ(x) = o` whose head a-equalities instantiate to `y ≈ y` / `y ≈ f(o')` no
  longer drops them as tautologies (the exact O+I+Q incompleteness) but
  replaces them with `⋁_{k} y ≈ o'_k` over fresh interned additional nominals.
  The disjunction width is `K + K''` (`K + 1` = max neighbour-variable index,
  `K''` = distinct pinned `f(o')` terms): the certified covering bound is the
  sum, and the paper's bare-`K` statement is too narrow whenever `K'' > K`.
  Budgeted (`KM_NOM_BUDGET`, default 4096) with an explicit incompleteness
  warning on exhaustion. Two enabling fixes: the ground context's Hyper now
  considers the side clause at non-side body positions (given-clause
  semantics — provably redundant elsewhere, the Nom trigger here), and the
  symmetric-group strict pruning admits the equal-`y` assignment there.
- **Join**: in-context resolution on ground atoms (cases 1+2 via new
  ground-body/bridge indexes and a `pred_local` refire on ground maximal
  heads; case 3 = provider over `x` + an `x ≈ o` bridge, fired from all three
  arrival orders).
- **r-Succ condition (*)**: pushes are blocked when a subsuming-modulo-merge
  clause shows the element may itself be a nominal (defer to equality
  reasoning).
- **r-Pred pipeline**: per-atom multi-edge discharge (different `A_i` over
  different individual-labelled edges of one source), verbatim `C_i` copies,
  and no edge requirement for head individuals — the old head filter made
  every Nom conclusion undeliverable.
- **Lean (Phase 3)**: `lean/ContextCalculus/Nominals.lean` (sorry-free)
  certifies soundness of all four rules and the grounded substitutions;
  `nom_cover`/`nom_sound` prove the covering bound and the
  conservative-extension soundness of Nom (the interpretation of the fresh
  constants is constructed).
- `owl_classify._run_engine`: the stdin writer thread raced
  `communicate()`'s flush on fast engine exits (`ValueError: I/O operation on
  closed file`); `communicate(input=…)` now owns the write.

Validation: 61 + 16 cargo tests (4 new engine-level tests incl. the paper's
Example 3 and a no-counting negative control); all six pipeline probes match
HermiT (`nom1`, `nom2`, `nom_dl8`, `nom_neg1`, `nom_unsat`,
`nom_oiq_funct` — the last is Example 3 as OWL, the first KM result that
*requires* additional nominals). Inert without individuals: every new code
path is gated on the ground context / ground atoms, and without `KM_NOMINALS`
the reasoner drops individual clauses, so SRIQ-fragment output is unchanged.
60-ontology corpus A/B with this binary pending.

### Chain-domain recognition validated corpus-wide; now DEFAULT ON

Full sweep 5976 (`KM_CHAIN_DOMAIN=1`, all 591 gold-comparable ontologies):
**543 ok / 46 timeout / 2 memout; vs Konclude gold 542 agree / 0 unsound /
1 incomplete / 0 both-disagree.** The single incomplete is `ore_ont_6999`,
whose one missing subsumption (`Distortion_Type_Affine`) is the known
*datatype* gap (identical in the old config) — within SROIQ-minus-datatypes
the corpus is now **0 unsound, 0 incomplete vs gold**, the first fully clean
correctness table. `ore_ont_11745` confirmed fixed at full scale (ok,
unsat=1592, gold-equal).

Landing: the pass is now default-on (`KM_NO_CHAIN_DOMAIN` opts out for A/B
debugging), per the completeness mandate and the disjunction-ordering
precedent. Cost vs the 5941 baseline: `ore_ont_2313` and `ore_ont_8737`
(chain-heavy; 8737 ran ~206 s before) go ok → timeout — honest resource
limits, not silent approximation.

### Frontend: role-chain recognition for pure-domain consumers (`KM_CHAIN_DOMAIN`)

Recovers `ore_ont_11745`, the last unsound-vs-gold ontology: with the flag,
full 11745 is byte-identical to Konclude gold (438277 subsumptions, 1592
unsatisfiable classes, `GO_0008046` correctly unsatisfiable). It was a genuine
unsat under-detection (HermiT-confirmed; an 18-axiom witness reduced from a
STAR module), not the parallel-pipeline artifact earlier assumed.

Root cause: `chain_clauses` / `transitivity_clauses` run inside `augment`
(frontend pass 1) and recognise a chain `R∘S⊑T` only when a TBox consumer
carries a concept on the chain target. A *pure-domain* consumer
`T(x,y) → D(x)` (from `ObjectPropertyDomain(T, D)`) has no such concept and is
added only in pass 2, so the chain feeding a domain restriction was never
recognised. In 11745, `GO_0008046` is a molecular_function (a `SubClassOf`
chain) and, via a transitive `part_of` chain plus `part_of∘ricdo⊑ridpo` with
`domain(ridpo) = biological_process`, also a biological_process; the two are
disjoint, so the class is unsatisfiable. KM reached the chain filler
(`__trans__part_of__GO_0048856`) but never composed it with the domain
restriction, so it missed the clash and emitted the class's ordinary
superclasses (scored as unsound, though KM never derived anything false).

Fix (gated by `KM_CHAIN_DOMAIN` while validated corpus-wide; reordering the
passes is blocked by the `reg.short` name-assignment byte-identity invariant):
`augment` now also returns the detected `ChainInfo`, and after
`domain_range_clauses` are built, `domain_consumer_chain_clauses` emits the
missing recognitions for pure-domain consumers of chain targets — the
`__chain__S__` recognition (any `S`-edge) plus the `R`-composition, and when
`R` is transitive the full `__trans__` up-propagation so the chain composes
across `part_of` hops. Additive and sound (only fresh recognition clauses;
standard chain unfolding, no calculus change, no Lean re-cert): off-flag output
is byte-identical. Reproducers:
`oracle/ontologies/{11745_unsat_core,chain_domain_propagation}.ofn`. Tests:
`domain_consumer_chain_recognition`, `domain_consumer_transitive_chain_recognition`.

### Nominals: grounded CB reasoning (`KM_NOMINALS`, default off) — Phases 0+1

KM's prior nominal handling replaced `{o}` with a fresh concept proxy
`__nom__o` and lifted unconditional ABox facts; sound but incomplete whenever
the singleton property matters. Minimal witness (HermiT-confirmed,
`oracle/ontologies/nom_merge_sub.ofn`): `A ⊑ ∃r.({o}⊓B)`, `A ⊑ ∃r.({o}⊓C)`,
`B⊓C ⊑ E`, `∃r.E ⊑ G` entails `A ⊑ G`, which the proxy misses (the two
successors stay distinct). 60 of the 592 benchmarked ORE ontologies use
`ObjectOneOf`/`ObjectHasValue`.

Implements the ALCHOIQ consequence-based calculus (Tena Cucala, Cuenca Grau,
Horrocks, IJCAI 2018; arXiv:1805.01396) behind `KM_NOMINALS`, mapped in
`docs/NOMINALS-CB.md`. Phase 0 (frontend): under the flag, `augment` emits the
DL7/DL8 defining clauses `⊤ → __nom__o(o)` and `__nom__o(x) → x ≈ o` plus the
ground ABox clauses, and fences ontologies with individuals off the elc path;
off-flag the output is byte-identical. Phase 1 (engine):

- Term space re-encoded to `z < y < x < o_k < f(x) < f(o)` (individuals below
  the Skolem terms, `f(o)` composites packed positionally), a pure id-space
  relabeling validated byte-identical vs the prior binary on `ore_ont_16461`
  and the cardinality probes. The order satisfies Def 3 of the calculus given
  the existing predecessor-trigger-bottom refinement.
- One ground (nominal root) context `v_r` is the only place Hyper grounds the
  central variable (`σ(x) ∈ Σo`); it is created eagerly when ground facts
  exist and holds all ground inference. Ground ontology facts seed `v_r`
  fully and every other context on demand (first clause mentioning the
  individual).
- The Su^r forms (`B(o)`, `S(x,o)`, `S(o,x)`) push their y-form to `v_r` over
  individual-labelled edges (r-Succ); `v_r`'s ground conclusions flow back
  through the existing Pred machinery (r-Pred), with an edge-coverage
  discipline that kept a naive version from livelocking. `x ≈ o` crosses an
  `f` edge as `f(x) ≈ o`, which the receiver's Eq rule rewrites into ground
  atoms. A `v_r` empty clause is global inconsistency.

All five witness probes pass (HermiT-checked): `nom_merge_sub` and the DL8
merge derive the expected subsumption, the two-distinct-nominals negative
stays underivable, and `{o}⊑B, {o}⊑C, B⊓C⊑⊥` is reported inconsistent.
Off-flag and SRIQ-path output are unchanged (every new branch is unreachable
without individuals in the clause set). Known cost on the flagged path:
ABox-heavy ontologies slow down (`ore_ont_10594` 0.6 s → 85 s) — perf and the
remaining rules (Join, the r-Succ side condition, Nom) plus Lean
re-certification are future phases before the flag can default on.

### Frontend: AtMost recognition (`≤n r.F` on the LHS could never fire)

The mirror of the AtLeast gap below, found by inspection: the AtMost
clausification emitted only the constraint direction, so nothing could ever
derive the reified Q and `≤n r.F ⊑ G` was silently incomplete (not
exercised by ORE gold so far). Fix: excluded-middle recognition — fresh NQ
with `⊤ → Q ∨ NQ`, `Q ⊓ NQ ⊑ ⊥`, and NQ ⊑ ≥(n+1) r.F (n+1 witnesses with
pairwise inequalities); a context that refutes the witnesses derives Q.
Polarity-gated (the `⊤ → Q ∨ NQ` split fires in every context): emitted for
negative or unseen occurrences, skipped only when the pre-pass proves the
occurrence positive-only. Probes: `∀r.⊥ ⊢ ≤1 r.J` (vacuous) and
functionality ⊢ `≤2 r.J` (merge-derived) both derive G; negative probes
stay sound. In-corpus clause changes are confined to current timeouts
(10702, 1194, 14817). Test:
`frontend::normalise::tests::atmost_recognition_polarity_gated`.

### Frontend: ≥n recognition clause for n ≥ 2 (the 16461 min-cardinality gap)

The clausifier (`normalise.rs`, `Concept::AtLeast`) emitted the recognition
direction of a reified `Q ≡ ≥n r.F` only for n == 1 (the plain ∃-recognition
clause). For n ≥ 2 no clause could ever derive Q, so a qualified
min-cardinality on the LHS of a subsumption never fired: ore_ont_16461's
single missing subsumption, reproduced in a 21-clause probe (`P ⊑ ∃r.J1,
P ⊑ ∃r.J2, J1⊑J, J2⊑J, Disjoint(J1,J2), ≥2 r.J ⊑ G ⊬ P⊑G`).

Fix: emit the standard contrapositive clausification `¬Q ⊑ ≤(n-1) r.F`, i.e.
`r(x,y0) ∧ F(y0) ∧ ... ∧ r(x,y_{n-1}) ∧ F(y_{n-1}) → Q(x) ∨ ⋁_{i<j} yi≈yj` —
the same clause shape the AtMost branch already produces and the engine's
Hyper + Eq/Factor machinery already reasons over (multi-neighbour-variable
bodies, equality heads). No calculus change, no Lean re-cert: only the input
clause set is completed; the emitted clause is the definitional-extension
direction of the reified Q and is logically equivalent to `≥n r.F ⊑ Q`.
(n == 0 falls out correctly as `→ Q(x)`, since `≥0 r.F ≡ ⊤`.)

The probe now derives P ⊑ G. Frontend output is byte-identical on
ontologies without min/exact-cardinality ≥ 2 (checked on 10); 27 corpus
ontologies are affected and were re-validated against gold. New tests:
`reasoner::tests::min_cardinality_recognition` (engine-level, the probe) and
`frontend::normalise::tests::atleast_two_recognition_clause`.

**Polarity gating**: the recognition clause is pure cost when the `≥n`
occurs only positively (RHS — intro direction suffices), and on
existential-rich ontologies it feeds the live-disjunction blow-up (a single
unqualified `≥5 setting-for` recognition clause on ore_ont_15672/DOLCE
doubles the pipeline wall time: the resolvent residues create new Hyper
providers, mutually incomparable under subsumption). The pre-pass
(`mark_polarity`) now records each AtLeast's polarities; recognition is
emitted unless the concept is PROVEN positive-only (negative or unseen ⇒
emit, so coverage gaps keep the complete behaviour). Even gated,
ore_ont_15672's genuinely-negative `≥5` (an EquivalentClasses conjunct)
keeps its recognition clause and the ontology joins the live-disjunction
timeout family — recovering it is the ordered-resolution workstream, not a
cardinality issue. Test:
`frontend::normalise::tests::atleast_recognition_polarity_gated`.

### Engine: symmetric-group pruning in the Hyper join

The recognition/at-most clause shape is fully symmetric in its neighbour
variables, so the backtracking join enumerated every permutation (and every
equal-term repeat) of each candidate combination — `k^n` assignments where
`C(k,n)` are distinct, ruinous for n ≥ 4. `OntologyClause` now precomputes
its exchange-invariant variable groups (pairwise swap-invariance,
union-find; transpositions of a connected component generate its full
symmetric group), flagging groups whose head carries an equality for every
pair. The join prunes assignments whose group terms are not sorted (strictly
sorted for flagged groups: an equal-term assignment makes some head equality
`t≈t`, a tautology `build_hyper_resolvent` drops). Side-clause variables are
exempt (the side clause is pinned to its body position and not
interchangeable with worked-off candidates). Output-preserving: every pruned
assignment is a permutation of a kept one and yields the identical canonical
resolvent (heads/bodies are sorted and deduped; `Lit::eq` normalises
orientation), so the derived set is unchanged — no Lean re-cert.

### Engine: central-strategy successor cores must hold facts only

With the recognition clause in place, n = 2 worked but n ≥ 3 still stalled
(probe: P with 3 pairwise-disjoint r-successors, `≥3 r.J ⊑ G` ⊬ P ⊑ G; the
real ore_ont_16461 needs n = 4). Trace: P's context correctly derives
`⊤ → A2(f1) | A3(f1) | Q` by paramodulation, but the central strategy had
pushed the disjunctively derived triggers A2(f1), A3(f1) into the successor
CORE alongside the fact A1(f1). The `[A1,A2,A3]`-core context derives ⊥, and
apply_pred conditions the push-back on the whole core — a clause
`A1(f1) ∧ A2(f1) ∧ A3(f1) → ⊥` that would have to cut TWO literals of the
same disjunction at once, which no resolution step can do. The per-disjunct
refutations (`A1 ∧ A2 → ⊥`, `A1 ∧ A3 → ⊥`) were unavailable because the
hypothesis clauses `p → p` added by apply_succ were subsumed by the
over-large core's `⊤ → p`. The legacy non-central strategy (empty cores,
pure hypotheses) does not have the bug — KM_NO_CENTRAL=1 derives G on every
probe, confirming the diagnosis.

Fix: a successor core now contains only the σ-image of FACT triggers (unit
clauses `⊤ → p(f)` in the predecessor); disjunctively or conditionally
derived triggers still travel as Succ messages (edge bookkeeping +
hypothesis `p → p` at the target) but stay out of the core, so their
consequences return conditioned on `p` alone and each disjunct is cut
individually. Context identity (`central_successor_for_core`) keys on the
fact core; hypothesis-only trigger growth keeps the same target and sends
just the new triggers. No calculus-rule change (Hyper/Pred/Succ/Eq schemata
untouched, no Lean re-cert, same category as the central-strategy landing):
cores shrink, so the context invariant (core ∧ body → head entailed) is
preserved, and every previously derived consequence is still derived — the
fact-trigger cores reproduce the old behaviour exactly on ontologies where
all succ triggers are facts (the common case: existential successors).
New test: `reasoner::tests::min_cardinality_recognition_three_witnesses`.
With both fixes the full ore_ont_16461 derives the gold-only subsumption
`Patient1 ⊑ Systemic_JIA_Patient` (≥4 hasAffectedJoint.Joint over 5
pairwise-disjoint joint successors).

### Engine: clause interning (Pred pipeline + global arena) — peak RSS −77%

KM_MEMSTATS accounting (new, diagnostics-only) on ore_ont_9944 at fixpoint
showed each derived clause stored 5+ times across the engine: per-context
`neighbor_pred` copies of back-substituted pred clauses (11.4M instances,
2.06 GB — only 388k distinct, 29x duplication), a full clause copy per
(edge, clause) in `pushed_pred`, full copies in `pred_pool`/`succ_pool` and
`clause_keys`, the `max_head` duplicate, and `Msg::Pred` carrying a cloned
neighbour core + clause per queued message (13.8M messages). On top of that,
the seeded shared closure was cloned into every context (8009 root contexts).

Two interning stages, both representation/sharing only (the derived clause
set is unchanged, so no Lean re-certification — skipping a duplicate Pred
arrival only skips re-deriving clauses `add_clause` would dedup anyway):

1. **Pred pipeline** (`228067f`): engine-level `pred_interned` table;
   contexts hold u32 ids and `neighbor_pred_seen` dedups duplicate arrivals
   (real, from a successor's pre-/post-growth contexts under the central
   strategy). `pushed_pred` keys by (edge → `pred_pool` index). `Msg::Pred`
   carries `{to, from, edge_label, pool_idx}` (24 B, no heap); the sender's
   pool entry and core are immutable, so apply-time resolution reads exactly
   the send-time snapshot. 9944: 8.50 → 4.99 GB, wall 2:58 → 2:26.

2. **Global clause arena**: `cc_arena: [Vec<ContextClause>; 2]`, content-
   interned, split by ordering domain (root / non-root — the same
   (body, head) caches a different `max_head` under the two orderings, so
   the domains are never crossed). `worked_off`/`todo`/pools become Vec of
   u32 arena ids; `clause_keys` becomes HashSet of the id (the id IS the
   content key); head indexes store ids; the shared closures seed ids
   instead of cloning clauses per context. 6.08M worked-off instances
   collapse to 193k distinct (31x). 9944: 8.50 → **1.99 GB peak (−77%)**,
   wall 2:58 → **1:56 (−35%)**, output identical (315,940 subsumptions,
   exact set match). 49+16 cargo tests pass.

This is the lever for the 9724 (GALEN) memout, which churns >82 GB
unconverged on the old representation.

### Engine: complete disjunctive case analysis (same-term literals incomparable)

The context literal ordering (`calc.rs pred_lteq`) imposed a total order on
same-term concept literals (iri id + internal-definer-low), applying the
mutually-incomparable refinement only in root contexts. That total order is
incomplete for disjunctive consequence finding: once a disjunct stops being
maximal it is never resolved, so a head disjunction never fully case-splits.
Minimal probe (CB engine): `A ⊑ ∃R.(C⊔D), C⊑E, D⊑E, ∃R.E⊑G ⊬ A⊑G` (the engine
derives `C(f)|Q_2(x)` and stalls). This is the root cause of the incomplete
disjunctive ORE ontologies (12698's `∃`-filler disjunction + transitive role).

Fix: concept literals on the same term are mutually incomparable in every
context, so Hyper fires on every disjunct and the case split completes. This
matches the Lean completeness proof, which models Hyper as resolution on an
arbitrary atom (`CompletenessProp.lean`) with no ordering assumption -- the total
order was never part of the certified calculus. Sound by construction (ordered
resolution is sound for any selection). Validated on probes + ORE 2313 / 12698
minimal cores; 65 tests green; Horn (single-head) reasoning is unaffected.

TRADEOFF (sweep 5814): genuinely-disjunctive ontologies now explore all branches,
which is heavy (12698 ~16-19 GB). About 10 ontologies regress ok→timeout/memout.
This is fundamental -- completeness on disjunctive inputs requires full case
analysis -- and is recoverable only by performance work (stronger redundancy on
disjunctive clauses, or decoupling Hyper-maximality from Succ-trigger selection),
not by weakening the ordering. `KM_DUMP_WO=1` dumps every context's worked-off
clauses (debug, env-gated). `KM_NO_PRUNE=1` disables inert inverse/role-bridge
pruning (diagnostic; pruning is sound -- disabling it does not recover the
remaining inverse-role / GALEN incompleteness, which is a separate engine gap).

### Frontend: handle EquivalentObjectProperties (was silently dropped)

`EquivalentObjectProperties(R1 … Rn)` had no parse arm in either the AST path
(`parse.rs`) or the streaming RBox builder (`rbox.rs` `rbox_node`), so role
equivalences were dropped. Every inference that bridges two equivalent roles was
lost. Minimal witness extracted from ORE `ore_ont_2313` (`ddmin`, oracle =
HermiT entails `C ⊑ D`), a 3-axiom core:

```
SubClassOf(TO_0000059, ObjectSomeValuesFrom(BFO_0000050, TO_0000056))
EquivalentObjectProperties(BFO_0000050, PPIO_0000091)
ObjectPropertyDomain(PPIO_0000091, PPIO_0000069)
⟹ TO_0000059 ⊑ PPIO_0000069
```

The existential uses `BFO_0000050`; the domain is stated on the equivalent
`PPIO_0000091`. Without the equivalence the two roles never connect, so the
domain never fires on the existential's Skolem edge. `2313` was missing 88 such
subsumptions.

Fix: expand `R1 ≡ … ≡ Rn` into pairwise both-direction inclusions. `parse.rs`
emits the AST `RoleInclusion`s (so `normalise` produces the subrole clauses that
reach the reasoner); `rbox_node` emits matching `Subrole` records (routing /
relevance / domain-range). Any inverse member fences the axiom to the CB engine.
`2313` now matches gold exactly (88 missing → 0, 0 extra). 57 ORE onts contain
the axiom; the change is sound (role equivalence = mutual inclusion) and can only
recover entailed subsumptions. Tests green.

### Correctness tail: sound datatype-ABox precheck + complex-domain clausification

Resolved the four "unsound vs gold" ontologies and recovered one incomplete one.
The headline result is that KM was never unsound on the four flagged ontologies:
they are all genuinely **inconsistent**, and the gold signatures were wrong.

**Proof the gold was wrong.** Delta-debugging (`ddmin` over the axioms, oracle =
HermiT-reports-inconsistent) reduced each of `8941` / `13912` / `15516` / `2669`
to a 2–8 axiom inconsistent core. Running those cores through HermiT *and*
Konclude directly, both reasoners report inconsistent (Konclude prints
`EquivalentClasses(Thing Nothing ...)`). The recorded gold said "consistent"
because of two benchmark-harness bugs, both fixed:
- `ore_canon.py` canonicalised Konclude's `Thing ≡ Nothing` (its encoding of an
  inconsistent ontology) into "consistent with N unsatisfiable classes". It now
  maps `owl:Thing` in the `owl:Nothing` SCC — and any `consistent=false` — to the
  uniform empty inconsistent signature.
- `ore_runone.py` recorded Konclude's exit-0-with-empty-output on a SWRL
  `DLSafeRule` parse failure (`15516` / `2669`) as a bogus "consistent". It now
  flags Konclude "All parsers failed" as `error` (excluded from comparison).
The gold was regenerated for every affected ontology.

**KM side (`frontend/data_abox.rs`).** The CB engine drops the ABox, so these
asserted-data clashes never reached saturation. A new sound precheck detects:
- range-vs-literal clash: a `DataPropertyAssertion` whose literal value-space is
  disjoint from a (possibly sub-property-inherited) `DataPropertyRange`
  (`8941`: `xsd:string` range carrying a language-tagged literal — an
  `rdf:PlainLiteral`, never in the string value space);
- functional-data clash: `FunctionalDataProperty` with two provably-distinct
  values on one individual;
- an at-most-1-driven ground individual merge (closing role assertions under
  symmetry / inverse / sub-roles and domain/range typing) feeding a
  `DataMax`/functional clash or a `DifferentIndividuals` violation (`13912`:
  symmetric `Owner` + domain `Photo` + `Photo ⊑ =1 Owner` merges two photos,
  then `Photo ⊑ ≤1 url` clashes their distinct urls);
plus an asserted-member-of-unsatisfiable-class rule (`asserted_classes` on the
ofn meta; `owl_classify` makes the ontology inconsistent when a class proved
unsatisfiable has a provable asserted member). Every clash is an OWL 2
entailment; caps degrade to "not detected" (incomplete, never unsound).

**Incompleteness.** `parse.rs` now clausifies a COMPLEX
`ObjectPropertyDomain`/`Range` on a named role as the equivalent class axiom
(`∃R.⊤ ⊑ C` / `⊤ ⊑ ∀R.C`) instead of dropping it as `complex-domain`. The
named-class case stays on the rbox path (byte-identical). Recovers `ore_ont_4827`
exactly (the olia `domain(hasCase) = Adjective ⊔ ...` chain via `∃hasCase.Self`).

**Validation.** 19 new `data_abox` unit tests; full suite green. Whole-corpus
frontend differential: clause + meta output byte-identical on every ontology
except those newly flagged inconsistent; all newly-inconsistent ontologies
confirmed inconsistent by HermiT/Konclude (zero false positives). Remaining
incomplete onts are deeper engine gaps: `16461` (1 nominal subsumption, CB drops
individuals); `2313` / `12698` / `9944` (existential-superclass `∃R.C`
propagation).

### EL completion: clone-free hot loop (recovers giant ore_ont_8737)

The `elcomplete` worklist saturation cloned a state collection on every
Sub/Edge item to satisfy the borrow checker. On the transitive ORE giants this
dominated: transitivity is encoded as NF4, so the existential rules fire on
huge predecessor and superclass sets, and each firing paid a full-set clone.
Three changes remove the per-item allocations:

- `in_edges` is `Vec<Vec<(parent,role)>>` instead of `Vec<HashSet<...>>` — a
  pair is appended only in the `edges[parent].insert` success branch, so
  duplicates were already impossible and the set bought nothing. The Sub-side
  NF4 rule and ⊥-edge back-propagation iterate it by index (new entries pushed
  during the loop are picked up by the growing bound), clone-free.
- The Edge-side NF4 rule collects conclusions into a reused `nf4_buf` during a
  read-only scan of `sub_super[d]`, then applies them (replaces a full-superset
  clone per edge).
- NF4/NF7 rule blocks are skipped outright when their indexes are empty.

Schedule-only change: the same conclusions are derived, possibly in a different
order; the fixpoint is unchanged (saturation is monotone + confluent), so no
Lean re-cert. Validated: 53 unit tests; gold-identical signatures on controls
16744 / 10016 / 1559 / 13482.

Effect: `ore_ont_8737` classify 252 → 221 s standalone; in the benchmark
pipeline it went **timeout → ok at 205.7 s** (9.5 GB peak), signature
byte-identical to the Konclude gold. `ore_ont_16744` pipeline 167 → 151 s.

**Full-sweep confirmation (job 5690): 564 ok / 26 timeout / 1 memout**, vs
gold 554 agree / 6 incomplete / 4 unsound / 0 both-disagree — agree +1 (the
recovered 8737), no regression anywhere. All three 3M-axiom giants (8737,
15059, 16744) now classify within budget via the EL path.

### EL fast path: optional canonical-model completeness certificate (`elc`)

`elcomplete::to_nf` no longer aborts on the first non-EL clause: it collects the
non-EL clauses into a *residual* and still saturates the EL subset. With
`KM_ELC_CERT=1`, `classify` then checks every residual clause against the
saturated **canonical model** (domain = satisfiable concept nodes; `x_C ∈ D^I`
iff `C ⊑ D` derived; `(x_C,x_D) ∈ R^I` iff edge `(C,R,D)` derived). If all hold,
`I ⊨ O` for the full ontology, so the EL classification is exact (sound AND
complete) for subsumption, unsatisfiability, and consistency; any failure (or a
work-budget overrun) returns `None` and the caller falls back to the CB engine.
Never an approximation. 7 unit tests; the certificate logic is a calculus-logic
addition and needs Lean certification of the canonical-model lemma (deferred).

**Default OFF.** On ORE 2015 every non-EL residual is a live covering
disjunction (`⊤ → A ⊔ B`), a non-inert inverse bridge, or multi-successor
functionality — none of which the canonical EL model satisfies — so the
certificate never passes there (verified: fails at residual clause 0 on
4205/6212/15803/7127/7246/11311), and attempting it would saturate the large EL
subset before failing, stealing time from the CB fallback. With the flag off,
routing is byte-identical to before (`to_nf` returns a non-empty residual ⇒
`classify` returns `None` ⇒ same exit-3 fallback). The capability is for
near-EL ontologies whose non-EL part IS model-satisfiable.

Also in `elc.rs`: read stdin as raw bytes + `serde_json::from_slice` (skips the
whole-buffer UTF-8 validation and a second allocation; lower peak memory), and
`KM_ELC_TIMING=1` per-stage timing. The timing showed the ORE giant
`ore_ont_8737` is **saturation-bound** (read 0.5 s, parse 8 s, classify 252 s,
serialise 2.8 s) — its 240 s timeout is the EL completion itself, not I/O, so it
needs a faster (parallel, ELK-style) completion, not an I/O fix. `ore_ont_16744`
classify is 83 s.

Goal: close the remaining ORE 2015 coverage gap to Konclude (was 551/590 ok;
40 failures = 21 timeout + 19 memout). Diagnosis, fixes, and benchmark deltas
tracked here.

### Frontend (`ofn`): inverse-role bridge clauses (8+ incomplete → agree)

`InverseObjectProperties(R, S)` was parsed into `hooks.role_inverses` — which no
code consumed — and `ObjectInverseOf(R)` in concepts became a fresh role
`__inv__R` with no clause linking it to `R`. The engine has no inverse machinery
of its own, so inverse-role semantics was silently dropped. Diagnosed on the
SWEET cluster (`14896`/`3795`/`4834`/`6060`/`7025`/`7320`, 24 byte-identical
missing subsumptions each): the gold derivation `Age ⊑ Set` needs
`temporalPartOf ⊑ subsetOf`, `inverse(subsetOf) = supersetOf ⊑ setRelation`,
`range(setRelation) = Set` — i.e. range of a superproperty of the inverse.

`normalise.rs` now emits the two bridge clauses `R(x,y) → S(y,x)` and
`S(x,y) → R(y,x)` per inverse pair (the same swapped-orientation shape as
symmetric roles, which the engine already propagates; verified on `14896` where
the engine derives exactly the 24 gold subsumptions once the bridges exist).

Two hardening fixes rode along: `elc`'s NF6/NF7 recognizers ignored variable
wiring (a bridge clause would parse as a FORWARD role inclusion — unsound; a
chain could bind in listed order, not chain order) and now check the wiring
explicitly, rejecting anything else to the CB engine (exit 3). `el_rbox_safe`
is also forced false whenever an inverse pair was registered, covering bare
`ObjectInverseOf` which produces no rbox record.

Clause output is byte-identical on ontologies without inverse constructs;
inverse-bearing ones gain only the bridge clauses. Harness-validated: the six
SWEET-cluster ontologies plus `3050` and `8999` flip incomplete → AGREE
(8 of the 17 incomplete; the rest have other causes). Sound by construction
(the bridges are the first-order semantics of the axiom; saturation only gains
derivations). No Lean re-cert (frontend/input clauses; calculus untouched).

### Frontend (`ofn`): sound ABox-inconsistency precheck (4 unsound → agree)

Re-diagnosed the 8 "unsound vs gold" ORE ontologies. The dominant cause is NOT
the nominal/number under-detection previously assumed: for `6720`, `15288`,
`443`, `7052` the **ABox** forces an individual into two disjoint named classes,
so the ontology is **inconsistent** (HermiT agrees; Konclude and ELK report all
classes unsatisfiable). KM missed it because the CB engine drops every
individual/ABox clause (`reasoner.rs` maps `Ind`/`Aux` terms to `None`), so the
clash never reaches saturation — KM emitted the full taxonomy of subsumptions,
which the aggregator scored as spurious "extra" subsumptions.

Witness (`6720`): `lemon_slice` is asserted both `fruit` (⊑ `non_alcoholic_-`
`ingredient`) and `sparqling_wine` (⊑ `alcoholic_ingredient`), and those two are
`DisjointClasses`.

New `frontend/abox_consistency.rs`: a sound, conservative precheck over the
parsed ontology. It closes ABox membership under the named subclass/equivalence
hierarchy, object-property domain/range, and `SameIndividual`, then reports
inconsistency iff some individual is provably in both ends of a named
`DisjointClasses`/`DisjointUnion` pair. Only NAMED classes participate (complex
operands and complex assertion concepts are skipped), so every fire is a genuine
OWL entailment — no false positives. The flag rides the `ofn` meta as
`abox_inconsistent`; `owl_classify` short-circuits to an inconsistent result
(empty subsumption set, matching the gold reasoners) without invoking the
engine. Cost is one TBox scan and an early-out (`None`) unless the ontology has
named-class disjointness, so the giants (no disjointness, no ABox) pay nothing.

Clause output is untouched (byte-identical); the only meta change is the added
`abox_inconsistent` field. Corpus-wide the flag fires only on the four family
ontologies plus two non-gold ontologies (`11305`, `11457`, both genuinely
inconsistent), and no ontology Konclude classifies consistently. Soundness vs
gold: **8 unsound → 4 unsound** (remaining: `7901` datatype empty data-range,
`8941` ALC `∀`-driven, `15516`/`2669` complex-boolean over-derivation); agree
530 → 534. No Lean re-cert (frontend, not calculus).

### Frontend (`ofn`): streaming parse + compact clause set (giant ontologies)

The three 3M-axiom giants (ore_ont_8737, 15059, 16744; 450–580 MB OFN) memouted
**in the frontend** at ~20 GB before the reasoner ever started. Three changes,
all output-preserving (byte-identical clause+meta JSON to the old frontend on the
full ORE corpus and on all three giants), cut the frontend peak ~5.5x:

- **Zero-copy tokeniser / parser** (`sexpr.rs`): tokens are now `&str` slices into
  the source produced by a lazy iterator, instead of a `Vec<String>` with a heap
  allocation per token. The parse tree (`Node`) borrows those slices. The
  whole-document token vector and its per-token strings are never materialised.
- **Streaming document walk** (`parse.rs` `for_each_ontology_child` /
  `parse_axioms`): each `Ontology(...)` child is parsed, turned into SROIQ
  axioms, and dropped, so the whole-document AST is never resident. The RBox /
  declared-class side scans re-stream the (cheap, zero-copy) parse instead of
  retaining and **deep-cloning** the AST across `normalise`/`augment` (the old
  `onto_nodes = args.clone()` was itself an O(document) copy). `reg.short` call
  order is preserved, so assigned internal names are identical.
- **Compact `DLClause`** (`clauses.rs`): `body`/`head` are sorted-deduped
  `Vec<Atom>` (canonicalised in the constructors) instead of `BTreeSet<Atom>`.
  A `BTreeSet` node over-allocates even for a 1–2 atom clause; on 3M clauses that
  dominated memory. `Ontology` also stores axioms behind `Rc` so the dedup set
  shares the allocation instead of cloning every axiom.

Measured on ore_ont_8737 (472 MB): frontend peak **19.2 GB → 3.6 GB**, wall
45 s → 20 s (per-stage `VmHWM` via `KM_OFN_TIMING`: normalise 9.4→2.6 GB,
augment 18.6→3.5 GB). Result: **ore_ont_15059 recovered** (was memout; now ok in
70 s / 5 GB, signature identical to the Konclude gold — consistent, empty
#UNSAT). 8737 and 16744 now reach the reasoner (frontend no longer the wall) but
are **not** EL-safe (inverse roles), so they route to the context engine and
remain time-bound there — the engine-scaling residual, not the frontend.

### Result (ORE 2015, 240 s / 20 GB, gold = Konclude 587 ok)

| build | ok | timeout | memout | vs baseline |
|---|---|---|---|---|
| baseline (16-thread, pre-fixes) | 551 | 21 | 19 | — |
| + Hyper join + adaptive retry | 553 | 33 | 5 | +2, 0 regressions |
| + message batching | 554 | 31 | 6 | +3, 0 regressions |
| **+ streaming frontend (final)** | **555** | 32 | 4 | **+4, 0 regressions** |

Recovered: 2397 (fully correct), 9944, 9724 (sound but CB-incomplete on
number/inverse), and 15059 (the giant — see the frontend section; agrees with the
Konclude gold). Soundness preserved: vs gold the correctness profile is unchanged
(530 agree, 17 incomplete, 8 unsound — the pre-existing CB nominal/number
under-detected-unsat cases — both-disagree = 0); the one newly-classified
ontology (15059) agrees with gold, and no previously-agreeing ontology regressed.
All landed changes (Hyper join, batching, streaming frontend) are
output-preserving, so they change *whether* an ontology finishes in budget, never
*what* it derives. km has the lowest median peak memory of the five reasoners
(45.9 MB; Konclude 65, Sequoia 536).

Residual is genuinely hard for the CB engine: live-`∀+⊔` disjunction
(message-traffic explosion — Sequoia, the same calculus, solves these via more
mature redundancy/ordering), the two remaining giants (8737, 16744 — frontend now
fits, but they are not EL-safe so they route to the context engine and time out
there), four CB-engine ~20 GB memouts (10781, 15491, 16444, 6682), and role-chain
propagation volume. The hypertableau (`tableau_cli`) is NOT a fallback: it errors
or hangs on real ORE ontologies (validated only on small synthetic + kinship).

### Hyper rule: backtracking join instead of full cartesian product
- `engine/src/engine.rs` `hyper()` / new `hyper_join()`: the Hyper rule used to
  build a candidate list per body position and iterate the **full cartesian
  product**, attempting unification per combination and discarding the ones that
  fail cross-position variable consistency. On number restrictions
  (`R(x,y1) ∧ C(y1) ∧ R(x,y2) ∧ C(y2) → …`) that is `(#successors)^k`
  combinations, almost all immediately discarded.
  Measured on ore_ont_13912: **738171 enumerated, only 2462 unifiable (99.7 %
  waste)**.
  Replaced with a backtracking join that extends the central substitution one
  body position at a time and only descends into candidates consistent with the
  bindings already made (shared neighbour variables bound earliest). Yields the
  **identical resolvent set** — the skipped combinations were exactly the ones
  that fail `unify` — at a fraction of the enumeration. Same ont: 738171 → 59410
  combinations (12×). All `cargo test` pass (incl. `factor_number_restriction_clash`,
  `existential_subsumption`). No change to soundness/completeness; pure
  enumeration optimisation.
- Added env-gated `KM_PROF` diagnostics (per-query seeding + message-loop
  progress, per-rule saturate counters). Off by default, no hot-path cost.

### Message loop: batched propagation
- `engine.rs` `run_for`: the inter-context message fixpoint used to `saturate`
  *and* `propagate` the target after **every** message. On disjunction/role-chain
  ontologies that re-scans each context's predecessor-edge and Succ/Pred pools
  thousands of times (ore_ont_5303: ~86 k propagate calls). Applying a message
  never enqueues new messages (only `propagate` does), so the loop now **drains
  the whole pending batch**, saturates each target, records the touched contexts,
  and propagates each **once** per round. `apply_succ`/`apply_pred` return the
  touched context instead of propagating inline. Fixpoint unchanged (saturation
  is monotone and confluent — the schedule does not affect the derived set);
  ~1.5× faster message throughput. Recovers ore_ont_9724; all `cargo test` pass;
  vs gold no new unsound/incomplete.

### Threading: adaptive parallel-then-single-threaded-retry (memory-aware)
- Root cause: `reasoner.rs` `saturate()` splits the named queries into
  `available_parallelism` chunks, each a full `Engine` that **re-derives the
  shared successor contexts**. On existential-heavy ontologies this multiplies
  the dominant cost by the thread count. Measured on ore_ont_2397 (ALCH): 1
  thread = 9 GB / 138 s **SUCCESS**, 8 = 40 GB, 16 = 84 GB, 64 = 20 GB **MEMOUT
  @ 9 s**.
- A *blanket* `KM_THREADS=1` is **net-negative**: it recovers the memory-bound
  onts but regresses the speed-bound ones (measured: −12 onts that needed
  parallelism for speed now time out, vs +1..4 memout recoveries). Parallelism
  is genuinely valuable for throughput; it is only harmful (memory) on the
  existential-blow-up onts.
- Fix (`owl_classify.py` `_run_engine_adaptive`): run the **default parallel**
  attempt under an RSS watchdog (`KM_PAR_MEM_GB`, default 18 GiB, just under the
  20 GiB benchmark memcap) that kills *only the engine child*; on overflow,
  **retry single-threaded** (one engine, successor contexts shared, far lower
  memory). Keeps parallel speed for the speed-bound onts (no regression) and
  recovers the memory-bound onts via the fallback. RSS (not virtual address
  space) is monitored so legitimate large parallel runs are not falsely tripped.
  An explicit `KM_THREADS` bypasses the adaptive logic.
