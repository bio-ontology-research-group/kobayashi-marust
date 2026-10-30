# Expressivity profiling and classification routing

KM chooses its classification procedure from an ontology profile before
normalisation. The default command uses the generated decision tree:

```bash
km classify ontology.ofn
km classify --route auto ontology.ofn
```

Every measured procedure remains directly selectable:

```bash
km routes
km classify --route cb_plain1 ontology.ofn
km classify --route ht_bridge ontology.ofn
```

`--route manual` preserves individually supplied `KM_*` settings. This is the
compatibility mode for experiments and for options that are not members of a
named bundle:

```bash
KM_THREADS=4 KM_NO_CENTRAL=1 km classify --route manual ontology.ofn
```

A selected route (any named route, or `manual`) bypasses the gate that keeps
each input on a mechanism that represents it. When the selected mechanism
drops or approximates part of the input, `km classify` refuses to publish a
consistent answer unless `KM_ALLOW_APPROXIMATE=1` is set; see
[Forced routes](#forced-routes).

## Selection boundary

The frontend's first streaming parse pass produces the source profile while it
builds the parsed SROIQ ontology. No token vector or document tree is added.
The route is selected after that pass and before normalisation because options
such as triggered absorption and cardinality metadata change the normalized
clause set.

For a small ontology, the frontend runs in the conductor process and installs
the selected option bundle directly. For a large ontology, the frontend worker
records the selected route in its meta file. The conductor applies the same
typed bundle and rebuilds its `Config` before starting EL, CB, or HT workers.
It then changes `KM_ROUTE` to `manual` so an explicit second frontend pass, such
as the absorbed pass in the sequential portfolio, cannot be re-routed.

The generated tree reads only source statistics and expressivity fields. It
does not use an ontology identifier. A small set of conservative source
candidates may refine after normalization when the frontend has proved a typed
payload certificate; the selected route and certificate outcome are recorded
in the route trace.

### Flat named-class taxonomies

A nonempty ontology whose logical axioms consist only of flat named-class
`SubClassOf` edges selects `elc`, even when conservative external expressivity
labels place it in the SRIQ core. The source gate excludes ABox and RBox axioms,
equivalence, disjointness, Boolean constructors, restrictions, cardinalities,
nominals, self restrictions, and datatypes. The EL worker independently checks
the normalized clause fragment before answering and declines outside it. This
generic gate covers 69 ORE ontologies; 68 move from `production_all` to `elc`
in v0.2.4, while the largest member already used EL completion.

## Konclude-compatible expressivity

`km profile ontology.ofn` emits a versioned JSON profile. Schema version 2 adds
the source-proved `positive_abox_tbox_separable` flag and explicit bottom-class
and bottom-role occurrence counts. Its expressivity code
is a Rust port of Konclude's
`COntologyStructureSummary::calculateExpressiveness()` and the occurrence flags
that `COntologyInspector` sees after preprocessing. Code construction follows
Konclude's precedence:

1. Select `AL`, `ALE`, or `ALC` from negation/disjunction and existential use.
2. Contract `ALC` plus transitivity to `S`.
3. Replace the base with `SR` for complex subroles, or append `H` for a role
   hierarchy.
4. Append `O`, `I`, and exactly one of `Q`, `N`, or `F` in that order.
5. Append `V`, `(D)`, and any remaining `+`.

The profiler walks parsed functional-syntax nodes, so comments and constructor
names embedded in IRIs do not create features. It also matches Konclude's
preprocessing effects for active transitive roles, inverse-partner role
equivalence, retained equivalence operands, reachable nominal domains, and
complex-chain suppression of the trailing `+`.

The implementation was checked against the official Konclude binary on the
complete 592-ontology ORE 2015 corpus: all 592 codes match and no ontology
failed profiling. Reduced witnesses for the final three preprocessing cases
are stored with the routing benchmark artifacts.

## Statistics

The `source` section contains:

- source bytes and top-level ontology-child counts;
- logical TBox, RBox, ABox, rule, unsupported-rule, declaration, annotation,
  and import counts;
- declared and distinct class, property, and individual counts;
- counts for each top-level axiom constructor;
- concept-constructor counts, including conjunction, disjunction, complement,
  existential, universal, cardinality, nominal, value, self, and datatype use;
- explicit occurrences of `owl:Nothing`, `owl:bottomObjectProperty`, and
  `owl:bottomDataProperty` in logical positions;
- maximum concept depth and arity, role-chain length, and cardinality.

The `clauses` section adds normalized-clause statistics when profiling is
requested: symbol counts, body/head sizes, Horn and disjunctive counts, maximum
disjunction width, empty sides, complementary definer patterns, function and
auxiliary terms, equality, role chains, and transitivity clauses. Ordinary
classification omits this second clause-vector scan because no routing split
uses those post-route values.

## Named procedures

The typed route catalog in `engine/src/routing.rs` is the executable definition
of each procedure. The matrix measures 24 isolated KM mechanisms and additive
HT combinations, plus four external baselines:

| Route | Procedure |
|---|---|
| `cb_plain16`, `cb_plain8`, `cb_plain1` | Pure CB with EL, HT, and absorption portfolio disabled |
| `cb_absorb16`, `cb_absorb8`, `cb_absorb1` | Direct absorbed CB at 16, 8, or 1 threads |
| `cb_trigger16`, `cb_trigger8`, `cb_trigger1` | Triggered-absorption CB at 16, 8, or 1 threads |
| `elc` | Strict normalized EL completion mechanism |
| `elc_cert` | Forced certified EL completion mechanism |
| `lean` | Single-threaded per-function CB without the central strategy |
| `ht_general` | Unrestricted HT measurement arm; never eligible for automatic routing (also not via the nominal general-HT probe, which is opt-in `KM_NOMINAL_GENERAL_HT_PROBE_UNCERTIFIED`); forced runs are wrong on 11647, 12566, 16372 |
| `ht_qo` | Structurally fenced QO measurement route; excluded from automatic policy because its certificate has incomplete corpus counterexamples |
| `ht_shoq` | Structurally fenced SHOQ measurement route; excluded because 10702 is incomplete; never selected automatically |
| `nominal_ni_tbox` | Wine-layout SHOIN specialist; measurement-only: its runtime checks accept 16372 and publish `consistent` for an inconsistent ontology, so it is never selected automatically |
| `ht_card` | Structurally fenced first-class cardinality measurement route; excluded because 10702 is incomplete |
| `ht_bridge` | Triggered absorption plus the ported Konclude completion/classification bridge |
| `ht_features` | One HT worker with the compatible completion feature modules combined |
| `ht_full` | The HT feature pack plus the Konclude bridge, sequentially inside one worker |
| `ht_rules` | DL-safe-rule consistency procedure with CB classification |
| `card_fn` | Functional properties as first-class `≤1` restrictions; measurement-only because forcing it regresses other inputs |
| `nominals` | Exact CB nominal/ABox calculus; the required route for every ABox outside the source-certified positive separation fragment |
| `nominal_ni_abox` | Post-normalization typed-ABox SHOIQ specialist: a complete data-assertion omission certificate gates a no-blocking complete-answer-or-defer worker, with exact nominal CB retained as fallback |
| `certified_card_proxy_abox` | First-class cardinality arm with a normalized positive-role ABox consistency/taxonomy certificate; a failed certificate defers to the exact nominal CB fallback |
| `seq_on`, `seq_off` | Force the Sequoia definer ordering on or off instead of using its internal structural gate |
| `elk`, `hermit`, `konclude_w1`, `konclude_w16` | External baselines, with official Konclude measured at one and 16 workers |

The catalog still exposes `default*`, `production_all*`,
`cb_absorb_portfolio16`, `tableau`, and `tab_race` for direct experiments.
They are not matrix rows: the first groups are portfolios, `tab_race` is a
race, and the historical tableau has no full-fragment procedure contract.
The matrix keeps the additive `ht_features` and `ht_full` combinations because
they define single, sequential completion mechanisms rather than concurrent
competitors.

Every isolated HT row sets `KM_MECHANISM=ht` and an exact `KM_HT_ONLY`
discriminator. A nonmatching input returns `unsupported`; it never falls
through to CB, the unrestricted HT worker, or the historical tableau. QO,
SHOQ, cardinality, general HT, and the additive feature packs remain measurable
but are excluded from policy learning because they have incomplete corpus
counterexamples or no complete-procedure contract. The ISOLATED bridge row
emits either a complete taxonomy or an explicit defer, but it remains excluded
as a policy leaf until the automatic route has a source-level applicability
contract, because a defer under `KM_MECHANISM=ht` has no in-process fallback.

The composed `production_all*` routes are different: `KM_HT_ONLY=certified`
admits only the bridge's complete-answer-or-defer path, the EL portfolio
answers only on a passing certificate, and the always-running CB engine is the
preferred fallback with the CB-preference winner rule. That composition has a
complete-procedure contract and is the exact configuration of the 2026-07-13
production sweep (574 ok / 508 exact matches, zero gold-match regressions,
docs/SOLVE-3215.md). It is therefore policy-eligible for the SRIQ core, and
the bootstrap generated tree selects `production_all` until the learned matrix
tree replaces it. The earlier `cb_plain16` bootstrap silently normalized the
trigger-absorption/bridge environment away before the frontend ran, so the
bridge-closed terminologies (541, 12653, 7914, 3215, 9663, 9724) regressed to
plain-CB timeouts whenever `KM_ROUTE` was unset — the deployed harness default.

Named bundles normalize their conflicting routing keys to the same settings as
the IBEX matrix. Diagnostic settings remain available. `manual` is the route to
use when a caller wants complete control over individual algorithm settings.

### Bridge terminology: source TBox or clause translation

The Konclude bridge builds its terminology in one of two ways
(`bridge_tinput_with_trigger_absorption`, engine/src/konclude_ht/bridge.rs).
With trigger absorption on (`KM_TRIGGER_ABSORB=1`, set by every bridge route)
and a nonempty `source_axioms` channel it builds the source TBox from the
normalized class axioms. Otherwise, or when `KM_NO_SOURCE_TBOX=1` forces it,
it translates the reverse-Skolemised clauses (the clause translation).

The frontend fills `source_axioms` from `SubClassOf`, `EquivalentClasses` and
`DisjointClasses`, including the axioms the parser desugars into them:
`DisjointUnion`, complex or inverse object property domains and ranges, and
`DataPropertyDomain`. No named route sets `KM_NO_SOURCE_TBOX`, so the automatic
route uses the clause translation only for an input without any such axiom.
Such an input has no class expressions and therefore no definer markers unless
it has an ABox, and a bridge input with individuals but without the typed
source ABox channel is declined (`has_any_nominal_input`). The defects below
all need resolved definer markers, so automatic routing was not affected; on
inputs without markers the translation is unchanged.

The clause translation resolves each frontend definer marker to the native
concept it abbreviates. Up to v1.5.4 only the trigger-absorbed concept-clause
encoder used the resolved concept. The trigger-less fallback, the guarded
`R(x,y)` encoder and the recognised `>=k` fallback still emitted the marker
atom, which had no definition there. Forcing `KM_NO_SOURCE_TBOX=1` then missed
consequences: 302 of the 700 generator seeds wrong against HermiT, all
incompleteness (25 missed inconsistencies), measured 2026-10-29. Now every
clause that mentions a resolved marker is encoded over the resolved concepts
only. It is absorbed when possible, dropped when it is a syntactic tautology,
and otherwise installed on TOP. A query class is never resolved, because
classification reads queries off their atoms. With the fix the forced clause
translation is wrong on 0 of the 700 seeds (results/agents/2026-10-29/
bridge-clause-path/). A clause shape the translation cannot encode still counts
as unsupported, and the bridge declines the input. On `--route ht_bridge`
that decline exits with status 3 and prints `unsupported: selected native HT
bridge deferred (konclude_ht bridge defer)`; on the automatic and
`production_all` routes the CB engine answers instead.

### Typed-ABox SHOIQ refinement

The source tree initially labels eligible nominal/inverse/functionality inputs
as `nominals`. After normalization, `nominal_ni_abox` is selected only if the
frontend proves the complete positive-data-assertion omission obligation. The
gate accounts for inherited data roles, conditional maximum and exact
cardinality one, duplicate values, `rdfs:Literal`, top data properties, and
unsupported constructs per property. It also requires the source-side nominal,
inverse, functionality, ABox, import, rule, and role-chain conditions. Any
unknown interaction leaves the route as exact `nominals`.

The specialist preserves inverse-functional equality clauses, accepts only
trusted named ABox classes and resolvable individual proxies, and rejects
generated/internal symbols. Its SHOIQ worker may return a complete taxonomy or
defer; defer runs the exact CB fallback. This route closed 6934 in the audited
v16 sweep without changing the accepted results of the other 591 inputs.

For a large source-certified typed object ABox, the `certified_nominals`
portfolio may schedule that same complete-answer-or-defer bridge before it
allocates the nominal-aware CB fallback. The scale gate requires at least
30,000 logical axioms and 100,000 concept expressions. If the bridge rejects
the normalized input, errors, or explicitly defers, KM starts the unchanged
exact CB procedure. Smaller inputs keep the concurrent race. This ordering
reduces process-tree memory when the bridge succeeds; it does not change either
procedure or the accepted answer contract.

The same sequential schedule applies to very large, source-certified
disjunctive SHI terminologies with no ABox, at least 50,000 logical axioms,
300,000 concept expressions, 10,000 unions, and 50,000 named classes. The
bridge remains complete-answer-or-defer and the unchanged `production_all` CB
stack starts after any defer. The complete 592-profile audit currently selects
only ORE3215.

For very large TBox-only SRIQ inputs with substantial role chains and qualified
cardinality, `production_all` uses eight workers instead of 16. The route,
frontend, inference procedures, fallback, and answer contract are unchanged.
The complete 592-profile audit currently selects only ORE14817.

An exact `elc` leaf runs completion in-process when its source profile is
structured rather than a flat one-class-per-axiom taxonomy. This removes the
worker taxonomy serialization and parse round trip. Flat taxonomies retain
process isolation so completion allocations are released before public-output
mapping. The selected route and completion algorithm are unchanged.

When positive-EL ABox materialisation runs before an atomic exact-EL leaf, its
completion result supplies both the consistency certificate and the taxonomy.
The leaf does not recompute that fixpoint. This reuse is limited to the exact
EL mechanism; every other mechanism and fallback retains its existing input
and scheduling contract.

The consolidated production portfolio also restores two guarded mechanisms
that the frozen matrix measured separately:

- the first-class cardinality arm may answer only as a CB-guarded fallback on
  its structural candidate fragment, restoring the historical 7499/9540 path;
- the DL-safe-rule consistency precheck may short-circuit only when it finds a
  sound clash, restoring 2669/15516 while unsupported rule forms still fail
  closed.

The generated bootstrap tree selects `production_all`, which retains the
validated KPSet bridge stack used by 541, 12653, 7914, 3215, 9663, 9724, and
14817. Isolated specialist routes remain excluded from learned automatic
leaves unless their complete-or-defer contract is documented.

`KM_ROOT_ORDERED` is intentionally outside the automatic route catalog. It
changes CB derivations and remains an opt-in experiment pending Lean
re-certification and a complete corpus A/B comparison.

### Vacuous universal-role inclusions

`SubObjectPropertyOf(R owl:topObjectProperty)` holds in every OWL 2 DL
interpretation, so it is a tautology. When it is the document's only mention
of the builtin, the frontend removes the axiom and its RBox row before
normalization (`engine/src/frontend/top_role.rs`), and the source profile then
describes the retained, universal-role-free terminology:
`expressivity.universal_role` is false, and the ABox certificates
(`positive_abox_tbox_separable`, `disjoint_union_abox_candidate`) together
with every automatic predicate keyed on the universal role are evaluated for
that terminology. This is exact in both directions. The retained ontology is
logically equivalent to the source, it is closed under disjoint unions, and no
clause or RBox row reads the builtin, so every worker fence that exists because
KM has no universal-role object is moot. A document that uses the builtin
anywhere else is never elided and keeps the conservative occurrence flag; so
does a run under `KM_NO_TOP_ROLE_ELISION`. The Konclude DL code is unaffected,
because `V` is contributed by grounding rather than by this flag.

The corpus witness is ORE 16303, an inverse/complement SHOI terminology with a
positive object ABox of 185 assertions whose asserted `is about` edges are read
by TBox existentials. No ABox projection certificate applies to it, and its
only universal-role occurrence is one tautological inclusion. That occurrence
alone used to force the eager nominal CB route. The typed object-ABox bridge
portfolio (`certified_nominals`) is now selected, with the unchanged
nominal-aware CB fallback. See [`SOLVE-16303.md`](SOLVE-16303.md).

## Forced routes

A route is forced when the caller names it: `--route NAME`, `KM_ROUTE=NAME`,
or `manual`. `auto` is not forced, and neither is an unset `KM_ROUTE` in a
library call. A forced route bypasses the source gate that keeps every input on
a mechanism that represents it, so the selected mechanism may drop or
approximate part of the input. Every such drop only weakens the ontology: an
inconsistency found without the dropped part is still an inconsistency, but a
consistent answer is the answer for the weakened ontology, not for the input.

The rule (`orchestrate::classify_with_evidence_mode`, outermost call):

- A forced route whose consistent answer has any drop does not publish it.
  `km classify` exits 3 and names the route and the dropped constructs:

  ```text
  unsupported: route `default` drops 3 ABox assertions (ClassAssertion); the answer would be approximate; use the automatic route (--route auto) or set KM_ALLOW_APPROXIMATE=1
  ```

- With `KM_ALLOW_APPROXIMATE=1` the answer is published, marked by an
  `APPROXIMATE<TAB>reason` line directly after `DROPPED` (JSON key
  `approximate`), and `DROPPED` counts every drop, including the
  route-specific approximations below that an automatic answer never carries.
- An inconsistent answer is published unchanged on every route, with one
  exception. When a route reads a one-sorted clause stream (no
  `KM_NOMINALS`, not the bridge-exclusive worker) on a source with a TBox
  nominal and data properties, and the sort encoding of docs/NOMINALS-CB.md
  section 6 would apply, the stream is stronger than the ontology: data
  successors fall under `⊤ ⊑ C` and can be forced onto a named individual
  (m2197: `⊤ ⊑ ≥2 u` and `⊤ ⊑ {a}` is consistent, the one-sorted stream is
  not). Such a forced route publishes neither verdict
  (`FrontendResult::one_sorted_data_successors`, checked in
  `orchestrate::classify_with_evidence_mode` after the drop rule, whose
  message wins for a consistent answer); with `KM_ALLOW_APPROXIMATE=1` the
  answer carries `APPROXIMATE` and a positive `DROPPED`:

  ```text
  unsupported: route `ht_general` reads data successors as objects (data properties beside a nominal outside nominal clausification); neither verdict would be exact; use the automatic route (--route auto) or set KM_ALLOW_APPROXIMATE=1
  ```

The same rule covers `km classify --realize` (forced routes require
`KM_REALIZE_ANY_ROUTE=1` first) and the `km incremental-source` session, which
keeps an ambient `KM_ROUTE`. The session refuses an approximate answer even
under `KM_ALLOW_APPROXIMATE=1`, because its rows, deltas and reuse checks carry
no marker. The legacy session (`KM_SOURCE_SESSION=legacy`) always routes the
source automatically. `km explain` accepts only `auto`. The Protégé adapter
declines any answer with `APPROXIMATE` or a positive `DROPPED`.

The automatic route is unaffected. The caller's route is read once, by the
outermost classification, before route selection or any fallback rewrites
`KM_ROUTE`. Nested classifications (fallbacks, probes, source rewrites, the
mirror projections) and the source-incremental session's own route-specific
backends (`orchestrate::InternalRoute`) are never forced, and the
route-specific approximations are never added to an automatic answer. The
regression test `tests/forced_route_fail_closed.rs` runs every route of
`km routes` on reproducers for each construct below, with and without
`KM_ALLOW_APPROXIMATE=1`, and requires each to refuse, answer exactly, or
(only when allowed) mark its answer; `auto` must answer each exactly.

### What each route drops

Drop sites (line numbers at the time of writing):

| Construct | Drop site | Published as |
|---|---|---|
| DL-safe rule whose atoms cannot be represented | `frontend/parse.rs:606` | `DROPPED`, every route |
| `HasKey` (only with `KM_NO_HAS_KEY_RULES`; otherwise `frontend/has_key.rs` rewrites it to a DL-safe rule before routing) and the remaining unencoded `Data*` axioms | `frontend/parse.rs:777` | `DROPPED`, every route |
| Unknown axiom kinds | `frontend/parse.rs:786` | `DROPPED`, every route |
| DL-safe rules the mechanism does not read (`KM_NO_HT_RULES`) and no exact lowering replaced | `frontend/mod.rs:1511` | `DROPPED` |
| ABox assertions outside nominal clausification: on an individual without a nominal proxy, `SameIndividual`, `DifferentIndividuals`, `NegativeObjectPropertyAssertion` (not counted when the source certifies the ABox separable) | `frontend/mod.rs:1585` (collected), `:1686` (counted) | `DROPPED`, selected routes only |
| The same assertions when a complete typed ABox payload exists (`KM_TRIGGER_ABSORB`) but the mechanism is not HT, so no worker reads the payload | `frontend/mod.rs:1690` | forced-route approximation |
| Nominals outside nominal clausification: the proxy class (`preprocess::nominal_clauses`) lacks the singleton and existence clauses (`preprocess::nominal_defining_clauses`), so it and every assertion on its individual are over-approximated | `frontend/mod.rs:1706` | forced-route approximation |
| Data-property assertions not carried after the `DataHasValue` conversion rerun (`orchestrate/frontend_run.rs:374`); converted ones are class assertions and drop with the ABox | `frontend/mod.rs:1708` | `DROPPED` |
| DL-safe rules a rule route's taxonomy does not apply when a nominal lets their conclusions reach class queries | `orchestrate/mod.rs:2838` | `DROPPED` |
| Clauses the CB signature builder cannot encode | `reasoner.rs:294` | `DROPPED` (worker) |
| Clauses and fenced constructs `cb_to_ht` cannot encode, when `KM_HT_FORCE` (`ht_general`) runs the HT worker outside every HT gate | `orchestrate/race.rs:759` | `DROPPED` (worker) |

Which routes reach which drop, from the bundles in `routing.rs` (and verified
on the reproducers of `tests/forced_route_fail_closed.rs`):

| Routes | ABox | Nominals | Data assertions | DL-safe rules | Keys |
|---|---|---|---|---|---|
| `nominals`, `certified_nominals`, `certified_card_nominals`, `certified_card_proxy_abox`, `nominal_ni_abox`, `nominal_ni_tbox` (`KM_NOMINALS`) | exact | exact | exact after conversion, else counted | unread: counted | rewritten to rules: counted as rules |
| `ht_bridge`, `ht_full` (HT reading the typed payload) | exact when the payload is complete, else counted | exact when the payload is complete, else approximation | as above | unread: counted | as rules |
| `production_all*` (portfolio with `KM_TRIGGER_ABSORB`) | counted, or approximation when the payload is complete (the CB arm lacks it) | approximation | as above | read | read as rules |
| `default*`, `manual`, `cb_absorb_portfolio16`, `tab_race`, `ht_rules` | counted | approximation | as above | read | read as rules |
| `cb_plain*`, `cb_absorb*`, `cb_trigger*`, `cb_portfolio16`, `lean`, `seq_on`, `seq_off`, `elc`, `elc_cert`, `certified_el_production` | counted (`cb_trigger*`: approximation when the payload is complete) | approximation | as above | unread: counted | as rules |
| `ht_general`, `ht_qo`, `ht_shoq`, `ht_card`, `ht_features`, `card_fn`, `tableau` | counted | approximation | as above | unread: counted | as rules |

"Read" rules still fail closed on unsupported rule shapes before any answer
exists. A frontend that lowers unary or constant-data rules sets `KM_NOMINALS`
for that run, so those inputs keep their nominals and ABox on every route.
The nominal count is conservative for the historical `tableau`, which seeds
its own nominal roots but has no full-fragment contract. The rule covers
representation drops only. Measurement-only mechanisms
(`ht_general`, `ht_qo`, `ht_shoq`, `ht_card`, `nominal_ni_tbox`, `card_fn`) can
still be incomplete on input they represent; the table in
[Named procedures](#named-procedures) lists the known counterexamples.

## Learning objective and safety gates

Each ontology and all 24 KM procedures run sequentially on one exclusive Intel
Xeon Gold 6248 node with a one-worker and a 16-worker official Konclude run.
The KM panel rotates position, and the Konclude order alternates. Each process
has a 240 second wall limit and a 20 GiB process-group RSS limit.

An incorrect, incomplete, timed-out, or memory-killed procedure has infinite
policy cost. For each correct procedure, the optimizer compares against a
strict Konclude envelope consisting of the faster reference time and the lower
reference memory, even when those come from different Konclude thread counts.
It minimizes:

```text
max(KM time / Konclude-best time, KM memory / Konclude-best memory)
```

A small mean-ratio term only breaks ties. Tree leaves minimize classification
failures first and cost second. Depth and minimum leaf size are selected by a
deterministic five-fold audit. General HT, QO, SHOQ, first-class cardinality,
historical tableau, and functional-cardinality measurement arms are excluded
from the policy regardless of empirical speed. Isolated bridge and HT feature
rows are also excluded until their automatic applicability contract is closed.
An ontology containing a DL-safe rule outside KM's supported rule forms is
hard-fenced from every ordinary route; empirical agreement cannot override
that source-level completeness guard.
Nominal/ABox inputs are routed by a hard semantic gate to the exact nominal CB
calculus, so the learner cannot replace it with faster proxy CB. The sole
exception is a source-proved positive ABox fragment described below. That
fragment enters the same performance tree as the nominal-free TBox core because
the certificate proves both consistency and TBox separation.

### Inverse and cardinality certificates

The first-class `≥n`/`≤n` arm needs one property: no number restriction may
apply to an inverse, inverse-connected, chained, transitive, universal, or
otherwise constrained role. Under that condition the exact inverse axioms, the
SHOQ number rules, and the inverse-aware blocking compose without Konclude's
NN/NI nominal-predecessor rule. `card_number_role_separable` records exactly
that proof. `inverse_cardinality_role_separable` records it together with the
separate ABox conditions: no negative assertion component may touch a non-simple
role and no positive assertion component may feed a proper role chain, because
the role automata are side data whose default use is universal propagation
rather than materializing every named-individual edge.

Both certificates admit an axiom that the first-class RBox channel cannot
represent while the frontend still clausifies it exactly. `rbox.rs` fences
irreflexivity, reflexivity, and a complex domain or range on a named role;
`parse.rs` and `normalise.rs` emit `R(x,x) → ⊥`, the `R(x,x)` fact, and the
ordinary `∃R.⊤ ⊑ C` / `⊤ ⊑ ∀R.C` inclusion for them. Those rows constrain a role
against classes or itself, never two role components, so they add no number-role
premise; the source certificate additionally requires the constrained role to
stay outside the number-role component. Asymmetry shares one fence reason with
the dropped `DisjointObjectProperties`, so it fails closed. `owl:topObjectProperty`
is admitted only as the super role of a plain role inclusion, where it is a
tautology compiled into a write-only bridge clause and the normalized recheck
proves no clause body, counted role, or other RBox row reads it.

A profile that holds both certificates selects `certified_card_nominals`, the
isolated HT mechanism carrying the exact typed ABox. A profile that holds only
the number-role half selects `certified_card_proxy_abox`. The normalized worker
input then proves whether the positive asserted-role graph can be omitted from
the cardinality taxonomy; a failed proof uses the exact nominal calculus.

The `certified_card_proxy_abox` route runs the same cardinality arm against the
exact nominal CB engine with the native ABox kept out of the card input. Before
the cardinality result can win, the normalized certificate requires a complete
positive object ABox with one asserted class per individual, rejects negative
roles, inequality, equality, disjunction, existential heads and number-role
interaction, closes the concrete asserted graph under positive role and chain
rules, and checks every resulting public type against the exact TBox taxonomy.
It also checks that every asserted class is satisfiable. Internal chain and
transitivity concepts are closed as role-automaton state and removed from the
published result. Any unsupported shape or missing entailment produces no card
answer. `KM_NOMINALS=1` preserves the complete fallback, so a source-profile
false positive changes scheduling only.

ORE 7499 is the corpus witness for the arm itself: its 74 asserted
`BFO_0000062` edges feed a proper role chain, its irreflexive role and complex
range are outside the number-role component, and
`km classify --route certified_card_proxy_abox` returns the Konclude/HermiT
taxonomy exactly. Current source selects the certified proxy route
automatically. Source-bound IBEX array `49701329` confirms the default route in
86.7359 seconds at 2,409.59 MiB, and audit `49710709` validates all 592 terminal
rows and route traces.

### Positive ABox separation certificate

KM certifies an ABox as TBox-separable only when it contains positive
assertions and the complete source scan finds no bottom class or bottom role,
class or role disjointness, complement, number restriction, nominal, different
individual, negative assertion, universal role, rule, key, or datatype
constraint. Functional and inverse-functional object properties are allowed:
mapping every individual to one object satisfies their equality constraint.
Every unlisted or uncertain constructor fails closed.
The implementation uses an explicit safe-axiom whitelist, so imports and
unknown or silently skipped axiom kinds also fail closed. The full contract and
proof are recorded in
[`POSITIVE-ABOX-SEPARATION.md`](POSITIVE-ABOX-SEPARATION.md).

For the accepted fragment, interpret every named class and object role as full
and every individual as one element. This gives a model of the TBox and all
positive assertions, proving consistency. Nominal-free SRIQ without the
universal role is preserved by disjoint unions. Any countermodel to a TBox
subsumption can therefore be united with the positive ABox model, proving that
the ABox adds no TBox subsumption. The normal EL or CB mechanism is consequently
sound and complete for classification; this is a proof boundary, not a pattern
learned from corpus agreement.

Konclude implements the more general architecture with separate individual
saturation, an all-assertion individual, and a consistency precomputation before
class classification. Its source checks the completed, non-clashed, sufficient
all-assertion saturation in
`CTotallyPrecomputationThread::isAllAssertionIndividualSaturationSufficient`.
On ORE 10697 and 15725, official Konclude spends 1,211 ms and 540 ms in
precomputation, then only 3 ms and 2 ms in class classification. KM's exact
monolithic nominal calculus times out under central and per-function schedules
at 1, 8, and 16 threads. The source certificate safely selects the ordinary
TBox mechanism on these inputs instead of repeating the ground closure in each
query engine.

`results/benchmarks/2026-07-15-routing/emit_rust_tree.py` translates the audited
JSON tree into `engine/src/routing/routing_tree_generated.rs`. The shipped
classifier has no runtime machine-learning dependency.

## Validation artifacts

The experiment scripts, per-ontology statistics table, immutable hashes,
matrix audit, learned tree, cross-validation results, predictions, and gap
lists live under `results/benchmarks/2026-07-15-routing/`. After tree generation,
a separate paired 592-ontology sweep runs default `auto` and both Konclude
references. It checks route identity, signature correctness, wall time, peak
RSS, host pairing, binary hashes, and expressivity codes.
