# DL-safe rules (SWRL `DLSafeRule`) — fragment and contract

## v1.4.4 behavior

Version 1.4.4 extends the historical precheck described below with
source-preserving rule normalization, finite grounding, and rule-aware
completion paths. An accepted classification must account for the complete
source rule obligation; a partial precheck alone cannot establish a consistent
taxonomy. The implementation also preserves the consistency check when rules
have already been normalized into ordinary clauses.

Input validation allows DL-safe SWRL alongside OWL 2 DL. Invalid input is
refused with an explanation and exit code 2; inability to establish complete
support is reported separately with exit code 3. In particular, the unmodified
ORE inputs 2669, 15516, and 10906 contain literals typed as `rdfs:Literal` and
are now refused. Historical results on cleaned or differently admitted inputs
below are not current verdicts on those original files. The grammar accepts a
named individual or variable as the subject of a `DataPropertyAtom`.

The final 1,920-input benchmark has no unsupported-input outcomes, and its
output audit confirms zero dropped axioms in successful classifications.
Invalid inputs and resource-limited runs remain separate outcomes. See the
source hashes, input audit, and validation records in
[`v1.4.4 support evidence`](../results/benchmarks/2026-10-02-v1.4.4-support/).

## Rule-aware taxonomy beside a nominal (2026-10-30, v1.5.5)

### Defect

On the automatic route, a consistent ontology with DL-safe rules was
classified in two steps: the rule worker (`KM_RULES_CONSISTENCY`, the
clausal `Tableau` over the ABox seeded as nominal roots and the O-guarded
rule clauses) decided consistency, and the CB engine then classified the
ontology without the rules. Without nominals this is exact: rules conclude
facts about named individuals only, and a model of the rules and the ABox,
in disjoint union with a countermodel of a non-entailed TBox subsumption,
refutes that subsumption. A nominal (`ObjectOneOf`, `ObjectHasValue`) or the
universal role lets a rule conclusion reach a class query, so the rule-free
taxonomy can miss subsumptions. v1.5.4 counted the rules as dropped
(`KM_TIMING rules-consistency: N rule(s) not applied to a nominal
taxonomy`, published `DROPPED N`). Generated seed fr282
(`results/agents/2026-10-30/rules-worker-cost`) shows the loss: `A ⊑ {c, b}`,
`D(c)`, `t(b, b)` with domain `∃s.{c}`, `v(c, 4)` and the rule
`s(x, y) ∧ v(y, n) ∧ n ≥ 0 → D(x)` entail `A ⊑ D`, which needs the rule
conclusion `D(b)` on the derived edge `s(b, c)`. A second defect on the
same step: a binary object-atom rule beside a TBox nominal and a data
property got no verdict, because outside nominal clausification the
rule worker reads the one-sorted clause stream (data successors fall under
`⊤ ⊑ {a}`, m2197), on which neither verdict is exact.

### Change

- `orchestrate::rules_reach_class_queries`: the source has an object
  nominal concept or the universal role. Then the rule worker runs with
  `KM_RULES_CLASSIFY=1` and classifies its input (`tableau::rules_classification`,
  `Tableau::classify` over the converter's queries, which include every
  declared class: the frontend gives a class without axioms the clause
  `C(x) → C(x)`), and its taxonomy is the published answer. The CB
  run is skipped on these inputs. `KM_RULES_NO_TAXONOMY=1` restores the
  v1.5.4 behaviour (consistency only, rules counted as dropped).
- The converter drops the individual proxy definitions
  `__nom__a(x) → x ≈ a` of nominal clausification (it has no individual
  constants) but declares every `__nom__a` a nominal of the worker, which
  seeds one root for it and merges every carrier into that root, so
  `__nom__a` denotes exactly one element, the individual `a` (the constant
  occurs in the worker input only through its proxy). The orchestrator
  counts these clauses (`orchestrate::proxy_definition`) and passes the
  count to the worker (`KM_RULES_CLASSIFY_PROXY_DEFINITIONS`); every other
  converter drop refuses the taxonomy.
- The rule-aware taxonomy runs only when the worker input has an
  executable rule (`input.rules` non-empty). Rules the frontend normalized
  (unary and constant-data rules, docs/RULES lowering in
  `frontend::data_rules`) are ordinary clauses of the stream every
  taxonomy worker reads, and finite grounding removes a rule only when no
  asserted value satisfies its built-ins (the rule is then inert). Without
  an executable rule nothing is outside the CB taxonomy, so it is published
  as computed; v1.5.4 counted those rules as dropped as well (seed fr344:
  `DROPPED 3` on a correct answer). The ABox-seeded tableau also has no
  backjumping on its careful path and can explode where the CB route
  answers at once (fr344: thousands of branches on `⊤ → X ∨ Y ∨ Z`), so it
  is not used where it adds nothing.
- A ground `DifferentIndividuals(a b)` is encoded on the nominal roots as
  `__nom__a(x) ∧ __nom__b(x) → ⊥`. The converter used to record it
  without encoding it and without counting it, in the consistency check as
  well (a consistent verdict could ignore a distinctness). Each proxy
  denotes exactly one element, so the clause says `a ≉ b` and is entailed
  by the ontology: it removes no model of the ontology. Probe `diff4`
  (`K ≡ {b} ⊓ {c}`, `b ≉ c`, `K` unsatisfiable) failed without it.
- Schedule. The rule-aware classification runs alone first, within a
  budget (`KM_RULES_TAXONOMY_BUDGET_S`, default 10 s). The rule tableau has
  no dependency-directed backjumping on its careful path, and a subsumption
  test that holds must exhaust its search: on seeds fr6 and fr29 it runs
  past 240 s where the CB route answers in under a minute. Past the budget
  the worker is stopped, the consistency-only check runs, the CB taxonomy of
  the rule-free stream is computed as before, and the rule worker then
  classifies with that taxonomy as given (`KM_RULES_CLASSIFY_KNOWN`,
  `Tableau::set_known`): a CB subsumption or unsatisfiable class is
  recorded without a test, every other model-label candidate is tested.
  Every CB entailment is an entailment of the ontology with its rules (the
  rules only add constraints, and the inert-sort release keeps every
  root-label test's verdict), so the given pairs are sound, and the
  remaining candidates are decided as in the first schedule: both schedules
  publish the same taxonomy. The worker decides every query over its
  complete input, so clauses the CB worker omitted are not omissions of
  the answer (`DROPPED` is reset; front-end omissions are counted
  separately). The budget is a scheduling bound, not a semantic one.
- The input is refused (exit 3, `unsupported: ...`) instead of answered
  with `DROPPED` when the rule worker's conversion omitted a clause or fenced
  a construct (a `DifferentIndividualsAtom` rule, for example), when the
  input has nominals, inverse roles and number restrictions together (the
  tableau has no NN-rule; the converter fences it as
  `inverse+number(SHIQ)`), and when the stream is one-sorted. The message
  names the fence. One existing fixture changes outcome this way:
  `finite_data_rule_normalization::finite_rule_nominal_query_uses_inverse_chain_and_transitive_premises`
  (an inverse role chain and a number restriction beside a nominal) was
  published by v1.5.4 with `DROPPED 1` and is now refused; the test
  accepts either an exact answer or that refusal.
- The frontend selects nominal clausification (`KM_NOMINALS`) for an
  automatically selected `ht_rules` route whose source has a rule and an
  object nominal or the universal role, so the sort encoding of
  docs/NOMINALS-CB.md section 6 applies and the stream is never one-sorted
  on this step. The finite-data-rule grounding already did this for rules
  with data atoms.

### Exactness argument

Write `O` for the clause set of the rule worker input (the frontend clauses,
the ABox seeded as one nominal concept `{a}` per named individual, the rule
clauses with the O-guard `__O__` on every variable, and `{a} → __O__` for
every named individual). Its models are the models of the ontology with
the rules read under the DL-safe semantics: a rule variable binds only to
an element that interprets a named individual. The consistency verdict
already relies on this correspondence and on the tableau being sound and
complete for `O` (equality blocking without inverse roles, pairwise blocking
with them; nominals with inverse roles and number restrictions are
refused).

A subsumption `A ⊑ B` fails in the ontology iff some model has an element
`e ∈ A \ B`. `Tableau::classify` tests it by the satisfiability of `O` plus
one fresh root labelled `{A, ¬B}`; the root carries no nominal and no
`__O__`. Soundness of a refutation (the root set unsatisfiable): every
expansion step is a consequence of `O` and the root label, and a branch
closes only on a clash, so a closed search proves that no model has an
element in `A \ B`. Completeness (a found completion graph refutes the
subsumption): a clash-free complete graph unravels into a model of `O` in
which the root is in `A` and not in `B`. A rule clause fires only at
`__O__` nodes, which are the nominal roots and the nodes merged into them;
if the root is merged with a nominal it becomes that named individual and
the rules apply to it, otherwise it is an anonymous element and the
DL-safe rules do not constrain it. Conversely, given a model with
`e ∈ A \ B`, the model-guided construction maps the root to `e` and the
nominal roots to the named individuals; labels added at the root are true
at `e` (rules add none there unless the root is merged with a nominal, and
then `e` is that individual), so the search reaches a clash-free leaf. The
same argument with the root label `{A}` covers unsatisfiable classes.
Candidate pruning in `Tableau::classify` only skips a `B` that is absent
from the root label of a model of `{A}`, which that model refutes; on the
nominal path the tableau records no dependency sets, so every remaining
candidate is tested. The worker runs with the label cache and pseudo-model
shortcuts off (`KM_TAB_CACHE`, `KM_HT_CACHE`, `KM_HT_PMMERGE` removed).

The inert-sort release (docs/NOMINALS-CB.md section 6, "Inert object sorts
in the rule checker") stays on: its conditions (B) and (H) read only the
clauses that mention a released definer, and the root label `{A, ¬B}` of
named classes mentions none, so the model correspondence of that argument
holds for `O` plus the root and every test keeps its verdict.

The published taxonomy therefore equals the taxonomy of the ontology with
its rules, for the named classes of the input, under the assumptions the
consistency verdict already made: the frontend clause set and the rule
encoding are faithful, and the tableau is sound and complete on its input.
The CB taxonomy of the rule-free part is no longer consulted on these
inputs; since the rule-free ontology entails a subset of what the
ontology with rules entails, it adds nothing to an exact rule-aware answer.

### Lean obligation

The inert-sort release on this path is checked in Lean when
`KM_RULES_INERT_LEAN_CHECKER` is set (2d5c28b1,
`WireInertSortRelease.check_sound`): the certificate is written inside
`rules_consistency`, so it covers every worker call of both schedules, and
the classification tests add only roots labelled with named classes, which
are reserved concepts, so `release_equisatisfiable` (any side theory over
reserved concepts) covers them. Nothing else on this path is checked in
Lean. The rule worker refuses every
`KM_HT_LEAN_*` checker ("HT Lean certification cannot publish the
unchecked rules-consistency route"), and the Lean clause language has no
O-guarded rule clause. To cover the path, Lean would need (1) a semantics of
O-guarded DL-safe rule clauses over the named-individual nominals and a
proof that it matches the DL-safe semantics, (2) a certificate format for
`Tableau::classify` on the rule input (a closed tableau per accepted
subsumption and unsatisfiable class, and a finite blocked completion graph
per refuted candidate, checked as a pre-model with equality or pairwise
blocking), and (3) the frontend translation, which is outside Lean for every
route (docs/CERTIFICATION-ROADMAP.md). I did none of these.
(1) and (2) are done in "Lean coverage" below; (3) remains open.

### Evidence

`results/agents/2026-10-30/fr282-dropped-rules/README.md`: the 400
generated `gen_finite_rules.py` seeds against HermiT with grounded
built-ins, the 2026-10-29 rule probes, the integration test
`engine/tests/rule_taxonomy_nominal.rs`, and timings on 7278 and 3726
(which do not take this step: their rules reach no class query).

## Lean coverage (2026-10-30, v1.5.5)

Until v1.5.4 the rule worker (`KM_RULES_CONSISTENCY`, `KM_RULES_CLASSIFY`,
the clausal `Tableau` of `tableau.rs`) refused every Lean checker: the
clause language of the HT certification has no O-guarded rule clause. The
only Lean check on the route was the inert-sort release of its input
(`RulesInertSortRelease.lean`, docs/NOMINALS-CB.md section 6). With
`KM_RULES_LEAN_CERT=<dir | file.json>` and
`KM_RULES_LEAN_CHECKER=<lean/.lake/build/bin/rules-cert-check>` the worker
now writes one certificate per published answer and publishes the answer
only when the Lean checker accepts it.

### Semantics (`lean/ContextCalculus/RulesRouteSemantics.lean`)

The worker input is one list of hypertableau clauses over the atoms of
`ContextCalculus.Hypertableau` (concept literals, roles, existential
obligations, equality), a list of nominal concepts `{a}` (one per named
individual, `__nom__a`) and the guard concept `O` (`__O__`). The checker
classifies each clause:

- an *introduction clause* `{a}(x) → O(x)` with `{a}` a nominal;
- a *rule clause*: its body contains a guard atom `O(v)`; then `O` occurs
  nowhere else in it, never negated, and every variable of the clause has a
  guard atom;
- an *ordinary clause*: `O` does not occur.

`encodingOK` checks these conditions, that `O` is not a nominal, and, when
a rule clause exists, that every nominal has an introduction clause.
`decode` turns the list into a knowledge base `KB` of ordinary clauses,
rules (rule clauses without their guards) and nominals. Its DL-safe
semantics (`DLSafeModel`): every nominal denotes exactly one element,
every ordinary clause holds under every assignment, and every rule holds
under every assignment of *named elements* (elements of some nominal) to
its variables. `O` is not interpreted.

Proved (no `sorry`, axioms `propext`, `Quot.sound`, and for the checkers
also `Classical.choice`):

- `clauseModel_of_dlSafeModel`: a DL-safe model, with `O` interpreted as
  the named elements, is a model of the guarded clause list with singleton
  nominals.
- `dlSafeModel_of_clauseModel`: a model of the guarded clause list with
  singleton nominals is a DL-safe model of the decoded knowledge base.

So the guarded clauses are exact for DL-safe rules: consistency,
subsumption and unsatisfiability under the DL-safe semantics coincide with
the same notions for the clause list read in first-order logic with
singleton nominals (`entailsSub_of_clausal`, `unsatConcept_of_clausal`,
`not_consistent_of_clausal`, `not_entailsSub_of_clauseModel`,
`not_unsatConcept_of_clauseModel`), for concepts other than `O`. Merged
nominal nodes need no separate treatment: a merge is an equality between
elements, and named is a property of elements.

### Certificates

Refutation (`RulesRouteRefutation.lean`). The closed tableau of the
careful expansion, as the worker ran it. A test with root label `L` starts
with node 0 carrying `L` and node `k + 1` carrying the `k`-th nominal
(`Tableau::find_model`). A proof node is a list of steps followed by an
end. Steps: `horn` (a clause with one head atom whose body holds under the
given assignment adds its head; an equality head merges the two nodes),
`witness` (an obligation `∃r.C` at `s` gets a fresh node), `nominal` (two
nodes carrying the same nominal merge). Ends: a clash `C, ¬C`, a clause
with an empty head whose body holds, or a split on a clause whose body
holds, with one sub-proof per head atom. A merge copies the facts of the
removed node to the kept one; the index that finds them is untrusted.
Loop-back alternatives of the pairwise path are not recorded: the fresh
successor alone is a sound step.

Model (`RulesRouteModel.lean`). A finite interpretation: labels (positive
concepts) and successor edges of each element; concepts are the positive
labels, negative literals the complement. `FModel.check` evaluates every
clause under every assignment (variables bound along body role atoms,
values drawn from recorded successors, predecessors or concept
extensions, all verified complete against the edges and labels) and
checks that each nominal labels exactly one element. The worker builds the
model from the completion graph, as it is or with every blocked node
folded onto its blocker; a Rust pre-check (`model_satisfies`, the same
evaluation) picks the first that is a model. A graph that is neither gives
no certificate.

Answer (`RulesRouteCertificate.lean`). Clause list, nominals, `O`, the
queries, the published consistency flag, unsatisfiable classes and
subsumptions, premises, refutations (claim `inconsistent`, `unsat A` or
`sub A B`, root `[]`, `[A]` or `[A, ¬B]`) and models with witnesses
(concept, element). Proved statement, `WireRulesCertificate.check_sound`:
if `check` accepts the document `w`, every premise subsumption and premise
unsatisfiable class is entailed under the DL-safe semantics of
`kb = decode O nominals ontology`, then

- `consistent = true` iff `kb` has a DL-safe model (non-empty domain);
- for every query `A`: `A` is listed unsatisfiable iff `A` is
  unsatisfiable in every DL-safe model of `kb`;
- for all queries `A ≠ B` with `A` not listed unsatisfiable: `(A, B)` is a
  published subsumption iff `A ⊑ B` holds in every DL-safe model of `kb`.

Building blocks: `refutation_inconsistent`, `refutation_unsat`,
`refutation_sub` (an accepted refutation from the corresponding root
entails the claim) and `FModel.check_sound` (an accepted model is a model
of the clause list, so of `kb`; an element carrying `A` and not `B`
refutes `A ⊑ B`).

### The two schedules of the rule taxonomy

`KM_RULES_CLASSIFY` alone: every published entailment has a refutation
recorded by its own test and every non-entailment a model; the certificate
has no premises. Completion with `KM_RULES_CLASSIFY_KNOWN` (`set_known`):
the pairs and classes taken from the CB taxonomy appear as
`premise_subsumptions` and `premise_unsatisfiable`, and the theorem above
is relative to them; the CB taxonomy has its own certificates
(`run-cb-certification-gate.sh`) but no theorem composes the two yet. The
models never depend on premises. Pairs that the transitive closure adds
without a test receive one more recorded test before the certificate is
written.

### Wire-up

- `KM_RULES_LEAN_CERT` selects the careful expansion (the recorder follows
  it, without `KM_TAB_CAREFUL_INC` and `KM_TAB_CAREFUL_ORDER`) and refuses
  `KM_HT_CONTRA`, which adds contrapositive clauses the certificate would
  have to state.
- The worker fails closed: with `KM_RULES_LEAN_CHECKER` set, a rejected
  certificate, an answer without one (a refutation the recorder lost, a
  completion graph that folds to no model) or a checker that cannot run
  ends the run without an answer. `KM_RULES_LEAN_CERT` alone writes the
  certificates without checking them.
- An `KM_HT_LEAN_*` request on the rules route is served by these
  certificates when both flags are set and refused otherwise.

### What the frontend is assumed to do

The certificate is about the clause list the worker receives. Outside the
boundary, as for every other route: OWL parsing and normalisation, the
conversion `cb_to_ht::convert` (ABox as nominal facts, rules as guarded
clauses, `DifferentIndividuals(a b)` as `{a}(x) ∧ {b}(x) → ⊥`), the
inert-sort release (checked by its own certificate), and rules the
conversion omits (reported as `DROPPED`). Built-ins: the worker language
has none. The finite-rule grounding (`data_rules::lower_finite_rules`)
binds every data variable of a rule to each value of a finite set of
asserted literals, evaluates the built-in conjunction on each tuple in
Rust, drops refuted tuples, declines the rule when an evaluation is
deferred, and turns satisfied tuples into rules over constant data atoms.
The assumption is that this set contains every value a data variable can
take where the body holds and that the evaluation is the XSD/SWRL
semantics; neither is checked in Lean. The checker verifies only the
ground clauses that result.

### Evidence

`results/agents/2026-10-30/lean-rules-route/README.md`: the gate run
(`lean/run-rules-certification-gate.sh`), the 400 `gen_finite_rules.py`
seeds with the checker on, and the cost of emission and checking on
ore_ont_7278.

## Historical precheck design and corpus investigations

KM supports SWRL DL-safe rules through the **ABox-seeded HT consistency
precheck** (`KM_HT_RULES`, default on). A rule fires only over *named
individuals* (DL-safety: every rule variable is `__O__`-guarded, and every
`Ind(a)` term is pinned by `__nom__a`). The precheck is one-sided: it seeds the
ground ABox as nominal nodes, fires the representable rules, and short-circuits
to **inconsistent** on a clash; otherwise it falls through to normal TBox
taxonomy classification. Dropping a rule from this precheck is sound — a lost
constraint can lose an inconsistency, never invent one.

## The rule pipeline

| stage | file | role |
|-------|------|------|
| parse | `frontend/parse.rs::parse_rule_atoms` | AST rule atoms; drops the whole rule on a Data/BuiltIn/DataRange atom |
| profile | `frontend/profile.rs::rule_atoms` | counts `unsupported_rule_axioms` (the semantic probe) |
| contract | `frontend/mod.rs::collect_rules` | `parsed == source` gate; converts to `JRule` or DECLINES |
| encode | `orchestrate/cb_to_ht.rs::build_rule_clause` | rule → HT clause; fires or defers |
| reason | `tableau.rs::rules_consistency_verdict` | seeds ABox, fires rules, one-sided clash check |

## The three tiers (rule atom shapes)

- **FIRED** — every atom is a `ClassAtom` over a *named* class, an
  `ObjectPropertyAtom`, or a `SameIndividualAtom`. Terms may be variables or
  named individuals.
  - A body `SameAs(u, v)` guard unifies u and v onto one Subst variable
    (union-find over rule terms); both `__nom__` pins land on the shared node.
  - A head `SameAs(u, v)` conclusion emits `HAtom::Eq{u,v}` (the rule derives the
    equality; the tableau o-rule then merges).
- **DEFERRED** — the rule additionally carries a `DifferentIndividualsAtom`. The
  fast Ht tracks no node distinctness (`HAtom` = Concept/Role/Eq/Exist only), so
  a `u ≠ v` guard has no sound encoding. `build_rule_clause` returns `None` and
  the rule is dropped (counted in `dropped`). It is **carried through
  `collect_rules`** (does NOT decline the route) — declining would forfeit the
  fired rules that detect the 2669/15516 clash.
- **DECLINED** — the rule has a `DataPropertyAtom`, `BuiltInAtom`,
  `DataRangeAtom` (a concrete-domain obligation with no DL encoding) or a
  `ClassAtom` over a complex class expression. The parser omits the AST rule, so
  `parsed < source` in `collect_rules` and the whole rule-aware route is
  rejected. KM declines rather than silently approximating a datatype rule.

## ORE `DLSafeRule` corpus (6 ontologies)

Gold: Konclude cannot parse `DLSafeRule` (exits 0 with empty output), so the
adjudicated gold is HermiT on a cleaned core (see `CONTESTED-GOLD.md`).

| ont | verdict | KM |
|-----|---------|----|
| 2669  | inconsistent | inconsistent ✓ (5 pure rules fire; 3 Diff deferred) |
| 15516 | inconsistent | inconsistent ✓ (2 pure rules fire) |
| 10906 | inconsistent | closed via the ABox/datatype precheck |
| 13129 | consistent | consistent ✓ |
| 12451 | consistent | — |
| 10860 | inconsistent | **automatic default certificate; full sweep certified** (see below) |

### ORE 10860 — the 17-shape breakdown

The 17 `DLSafeRule` axioms partition into:

| count | shape | tier |
|-------|-------|------|
| 8 | Class + Role (some Class/head args are named individuals) | FIRED |
| 5 | Class + Role + `DifferentIndividualsAtom` | DEFERRED |
| 4 | + `DataPropertyAtom` / `BuiltInAtom` (`greaterThan` on dates, `hasClass`, `isSubClassOf`) | DECLINED |

Four rules carry built-ins, so the generic rule worker can directly encode only
13 of 17 rules. A direct
source audit on the frozen corpus file (SHA-256
`480139a6018bc4eb0d35e47edf00a6d257dd87137c1d0f93a27021cf154f4a2d`)
narrows the live obligation substantially:

- Three rules compare access/authorization dates or shift times. The ontology
  contains zero `DataPropertyAssertion`, zero `SubDataPropertyOf`, and zero
  `EquivalentDataProperties` axioms. No named binding can satisfy either data
  atom in these DL-safe rule bodies, so all three rules are provably inert;
  evaluating `swrlb:greaterThan` is unnecessary for this ontology.
- One rule uses the legacy Protégé 3.3 built-ins `abox:hasClass` twice and
  `tbox:isSubClassOf` once. This is not the similarly named modern SWRLAPI
  axiom-query interface. The original Protégé 3.5 distribution and bytecode
  establish the operative contract:
  - `hasClass(i, C)` calls `P3OWLUtil.getOWLClassesOfIndividual`, which reads
    `individual.getRDFTypes()` and retains named classes. It therefore ranges
    over asserted named RDF types, not inferred memberships.
  - `isSubClassOf(C, D)` calls `P3OWLUtil.isOWLSubClassOf(..., true)`, which
    tests membership in `C.getSuperclasses(true)`. It follows the asserted
    superclass graph transitively; `isDirectSubClassOf` is the separate
    non-transitive built-in.

Under that exact contract, the meta-rule adds no new firing in 10860. Every
`hasRelatedEHRSection` assertion from a legal authorization targets the named
individual `diagnosis`, whose asserted named type is `Diagnosis`. Among the
asserted types of all `hasEHRSectionPart` targets, the only type below
`Diagnosis` in the transitive asserted superclass graph is `Diagnosis` itself,
on the same individual `diagnosis`. The rule's two section variables must
therefore denote the same individual whenever its built-in conjunction holds.
The ontology already contains the ordinary supported rule with that exact
same-section guard and the same `hasR2RRelation` head. The legacy meta-rule is
subsumed by that rule and is provably redundant for this source.

The frontend contains a fail-closed certificate for the three inert data
rules and the subsumed legacy meta-rule. It verifies the relevant assertions,
asserted type sets, transitive named-superclass relation, and the subsuming
ordinary rule from the parsed source; synthetic negative controls revoke the
certificate when a data fact is added or the section targets differ. On the
frozen source it certifies exactly 4 rules and carries the other 13. It remains
opt-in (`KM_RULE_REDUNDANCY_CERT=1`) when considered alone.

The ontology is nevertheless inconsistent. A supported rule has a complete
explicit named-ABox match and derives a second `hasR2RRelation` target for a
situation asserted to have unqualified exact cardinality one on that role. The
existing and derived targets are explicitly different. The rule's
`DifferentIndividualsAtom` is also forced by asserted memberships in explicitly
disjoint classes. HermiT job `49718396` independently rejects the extracted
core as inconsistent. Commit `4703045` adds a one-sided finite matching
certificate that accepts only this exact shape and fails closed on unsupported
atoms, missing body facts, absent difference evidence, and qualified
cardinalities. Plain `km classify` returns `consistent:false` in 0.02 seconds
locally. IBEX sanity job `49721625` confirms 0.0403 seconds and 10.31 MiB;
full sweep `49721626` and audit `49734184` certify the route across all 592
ontologies.

## Soundness note

Firing a *subset* of DL-safe Horn rules is a sound under-approximation for
consistency and classification (fewer constraints ⇒ a superset of models ⇒ a
subset of entailments). KM does NOT partial-fire a DECLINED ontology, but the
DEFERRED (Diff) drop within an otherwise-representable ontology relies on exactly
this: a dropped Diff rule can only lose a clash, never fabricate one.
