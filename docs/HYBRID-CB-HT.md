# Hybrid CB / HT reasoner — design and evidence

Status: design + head-to-head evidence consolidated 2026-06-17. Routing options
under full-corpus evaluation on IBEX. This document is the consolidation of the
KM_HT (HermiT-style hypertableau) line and its integration into the main
reasoner.

## 1. Why a hybrid

KM has two general-purpose engines with **complementary** strengths:

- **CB** — the consequence-based disjunctive-context calculus (`engine.rs`,
  `kobayashi-marust`). Lean-certified sound + complete for SROIQ-sans-datatypes;
  in production wrapped by the elc EL fast path, the absorption portfolio, and
  the KM_TAB label-caching tableau race. Current ORE coverage: 564 ok.
- **HT** — the ported HermiT-style hypertableau (`hypertableau.rs`,
  `tableau_cli` under `KM_HT=1`, driven through `cb_to_ht.convert`). Anywhere
  blocking + CDCL search. Gated research engine, never in production.

The two do **not** dominate one another. On the ORE corpus (584 onts with a
gold signature), joining the per-ont CB results (`cmp2_res`, reasoner=km, 600 s)
with the ofn-driven HT sweep (job 47566667) gives:

| bucket  | count | meaning                                     |
|---------|-------|---------------------------------------------|
| BOTH    | 429   | both solve correctly                        |
| CB_ONLY | 129   | CB solves, HT times out / incomplete        |
| HT_ONLY | 4     | **HT solves, CB times out** (4604, 9635, 11460, 15491) |
| NEITHER | 22    | the residual hard set (disjunction family + giants) |

Union solvable = **562** vs CB-alone 558 in this measurement. The four HT_ONLY
onts are precisely the central-core-growth / context-explosion ontologies CB
blows up on (task #52): CB hits the 20 GB memcap or the wall, HT finishes. HT is
also **faster** on 45 of the 429 both-solve onts (e.g. 6246: CB 252 s -> HT
0.01 s; 868: 79 s -> 9.8 s), because the hypertableau never materialises the
context closure CB pays for.

## 2. HT correctness on the routable fragment (the safety question)

A naive flat-set comparison of HT output vs gold is wrong: gold signatures are
the output of `ore_canon.canonicalize` (transitive closure + SCC condensation +
`is_internal` filtering), and HT emits the full closure. Comparing HT through the
**same** canon (runner `engine/py/ht_check.py`, job 47570686) over the 47
flagged onts + controls settles it:

- **HT is SOUND.** unsound = 0 on every routable ontology measured (no
  wrong-positive subsumption). The "3 unsound" from the old flat-canon sweep were
  artifacts of the buggy `loc()` (slash-localname split + `_hasValue` datatype
  surrogates leaking in).
- Most "incomplete" were also runner artifacts: real classes whose local names
  start with `Q_` / `__` or contain `:` (`Q_Fever`, `_MGI:101757`,
  `__adipocyte_glucose_uptake`) were wrongly dropped by an `is_internal` that
  filtered the IRI instead of the internal name with the `named_iri` escape.
  Fixed to match `owl_classify` exactly.
- **HT is INCOMPLETE on a genuine subset** (6433, 8864, 12009, 5566, 7216, 8982,
  6817, 15098, 14312, ...). Root cause = subset (label-⊆) blocking is incomplete
  for ALC with live disjunctions (the 5303 family); `classify`'s model-based
  possible-subsumer pruning then never tests the missed pairs. This is the same
  hard residual documented in `project_km_5303_diagnosis` and
  `project_km_family_diagnosis` — it has no cheap structural fix and no available
  search lever closes it (option-3 grid job 47569737: all family onts timeout
  under learning/restarts/absorption).
- The 6 `DIFF_consistency` onts (13912, 443, 6720, 7052, 8941, 15288) are all
  gold-**inconsistent**. The CB pipeline catches them with the frontend
  `abox_inconsistent` precheck (and the datatype oracle) **before** any engine
  runs, so they never reach HT in the real pipeline.

**Conclusion: HT is sound but not complete on the routable fragment, and we have
no general structural rule that separates the HT-complete onts (15491, gold-clean
with disjunctions) from the HT-incomplete ones (8982, incomplete with
disjunctions).** Disjunction density does not separate them. This rules out any
routing that *replaces* a CB-correct answer with an unvalidated HT one.

## 3. Routing fragment guard (general, never ontology identity)

`cb_to_ht.convert` reports `dropped`, `fenced`, `inverse`, `number`, `nominals`.
HT is routable iff the conversion is **lossless** (`dropped == 0 and fenced == []`)
**and there are no inverse roles** (inverse needs the double-blocking the port
lacks -> unsound risk). Qualified number restrictions (ALCQ, no inverse) ARE
routed: `cb_to_ht` encodes them with slot-fillers + eq-merge.

Datatype / concrete-domain content is opaque to `cb_to_ht` (hasValue is encoded
as ordinary surrogate concepts, so `dropped` stays 0), and HT does no datatype
reasoning. Datatype onts are therefore HT-incomplete (5940, 8135). Because HT is
only ever consulted as a fallback for a CB failure (below), this cannot regress a
passing ontology; the guard still excludes them where detectable.

This is a **structural fragment test only** — it reads the converted clause set,
never an ORE id or a gold-derived list.

## 4. The monotone-safe hybrid (recommended default)

CB is the certified sound + complete engine. The hybrid keeps CB primary and uses
HT only to fill CB's coverage gap:

> Run CB (the full production path: elc -> absorption portfolio -> KM_TAB race).
> Concurrently run HT (niced, single-threaded, low memory) **only on routable
> ontologies**. Accept HT's answer **only if CB fails to produce one** (timeout
> or OOM).

Why this is safe with zero regression risk:

- Any ont CB solves keeps CB's correct answer; HT incompleteness / consistency
  misses cannot touch it.
- On a CB timeout/OOM (already a non-answer today), HT is sound, so the worst case
  is an incomplete answer on an ontology that was a timeout anyway — never a
  regression — and the best case (4604, 9635, 11460, 15491, and any other routable
  CB-timeout HT can classify) is a full gold-clean classification, a coverage gain.
- HT is single-threaded and memory-light, so it racing alongside CB does not
  threaten the job memcap (the same property the existing KM_TAB racer relies on).

## 5. Routing options — full-corpus result (IBEX, 587 onts, 240 s / 20 GB)

Both gated options were swept against the same build's base arm (`KM_ABSORB=1`,
no HT), gold = byte-identical canonical signature. Jobs 47570890 (base),
47571283 (fallback), 47571284 (race).

| arm                    | ok + gold-MATCH | vs base                       | regressions |
|------------------------|-----------------|-------------------------------|-------------|
| base (CB only)         | 558             | --                            | --          |
| **fallback** (KM_HT_MODE=fallback) | **562** | **+4: 4604, 9635, 11460, 15491** | **0**       |
| race (KM_HT_MODE=race) | 559             | +3 (4604, 9635, 15491)        | 2 (868, 8486) |

**Fallback wins decisively.** It recovers all four central-blow-up / context-
explosion ontologies CB times out on, with **zero regressions** -- the monotone
guarantee of section 4 held exactly. Race is strictly worse: it captures fewer
gains (it loses 11460 -- race accepts HT only if HT finishes before the per-ont
wall, and on this central-blow-up ont the niced HT is slowed by CB's memory
pressure and misses that window, whereas fallback's KM_HT_BUDGET_S gives HT the
full pre-timeout window) and it regresses 868 and 8486. Those two are
large-closure onts (868 emits 14.8M subsumptions): in race mode HT wins, CB is
killed mid-serialisation, and canonicalising HT's large output under the
concurrent racer's memory/time pressure trips the per-ont wrapper -- a transient
(868 re-runs clean standalone), but a fragility race mode introduces and fallback
never does (fallback lets CB finish and only consults HT on a genuine CB failure).

**Decision: KM_HT_MODE=fallback is the new main hybrid.** It is the
zero-regression coverage win. Race is not deployed.

The base arm here (558) is a leaner config than the fully-portfolioed deployed
production (564 = base + absorption portfolio + DISJ_INT auto-route); the +4 HT
onts are central-blow-up timeouts that the portfolio levers do not target
(4604/11460 are the open task-#52 set), so fallback composes additively on top of
the full production config. A confirmation sweep under the full portfolio config
is the productionisation step.

## 6. Deployment

Enable on the benchmark/production config by adding to the engine env:

```
KM_HT_RACE=1            # turn on the HT racer
KM_HT_MODE=fallback     # monotone-safe (default if unset)
KM_TAB_BIN=<.../tableau_cli>   # the KM_HT-capable binary (already set in prod)
```

`KM_HT_BUDGET_S` (default 225) is the CB wall before HT may fill on a routable
ontology; `KM_HT_NICE` (default 1) the racer priority. Everything is inert
without `KM_HT_RACE`.

## 6. Artifacts

- `engine/py/ht_check.py` — canon-faithful HT correctness runner (the section-2
  measurement).
- IBEX `km-htport` (`$HP=/ibex/scratch/hohndor/km-htport`): `tableau_cli` with
  `KM_HT`, `cb_to_ht.py`, `ht_ofn_runone.py` (sweep runner), `sweep_ofn/`
  (job 47566667), `htcheck/` (job 47570686), `h2h_joined.jsonl` (the join).
- Head-to-head join: `h2h_analyze.py` over `cmp2_res` (CB) + `sweep_ofn` (HT).

## 7. Complementary-definer elimination (EMELIM)

`cb_to_ht::elim_complements` (default on; off under `KM_HT_CARD` card
definitions, DL-safe rules, or `KM_NO_HT_EMELIM`) folds a complementary pair
`B ≡ ¬A`, given as `⊤ → A ∨ B` and `A ∧ B → ⊥`, into the single concept `A`:
both clauses are dropped and `B` is replaced by `¬A` in every other clause.

The worker matches a body literal against node labels by sign. A body literal
`¬A(t)` therefore fires only when the node carries an explicit `¬A` label, and
once `⊤ → A ∨ B` is gone nothing derives `¬A` from the failure of `A`. Up to
v1.5.4 the fold wrote each body occurrence of `B` as such a literal, and its
completeness guard (keep the pair if a side drives a consequence and is not
Horn-derivable) let a Horn-derivable side through. That loses every
consequence the excluded middle supplied when the other side was refuted. The
reproducer (2026-10-29):

    EquivalentClasses(:Has DataMinCardinality(1 :d))
    EquivalentClasses(:Two DataMinCardinality(2 :d))
    EquivalentClasses(:No ObjectComplementOf(:Has))
    EquivalentClasses(:AtMostOne ObjectComplementOf(:Two))

The frontend clause set is exact. Its complements `Q_3 ≡ ¬Has` and
`Q_4 ≡ ¬Two` are both Horn-derivable (`No → Q_3`, `AtMostOne → Q_4`), so both
folded into `No → ¬Has`, `¬Has → No`, `AtMostOne → ¬Two`, `¬Two → AtMostOne`.
The test `{No, ¬AtMostOne}` then has the clash-free model `{No, ¬Has,
¬AtMostOne}`: `¬AtMostOne` should force `Two` (through `Q_4`'s excluded
middle), whose two witnesses give `Has` and the clash. `ht_general` and
`tableau` reported only `Two ⊑ Has`. Cardinality plays no part: the object
spelling and the cardinality-free `SubClassOf(:Two :Has)`,
`SubClassOf(:T2 :Two)` miss the same subsumption.

The fold now writes a body occurrence `B(t)` as the head literal `A(t)`:
`B ∧ Body → H` and `Body → A ∨ H` are the same clause under `B ≡ ¬A`, and the
second has the positive-body shape for which the hypertableau is complete
(Motik, Shearer and Horrocks 2009). A head occurrence becomes `¬A(t)`, a
constraint that clashes with `A(t)` as `A ∧ Body → H'` would. A clause with
`A(t)` on both sides is a tautology and is dropped. Each output clause is then
equivalent to its source clause once `B` is defined as `¬A`, and the two
dropped clauses are valid under that definition, so the folded set and the
source set have the same models up to the value of `B` and the same
subsumptions over the remaining names. If a moved literal's variable would be
unbound (neither the centre nor in the remaining body), the fold returns the
source clause set unchanged. The pair guard stays as a scheduling heuristic
(a folded pair whose side drives a consequence re-creates the excluded middle
as a head disjunction); completeness no longer rests on it.

A second, latent gap: when both sides were non-internal the fold eliminated
the larger id, a named class. The classifier still queries that id (`{X, ¬B}`),
which no clause mentions after the fold, so every subsumption into `B` would be
lost. The fold now eliminates only internal definers.

Routes. The fold runs on every HT conversion with no card definitions and no
rules. Under `KM_TRIGGER_ABSORB` (`production_all*`, `certified_*`,
`ht_bridge`, `ht_full`) `normalize_signed_trigger_clauses` already moved the
negative body literals into the head, which is why those routes answered the
reproducer correctly; `certified_card_proxy_abox` runs an HT arm only for a
card candidate, which requires card definitions and so disables the fold.
Forced `ht_general`, `tableau` and `ht_features` answered the reproducers
incompletely; `ht_qo`, `ht_shoq` and `nominal_ni_*` ran the same fold without
the literal movement (their structural gates or the CB arm decided these
small inputs). None of these is an automatic route under either routing
policy. Measurements are in
`results/agents/2026-10-29/ht-card-complement/`.

## 8. Bridge `≤0` restrictions and inverse predecessors

Defect. The Konclude bridge (`engine/src/konclude_ht/bridge.rs`, `Builder`)
built `≤0 R.C` as a `CCATMOST` concept with parameter 0, and `¬≥1 R.C` as a
negated `CCATLEAST` with parameter 1, which the saturation reads as the same
`≤0` count. The ported saturation's critical at-most test
(`is_critical_atmost_concept_descriptor_insufficient`, saturation/s09.rs)
counts only the `R`-successors a saturated node links to. A neighbour that is
the node's predecessor, reached over the inverse of `R`, is never counted, so
the node stayed sufficient and its satisfiability was published from the
saturation. On `D ⊑ ∃s.⊤`, `⊤ ⊑ ≤0 s⁻.D` (HermiT: `D` unsatisfiable) the
source-TBox bridge answered `D` satisfiable. The automatic route took the
bridge for fresh generator seed 1241 (`D ≡ ∃s.∃t.B`, `⊤ ⊑ ≤0 s⁻.D`,
`Q3 ≡ ¬C`) and published `D ⊑ Q3` instead of `D` unsatisfiable;
`production_all` and `ht_bridge` did the same. `KM_HT_NO_SATURATION=1`
answered correctly, which places the miss in the saturation, not in the
completion tableau. The clause translation (`KM_NO_SOURCE_TBOX=1`) was
already right, because the frontend clausifies `≤0 R.C` as `R(x,y) ∧ C(y) →
⊥`.

Fix. Konclude's ontology builder never produces a `CCATMOST` with parameter
0: it builds `≤0 R.C` as `∀R.¬C` (see the note on
`generated_successor_filler_negation`, model/op.rs). The bridge builder now
does the same in `atmost_q` and `atmost` (`≤0 R ≡ ∀R.⊥`), and `atleast_q`
builds `≥1 R.C` as `∃R.C`, so `¬≥1 R.C` becomes `∀R.¬C` as well. These are
equivalences, so the translated terminology has the same models. The
universal rule propagates to predecessors in both the saturation and the
completion, which covers the inverse case. No tableau rule changes, and the
bridge has no Lean model (docs/CERTIFICATION-ROADMAP.md), so no Lean surface
changes.

Fixtures: `engine/tests/fixtures/bridge_atmost_zero/`, run by
`engine/tests/bridge_atmost_zero.rs` on auto, production_all, ht_bridge and
ht_bridge with `KM_NO_SOURCE_TBOX=1`. Measurements:
`results/agents/2026-10-29/cb-inverse-top/`.

Open: clause-translation `≤2` with a counted predecessor. The forced clause
translation (`KM_NO_SOURCE_TBOX=1`) misses the eight `≤2` probes in
`engine/tests/bridge_atmost_predecessor.rs` (ignored test
`ht_bridge_clause_translation_known_misses`). A temporary trace of
`is_critical_atmost_concept_descriptor_insufficient` (saturation/s09.rs) and
`mark_atmost_restricted_ancestors_as_insufficient` (saturation/s08.rs) on
`inv_atmost2_u_pred` showed the same input on both paths: the same `≤2`
concept with qualifier TOP, the same linked successors (count 2, found 2,
nothing mergeable), the same verdict (not insufficient, ancestors possibly
critical), and the same backward-propagation roles at the ancestor marking.
The saturation node flags and the unknown-subject count also matched. The
one difference is the role object: the clause translation gives the at-most
the named role `__inv__s`, while the source TBox gives the wired inverse of
`s`. Building `__inv__s` as that inverse object made the at-most input
identical and did not fix the miss. `KM_HT_NO_SATCACHE=1` (saturation on,
saturation-node coupling in the residue probes off) answers all eight, so the
miss is in the completion's expand-from-saturation and caching-blocking
coupling, not in the saturation's at-most rule or the translation. The fix
belongs to that coupling (v1.5.5 work); no automatic route uses the clause
translation for an input with a `≤2` restriction.
## 9. Subset blocking and backward clauses

The worker's default blocking (mode 1, anywhere subset) blocks a node `w` by
an earlier node `w'` with `L(w) ⊆ L(w')`; the card arm's mode 5 (Konclude's
optimized blocking) adds a check for `∀` over an edge back to the predecessor.
When the model is unravelled, `w`'s position takes `w'`'s label and
successors, so it carries the gained literals `L(w') \ L(w)`. The code
described subset blocking as complete for ALC(H). It is not, as soon as a
clause body mentions a literal at a neighbour variable: `∃r.C ⊑ D` gives
`C(y) ∧ r(x, y) → D(x)`, and a gained `C` at `w` makes the predecessor need
`D`, which the tableau never derived because `w` was not expanded. Minimal
cases (2026-10-29, delta-debugged from the ALCHIQ seeds 103, 507 and 639):

    EquivalentClasses(:D ObjectSomeValuesFrom(:t ObjectUnionOf(:A ObjectComplementOf(:A))))
    DisjointClasses(owl:Thing ObjectAllValuesFrom(:t :D))

is inconsistent (every element needs a `t`-successor outside `D`, that is
without a `t`-successor), but `ht_general` answered consistent. With any
blocking that compares whole labels (modes 0, 2, 3, 4, 6) it answers
inconsistent; modes 1 and 5 do not. The `A ⊔ ¬A` filler is what makes the
gain possible: one node's label carries the chosen disjunct and the
recognition literal of `∃t.(A ⊔ ¬A)` depends on it. The data-range excluded
middle of `excluded_middle_of_complement_ranges` is the same mechanism: there
the gained literal is a data-range label such as `xsd:integer` at a
`d`-successor, which the recognition clause of `∃d.xsd:integer` reads, so
`H ≡ ≥1 d` was never classified under `∃d.xsd:integer ⊔ ∃d.¬xsd:integer`
(again correct under modes 0, 2 and 3, wrong under mode 1).

The rule (`SubsetGain` in `hypertableau.rs`). When the model is unravelled,
`w`'s position keeps its incoming edges and its edges to nodes other than its
own successors, and takes `w'`'s label and successors. Every clause instance
the tableau evaluated over a kept edge stays satisfied, because its head holds
at the neighbour or in `L(w) ⊆ L(w')`. Only a gained literal can create a new
instance, so a pair is admitted when no gained literal is relevant for a kept
edge `u -r-> w` (or `w -r-> u`):

- a literal at the neighbour variable of a body atom `r(x, y)` (or
  `r(y, x)`), for example `C(y)` in `C(y) ∧ r(x, y) → D(x)`;
- a literal at the centre of a clause with such a body atom (an instance
  centred at `w` itself);
- a cardinality filler on the number role `r` (both signs; the number and
  recognition rules count it at `u`), a cardinality marker (counted at `w`),
  and any nominal concept.

The position also takes `w'`'s existential obligations, but only copies of
`w'`'s successor edges. So, in addition (2026-10-30, "Inverse witnesses"
below), every existential `∃r.F` that `L(w')` triggers and that `w'`
witnesses only through an edge to a non-successor (the inverse edge to its
own predecessor) must be witnessed at `w`'s own predecessor over `w`'s
`r`-edge (`SubsetGain::back_need`, `back_witnessed`). This applies to every
pair, including equal labels, on the fragment with a fold certificate (no
first-class cardinality rules, no nominals).

A kept edge on a role of a clause with two or more neighbours or an equality
head (number restrictions, functional roles) forbids the pair, since an
instance centred at `w` could count that edge together with `w'`'s
successors, and a clause with a role atom between two neighbours forbids
subset blocking altogether. Modes 1 and 5 apply the rule to each candidate
pair. Because a node that is not yet blockable may grow successors, a node
whose predecessor is blocked is blocked too (indirect blocking; descendants
of a blocked node are not part of the unravelled model). The incremental
subset snapshot (`KM_HT_INCRBLOCK2`, set by `ht_general`), the persistent
index path (`KM_HT_INCRBLOCK`) and ancestor blocking do not check pairs, so
they run only when no literal is relevant and there is no inverse bridge;
otherwise the worker uses the checked anywhere scan. Equal labels gain
nothing, so the body-literal part of the rule never rejects a pair that
equality blocking would accept; the existential part can (see "Inverse
witnesses").

Falling back to a whole-label mode was measured and rejected: mode 4
(pairwise with indirect blocking) answers the minimal cases correctly but did
not finish seed 1 in 30 s, and mode 3 (pairwise on the positive core, no
indirect blocking) did not finish the seed-507 case; the search expands a
node's existentials before its disjunctions are decided, and an incomplete
label never equals a complete one. Certified runs (mode 6) are unchanged.

Scope. Before this change the automatic route published a wrong answer: the
ontology of `tests/ht_subset_blocking.rs::card_arm_subset_blocking_on_the_automatic_route`
(the seed-103 core, a qualified number restriction, an inverse pair and a
role chain over an asserted edge) is selected for `certified_card_proxy_abox`,
whose card arm (mode 5) answered `CONSISTENT 1` (5cc0bccf); HermiT and the
CB routes answer inconsistent. Without the class assertion on `b` the same
route aborted instead, on an eagerly evaluated `then_some(assertions[0])` in
the proxy-ABox certificate (`race.rs`), which this change also fixes.

Cost (2026-10-30). The checked pairs made the card arm about four times
slower on `ore_ont_205` and `ore_ont_7499` (`certified_card_proxy_abox`). On
7499 the search runs 1.04M steps instead of 0.65M, but blocking took 145 s of
the worker's 176 s (25 s of 48 s before): mode 5 recomputed every node on
every one of the 1.03M passes, and 112M candidate pairs reached `admits`
(0.85 µs each). Three changes cut it without changing any decision:

1. `admits` is split into `kept_edge_sets` (the per-node part: `two_hop`,
   counted kept edges, the literal sets of the kept edges) and
   `gain_irrelevant` (the per-pair part). The per-pair test skips literals
   outside `relevant_bits`, the union of every relevant set (they satisfy
   `k ∉ ⋃ relevant` already), and answers yes when `|L(wp)| = |L(w)|`,
   since every caller has already established `L(w) ⊆ L(wp)`, so the labels
   are equal and nothing is gained. Both are rewritings of the same formula
   `∀k ∈ L(wp). k ∈ L(w) ∨ k ∉ ⋃ relevant(w)`.
2. Modes 1 (when `SubsetGain` is not trivial) and 5 run incrementally under
   `KM_HT_INCRBLOCK2` (`Ht::checked_subset_recompute`), like the unchecked
   mode-1 snapshot. The status of node `n` in both scans reads only: `L(n)`
   and `n`'s in- and out-edges (`admits`, B2a), `pred` of `n`'s out-edge
   targets (`admits` skips successor edges), the labels and statuses of the
   candidate blockers `m < n`, and the label and status of `pred(n) < n`
   (B2a, indirect blocking). `Ext` already lowers `i2_lo` to every node
   whose label changes and to every new or removed node; with `edge_note`
   it also lowers it to the smaller endpoint of every added or removed edge,
   except that an edge to a node's own successor only lowers it to the
   successor, because the predecessor reads that edge nowhere (`admits`
   skips it, B2a reads only the edge to the node's own predecessor, which has
   a smaller id). `pred[t]` changes only when `t` is removed and its id is
   reused, and the edge to `t` is removed first. So every node below `i2_lo`
   has the inputs it had at the last pass, keeps its status and its
   postings, and an ascending pass over `i2_lo..nn` with the same predicates
   reproduces the full scan. The order in which candidates are tried, and
   the choice of the rarest posting list, change nothing: the result is the
   existence of an admitted superset, and every superset of `L(n)` is in the
   list of each literal of `n`. The post-pass that marks merged nodes blocked
   runs on the returned copy, as in the full scan, where merged nodes still
   serve as candidates.
3. Inside that pass `kept_edge_sets(n)` is evaluated once per node, and a
   node for which it rejects every pair is not searched. Each candidate
   blocker's relevant literals (`L(m) ∩ relevant_bits`, `Ext::cs_rel`) and,
   in mode 5, its `forall_idx` body concepts (`Ext::cs_fa`, the only
   literals B2a looks up) are cached when it is posted. The cache is invalid
   only when `L(m)` changes, which moves `i2_lo` to `m` or below and reposts
   `m`, or when another `SubsetGain` is in use, which a per-build id detects
   and answers with a full pass (`forall_idx` is fixed at construction).

`KM_HT_INCRBLOCK2_CHECK=1` compares every incremental pass with the full
`compute_blocked` and aborts on a difference. Measurements:
`results/agents/2026-10-30/subset-blocking-cost/`.

The slowdown of `ore_ont_7278` and `ore_ont_3726` (7.9 s to 33.7 s) has a
different cause. Their time is in the rules-consistency worker, which runs
the clausal `Tableau` of `tableau.rs`, not the native hypertableau, so no
blocking code in this section is involved. Since 5a9eaa77 the frontend
carries the 81 data-property assertions of 7278 as `DataHasValue` class
assertions (478 more clauses: 8,552 instead of 8,074) and runs a second
frontend pass (3726 publishes the same output and has the same 81
assertions). The v1.5.3 worker binary takes 26.9 s (7278) and 25.4 s
(3726) on the v1.5.4 input (`KM_TAB_BIN`), the same as the v1.5.4 worker.

With these changes the card arm takes 70 s on 205 and 61 s on 7499 (v1.5.3:
47 s and 44 s; v1.5.4: 178 s and 160 s, all one core). The rest of the
gap to v1.5.3 is the larger search the checked pairs require (1.04M
instead of 0.65M steps on 7499, propagation 28.6 s instead of 19.5 s),
which no exact change to the blocking computation can remove.

Lean coverage (2026-10-30). Before this change no Lean certificate covered
a subset-blocked answer. The HT gate's checkers certify the separate
certified search (`Ht::new_certified`, mode 6: full-label pairwise blocking
without indirect blocking, and its own Rust refutation search
`lean_refutation`); modes 1 and 5, and so `checked_subset_incremental`,
`Ext::edge_note_node`, `SubsetGain::kept_edge_sets` and `gain_irrelevant`,
never run on a certified path. The certified SAT side already treats a fold
as untrusted (`FiniteFoldCertificate.check_satisfiable` in
`HypertableauBlockingCertificate.lean` has no premise on the folds), so the
coverage reuses that design for the production terminal:

- `lean/ContextCalculus/HypertableauSubsetUnravelling.lean`:
  `SubsetUnravelling` holds a production SAT terminal (descendants of blocked
  nodes and merged nodes removed), its predecessor pairs, the blocking pairs
  the engine used, the root and the query seed. `materialize` builds the
  unravelling of this section (a blocked position takes the blocker's label
  and obligations and copies of the edges between the blocker and its
  successors; with `relabel = false` it keeps its own label instead).
  `check` requires every pair to be a subset pair with an unblocked blocker,
  the seed at the root, and `FiniteSatCertificate.checkSat` of the
  unravelling (every clause under every assignment, every obligation
  witnessed, no clash). Proved: `SubsetUnravelling.check_sound` (an accepted
  unravelling is a finite model of the certificate's clauses with the seed
  at the root), `check_not_unsatisfiable`, `check_not_entailsSub`,
  `WireSubsetUnravelling.check_sound`. No sorry; axioms propext,
  Classical.choice, Quot.sound. The pairs and the predecessor relation are
  untrusted, so the relevance condition (`SubsetGain`) and B2a are not part
  of the trusted base: the checker verifies directly what they are meant to
  guarantee.
- `KM_HT_SUBSET_MODEL_CERT=<dir>` writes every SAT terminal of modes 1 and 5
  of `Ht::consistent` as a `WireSubsetUnravelling`; the blocking relation is
  the one the search used (the incremental pass when it is on, compared with
  the full `compute_blocked` there as well). With
  `KM_HT_SUBSET_MODEL_CHECKER` naming `ht-subset-unravelling-check`, the
  worker returns no verdict when the terminal has no certificate or Lean
  rejects both the relabelled and the own-label unravelling. Not emitted
  (fail closed under the checker): first-class cardinality rules, nominals,
  role-chain composition, native ABox individuals, and a blocked node whose
  only admitted blocker is itself blocked or dropped.

What this covers: a SAT answer of a mode-1 or mode-5 run whose certificate
Lean accepts is a model of the worker's compiled clauses (`index.clauses`)
with the query seed. UNSAT answers of these modes do not depend on blocking
for soundness (blocking only withholds expansion), but they carry no
certificate. Not covered: the `consistent_with_snapshot` and
`resume_satisfiable_model` entries, and the card arm (its cardinality rules
are not clauses of the version-1 wire).

Findings (`results/agents/2026-10-30/lean-v155-coverage/`). On the
fixtures of `tests/ht_subset_blocking.rs` (seeds 507 and 639, route
`ht_general`, mode 1 and forced mode 5) every terminal is accepted, with up
to three blocking pairs, and `KM_HT_INCRBLOCK2_CHECK=1` aborted on none. On
the ALC seed corpus Lean rejected the relabelled unravelling on a share of
the folded terminals. In the inspected case (seed 2) the blocker satisfies
an existential `A ⊑ ∃u.C` through the inverse edge to its own predecessor,
not through a successor; the blocked position gains `A` but its
predecessor lacks `C`, so the section's construction is not a model. The
relevance rule only looks at literals in clause bodies, not at the
witnesses of the existentials a gained literal triggers through
non-successor edges. This does not show a wrong answer (another model may
exist, and the own-label fold is accepted on part of these terminals), but
the written argument of this section does not cover these pairs. A second
limitation is cost: `checkSat` enumerates every assignment, so terminals
with more than about 50 nodes and four-variable clauses did not finish in
an hour.

### Inverse witnesses (2026-10-30, `fix/v155-subset-blocking-gap`)

The gap. The section-9 construction gives a blocked position `w` the label
and the existential obligations of its blocker `w'`, but only copies of the
edges between `w'` and its successors. When `L(w')` triggers `∃r.F` and `w'`
witnesses it through an edge to a node that is not its successor (with
inverse roles, the edge `r(w', p')` to its own predecessor `p'`, which the
search creates as the inverse of `p' -r⁻-> w'`), the obligation reaches `w`
without a witness. The body-literal rule above does not see this: the
trigger is a literal at the clause centre of a clause without role atoms.
It also concerns equal labels and literals that `w` carries itself, since
`w`'s position takes all of `w'`'s obligations. Every relabelled rejection
inspected on the generated ALCI seeds below was of this kind (an unwitnessed
obligation at a blocked position, `diag2.py`); none was a clash or a failed
clause instance.

Published answers (question 1). No wrong answer was found:
on 1,500 generated nominal-free ALCI seeds (`gen_alci.py`: existentials
and universals over inverse roles, excluded middles), route `ht_general`
without the checker, the base binary agreed with HermiT on all 1,466 seeds
that answered (25 timed out or failed to spawn workers, 9 had no HermiT
gold), while Lean rejected 10,993 of its terminal certificates on 870 of
those seeds. So under `KM_HT_SUBSET_MODEL_CHECKER` the route would have
refused 870 seeds whose published answer was right; on the 700-seed corpus
the earlier run had 552 rejections and 183 checked answers, none wrong. The reason is that the infinite unravelling used by the
classical subset-blocking proofs is a model whenever the body-literal rule
admits the pair: unravel the completion graph into a tree in which every
copy of a node has one copy of each of its neighbours, except that a
blocked node's copy has its own kept neighbours together with copies of
*all* of `w'`'s neighbours, the predecessor `p'` included (a copy of `p'`
brings copies of `p'`'s other neighbours, and so on). Every node copy then
has the neighbourhood of a tableau node, so its clauses and obligations
hold as they did in the terminal, except for instances that combine a
blocked position's kept edges with `w'`'s label or neighbours. Those are
exactly what the body-literal rule and the counted-role (`multi_*`) rule
exclude. So the SAT answers of modes 1 and 5 were not shown wrong, and the
argument above says they are not; but that model is infinite and is not
the finite fold the Lean checker verifies, so the Lean backstop rejected
these terminals and, with `KM_HT_SUBSET_MODEL_CHECKER` set, the route
refused to answer.

The fix (`SubsetGain::back_need`, `back_witnessed`). For a candidate
blocker `m`, `back_need(m)` is the set of existentials `∃r.F` that `L(m)`
triggers (`L(m)` contains the literals that some clause with that head
has at the existential's variable; `existential_triggers`) and that `m`
witnesses over an `r`-edge to a non-successor `u` with `F ∈ L(u)`. A pair
`(w, m)` is admitted only if `w`'s own predecessor `p` carries `F` and `w`
has the edge `r(w, p)`, for every `(r, F) ∈ back_need(m)`; `p` is kept,
unblocked and keeps its own label in the fold, so `w`'s position witnesses
the copied obligation. The condition is applied in every mode-1 and mode-5
scan (`admits`, the incremental `checked_subset_recompute`) and in the fold
selection of the certificate, on the fragment the certificate covers (no
first-class cardinality rules, no nominals). It is the conservative form in one respect:
a successor of `m` that also witnesses `∃r.F` is ignored (the pair is
judged as if only the non-successor witness existed). The exact form
(subtract successor witnesses) had no rejected certificate on the 30
generated seeds it was run on, but made `back_need(m)` read the labels of
`m`'s successors, whose ids lie above `m`; the incremental scan then had to
rescan from `pred(t)` on every label change at `t`, which took
`ore_ont_205` from 100 s to 165 s (measured while the card arm still
applied the condition; see below). `back_need` is empty, and
nothing changes, unless the clause set has an existential head and some
edge can point to a non-successor (a role head whose source is not the
clause centre, or an equality head; `SubsetGain::back`). `trivial` is
false in that case, so the unchecked subset paths never run with such
clauses. Three kinds of edge are not counted as witnesses: edges to a
merged victim (dead; the merge redirected the edge to the survivor),
edges to a non-blockable node other than `pred(m)` (a shared individual
that no unravelling copies), and, when the worker has nominals, every
edge (`back` is false). The o-rule merges link nodes to the shared
nominal nodes; counting those witnesses made the forced `ht_general`
search on `tests/fixtures/top_nominal_data/probe_v6.ofn` (`⊤ ⊑ ≥2 u`,
`⊤ ⊑ {a, b}`) block nothing and run past the test's 120 s bound, where
the base binary finishes the search at once and then refuses the input
for its dropped nominals. The finite certificate is not emitted with
nominals or ABox individuals, so these cases keep the earlier rule and
the argument of the infinite unravelling (with one copy of each shared
individual).

Certificate emission. The certificate listed, for every edge `r(s, t)`, the
obligation `(r, F, s)` for every existential filler `F ∈ L(t)`, even when
`L(s)` triggers no clause with head `∃r.F`. A blocked position copies its
blocker's list, so an untriggered entry witnessed over the predecessor
would make Lean reject a fold that is a model. The emitter now lists a
satisfied existential only when `L(s)` triggers it (every clause instance
with that head whose body holds is triggered, so the Lean clause check
still finds every needed atom); the obligations the search recorded are
listed as before. The list is untrusted data either way.

Incremental exactness. `back_need(m)` reads `L(m)`, `m`'s out-edges, and
the label, `pred` and merge status of its non-successor targets;
`back_witnessed(w)` reads `w`'s out-edges and the label and merge status of
`pred(w) < w`. With `Ext::back_note` (set with `edge_note` when
`back_possible`), a label change at `t` lowers `i2_lo` to the sources of
`t`'s non-successor in-edges as well (in a tree, `t`'s children, which have
larger ids, so the suffix does not grow), and a merge of `v` also to
`pred(v)`. Edges were already noted at the smaller endpoint unless they are
successor edges, which `back_need` skips. `KM_HT_INCRBLOCK2_CHECK=1` aborted
on none of the runs below; the unit test
`inverse_witness_incremental_matches_full_scan` runs both modes with it.

Lean obligation. None new: the checker (`SubsetUnravelling.check_sound`) is
unchanged and still verifies each terminal's fold directly; `back_need`,
`back_witnessed` and the emitter are untrusted. What the fix adds is the
claim that the fold of a terminal whose pairs pass the rule satisfies
`checkSat`; the seed runs below test that claim, they do not prove it. Not
covered by the fold argument: the card arm, and counting at a blocker's
successors, which in the fold have the blocked position as a second
neighbour (an equality head over that role would be violated in the fold;
the seeds did not produce such a rejection). The card arm does not apply
`back_need` (`back` is false with first-class cardinality rules): its number
rules count `r`-neighbours, the predecessor included, and the fold changes
those counts at the blocker's successors, so the condition would not make
its fold a model, and it has no fold certificate. Applying it there cost
10.6% more search steps and 43% more blocking time on `ore_ont_7499`
(1,146,968 against 1,037,056 steps; 104 s against 83 s wall, both run at
once). The card arm's answers rest, as before, on the infinite unravelling
above.

Measurements (`results/agents/2026-10-30/subset-blocking-gap/`):

- ALCI seeds (`gen_alci.py`, 1..1,500, base binary): 1,466 ok, 0 wrong,
  25 errors (timeouts, failed thread spawns), 9 without gold; 28,616
  terminals accepted, 10,993 rejected (870 seeds). A random sample of 200
  rejected certificates re-checked with retries: all 200 rejected again
  (`head-sample-recheck.txt`), and `diag2.py` finds an unwitnessed
  obligation at a blocked position in each and nothing else
  (`head-sample-diag.txt`).
- ALCI seeds, fixed binary: the first 773 of the 1,500 seeds (seeds 1-425,
  501-663, 1001-1185; stopped for time): 747 ok, 0 wrong, 21 timeouts at
  120 s, 5 without gold; 19,679 terminals accepted, 0 rejected, 291 checker
  timeouts (30 s), none not emitted. The base binary had 5,539 rejected
  terminals on 450 of these seeds.
- Search cost of the condition: 9 of those 773 seeds answered on the base
  binary and timed out with the fix. Rerun one core each without the
  incremental check (`alci-fix-slow-seeds.txt`): base 0-16 s on all nine;
  fixed binary 55, 78, 121 and 297 s on four (outputs identical), over
  300 s on five (195, 392, 645, 1011, 1182). These ontologies combine
  `∃r.D` and `∃r⁻.D` at the same concept (seed 195: `B ⊑ ∃r.D`,
  `B ⊑ ∃r⁻.D`); a node whose blocker witnesses `∃r⁻.D` through its own
  predecessor can now be blocked only by a blocker whose predecessor is
  related to it as the node is to its own, which comes close to pairwise
  blocking, and the doc above records that pairwise blocking did not finish
  such seeds. This is the price of making the finite fold a model; it is
  not an answer change. Two alternatives were not taken: applying the
  condition only when `KM_HT_SUBSET_MODEL_CERT` is set (the default route
  would keep the earlier rule and its infinite-unravelling argument), or
  extending the Lean construction to copy the blocker's edge to its
  predecessor as well (no blocking change; it adds the blocked position as
  a second neighbour of that predecessor, which counting clauses there
  would reject).
- ALC corpus (700 seeds, `CORPUS`, fixed binary, checker timeout 20 s):
  326 ok, 0 wrong, 2 without gold, 372 errors (225 outside the
  `ht_general` fragment, 137 timeouts at 120 s with
  `KM_HT_INCRBLOCK2_CHECK=1`, the rest failed thread spawns); 10,506
  terminals accepted, 0 rejected, 880 checker timeouts, 31 certificates not
  emitted ("blocked node has no admitted unblocked blocker"). Ten sampled
  timeout seeds also time out on the base binary
  (`corpus-timeout-sample.txt`). The not-emitted cases: seed 18 has three
  on both binaries; on seeds 141 and 548 (`≤` restrictions, so equality
  merges and `back` true) the fixed binary has 7 and 5 where the base had
  none: the only blocker admitted for the node is a merged victim, which the
  scan keeps as a candidate and the certificate drops. Under the checker
  these terminals fail closed; making merged victims non-candidates is
  left open.
- `KM_HT_INCRBLOCK2_CHECK=1` aborted on no seed of either run, and on
  `ore_ont_205` and `ore_ont_7499` (card arm) with the final binary.
- Cost (one core, `run1.sh`, alternating base and fixed binary, host load
  about 50): 205: 129.1, 130.4 s base, 119.8, 139.3 s fixed; 7499: 127.5,
  114.6 s base, 126.9, 123.3 s fixed (`timing/table-final.tsv`); the search
  is the same (205: 1,101,827 steps on both; v1.5.4: 179 s, v1.5.3: 48 s,
  after the blocking-cost fix: 65 s on an idle host). Outputs identical to
  the base binary (md5).

### Predecessor fold (2026-10-31, `fix/v155-subset-unravelling`)

The conservative rule above made the finite fold a model by rejecting
pairs, which cost five generated ALCI seeds their answer within 300 s.
This change moves the work to the certificate instead: the fold copies one
more level of the classical unravelling, and the admission rule returns to
the exact condition for the pairs that fold covers.

Lean (`HypertableauSubsetUnravelling.lean`). `SubsetUnravelling` has a new
field `predecessorFolds` (wire field `predecessor`, a list of blocked
nodes; absent means none, the earlier wire). For a pair `(w, w')` whose
`w` is listed, `copiedEdges` copies, besides the edges between `w'` and its
successors, the edges between `w'` and its own predecessor `p'` (a node
`p` with `(w', p) ∈ parents`), in both directions, to `w`'s position. `p'`
keeps its own label; with relabelling `w`'s position has `L(w')` and
`w'`'s obligations, so an obligation `w'` witnesses through `r(w', p')`
is witnessed at `w` through the copy `r(w, p')`. The successor fold and the
own-label fold stay available (`predecessorFolds = []`;
`copiedNeighbour_of_predecessorFolds_nil` states that the copied
neighbours are then exactly the blocker's successors).

Proved statement (unchanged in form, now over every choice of
`predecessorFolds`): `SubsetUnravelling.check_sound : u.check = true →
∃ I : Interp (Fin nodeCount) (Fin conceptCount) (Fin roleCount),
I.models u.base.ontology ∧ ∀ literal ∈ u.seed, I.satLit literal u.root`,
and `WireSubsetUnravelling.check_sound` for the decoded wire document. No
sorry; axioms propext, Classical.choice, Quot.sound. The proof does not
depend on how `materialize` builds the graph: `check` runs
`FiniteSatCertificate.checkSat` on it, which evaluates every clause under
every assignment, checks every obligation's witness and every label for a
clash, and acceptance gives the canonical model of the materialized graph.

Counting clauses at the copied predecessor. The copies make `w`'s position
a second neighbour of `p'` with the label of `w'`. A clause that counts
`p'`'s neighbours (two neighbour variables and an equality head, for example
a functional or inverse-functional role) may then fail at `p'`; `checkSat`
finds the failing assignment and `check` returns false, so the fold is
rejected, never accepted. `SubsetUnravellingTests` has this case (a
functional `s` over the inverse-witness terminal), next to one where the
successor fold fails and the predecessor fold is accepted.

Engine. `SubsetGain::back_need(m)` no longer lists an obligation that `m`
witnesses at `pred(m)` when `pred_fold_ok(m)` holds; `back_need_strict(m)`
is the rule of 2026-10-30. `pred_fold_ok(m)`: `m` has a predecessor `p'`,
no role of an edge `m -r-> p'` is in `multi_in` and no role of an edge
`p' -r-> m` is in `multi_out` (no clause counts that edge at `p'`), and no
clause body has two role atoms between the same two variables
(`SubsetGain::parallel`; with such a clause, for example disjoint roles,
the blocked node's own kept edges to `p'` and the copies would be read
together). The certificate emitter lists `w` in `predecessor` exactly when
`back_witnessed(w, back_need_strict(m))` fails, so every pair the earlier
rule admitted keeps the successor fold; it records the number
(`predecessor_folds=`) and the variant (`relabel+predecessor`) in the
`KM_HT_SUBSET_MODEL_CERT` line. Under `KM_HT_SUBSET_MODEL_CHECKER` a
rejected document is retried with the own label, as before, and a
rejection of both still fails closed.

Exactness. The admission rule is now the body-literal rule, the
counted-role rule and the residual `back_need`. The answers rest on the
infinite unravelling of "Inverse witnesses" above, which copies all of
`w'`'s neighbours and needs only the first two rules; the residual
`back_need` only withholds pairs, so it cannot change an answer, and it
only affects which terminal the search reaches. The finite fold is checked
by Lean, not argued. Why the predecessor fold should pass on the pairs the
rule now admits (a claim the runs test, not a proof): at `w`'s position
every instance over copied edges reads the same labels and edges as at
`w'`; at `p'` an instance over a copied edge reads `w`'s position as it
reads `w'`, unless it counts neighbours (`pred_fold_ok`) or reads two role
atoms on one pair (`parallel`); instances over kept edges are those of the
body-literal rule.

Shapes still outside the predecessor fold, for which `back_need` stays:

- an obligation that `m` witnesses only through a non-successor other
  than `pred(m)` (an edge a merge redirected to another node);
- an edge between `m` and `pred(m)` on a role counted at `pred(m)`
  (`multi_in` / `multi_out`: number restrictions, functional roles);
- a clause with two role atoms between the same two variables
  (`parallel`);
- the card arm and runs with nominals, where `back` is false and no
  certificate is emitted (unchanged).

Merged victims (seeds 141 and 548 of the 700-seed corpus). The certificate
drops a merged victim and, through `pred`, every successor of it, while the
checked scans posted the victim as a candidate blocker and treated its
successors as ordinary unblocked nodes; a node whose only admitted blocker
was one of these had no certificate ("blocked node has no admitted
unblocked blocker"). Two changes: the checked scans (mode 1 with a
non-trivial `SubsetGain`, and mode 5) no longer post a merged victim as a
candidate (`Ext::merged_victim`; the victim is dead, its label a stale
copy); and a victim's successor counts as a successor of the survivor
(`Ext::live_pred = resolve(pred)`), which is what the merge made it (it
redirected the victim's edges to the survivor), in the mode-1 indirect
blocking and in the certificate's kept nodes and `parents`. Excluding the
victims' successors as candidates instead was tried and dropped: a label
that then occurs only below a victim never finds a blocker, and seed 548
ran past 120 s. Exactness: excluding a dead candidate blocks less; the
indirect rule blocks the successors of a blocked node in the merged graph,
which the unravelling replaces by the blocker's (the same argument as for
`pred`). Mode 5 keeps `pred` for its indirect pass (the card arm), so a
mode-5 certificate whose survivor is blocked can still fail closed. The
unchecked mode-1 paths (`exact`) are unchanged, as their unchecked
incremental twin is.

Incremental exactness. `back_need(m)` now also reads the roles of the
edges between `m` and `pred(m)`: the out-edges of `m` (already read, and
noted at `pred(m) < m`) and the edge `pred(m) -r-> m`, a successor edge
noted at `m`. `parallel`, `multi_in` and `multi_out` are fixed per
`SubsetGain`. A victim's posting depends on its merge status, and
`live_pred(n)` on the merge status of `pred(n)` and the status of the
survivor, which has a smaller id; `Ext::merge` and its undo lower `i2_lo`
to the victim (with `edge_note`), below every successor of it.

Lean obligation. None open for soundness: the checker verifies each fold
directly, and `pred_fold_ok`, `back_need`, the fold selection and the
victim exclusion are untrusted. What remains a tested claim is
completeness of the certificate: that every terminal the rule admits has a
fold Lean accepts.

Measurements (`results/agents/2026-10-30/subset-unravelling/`; the
binaries are `km-base` = 0e1bd99a and `km-fix3` = this branch):

- The five seeds the conservative rule lost (`gen_alci.py` 195, 392, 645,
  1011, 1182; one core, `ht_general`, no certificates): 19.0, 14.9, 15.0,
  1.1 and 0.5 s with the fix (10.9, 7.9, 8.6, 0.6, 0.3 s in a quieter
  period), past 120 s on the branch point; the answers agree with HermiT.
  With the checker inline, Lean's `checkSat` dominates: 1182 answers in
  17.5 s (51 terminals accepted, 39 with predecessor folds), the other four
  run past 60 s while checking (no rejection).
- ALCI seeds (`gen_alci.py` 1-1,500, `drive.py`, `JOBS=4`, checker budget
  30 s): 1,477 ok, 0 wrong, 17 km errors (120 s timeouts with
  `KM_HT_INCRBLOCK2_CHECK=1` on a host at load 30 to 130; each of them also
  failed on the binary before the gap fix, and 1478 runs past 300 s on the
  branch point too), 6 without HermiT gold; 39,202 terminals accepted, 0
  rejected, 536 checker timeouts, 0 not emitted (main run and the two
  reruns). Before the gap fix the same
  seeds had 10,993 rejected terminals on 870 seeds; the conservative rule
  had none but lost the five seeds above. Seed 645 timed out in the main
  run at load 130 and answered on the rerun.
- ALC corpus (700 seeds, `CORPUS`, checker budget 30 s): 326 ok, 0 wrong,
  2 without gold, 372 errors (234 outside the `ht_general` fragment, 138
  timeouts at 120 s); every seed has the status it had on the binary of
  2026-10-30 (`corpus-fix4.tsv`). 10,778 terminals accepted, 0 rejected,
  640 checker timeouts, 0 not emitted (31 on 14 seeds before, 141 and 548
  among them).
- `KM_HT_INCRBLOCK2_CHECK=1` aborted on no seed of either run.
- `ore_ont_205` and `ore_ont_7499` (card arm, one core, alternating, host
  load about 30): 205: 90.3 and 98.2 s on the branch point, 94.2 and
  85.5 s with the fix; 7499: 82.6 and 74.9 s, 81.3 and 75.5 s; outputs
  identical (md5). The card arm has `back` false, so only the merged-victim
  change reaches it.
- `top_nominal_data/m2197.ofn` on the `nominals` route: 64.2 and 50.5 s on
  the branch point, 46.7 and 52.4 s with the fix, same output. Its test
  bound is 120 s; under load 130 both binaries ran past it, and the suite
  passed (16 of 16) when the load was about 25.

## 10. Nominal merges and the reuse of the consistency model (2026-10-31)

Defect. `results/agents/2026-10-30/nominal-seeds/bridge_merge_min.ofn`:

    SubClassOf(ObjectOneOf(:b :c) ObjectOneOf(:b))
    ClassAssertion(ObjectOneOf(:b :c) :a)
    ClassAssertion(ObjectUnionOf(ObjectOneOf(:c) :C) :a)
    ObjectPropertyAssertion(:s :b :c)
    ClassAssertion(ObjectAllValuesFrom(:s :A) :a)
    EquivalentClasses(:Q1 ObjectOneOf(:b))
    SubClassOf(:A ObjectMaxCardinality(1 :r :C))

`{b,c} ⊑ {b}` merges `c` into `b`, `a : {b,c}` then puts `a` at `b` in every
model, `s(b,c)` becomes `s(b,b)`, and `a : ∀s.A` gives `A(b)`, so HermiT
entails `Q1 ⊑ A`. The forced `ht_bridge` route and the automatic route of
the development head (a2e98d95) answered without it. Konclude 0.7.0-1138
(`~/konclude-build/Release/Konclude classification`) misses it as well, on
this file and on r2730, and does not finish r3086 in 60 s; the defect is in
the ported algorithm, not in KM's admission or translation. The translated
input is faithful: with `KM_BRIDGE_FRESH_ENV=1` (a fresh completion per
probe, no reuse) the same `TInput` gives HermiT's answer. Three separate
defects of the reuse machinery lose the consequence; each is fixed where it
occurs.

1. Functional successor reuse through a merged-away node
   (`completion/u35.rs`, `try_extend_functional_successor_individual`; r3086
   and the functional-role seeds). Konclude's `mergeIndividualNodeInto`
   removes every link to the merged-away node. The port keeps those links
   and filters them in `ht_role_successor_links`, but the functional-reuse
   step of the `∃` rule read the role-successor hash directly and took the
   first link. In r3086 (`r` functional, `r(c,c)`, `r(c,a)`, `a : ∃r.A`)
   `a` merges into `c`, `c` keeps its link to `a`, and the `∃r.A` on `c`
   wrote `A` onto the ghost `a`, which no rule or read-off sees again. The
   step now skips merged-away and purged successors, the filter every other
   successor scan applies. Exactness: the live successors it chooses from
   are the links Konclude still holds after its removal; Konclude takes the
   first of them, and any live successor of a functional role is a correct
   choice because the at-most rule merges all of them.

2. Stale current node at the retained consistency base (`bridge.rs`, the
   first-fork rollback of the conditional-full schedule, the drain, and
   `restore_retained_classification_base`). The context's current-node
   pointer is not journaled. After the rollback to the first fork it still
   named the fork node, so `add_individual_to_processing_queue` treated that
   node as being processed and reported it queued without inserting it. The
   requeue of the fork node, and with it the disjunction the rollback put
   back, never ran: on `bridge_merge_min` no class job reopened `a`'s
   `{b} ⊔ {c}`. The pointer is now cleared at the rollback, after the drain,
   when a drain fails, and at the start of every class job, exactly as the
   in-process backtrack already does (u02, fuzz case 1002). Exactness: the
   pointer only says that a node's queue is being drained by the running
   loop; at these points no loop runs, so clearing it changes no rule, only
   makes pending work of the retained graph run.

3. Representative-cache replay without the merged individuals' nominals
   (`bridge.rs`, `replay_native_representative_cache` and
   `install_native_nominal_backend_replay`; `completion/u36.rs`, the lazy
   loader). The replay adds an association's deterministic labels with AND
   processing skipped: the cached label is taken as closed under the
   conjunction, implication and trigger rules. The writeback, like
   Konclude's representative cache, omits every positive nominal concept, so
   the replayed set is closed only up to the nominals. On
   `bridge_merge_min` `c`'s association is `b`'s merged label; it holds the
   trigger of `{b,c} ⊑ {b}`, which went into `c`'s label without its
   consequence `{b}`, and the later processing of `{c}` found the trigger
   present and derived nothing, so `c` was never merged with `b`. The
   positive nominal concepts in a node's deterministic label are exactly the
   nominal concepts of the individuals in its deterministic same-individual
   set (the nominal rule puts `{x}` on the node that represents `x`). The
   replay now adds those concepts, for every member other than the
   individual itself, with ordinary processing after the cached labels, so
   the nominal rule performs the recorded merges and the replayed state is
   the deterministic label again. When the association records no
   deterministic same set, or the set names an individual without a nominal
   seed, no cached label is replayed and both backend expansion blocks are
   off, so the node is expanded from its raw assertions. Exactness: every
   added concept is a deterministic consequence by the same criterion the
   replay already trusts for its labels (the consistency graph's dependency
   tracking marks the merge as independent of every branch); the change adds
   the part of the closure the cache format drops and removes no derivation.

What the fixes rest on. The bridge has no Lean model and emits no
certificate on any route (`docs/CHECKERS-ON.md` §1.1), so these arguments are
written, not mechanised, and no checker cross-checks a bridge answer on
nominal inputs. The three arguments assume the completion rules of the port
are correct and, for the third, that the consistency graph's deterministic
flags are right; both assumptions are those of the bridge before this change.
The answers are cross-checked only differentially against HermiT, below.
Lean obligation created: none discharged; a bridge model would have to state
that the replayed labels plus the deterministic same nominals are a
deterministic consequence of the ABox and closed under the AND-like rules,
and that the class-job queues hold every pending item of the retained graph.

Not changed. r2730 and r3086 repeat a role assertion, and the bridge's ABox
conversion declines repeated assertions ("ABox conversion was incomplete");
the automatic route answers them through the CB fallback, exactly. The
`-dedup` variants (same HermiT answer) exercise the bridge.

Cost. Some inputs the bridge answered before now reach one of the
fail-closed `raise_stop` checks of `merge_individual_node_into` (the
role-assertion transfer and disjoint-neighbour relocation of a nominal
merge) and the bridge defers: four generated seeds that were answered
wrongly (g545, g789, g1344, g1551), two R3 seeds that were answered wrongly
(r1536, r1866) and five R3 seeds that were answered correctly before
(r1164, r281, r947, r2627, r2970). With defect 2 fixed these class jobs run
the pending ABox work the old code dropped, and that work is where the merge
reaches the checks; the earlier correct answers on the five did not rest on
a complete search. The automatic route then needs the CB fallback: r2627 and
r2970 answer in 75 to 81 s, r1164, r281, r947 and r1536 do not finish in
120 s (load 140 on 56 cores). The subsection "Asserted edges through merge
chains" below lifts the check that fires and recovers all seven.

Evidence (`results/agents/2026-10-30/bridge-nominal-merge/`, before =
development/v1.5.5 0e1bd99a, after = this branch merged with it):

- 2,000 generated seeds (`gen_merge.py`, 30 s): forced bridge 1,751 ok /
  22 wrong / 227 declined before, 1,769 / 0 / 231 after; automatic route
  1,934 / 22 / 44 timeouts before, 1,956 / 0 / 44 after.
- R3 motif sets: tpl and tpl2 unchanged (0 wrong); 4,000 random seeds
  (10 s) forced bridge 3,133 ok / 7 wrong before, 3,134 / 0 after, automatic
  route 3,554 / 7 wrong / 439 timeouts before, 3,558 / 0 / 442 after.
- 700 ALCHIQ and fresh 300 bridge seeds (2026-10-29 sets): identical before
  and after on both routes (the three automatic-route wrong answers 621,
  1014, 1022 are on the development head before and after this change).
- 112 nominal ORE inputs of the paired design half, automatic route, 300 s,
  two streams side by side: 106 answered by both with identical output, mean
  time ratio 1.011, median 0.979; ore_ont_699 (295 s before) crossed the cap
  after and gives identical output at 900 s (350 s after, 450 s before).

### Asserted edges through merge chains (2026-10-31, `fix/v155-bridge-merge-edges`)

Which check fired. On all five R3 seeds (r1164, r281, r947, r2627, r2970)
the stop is the same one: the forward role-assertion transfer of phase 11 of
`merge_individual_node_into` (`completion/u15.rs`), where
`install_native_role_assertion_edge` (`completion/u36.rs`) returned false.
Inside it the refusal was the multi-hop check: the individual named as the
assertion's target had been merged into a node that was itself merged
since, so its live node lies two or more merges away. Because phase 9 marks
the merged-away node before phase 11 runs, an assertion `r(x, y)` held by
`x` reaches this state as soon as `y` was merged into `x` earlier (or into
any node merged later), for example a self assertion `s(a, a)` on a node
merged twice. No disjoint-neighbour stop and no other check fired on these
seeds (env-gated site trace on a scratch build; the trace is not committed).

Why the port stopped where Konclude continues. Konclude keeps on every node
an `IndividualMergingHash`: when `x` merges into `y`, every entry of `x`'s
hash moves to `y` with its dependency rewritten to
`MERGEDINDIVIDUAL(mergeDep, entryDep)` (`mergeIndividualNodeInto`, phase 6),
so the final node knows every individual it absorbed and the combined merge
dependency of each. The port has not ported that hash, and the edge
installer refused chains longer than one hop because it had no way to name
the combined dependency (a bridge unit test asserted that refusal).

Fix. `resolve_native_merge_chain` follows `mergedIntoIndividualNodeID` from
a node to its live representative and folds the hop dependencies exactly as
the hash would hold them: one hop gives that merge's
`mergedDependencyTrackPoint`, and each further hop `h` wraps the result as
`MERGEDINDIVIDUAL(dep(h), previous)`. It also reports whether any hop is
non-deterministic. `install_native_role_assertion_edge` uses it for the
target in place of the one-hop special case, and passes the folded
dependency as the nominal-merge part of the `ROLEASSERTION` dependency,
which it already did for one hop. The reverse-assertion transfer resolves
the asserting individual the same way: before, it looked the source up by
id and could install the edge on a merged-away node, where no rule sees it;
now the edge starts at the live representative under
`MERGEDINDIVIDUAL(this merge, the source's chain)`.

Exactness argument.
- Facts. A merge of `x` into `y` records `x = y` under the merge's
  dependency, so in every model of the current branch the individual named
  `y` in `r(z, y)` is the element the live end of `y`'s chain represents.
  The edge to that node is the asserted fact stated about the node that
  carries every label of the merged individuals; it adds nothing that is not
  entailed under the current branch, and it is the edge Konclude's lookup
  through the merging hash gives.
- Dependencies. A `MERGEDINDIVIDUAL` node is a two-parent deterministic link
  whose branching tag is the maximum of its parents
  (`update_dependency_branching_tag`), so the folded track point names every
  hop's merge, and a clash that involves the edge backtracks to the latest
  branch any hop depends on: the same set Konclude's rewritten hash entry
  carries. Backtracking past a hop restores the node state, and with it the
  chain, through the existing journal; the chain is read at install time
  and not cached.
- Determinism flag. The edge counts as deterministic for the
  cached-neighbour match only if the assertion's own dependency and every
  hop are deterministic, the one-hop rule extended to the chain.
- What still stops. A chain that does not resolve (a hop names no node) or
  that is longer than the number of nodes (a cycle; the merge rules choose
  live nodes as targets, and the bound turns a violation into a stop
  instead of a loop) returns false and the bridge defers, as do the
  remaining checks of phase 11 (an assertion naming an individual outside
  the arena, a non-nominal owner of a reverse assertion) and the
  unlocalised disjoint neighbour of phase 5. The remaining bridge declines
  below were not traced to a site.

What the argument rests on. As for the three fixes above: the bridge has no
Lean model, no certificate covers a bridge answer, and the argument assumes
that the port's merge, dependency and backtracking machinery is Konclude's.
HermiT differentials are the only cross-check. Lean obligation created:
none discharged; a bridge model would have to show that the folded
dependency's branch set is the union of the hops' and that the live end of
the chain is the unique node carrying the merged individual.

Evidence (`results/agents/2026-10-30/bridge-merge-edges/`, baseline the
bridge-nominal-merge `km.after`, `KM_THREADS=1`):

- The five seeds: answered as HermiT on the forced bridge and the automatic
  route, 0.01 s each (the automatic route took 75 s to over 120 s before).
  The six seeds km.after declined after answering them wrongly (r1536,
  r1866, g545, g789, g1344, g1551) are answered correctly on both routes.
- 2,000 generated seeds: forced bridge 1,769 to 1,993 ok, declines 231 to 7;
  automatic route 1,956 to 2,000 ok, timeouts 44 to 0. 4,000 R3 random
  seeds: bridge 3,134 to 3,333 ok, automatic 3,558 to 3,738 ok. R3 motif
  sets and the 2026-10-29 bridge sets unchanged per seed. 0 wrong answers
  on every set; no answer of km.after lost.
- None of the 777 remaining bridge declines of these sets reaches a stop in
  `merge_individual_node_into` (traced); 773 are ABox-conversion declines.
- 112 nominal ORE inputs, paired at 300 s: 108 answered by both with
  identical output and route, mean time ratio 1.034, median 1.006.

## 11. Global-decision and taxonomy wire fixes (2026-10-30)

The checkers-on suite (`docs/CHECKERS-ON.md` section 3.2,
`results/agents/2026-10-30/checkers-on-suite/README.md`) found that
`ht-cert-check` rejected the HT global decision document (H1) and that one
taxonomy test asserted a wire shape the producer no longer writes (T1). No
answer was wrong: both paths sat behind test variables that no gate set, so
the tests ran against `/bin/true` or skipped their Lean step.

H1 has two causes on one path. With no body equality and no preprocessing
(the common case) the HT source has no normalization records, so the
published global document is the raw regular-decision envelope
(`WireRegularDecisionCertificate`, version 1).

* `lean/HTCertCheck.lean` routed a version-1 document to the
  regular-decision decoder only when its evidence was `regular_sat` or
  `finite_unsat`. A `finite_sat` envelope, which the producer prefers when a
  finite model checks, fell through to `WireCertificate` and failed on
  `node_count`. The dispatcher now also routes `finite_sat`. This is
  executable dispatch only: `WireRegularDecisionCertificate` already decodes
  `finite_sat` and `DecodedRegularDecision.check_sound` already covers it,
  and `WireEvidence` has no constructor with any of the three names, so no
  plain certificate can be misrouted. No theorem changed.
* After the rejected finite candidate the producer tried the regular SAT
  certificate. The source-bound ordinary global document wraps a raw
  envelope in an explicit identity normalization, and the Rust wrapper looked
  for an `ontology` field, which a regular certificate does not have
  (`identity-normalized global decision has no ontology`). The wrapper
  (`lean_identity_normalized_global_source` in `engine/src/hypertableau.rs`)
  now lists the ontology Lean decodes from the certificate,
  `FiniteRegularCertificate.ontology`: the role clauses through
  `NormalizedRoleClause.toClause`, then the residual clauses, in that order.
  The checker verifies every identity record against its target clause
  (`decodeOntologyNormalization`), so a wrong list is rejected, not trusted;
  the test `identity_normalized_regular_source_lists_the_lean_target_ontology`
  checks that the source clause order (residual first) is rejected.

Exactness. Neither change alters a search, a verdict or a published
answer. The Lean change accepts documents whose proof object the existing
sound decoder already handles; the Rust change emits the identity
normalization the proved checker expects. Lean obligation: none new; the
soundness of the accepted branch is `DecodedRegularDecision.check_sound`
(and `WireSourceBoundOrdinaryGlobal.check_sound` for the source-bound
document), both unchanged.

T1. `lean_taxonomy_checker_accepts_a_materialized_equality_body` asserted
`payload.plain.certificate`. Certified taxonomy publication now always
writes the mixed version-2 matrix that
`WireOrdinaryTaxonomyRunMatrix.terminalMatrix?` derives for every fragment,
so the test asserts `payload.mixed.certificate` (version 2) and the absence
of `plain`; `ht-taxonomy-cert-check` accepts the document.

Gate. `lean/run-ht-certification-gate.sh` now exports
`KM_HT_TEST_LEAN_CHECKER`, `KM_HT_TEST_LEAN_GLOBAL_CHECKER`,
`KM_HT_TEST_LEAN_TAXONOMY_CHECKER`, `KM_HT_TEST_LEAN_CARDINALITY_CHECKER`,
`KM_HT_TEST_NATIVE_ABOX_DECISION_CHECKER`, `KM_HT_TEST_PROJECTION_CHECKER`
and `KM_HT_TEST_LEAN_NATIVE_ABOX_SOURCE_DECISION_CHECKER`, runs the lib
tests that read them one at a time, and runs `tests/ht_taxonomy_certificate.rs`
with one test thread (real checkers fail to start threads near the host's
commit limit when many run at once). With the fixed checkers all 35 lib
tests that read these variables pass; with the v1.5.4 `ht-cert-check`,
`regular_decision_prefers_a_checked_finite_sat_model` fails with the
`node_count` error. The gate passed end to end on this branch (97 test
binaries or filters, 249 tests passed, 0 failed, 0 ignored; 12 min 53 s
wall with the checker executables already built).

Not covered here. When the source does have normalization records,
`wrap_normalized_lean_certificate` wraps a regular SAT envelope with the
records in source clause order, while Lean decodes the regular target with
the role clauses first; a source that mixes role clauses with body-equality
clauses would then, by reading the code, be rejected (fail closed). No test
exercises that case.
`KM_HT_GLOBAL=1` is a worker variable (consistency only); set on
`km classify --route ht_general` it publishes an empty subsumption list (on
a five-axiom ALC input the entailed `B ⊑ D` was missing), so it is not a way
to reproduce H1 through the CLI and the orchestrator should refuse it.

## 12. Worker-only variables at the user entry (2026-10-31, agent `incremental-ht-regression`)

Section 11 found that `KM_HT_GLOBAL=1`, a worker protocol variable (the HT
worker answers consistency only and returns an empty taxonomy), leaked
from the user's environment into `km classify --route ht_general` and
published an incomplete taxonomy. `Route::apply_environment` already
removed `KM_HT_TOTAL_GLOBAL` and `KM_HT_GLOBAL_NATIVE_ABOX` (`ROUTE_KEYS`)
for forced routes, but not `KM_HT_GLOBAL`, and the automatic route removes
none of them.

`routing::WORKER_ONLY_KEYS` lists the variables that change what a worker
answers rather than how it searches: consistency-only verdicts
(`KM_HT_GLOBAL`, `KM_HT_TOTAL_GLOBAL`, `KM_HT_GLOBAL_NATIVE_ABOX`,
`KM_HT_REQUIRE_MASKED_DISJOINT_UNION_SHAPE`, `KM_RULES_CONSISTENCY`), the
rule worker's taxonomy protocol (`KM_RULES_CLASSIFY`,
`KM_RULES_CLASSIFY_KNOWN`) and subject subsets (`KM_QUERIES`,
`KM_QUERIES_FILE`). The supervisor sets each of them itself, per worker
(`Command::env`) or inside an `EnvironmentGuard`. `km classify` and
`km explain` now call `routing::strip_worker_only_environment` first, which
removes them from the process environment and names them on stderr. The
supervisor's own later settings are unaffected, so no published answer can
depend on a user value of these variables. Stripping (rather than refusing)
also keeps the incremental session's `km classify` witness subprocess
(`incr_session::classify_process_json`) correct if it inherits one.

Exactness: the change removes inputs that no exact published answer may
read; it alters no search, rule or verdict. Lean obligation: none.

Test: `engine/tests/worker_only_environment.rs` classifies an ALC input
with the entailed `B ⊑ D` on `--route ht_general` and the automatic route,
once plain and once with each `WORKER_ONLY_KEYS` variable set to `1`; the
published lines must be equal and stderr must name the variable.

## 13. `SameIndividual` by pre-merge in the native ABox conversion (2026-11-01, `fix/v155-sameindividual-bridge`)

Before. The generic native ABox conversion
(`orchestrate/cb_to_ht.rs`, `install_nominal_abox_with_same` with
`allow_same = false`) declined every input with a `SameIndividual`
assertion ("SameIndividual requires equality merging not implemented by the
native HT bridge"), so the automatic route had no HT racer and the nominal CB
stack had to answer alone. Since 24067ca3 (2026-07-31) only the certified
nominal-NI specialist, the forced `ht_bridge` route and the ground-rule data
source admitted equality. On those routes the bridge read the untouched
typed ABox (`TInput::nominal_abox`) and encoded `SameIndividual(a, b)` as
the nominal assertion `{b}(a)` (`bridge.rs`, native-nominals phase), so
the completion merged `a` into `b` at run time, one merge per equality,
through `merge_individual_node_into` (section 10).

Change. With equality admitted, the conversion now installs the quotient of
the ABox by its equalities (`quotient_same_individuals`) and renames the
source TBox to match (`KM_NO_SAME_PREMERGE=1` restores the run-time
encoding). The routes that admitted equality before (forced `ht_bridge`,
the ground-rule data source, the certified specialists) now take the
quotient. The generic automatic HT racer still declines `SameIndividual`
by default (`KM_HT_ADMIT_SAME=1` admits it): on the inputs that motivated
the change the bridge does not finish (below), and with one thread its
attempt runs before the CB stack, so admitting it would only move CB time
into a failing bridge attempt.

Construction. Let `I` be the named individuals of the typed ABox and `~`
the least equivalence relation on `I` that contains every pair of a
`SameIndividual` assertion (union-find over `NominalAboxMeta::same`). Each
class `[a]` gets one representative `ρ(a)`, its first member in entry
order, and `σ` replaces every individual name `a` by `ρ(a)`. The installed
ABox is `σ(A)`:

- one entry per class, named `ρ(a)`, whose proxy concepts are the union of
  the members' proxies (`{a}`, `{b}`, ... all name the one root) and whose
  class assertions are the union of the members' assertions with `σ`
  applied inside each expression (`ObjectOneOf`, `ObjectHasValue` and
  other nested nominals), paired with their unchanged markers;
- `same` empty;
- `σ` on both ends of every `DifferentIndividuals` pair, every object
  property assertion and every negative object property assertion
  (data property assertions are class assertions `∃p.{v}` of their
  subject and are covered by the first item);
- assertions that `σ` makes equal kept once;
- `σ` on every `Concept::Nominal` of the source TBox
  (`TInput::source_axioms`), which the bridge encodes from the source
  expressions; the clause view keeps the members' proxy names, and those
  now denote the representative's singleton.

Exactness. Write `O = T ∪ A ∪ E` with `E` the equality assertions, and
`O' = σ(T) ∪ σ(A)`. Taxonomy and consistency are unchanged:

1. Every model `I` of `O` is a model of `O'`. In `I` all members of a class
   denote one element (`E` holds and `~` is the closure of `E`), so
   `a^I = ρ(a)^I` for every `a`. Then the extension of every concept and
   the truth of every axiom are the same before and after `σ`: `σ` only
   replaces a name by a name of the same element.
2. Every model `J` of `O'` extends to a model of `O` with the same domain
   and the same concept and role extensions: set `a^J := ρ(a)^J` for every
   individual. Then `E` holds, and every axiom `α` of `T ∪ A` holds because
   it has the truth value of `σ(α)` under `J`, as in 1.
3. Both directions keep the interpretation of every class and property name.
   So `O` is consistent iff `O'` is, a class name is unsatisfiable in `O`
   iff it is in `O'`, and `O ⊨ C ⊑ D` iff `O' ⊨ C ⊑ D` for class names `C`,
   `D`: a counter-model of one is a counter-model of the other. The
   classification output names no individual, so the renaming is not
   visible in it.

Two consequences the argument covers and the code reads directly:

- `DifferentIndividuals(a, b)` with `a ~ b` becomes `(ρ(a), ρ(a))`. In `O`
  it says `a ≠ b` while `E` forces `a = b`, so `O` is inconsistent, and
  `σ` of the axiom (`ρ(a) ≠ ρ(a)`) is unsatisfiable. The native
  conversion keeps the pair as a self pair, `native_abox.different` holds
  `(i, i)`, and `native_nominal_consistency` returns inconsistent before
  any completion for any self pair (it already did; the pre-merge only
  makes the pair visible without a run-time merge).
- A nominal `{b}` of a merged-away `b` in the TBox: in the source axioms
  it becomes `{ρ(b)}`; in the clauses the proxy `{b}` stays and is one of
  the representative's proxies, so the bridge's nominal concept of `{b}`
  points to the representative's individual. Both are `σ`.

Equalities that the TBox forces (functional or inverse-functional roles,
at-most restrictions, nominal subsumptions such as `{a, b} ⊑ {a}`) are not
part of `E` and stay run-time merges of the completion, as before. They are
consequences of `O'` exactly when they are consequences of `O`, by 1 and 2.

Fail closed. The quotient is built only when `allow_same` holds, the input
has equalities and no rule-source ABox (`TInput::rule_source_abox`, which
names individuals in a second structure the renaming does not touch). An
equality that names an individual without an entry gives no quotient and
the conversion declines as before. If any later check of the conversion
fails, the conversion restores the source ABox and adds no renamed state.

Lean obligation: none discharged. The statement is propositional (a
renaming of constants along an equivalence that the theory entails) and
does not touch the CB calculus; the bridge has no Lean model
(`docs/CHECKERS-ON.md` §1.1). Cross-checked differentially below.

### Where the bridge's time goes on the large equality ABoxes

The five held-out inputs of the task (ore_ont_16315, 10838, 3087, 7557,
10926) and ore_ont_15846 share one Drosophila ABox family: 30,657 to 66,423
`SameIndividual` axioms, 33 property chains, 22 transitive roles, hub
individuals with up to 3,525 asserted neighbours. 10926 has no
`SameIndividual` at all; its HT worker is spawned (3.5 million clauses) and
the run ends on memory. With the pre-merge, 16315 goes from 58,273
individuals to 29,495 classes, and the forced bridge still does not finish.
Traced on ws (`KM_HT_STOP_TRACE=1` names the stop site; gdb stack samples of
the worker):

1. Consistency completion (`native_nominal_consistency`, all roots, the
   legacy nominal schedule because the ABox has more than 10,000
   individuals). Stopped by the 30 s probe budget of the route (u02.rs
   drive deadline); with a 1,100 s budget it still had not finished after
   19 minutes. Nearly every sample sits in the automaton rule
   (`apply_automat_transactions` → `ht_all_rule_target_links`). Two causes:
   - a linear duplicate scan of the output vector, quadratic in the node
     degree. Replaced by a membership set past 16 entries (same output,
     same order). Not enough on its own.
   - the port has no restricted (`restLink`) arm: when a new link re-fires
     the armed `∀`-automaton states of a node
     (`apply_reapply_queue_concepts_restricted` attaches the link
     restriction), the port propagates over every successor again, so a
     hub with `d` links costs `d²` per state. Konclude propagates over the
     restricting link only (cpp 9662-9700). `KM_HT_AUTOMAT_REST_LINK=1`
     implements that arm (`ht_rule_target_of_link`); with it the
     consistency completion of 16315 finishes in 15 s. It stays off by
     default: `KM_HT_AUTOMAT_REST_LINK_AUDIT=1`, which runs the full arm and
     counts the operands it adds outside the restricting link, reports such
     operands on 122 of the 3,203 chain-seed runs that take the arm (61
     seeds of `gen_chain.py`, on both routes; every one of them has a
     nominal or an equality, so run-time merges, which relocate links, are
     the first suspect), so the
     port's links are not all registered for a restricted re-fire the way
     Konclude's per-role links are, and the arm is not shown complete for
     this port. All 4,000 answers still agree with HermiT with the arm on,
     which shows only that the missing operands arrived by another path on
     these seeds.
2. Classification probes after consistency. On the legacy schedule each of
   the 4,895 subject probes re-completes the ABox (15 s each). On the
   conditional-full schedule (`KM_HT_CONDITIONAL_FULL_LIMIT=1000000`
   lifts Konclude's 10,000-individual bound for measurement) the probes
   reuse the retained consistency graph and run 64 subjects in about 4 s,
   but the representative-cache writer
   (`write_completed_native_representative_associations`) took 128 s: it
   scanned every individual and every seed's assertion journal once per
   association. Both scans are now read from indexes built once per writer
   call (`native_completion_same_individual_index`,
   `native_completion_assertion_journal`); the visited assertions, their
   order, and the failure cases are unchanged.
3. The saturation writer (`write_native_abox_representative_cache`)
   replayed every seed's assertion journal, with a copy of the super-role
   list per assertion, once per association: 130 s of 10838's run. The
   journal is now resolved once per call
   (`native_saturation_assertion_journal`); its targets are sets, so the
   result is unchanged. 10838's saturation drops to 0.6 s.
4. Left: on the conditional-full schedule the first 1,700 subject probes of
   10838 cost 0.15 s each, mostly in
   `get_anywhere_blocking_individual_node_canidate_hashed` and its backward
   scan over the retained graph's positive node ids, which copies nodes
   (`ProcessContext::node_mut`).

With the three switches (`KM_HT_ADMIT_SAME=1 KM_HT_AUTOMAT_REST_LINK=1
KM_HT_CONDITIONAL_FULL_LIMIT=1000000`) and the index fixes, the bridge
answers 16315 in 131 s on ws (2.3 GiB peak) with Konclude's reference
taxonomy; 10838, 3087, 7557 and 15846 finish consistency in 22 to 30 s and
time out in the probes (cost 4); 10926 (no equality) needs about 470 s at
the measured probe rate. Without the switches nothing changes for these
inputs. The index fixes change no output on the 112 nominal ORE inputs of
the design half and the 66 small equality inputs (identical signatures,
time ratio 0.97 and 1.01 against a non-PGO base build).

Not done. The bridge has no exact large-ABox schedule that finishes these
inputs. The conditional-full schedule above 10,000 individuals is
Konclude's choice only below that bound (Konclude uses its lazy, batched
representative precomputation above it), and the restricted automaton arm
is not shown complete for the port. The generic automatic racer therefore
keeps declining `SameIndividual`.
## 14. Witnesses for empty stored refutations (2026-11-01, `fix/v155-bridge-speed`)

**Defect.** On ore_ont_4796 (DOLCE, 199 classes, 296 KB) the native bridge
spent 30 s on each of the two unsatisfiable classes `system-as-artifact` and
`physical-plurality`, hit the per-subject budget and deferred the whole
classification; Konclude answers in 0.3 s. Profile evidence
(`results/agents/2026-11-01/bridge-speed/`): 400,000 drives and 600,000
backtracks per subject over a 300-deep branch stack; 28 % of the clashes fell
back to chronological backtracking (`KM_BRIDGE_DDB_TRACE`). Every fallback
followed the same pattern: the topmost decision, a four-way disjunction
`¬(social-object ⊓ ∀r141.particular ⊓ ∀r142.particular ⊓ …)` on one node, had
all four alternatives marked refuted, u29 collected their closure at
branching level 0 (the clash depends on no open choice, so the subject is
unsatisfiable), and the root cancellation was **withheld** because two of
the four alternatives had an EMPTY stored refutation. The search then
backtracked chronologically into unrelated decisions and re-derived the same
refutation under each of their combinations.

The empty sets are genuine: the alternative `∃r142.¬particular` creates a
successor that receives `particular` from a ⊤-GCI, so the clash
`particular, ¬particular` on that successor depends on nothing older than
the alternative itself. Konclude stores the same empty set and cancels. The
witness test of §11 (`all_siblings_stored_refutation`) was introduced
because an empty set can also come from a lossy closure reconstruction
(ore_ont_12653), and it cannot tell the two apart.

**Change.** An empty stored refutation now counts as a refutation record when
an independent probe shows that the alternative's operand alone is
unsatisfiable with respect to the input (`verify_empty_alternative_operand`):

1. u29 looks up the sibling's `(operand, negation)` on the search stack
   (`ht_disjunction_alternative_operand`) and in
   `CompletionTaskHandleAlgorithm::empty_alternative_witnesses`. `true`:
   the sibling is justified. `false`: withheld as before. Unknown: withheld,
   the operand is requested, and, when the driver has enabled
   `stop_on_unknown_empty_alternative_witness`, the drive STOPs at its next
   drive boundary (`run_completion_on`).
2. The classification driver (`bridged_classify_opts_…_inner`, subject
   read-off) probes every requested operand in a FRESH bridge environment
   over the same `TInput`, records the verdict, rebuilds the job and reruns
   it. Every round adds at least one entry, so the loop ends. All later jobs
   of the classification see the map (`renew`).
3. The probe: the operand on a fresh root with ⊤, every disjunction parked
   (`defer_or_branching`, never expanded), dependency-directed backjumping
   off, in-process copy-on-write epochs on, chronological search over the
   remaining branch points (at-most merges, qualification choices, backend
   reuse), 5 s budget. Only `Some(true)` (UNSAT) with no unrestored advance,
   no completeness poison and no root cancellation counts. The concept is
   matched between the two environments by tag, operator and operand list.

**Exactness.** The probe decides a weaker problem than the input (the
parked disjunctions are left out; every other rule runs, and every other
branch point is enumerated completely, with complete state restoration),
so its UNSAT verdict is a sound proof that the operand is unsatisfiable with
respect to the input, independent of any stored-set reconstruction and of
the DDB analysis. An alternative whose operand is unsatisfiable fails in
every context and contributes no cause, which is exactly what an empty
stored set claims. The cancellation is then justified on the same terms the
existing witness already accepts for non-empty stored sets: the change only
widens `all_siblings_stored_refutation` by a proven case, so it cannot
cancel where the old test was right to withhold for a lossy set (a lossy
empty set on a satisfiable operand yields `false` and stays withheld). A
STOP is an UNKNOWN verdict that the driver answers with a rerun of the same
job; a missing or failed probe leaves the historical behaviour. No answer can
change; the subjects that previously exhausted their budget now reach the
cancellation Konclude takes.

## 15. Cleared-queue screen on a resuming retained base (2026-11-01, `fix/v155-bridge-speed`)

**Defect.** On the ObjectHasValue family (ore_ont_3917, 11378, 12191, 9151,
9577: hundreds of `ObjectHasValue`, thousands of class assertions) the
consistency completion is nondeterministic, so the retained base resumes the
first fork (`KM_BRIDGE_FORK_DRAIN=resume`, the default): every class job
re-decides the base's pending ABox disjunctions. Profile evidence on 3917
(`BRIDGE-SUBJECT-STATS`): every one of the 5,383 subject jobs opened the same
173 branch points (93 on nominal nodes) and made 3,000 to 4,400 insertions
with zero backtracks, 16 ms per job, 87 s of a 117 s prepare phase. Konclude
starts every class task from its deterministic consistency task with the
individual processing queues cleared and touches an individual only when the
class task reaches it. `KM_BRIDGE_FORK_DRAIN=konclude` (the same cleared-queue
class task in the port) runs 3917 in 12 s with the reference answer, but it
is not exact by itself: a job that modifies a base node next to a node whose
disjunction is still pending can publish a model in which that disjunction
has no consistent choice.

**Change.** On a base that resumes the first fork, each subject read-off
first runs as a SCREEN on the same retained graph with cleared processing
queues (`restore_retained_classification_base_with(…, cleared_queues =
true)`, which sets `retained_base_node_count` to the base size) and with the
satisfiability cache writers off. The screen is accepted only when the job
is isolated from the retained graph (`cleared_queue_job_isolated`):

- no retained node was modified in place (`retained_node_modified_count`,
  counted in `propagate_individual_node_modified`, through which every
  concept, link and merge modification passes),
- no node of the job carries the individual id of a retained individual (the
  port, like Konclude, LOCALIZES an individual into the task before changing
  it: the change goes to a new arena slot with the old id and the retained
  slot is never written, so the first test alone does not see it), is merged
  into one, or has an edge to one (the successor hash records both
  directions),
- no branch point was opened on a retained node, and
- no node of the job is blocked by a retained node.

The localization rule was added after the first version of the screen,
which tested only in-place modifications, published 249 incomplete answers
on each route of the `bridge-nominal-merge` seed pool (g1002: `Q1 ≡ {a}`
missed `Q1 ⊑ E`, because the subject root merged with a localized copy of
`a`) and failed `bridge_conditional_full_replay` (cw_min4051).

Otherwise the subject runs exactly as before on the resuming base. A
rejected screen costs a second job, so the driver stops screening an input
once at least 512 screens were rejected and fewer than one in five was
accepted (the subject order puts ABox-touching subjects first on 3917, so a
short window would switch the screen off before the first acceptance).

**Default: off** (`KM_BRIDGE_CLEARED_QUEUE_SCREEN=1` enables it). Measured
on 3917: the forced `ht_bridge` route accepts 2,514 of 5,383 screens and
drops from 100 to 146 s to 52 s, but on the automatic route the bridge runs
on the `certified_nominals` input, where every class job reaches a retained
individual: 0 of 512 screens are accepted and the screen only adds jobs
(3917 automatic: 77.5 s without, 90.5 s with, same binary and host). The
remaining cost of this family needs Konclude's lazy reuse of the
consistency model for touched individuals (the precomputation replay, which
the port disables after a nondeterministic consistency completion).

**Exactness.** The input is consistent (the base exists only after a
successful consistency completion). An isolated screen job never added a
concept, link or merge to a retained individual (in place or through a
localized copy), has no edge to one and never used one as a blocker,
so its graph is the retained graph plus a component of fresh nodes that
shares no edge, merge or blocking relation with it. UNSAT: the job's clash
derivation used only retained facts (deterministic consequences of the
input, the drained base) and its own branch points, all of which it
enumerated; leaving the base's pending disjunctions unexpanded only removes
constraints, so the verdict holds for the input. SAT: the fresh component
is complete and clash-free and does not refer to any individual, so its
unravelling next to any model of the input (the disjoint union) is a model
of the input in which the subject root is an instance of exactly the
concepts in its label; the read-off and its authoritative flag are those of
that model. Any job that touched the base reruns on the resuming base, so
its answer is the old one. The screen writes no satisfiability cache entry,
so no later job can read state that rested on an unaccepted screen.

## 16. Retained consistency leaf with a reuse branch point (2026-11-02, `fix/v155-bridge-replay`)

**Defect.** On the ObjectHasValue family (ore_ont_3917, 11378, 12191, 9151,
9577) the consistency completion is nondeterministic, so the port disables
the precomputation replay (`BRIDGE-REPLAY disabled`) and every class job
resumes the first fork of the consistency completion: each of the 5,383 jobs
on 3917 re-decides the same 173 ABox branch points (§15). Konclude does not:
its class tasks start from the deterministic consistency task with cleared
queues and consult the cached nondeterministic consistency model
(`CCompletionGraphCacheHandler`, `PRFCOMPLETIONGRAPHCACHED`), reactivating an
individual only when the class task contradicts the cached model. On the
inputs whose saturation refuses `SELF` (6132, 9899) the port has no retained
base at all and every job re-initializes and re-decides the whole ABox.

**Change.** `bridge.rs`, the block "Retained consistency leaf"
(`build_retained_consistency_leaf`, `restore_retained_consistency_leaf`,
`drop_retained_consistency_leaf`, `retained_leaf_verdict_accepted`) and the
`leaf_*` state of the classification driver; `process/context.rs`,
`push_spine_journal_epoch` / `pop_spine_journal_epoch`.

1. *The leaf.* The first class job that wants it builds the LEAF: it
   restores the job base exactly as for a class job (the resuming base, or,
   without a retained base, the per-job reset that initializes the whole
   native ABox), configures the job algorithm exactly as for a class job,
   and runs the completion with no class root to a clash-free fixpoint. The
   leaf is accepted only when the drive ended consistent with no pending
   signal, no completeness poison and no unrestored advance; otherwise leaf
   reuse is off for the input. The leaf's open decisions are removed from the
   job branch stack; their epochs stay open beneath every leaf job.
2. *Leaf jobs (alternative 0 of the reuse branch point).* Each subject
   read-off, pair probe and batch refutation first runs on the leaf: the
   previous leaf job is rolled back (its owned branch epochs, its job epoch),
   a new job epoch opens with the leaf's databox, branch cursor (so the job's
   branch levels lie above every leaf level) and id allocator, and with a
   fresh job algorithm. The spine arenas (track points, dependency nodes and
   links, clash and concept descriptors, branch-tree nodes) are exempt from
   branch epochs; leaf jobs run inside a journaled spine epoch that is
   popped per job, so the DDB marks a job puts on the leaf's track points
   (and every other spine change) do not survive into the next job. Leaf
   jobs write no satisfiability-expansion cache entry.
3. *Acceptance.* A leaf verdict is accepted only if the job search is not
   poisoned and either (a) the verdict is satisfiable (a clash-free fixpoint,
   no pending signal), or (b) the verdict is unsatisfiable and the drive
   ended in a ROOT CANCELLATION (`ddb_root_cancelled`: u29 traced the clash to
   branching level 0, with every sibling refutation witnessed as in §11 and
   §14). Accepted satisfiable read-offs are never authoritative. A batch
   refutation is used only on an accepted satisfiable verdict.
4. *Fallback (alternative 1).* Any other outcome (an unsatisfiable verdict
   without root cancellation, a STOP, a poisoned search) takes the second
   alternative: the leaf is dropped (all epochs above the job base and both
   spine journals popped; on the reset path the reset itself discards it)
   and the job reruns exactly as before this change. The leaf is rebuilt
   lazily by the next leaf job. A scheduling rule (no verdict depends on it)
   stops leaf attempts once alternative 1 was taken at least 256 times and on
   more than half of the attempts.

`KM_BRIDGE_NO_LEAF_REUSE=1` restores the previous path; `KM_BRIDGE_LEAF_STATS=1`
(with `KM_HT_STATS=1` on the orchestrated route) prints the counters.

**Exactness.**
- *The leaf is a model.* The job base is exact by the arguments of §10 and
  §15 (it is the resuming base or a freshly initialized ABox). The leaf is
  the consistency completion continued from it by the unchanged rules to a
  clash-free fixpoint, so its graph is a complete clash-free completion graph
  of the input ABox; leaving no unrestored advance, it carries no leftovers of
  refuted alternatives and its dependency tags are those of its decisions.
- *Satisfiable verdicts.* A leaf job adds the class root (and the probe
  seeds) to that graph and runs every rule to a clash-free fixpoint. No queue
  of the leaf is pending, so the final graph is a complete clash-free
  completion graph of the ABox plus the probe: a model of the input in which
  the root has the probe's concepts. The read-off of such a model is what
  any satisfiable probe on the resuming base also yields (an arbitrary model
  of the input); it is marked non-authoritative because its root label can
  contain consequences of the leaf's choices. Its positive labels go into
  KPSet's candidate set and its deterministic labels into the certain set
  through the dependency branch tags, exactly as for a job that made the
  same choices itself: the leaf's decisions carry branch tags 1 to the
  leaf's depth and `maximum_deterministic_branch_tag` stays 0, so no fact
  that rests on a leaf decision reads as deterministic.
- *Unsatisfiable verdicts.* A leaf job is a continuation of the consistency
  search: its branch tree extends the leaf's, and the leaf's decisions are
  ordinary nondeterministic dependency nodes whose refuted alternatives keep
  the refutation sets stored during the consistency search (those stay valid:
  the probe only adds facts). A root cancellation means the clash closure,
  propagated through decisions all of whose alternatives carry a witnessed
  stored refutation, reached branching level 0, i.e. depends on no decision
  of the job or of the leaf: the probe is unsatisfiable with respect to the
  input. This is the verdict the full consistency search would reach after
  enumerating the leaf's alternatives, and it rests on the same trust base
  as every DDB root cancellation of the bridge. Every other unsatisfiable
  outcome, in particular the exhaustion of the job's own branch stack, may
  rest on a leaf decision whose other alternatives were never tried, and is
  rejected.
- *No leakage between jobs.* The graph, labels, queues and databox of a job
  are rolled back by its branch epochs; the dependency spine by the spine
  journal; the job algorithm is fresh. What survives a job is what survives
  a job on the resuming base too (the unsatisfiable cache, whose entries are
  label subsets refuted with respect to the TBox; the learned disjunct
  priorities; the witness map of §14), plus nothing a leaf job writes to the
  satisfiability-expansion cache, because leaf jobs write none.
- *Fallback.* Alternative 1 is the unchanged job on the unchanged base, so
  its verdict is the old one; dropping the leaf restores that base exactly
  (branch epochs and both spine journals popped, then the ordinary restore).

What it rests on. As for §10 to §15: the bridge has no Lean model and no
certificate covers a bridge answer; the argument assumes the port's rules,
dependency tracking and DDB root cancellation are Konclude's, and is checked
differentially. Lean obligation created: none discharged; a bridge model
would have to show that a root-cancelled closure over a search tree that
extends a completed consistency search is a refutation of the probe, and
that the spine journal restores every spine field a job reads.

## 17. The restricted automaton re-fire, read-only blocking scans, and Konclude's full-graph decision (2026-11-02, `fix/v155-bridge-abox-probes`)

Section 13 left three switches between the large equality ABoxes and the
default route. This section removes them: the restricted automaton arm is
on by default (with the argument below), the subject probes no longer copy
the retained graph, the schedule choice follows Konclude's whole decision,
and the automatic racer admits `SameIndividual`. Measurements and seed
counts are in `results/agents/2026-11-02/bridge-abox-probes/README.md`.

### 17.1 The restricted arm derives the closure of the all-successors arm

`apply_automat_transactions` (u05) handles an automaton state `S` at a
node `x`. On the first processing of `S` (`reapplied == false`) the
descriptor has no link restriction; the arm walks the `CCAQAND` state graph,
adds every `CCAQALL` transition `∀r.T` to every `r`-neighbour of `x`
(`ht_all_rule_target_links`: forward links, the opposite end of the
ancestor link, and the connection-set predecessors whose link reads as an
`r`-link from `x`), and registers `S` in `x`'s reapply queue under `r`
(`addConceptToReapplyQueue(baseConDes, role, …)`). A later re-fire comes
from `apply_reapply_queue_concepts_restricted` for one freshly installed
link `L`; the restricted arm (`ht_rule_target_of_link`) adds `T` to the
opposite end of `L` when `L` reads as an `r`-link from `x`, with the same
hierarchy and inverse test (`ht_signed_role_matches`) that the full arm
applies to each link. Konclude's own arm (cpp 9662-9700) tests
`restLink->getLinkRole() == role`; the port's test accepts every link the
full arm accepts.

Claim. At every clash-free fixpoint of a completion run, for every live
node `x` (not merged, not purged, not blocked, not represented by a
satisfiability, signature, saturation or completion-graph cache), every
state `S` in `L(x)`, every transition `∀r.T` of `S` and every live
`r`-neighbour `y` of `x` through a link `L`: `T ∈ L(y)`. This is the
closure the all-successors arm reaches, so the two arms agree on every
clash-free graph, and the restricted arm adds a subset of what the full arm
adds, so every clash it finds is one the full arm finds.

Argument. Fix `x, S, ∀r.T, y, L` and the first processing of `S` at `x`.
(1) If `L` existed then, the full arm added `T` to `y`. (2) Otherwise `L`
was installed later, and every production install fires the reapply queue
of the endpoint that reads `L` as an `r`-link: `ht_install_role_successor_edge`
(u08; the link role's queue on the source, the non-inverted super roles on
the source, the inverted super roles and the mirror inverse link on the
destination), `create_new_individuals_links_reapplyed` (u10, one link per
indirect super-role entry in both orientations; the ABox assertion install
`install_native_role_assertion_edge` uses it) and
`create_new_individuals_link_reapplyed`. Merge relocation (u15
`ht_relocate_incoming_links`, `ht_relocate_nominal_connections`,
`ht_relocate_self_links`) installs through `ht_install_role_successor_edge`.
The non-reapplying installs (`create_new_individuals_links`,
`create_new_individuals_link`, `install_individual_node_role_link`, u35)
have no production caller. So `S` re-fires restricted to `L` and adds `T`
to `y`. (3) Merges move labels with the links: a merged-away `y` passes its
label to the merge target, whose relocated link is an install of case 2;
a merged-away `x` passes `S` to its target as a new concept, whose first
processing is case 1 or 2 there. (4) Backtracking restores the graph, the
labels and the reapply queues together (the queues live in the journaled
role-successor hash), so the case analysis holds in every branch state.
Nodes skipped as sources (blocked, cached) are skipped by both arms; their
targets are still checked, since a live source reaches them.

The argument rests on two facts of the port that are not visible in one
place: the reapply-queue registration under every transition role, and the
inverse entries of the indirect super-role lists (`role_chain_automata`
adds them for every created inverse role). Both are exercised by the
seeds below, and a closure check tests the claim directly.

Check. `KM_HT_AUTOMAT_CLOSURE_AUDIT=1` evaluates the claim at every
clash-free fixpoint of `run_completion_on` (u02) and counts each
`(x, S, ∀r.T, y)` with `T ∉ L(y)` (`ht_automat_closure_audit`, u10). The
transient audit of section 13 (`KM_HT_AUTOMAT_REST_LINK_AUDIT=1`) compared
the two arms in the middle of a run; its 122 reports were operands still
due from later re-fires or runs that end in a clash (the seeds c0 and c190
it named are inconsistent for HermiT), not misses of the closure. The
closure check has power: with the restricted re-fire dropped
(`KM_HT_AUTOMAT_REST_LINK_DROP=1`, a negative control) it reports misses on
113 of the first 300 chain seeds. Its first version also counted purged
targets (nodes pruned by a merge); the full arm writes into their stale
labels, but they are not elements of the graph, and the check now skips
them, as `ht_rule_target_of_link` does.

### 17.2 The subject probes on a retained graph

With the conditional-full schedule every class job runs on top of the
retained consistency graph (one branch epoch per job, popped at its end).
Two defects made each job pay for the size of that graph.

1. Journaled reads. Thirty-two reads of a node's label set
   (`getReapplyConceptLabelSet(false)`) and role-successor hash went through
   `ProcessContext::node_mut`. Under an open epoch `node_mut` saves a copy
   of the node for rollback, and `pop_branch_epoch` restores every copy.
   `get_blocking_individual_node_candidate_iterator` read every base node
   this way, and `is_individual_node_blocking` every candidate, so a job
   copied and restored thousands of base nodes (gdb samples on 10838: 15 of
   25 in `node_mut`, 6 in `pop_branch_epoch`). The reads now take a shared
   borrow; `get_reapply_concept_label_set(false)` and
   `get_reapply_role_successor_hash(false)` return the field unchanged, so
   the values read are identical and only the rollback journal shrinks.
2. A full scan per job and initialization concept. The anywhere-blocking
   candidate hash is per initialization concept and lazy: a fresh entry
   (`max_valid == 0`) walks every node id below the tested node and reads
   its label. A job's entries start from the base's, and the base had
   built none, so each job walked all base ids once per initialization
   concept (`KM_HT_BLOCKING_SCAN_TRACE=1`: every scan on 7557 starts at
   `max_valid=1` with 119,132 ids to walk, 0.1 s each). The bridge now
   builds a `BlockingBaseIndex` once at the retained base (per concept tag
   and polarity, the blockable, unpurged base nodes whose label holds it;
   0.02 s on 7557) and seeds a job's fresh entry with it, as a shared list
   that the job never copies. The entry is then in the state the lazy
   update would have reached had it run at the base: base nodes that a
   job switches or relabels are rechecked by the update's own tests
   (`max_valid`, the label-modification tag, the node-switch history), and
   the iterator skips purged and unblockable candidates as before. The
   candidate iterator merges the shared list with the job's own map in key
   order (`blocking_hash.rs`, `SharedCursor`), so the candidate order is
   the order of one map holding both.
3. A satisfiable-cache sweep of every base id per job. After each subject
   probe, `cache_satisfiable_individual_nodes` offers every node id from 1
   to the largest to the satisfiable-expansion caches. Konclude skips the
   nodes of a completion-graph-cached base in this sweep
   (`satisfiable_cache_write_in_completion_graph_range`); the bridge's
   retained base is not registered as such a cache, so every job offered
   all 119,132 base ids of 7557 again (gdb samples after the blocking fix:
   22 of 27 in this sweep). The first job still sweeps the base ids; later
   jobs start above the base. A skipped write omits a cache entry, which
   can cost an expansion in a later probe and cannot change a verdict.

None of the three changes alters a rule. The first changes no value read. The second
is meant to yield the candidate set of the scan; where it does not (a base
node relabelled in a job without a node-switch record would be missed), it
can change which blocker a job finds, or leave a node unblocked that the
scan would block, never the correctness of a blocking decision: every
candidate still goes through `is_individual_node_blocking` on the current
graph, a node without a blocker is expanded, and the job's own nodes (all
ids above the base) are scanned as before, which keeps the termination
argument of anywhere blocking.

### 17.3 Konclude's full-completion-graph decision

`native_conditional_full_abox_profile` selects the retained full
completion graph (the conditional-full schedule) or the per-probe ABox
completion. The port took only one arm of Konclude's decision, fewer than
10,000 individuals. Konclude's `ConditionalFullCompletionGraphConstruction`
(on by default; CTotallyPrecomputationThread.cpp 159-172, defaults in
CReasonerConfigurationGroup.cpp 1076-1103) builds the full graph unless an
exclusion condition holds (at least 300,000 individuals, or at least 50
individuals per concept) and when a suggestion condition holds (fewer than
10,000 individuals, or fewer than 5 individuals per concept). The bridge now
evaluates that whole decision (`konclude_full_completion_graph_suggested`),
counting the concept names of its input (`TInput::concepts`: classes,
definers, nominal proxies) as the terminology's concepts, the closest count
the bridge has to `CTBox::getConceptCount`. The four inputs have ratios
below 1 (10838: 55,433 individuals after the pre-merge against about
103,000 concept names), so Konclude's suggestion holds for them.

Konclude counts its own concept objects, which include every complex
subexpression and exclude per-individual proxies; its count can differ
from the bridge's, and on 10838 the local Konclude build (`Release/Konclude`,
v0.7.0-1138) logs no "Enabling full completion graph construction" line,
so it chose the lazy path there. The bridge has no counterpart of that lazy,
batched representative precomputation: its alternative re-completes the
ABox per subject probe (about 15 s per probe on 16315). The decision is
therefore Konclude's rule over the bridge's count, applied to the two
schedules the bridge has. Both are complete-or-defer, so the choice changes
cost and memory, never an answer. Two guards stay: a role-free ABox of
10,000 or more individuals keeps its validated independent-component
schedule (`independent_component_abox_profile`), and
`KM_HT_CONDITIONAL_FULL_LIMIT=<n>` still replaces the decision by the plain
bound for measurement.

### 17.4 Admission

`orchestrate/race.rs` installs the exact `SameIndividual` pre-merge on the
automatic HT racer (`KM_HT_NO_ADMIT_SAME=1` restores the decline). The
racer's contract is unchanged: the bridge answers completely or defers, and
a defer runs the exact CB fallback.

### 17.5 Result

On the default route, with no switches, on ws: ore_ont_16315 24 s
(1.3 GiB), 10838 59 s (2.4 GiB), 3087 61 s (2.5 GiB), 7557 97 s (4.0 GiB),
each with Konclude's reference taxonomy; before, all four timed out at the
CB stack's 18 GiB plateau. The closure check reports no miss on 6,000
seeds (the chain and `SameIndividual` pools of section 13 and 2,000 seeds
of four new merge families), against 113 of 300 for the negative control. The HermiT
differentials and the 112 nominal ORE inputs of the design half are
unchanged against the base. One pre-existing incompleteness of the reuse
of the consistency model, found by the new merge families and present on
the base, is recorded with its minimized seed in the results README; it is
not part of this change.

## 18. Probe-time merges on the reused consistency model, and dependencies of popped nodes (2026-11-02, `fix/v155-bridge-m413`)

Four defects, found from the m413 seed of section 17, the four panic
seeds of the same pool, and a new seed family built around m413's shape
(`results/agents/2026-11-02/bridge-m413/tools/gen_m413.py`). All four are
in the port, not in KM's admission or translation: with the reuse
switched off where that matters (`KM_BRIDGE_FRESH_ENV=1`,
`KM_BRIDGE_NO_PRECOMPUTATION_REPLAY=1`) the same `TInput` gives HermiT's
answer for 18.1 and 18.4, and 18.2 and 18.3 fail on a fresh environment
too. Measurements and seed counts are in
`results/agents/2026-11-02/bridge-m413/README.md`.

Background. With the precomputation replay on (a deterministic
consistency completion), every ABox nominal of a class job starts from
its representative-cache association with Konclude's backend blocks set:
`PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED` (its cached
successors stand in for the expansion) and
`PRFSYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED` (its asserted edges
are not materialized; the association's neighbour-role sets stand in
for them). A job that changes such a node must release the blocks
before the cached view stops being a correct stand-in. Konclude does so
in `detectIndividualNodeBackendCacheSynchronized` and its tests
(`testIndividualNodeBackendCacheNeighbourExpansionBlockingCritical`,
`testIndividualNodeBackendCacheExpansionBlockingCriticalCardinality`),
and then expands the influenced neighbours from the cache
(`expandDirectlyInfluencedIndividualNeighbourNodesFromBackendCache`).
The port's typed counterparts are `process_native_nominal_backend_retest`
(u36), the two tests (u20) and the selective expansion (u24, u27).

### 18.1 m413: the block of a changed nominal was never released

m413 (`data/m413-min.ofn`, 10 axioms): `f` functional below `r`,
`r ∘ s ⊑ t`, `t` transitive, `s(i3,i2)`, `t(i2,i0)`, `f(i3,i0)`,
`B ⊑ ∃f.{i3}`, `B ⊑ ∃f.B`, `i3 : ∀t⁻.D`. In the `B` probe the root's
`f`-successor carrying `B` merges into `i3`, so `i3` gets `B` and an
`f`-self-link; with `f(i3,i0)` the functional restriction merges `i0`
into `i3`, which turns `t(i2,i0)` into `t(i2,i3)`; the automaton of
`∀t⁻.D` at `i3` then runs `i3 -t⁻-> i2 -s⁻-> i3 -r⁻-> root` and gives
`D(root)`. Two defects stopped it (found with the graph dump
`KM_HT_GRAPH_DUMP=1`, which prints every node with its flags, label tags
and links at each clash-free fixpoint, and every merge).

1. *A role-successor count that was always 0* (u36
   `native_cardinality_critical_roles`). The cardinality test counts,
   per cached at-most role, the node's materialized links
   (`roleSuccHash->getRoleSuccessorCount(role)`), the cached existential
   successors while the successor block holds, and the cached neighbours,
   and releases both blocks when the sum exceeds the cached minimum
   restricting cardinality. The port read
   `IndividualProcessNode::get_role_successor_count`, a stub without
   arena access that returned 0. On m413 the count for `f` at `i3` was
   0 + 1 (cached `i0`) and never exceeded 1, so `i0` was never
   materialized and the merge never happened. The test now reads
   `ProcessContext::node_role_successor_count`, the arena-backed
   count; the stub is removed (its only other caller sat in a loop over
   an empty list). An audit of the other node-level accessors of
   `process/pn3.rs` found no further live production caller of a stub
   (the one in `try_delay_nominal_processing` only disables an
   optimization).

   Exactness. The count is now Konclude's value, except that the port
   keeps links to merged-away nodes in the hash (they are filtered at
   every successor scan, section 10), so it can be larger. A larger
   count only releases the blocks earlier. A released block makes the
   node expand its cached neighbours (asserted or deterministic edges,
   which hold in every model of the current branch) or replay its raw
   assertions: the exact route the bridge takes without the cache.
   Releasing a block never removes a derivation.

2. *A non-deterministic concept never made the block critical* (u20
   `test_individual_node_concept_backend_cache_neighbour_expansion_blocking_critical`).
   For a `∀`, at-most or automaton concept on a node whose association
   is completely propagated, Konclude's test is
   `!hasConceptInAssociatedFullConceptSetLabel(assoc, concept, neg,
   !nondeterministic)` (cpp 26314; line numbers in this section are those of the local Konclude source, `~/konclude-build`): the last argument selects the
   deterministic or the non-deterministic partition of the cached label.
   The port's comment quoted it with an extra `!nondeterministic &&`
   conjunct and the code followed the comment, so a concept that depends
   on a branch was never critical. On m413 the automaton state that
   `∀t⁻.D` puts on `i2` depends on the merge decision, so `i2` kept its
   block and its asserted edge `s(i3,i2)` never appeared; the state could
   not continue to `i3` and the root. The conjunct is gone; the test is
   now Konclude's.

   Exactness. The changed test can only answer "critical" more often.
   As for item 1, a critical block leads to the cache-backed or raw
   expansion of the node's neighbours, both exact.

The two other occurrences of the partition argument (u27
`can_expand_directly_influenced_neighbour_with_propagation`, both
membership tests) match Konclude. The port's
`test_individual_node_backend_cache_concepts_synchronization` is still
deferred, but the synchronisation flag it reads is never set in
production, so it answers "not synchronized" and leaves the last-synched
cursor unset: the criticality scan covers every new descriptor and
skips none.

*The previous suspect.* The deferred nominal-neighbour backend-expansion
sub-block of merge phase 5 (cpp 21241-21256; the port's comments cite it as 21155-21178,
`expandIndividualNeighbourNodeFromBackendCache` on a connected nominal
before its links are relocated) is not the cause and stays deferred. It
runs for a connected node of the merged-away node's connection set; in
m413 `i2` had no materialized link to `i0` at all (its block held), so
`i2` was not in `i0`'s connection set and the sub-block would not have
run in Konclude either. After the two fixes `i2`'s block is released by
its own changed label, which is the route Konclude takes.

*The retained consistency leaf (section 16).* The leaf is affected only
through the same tests, which every job runs. On the retained-base path
the leaf exists only when the consistency completion is
non-deterministic, and then the precomputation replay is off
(`BRIDGE-REPLAY disabled`), so no nominal carries a backend block: in
the leaf variants of m413 (`data/m413-leaf{1,2,3}.ofn`, a disjunction on
an ABox individual; the leaf is built with 1 or 2 decisions) every
nominal has flags 0 and its asserted edges materialized, and the
variants answer as HermiT before and after the change, with leaf reuse
on and off. On the per-job-reset path (no retained base) the leaf's ABox
is initialized with the replay installed, so blocks can occur there;
the fixes act in the code every job runs, so they apply to it in the
same way.

### 18.2 Dependencies of popped nodes (the forced-bridge panic)

m37, m337, m593 and m977 panicked on the forced bridge (index out of
bounds in `get_coressponding_individual_node_from_dependency_node`) and
timed out on the automatic route. Cause (m37): a disjunction with three
alternatives was refuted in all three, the sibling with an empty stored
refutation had no witness, so the root cancellation was withheld
(section 14) and the analysis went on with the collected closure. Its
descriptors come from the stored refutation of another sibling and
include deterministic dependencies (branching tag 0) that were derived
inside that sibling, among them the merge dependency of a node that the
sibling had created. The dependency spine is epoch-exempt (DDB marks must
survive the alternative), the node arena is not: the epoch pop truncated
the node, and the analysis read its slot. Konclude keeps the node object
alive in the task's memory; the port cannot. When no slot is past the
end, the same dependency reads a node allocated in the slot since, a
silent misattribution.

Fix (`process/context.rs`, `completion/u28.rs`, `u29.rs`, `u30.rs`,
`u22.rs`):

- Every branch epoch keeps a release frame (node-arena length at the
  push, a cursor into the dependency-node arena, a pending list). At each
  push and pop the dependencies created since the innermost cursor are
  filed under the innermost open epoch whose push-time node length is at
  most the index of their node, that is, the epoch that allocated the node
  (a node that predates every open epoch is never truncated by a pop).
  `pop_branch_epoch`, after the node arena is truncated, clears the
  appropriate individual of every dependency filed under the popped epoch
  that names a truncated node, and records it as released
  (`release_dependency_individuals_of_popped_nodes`). Each dependency is
  examined once. The first version rescanned every dependency above the
  epoch's mark at every pop, which is quadratic in the nesting depth and
  cost 0.6 s on ore_ont_4796 (a consistency leaf of 119 decisions, about
  120 nested epochs per leaf drop). The release test is self-validating
  (a dependency is released only if its node index is at or above the
  node-arena length after the pop), so a filed index that a spine
  truncation reused cannot be released wrongly.
- A dependency whose individual is set after it was filed (one factory
  sets it after allocation) is caught at read time:
  `get_coressponding_individual_node_from_dependency_node` releases a
  dependency whose node index lies past the node arena.
- A released dependency takes Konclude's path for a dependency without
  an appropriate individual: the backtracked descriptor keeps its
  parent descriptor's attribution. The port's version of that path
  re-read the parent's node; it now copies the parent's stored node id,
  level, nominal flag and error flag, as Konclude's
  `initTrackedClashedDescriptor(CTrackedClashedDescriptor*, ...)` does.
- In `try_get_invalid_same_individual_node_level_backtracked_*` a
  released individual has no level to compare; the descriptor is kept
  (the result for a differing level) instead of being backtracked early.
- A tracking line that met a released individual writes no
  unsatisfiability-cache entry.

Exactness. The walk of an analysis follows each descriptor's previous
track point and additional dependencies, which do not read the
individual, so the set of dependencies it visits, the non-deterministic
dependencies it reaches, the branching level and the stored refutations
are those of the walk with Konclude's stale node. The individual enters
only (a) the individual level of a descriptor, which orders the
processing of the tracking line and decides whether a no-concept
descriptor is backtracked now or later, (b) the involved-individual set,
which is never enabled in production (only self-tests set it), and (c)
the unsatisfiability cache, whose entry is the line's concept set taken
as one node's label. (a) changes the order of a fixpoint computation
over the same dependencies, (b) is inert, and (c) is suppressed, and an
omitted cache entry costs work, never a verdict. The release itself
changes nothing a live state reads: a released dependency named a node
that no longer exists.

What it rests on: that the port's DDB walk is Konclude's apart from the
attribution, the claim the bridge's DDB already rests on (sections 11,
14, 16). A live epoch keeps its nodes, so a slot is reused only after a
pop, and a pop releases every filed dependency that names a truncated
slot. The one case left is a dependency whose individual is set after
it was filed and whose slot is reused before it is read; it reads the
newer node, as the base code did for every dependency, and only its
attribution is affected.

### 18.3 The at-most reapplication in later alternatives

`k1414` (`data/k1414-min.ofn`, 7 axioms): `i1 : ≤1 s` with asserted
`s`-successors `i0`, `i2` (with `A`), `i5`, and `P1 ⊑ ∃s⁻.{i1}`. HermiT
entails `P1 ⊑ A`. The pair probe `P1 ⊓ ¬A` found a clash in the first
alternative of the at-most merge branch over the three ABox successors,
backtracked to its second alternative, merged the three successors
again, and ended at a clash-free fixpoint in which `i1` still had two
live `s`-successors (the merged ABox node and the probe root). Cause:
`apply_atmost_rule` installs the rule's reapplication
(`installReapplication`, cpp 15053-15057; the port cites 15001-15005) after the merge call, which
pushed the branch, so the registration lies in the epoch of the first
alternative; the pop before the advance removes it, and
`advance_atmost_merge_alternative` / `advance_atmost_qualify_alternative`
did not install it again. The link the probe installs at `i1` later
found no `≤1 s` in the reapply queue. Konclude's branch children copy
the parent's data box when they start, after the parent installed the
reapplication, so every alternative has it.

Fix (`completion/u02.rs`, `ht_rearm_atmost_reapplication`): both advance
functions install the same reapplication (the static role descriptor,
or the rest-carrying one when the branch has a branching-merging rest)
after the alternative's merge and bound re-check, exactly where the first
alternative has it, unless the parent's role queue already holds it (a
registration that predates the branch's epoch).
`KM_HT_DIAG_NO_ATMOST_REARM=1` turns the re-arm off (negative control).

Exactness. Every alternative now holds the registration the first one
holds. A reapplication re-runs the bound check of the at-most rule on
the current graph, which derives nothing that the rule does not derive;
missing it is what loses merges.

### 18.4 The selective expansion installed one edge per neighbour

`k163` (`data/k163-min.ofn`, 6 axioms): `g` inverse functional,
`g(i4,i5)`, `C(i4)`, `P2 ⊑ ∃g.{i5}` (and a functional `f` with
`f(i5,i4)`). HermiT entails `P2 ⊑ C`. When the probe element's
`g`-successor merges into `i5`, the cardinality test of 18.1 releases
`i5`'s blocks and the selective expansion walks `i5`'s concepts: `≤1 f`
expands `i5 -f-> i4`, then `≤1 g⁻` should expand `i5 -g⁻-> i4`, but
`i4` was already marked possibly influenced by the first install and
was skipped, so the inverse-functional merge never happened. Konclude
may mark the neighbour because its `expandIndividualNeighbourNodeFromBackendCache`
(cpp 23996-24040) installs every cached value toward that neighbour at
once, a non-inversed value as `node -role-> neighbour` and an inversed
one as `neighbour -role-> node`. The typed route
(`initialize_neighbour_expansion_with_propagation`, u27) installed only
the role of the concept being expanded.

Fix: after that install, `ht_expand_remaining_native_neighbour_values`
installs the other cached values toward the neighbour in both
orientations, with the per-value rule the typed route already applies
(deterministic values, and non-deterministic ones only when they are
asserted ABox edges). An inversed value whose source neighbour is merged
away or purged declines the cache-backed route (the caller replays the
raw assertions, the exact fallback), because this route has no merge
dependency for a source.

Exactness. Every installed edge is a cached value the same route already
installs when the expanded role matches it; the change installs it
without waiting for a concept of that role. `install_native_role_assertion_edge`
skips links that exist. The marking of the neighbour is now justified
in the way Konclude's is.

### 18.5 What the four fixes rest on

As for sections 10 to 17: the bridge has no Lean model and no
certificate covers a bridge answer. The arguments assume the port's
rules, merge and dependency machinery are Konclude's, and the typed
association's deterministic and asserted values are correct. They are
cross-checked differentially against HermiT only. Lean obligation
created: none discharged; a bridge model would have to show that a
released backend block, followed by the cache-backed or raw expansion,
yields the graph the unblocked expansion yields, and that the DDB walk
is independent of the descriptors' attribution.

### 18.6 Evidence

`results/agents/2026-11-02/bridge-m413/README.md` (before = development
63d6e63e, after = this branch):

- m413 and the four panic seeds answer as HermiT on the forced bridge and
  the automatic route (before: m413 missed `B ⊑ D` on both, the panic
  seeds panicked on the forced bridge and three of them timed out at 30 s
  on the automatic route).
- The m413 seed family (`gen_m413.py`, 2,000 seeds, HermiT gold): 113
  incomplete seeds on each route before, 0 after; a second batch of
  2,000 seeds: 0 differences after.
- Every seed pool with HermiT gold left by earlier agents (bridge-abox-probes,
  sameindividual-bridge, bridge-defers, bridge-nominal-merge,
  bridge-replay, the data and nominal pools of bridge-defers, and the
  gold-bearing fixtures of `results/agents/2026-10-3*/`; 13 pools,
  10,618 seeds, both routes): no answer lost; m413, the panic seeds and
  `nominal-r1600/m1` recovered.
- The 16 held-out ORE inputs of docs/V1.5.5-STATUS.md: identical output
  on all 16, times within noise (ratios 0.93 to 1.04).
- Library tests at the baseline (21 checker-bound failures), every
  integration target passing, regression test
  `engine/tests/bridge_probe_merge.rs`.

## 19. Value helpers disjoint from a folded object sort (2026-11-02, `fix/v155-bridge-auto-data`)

### 19.1 The decline

ore_ont_6132 and ore_ont_9899 (2.8 MB, 2,839 data-property assertions,
cardinalities) answered on the automatic route only when the bounded
bridge-first attempt finished inside its 8 s budget. When it declined, the
`certified_nominals` racer's bridge exited after 0.15 s. Its message, now
visible under `KM_TIMING` (19.4), was

    datatype gate: a linear value-encoding disjointness has an unsupported shape

The forced `ht_bridge` input and the racer's input differ in one respect
that matters here. The racer runs under `KM_NOMINALS=1`, so the frontend's
two-sorted encoding (`frontend/sorts.rs`) adds, for the object-sorted
definer `G` (`Q_201` on 6132), the facts `→ G(x) ∨ D(x)`, the sort clause
`G(x) ∧ D(x) → ⊥`, and `X(x) → D(x)` for every data range `X`, with
`D = __data__`. In the HT conversion the complementary-definer elimination
(`cb_to_ht::elim_complements`) folds the pair `⊤ ⊑ G ⊔ D`, `G ⊓ D ⊑ ⊥` into
`D := ¬G`. Every `X(x) → D(x)` becomes `G(x) ∧ X(x) → ⊥`, including one
clause for each helper of the linear value encoding
(`__dt__aux__digit__p__d`, `__dt__aux__profile__k`): 24 such clauses on
6132. `linear_value_encoding_exact` admitted a helper disjointness only
between two digits of one position or between a membership profile and a
datatype range, so it deferred.

### 19.2 The admission

The gate's argument (the comment on `linear_value_encoding_exact`) reads
each helper `H` as the union of the values `v` with a clause `v → H`, which
are the only clauses that imply a helper; a model of the clauses without
helpers then extends to a model of the helper clauses, so the helpers add
no consequence over the source vocabulary. The new shape `H(x) ∧ G(x) → ⊥`
with `G` not a helper is admitted when, for every value `v` with
`v → H`, the input contains the clause `v(x) ∧ G(x) → ⊥` itself. That clause
mentions no helper, so it holds in every model `M` of the remaining
clauses; `H^M = ⋃ v^M` is then disjoint from `G^M`, and the extension
satisfies the new clause. Any other helper pair, or a value of `H` without
its own disjointness from `G`, still defers ("a helper is disjoint from a
concept one of its values is not disjoint from"). On 6132 every value has
the clause, since the elimination folds `v → D` into `v ∧ G → ⊥` as well.

The change touches only `linear_value_encoding_exact`, and only clauses
that mention a value helper; inputs without helpers take the identical
path. No conversion, budget or routing rule changes.

### 19.3 Effect

Both inputs now pass the gate on every bridge input built from the nominal
clause set. On the automatic route the first exact attempt that applies is
the ground-rule data source (`data_source::automatic_candidate`), whose
bridge input carries the same folded sort; it previously declined at the
same gate after 0.2 s and now answers, before the bridge-first attempt and
the race are reached. The `certified_nominals` racer answers 6132 in 6.7 s
when forced. All answers equal Konclude's and HermiT's.

### 19.4 Defer reasons in the race trace

The race's HT worker had a null stderr unless `KM_HT_STATS` or `KM_HT_TRACE`
was set, so its `tableau error: konclude_ht bridge defer: <gate>` line was
lost. Under `KM_TIMING` the stderr is now piped and every error line is
repeated as `KM_TIMING race: HT worker reported: ...`
(`race::forward_ht_worker_errors`). The thread reads nothing else and never
touches the worker's output or exit status.

### 19.5 Two bridge tests that read the release flags

`conditional_full_class_probe_restores_all_root_consistency_base` and
`production_read_off_keeps_open_or_disjuncts_nondeterministic` failed
together in some full library runs. The cause is the environment of the
test process, not load or wall-clock budgets: measurement scripts that
export the release flags (`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 ...`) before
`cargo test`, such as `.work/v155-heldout-gap/combined/run.sh`, hand them to
every test. With `KM_HT_NATIVE_FULL=1` alone the first test fails
deterministically, even run by itself, at its premise that the number-free legacy fixture is
not on the conditional-full schedule (`native_cardinality_abox_profile`
reads the flag). With `KM_HT_DDB=1` alone the second fails at its premise
that dependency-directed backjumping is off (`configure_default_blocking`
reads the flag). No other library test changes its result under the flags.

Each premise now states the configuration the environment selects, and the
property each test checks (every fixed root retained on the restored base;
an open `OR` alternative never reported as a deterministic subsumer) passes
under both configurations. No production code reads time differently, and
no verdict changed.

### 19.6 Result

Automatic route, release flags, one core, ws under its normal shared load
(load average 16 to 27):

- ore_ont_6132, five runs: 23.3, 21.7, 22.0, 20.7, 21.5 s; ore_ont_9899:
  25.2, 21.6, 24.0, 24.2, 23.9 s. Every run answers through the ground-rule
  data source with the Konclude and HermiT answer. The base on the same
  host answered 6132 in 10.6 to 16.0 s (bridge-first inside its 8 s budget)
  and 9899 once in 13.3 s and four times not at all (240 s timeout).
  Scaled by the Ibex factor of 1.3 the branch stays near 33 s.
  The ground-rule bridge spends about 16 s on its 401 public subjects (30 to
  50 ms each), against 6.7 s for the whole `certified_nominals` racer;
  that per-subject cost is a separate performance question.
- The 16 held-out inputs keep their answers; times are within noise except
  6132 and 9899 (above). ore_ont_12128 publishes the same wrong taxonomy on
  base and branch whenever the `production_all` race finishes inside the
  cap (230 s on the base); it has no data values, so this change cannot reach
  it.
- Seed pools with HermiT gold, both routes, 60 s cap: 0 WRONG before and
  after, and 3 verdict transitions, all at the 60 s cap (timing).
- The 112 nominal ORE inputs of the design half: 109 identical signatures,
  no answer-status or route change, time ratio branch/base mean 1.041,
  median 0.987.

## 20. The saturation SELF rule (2026-11-02, `fix/v155-bridge-self`)

**Defect.** The bridge's approximation saturation refused every terminology
with a `CCSELF` concept (`saturation_refuses_terminology`): its
`applySELFRule` was a `todo!`. A SELF concept arises from `ObjectHasSelf`,
from `ReflexiveObjectProperty` (Konclude and the bridge both encode it as the
GCI `⊤ ⊑ ∃R.Self`, `CConcreteOntologyUpdateBuilder.cpp` 1751–1755) and from
`IrreflexiveObjectProperty` (`⊤ ⊑ ¬∃R.Self`). On ore_ont_12128 (two
reflexive roles, `has-part` and `part-of`) the refusal left the bridge
without a saturated base, so each of its 187,518 classes needed its own
completion job (about 1.6 ms each) and the input timed out at 240 s.
Konclude decides most of these classes in its saturation.

**Konclude's mechanism.** `CCalculationTableauApproximationSaturationTaskHandleAlgorithm`
maps `CCSELF` (positive) to `applySELFRule` (cpp 77, 6843–6890); a negated
SELF has no jump entry and falls to `applyELSERule`, which flags the node
INSUFFICIENT. `applySELFRule` walks `role->getIndirectSuperRoleList()`
(which starts with the role itself and carries every super role in both
polarities) and, for each entry `(S, neg)`:

1. adds `S`'s domain concepts (`getDomainRangeConceptList(neg)`) and range
   concepts (`getDomainRangeConceptList(!neg)`) to the node, with the
   label-set overload and `updateCopyDependedIndividual = false`;
2. allocates a `CBackwardSaturationPropagationLink(processIndi, S)` and adds
   it with `CRoleBackwardSaturationPropagationHash::addSelfConnectedBackwardPropagationLink`
   (`CRoleBackwardSaturationPropagationHash.cpp` 82–93): set the hash's
   `mSelfConnected`; if the role's head link already has this source,
   return null; else prepend the link, set the role's `mSelfConnected` and
   return the role's reapply descriptors;
3. replays the returned descriptors with `applyBackwardPropagationConcepts`
   on the node itself.

A backward link `(S, source P)` on a node `Y` means that `P` is an
`S`-neighbour of `Y` in the sense that `∀S.C ∈ L(Y)` must put `C` into
`L(P)`: `applyALLRule` (cpp 6143–6175) registers its descriptor under its
role and walks the role's links. Successor creation installs such links
for the negated super-role entries (cpp 7040–7050). For a self edge
`R(x,x)` every super role `S` of `R` and every inverse `S⁻` holds on
`(x,x)`, so the link `(S, x)` on `x` is correct for both polarities; this
is why the rule does not test `neg` before installing it. `∀S.C` added
later finds the link through `applyALLRule`; `∀S.C` already present is
replayed in step 3. Node copies keep the self edges:
`copyRoleBackwardSaturationPropagationHash` re-creates a self link to the
new node for every role whose `mSelfConnected` is set (ported in
`ProcessContext::copy_role_backward_saturation_propagation_hash`).

No other part of Konclude's concept saturation treats SELF specially:
`CExtractPropagationIntoCreationDirectionPreProcess` does not count SELF as
a creating operator (`CCFS_POSSIBLE_ROLE_CREATION_TYPE`), and the
satisfiable-cache test (cpp 4773) already lists `CCF_SELF` (ported in
`s08.rs`). The individual saturation's representative-cache writer
additionally collects self-restriction roles
(`CSaturationNodeBackendAssociationCacheHandler::collectSelfRestrictionRoles`,
cpp 225–250); the port's writer (`write_native_abox_representative_cache`)
has no counterpart.

**Change.**

1. `saturation/s03.rs` `apply_self_rule`: the transcription of cpp
   6843–6890 above, over `saturation_indirect_super_roles` (the
   reflexive-entry view that every other saturation super-role walk uses).
2. `process/context.rs`
   `sat_node_add_self_connected_backward_propagation_link`: the per-role
   `self_connected` flag is now set only when the link is appended, as in
   cpp 82–93 (it was set also on the duplicate-head early return). The
   helper had no production caller before this change.
3. `bridge.rs` `saturation_refuses_self_terminology`: the concept
   saturation no longer refuses SELF. The native-nominal individual
   saturation (`bridged.has_native_nominals()`, or a native consistency
   prefix) keeps the refusal, because its representative-cache writer lacks
   `collectSelfRestrictionRoles`; the conditional-full nominal schedule
   (`card_nominal_profile`) keeps its completion-only branch for the same
   reason. `KM_BRIDGE_SAT_REFUSE_SELF=1` restores the old behaviour
   everywhere, including point 6 (used for the before columns below).

Three guards are not in Konclude. Each one only defers work to the exact
completion (an INSUFFICIENT node is never a saturation verdict and never a
caching target; a missing expansion cache only means the completion expands
every node itself), so none of them can change an answer. Guards 5 and 6
are backed by HermiT disagreements of the unguarded port; guard 4 follows
`createSuccessorForConcept`.

4. *Disjoint roles* (`apply_self_rule`): if a super role has disjoint roles,
   the node is flagged INSUFFICIENT and `setInsufficientNodeOccured` is
   called, as `createSuccessorForConcept` does for such roles (cpp
   7026–7029). A self edge on such a role can clash (two disjoint roles
   self-related on one node; an asymmetric role, which the bridge encodes
   as disjoint from its inverse), and no saturation rule inspects self
   edges for role disjointness.
5. *At-most on a self-edge role* (`apply_self_rule` for an at-most already
   in the label, `apply_atmost_rule` for one that arrives later, with the
   helpers `sat_node_has_self_edge_for_role` and
   `sat_node_label_has_atmost_on_role` in `saturation/s04.rs`): a node whose
   SELF edge lies on a role that one of its at-most restrictions
   constrains is flagged INSUFFICIENT. The self edge fills one neighbour
   slot of that role, and neither the critical at-most check (it counts
   linked successors) nor the completion's saturation caching counts it:
   with `InverseFunctional(s)` and `B ⊑ ∃s.(F ⊓ ∃s.Self)`, the
   `s`-successor of a `B` node equals that node, so `B ⊑ F`; the unguarded
   port cached the successor against its saturated node and missed the
   merge (seed `v1s102`, `v1s1838`). The hash-level `self_connected` flag
   is set only by the SELF rule (and copied with a node), so the guard is
   inert on SELF-free terminologies.
6. *Expansion caches* (`bridge.rs` `positive_self_terminology`,
   `KM-SOUNDNESS-GATE[self-satexp]`): when the terminology has a SELF
   concept that can create a self edge (every SELF concept except the
   negated ones built for irreflexivity), the bridge installs neither the
   satisfiable expander cache nor the saturation-node associated-expansion
   cache. Both key a node's satisfiability on its own label (and
   ancestors), and with self edges that locality fails in the port. Two
   witnesses:
   - the base's published answer on ore_ont_12128 (below): 1,567 of
     Konclude's 4,716 unsatisfiable classes;
   - `∃p.Self ⊓ ≤1 p⁻` is satisfiable on its own but merges with every
     `p`-predecessor, so an expansion recorded for a root does not carry
     over to a successor (seeds `v1s160`, `v1s1420`, `v1s1543`:
     `Q1 ⊑ ≥1 p.(∃p.Self)` with `InverseFunctional(p)` and `Range(p, F)`
     entails `Q1 ⊑ F`).
   On the same terminologies the completion also does not expand created
   successors from saturated labels (`conf_expand_created_successors_from_saturation`
   off): on the SELF seed `s9` that expansion made the completion
   non-terminating (0.02 s without the saturation, no answer within 60 s
   with it); caching blocking stays on and still requires a sufficient,
   completed saturation node.
   Without either cache and without the label expansion the completion
   expands every node itself, which is Konclude's algorithm with these
   options configured off, so the gate can only cost time. Irreflexivity concepts are excluded because they never
   create a self edge; with them included ore_ont_9899 (five irreflexive
   roles) lost both caches and went from 11.5 s to a timeout.

**The incomplete base answer on ore_ont_12128.** With a 400 s cap the base
(68ad4132, and this branch with `KM_BRIDGE_SAT_REFUSE_SELF=1`) publishes the
`production_all` race's bridge answer after about 230 s with 1,567
unsatisfiable classes; Konclude and this branch report 4,716
(`compare_ref.py`: `konclude=taxonomy_disagreement` before, `agreement`
after). The 3,149 missed classes are all reported satisfiable; none is
reported unsatisfiable wrongly. Cause: on the base the saturation refuses
SELF, so every class is decided by a completion job, and those jobs install
the satisfiable expander cache. A syntactic-reachability module of one
missed class (1,165 axioms, `data/12128-incomplete/m53.ofn`) shows the same
defect (28 of HermiT's 40 unsatisfiable classes on the base; 40 with
`KM_HT_NO_SAT_EXP_CACHE=1`; 40 on this branch), and delta debugging reduces
it to 23 axioms (`m53tiny.ofn`): `world_of_Model53 ⊑ Continuant ⊓
∃has_part.∃has_part.GO_0005518` with `GO_0005518 ⊑ Function`,
`Disjoint(Continuant, Function)` and `Continuant ⊑ ∀has_part.Continuant`
is unsatisfiable without any self edge, but the base reports it
satisfiable as soon as `ReflexiveObjectProperty(part_of)` and an unrelated
`FunctionalObjectProperty(quality_of)` are present, and only with the
expander cache. Removing either axiom, or the cache, restores HermiT's
answer. I did not isolate the exact cache entry that goes wrong; the gate
in point 6 removes the cache wherever a self edge can exist, which covers
this case and every other one of its kind. The integration target
`engine/tests/bridge_self.rs` pins the reduction and the SELF seeds for the
automatic route and for `ht_bridge` with and without the saturation; with
`KM_BRIDGE_SAT_REFUSE_SELF=1` the reduction fails on both routes. (The
library entry `bridged_classify_opts` does not reproduce it; only the
orchestrated route does.)
On this branch the saturation decides 187,377 of the 187,518 classes of
ore_ont_12128, but the residue, the pair probes and the batch refutations
are completion jobs, so the gate is needed there too.

Konclude 0.7.0 does not terminate within 60 s on the four smallest of these
seeds (it stays in "Precomputing ontology"), so it gives no reference for
them; HermiT does.

**Why the verdicts stay exact.** The saturation's verdict contract is
unchanged: a clashed node certifies unsatisfiability, an unflagged node
certifies satisfiability with its positive named labels as the complete
subsumer set, and an INSUFFICIENT, UNPROCESSED or problematic EQ-candidate
node defers to completion (`extract_saturation_outcome`). The SELF rule
adds only consequences that hold in every model of a node with a self edge
(the domain and range of every super role, universal restrictions along the
edge in both directions), so it never turns a satisfiable concept into a
clashed node. Conversely, an unflagged node with a self edge is a model
witness for that edge: every `∀S.C` on the node reaches the node itself
(step 3 for restrictions already present, `applyALLRule` for later ones),
its domain and range concepts are in the label (step 1), negated SELF
(irreflexivity) flags the node INSUFFICIENT through `applyELSERule` as in
Konclude, and the two interactions that no saturation rule sees, role
disjointness and at-most counting, are deferred by guards 4 and 5. Guard 6
removes the one completion-side reuse that fails with self edges.

Probes (`results/agents/2026-11-02/bridge-self/data/micro/`): a self edge
with a functional role, an unqualified and a qualified at-most, an
inverse-functional role and an existential successor, an asymmetric role,
`∀r⁻` and a transitive super role. In each the final answer equals
HermiT's.

**Result.** ore_ont_12128 on ws, release flags, alone: the base
configuration times out at 240 s (2.18 GiB) and, with a 400 s cap,
publishes after 229.8 s (2.74 GiB) a taxonomy that disagrees with Konclude
(1,567 of 4,716 unsatisfiable classes, 3,149 missed). This branch answers in
37.5 s (2.19 GiB) with Konclude's taxonomy (`compare_ref.py`: agreement);
the saturation answers 4,716 unsatisfiable and 182,661 satisfiable subjects
of 187,518 in 4.8 s and leaves 141 to completion. Validation, seed pools
and the held-out and nominal ORE pairings: `results/agents/2026-11-02/bridge-self/README.md`.

## 21. Reflexive roles next to functional roles: three bridge defects (2026-11-03, `fix/v155-bridge-reflexive`)

**Defect.** The cb-s974 agent's merge family
(`results/agents/2026-11-03/cb-s974/README.md`) left five seeds that KM
answered wrongly through the bridge in the race's HT-first phase (merge526,
merge1322, merge1585, merge1708, merge1722), on rc1 as well. Two
reductions came with them: `min1722` (inconsistent; the bridge said
consistent) and `min526` (eleven subsumptions under `Q3` missed). Each seed
combines a reflexive role, directly or through an inverse pair, with
functionality or inverse functionality, so that every neighbour along the
role collapses into the node. Three separate port defects produce the
five answers; none of them is in the CB calculus or the frontend.

**Gold.** Konclude 0.7.0 does not finish on these inputs (it stays in
precomputation, also on the four-axiom reductions below), and no Openllet
or JFact installation exists on ws, so the HermiT answers are checked by
hand.

- `min1722`: `p` is the inverse of `r` and reflexive, so `r` is reflexive;
  `p` inverse functional makes `r` functional. A reflexive functional role
  is contained in the identity: from `r(x,x)` and `r(x,y)`, functionality
  gives `y = x`. Every element then has exactly one `r`-predecessor (itself),
  so `≤1 r⁻ ⊑ B` puts every element into `B`, and `B ⊑ ≥3 r` contradicts
  functionality. Inconsistent.
- `min526`: `r` is reflexive and inverse functional, `p = r⁻`. For
  `r(x,y)`, reflexivity gives `r(y,y)`, and inverse functionality on
  `r(x,y)`, `r(y,y)` gives `x = y`: `r`, and with it `p`, is contained in
  the identity, and every element is `r`- and `p`-related to itself.
  `∀p.Self(p)` holds everywhere (the only `p`-successor of `x` is `x`, and
  `p(x,x)`), and `≤1 p⁻` holds everywhere (the only `p⁻`-successor of `x` is
  `x`), so `Q3 ≡ ⊤` and every class is under `Q3`. `F ⊑ ∃r.(C ⊓ Self(p))`
  with the only `r`-successor being `x` itself gives `F ⊑ C`, and
  `E ⊑ ∀p.F` with `p(x,x)` gives `E ⊑ F ⊑ C`. The one-element model with
  `r = p = {(a,a)}`, `s = ∅` and every class true is a model, so the
  ontology is consistent. The derivation gives 11 subsumptions (eight
  classes under `Q3`, `E ⊑ F`, `E ⊑ C`, `F ⊑ C`), exactly HermiT's list.
- The reductions of the three remaining seeds (`merge1322_min`,
  `merge1585_min`, `merge1708_min` in
  `engine/tests/fixtures/bridge_reflexive/`) are checked in the paragraphs
  of their defects below.

### 21.1 The at-least rule counted neighbours that were not distinct

`apply_atleast_rule` (`completion/u08.rs`) skipped the successor generation
of `≥n R.C` whenever the node had `n` qualified `R`-neighbours. Konclude
(cpp 16145) calls `hasDistinctRoleSuccessorConcepts` (cpp 20255–20290),
which counts only neighbours that the distinct hash separates; the port
has a faithful transcription of that function
(`has_distinct_role_successor_concepts`, `u35.rs`) but the rule used the
plain neighbour count `ht_role_successors_with_concepts(...).len()`.

With a reflexive role every node is its own `R`- and `R⁻`-neighbour. In
`min1722` (reduced to `selfloop_atleast`: `r` reflexive and functional,
`⊤ ⊑ B ⊔ ≥2 r⁻`, `B ⊑ ≥3 r`, `E ⊑ ∃r⁻.A`) the trace
(`KM_BRIDGE_SEARCH_LOG`) shows the root `x` taking `≥2 r⁻`, finding `x`
itself and the `∃r⁻.A` successor `y` as two `r⁻`-neighbours, and creating
nothing. `y`'s functional `r` (its neighbours `y` and `x`) then merged `y`
into `x`, leaving `x` with one `r⁻`-neighbour, and the at-least restriction
was never applied again: a clash-free graph for an inconsistent input.

**Change.** The rule is skipped only when `cardinality` of the qualified
neighbours are pairwise distinct (`ht_has_pairwise_distinct_subset`, a
bounded clique search over the nodes' distinct hashes).

**Exactness.** This is the applicability condition of the `≥`-rule of the
SROIQ tableau (Horrocks, Kutz and Sattler 2006): the rule applies unless
there are `n` safe `R`-neighbours `y1 … yn` with `C ∈ L(yi)` and
`yi ≠̇ yj` for `i ≠ j`. Konclude's own test is a star around one neighbour
(each of the counted neighbours is distinct from the first), which for
`n ≥ 3` accepts sets that the clique test rejects; the clique test is the
stricter of the two. A stricter skip condition only applies the rule in
more situations, and every application of the `≥`-rule is sound for
satisfiability (it adds `n` fresh, pairwise distinct `R.C`-successors, which
any model of the node's label provides), so no unsatisfiable input becomes
satisfiable and no clash becomes spurious. Conversely the old count could
declare `≥n R.C` satisfied by fewer than `n` elements, which is the defect.
When the search budget (100,000 steps) is exhausted the answer is "no
clique", so the rule generates fresh successors: permitted, and only a cost.
Termination: after one application the new successors form a clique, so the
rule does not fire again on the same restriction until a merge or a prune
removes one of them, as in the standard argument.

### 21.2 Optimized blocking did not count the blocker's self link

`is_label_concept_optimized_blocking` (`completion/u19.rs`) transcribes
Konclude's B1–B6 test (cpp 18545–18790). For an at-most restriction
`≤n R.C` in the blocker `w'` on the role `R` of the edge from the blocked
node `w` to its predecessor `v`, B3/B5 count `w'`'s `R`-successors (nodes
deeper than `w'` and nominals) and keep the block only if fewer than `n`
of them carry `C` (cpp 18695): in the model the copy of `w'` that replaces
`w` has `v` and the copies of those successors as `R`-neighbours. A self
link of `w'` is neither deeper than `w'` nor a nominal, so it was not
counted. But the copy of `w'` keeps `w'`'s self edges (its label carries
the `∃R.Self` concepts, and the SELF rule recreates the edge), so the copy
has one `R`-neighbour more than counted.

`merge1322_min` (HermiT: `E`, `Q1` unsatisfiable) reduces further to
`selfloop_blocker`: `r` and `s` reflexive, `⊤ ⊑ ≤1 s⁻`,
`⊤ ⊑ ∃s⁻.F`, `Disjoint(E, F)`, `≥2 r⁻ ⊑ E`, `Q1 ⊑ ≥3 r`. Every element `x` is
in `F`: its `∃s⁻.F` successor `y` gives `s(y,x)`, reflexivity gives
`s(x,x)`, and `≤1 s⁻` at `x` gives `y = x`. Hence no element is in `E`,
and every element has at most one `r`-predecessor; each of the three `r`-successors of a `Q1` element has
two (the `Q1` element and itself, by reflexivity), so at least two of them
equal the `Q1` element, against their distinctness: `Q1` is unsatisfiable.
In the base graph (`KM_HT_GRAPH_DUMP`) the three successors of the `Q1` root
are DIRECTBLOCKED by the root itself, before their labels are expanded:
`≤1 r⁻` is in the root's label, the root's `r⁻`-successors deeper than the
root are none, and the root's `r⁻` self link was not counted.
`merge1708_min` is the same defect on `p`: `⊤ ⊑ ≤1 p⁻`, `B ⊑ Self(p)`,
`B` for every element (by `InverseFunctional(s)` and `≤1 s⁻ ⊑ B`),
so `p` is contained in the identity and `Q3 ≡ ≤2 p.C` is `⊤`; HermiT agrees,
and the base missed `B ⊑ Q3` and `C ⊑ Q3`.

**Change.** In the B3/B5 walk a self link of the blocker counts like a
successor (`succ_indi_node == w_pred_node`, `KM-SOUNDNESS-GATE[self-blocker]`).

**Exactness.** The soundness proof of the optimized blocking condition
builds the model by replacing each blocked `w` with a copy of `w'`; B3/B5
are there to keep every at-most restriction of `w'` satisfied at the copy,
whose `R`-neighbours are `v` plus `w'`'s non-predecessor `R`-neighbours.
With self edges those include `w'` itself, so the count has to include the
self link; with the change the B3/B5 premise of that proof holds again.
The change can only refuse blocks (it adds to a count that must stay below
`n`), so it never makes a clash-free graph out of one that had a clash
(soundness of unsatisfiability verdicts is untouched, and blocking less is
never incomplete). B4a (at-least restrictions of `w'` met by its
successors) still ignores the self link, which can only refuse more blocks.
Terminologies without SELF concepts have no self links, so the test is
unchanged for them.

### 21.3 Saturation caching without the saturated expansion

Section 20 (point 6) turned off `conf_expand_created_successors_from_saturation`
for terminologies with a positive SELF concept and kept
`conf_caching_blocking_from_saturation`. Konclude creates a successor
(`createSuccessorIndividual`, cpp 21692–21728) by first copying the
saturated label into it (`tryExpansionFromSaturatedData`) and only then
caching it against its saturation node (`tryEstablishSaturationCaching`,
cpp 21731). The copied label carries the concepts that the saturation
derived for the successor, among them the universal restrictions and
triggers that propagate back to the predecessor; the cached successor still
applies those along its predecessor link. Without the copy the successor
holds only its creation label, and the caching then declares its subtree
done: whatever the saturation would have sent back to the predecessor is
lost.

`merge1585_min` (four axioms: `Q2 ≡ ∃r.(≥1 s.C)`, `F ⊑ ∃r.∃s.C`, plus a
SELF axiom on an unrelated class and an at-least on `r⁻`): `F ⊑ Q2` holds
trivially (`≥1 s.C` is `∃s.C`), HermiT agrees, and the base missed it. In
the base graph the `r`-successor of the `F` root is SATURATIONBLOCKINGCACHED
with the label `{⊤, ∃s.C}`; with the expansion on (SELF axiom replaced) it
carries two more concepts from its saturation node and the root receives
the trigger that derives `Q2`. `KM_HT_NO_SAT_CACHING_BLOCKING=1` and
`KM_BRIDGE_SAT_REFUSE_SELF=1` both restore the answer.

**Change.** Under the section 20 gate both options go off together
(`bridge.rs`, the `self_cardinality` branch of the production coupling).

**Exactness.** Saturation caching and the saturated expansion are
optimisations of the completion; with both off the completion expands every
node itself, which is Konclude's algorithm with these options configured
off. The change removes a cache, so it can only cost time; ore_ont_12128
(two reflexive roles, the input the section 20 gate was built for) answers
in 36.1 s with the caching and 35.9 s without it on the same binary.

### 21.4 Results

All numbers in `results/agents/2026-11-03/bridge-reflexive/README.md`.
The five seeds, `min1722`, `min526` and the three new reductions agree with
HermiT on `ht_bridge` and on the automatic route in 20 of 20 runs (base: all
wrong). A sibling family of 2,000 generated seeds around both reductions
(`tools/gen_reflexive.py`, HermiT gold, three runs per seed and route) has
50 wrong rows on the base (25 seeds on each route) and 12 after the change:
two seeds, refl1008 and refl439, wrong identically on the base. Both reduce
to an at-most restriction at a nominal over a blockable neighbour that the
nominal did not create (`f1008`: `≤1 s.(∃p.{c}) ⊑ C` with
`InverseFunctional(p)`; the second `s`-successor is blocked by its sibling,
whose `p`-successor merged into `c`). That is Konclude's NN-rule
(`applyFUNCTIONALRule`, `requiresNNRule`), which the port leaves W3-DEFER;
it is not a reflexive-role defect and is not fixed here. The gold-backed
seed pools of earlier agents, the 16 held-out inputs and the 112 nominal
ORE design-half inputs keep their answers; times are unchanged within noise.

## 22. The NN-rule: nominals under at-most restrictions (2026-11-04, `fix/v155-bridge-nn-rule`)

**Defect.** Section 21 left two seeds of the reflexive family that KM answered
wrongly on both routes, on the base and on rc1 (`refl1008`, `refl439`). Both
reduce to an at-most restriction at a nominal over a blockable neighbour that
the nominal did not create, and both need Konclude's NN-rule, which the port
had marked W3-DEFER (`u08.rs`, the `applyFUNCTIONALRule` stub and the
`mergeMergingIndividualNodes` comments).

- `f1008` (two axioms): `≤1 s.(∃p.{c}) ⊑ C`, `InverseFunctional(p)`.
- `f439` (five axioms): `Q2 ≡ {c} ⊓ ≤1 r`, `ReflexiveObjectProperty(r)`,
  `InverseFunctional(p)`, `E ⊑ ∃r⁻.∀r⁻.{c}`, `Q5 ≡ ≤1 s⁻.(∃p.E)`.

**Gold, by hand.**

- `f1008`. Let `x` be any element and `y1, y2` two `s`-successors of `x` in
  `∃p.{c}`: `p(y1,c)` and `p(y2,c)`. Inverse functionality of `p` gives
  `y1 = y2`. So every element satisfies `≤1 s.(∃p.{c})`, and `⊤ ⊑ C`. The
  one-element model with every class true and every role empty shows
  consistency. Every class is under `C`: HermiT's eight subsumptions.
- `f439`. Let `x ∈ Q2`; then `x = c` and `c` has at most one `r`-successor.
  `r` is reflexive, so `r(c,c)` and `c` is that successor. Let `e ∈ E`. It
  has an `r⁻`-successor `y` (`r(y,e)`) with `y ∈ ∀r⁻.{c}`: every
  `r`-predecessor of `y` is `c`; `r(y,y)` makes `y` its own predecessor, so
  `y = c` and `r(c,e)`; the bound at `c` gives `e = c`. Now let `z1, z2` be
  `s`-predecessors of `c` with `p(z1,e1)`, `p(z2,e2)` and `e1, e2 ∈ E`. Both
  `e1` and `e2` equal `c`, so `p(z1,c)` and `p(z2,c)`, and inverse
  functionality gives `z1 = z2`: `c ∈ ≤1 s⁻.(∃p.E) = Q5`. Hence
  `Q2 ⊑ Q5`. No other subsumption between the named classes holds. In
  `M1` (domain `{c, d}`, `r` the identity, `s = p = ∅`, `E = ∅`) the axioms
  force `Q2 = {c}` and `Q5 = Δ`; in `M2` (domain `{c, e1, e2, z1, z2}`,
  `r` the identity plus `(c,e1)`, `(c,e2)`, `p = {(z1,e1), (z2,e2)}`,
  `s = {(z1,e1), (z2,e1)}`, `E = {e1, e2}`) they force `Q2 = ∅` and
  `Q5 = Δ ∖ {e1}`. The other classes are free in both. `M1` refutes every
  `Q2 ⊑ X` with `X ≠ Q5`, every `X ⊑ E` and `X ⊑ Q2` (put `d` in `X`), and
  every `Q5 ⊑ X`; `M2` refutes every `X ⊑ Q5` with `X ≠ Q2` (put `e1` in
  `X`), including `E ⊑ Q5`, and every `E ⊑ X`. Two free classes are
  separated in either model. So `Q2 ⊑ Q5` is the only subsumption, as
  HermiT says.
- For `f1008` the same holds for the classes other than `C`: with every role
  empty and `C = Δ` every axiom holds and the other classes are free.

The CB engine gets both right (below), so the gold is also confirmed by a
second, independent calculus.

**Trace on the base.** `f1008`, the probe of `¬C` (`≥2 s.(∃p.{c})`) on a
root `x`: the completion creates two distinct `s`-successors `y1`, `y2`;
`y1`'s `p`-successor carries `{c}` and merges into the nominal `c`, which
leaves the link `y1 --p--> c` (creator `y1`). `≤1 p⁻` holds at `c` (one
`p⁻`-neighbour), and `y2`, whose label is a subset of `y1`'s, is
DIRECTBLOCKED by `y1` before it expands (`KM_HT_GRAPH_DUMP`, node 1002
flag `0x…01`). The graph is clash-free, and the probe reports `¬C`
satisfiable. The blocked `y2` would be unravelled into a copy of `y1`, a
second `p`-predecessor of `c`, which `≤1 p⁻` at `c` forbids: blocking by a
node that reaches a nominal from outside is unsound for the bound at that
nominal. `f439` has the same shape twice (`≤1 r` at `c` over the element
`e` that reached `c` through its reflexive `r⁻`-successor, then `≤1 p⁻` at
`c` over the blocked `s⁻`-neighbour).

**Konclude's rule.** Konclude (cpp line numbers of the local source,
`~/konclude-build/Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`)
treats a nominal's neighbour that it did not create in two places:

1. `applyFUNCTIONALRule` (cpp 14741-14871), which handles every unqualified
   `≤1 R` (cpp 14886 delegates to it). At a nominal node with an
   `R`-successor, the pre-scan (cpp 14756-14777) sets `requiresNNRule` when
   some `R`-link was created by another node
   (`link->getCreatorIndividualID() != processIndi->getIndividualNodeID()`)
   and stops at the first nominal successor (`hasAlreadyMergingNominal`).
   Without a nominal successor and with `requiresNNRule`,
   `createNominalsSuccessorIndividuals(processIndi, role->getIndirectSuperRoleList(), role, …, nnRequireDepTrackPoint, 1)`
   (cpp 14780-14789, body cpp 22314-22331) creates one fresh node of type
   NOMINAL at nominal level `level(x)+1`, linked by every indirect super role
   under the link's dependency, and makes it the merge target. Every other
   `R`-successor is then merged into the target, deterministically, under a
   `FUNCTIONAL` dependency of the at-most concept and both links (cpp
   14812-14857), with `getMergedIndividualNodes` choosing the direction
   (a nominal absorbs a blockable node; between nominals the lower level
   wins, cpp 20993-21038). A successor that cannot be merged is the
   functional clash (cpp 14858-14863).
2. `mergeMergingIndividualNodes` (cpp 15146-15526), every other at-most.
   `fixedNominalMerging` holds when the node is a nominal and a merge
   candidate is blockable and the creator of its link
   (`isCandidateBlockableAndCreator`, `CBranchingMergingIndividualNodeCandidateLinker.cpp`
   80-82; recorded in `CBranchingMergingProcessingRestrictionSpecification.cpp`
   194-196, 230-232). The distinct set is then rebuilt from scratch with
   `cardinality` new-nominal slots (cpp 15201-15257). With
   `LazyNewMergingNominalCreation` (default on,
   `CCalculationConfigurationExtension.cpp` 386-391) each candidate either
   merges into a mergeable representative (a branch per choice, cpp
   15465-15540) or, while slots remain, becomes a new representative: a
   non-nominal candidate is moved into a fresh empty NOMINAL node by
   `getIntoEmptyMergedIndividualNode(candidate, true, processIndi, …)`
   (cpp 15443-15470, body cpp 21047-21063).

Both are the NN-rule of the SROIQ tableau (Horrocks, Kutz and Sattler 2006):
a blockable neighbour of a nominal under an at-most restriction is replaced by
a nominal node, so that it can neither block nor be blocked, and the bound is
then enforced over nominal neighbours only.

**Change.** `completion/u08.rs`, `ht_apply_nn_rule`, called at the head of
every iteration of the production at-most loop (`ht_apply_atmost_merge`),
after the choose rule and before the count, so it runs on the first
application, on every reapplication through a new link, and in every merge
alternative (`advance_atmost_merge_alternative` re-enters the loop).
`KM_HT_NO_NN_RULE=1` turns it off (negative control); `KM_HT_NN_TRACE=1`
prints each application.

1. *Functional arm* (`≤1 R` without qualifier, at a nominal `x`): the
   pre-scan above over the live `R`-links (`ht_role_successor_links`, which
   skips merged-away and purged nodes). The arm applies when
   `requiresNNRule` holds and some successor is blockable. The target is the
   first nominal successor, or a fresh nominal created by the port of
   `createNominalsSuccessorIndividuals` (`u16.rs`, now returning the created
   node and its link; it had no caller before). Every other successor is
   merged into the target through `get_merged_individual_nodes` (the port of
   cpp 20993-21038) under `create_functional_dependency` (cpp 10083-10089)
   of the at-most concept, the target's link and the successor's link, and
   the counted parent's links are relocated as at every at-most merge
   (`ht_relocate_incoming_links`). An unmergeable successor raises the
   functional clash with the clashed concept descriptor and both
   merge-causing descriptors, as cpp 14858-14863. The arm is skipped when
   every successor is a nominal: the NN-rule creates nothing there, and the
   at-most merge below enforces the bound as before.
2. *General arm* (every other `≤n R.C`, `n ≥ 1`, at a nominal `x`): when a
   qualified candidate is blockable and the creator of its link, blockable
   qualified candidates are moved into fresh nominals by
   `get_into_empty_merged_individual_node(candidate, true, x, …)` (the port
   of cpp 21047-21063, which also had no caller) under a `FUNCTIONAL`
   dependency of the at-most concept, the link that requires the rule and
   the candidate's link; the new node inherits the candidate's creation
   dependency (merge phase 7, cpp 21440-21442, which the port's merge does
   not perform), the parent's links are relocated and the new node is
   queued. At most `n − k` candidates are moved, where `k` is the number of
   qualified nominal neighbours: Konclude gives the rule `cardinality`
   new-representative slots (`setRemainingNominalCreationCount`,
   cpp 15231-15233) and spends one per new representative (cpp 15446-15458);
   every further candidate is merged into a representative. The probe root
   is never moved: Konclude never merges its constructed node away
   (`mOptMergeConstructedIndividualNode` off, cpp 21003-21006), and the
   bridge's probes do not register their root as the constructed node, so
   the port skips the blockable node without an ancestor link. The loop then
   counts and merges as before: if more than `n` qualified neighbours
   remain, the at-most merge branches over every mergeable pair, and a pair
   of a blockable node and a nominal (or of two nominals of different
   nominal levels) now merges in `getMergedIndividualNodes`' direction, into
   the nominal (the shallower one), instead of the order of the successor
   scan (`ht_orient_nominal_merge_pair`). The first version of this arm
   moved every blockable candidate and kept the scan order; on family seeds
   (`nn606`, reduction `hang606`, five axioms) the new nominals' re-derived
   successors reached the nominal again, became new nominals, and were
   merged into older ones without end: the completion did not terminate,
   where the base answers in 0.02 s.
3. *The reused consistency model* (`u36.rs`,
   `native_cardinality_critical_roles`, section 18.1). With the
   precomputation replay on, an ABox nominal of a class job starts from its
   representative-cache association with Konclude's backend blocks set, and
   its cached at-most concepts are not re-run: the cached view stands in for
   them until the cardinality test finds more `R`-neighbours than the cached
   bound (Konclude's `testIndividualNodeBackendCacheExpansionBlockingCriticalCardinality`,
   cpp 23318-23395). The NN-rule needs the at-most rule at the nominal below
   the bound as soon as a blockable neighbour that the nominal did not create
   appears, so the test now also reports a cached at-most role `R` (bound at
   least 1) for which the nominal has a live `R`-link to such a neighbour
   (`ht_nn_rule_candidate_link`). Found by the family seed `nn1018`
   (reduction `nn1018min`, three axioms: `Q1 ≡ ≥3 p⁻.(F ⊓ ∃r.{c})`,
   `⊤ ⊑ ≤1 r⁻`, `r(b,b)`; `Q1` is unsatisfiable because `c` has at most one
   `r`-predecessor, and the ABox assertion only switches the replay on;
   the base and the first version of this branch reported `Q1` satisfiable on
   both routes, and `KM_BRIDGE_NO_PRECOMPUTATION_REPLAY=1` gave the right
   answer). Konclude's own test has no such condition; Konclude 0.7.0 does not
   finish on `nn1018min` within 30 s, so its behaviour there is unknown. The
   added condition only releases blocks, which section 18.1 shows exact (the
   released node expands its cached neighbours or replays its raw
   assertions, the route without the cache).

The functional arm is a transcription of cpp 14756-14864 with one
restriction (a blockable successor must exist). The general arm departs
from Konclude in one point: Konclude decides per candidate between merging
into each mergeable representative and a new representative (a branch,
cpp 15465-15540), while the port moves candidates into the free slots in
the scan order and leaves every identification to the pair branching that
follows, which includes Konclude's alternatives.
The port's live at-most path is the pairwise merge of section 8 (the
`mergeMergingIndividualNodesPairwise` shape), not Konclude's distinct-set
state machine, which exists only in the opt-in `KM_HT_ATMOST_REST` path; that
path keeps the NN halves W3-DEFER.

**Exactness.**

- *A conversion is a renaming.* `get_into_empty_merged_individual_node`
  creates an empty node `N` and merges the candidate `y` into it: `N` gets
  `y`'s label (phase 4, each concept under a MERGEDCONCEPT dependency on the
  conversion), its links (phase 5, from `y`'s ancestor and its nominal
  connections, and the explicit relocation from `x`), and its distinctness
  edges (phase 8); `y` is marked merged and its successors are pruned and
  re-derived from `N`'s label, as at every merge into a nominal. In model
  terms `N` and `y` denote one element, so every model of the graph before
  the conversion is a model after it and conversely; only the node type
  changes. The functional arm's fresh target is an empty node linked to `x`
  by `R` and its super roles: an element that exists in every model of the
  graph in which `x` has an `R`-neighbour, which `requiresNNRule` guarantees,
  and the merges then identify it with that neighbour.
- *No verdict becomes unsound.* Neither arm adds a concept or a constraint
  that does not hold in every model of the current branch: the functional
  merges are the `≤1 R` rule itself (every `R`-neighbour of `x` is one
  element), and the conversions are renamings. A clash found after them is a
  clash of the input under the branch's choices. The dependencies of the new
  edges and labels include the at-most concept and the links (FUNCTIONAL and
  MERGEDCONCEPT/MERGEDLINK dependencies), a superset of the facts each
  derivation rests on, so the DDB analysis never jumps over a decision that a
  clash depends on.
- *Satisfiable verdicts become sound for the bound.* A node of type NOMINAL
  is never a blocking candidate and never blocked
  (`get_blocking_individual_node_candidate_iterator`,
  `detect_individual_node_blocked_status` and the anywhere-blocking scans
  test `is_blockable_individual`). After the rule, every `R.C`-neighbour of a
  nominal `x` under `≤n R.C` that reached `x` from outside its own subtree is
  a nominal node, so no blocked node is unravelled into an extra neighbour of
  `x`; the bound counts the nodes that stand for the neighbours in the model.
  This is the premise of the soundness of blocking in the SROIQ tableau, and
  the case the base violated on `f1008` and `f439`.
- *Completeness of the merge search.* After the general arm the at-most loop
  branches over every mergeable pair of qualified neighbours while more than
  `n` remain, a superset of Konclude's alternatives (merge into a
  representative, or a new representative while slots remain). When `n` or
  fewer remain no merge is needed: separate nodes that are not distinct may
  denote the same element, and the completeness argument of the tableau maps
  nodes to model elements without requiring injectivity on nodes that carry no
  distinctness edge.
- *Termination.* Converted nodes are nominals and are never converted again.
  The general arm creates a new nominal only while fewer than `n` qualified
  neighbours of `x` are nominals, and a pair of a blockable neighbour and a
  nominal merges into the nominal, so once `n` nominal neighbours exist every
  further blockable neighbour is merged into one of them, as in the SROIQ
  tableau after the NN-rule has fixed its `m` nominals. Every node the rule
  creates is at nominal level `level(x)+1`, as in Konclude. This is an
  argument by analogy with the SROIQ termination proof, not a proof for the
  port; it is checked empirically below (timeouts against the base on the
  family and the pools), and the family still has seeds on which the branch
  answers more slowly than the base (listed in the results README).

**Interaction with the bridge's other machinery.**

- *Blocking.* New nominals are never blocked and never block (above). A node
  that was blocked by the converted candidate `y` loses its blocker: `y` is
  merged away, and the valid-blocker test (`is_individual_node_valid_blocker`,
  `u18.rs`) rejects nominal nodes and nodes with the invalidating flags; the
  node is re-tested and expands. On `f1008` the second `s`-successor expands,
  reaches `c`, and its merge into the new nominal clashes with the `≥2`
  distinctness.
- *Merging and backtracking.* The rule uses the merge functions every other
  rule uses; every merge lies in the branch epoch of the at-most application
  that triggered it, so backtracking removes the new nodes and restores the
  candidates. The new nodes are allocated above the epoch's node-arena mark,
  so section 18.2's release of dependencies of popped nodes covers them.
- *Caches.* The NN-rule fires only at nominal nodes, which none of the
  satisfiability, signature or saturation caches represent. The representative
  cache writer (`write_completed_native_representative_associations`) treats a
  new nominal like any other neighbour without an ABox individual
  (`native_completion_nominal_tag` returns none): its links enter the
  association as instantiated and existential roles of the individual, as the
  links to blockable successors did before. The retained consistency base and
  the consistency leaf (section 16) can contain new nominals created during the
  consistency completion; class jobs see them as ordinary nominal nodes of the
  base, and jobs that create new ones roll them back with their epochs.
- *Saturation.* The approximation saturation has no NN-rule in Konclude
  either. Its critical at-most test marks the ancestors of a node with an
  integrated nominal insufficient
  (`mark_nominal_atmost_restricted_ancestors_as_insufficient`, `s09.rs`), so
  such nodes go to the completion, where the rule now runs. The automatic
  route, on which the saturation runs first, is part of every measurement
  below.

**Results** (`results/agents/2026-11-04/bridge-nn-rule/README.md`).
`f1008`, `f439`, the seeds `refl1008` and `refl439`, and the family
reductions `nn1018`, `nn1018min` and `hang606` agree with HermiT on
`ht_bridge` and the automatic route in 20 of 20 runs (base: the first four
and `nn1018` wrong on both routes). A sibling family of 2,000 generated
seeds (`tools/gen_nn.py`, HermiT gold for 1,993) has 499 wrong seed-routes
on the base and 11 wrong seed-routes over 6 seeds on this branch, each wrong
on the base too: three satisfiable-expander-cache misses next to nominals
(`nn1064`, `nn1313`, `nn1348`; right with `KM_HT_NO_SAT_EXP_CACHE=1`), one
unreduced seed (`nn1116`), one seed on which HermiT is wrong (`nn5`, model in
the README), and one wrong answer of the nominal CB stack after the HT worker
exceeded its memory cap (`nn1811`). Seven family seeds that the base answers
time out on this branch (the general arm's merge search; README). The
gold-backed pools of earlier agents (17,797 seeds, both routes), the 16
held-out ORE inputs and the 112 nominal ORE design-half inputs keep their
answers; times are unchanged within noise (nominal mean ratio 0.956, maximum
1.03).

What it rests on: as for sections 10 to 21, the bridge has no Lean model and
no certificate covers a bridge answer; the arguments assume that the port's
merge, blocking and dependency machinery are Konclude's, and are checked
differentially against HermiT only. Lean obligation created: none
discharged; a bridge model would have to show that turning a blockable
neighbour of a nominal into a nominal preserves the models of the
completion graph and restores the premise of the blocking soundness proof.

## 23. The satisfiable expander cache: absorption on cached nodes and the replay of written entries (2026-11-04, `fix/v155-bridge-satcache`)

**Defect.** The NN-rule family of section 22 left three seeds that KM answered
wrongly on both routes in every run, on the base and on rc1 (`nn1064`,
`nn1313`, `nn1348`, reduced to `nn1064min`, `nn1313min`, `nn1348min`), and one
unreduced seed (`nn1116`). The three answer as HermiT with
`KM_HT_NO_SAT_EXP_CACHE=1`, `KM_BRIDGE_FRESH_ENV=1` or `KM_HT_NO_SATURATION=1`.
Section 20 met the same cache on ore_ont_12128 and installed it no more on
terminologies with a positive SELF concept, without isolating the wrong
entry. This section isolates the entries for both, and the sibling family
built around the three reductions adds a fourth (`sat1096`). In every case
the entry is correct and the port uses it differently from Konclude; none
of the defects is tied to nominals or to self edges. `nn1116` turns out not
to be a cache defect.

**Gold, by hand.**

- `nn1064min`: `Q1 ≡ {b} ⊓ ≥2 p.B`, `Q3 ≡ ≤1 r⁻.(∃r.{a})`,
  `InverseObjectProperties(r, p)`, `InverseFunctional(p)`, `b ≠ a`. Let
  `x ∈ Q1`, so `x = b`. A `p`-successor `y` of `b` (an `r⁻`-successor) in
  `∃r.{a}` has `r(y,a)`, so `p(a,y)`: `y` has the `p`-predecessors `a` and
  `b`, and inverse functionality gives `a = b`, against `b ≠ a`. So `b` has no
  such successor and `b ∈ Q3`: `Q1 ⊑ Q3`. In the model with domain
  `{a, b, y1, y2, z1, z2}`, `p = {(a,y1), (a,y2), (b,z1), (b,z2)}`, `B = {z1, z2}`,
  `a` has two `p`-successors in `∃r.{a}` and so `a ∉ Q3`; putting `a` into
  any other class refutes `X ⊑ Q3` for `X ≠ Q1`, and `Q1 = {b}` is refuted
  under every other class by leaving `b` out. HermiT's single subsumption.
- `nn1313min`: `≤1 p⁻.(∃s⁻.({a} ⊓ ¬A)) ⊑ E`, `InverseObjectProperties(p, s)`,
  `InverseFunctional(s)`, and a definition of `Q2` that does not touch `E` or
  `A`. `p⁻ = s` and `s⁻ = p`, so the left side is
  `≤1 s.(∃p.({a} ⊓ ¬A))`. Let `x ∈ A` and `y` an `s`-successor of `x` with a
  `p`-successor `a ∉ A`, that is `s(a,y)`: `y` has the `s`-predecessors `x`
  and `a`, so `x = a` by inverse functionality, against `x ∈ A`, `a ∉ A`. `x`
  has no such successor, so `x ∈ E`: `A ⊑ E`. With `a ∉ A` given two
  `s`-successors `y1, y2` (each with the single `s`-predecessor `a`), `a`
  violates the left side, so `a ∉ E` is allowed, and putting `a` into any
  class other than `A` refutes `X ⊑ E`; the other classes are free. HermiT's
  single subsumption.
- `nn1348min`: `⊤ ⊑ ≤1 r`, `Q5 ≡ ≤0 r`, `Q4 ≡ ≤1 r⁻.(∃r.∃r.{b})`,
  `F ⊑ ≤1 s⁻.(E ⊓ ∃r⁻.{c})`. Let `x ∈ Q5` and `y` an `r`-predecessor of `x`
  in `∃r.∃r.{b}`. `r` is functional, so the `r`-successor of `y` that
  satisfies `∃r.{b}` is `x`, and `x` has an `r`-successor, against `≤0 r`. So
  `x` has none and `x ∈ Q4`: `Q5 ⊑ Q4`. In the model with domain
  `{v1, v2, w, b, c}`, `r = {(v1,w), (v2,w), (w,b)}` and `s` empty, `r` is
  functional, `Q5 = {b, c}`, and `w` has the two `r`-predecessors `v1, v2` in
  `∃r.∃r.{b}`, so `w ∉ Q4` and `w ∉ Q5`: putting `w` into a class `X`
  refutes `X ⊑ Q4` and `X ⊑ Q5`; leaving `b` out of `X` refutes `Q5 ⊑ X`,
  and leaving `v1 ∈ Q4` out of `X` refutes `Q4 ⊑ X`. The remaining classes
  are free. HermiT's single subsumption.
- `nn1116`: `⊤ ⊑ ≤1 s⁻`, `Q3 ≡ ≤2 s.(∃s.{c})`. An `s`-successor of `x` in
  `∃s.{c}` is an `s`-predecessor of `c`, and `c` has at most one: every
  element has at most one such successor, so `⊤ ⊑ Q3`. HermiT lists the nine
  `X ⊑ Q3` and nothing else. (Not a cache defect, see below.)
- `sat1096min` (six axioms, reduced from the sibling family seed `sat1096`
  with `tools/ddmin_cache.py`): `Q5 ≡ {a} ⊓ ∃p.(∃r.{b})`,
  `Q5 ≡ ≤1 r.(∃s.{a})`, `Q4 ≡ {b} ⊓ ∃p⁻.{a}`, `r ≡ s⁻`,
  `Q2 ≡ ≤2 p.(∃r⁻.∃p.{a})`, `Q2 ≡ ≤2 r⁻.(∃p⁻.{a})`. Let `P` be the
  `s`-predecessors of `a`. `Q5 ⊆ {a}`, so every `x ≠ a` lies outside
  `≤1 s⁻.(∃s.{a})`: it has two `s`-predecessors in `P`, so `|P| ≥ 2` and
  `a ∉ Q5` as soon as a second element exists. A non-empty `Q5` forces the
  one-element model, where `a = b` and `p(a,a)` (from `∃p`), so `a ∈ Q4`
  and `a ∈ Q2`: `Q5 ⊑ Q4`, `Q5 ⊑ Q2`. For `Q4 ⊑ Q2`: if `b` has an
  `s`-successor `z` with `p(a,z)`, then `a ∈ ∃p.∃r.{b}` (`r(z,b)`), so
  `a ∈ Q5` and the model has one element; otherwise `b` has no such
  successor; either way `b ∈ ≤2 r⁻.(∃p⁻.{a}) = Q2`. HermiT gives exactly
  these three subsumptions.

**The wrong entries.** `KM_HT_SATEXP_TRACE=1` (new, diagnostic) prints every
satisfiable-cache write, every satisfiable hit with the node and its
ancestor, every replayed concept, every expansion write, and every rule
taken from a node's queue; `KM_SAT_ABSORB_DEBUG=1` prints the generating
absorption test. On `nn1348min` (concept tags from `KM_BRIDGE_CONCEPT_DUMP`:
41 is `≤1 r.⊤`, 44 is `∃r.∃r.{b}`, 43 is `∃r.{b}`, 42 is `≤0 r`):

1. The probe of `E` creates the `r⁻`-successors `y1, y2` of the root, each
   with the label `{⊤, 41, 44}`. `44` creates an `r`-successor that `41`
   merges into the root, which receives `43`. The probe is satisfiable, and
   the end-of-task writer records `{⊤, 41, 44}` as satisfiable, with no
   branched concept (`SATEXP-WRITE-SAT sig=420296238655154 branched=false`).
   The entry is correct: a node with that label is satisfiable.
2. The probe of `Q5 ⊓ ¬Q4` creates `y1, y2` again, below a root that carries
   `≤0 r`. Both hit the entry (`SATEXP-HIT compatible=true
   without_branched=true`) and are marked `PRF_SATISFIABLECACHED`. The node
   still runs its own rules, as in Konclude
   (`isSatisfiableCachedProcessingBlocked` blocks only the successors of a
   cached node). Its queue pops `44` first, and the port's generating-concept
   absorption accepts it (`SAT-ABSORB-CHECK concept-tag=44 cached=true
   absorbable=true`); `41` is then absorbed as a merging concept. No
   successor is created, nothing reaches the root, and the probe is
   satisfiable: `Q5 ⋢ Q4`.

So the entry is right and its use is wrong. Konclude's
`isGeneratingConceptSatisfiableCachedAbsorpable` (cpp 14217-14253) refuses
to absorb `∃R.C` when the node is linked to its ancestor by a super role of
`R` that is functional or carries an at-most restriction in the node's role
reapply queue: the successor would have to be merged into the ancestor, and
the cache entry, which knows nothing of the ancestor, cannot stand for that
merge. The port's transcription of the test is faithful. It accepts here
because of three differences around it:

- *The functional rule is never absorbed.* `applyATMOSTRule` sends an
  unqualified `≤1 R` to `applyFUNCTIONALRule` (cpp 14933-14935) before its
  own absorption test (cpp 14938-14941); the functional rule merges the
  node's `R`-neighbours and registers the concept in the role reapply queue
  (cpp 14868-14871). The port's `apply_atmost_rule` handled `≤1 R` through
  the general at-most path, after the absorption test, so on a cached node
  the functional at-most was absorbed and never registered.
- *`≤1 R.⊤` keeps its operand in the bridge.* `CConcreteOntologyUpdateBuilder.cpp`
  1197-1199 drops a `⊤` filler from a cardinality restriction, so Konclude
  has no `≤1 R.⊤`. The bridge builds `SubClassOf(owl:Thing
  ObjectMaxCardinality(1 :r))` as `≤1 r.⊤` with a `⊤` operand (tag 41,
  `ops=[1]`). That concept is not the functional rule, and its priority is
  3.5, below `∃` (4), where Konclude's unqualified `≤1` has 5.5: the
  existential is popped, and tested against an empty reapply queue, before
  the at-most is registered. Konclude never meets that order.
- *`∃R.{a}` never reaches the absorption.* `applySOMERule` answers an
  existential with one positive nominal operand by the VALUE shortcut (cpp
  14316-14380): it links the node to the nominal and returns before the
  absorption test at cpp 14388. The port has no VALUE shortcut (W3-DEFER); it
  creates a successor that merges into the nominal, after the absorption
  test, so on a cached node `∃p⁻.{a}` was absorbed (`nn1064min`, tag 34 on
  every cached successor of `b`).

`nn1064min` (absorbed `∃r.{a}` and `≤1 p⁻` on the cached `p`-successors of
`b`) and `nn1313min` (absorbed `≤1 s⁻` and `∃s⁻.({a} ⊓ ¬A)` on the cached
`s`-successors) are the same use of a correct entry. Nominals matter only
because the seeds' existentials reach them; the absorption needs no nominal.

**`sat1096`: the successor of a non-absorbed `∃R.{a}`.** Once `∃s.{a}` is no
longer absorbed on a cached node (the third point above), the port creates
its successor, and that successor inherits `PRF_ANCESTORSATISFIABLECACHED`
from the cached creator (`createSuccessorIndividual`, cpp 21692-21720, which
the port follows), so it is never processed: its nominal concept `{a}`
never merges it into `a`. On `sat1096min` the probe of `Q5 ⊓ ¬Q4` builds the
`r`-successors `z1, z2` of the nominal `b` with `∃s.{a}`; they hit a
satisfiable entry, their `s`-successors carry `{a}` with flags `0x200200`
(ancestor-satisfiable-cached), `a` never sees `z1, z2` as `s`-predecessors,
and its `≤1 r.(∃s.{a})` never merges them (they are distinct by `≥2`), so
the clash is missed. Konclude creates no such successor: the VALUE shortcut
links `z1` to `a` directly and propagates the nominal connection, after
which `z1` is no longer satisfiable-cached (`detectIndividualNodeSatisfiableExpandedCached`
requires no `PRFSUCCESSORNOMINALCONNECTION`). The family seed `sat1096` is
wrong on the base on both routes and right with `KM_HT_NO_SAT_EXP_CACHE=1`.

**The ore_ont_12128 reduction (section 20) is a separate defect, in the
replay.** With the section 20 gate removed (`KM_BRIDGE_SELF_SATEXP=1`, new,
diagnostic) or under the old completion-only schedule
(`KM_BRIDGE_SAT_REFUSE_SELF=1`), the changes above do not repair `m53tiny`.
Its trace (tags: 34 `GO_0005518`, 38 `Continuant`, 44 `GO_0003674`, 45
`Function`; `44` is a `CCSUB` with the operand `45`; `Continuant ⊑ ¬Function`):

1. In the probe of `Amadori_species`, node 1013 (the `has_part`-successor
   `GO_0005518 ⊓ Continuant` of `world_of_Model53`) processes `47` and `46`
   (the told chain `GO_0005515 ⊑ GO_0005488 ⊑ GO_0003674`); before `44` is
   taken from the queue, the node is popped for its blocking test, and
   `cacheIndividualNodeExpansion` writes the entry
   `{⊤, 34, 38, SELF, ≤1 quality_of, 53, ¬45, ¬48, ¬49, 47, 46, 44}`
   (`SATEXP-WRITE-EXP … values=[1,34,38,72,73,53,-45,-48,-49,47,46,44]`).
   Every value is a correct deterministic consequence of the prefix, but `44`
   is not yet applied. Then `44` adds `45`, the node clashes, and the probe
   goes on.
2. In the next probe the same node with the prefix `{⊤, 34, 38}` reads the
   entry, and `expandCachedConcepts` replays the suffix with
   `addConceptToIndividualSkipANDProcessing`, which queues every concept
   except those whose rule is `applyANDRule` (AND, SUB, EQ, TOP, IMPLTRIG,
   BRANCHTRIG; cpp 26814-26844, 27350-27364). `44` is a SUB, so it is added
   and never processed: `45` never arrives, the clash with `¬Function` is
   missed, and `world_of_Model53` is reported satisfiable.

Konclude skips the AND rule on replay because its entries cannot contain an
unapplied AND-family concept: with `DirectRulePreprocessing` (on in every
Konclude completion task, `CCalculationConfigurationExtension`) a concept of
priority 13 is applied as soon as it is added
(`addConceptPreprocessedToProcessingQueue`, cpp 27388-27390), so its
operands are in the label before any later write. The bridge runs most
terminologies without direct rule preprocessing (`bridge.rs`,
`conf_direct_rule_preprocessing = card_nominal_profile`, a scheduling choice
earlier agents validated), so the writer can record an AND-family concept
that is still queued, and the replay drops its operands. The reflexive
`part_of` and the functional `quality_of` of the reduction add a SELF and an
at-most concept to every label through `⊤`; they only change the queue order
so that the blocking test falls between `46` and `44`. That is why section
20 met the defect next to self edges.

**`nn1116` is not a cache defect.** It is wrong on the base and on this
branch with `KM_HT_NO_SAT_EXP_CACHE=1`, `KM_HT_NO_SATURATION=1` and
`KM_HT_NO_NN_RULE=1` alike. Its bound `⊤ ⊑ ≤1 s⁻` is again a `≤1 s⁻.⊤`
with a `⊤` operand, so at the nominal `c` the NN-rule's general (qualified)
arm runs instead of its functional arm (section 22). Building `≤n R.⊤`
without the operand, as Konclude does, answers `nn1116` as HermiT, but it
also sends every such bound through the functional arm, and on five family
seeds (`sat346`, `sat181`, `sat1094`, `sat1496`, `sat1836`, base 0.5 to 12 s)
the completion then did not finish within 20 to 30 s (with
`KM_HT_NO_NN_RULE=1` `sat1094` answers in 0.4 s). That is the NN-rule
termination work of `fix/v155-bridge-nn-term`; this branch keeps the
bridge's representation and hands `nn1116` on.

**Change.** All decisions are in `completion/satexp_absorb.rs` (new), used
at four call sites:

1. `atmost_is_functional_rule` (in `u08.rs` `apply_atmost_rule`): a `≤1 R`
   without a qualifier, or with the qualifier `⊤`, is never absorbed on a
   satisfiable-cached or completion-graph-cached node; it runs the at-most
   merge, which registers it in the role reapply queue as the functional rule
   does.
2. `label_restricts_role_cardinality` (in `u22.rs`
   `is_generating_concept_satisfiable_cached_absorpable`): besides the
   reapply queue, the test reads the node's label for an at-most (or negated
   at-least) restriction on the super role that links the node to its
   ancestor, so the refusal no longer depends on the queue order.
3. `some_is_value_shortcut` (in `u08.rs` `apply_some_rule`): an `∃` (or
   `≥1`) whose single operand is a positive `CCNOMINAL` is never absorbed,
   and its successor does not inherit the cached-ancestor blocks
   (`VALUE_SHORTCUT_CLEARED_ANCESTOR_FLAGS`: ancestor satisfiable-cached,
   signature-blocking-cached, saturation-blocking-cached), so it is processed
   and merged into the nominal. The saturation-integrated-nominal arm of
   Konclude's shortcut is not reproduced; it keeps the absorption test.
4. `expanded_concept_skip_function` (in `u21.rs` `expand_cached_concepts`,
   through the new `u04.rs` `add_concept_to_individual_with_skip_function`):
   replayed concepts are queued without the AND skip.
5. `bridge.rs`: the satisfiable expander cache no longer takes the section
   20 gate. The associated-expansion cache and the saturated-label expansion
   keep it: this section does not analyse them.

`KM_HT_SATEXP_ABSORB_LEGACY` restores the former behaviour, all arms (`1`)
or a comma list of `functional`, `top`, `label`, `value`, `replay`;
`KM_BRIDGE_SELF_SATEXP_GATE=1` restores the gate. Production sets neither.
Each reduction fails again with all arms restored, and with single arms as
follows (ht_bridge): `functional,top` loses `nn1313min` and `nn1348min`,
`label` loses `nn1348min`, `value` loses `sat1096min`; `nn1064min` needs
both `functional` and `value` restored to fail; `replay` loses `m53tiny`
and the 12128 reduction under the completion-only schedule.

**Exactness.** None of the changes adds a concept, a merge or a clash that
the completion could not derive without the caches; each removes a deferral
or adds a rule application.

- *1, 2 and 3 only refuse deferrals.* An absorbed concept, and a successor
  blocked under a cached ancestor, are promises that the cache entry stands
  for what the concept or the successor would build. For `≤1 R` (with or
  without the `⊤` qualifier, which has the same models) and for an
  existential whose successor must merge into the ancestor, that promise
  fails whenever the ancestor is an `R`-neighbour outside the cached
  subtree; for `∃R.{a}` the successor is the nominal itself. Konclude never
  makes these promises (points 1 and 3) or makes them only in a queue order
  that the port's `⊤`-qualified bounds do not reproduce (point 2). Refusing
  one runs the ordinary rule on that node, as the completion does on every
  node that is not cached, so a verdict reached with the refusal is a
  verdict of the plain tableau on the same branch. The cost is the rule
  application.
- *4 only adds rule applications.* The AND rule adds the operands of a
  concept that is in the label; they are consequences of it, and when they
  are present already the insertion is a no-op. The replayed concepts are
  those of an expansion entry, whose correctness (each value a deterministic
  consequence of the entry's prefix, by the dependency tracking of
  `cacheIndividualNodeExpansion`) is unchanged.
- *5 removes a gate whose two witnesses are explained.* The gate's
  witnesses were `m53tiny` (defect 4) and the seeds `v1s160`, `v1s1420`,
  `v1s1543` (`∃p.Self ⊓ ≤1 p⁻`, defect 1: the cached node absorbed its
  `≤1 p⁻`). With the cache installed on SELF terminologies the 14 SELF
  fixtures (`tests/fixtures/bridge_self` and `m53tiny`) agree with HermiT on
  both routes; with the gate off and the absorption arms restored the three
  seeds fail again, and with the replay arm restored `m53tiny` and the 12128
  reduction fail again under the completion-only schedule. What the gate
  guarded against was not a property of self edges, so no new precondition
  replaces it; the SELF pools below are the evidence beyond the fixtures.

What the cache still rests on, as in Konclude: an entry's values are
deterministic consequences of its prefix (dependency tracking; nominal nodes
neither read nor write it, section 10, `KM-SOUNDNESS-GATE[nominal-satexp]`),
a satisfiable entry holds for any node with that label whose ancestor is
compatible (`isSatisfiableCachedCompatible`), and only the deferrals that
Konclude makes are made. None of these is machine-checked; the bridge has
no Lean model, and the arguments above are checked differentially against
HermiT only.

RESULTS23-PLACEHOLDER
