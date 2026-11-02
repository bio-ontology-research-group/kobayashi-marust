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
