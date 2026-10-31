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
