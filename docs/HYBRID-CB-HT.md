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

## 5. Routing options under evaluation

Per the directive to sweep every option and decide later, the full-corpus IBEX
sweeps compare, against the current production baseline (564 ok):

- **Option 1 — safe coverage hybrid** (section 4). HT answer used only on CB
  failure. Expected: +coverage (the HT_ONLY set), 0 regression. `KM_HT_FALLBACK`.
- **Option 2 — speed race**: routable onts take the first finisher of CB ∥ HT.
  Captures the 45 speed wins + coverage, but regresses the HT-incomplete onts
  whenever HT wins the race with an incomplete answer. The sweep measures exactly
  how many. `KM_HT_RACE`.

Option 1 is the expected default; Option 2 quantifies the speed-vs-correctness
trade. Both are gated; the winner becomes the new main pipeline default.

## 6. Artifacts

- `engine/py/ht_check.py` — canon-faithful HT correctness runner (the section-2
  measurement).
- IBEX `km-htport` (`$HP=/ibex/scratch/hohndor/km-htport`): `tableau_cli` with
  `KM_HT`, `cb_to_ht.py`, `ht_ofn_runone.py` (sweep runner), `sweep_ofn/`
  (job 47566667), `htcheck/` (job 47570686), `h2h_joined.jsonl` (the join).
- Head-to-head join: `h2h_analyze.py` over `cmp2_res` (CB) + `sweep_ofn` (HT).
