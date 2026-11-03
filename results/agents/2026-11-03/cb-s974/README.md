# cb-s974: two wrong SELF-family answers (s974, s1966)

Branch `fix/v155-cb-s974` from `development/v1.5.5` at 117f143d, worktree
`.work/worktrees/fix-cb-s974`. Scratch: `.work/agent-scratch/cb-s974/`.
Release flags for every measurement: `KM_HT_DDB=1 KM_HT_NATIVE_FULL=1
KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1
KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`. Base binary: the merged 117f143d
binary `.work/v155-heldout-gap/selfmerge/km-117f143d`.

## s974: Q2 unsatisfiable, KM said satisfiable (CB engine)

### The gold holds

HermiT says `Q2` is unsatisfiable. Konclude (`~/konclude-build/Release/Konclude`,
the reference build) did not finish on s974 or s1966 within 60 s (it stays in
"Precomputing ontology ... expressiveness SIQ"; logs in `data/s974/`), and no
Openllet or JFact installation exists on ws (the reference audit ran them on
Ibex). The gold follows by hand from three axioms:

    Q2 ≡ E ⊓ ≥ 2 r.Self(p)      ReflexiveObjectProperty(r)
    InverseFunctionalObjectProperty(r)

Let `x ∈ Q2` with distinct r-successors `y1`, `y2`. Reflexivity gives
`r(y1,y1)`; inverse functionality on `r(x,y1)` and `r(y1,y1)` gives `x = y1`,
and likewise `x = y2`, so `y1 = y2`, a contradiction. HermiT also agrees on
the 3-axiom reduction `data/s974/m1.ofn` (`Q2 ⊑ ≥ 2 r`, `r` reflexive and
inverse functional: `Q2` unsatisfiable); the base binary answers it wrong too.

### Cause

The CB engine (route `production_all`, the in-process engine alone) derives
in the successor context `T → x ≈ y` (the successor equals its
predecessor) but never sends it to the predecessor: `pred_pool_eligible`
(`engine/src/engine.rs`) admitted predicates and the nominal forms
`x ≈ o`, `y ≈ o`, `o ≈ o'`, and kept `x ≈ y` local. arXiv:1805.01396,
Definition 2, puts `x ≈ y` in the predecessor triggers `Pr`, so the Pred
rule must deliver it, as `f(x) ≈ x`. Without it the predecessor learns the
consequences of the merge that the successor rewrote onto `y` (so
`Q2 ⊑ F` was found in a variant), but never that two successors `f1(x)` and
`f2(x)` both equal `x`, so the clause `Q_0(x) ∧ f1(x) ≈ f2(x) → ⊥` never
fires. Context dumps before and after: `data/s974/m1.{base,fixed}.dump.txt`
(after the fix context 0 holds `T → f(x) ≈ x` and `T → ⊥`).

### Fix and exactness

`pred_pool_eligible` admits `Eq{x, y}` (commit 4e5d6a46). The Lean
specification of the ordinary Pred send scan
(`lean/ContextCalculus/CBPredSendEnumeration.lean`,
`predHeadLiteralEligible`) admits the same literal, with kernel-evaluated
examples for `x ≈ y` (eligible), `y ≈ x` and `f(x) ≈ x` (not eligible).

- Soundness: if every element `e` described by the successor context with
  predecessor `d` satisfies `e = d`, then for the predecessor's element `d`
  and its successor `f(d)` along the edge, `f(d) = d`. This is the Pred rule
  of the paper instantiated with `L = x ≈ y ∈ Pr`.
- Completeness: the change restores the paper's `Pr`; KM's previous set was
  a strict subset, and the s974 family shows the gap.
- Order and termination: Definition 3, condition 6 constrains only atoms
  `A ≈ true ∈ Pr`; `x ≈ y` is not such an atom, so no ordering condition
  changes. `f(x) ≈ x` is already a context literal, so the set of derivable
  clauses stays finite.
- Lean build (`PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=4 nice taskset
  -c 17-24`): `lake build ContextCalculus` (8,659 jobs) and `lake build
  Validation` plus all 50 `cb-*` checkers and
  `ContextCalculus.CBCertificationSurface` (7,016 jobs) succeed; no
  `sorryAx` in either log; `mem_enumerate_iff` still depends only on
  `propext` and `Quot.sound`.
- Certified runs: `pred_triggers` in the CB certificate wire are the
  predicate triggers of the order (condition 6), not the Pred pool, so they
  stay predicates and `CBSourceHyperClosure`'s `pred_triggers_predicates`
  is unaffected. With `KM_LEAN_CHECKERS=<lean bin> KM_LEAN_CHECKERS_SET=all`
  the probes that derive `x ≈ y` (`data/probes/c1.ofn`, `c4.ofn`, s974,
  s1966, m1) publish with `cannot_check` events only (typed source
  declined, or "CB event has no chronological proof"); no checker rejected
  and none accepted, so the new literal never passes a checker unexamined.

## s1966: C ⊑ Q3 missing in about half of the runs (certified elc race)

### The gold holds

`ReflexiveObjectProperty(:r)` and `Q3 ≡ ∃r.Self` put every element in
`Q3`, so every class is under `Q3`, `C` included. HermiT agrees.

### Cause

`KM_TIMING` traces of a good and a bad run differ only in the engine block
(`data/s1966/timing.{good,bad}.err`: 9 subject rows after 0.11 s against 12
after 0.01 s). With `KM_THREADS=1` the CB stack is
`race::race_adaptive_vs_elc`: the full CB engine races the certified elc
worker (`KM_ELC_CERT=2`). On the absorbed clauses the certificate is partial
(exit 4): it publishes the subjects it could decide and hands the rest to a
query-restricted residue engine, whose answer is merged with the partial one.
Whichever of the full engine and the residue engine finishes first wins, which
is the run-to-run difference.

The partial answer was wrong. `C` occurs in one clause, `t(x,y) → C(x)`
(from `ObjectPropertyDomain(:t :C)`), and `t` occurs in no clause head. The
certificate's bridge preprocessing (`prepare_inverse_bridges`, vacuous-role
elimination) deletes that clause, which preserves the entailments of the
clause set, but `C` then occurs nowhere: it has no completion node, it is not
a certificate subject, it is not in the unresolved list, and the merged
answer publishes `C` with no superclass. The frontend emits a declaration
clause `C(x) → C(x)` only for a declared class that no other clause names,
so nothing restored `C`. `KM_ELC_SEQUENTIAL=1` (elc first, then its
residue) makes the wrong answer deterministic (4 of 4 on the base). The same
loss shows on the forced `elc_cert` route without any race:
`data/probes/top.ofn` (`⊤ ⊑ A`, `C` only in the domain of an unused role)
loses `C ⊑ A` on the base.

### Fix and exactness

`prepare_inverse_bridges` records the concept names of its input and appends
`C(x) → C(x)` for every name its rewrites removed (`retain_concept_signature`,
commit 4e5d6a46). A tautology adds no constraint, so the model class and the
entailments of the rewritten set are unchanged; the name gets its node, the
completion seeds it with the closure of `⊤`, and the certificate decides it
like every other named subject (on s1966 `C` now lands in the residue and the
engine answers it: `data/s1966/elc-cert.{base,fixed}.json`). The rewrites run
only in the non-Lean certificate modes (a checker-backed run keeps the exact
input stream), so no Lean statement is involved. Argued in
`docs/INVERSE-BRIDGE-CANONICALISATION.md`, "The rewrites must keep the
concept signature".

### Publication coverage guard (supervisor addition)

`orchestrate::undeclared_coverage` (commit a62e9ced, refined in f60acd77):
a consistent row-form worker answer (CB engine, elc and its residue merges)
that has no subject row for some declared class is declined
(`coverage guard: the worker answer omits N declared class(es)`), never
published. The elc worker now emits an empty row for every public concept
node (string map and compact output); the CB engine already did. HT, bridge
and tableau answers arrive as pair lists or as HT compact output without
empty rows, so absence carries no information there; they are marked
`pair_form` and stay outside the guard (an open protocol change: those
workers would have to report the query classes they decided). Argued in
`docs/ROUTING.md`, "Publication coverage guard". Unit test
`orchestrate::tests::coverage_guard_declines_an_answer_without_a_declared_class`
removes a class from a worker answer and checks the decline (plus the empty
row, unresolved and compact cases).

## Commits (branch `fix/v155-cb-s974`, not pushed, not merged)

- 4e5d6a46 fix(cb,elc): send x≈y over Pred; keep concept names lost by elc bridge prep
- 531de407 docs: argue the x≈y Pred send and the elc signature retention
- a62e9ced orchestrate: publication coverage guard for row-form worker answers
- f60acd77 elc: empty rows only for concept nodes; adapt elc tests to the kept signature
- 52ee3320 results(cb-s974): tools, family data, bridge-miss reductions, README draft
- 16e638aa elc: keep empty rows for public subjects on every elc output path
- dbb259c8 docs(routing): list the elc output paths the coverage guard relies on
- (this README and the final data)

Binaries in `.work/agent-scratch/cb-s974/bin/`: `km-v4` (both fixes and the
guard; families), `km-v5` (= f60acd77; pools, held-out, nominal),
`km-v6` (= 16e638aa, final code; seeds, C1 sample, tests). v4 → v5 → v6
change only which empty subject rows the elc worker emits: no published pair
changes, and the guard can only fire less often (the v5 → v6 change was
forced by six guard declines in the C1 sample, see below). A 800-run spot
check of v5 on the families matched v4.

## Seeds, 20 runs each (final binary v6, release flags)

| seed | automatic route | failed route |
|---|---|---|
| s974 | 20/20 ok | `cb_plain1` 20/20 ok |
| s1966 | 20/20 ok | `KM_ELC_SEQUENTIAL=1` 20/20 ok |

(base 117f143d: s974 wrong 10/10, s1966 wrong 5/10 automatic and 4/4
sequential). The supervisor's independent check of the 09:18 build: 20/20 on
both seeds and on its own minimal variants.

## Sibling families (2,000 seeds each, HermiT gold, 3 runs per seed and route)

Generators `tools/gen_merge.py` (s974 shape: successors forced to merge
with their predecessor by reflexive, inverse-functional, functional,
symmetric and inverse roles, `≤ 1 R⁻`, Self, cardinalities) and
`tools/gen_vacuous.py` (s1966 shape: classes named only next to head-free
roles, a nontrivial superclass of `⊤`, non-EL residue). Gold by
`tools/gold_batch.sh` (HermiT 1.4 through `OracleBatch`); runner
`tools/fam_run.py` (60 s automatic, 15 s forced). Data `data/families/`.

| family, route | after (v4, 3 runs) | base (117f143d, 1 run) |
|---|---|---|
| merge, auto | 5,982 ok, 3 timeout, **15 wrong (5 seeds × 3)** | 1,957 ok, 42 wrong |
| merge, `cb_plain1` | 4,305 ok, 891 timeout, 804 refused, **0 wrong** | 1,305 ok, 93 wrong (5 s cap) |
| vacuous, auto | 5,985 ok, 15 timeout, **0 wrong** | 1,966 ok, 29 wrong |
| vacuous, `KM_ELC_SEQUENTIAL` | 5,979 ok, 21 timeout, **0 wrong** | 1,930 ok, 63 wrong |

No answer differed between the three runs of a seed (only ok/timeout on the
forced CB route). The `cb_plain1` refusals are forced-route exactness
refusals (ABox assertions or nominals the route would drop). The coverage
guard fired 0 times.

The 5 remaining misses (merge526, 1322, 1585, 1708, 1722) are wrong on the
base binary too, are answered by the HT bridge in the HT-first phase of the
race (`ht_bridge` gives the same wrong answer), and `cb_plain1` answers 4 of
them correctly (1322 times out). They are a separate defect of the Konclude
bridge, not of the CB engine: roles that reflexivity plus inverse
functionality (through an inverse pair) force into the identity relation.
Reductions with HermiT gold in `data/bridge-misses/` (`tools/ddmin_route.py`):

- `min1722.ofn` (6 axioms): `InverseObjectProperties(r p)`,
  `Reflexive(p)`, `InverseFunctional(p)`, `≤ 1 r⁻ ⊑ B`, `B ⊑ ≥ 3 r`,
  `E ⊑ ∃r⁻.Self(s)`. HermiT: inconsistent. Bridge and automatic route:
  consistent, `E` satisfiable. `cb_plain1`: inconsistent.
- `min526.ofn` (7 axioms): bridge misses `A, B, C, D, E, F, Q1, Q2 ⊑ Q3`
  for `Q3 ≡ ∀p.Self(p) ⊓ ≤ 1 p⁻` with `p = r⁻`, `r` reflexive and inverse
  functional (so `Q3 ≡ ⊤`).

Not fixed here (HT bridge, out of the brief's two causes); reported for a
separate branch.

## Differential pools (gold-backed seeds of earlier agents)

`tools/pools.sh` on v5, routes `ht_bridge` and auto, 60 s: the ten pools
under `.work/agent-scratch/bridge-self/pools/` (abox-probes-f/m,
bridge-defers, bridge-defers-f, bridge-replay, res-data-values-3,
res-forced-nominal, res-fr282, res-lean-data-values,
sameindividual-bridge), the SELF pool (`bridge-self/pool`, 2,000) and the
m413 residue pool: 7,775 seeds, 15,550 runs. After: 14,818 ok, 614 ERR
(forced-route refusals, mostly `ht_bridge`), 104 timeouts, 14 wrong.
`tools/pools_before.sh` reran the base on every seed that was not ok after
on some route (all 14 wrong, ERR and timeout rows): every one has the same
verdict on the base. **0 new differences.** The 14 wrong rows are
pre-existing: m413 residue 7 (auto), res-data-values-3 6 (auto),
res-lean-data-values 1 (auto), the same counts the bridge-self agent
recorded. The guard fired 0 times. Data `data/pools/`.

## The 16 held-out inputs (before = base, after = v5, 240 s)

Every input keeps its answer and its reference verdicts; 10926 times out on
both (18 GiB). Wall times (s) before / after: 4903 3.7/3.3, 11647 4.3/4.2,
4796 3.0/2.9, 3917 4.5/4.3, 11378 5.6/5.5, 12191 5.9/5.8, 9151 55.4/54.4,
9577 66.5/63.7, 6132 18.9/16.9, 9899 21.2/17.9, 16315 25.4/23.4,
10838 56.1/58.7, 3087 59.9/61.4, 7557 95.3/93.1, 12128 36.1/35.7,
10926 timeout/timeout; RSS unchanged. No regression beyond noise.
Data `data/heldout/summary.tsv`.

## The 112 nominal ORE design-half inputs (base then v5, one at a time, 300 s)

109 answered by both, 109 identical signatures, 0 answer-status changes,
0 route changes; time ratio new/base over the 26 inputs above 1 s: mean
0.972, median 0.975, max 1.10. Guard fired 0 times. Data `data/nominal/`.

## C1 regression-pool sample (CB engine touched)

300 of the 1,708 admitted inputs of
`.work/v152-correctness-1920/full-candidate-inputs-ws.json`, uniformly at
random with seed 974, held-out inputs excluded (`tools/c1_sample.py`, list
in `data/c1/sample.tsv`); base and new side by side, release flags, 120 s
cap, every answer compared with the pinned references
(`tools/c1_run.sh`).

- v6 (final): 299 answered by both, 1 timeout on both; 0 reference-verdict
  differences between base and new; Konclude verdicts of the new answers:
  292 agreement, 6 inconsistent-agreement, 1 taxonomy disagreement
  (ore_ont_9540, where HermiT agrees with KM, identical on the base). Time
  ratio over 64 inputs above 1 s: mean 1.002, median 0.998, max 1.10.
  Guard fired 0 times.
- v5 (before the last elc row fix): the guard declined 6 inputs the base
  answered correctly (11572, 13112, 14185, 16115, 3839, 5220; elc flat
  hierarchy path without empty rows). Fixed in 16e638aa; all six answer and
  agree with every reference on v6. Data `data/c1/`.
