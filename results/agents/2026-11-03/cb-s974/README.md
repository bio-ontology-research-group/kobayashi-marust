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

### A third instance found by the guard: the forced `ht_rules` route

The guard declined the integration test `rules_route::same_individual_guard_does_not_fire_without_the_merge`.
The cause is the s1966 defect in another worker: the CB builder drops the
ground clauses on the forced `ht_rules` route, so a class named only by class
assertions and a DL-safe rule had no CB query. With `SubClassOf(owl:Thing :G)`
added (`engine/tests/fixtures/cb_s974/rules/rules_route_top.ofn`) the base
publishes `A` and `B` with no superclass on `ht_rules` (`A ⊑ G`, `B ⊑ G`
lost; the automatic route is exact). `reasoner::Builder::clauses` now keeps a
query (`C(x) → C(x)`) for every public class of a clause it drops (commit
80605775). This changes the CB input only on inputs where the builder drops a
clause, adds no constraint, and adds only rows.

## Commits (branch `fix/v155-cb-s974`, not pushed, not merged)

- 4e5d6a46 fix(cb,elc): send x≈y over Pred; keep concept names lost by elc bridge prep
- 531de407 docs: argue the x≈y Pred send and the elc signature retention
- a62e9ced orchestrate: publication coverage guard for row-form worker answers
- f60acd77 elc: empty rows only for concept nodes; adapt elc tests to the kept signature
- 52ee3320 results(cb-s974): tools, family data, bridge-miss reductions, README draft
- 16e638aa elc: keep empty rows for public subjects on every elc output path
- dbb259c8 docs(routing): list the elc output paths the coverage guard relies on
- 80605775 reasoner: keep a query for every public class of a dropped CB clause
- 9342784d docs(routing): the coverage guard's rules-route finding
- final commit: README, data

Binaries (`.work/agent-scratch/cb-s974/bin/`): `km-v4` = both fixes and the
first guard (three-run families), `km-v5` = f60acd77 (first pools,
held-out, nominal runs), `km-v7` = 80605775, the final code (everything
below marked "final"). Intermediate binaries differ only in which empty rows
the workers emit and in the queries the CB builder keeps for classes of
dropped clauses; the final runs repeat every measurement on v7 except the
three-run families (v7 ran them once).

## Seeds, 20 runs each (final v7, release flags)

| seed | automatic route | failed route |
|---|---|---|
| s974 | 20/20 ok | `cb_plain1` 20/20 ok |
| s1966 | 20/20 ok | `KM_ELC_SEQUENTIAL=1` 20/20 ok |

Base 117f143d: s974 wrong 10/10; s1966 wrong 5/10 automatic, 4/4
sequential. Data `data/final/seeds20.tsv`.

## Sibling families (2,000 seeds each, HermiT gold)

Generators `tools/gen_merge.py` (s974 shape: successors forced to merge
with their predecessor by reflexive, inverse-functional, functional,
symmetric and inverse roles, `≤ 1 R⁻`, Self, cardinalities) and
`tools/gen_vacuous.py` (s1966 shape: classes named only next to head-free
roles, a nontrivial superclass of `⊤`, non-EL residue). Gold by
`tools/gold_batch.sh` (HermiT 1.4 through `tools/OracleBatch.java`); runner
`tools/fam_run.py` (60 s automatic, 15 s forced). Data `data/families/`,
`data/final/`.

| family, route | v4, 3 runs per seed | final v7, 1 run | base, 1 run |
|---|---|---|---|
| merge, auto | 5,982 ok, 3 timeout, **15 wrong (5 seeds × 3)** | 1,994 ok, 1 timeout, **5 wrong (same seeds)** | 1,957 ok, 42 wrong |
| merge, `cb_plain1` | 4,305 ok, 891 timeout, 804 refused, **0 wrong** | not rerun | 1,305 ok, 93 wrong (5 s cap) |
| vacuous, auto | 5,985 ok, 15 timeout, **0 wrong** | 1,995 ok, 5 timeout, **0 wrong** | 1,966 ok, 29 wrong |
| vacuous, `KM_ELC_SEQUENTIAL` | 5,979 ok, 21 timeout, **0 wrong** | 1,993 ok, 7 timeout, **0 wrong** | 1,930 ok, 63 wrong |

No answer differed between the three runs of a seed (only ok/timeout on the
forced CB route). The `cb_plain1` refusals are forced-route exactness
refusals (ABox assertions or nominals the route would drop). The coverage
guard fired 0 times.

### Every miss: five HT-bridge answers, all pre-existing

merge526, merge1322, merge1585, merge1708 and merge1722 are wrong on the
base too, are answered by the HT bridge in the HT-first phase of the race
(`ht_bridge` gives the same wrong answer), and `cb_plain1` answers 4 of them
correctly (1322 times out). They are a defect of the Konclude bridge, not of
the CB engine: roles that reflexivity plus inverse functionality (through an
inverse pair) force into the identity relation. Reductions with HermiT gold
in `data/bridge-misses/` (`tools/ddmin_route.py`):

- `min1722.ofn` (6 axioms): `InverseObjectProperties(r p)`,
  `Reflexive(p)`, `InverseFunctional(p)`, `≤ 1 r⁻ ⊑ B`, `B ⊑ ≥ 3 r`,
  `E ⊑ ∃r⁻.Self(s)`. HermiT: inconsistent. Bridge and automatic route:
  consistent with `E` satisfiable (KM claims the answer exact).
  `cb_plain1`: inconsistent.
- `min526.ofn` (7 axioms): the bridge misses `A, B, C, D, E, F, Q1, Q2 ⊑ Q3`
  for `Q3 ≡ ∀p.Self(p) ⊓ ≤ 1 p⁻` with `p = r⁻`, `r` reflexive and inverse
  functional (so `Q3 ≡ ⊤`).

Not fixed here; they need a bridge branch.

## Differential pools (gold-backed seeds of earlier agents)

`tools/pools.sh`, routes `ht_bridge` and auto, 60 s: the ten pools under
`.work/agent-scratch/bridge-self/pools/` (abox-probes-f/m, bridge-defers,
bridge-defers-f, bridge-replay, res-data-values-3, res-forced-nominal,
res-fr282, res-lean-data-values, sameindividual-bridge), the SELF pool
(`bridge-self/pool`, 2,000) and the m413 residue pool: 7,775 seeds, 15,550
runs per binary.

- Final v7: 14,817 ok, 614 ERR (forced-route refusals, almost all
  `ht_bridge`), 105 timeouts, 14 wrong. v5: identical except one seed
  (SELF s1281, automatic route) at 54.6 s on v5 and past 60 s on v7 and on
  the base (borderline timeout, not an answer change).
- Base: `tools/pools_before.sh` reran the base on every seed that was not ok
  after on some route. Every one of them has the same verdict on the base.
  **0 new differences.** The 14 wrong rows are pre-existing (m413 residue 7,
  res-data-values-3 6, res-lean-data-values 1, all automatic route; the same
  counts the bridge-self agent recorded).
- The coverage guard fired 0 times. Data `data/pools/`.

## The 16 held-out inputs (240 s, two at a time, 12128 alone)

Every input keeps its answer and reference verdicts on v5 and v7; 10926
times out on all three binaries (18 GiB). Wall times (s), base / v5 / v7:
4903 3.7/3.3/3.4, 11647 4.3/4.2/4.1, 4796 3.0/2.9/3.0, 3917 4.5/4.3/4.4,
11378 5.6/5.5/5.8, 12191 5.9/5.8/5.6, 9151 55.4/54.4/55.2,
9577 66.5/63.7/65.7, 6132 18.9/16.9/16.5, 9899 21.2/17.9/19.5,
16315 25.4/23.4/24.6, 10838 56.1/58.7/59.8, 3087 59.9/61.4/61.7,
7557 95.3/93.1/93.5, 12128 36.1/35.7/36.2; RSS unchanged. No regression
beyond noise. Data `data/heldout/`.

## The 112 nominal ORE design-half inputs (one at a time, 300 s)

Base against v5 and against v7: 109 answered by all, 109 identical
signatures, 0 answer-status changes, 0 route changes. Time ratio over the 26
inputs above 1 s: v5 mean 0.972 (median 0.975, max 1.10), v7 mean 1.020
(median 1.014, max 1.26: ore_ont_15655, 1.95 s → 2.47 s; four alternating
reruns give base 2.53/2.32/2.21/2.38 s and v7 2.17/2.36/2.62/2.44 s, noise).
Guard fired 0 times. Data `data/nominal/`.

## C1 regression-pool sample (CB engine touched)

300 of the 1,708 admitted inputs of
`.work/v152-correctness-1920/full-candidate-inputs-ws.json`, uniformly at
random with seed 974, held-out inputs excluded (`tools/c1_sample.py`, list
in `data/c1/sample.tsv`); base and new side by side, release flags, 120 s
cap, each answer compared with the pinned references (`tools/c1_run.sh`).

- Final v7: 299 answered by both, 1 timeout on both; 0 reference-verdict
  differences between base and v7; Konclude verdicts of the v7 answers 292
  agreement, 6 inconsistent-agreement, 1 taxonomy disagreement
  (ore_ont_9540, where HermiT agrees with KM; identical on the base). Time
  ratio over 63 inputs above 1 s: mean 1.003, median 0.998, max 1.07. Guard
  fired 0 times.
- v5: the guard declined 6 inputs the base answered correctly (11572,
  13112, 14185, 16115, 3839, 5220; the elc flat hierarchy path emitted no
  empty rows). Fixed in 16e638aa; v6 and v7 answer all six and agree with
  every reference. Data `data/c1/`.

## Coverage guard firings

0 on the families (v4, v7), 0 on the pools (v5, v7), 0 on the 112 nominal
inputs (v5, v7), 0 on the C1 sample (v6, v7); 6 on the C1 sample with v5
(an elc output path, fixed) and 1 integration test with v6 (the `ht_rules`
query loss, fixed in the CB builder).

## Tests (final code 80605775, clean environment, `KM_THREADS=1`, `--test-threads=1`)

`tools/tests.sh` (no release flags exported). Library: 3,115 passed, 21
failed, 10 ignored: exactly the 21 checker-bound failures of the baseline
(20 `tableau::` tests and
`cli::cb_derivation_candidate_tests::source_exact_taxonomy_uses_real_production_traces_and_models`);
no other failing test. Integration: all 89 targets pass (the 88 of the
baseline plus the new `cb_s974`); `empty_and_universal_data_ranges` passed
in 140 s. Data `data/tests/`.

During development two tests failed and were fixed, not excused:
`incr_session::tests::session_row_delta_protocol_runs_isolated` (the guard
declined the incremental session answer, whose elc result emitted no empty
rows; fixed in 16e638aa) and
`rules_route::same_individual_guard_does_not_fire_without_the_merge` (the
guard declined the `ht_rules` answer; a real omission, fixed in 80605775).

New regression tests: `engine/tests/cb_s974.rs` (automatic route three
times on s974, s974_min, s1966 and vacuous_domain_top against HermiT;
`cb_plain1` on s974 and s974_min; `KM_ELC_SEQUENTIAL` on s1966; forced
`elc_cert` on vacuous_domain_top; forced `ht_rules` on the rules fixture),
`orchestrate::tests::coverage_guard_declines_an_answer_without_a_declared_class`,
and the adapted elc tests (`vacuous_prune_preserves_the_certified_classification`
now asserts that the pruned class keeps its row).

CB certification gate subset with the built Lean checkers
(`KM_REQUIRE_LEAN_CHECKERS=1` and the gate's `KM_CB_TEST_*` checker paths):
`terminal_snapshot_is_exact_stable_and_complete`, `certified_typed_source`,
`source_exact_taxonomy_uses_real_production_traces_and_models`,
`pred_standalone_dag_passes_the_real_lean_checker`,
`native_source_live_pred_candidate_passes_real_lean_checker`,
`native_pred_send_candidate_passes_real_lean_checker`,
`native_root_pred_send_candidate_passes_real_lean_checker`, and the
targets `cb_live_state`, `inverse_predecessor_propagation`,
`cb_nominal_merge_import`, `integral_datatype_difference`: all pass. The
full `lean/run-cb-certification-gate.sh` was not run (it rebuilds into
`.work/target` and runs `tools/workspace-preflight.sh`).

## Not done

- The five HT-bridge misses of the merge family (`data/bridge-misses/`)
  are reported, not fixed.
- No independent DL reasoner confirmed the two golds by machine: Konclude
  times out on both seeds and Openllet/JFact are not installed on ws. The
  s974 gold is proved by hand above; the s1966 gold is immediate
  (reflexive `r`, `Q3 ≡ ∃r.Self`).
- The coverage guard does not cover pair-form answers (HT, bridge, tableau,
  HT compact) or the `flat_nf1`, `mirror_private` and rule-taxonomy
  publication paths; covering them needs the workers to report the query
  classes they decided.
- The certified CB path never accepts an `x ≈ y` Pred send yet: the typed
  source declines or a CB event lacks a chronological proof, so such runs
  publish with `cannot_check`. The Lean change widens the send
  specification; it is not a completeness proof (open, per the roadmap).
- The three-run families ran on v4; the final binary v7 ran them once.
- `lean/.lake` in the worktree (22 GB, a plain copy of
  `.work/worktrees/checkers-on/lean/.lake`, no hard links) is kept for the
  re-certification; delete it if the space is needed.
