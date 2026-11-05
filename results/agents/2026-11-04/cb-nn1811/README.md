# cb-nn1811: the nn1811 miss, a native-bridge defect behind a nominal route

## Status (fourth agent, 2026-11-05 19:30, final)

State at takeover: commits 862ba3e5, ae5dbbae, 4b4cb4a3, 56cf6e56, 067201c3 and
eea918f1 (`km-p2`, sha256 `afcfbfe5…`), plus an uncommitted edit in
`docs/ROUTING.md` (cost argument for the linear `add_entailed_functional_clauses`
pass) and partial `km-p2` validation runs (`data/targets-p2.tsv`,
`data/family-p2.tsv` at 2,673 of 12,000 rows, `data/lean-audit.txt`, and 15.5 of
the 16 held-out ORE inputs in `.work/agent-scratch/cb-nn1811/runs/summary.tsv`).

Completed in this continuation:
- Confirmed the hand-checked golds for `nn1811`, `r1`, `r3`, `r5`, `r12`,
  `r13`, `r17`, `r19` and `m1`, `m2`, `m6`, `m7`, `m8`, `m9`, `m10`, `m11`,
  `m12`, `fx12`.
- Completed the 20-run target route sweep (`data/targets-routes-p2.tsv`:
  `certified_nominals` 360/360 `ok`; `nominals`, `cb_plain1`,
  `nominal_ni_abox`, `certified_card_proxy_abox`, `production_all` 600/600 `ok`
  on `r1, r5, r12, r13, r17, r19`; `nominals` 120/120 `ok` on
  `m2, m6, m8, m9, m11, m12`).
- Completed the 2,000-seed sibling family (`data/family-p2.tsv`, 12,000 rows;
  `data/family-base.tsv`, 4,000 rows; `data/family-summary.txt`;
  `data/family-nominals-check-p2.tsv`).
- Completed all 21 differential pools (`data/pools-summary.txt`: 19,790 seeds,
  0 new wrong answers, 9 base wrong seed-routes fixed).
- Completed the 16 held-out ORE inputs (`data/heldout-summary.tsv`), the 112
  nominal ORE design-half inputs (`data/ore-nominal-pair.txt`), and the
  300-input C1 regression-pool sample (`data/c1-sample-300-summary.tsv`).
- Ran the full Rust test suite (`data/tests-summary.txt`,
  `data/lib-failures.txt`), deleted `engine/target`, and wrote `HANDBACK.md`.

## Status (third agent, 2026-11-05 09:35, interim)

State at takeover: commits 862ba3e5, ae5dbbae, 4b4cb4a3 and an uncommitted
engine edit with Lean (the CB repair `Engine::offer_root_reach`), which I
committed as 56cf6e56 after reading it. Done since: `lake build ContextCalculus`
(rc 0, no `sorryAx`), gap fixtures and tests (067201c3, 10 tests in
`engine/tests/cb_nn1811.rs` pass), NOMINALS-CB.md section 12 rewritten as
repaired, target seeds 20 of 20 on `ht_bridge` and the automatic route with the
CB repair (`data/targets-p1.tsv`).

Found by running the held-out inputs, which the earlier agents had not done:
ae5dbbae made ORE 3917 take more than 100 s (base 4.4 s). The cause is the
quadratic `add_entailed_functional_clauses` (gdb: `convert_with_rule_abox`), not the CB
repair. A linear rewrite with a reference test follows in the next commit. Every
measurement below that was taken with `km-p1` (the binary before that rewrite)
is void for timing and is repeated with the final binary.

## Status (continuation, 2026-11-04 23:55)

A second agent took over after the first stopped. State found:

- Committed: 862ba3e5 (reductions r1 to r19; bridge tests), ae5dbbae (the HT
  view carries entailed functionality, `cb_to_ht.rs`), 4b4cb4a3
  (docs/ROUTING.md "Entailed functionality in the HT view"; docs/NOMINALS-CB.md
  section 12 "An at-most with a filler at a nominal", ignored test).
- Uncommitted: `tools/pools.sh` (output directory, `DIFF_THREADS` override),
  `tools/detect_changed.py`, this README.
- Validation done before the stop: family gold (2,000 `fx` seeds), the base
  family run (one run, partly aborted) and three runs of `km-v1`; pool screen
  (13,959 of 19,790 seeds may change) and most of the `km-v1` pool rows
  (`pools/after/`, stopped inside `bridge-nn-rule-fam`). Not done: the 16
  held-out and 112 nominal ORE inputs, the test suite, the family summary
  (`FAMILY_PLACEHOLDER` below).
- Open: section 12 was recorded as "open". It is a wrong answer, not a
  decline: `--route nominals` answers m9, m11, m1, m6 to m10 without `⊤ ⊑ Q3`,
  and `certified_nominals`, which races the nominal CB arm against the bridge,
  publishes that answer when the CB arm wins (m9: 1 of 7 runs on `km-v1`, 3 of
  3 then 2 of 5 on `km-base`). So it is in scope and this continuation fixes it
  in the CB engine (section "The nominal CB filler gap" below).

Branch `fix/v155-cb-nn1811` from `development/v1.5.5` at 48a1113b, worktree
`.work/worktrees/fix-cb-nn1811`. Scratch: `.work/agent-scratch/cb-nn1811/`.
Release flags for every measurement: `KM_HT_DDB=1 KM_HT_NATIVE_FULL=1
KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1
KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`. Binaries
(`.work/agent-scratch/cb-nn1811/bin/`): `km-base` = 48a1113b (sha256
a44ac18b…), `km-v1` = ae5dbbae (sha256 80a3af3f…; later commits change
docs, tests and results only). The engine sources of 48a1113b and ca64efb1
(the previous agent's `km-new`) are identical, so that agent's "after" pool
rows are a base for this branch.

## Gold (hand check)

nn1811: `InverseObjectProperties(r s)`, `InverseObjectProperties(r p)`, so
`s = p = r⁻`, and `⊤ ⊑ ≤1 r⁻` makes `s` functional.

- `Q4 ≡ ≤0 r` and `Q4 ≡ ≤1 r.(∃s.C)`. An `r`-successor `y` of `x` has `x`
  as its only `s`-successor, so `y ∈ ∃s.C` iff `x ∈ C`, and
  `≤1 r.(∃s.C) ≡ ¬C ⊔ ≤1 r`. With `Q4 ≡ ≤0 r` this gives `¬C ⊑ ≤0 r = Q4`;
  `DisjointClasses(A C)` gives `A ⊑ Q4`.
- `Q1 ≡ ≤3 s⁻.(∃p.{c})`: an `r`-successor of `x` is in `∃p.{c}` iff
  `x = c`, so `Q1 ≡ ¬{c} ⊔ ≤3 r ⊒ ≤0 r = Q4`: `Q4 ⊑ Q1`, `A ⊑ Q1`.
- `Q5 ≡ ≤1 s⁻.(∃s⁻.({b} ⊓ F))`: the elements with an `r`-successor `b` are
  `s`-successors of `b`, at most one, so `⊤ ⊑ Q5`.

HermiT's 13 pairs are these. A model with `c ∈ C` and four `r`-successors
of `c` (every element with an `r`-successor in `C` and at least two of them)
keeps `c ∉ Q1`; HermiT reports nothing more, and no further subsumption
follows from the axioms above. Every reduction below was checked against
HermiT 1.4 (`data/reductions/*.hermit.json`); r19 and r13 by hand as above.

## Cause

The wrong answer does not come from the nominal CB stack. On every run that
published it (the previous agent's and mine) the native bridge HT worker of
the `certified_nominals` race answered after 32 to 35 s
(`KM_TIMING race: HT worker exited @ 34.46s (success=true)`); in the runs
where that worker hit its 18 GiB cap the nominal CB arm gave no answer
within 150 s and the run timed out (`--route nominals` exceeds its RSS cap
as well). The previous agent's wrong automatic answers at 45 s and 58 s are
the 8.4 s bounded bridge-first attempt plus this 34 s answer.

Reductions (`data/reductions/`, 20 runs each, `data/reductions/runs20-*.txt`):

| input | axioms | HermiT | base: CB routes | base: bridge routes |
|---|---|---|---|---|
| r19 | `InverseObjectProperties(r s)`, `DisjointClasses(A C)`, `⊤ ⊑ ≤1 s`, `¬Q4 ⊑ ∃r.∃s.C` | `A ⊑ Q4` | right 20/20 | wrong 20/20 |
| r13 | as r19 with `≤1 r.(∃s.C) ⊑ Q4` | `A ⊑ Q4` | right | wrong |
| r1 | nn1811's six axioms on `r, s, p, A, C, Q4` | `A ⊑ Q4` | right | wrong |
| r3 | r1 plus `Q1 ≡ ≤3 s⁻.(∃p.{c})` | `A ⊑ Q1, A ⊑ Q4, Q4 ⊑ Q1` | `nominals` times out | wrong |
| r12 | r13 with `InverseFunctionalObjectProperty(r)` | `A ⊑ Q4` | right | wrong |
| r17 | r13 with `ObjectPropertyDomain(s ≤1 s)` | `A ⊑ Q4` | right | wrong |
| r5 | r13 with `FunctionalObjectProperty(s)` | `A ⊑ Q4` | right | right |

CB routes: `nominals`, `cb_plain1`, `nominal_ni_abox`,
`certified_card_proxy_abox`. Bridge routes: `ht_bridge`, `production_all`
(the automatic route of the TBox reductions), `certified_nominals`,
automatic. r19 has no individual: the defect is in the bridge on a
four-axiom SHI TBox with one global at-most.

Mechanism (`data/traces/`, `KM_SAT_ABSORB_DEBUG=1`): in the `A ⊓ ¬Q4` probe
the `r`-successor (node 1001) is satisfiable-cached from the earlier `C`
probe, and `SAT-ABSORB-CHECK parent=1001 concept-tag=19 role-tag=100 …
cached=true absorbable=true` absorbs `∃s.C`
(`completion/u22.rs` `is_generating_concept_satisfiable_cached_absorpable`,
a faithful port of Konclude cpp 14217). The successor that `≤1 s` would
merge into the parent is never built, so the parent never gets `C`. The test
refuses absorption only when the role to the ancestor is functional or an
at-most of it is already in the node's reapply queue. The bridge flags a role
functional only from the plain clause `R(x,y1) ∧ R(x,y2) → y1≈y2`
(`bridge.rs` functional scan), which only `FunctionalObjectProperty`
produces; `⊤ ⊑ ≤1 s` arrives as `Q_1(y1) ∧ Q_1(y2) ∧ Q_0(x) ∧ s(x,y1) ∧
s(x,y2) → y1≈y2` with `⊤` definers, from which the bridge builds a
`⊤`-qualified at-most (priority 3.5 instead of Konclude's 5.5 for an
unqualified `≤1`, so it is processed after the `∃`). Confirmed on the dumped
HT view (`KM_DUMP_TIN`) with the HT worker run standalone under the
`ht_bridge` bundle: the original view and a view with the qualifier removed
are wrong, a view with the plain clause added is right. The bridge is right
with `KM_HT_NO_SAT_EXP_CACHE=1`, `KM_BRIDGE_FRESH_ENV=1` or
`KM_HT_NO_SATURATION=1`, as on the previous agent's `nn1064`, `nn1313`,
`nn1348`. Konclude 0.7.0 does not finish TBox tasks on these inputs; it
answers the ABox form of r13 right.

## Fix (orchestrator, `orchestrate/cb_to_ht.rs`)

`add_entailed_functional_clauses` adds `R(0,1) ∧ R(0,2) → 1≈2` to the HT
view for every role whose functionality an at-most-1 clause of the view
entails with trivial guards: every concept atom of the clause is universal
(derived on every element from unit facts by one-variable Horn clauses) or
implied at its endpoint by the role atom (domain and range clauses, closed
under one-variable Horn clauses and the inverse and inclusion role clauses);
for the shared-target orientation (`InverseFunctionalObjectProperty`) it adds
the clause for every `S` with `S(0,1) → R(1,0)`. Every clause stays. The
argument is in docs/ROUTING.md ("Entailed functionality in the HT view"):
each added clause is a resolution consequence of the view, so the view has
the same models and every exact HT worker the same answer. The CB input, the
frontend output and the bridge are unchanged. Off under Lean HT certification
(the projection checker compares the view with its source clause by clause)
and with `KM_HT_NO_ENTAILED_FUNCTIONAL=1`. Not a CB calculus change, so no
Lean re-certification; the pass itself has no Lean proof (the bridge has no
Lean model).

Effect: nn1811 answers as HermiT in 0.1 s on the automatic route,
`ht_bridge` and `certified_nominals` (20 of 20 each); before, 34 s wrong or a
timeout. Every reduction answers as HermiT on every route that answers, 20
of 20 (`data/reductions/runs20-new.txt`).

What it does not cover: an at-most-1 with a real guard or filler
(`D ⊑ ≤1 s`, `⊤ ⊑ ≤1 s.D`) keeps its qualified encoding, and the bridge's
absorption test can still meet it before the at-most enters the reapply
queue. The complete repair belongs in the bridge (an agent on
`bridge-satcache` was running a family when I finished).

## The nominal CB filler gap: a wrong answer, now repaired

The earlier note recorded section 12 of `docs/NOMINALS-CB.md` as open. It is a
wrong answer, not a decline: `--route nominals` answered `m6`, `m8`, `m9`, `m11`
and (before this repair) `m1`, `m7`, `m10`, `fx12` without `⊤ ⊑ Q3`, and
`certified_nominals`, which races the nominal CB arm against the bridge,
publishes that answer when the CB arm wins (`m9`: 1 of 7 runs on `km-v1`, 3 of
3 then 2 of 5 on `km-base`). So it is in scope and repaired in commit 56cf6e56.

### Gold of the gap inputs (hand check)

Every input has `Q3 ≡ ≤1 r.(∃s.{b})` (`m11`: `≤1 r.(B ⊓ ∃s.{b})`) and
`InverseObjectProperties(s p)`, so `s = p⁻` and `y ∈ ∃s.{b}` iff `p(b,y)`.
`x ∈ Q3` says that at most one `r`-successor of `x` is a `p`-successor of `b`.
If `b` has at most one `p`-successor, this holds for every `x`: `⊤ ⊑ Q3`.
Each input forces that bound differently:

| input | axiom | why `b` has at most one `p`-successor |
|---|---|---|
| m2, m12 | `FunctionalObjectProperty(p)` | functionality |
| m8 | `⊤ ⊑ ≤1 p` | every element, so `b` |
| m9 | `{b} ⊑ ≤1 p` | `b` itself |
| m6 | `D(b)`, `D ⊑ ≤1 p` | `b ∈ D` |
| m1 | `ObjectPropertyDomain(p ≤1 p)` | `b` has none, or it is in the domain and in `≤1 p` |
| m10 | `∃p.⊤ ⊑ ≤1 p` | same case split |
| m7 | `∃p.⊤ ⊑ D`, `D ⊑ ≤1 p` | same case split |
| m11 | `{b} ⊑ ≤1 p.B` | at most one `p`-successor in `B`, and the `r`-successor must be in `B ⊓ ∃s.{b}` |

So `⊤ ⊑ Q3` and `X ⊑ Q3` for every declared class `X`; `m12` adds the told
`A ⊑ B`. No other axiom constrains the named classes, so no further
subsumption holds (every other class pair has a model with one element in the
first and not in the second). `fx12` adds `B ⊑ A` and three guarded axioms
(`A ⊓ ∃s.{a} ⊑ D`, `∃r.∃r⁻.{a} ⊑ A`, `{a} ⊑ ∃s⁻.∃s⁻.{c}`) whose guards a fresh
element avoids, so its gold is `⊤ ⊑ Q3` for all of `A B C D E Q1 Q2 Q4` plus
`B ⊑ A`. These are the HermiT answers in `data/cb-gap/*.hermit.json`.

### Fix (CB engine, `engine/src/engine.rs`, and Lean model, `lean/ContextCalculus/`)

Why `--route nominals` missed `⊤ ⊑ Q3`: the frontend encodes `{b} ⊑ ≤1 p` with
a `⊤` definer filler (`Q_3(x) ∧ Q_4(y0) ∧ Q_4(y1) ∧ p(x,y0) ∧ p(x,y1) → y0≈y1`,
`→ Q_4(x)`), and `{b} ⊑ ≤1 p.B` with `B(y0) ∧ B(y1)`. The ground context reads
every element linked to an individual `o` as its predecessor variable `y`, so
its Hyper can match `Q_4(y)` or `B(y)` only when `Q_4(y) → Q_4(y)` or
`B(y) → B(y)` is a hypothesis in the ground context. As stated in
arXiv:1805.01396, `Su^r = {B(o), S(y,o), S(o,y)}` never pushes a predecessor
label `B(y)` to the ground context.

With r-Succ on, `Engine::offer_root_reach` (`engine/src/engine.rs`) now offers
every central label `B(x)` in `rsucc_reach` of a context `u` over each root
edge `o` of `u` (`Context::root_labels`, recorded when `u` pushes an r-Succ
trigger, merge hypothesis or merge subscription to the ground context) as
`Msg::Succ { f: o, p: B(y) }`, once per `(o, reach entry)` (`root_reach_hwm`).
On the return path, r-Pred discharges an individual-free body atom `B(y)` of a
ground clause when one of `u`'s root edges carries `B(y)`. `KM_NO_ROOT_REACH=1`
restores the previous behaviour (negative control). Argument in
`docs/NOMINALS-CB.md` section 12.

Lean re-certification (`data/lean-audit.txt`):
- `lean/ContextCalculus/Nominals.lean` section 5b: `root_label_hyp_sound`
  (tautology `B(y) → B(y)`, depends on `propext`), `rpredY_valid` (the r-Pred
  substitution `y ↦ x` preserves validity on every clause, including `f(x)`
  terms), and `rpred_label_sound` (resolution of `B(y){y↦x} = B(x)` against a
  context clause with `B(x)` in its head; depends on `propext`,
  `Classical.choice`, `Quot.sound`).
- `lean/ContextCalculus/CBRSuccClosure.lean`: `parentOfEdge` maps `.const o`
  to `.var 0` so `rSuccOffers` states root-edge offers;
  `forwardPredicate_root_label` proves that offering `B(x)` over `.const o`
  pushes `B(y)`.
- `PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=4 nice taskset -c 17-24 lake build ContextCalculus`
  and all 41 `cb-*` checker executables built with rc 0 and 0 `sorryAx`.

Effect on the gap inputs: `m6`, `m8`, `m9`, `m11` (and `m2`, `m12`) answer as
HermiT in 0.02 s on `--route nominals`, `ht_bridge`, `certified_nominals` and
the automatic route (20 of 20 runs each). On `m1`, `m7`, `m10` and `fx12`
(where the filler sits behind a domain axiom or an existential) `--route nominals`
no longer gives a wrong answer and instead times out cleanly while saturating
equality disjunctions over fresh nominals; `ht_bridge`, `certified_nominals`
and the automatic route answer all four as HermiT in 0.01 to 0.02 s (20 of 20
runs each).

## Target seeds and reductions (20 runs per route, final binary `km-p2`)

`tools/runs20.sh`, release flags (`data/targets-p2.tsv`,
`data/targets-routes-p2.tsv`):

| seeds | routes | runs | verdict | max wall (s) |
|---|---|---|---|---|
| `nn1811`, `r1`, `r3`, `r5`, `r12`, `r13`, `r17`, `r19`, `m1`, `m2`, `m6`, `m7`, `m8`, `m9`, `m10`, `m11`, `m12`, `fx12` (18 inputs) | `ht_bridge`, `auto`, `certified_nominals` | 20 per route (1,080 runs) | 1,080 / 1,080 ok | 0.14 (`nn1811`), 0.02 (all others) |
| `r1`, `r5`, `r12`, `r13`, `r17`, `r19` (6 reductions) | `nominals`, `cb_plain1`, `nominal_ni_abox`, `certified_card_proxy_abox`, `production_all` | 20 per route (600 runs) | 600 / 600 ok | 0.02 |
| `m2`, `m6`, `m8`, `m9`, `m11`, `m12` (6 gap inputs) | `nominals` | 20 per input (120 runs) | 120 / 120 ok | 0.02 |

On `nn1811`, `r3`, `m1`, `m7`, `m10` and `fx12`, `--route nominals` times out
with no wrong answer.

## Sibling family (`fx0` to `fx1999`, 2,000 seeds with HermiT gold)

Generator `tools/gen_fx.py` (variations of `r19`, `r13` and `nn1811`:
functionality/at-most encodings on inverse-linked roles, two-step paths,
nominals in 40% of seeds). All 2,000 seeds have HermiT 1.4 gold
(`.work/agent-scratch/cb-nn1811/fam/gold/`). Runner `tools/family_complete.py`
(`data/family-p2.tsv`, `data/family-base.tsv`, `data/family-summary.txt`, 60 s
cap on `auto`, 15 s cap on forced routes):

| route | binary (runs) | ok | WRONG | TIMEOUT | NOANSWER (forced defer) |
|---|---|---|---|---|---|
| `auto` | `km-base` (1 run × 2,000) | 1,949 | **18** | 33 | 0 |
| `auto` | `km-p2` (3 runs × 2,000 = 6,000) | 5,940 (1,980 × 3) | **0** | 60 (20 × 3) | 0 |
| `ht_bridge` | `km-base` (1 run × 2,000) | 1,891 | **18** | 39 | 52 |
| `ht_bridge` | `km-p2` (3 runs × 2,000 = 6,000) | 5,796 (1,932 × 3) | **0** | 48 (16 × 3) | 156 (52 × 3) |

- **0 wrong answers** on `km-p2` across all 12,000 runs (`ht_bridge` and `auto`).
- All **18 seeds that were wrong on `km-base`** (`fx61`, `fx520`, `fx531`,
  `fx666`, `fx674`, `fx829`, `fx878`, `fx906`, `fx988`, `fx1034`, `fx1070`,
  `fx1077`, `fx1154`, `fx1269`, `fx1386`, `fx1673`, `fx1751`, `fx1798`) answer
  `ok` in 3 of 3 runs on both `ht_bridge` and `auto`.
- **0 seeds vary across their three runs** on either route.
- On `ht_bridge`, 0 seeds that were `ok` on `km-base` become non-`ok` on
  `km-p2`, and 23 seeds that timed out on `km-base` now answer `ok` 3/3 (39
  timeouts down to 16). The 52 `NOANSWER` seeds are identical on `km-base` and
  `km-p2` (exactness deferrals when an inverse-role or ABox shape is declined
  by the forced native bridge).
- On `auto`, 15 seeds that timed out on `km-base` now answer `ok` 3/3, and 2
  seeds (`fx346`, `fx1454`, both in the 52 `ht_bridge` deferrals so the
  automatic route falls back to the nominal CB arm) answered on `km-base` and
  time out at 60 s on `km-p2` under `Engine::offer_root_reach` (net timeouts
  33 down to 20).
- On `--route nominals` over `fx0` to `fx1064` (1,065 seeds × 3 runs in
  `.work/agent-scratch/cb-nn1811/famrun/new-3runs.tsv`), `km-v1` (before
  `Engine::offer_root_reach`) had 2,682 `ok`, 509 `TIMEOUT`, and 6 `WRONG`
  rows across 2 seeds (`fx12` and `fx244`, which reduced to `m1`..`m12`). With
  `km-p2` (`data/family-nominals-check-p2.tsv`), neither `fx12` nor `fx244`
  gives a wrong answer.

## Differential pools (`tools/pools.sh`, `tools/pools_complete.py`, 60 s cap)

All 21 gold-backed pools of earlier agents (`.work/agent-scratch/bridge-self/pools/*`,
`bridge-self/{pool,regress,micro}`, `bridge-m413/{respool,kseeds,k2seeds}`,
`cb-s974/{fam-merge,fam-vacuous}`, `bridge-reflexive/{fam,seeds20}`,
`bridge-nn-rule/fam`: 19,790 seeds, routes `ht_bridge` and `auto` = 39,580
seed-routes; `data/pools-summary.txt`):

| route | binary | ok | WRONG | TIMEOUT | ERR / NOANSWER |
|---|---|---|---|---|---|
| `auto` | `km-base` | 19,631 | 20 | 135 | 4 |
| `auto` | `km-p2` | 19,625 | 15 | 146 | 4 |
| `ht_bridge` | `km-base` | 18,236 | 5 | 65 | 1,484 |
| `ht_bridge` | `km-p2` | 18,239 | 1 | 59 | 1,491 |

- **0 new wrong answers** (`new wrong vs base: 0`).
- **9 wrong seed-routes fixed** in `bridge-nn-rule-fam`: `nn1811` (`auto`),
  `nn1064` (`ht_bridge`, `auto`), `nn1116` (`ht_bridge`, `auto`), `nn1313`
  (`ht_bridge`, `auto`), and `nn1348` (`ht_bridge`, `auto`) all move from
  `WRONG` to `ok`.
- The remaining `WRONG` rows are all pre-existing and identical to base:
  `nn5` on `ht_bridge` and `auto` in `bridge-nn-rule-fam` (the seed where
  HermiT's gold is wrong, `docs/HYBRID-CB-HT.md` section 22), and the 14
  `auto` rows on `bridge-m413-respool` (7),
  `bridge-self-pools-res-data-values-3` (6), and
  `bridge-self-pools-res-lean-data-values` (1) (documented facet/string
  corners, `docs/DATATYPES.md` and `docs/V1.5.5-STATUS.md`).

## The 16 held-out ORE inputs (`tools/heldout_seq.sh`, 240 s cap, one at a time)

Paired `km-base` (`48a1113b`) and `km-p2` (`eea918f1`), release flags
(`data/heldout-summary.tsv`):

| ORE input | base wall (s) | new wall (s) | base RSS (GiB) | new RSS (GiB) | reference verdicts (both identical) |
|---|---|---|---|---|---|
| 4903 | 3.65 | 3.57 | 0.18 | 0.19 | konclude=agreement |
| 11647 | 4.49 | 4.41 | 0.24 | 0.25 | konclude=agreement hermit=agreement openllet=agreement |
| 4796 | 3.07 | 3.11 | 0.20 | 0.20 | konclude=agreement openllet=agreement jfact=agreement |
| 3917 | 4.95 | 4.95 | 0.26 | 0.27 | konclude=agreement jfact=consistency_disagreement |
| 11378 | 6.19 | 6.62 | 0.31 | 0.31 | konclude=agreement jfact=consistency_disagreement |
| 12191 | 6.18 | 6.17 | 0.32 | 0.31 | konclude=agreement jfact=consistency_disagreement |
| 9151 | 58.69 | 57.85 | 0.63 | 0.63 | konclude=agreement jfact=consistency_disagreement |
| 9577 | 81.18 | 83.49 | 0.66 | 0.67 | konclude=agreement jfact=consistency_disagreement |
| 6132 | 21.27 | 20.75 | 0.51 | 0.51 | konclude=agreement hermit=agreement |
| 9899 | 22.44 | 22.82 | 0.51 | 0.51 | konclude=agreement hermit=agreement |
| 16315 | 28.21 | 28.81 | 1.33 | 1.33 | konclude=agreement |
| 10838 | 60.59 | 60.27 | 2.35 | 2.35 | konclude=agreement |
| 3087 | 60.91 | 66.12 | 2.47 | 2.47 | konclude=agreement |
| 7557 | 95.59 | 100.91 | 3.18 | 3.17 | konclude=agreement |
| 12128 | 38.03 | 39.59 | 2.20 | 2.22 | konclude=agreement |
| 10926 | 241.12 (rc=124) | 241.03 (rc=124) | 18.01 | 18.02 | timeout on both |

15 of 16 answer on both binaries and agree with Konclude; 10926 times out on
both at 18 GiB. Total wall time on the 15 answered inputs: base 495.4 s, new
509.4 s (ratio 1.028; mean per-input ratio 1.012, median 1.000).

## The 112 nominal ORE design-half inputs (`tools/ore_nominal_seq.sh`, 300 s cap, one at a time)

Paired sequential run (`data/ore-nominal-pair.txt`):

- **104 answered by both binaries, 104 identical signatures (`differ []`)**.
- **0 route changes**, **0 coverage guard firings**.
- Time ratio `new/base` over the 33 inputs above 1 s: **mean 0.994, median
  0.995, max 1.15** (`ore_ont_668`: 2.80 s to 3.21 s).
- One borderline timeout at the 300 s cap: `ore_ont_3077` finished at 293.9 s
  in the `before` pass and hit the 300.0 s cap in the `after` pass (ratio
  1.021); `ore_ont_3077` routes to `ht_bridge` and `cb_to_ht [entailed-functional]`
  adds `+0 functional clauses`, so both binaries execute the identical HT view
  and worker.

## C1 regression-pool sample (`tools/c1_pair.sh`, 300 inputs, 60 s cap)

300 inputs drawn with `random.Random(1811)` from the 1,708 admitted rows of
`.work/v152-correctness-1920/full-candidate-inputs-ws.json`
(`tools/c1-sample-300.txt`), run side by side with `km-base` and `km-p2` under
release flags (`data/c1-sample-300-summary.tsv`):

- 294 answered (`rc=0`) by both binaries, 5 timeouts (`rc=124`) on both, 1
  exactness refusal (`rc=3`, `ore_ont_8250`) on both; **0 status changes**.
- **0 reference-verdict differences** between `km-base` and `km-p2` across all
  294 answered inputs. Konclude comparison on the 294 answers: 284 `agreement`,
  7 `inconsistent_agreement`, and 3 known adjudicated disagreements identical
  on base and new (`ore_ont_3794`, `ore_ont_6333` where Openllet and JFact
  agree with KM, and `ore_ont_9540` where HermiT agrees with KM).
- Time ratio `new/base` over the 83 inputs above 1 s: **mean 0.995, median
  1.001, max 1.101**.
- Publication coverage guard fired 0 times.

## Full Rust test suite (`tools/tests.sh`, `data/tests-summary.txt`)

Run in a clean environment (`env -i PATH=... HOME=... CARGO_TARGET_DIR=...`)
with `--test-threads=1`:

- **Library (`cargo test --release --lib -- --test-threads=1`)**: 3,120 passed,
  **21 failed**, 10 ignored (`data/lib-failures.txt`). The 21 failures are the
  exact 21 baseline tests in
  `.work/worktrees/fix-bridge-defers/results/agents/2026-11-01/bridge-defers/data/lib-failures.txt`
  (0 new library failures).
- **Integration targets (`engine/tests/*.rs`, 90 targets)**: **89 of 90 pass
  (`rc=0`)**, including `cb_nn1811` (10 passed),
  `empty_and_universal_data_ranges` (10 passed), and `source_incremental_rules`
  (4 passed).
- **Newly failing integration tests (3 tests in `top_nominal_data_successors`)**:
  - `top_nominal_data_successors::exact_data_cardinality_with_has_value_hub_keeps_counting`
  - `top_nominal_data_successors::hermit_answers_on_every_route`
  - `top_nominal_data_successors::top_min_data_cardinality_with_inverse_functional_hub_is_consistent`

  All three fail by hitting the test harness's 120 s timeout on the forced
  `Some("nominals")` route on `tests/fixtures/top_nominal_data/probe_v7.ofn`
  (`⊤ ⊑ ≥2 u`, `⊤ ⊑ ∃r.{a}`, `{a} ⊑ ≤1 r⁻`) and `probe_v11.ofn` (the same hub
  with `⊤ ⊑ =2 u`, `⊤ ⊑ ≤1 r`, `A ⊑ ≥3 u`). Both fixtures write `{a} ⊑ ≤1 r⁻`
  with the universal `⊤` definer `Q_0(y0) & Q_0(y1) & Q_3(x) & __inv__r(x,y0)
  & __inv__r(x,y1) -> y0=y1`. Before `Engine::offer_root_reach` (`56cf6e56`),
  `probe_v7.ofn` and `probe_v11.ofn` finished in 0.06 s on `--route nominals`
  only because of the section 12 incompleteness bug: `Q_0(y) -> Q_0(y)` never
  reached the ground context, so `{a} ⊑ ≤1 r⁻` never fired there. With
  `offer_root_reach`, `{a} ⊑ ≤1 r⁻` fires in the ground context and triggers
  `Nom`, which in the presence of `⊤ ⊑ ≥2 u` (`Q_0(x) -> Q_1(x) | __data__(x)`,
  `Q_1(x) -> u(x, f_Q_1_0(x))`) saturates equality disjunctions over fresh
  nominals past 120 s (the exact phenomenon already recorded in
  `docs/NOMINALS-CB.md` section 6 lines 815-821 when `Q_0` was eliminated on
  `probe_v7.ofn`). On the automatic route and on `certified_nominals`, both
  `probe_v7.ofn` and `probe_v11.ofn` still answer in 0.02 s as HermiT.

## Commits on `fix/v155-cb-nn1811`

- `862ba3e5`: `test(cb-nn1811): add reductions r1..r19 of nn1811`
- `ae5dbbae`: `fix(orchestrate): carry entailed functionality in the HT view`
- `4b4cb4a3`: `docs(routing): record the entailed-functionality HT view rule and the nominal CB filler gap`
- `56cf6e56`: `fix(cb): offer root-edge predecessor labels to the ground context`
- `067201c3`: `test+docs(cb-nn1811): nominal CB filler gap fixtures, tests and Lean proof note`
- `eea918f1`: `perf(cb_to_ht): make add_entailed_functional_clauses linear in the clause set`
- `381441a8`: `docs+test(cb-nn1811): status note, nominal CB gap gold and Lean summary, validation tools and target/held-out results`
- `2095786f`: `results(cb-nn1811): C1 300-input sample, differential pools and 112 nominal ORE summaries`
- `3852a11b`: `results(cb-nn1811): completed 2,000-seed sibling family runs and summary`

## Residual / What was not managed

1. **Real-guard / real-filler at-most-1 absorption (`D ⊑ ≤1 s`, `⊤ ⊑ ≤1 s.C`)**:
   As recorded in `docs/ROUTING.md` ("Entailed functionality in the HT view"),
   when `s = r⁻` is only conditionally functional under a genuine concept guard
   `D(x)` or filler `C(y)` that is neither universal nor implied by `s(x,y)`,
   absorbing `r(y,x) ∧ C(x) → B(y)` requires propagating `C(x)` or `D(y)` across
   the edge in `absorb_functional_inverse_links` rather than emitting an
   unconditional functionality clause.
2. **Nom-rule saturation on forced `--route nominals` (`m1, m7, m10, fx12,
   probe_v7, probe_v11`)**:
   `Engine::offer_root_reach` removes the wrong (incomplete) answer on the
   nominal CB arm by offering `B(y) -> B(y)` to the ground context when a root
   edge `s(x, #a)` co-occurs with `B(x)`. On ontologies where firing `{a} ⊑ ≤1
   r⁻` in the ground context combines with unrestricted existential or data
   successors (`m1, m7, m10, fx12, probe_v7, probe_v11`), the forced
   `--route nominals` worker now times out instead of returning an incomplete
   taxonomy; `auto`, `ht_bridge`, and `certified_nominals` answer all of them
   in 0.02-0.06 s.
