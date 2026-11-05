# bridge-nn-term: termination and search cost of the NN-rule port

**Status (2026-11-05, continuation completed).** The first agent committed the
fixed distinct set, per-candidate NN-rule decisions and leaf-job exit
(7ae078c3, 68a1b917) and section 24 with initial results (5b50db3a), then
stopped. A second continuation agent added a status note (470609cc), reduced
`nn1153` to `n1153min` and fixed the missing descriptor track point in
`try_initializing_concept_from_saturated_data` (c886e3f9), and completed the
termination argument in section 24. This continuation routed
`KM_HT_NN_DISTINCT_FIRST` and `KM_BRIDGE_DUMP_CLASH_LIMIT` through cached
completion accessors so `completion_hot_path_env` passes, added `nn1153` to the
`bridge_nn_term` regression target (061fb797), and completed every validation
item of `common.md` on the final LTO binary (`km-c886`).

Branch `fix/v155-bridge-nn-term` from `development/v1.5.5` at 48a1113b,
worktree `.work/worktrees/fix-bridge-nn-term`. Scratch:
`.work/agent-scratch/bridge-nn-term/`. Release flags for every measurement:
`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`.
Binaries (`.work/agent-scratch/bridge-nn-term/bin/`, release profile with
LTO unless noted): `km-base` = 1ffee4a6 (the bridge-nn-rule agent's base,
before the NN-rule; `../bridge-nn-rule/bin/km-base`), `km-48a` = 48a1113b
(byte-identical to the bridge-nn-rule agent's `km-new`), `km-new` = 68a1b917,
`km-c886` = 061fb797 (the final branch binary). `km-v1` to `km-v18` are
non-LTO experiment builds (`buildfast.sh`).

The argument for every change is in `docs/HYBRID-CB-HT.md` section 24.

## Infinite or exponential, and why

Exponential, not infinite, on every input measured; but the 48a procedure had
no bound. The seven seeds on 48a with a 120 s cap (`data/seven/n48.tsv`,
one run): `nn346` 91 to 100 s, `nn1333` 95 to 96 s, `nn952` 58 s, `nn745` 30
to 38 s, `nn969` 8.1 s (auto) and 35.7 s (`ht_bridge`); `nn1957` and `nn777`
over 120 s (`nn777` `ht_bridge`: the bridge defers at its 60 s budget). With
the NN trace, `hang952` ends after 25 s and its new nominals keep ids below
1050.

Two causes multiply (section 24):

1. The general arm recomputed its new-nominal slots at every application from
   the current qualified nominal neighbours; the pairwise at-most branching
   could merge two of them, which returned the slot, and the arm converted the
   next candidate again (`hang952`: two restrictions at the reflexive nominal
   `b` convert the same candidate in alternation). No bound on new nominals
   per restriction, and the clash sets blamed every counted successor.
2. On the retained consistency leaf (section 16) an NN-rule clash at an ABox
   nominal depends on the leaf's own choices, which the job cannot revise. The
   clash analysis marks no open job decision, and the DDB safety net
   backtracks chronologically through every job decision before the leaf
   rejects the unsatisfiable verdict and the job reruns on the base. This is
   where the time goes: on the reductions `xbmin` (three axioms, no ABox) and
   `n745min` (five axioms) the 48a binary needs 12.7 to 21.0 s and 60.4 to
   68.5 s, and with `KM_BRIDGE_NO_LEAF_REUSE=1` both answer in 0.03 s.

Konclude 0.7.0 (`-w 2`) answers all 15 target seeds and reductions in 7 to
75 ms of classification time and agrees with HermiT on each
(`data/konclude/timings.tsv`). The bridge-nn-rule README's "Konclude does not
finish" was the default worker count: Konclude hangs at 0 % CPU on this host
even on a one-axiom ontology; `-w 2` works.

## The fix (commits)

- `7ae078c3` fix(bridge): Konclude's per-candidate NN-rule decisions, fixed
  distinct set with slot budget, leaf jobs end on unattributed clashes
- `68a1b917` fix(bridge): NN distinct set follows merged representatives;
  regression target `bridge_nn_term`
- `5b50db3a` docs(hybrid): section 24, termination and search cost of the
  NN-rule; bridge-nn-term results so far
- `470609cc` results(bridge-nn-term): status note of the continuation
- `c886e3f9` fix(bridge): sat-data initialisation reads the descriptor's track
  point; fallback-nomark clash dump
- `061fb797` fix(bridge): cache `KM_HT_NN_DISTINCT_FIRST` and
  `KM_BRIDGE_DUMP_CLASH_LIMIT`; add `nn1153` fixture

1. Konclude's branching-merging state per at-most restriction on the nominal
   node (`NnAtmostState`, journaled with the node): the fixed distinct set,
   `cardinality` new-representative slots that are never returned, the base
   dependency of the last decision, and the merge dependencies of lost
   representatives.
2. One candidate per step, with Konclude's alternatives (merge into each
   mergeable representative, then a new representative while a slot
   remains), as an at-most branch point; the probe root stays out.
3. Konclude's causes: candidate, representatives, rejected merges, base
   dependency chain, lost representatives.
4. A job on the retained leaf ends when its clash analysis marks no open job
   decision; the leaf rejects that outcome and the unchanged job reruns on
   the base (no verdict depends on it). `KM_BRIDGE_LEAF_CHRONOLOGICAL=1`
   restores the old path.
5. In `try_initializing_concept_from_saturated_data` (`completion/u17.rs`),
   both label-set lookups use `get_concept_descriptor_and_reapply_queue_by_tag_in_context`
   instead of the ctx-less stub so the AND dependency and clash carry
   `conDes->getDependencyTrackPoint()` instead of `TrackPointId::NONE` (which
   caused a tracking error that aborted DDB clash analysis and forced
   chronological backtracking on `nn1153` and five other family seeds).

Termination argument: section 24 (general arm bounded by `n` unreturned slots
per `(x, ≤n R.C)` per branch line; functional arm creates at most one nominal
per `(x, R)` per line because incoming links relocate on merge; at most
`N₀ · Kˡ` nominal nodes at level `l` per line; finite branching factor and
König's lemma, with the nominal-level bound and tree blocking taken from the
SROIQ proof of Horrocks, Kutz and Sattler 2006).

## Hand derivations of the reductions (`data/reductions/`)

1. **`hang952.ofn`** (6 axioms): `ReflexiveObjectProperty(:s)` gives
   `⊤ ⊑ ≥1 s.⊤`, and `Q3 ≡ ≤0 s`, so `Q3 ⊑ ⊥` (`unsatisfiable: ["Q3"]`). The
   remaining axioms define `Q1`, `Q5 ≡ ≤2 s⁻.∃s.{b} ≡ ≤1 s⁻.∃r⁻.F` and
   `D ⊑ ∃p⁻.∀p⁻.{b}`; taking `r = p = ∅` and `s = id` satisfies both `Q5`
   equivalences on all elements, and varying the remaining classes and roles
   independently refutes every other subsumption.
2. **`m1.ofn`** (3 axioms): `ReflexiveObjectProperty(:s)` and
   `Q5 ≡ ≤2 s⁻.∃s.{b} ≡ ≤1 s⁻.∃r⁻.F`. Taking `s = id` and `r = ∅` makes
   every element satisfy both descriptions of `Q5`; all classes are
   satisfiable and no subsumptions hold between distinct named classes.
3. **`xbmin.ofn`** (3 axioms): `Q1 ≡ ≤2 p.∃p⁻.({a} ⊓ E) ≡ ≤1 p⁻.∃s.D` and
   `Q4 ≡ ≤1 p.(C ⊓ ∃s.{a})`. With `p = s = ∅`, `Q1 = Q4 = Δ`; varying `C`,
   `D`, `E`, `p` and `s` separates `Q1`, `Q4` and the atomic classes, so
   all classes are satisfiable and no subsumptions hold.
4. **`nn346-batch.ofn`** (11 axioms): `XB ≡ D ⊓ ¬Q1 ⊓ ¬Q4 ⊓ ¬Q2` gives
   `XB ⊑ D` directly. For any `x ∈ XB`, `x ∈ ¬Q4` means `x ∈ ≥2 p.(C ⊓ ∃s.{a})`,
   so `x` has a `p`-successor `y ∈ C`. By `InverseObjectProperties(:p :r)`,
   `(y, x) ∈ r`, and by `C ⊑ ∀r.F`, `x ∈ F`. Hence `XB ⊑ F`. All classes are
   satisfiable and no other subsumptions hold (`subsumptions: [["XB", "D"], ["XB", "F"]]`).
5. **`n745min.ofn`** (5 axioms): `s = p⁻`, `Q5 ≡ ≤1 p.∃s.{b} ≡ ≤2 s⁻.∃s.C`,
   `(≤1 s⁻.(¬E ⊓ ∃p.({b} ⊓ D))) ⊑ E`, and `a ∈ ∀p.{a}`. The third axiom is
   equivalent to `¬E ⊑ ≥2 p.(¬E ⊓ ∃p.({b} ⊓ D))`: placing `b ∈ D ∩ E` and a
   pair of mutually `p`-linked elements `u₁, u₂ ∈ ¬E` both `p`-linked to `b`
   satisfies `¬E` without forcing `⊤ ⊑ E`. All classes are satisfiable and no
   subsumptions hold.
6. **`n1333min.ofn`** (12 axioms): `EquivalentClasses(:Q4 :F)` gives `F ⊑ Q4`
   and `Q4 ⊑ F`. `Q1 ≡ ≤1 r⁻` and `Q2 ≡ ≤1 r⁻.∃p.C`: every element with at
   most one `r⁻`-neighbour has at most one `r⁻`-neighbour in `∃p.C`, so
   `Q1 ⊑ Q2`. All classes are satisfiable and no other subsumptions hold
   (`subsumptions: [["F", "Q4"], ["Q1", "Q2"], ["Q4", "F"]]`).
7. **`n1153min.ofn`** (10 axioms): `InverseFunctionalObjectProperty(:p)` gives
   `⊤ ⊑ ≤1 p⁻`, which implies `⊤ ⊑ ≤2 p⁻.∃r.F ≡ Q1` (and by `Q1 ≡ ≤0 p⁻`
   forces `p = ∅` in every model). Hence every named class (`A`, `B`, `C`,
   `D`, `E`, `F`, `Q2`, `Q3`, `Q4`) is subsumed by `Q1`. From
   `Q4 ≡ {b} ⊓ B ⊓ ∃s⁻.{c}` we also have `Q4 ⊑ B`. For consistency and the
   absence of further subsumptions: let `T = {0, 1}*` be the infinite binary
   tree with root `ε = a`, set `(a, a) ∈ s` and `(w, w0), (w, w1) ∈ s` for
   each `w ∈ T` (each node in `T` has `s`-indegree 1, satisfying
   `InverseFunctionalObjectProperty(:s)`), `D = {a}`, `r = T × {a}`, and
   `p = ∅`. Then `(a, a) ∈ r`, `D ⊑ ∃s.{a}`, `≤0 r = Δ \ T = ≤1 s.∃r.D = Q3`,
   and `∃r.(≤1 p) = T ⊑ B`; elements outside `T` have no `r`- or `s`-links and
   separate the remaining classes.

## Target seeds and reductions, before and after (`data/seven/`, 120 s cap, 20 runs)

| input | base auto / `ht_bridge` | 48a auto / `ht_bridge` | `km-c886`, 20 runs, auto / `ht_bridge` | Konclude `-w 2` |
|---|---|---|---|---|
| `nn1333` | 0.48 / 0.52 s | 96.04 / 95.27 s | ok (20/20) 4.41-4.79 / 4.26-4.62 s | 75 ms |
| `nn346` | 0.02 / 0.02 s | 99.71 / 91.13 s | ok (20/20) 0.02-0.03 / 0.02 s | 18 ms |
| `nn952` | 0.02 / 0.02 s | 57.70 / 57.54 s | ok (20/20) 0.03-0.04 / 0.02-0.04 s | 14 ms |
| `nn745` | 0.10 / 0.06 s | 38.49 / 30.38 s | ok (20/20) 0.06-0.08 / 0.06-0.09 s | 54 ms |
| `nn1957` | 30.61 / 31.51 s | >120 / >120 s | ok (20/20) 0.03-0.05 / 0.03-0.05 s | 31 ms |
| `nn777` | 38.40 / 30.30 s | >120 s / defer 60.51 s | ok (20/20) 0.03-0.04 / 0.03-0.07 s | 37 ms |
| `nn969` | 8.11 / 37.78 s | 8.11 / 35.70 s | ok (20/20) 8.09-8.11 / 30.61-32.77 s | 19 ms |
| `nn1153` | 0.03 / 0.03 s | 29.19 / 21.55 s | ok (20/20) 0.04-0.05 / 0.03-0.04 s | 12 ms |
| `hang952` | 0.39 / 0.39 s | 1.81 / 11.77 s | ok (20/20) 0.02-0.03 / 0.01-0.03 s | 18 ms |
| `m1` | 0.02 / 0.01 s | 0.98 / 0.95 s | ok (20/20) 0.01-0.02 / 0.01 s | 7 ms |
| `n1153min` | 0.03 / 0.03 s | 31.60 / 22.72 s | ok (20/20) 0.04-0.05 / 0.03-0.04 s | 12 ms |
| `n1333min` | 0.49 / 0.54 s | 94.97 / 95.14 s | ok (20/20) 4.43-4.70 / 4.34-4.72 s | 34 ms |
| `n745min` | 0.02 / 0.02 s | 68.51 / 60.43 s | ok (20/20) 0.02 / 0.02 s | 8 ms |
| `nn346-batch` | 0.02 / 0.02 s | 38.22 / 30.18 s | ok (20/20) 0.02-0.03 / 0.02 s | 8 ms |
| `xbmin` | 0.02 / 0.01 s | 20.96 / 12.74 s | ok (20/20) 0.02 / 0.02 s | 11 ms |

All 600 runs of `km-c886` (300 `auto`, 300 `ht_bridge`) match HermiT and
Konclude (`data/seven/new.tsv`).

## The NN family (2,000 seeds, three runs, both routes, `data/family/`)

Caps match the `bridge-nn-rule` campaign: 60 s on `auto`, 30 s on `ht_bridge`
(6,000 runs per route).

| binary | route | `ok` | `WRONG` | `TIMEOUT` | `NOANSWER` | `NOGOLD` |
|---|---|---|---|---|---|---|
| `km-base` (1 run) | `auto` | 1,739 | 249 | 5 | 0 | 7 |
| `km-base` (1 run) | `ht_bridge` | 1,732 | 250 | 9 | 2 | 7 |
| `km-48a` (3 runs) | `auto` | 5,901 | 16 | 62 | 0 | 21 |
| `km-48a` (3 runs) | `ht_bridge` | 5,875 | 15 | 83 | 6 | 21 |
| `km-c886` (3 runs) | `auto` | 5,943 | 18 | 18 | 0 | 21 |
| `km-c886` (3 runs) | `ht_bridge` | 5,928 | 15 | 30 | 6 | 21 |

Seed-route comparison (`data/family/delta.txt`, `data/family/compare.txt`):

- Of the 499 seed-routes that `km-base` answers wrongly, **484** are `ok` in
  all 3 runs of `km-c886` (`km-48a`: 464). All 464 seed-routes recovered by
  `km-48a` remain `ok` in all 3 runs of `km-c886`, and `km-c886` recovers 20
  additional seed-routes (`nn1163`, `nn1170`, `nn164`, `nn427`, `nn519`,
  `nn584`, `nn635`, `nn668`, `nn798` on both routes, plus `nn1450` and
  `nn1484` on `ht_bridge`).
- Across the entire 4,000 seed-routes, **32** seed-routes are `ok` in all 3
  runs of `km-c886` and not in all 3 runs of `km-48a`, while **0** seed-routes
  that are `ok` in all 3 runs of `km-48a` fail on any run of `km-c886`.
- Only 1 seed-route that `km-base` answered in its 1 run is not `ok` in all 3
  runs of `km-c886` under the 30 s forced-route cap: `('nn969', 'ht_bridge')`,
  which takes 28.8 s on `km-base`, 29.4 to >30 s on `km-48a` (2/3 timeouts),
  and 30.6 to 32.8 s on `km-c886` (20/20 `ok` under the 120 s target cap; as
  slow with `KM_HT_NO_NN_RULE=1`).
- Zero new wrong answers: the 11 wrong seed-routes on `km-c886` (`nn1064`,
  `nn1116`, `nn1313`, `nn1348`, `nn5` on both routes, and `nn1811` on `auto`)
  are the exact 6 seeds documented in section 22, all wrong on `km-base` and
  `km-48a`.

## Differential pools (`data/pools/`, 60 s cap, both routes)

21 gold-backed pools of earlier agents (17,804 seeds, 35,608 seed-route runs
across `ht_bridge` and `auto`; `data/pools/after/summary.txt`,
`data/pools/compare.txt`):

- Totals on `km-c886`: 33,954 `ok`, 1,486 `ERR` (forced-route refusals), 154
  `TIMEOUT`, 14 `WRONG`.
- The 14 `WRONG` rows are the same pre-existing data-value seeds on the
  automatic route as on `km-base` and `km-48a`: `res-data-values-3` (6),
  `res-lean-data-values` (1), and their copies in `bridge-m413-respool` (7).
- 20 of the 21 pools have 0 verdict differences against `km-48a`.
- In `bridge-reflexive-fam`, two `auto` rows (`refl1575.ofn` and `refl352.ofn`,
  both of which time out on `ht_bridge` on `km-48a` and `km-c886` and fall
  back to the CB nominal engine near the 60 s cap; `refl1575` was already
  noted as CB-near-cap noise in the `bridge-nn-rule` README) flipped from
  `ok` (30.2 s and 32.2 s) to `TIMEOUT` (60.1 s); when rerun on `km-48a` with
  a 120 s cap (`data/pools/refl-check-48a.tsv`), both time out at 120.1 s on
  `km-48a` as well (`refl352` answers `ok` in 75.4 s on `km-c886`,
  `data/pools/refl-check-c886.tsv`).
- **0 new differences.**

## The 16 held-out inputs (`data/heldout/summary.tsv`, 240 s cap)

| `ore_ont_<n>` | `km-48a` wall (s) | `km-c886` wall (s) | `km-c886` RSS (GiB) | Reference agreement |
|---|---|---|---|---|
| 4903 | 4.81 | 3.53 | 0.18 | konclude=agreement |
| 11647 | 6.96 | 4.24 | 0.24 | konclude=agreement hermit=agreement openllet=agreement |
| 4796 | 4.26 | 0.76 | 0.04 | konclude=agreement openllet=agreement jfact=agreement |
| 3917 | 7.32 | 4.68 | 0.27 | konclude=agreement jfact=consistency_disagreement |
| 11378 | 8.76 | 6.53 | 0.31 | konclude=agreement jfact=consistency_disagreement |
| 12191 | 9.35 | 6.30 | 0.32 | konclude=agreement jfact=consistency_disagreement |
| 9151 | 65.06 | 58.25 | 0.64 | konclude=agreement jfact=consistency_disagreement |
| 9577 | 88.36 | 81.15 | 0.66 | konclude=agreement jfact=consistency_disagreement |
| 6132 | 23.11 | 20.96 | 0.51 | konclude=agreement hermit=agreement |
| 9899 | 27.07 | 24.79 | 0.51 | konclude=agreement hermit=agreement |
| 16315 | 36.23 | 28.69 | 1.33 | konclude=agreement |
| 10838 | 66.55 | 58.96 | 2.37 | konclude=agreement |
| 3087 | 76.38 | 60.74 | 2.49 | konclude=agreement |
| 7557 | 108.87 | 96.97 | 3.74 | konclude=agreement |
| 10926 | >240 (rc=124) | >240 (rc=124) | 18.00 | timeout on both |
| 12128 | 43.90 | 40.48 | 2.20 | konclude=agreement |

All 15 answered inputs agree with Konclude and match `km-48a` output; every
answered input is faster on `km-c886` than on `km-48a`.

## The 112 nominal design-half inputs (`data/nominal/`)

- `inputs 112 both-answered 109 identical 109 differ []`
- `answer-status changes []`
- `time ratio new/base over 26 inputs above 1 s: mean 1.012 median 0.953 max 2.00`
- `route changes []`
- `guard fired (c886): 0`

## Tests (`data/tests/`)

Clean environment (`env -i PATH=$PATH HOME=$HOME KM_THREADS=1`),
`--test-threads=1`:

- Library (`cargo test --release --lib -- --test-threads=1`): 3,115 passed,
  21 failed, 10 ignored. `diff` of `data/tests/lib-failures.txt` against
  `.work/worktrees/fix-bridge-defers/results/agents/2026-11-01/bridge-defers/data/lib-failures.txt`
  is empty (the exact 21 baseline failures).
- Integration targets (`engine/tests/*.rs`, all 73 targets including
  `bridge_nn_rule`, `bridge_nn_term` with 6 fixtures, and
  `completion_hot_path_env`): all 73 targets pass (`rc=0`, 0 failures).
- Newly failing tests: **none**.

## Not done

- Three other callers in `unsat_handler.rs` (around line 355) and `u06.rs`
  (around lines 1724 and 1814) still read a track point from the ctx-less
  label-set stub; they are outside this task's scope and are noted in
  `docs/HYBRID-CB-HT.md` section 24.
- `nn1333` answers in 4.3 to 4.8 s (down from 95 s on `km-48a`, vs 0.5 s on
  `km-base`); the remaining ~4 s is spent in KM's batch refutation probe
  (`1.3 s` with `KM_BRIDGE_NO_BATCH_REFUTATION=1`).
