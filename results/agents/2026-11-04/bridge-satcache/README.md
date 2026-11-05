# bridge-satcache: the satisfiable expander cache in the native bridge

## Status (2026-11-05, continuation by a second agent)

Done by the first agent (commits bf8b6932, 5843d501, 2cba8fbd): the four
absorption/replay fixes and the lifted SELF gate of section 23; the target
reductions and the 14 SELF fixtures 20/20 on both routes; ore_ont_12128 in
agreement with Konclude (three paired 240 s runs); the sibling family (2,000
seeds, 3 runs on the new binary, 1 on the base); the 16 held-out inputs,
paired with the base. Open when the first agent stopped: the 112 nominal
inputs, the differential pools, the test suites, the paired check of the
family timeouts, the results section. `nn1116` is not fixed (NN-rule
functional arm, handed on, see below). The second agent also found that
`tools/pools.sh` still wrote into `bridge-nn-rule`'s scratch directory and
redirected it to this task's scratch before any pool run. The results
section at the end of this file lists what the second agent ran.

## Status (2026-11-05 09:10, third agent)

The second agent stopped after committing the paired family timing and the
held-out pairs (41a2024f); its `campaign-late.sh` had finished the held-out
step and was gone (no process left). The 112 nominal step had written five
rows only (kept as `ore-partial-1` in the scratch directory). Code is
unchanged since 2cba8fbd; `engine/target/release/km` is byte-identical to
`bin/km-new`, and the test binaries were built (00:25) but never run.
Still open at this point: the 112 nominal inputs, the differential pools
(before and after), the library and integration suites, a check that
ore_ont_12128 really exercises the cache now that the SELF gate is lifted,
and the results sections here and in section 23. The third agent runs these
in that order; its results are under "Results" below.

## Status (2026-11-05 16:58, fourth agent)

The third agent ran the test suite (`tests.sh`) on `km-new` (2cba8fbd) and
found two failures: `completion_hot_path_env` (an uncached `std::env::var` in
`satexp_absorb.rs`) and `bridge_reflexive` on `merge1708_min.ofn` when the
section 20 SELF gate is lifted. It traced `merge1708_min`, restored the
section 20 SELF gate on the satisfiable expander cache (`KM_BRIDGE_SELF_SATEXP_NO_GATE=1`
as negative control), moved `KM_HT_SATEXP_ABSORB_LEGACY` to the cached
accessor in `completion/mod.rs`, updated section 23 and `bridge_satcache.rs`,
built `km-final` (commit a7cfc6a1), and started `campaign-final.sh`. That run
completed the full library and integration suites (`tests-final`: 21 baseline
lib failures, all 92 integration targets passing), the 20-run seed/reduction
checks (`red20-final.tsv`, `self20-final.tsv`, `refl20-final.tsv`), and run 1
plus 1,556 of 1,831 `ht_bridge` seeds in runs 2-3 of the sibling family before
stopping. This fourth agent finishes the remaining runs 2-3 of the sibling
family, the paired `ore_ont_12128` and `m53` checks, the 112 nominal ORE
design-half inputs, the differential pools, and the results sections and
hand-back.

Branch `fix/v155-bridge-satcache` from `development/v1.5.5` at 48a1113b,
worktree `.work/worktrees/fix-bridge-satcache`. Scratch:
`.work/agent-scratch/bridge-satcache/`. Release flags for every measurement:
`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`.
Binaries (`.work/agent-scratch/bridge-satcache/bin/`, LTO release builds):
`km-base` = 48a1113b, `km-new` = 2cba8fbd, `km-final` = a7cfc6a1 (2cba8fbd
plus the restored SELF gate and cached legacy-arm accessor). `km-trace` and
`km-fix1` to `km-fix8` are non-LTO diagnostic builds of intermediate states
(used for traces and ablations only, never for a timing).

The argument for every change is in docs/HYBRID-CB-HT.md section 23.

## Gold, checked by hand (section 23 has the full derivations)

- `nn1064min`: `b` has no `p`-successor in `∃p⁻.{a}` (it would have the two
  `p`-predecessors `a ≠ b` under inverse functionality): `Q1 ⊑ Q3`; a model
  with `a` given two such successors refutes every other subsumption.
- `nn1313min`: an `A` element and `a ∉ A` cannot share an `s`-successor
  (inverse functional `s`): `A ⊑ E`; `a` with two `s`-successors refutes the
  rest.
- `nn1348min`: `r` functional and `Q5 ≡ ≤0 r`: an `r`-predecessor of a `Q5`
  element cannot satisfy `∃r.∃r.{b}`: `Q5 ⊑ Q4`; the model
  `r = {(v1,w),(v2,w),(w,b)}` refutes the rest.
- `nn1116`: `c` has at most one `s`-predecessor, so `⊤ ⊑ Q3`.
- `sat1096min` (reduced here): a second element forces two
  `s`-predecessors of `a` and so `a ∉ Q5`; a non-empty `Q5` is the
  one-element model: `Q5 ⊑ Q4`, `Q5 ⊑ Q2`, and `Q4 ⊑ Q2`.
- `sat578` (family miss, not a cache defect): a non-empty `F` forces
  `c = a` (`F ⊑ {c}`, `F ⊑ ∃p⁻.(≤1 p⁻ ⊓ ∃p.{a})` with functional `p`), then
  every element lies in `Q2 ≡ ≤1 s⁻.(∃s.{a})` (`c` has at most one
  `s`-predecessor), so every element other than `c` is an `r`-predecessor of
  `c` (the other definition of `Q2`), and inverse functional `r` leaves one
  element: `F ⊑ Q1`, `F ⊑ Q4` hold, as HermiT says.
- Every answer above is HermiT 1.4's (`.work/agent-scratch/bridge-satcache/gold/`,
  `famgold/`); the fixed bridge agrees on each except `nn1116` and `sat578`.

## The wrong entries and their causes

`KM_HT_SATEXP_TRACE=1` (new) prints the cache's writes, satisfiable hits
(node and ancestor), replays, expansion writes and the rules taken from a
node's queue; `KM_SAT_ABSORB_DEBUG=1` the generating absorption test.
Traces under `data/traces/`.

In every case the cache entry is correct (a node with that label is
satisfiable, or the expansion is a deterministic consequence of its prefix);
what is wrong is the use the port makes of it on the cached node:

1. `nn1348min`: the entry `{⊤, ≤1 r.⊤, ∃r.∃r.{b}}` (satisfiable, no branched
   concept), written in the probe of `E`, is hit by the `r⁻`-successors of
   the `Q5 ⊓ ¬Q4` root; the cached node absorbs `∃r.∃r.{b}` (its reapply
   queue holds no at-most yet: the bridge's `≤1 r.⊤` keeps its `⊤` operand,
   which Konclude's builder drops, so it is popped after the existential) and
   then absorbs `≤1 r.⊤`. Nothing is merged into the root.
2. `nn1064min`, `nn1313min`: the cached successor absorbs its functional
   `≤1 p⁻` / `≤1 s⁻` (Konclude's `applyFUNCTIONALRule` is never absorbed) and
   the existential (`∃p⁻.{a}` is Konclude's VALUE shortcut, never absorbed).
3. `sat1096` (family): once `∃s.{a}` is not absorbed, its successor inherits
   `PRF_ANCESTORSATISFIABLECACHED` and is never processed, so it never merges
   into `a`; Konclude links the node to `a` directly.
4. `m53tiny` (the ore_ont_12128 reduction of section 20): an expansion entry
   was written while `GO_0003674 ⊑ Function` was still queued (the bridge runs
   without direct rule preprocessing); the replay skips the AND rule
   (`addConceptToIndividualSkipANDProcessing`), so `Function` never arrives
   and the clash with `Continuant ⊑ ¬Function` is lost. This is the wrong
   entry behind the SELF gate of section 20; it has nothing to do with self
   edges (the SELF and at-most concepts on `⊤` only shift the queue order).

## The fix (`engine/src/konclude_ht/completion/satexp_absorb.rs`)

- a `≤1 R` without qualifier or with `⊤` is never absorbed on a cached node
  (`u08.rs` `apply_atmost_rule`);
- the existential absorption test also reads the label for an at-most on the
  role to the ancestor (`u22.rs`);
- `∃R.{a}` is never absorbed, and its successor does not inherit the
  cached-ancestor blocks (`u08.rs` `apply_some_rule`);
- replayed expansion concepts are queued without the AND skip (`u21.rs`,
  `u04.rs` `add_concept_to_individual_with_skip_function`);
- the section 20 SELF gate stays on all three caches (`bridge.rs`): lifting it
  from the satisfiable expander cache broke `bridge_reflexive/merge1708_min.ofn`
  (a successor hits a satisfiable entry whose model built a `p` self edge,
  absorbs `B ⊔ ≥2 s⁻`, and never builds the self edge that would merge it into
  its ancestor under `≤1 p⁻`; Konclude's `isSatisfiableCachedCompatible` has no
  SELF case).

Each change only refuses a deferral or adds a rule application.
`KM_HT_SATEXP_ABSORB_LEGACY=1` (or `functional`, `top`, `label`, `value`,
`replay`) restores the former behaviour; `KM_BRIDGE_SELF_SATEXP_NO_GATE=1`
lifts the SELF gate from the satisfiable expander cache (negative control). A
first version also built `≤n R.⊤` without its operand, as Konclude does; it
fixed `nn1116` but made the NN-rule's functional arm run on those bounds, and
five family seeds stopped finishing (`sat346`, `sat181`, `sat1094`, `sat1496`,
`sat1836`; base 0.5 to 12 s). It was dropped.

## Commits (branch `fix/v155-bridge-satcache`, not pushed, not merged)

- `bf8b6932` fix(bridge): Konclude's satisfiable-cached absorption gates for functional at-most, nominal VALUE shortcut and top fillers
- `5843d501` fix(bridge): replay satisfiable-expander entries without the AND skip; lift the SELF gate from the satisfiable expander cache
- `2cba8fbd` fix(bridge): order-independent existential absorption test, top-qualified functional at-most, unblocked VALUE successors; keep the bridge's at-most representation
- `41a2024f` results(bridge-satcache): status note, held-out pairs, paired family timing; pools.sh writes to this task's scratch
- `69f667bf` results(bridge-satcache): third-agent status note; tests.sh
- `a7cfc6a1` fix(bridge): keep the section 20 SELF gate on the satisfiable expander cache; cached legacy-arm accessor
- final commit: section 23 results, README and validation data

## Results

### Target seeds, reductions and fixtures (20 runs, both routes)

`data/seeds20/red20-final.tsv`, `self20-final.tsv`, `refl20-final.tsv` (`km-final`, `ht_bridge` and automatic, 20 runs each):

- `nn1064`, `nn1064min`, `nn1313`, `nn1313min`, `nn1348`, `nn1348min`, `sat1096`, `sat1096min`, `m53tiny`: 20 of 20 agree with HermiT on both routes (360 of 360 runs). Base (`data/seeds20/red1-base.tsv`): the first eight are wrong on both routes (`nn1064`/`nn1064min` missing `Q1 ⊑ Q3`, `nn1313`/`nn1313min` missing `A ⊑ E`, `nn1348`/`nn1348min` missing `Q5 ⊑ Q4`, `sat1096`/`sat1096min` missing `Q4 ⊑ Q2`, `Q5 ⊑ Q2`, `Q5 ⊑ Q4`).
- Under `KM_BRIDGE_SAT_REFUSE_SELF=1` (completion only, SELF gate off, satisfiable expander cache installed), `m53tiny` and `m53` (the 1,165-axiom module of `ore_ont_12128`) are wrong on the base on both routes (`m53`: 28 of 40 unsatisfiable classes, 3,141 subsumptions) and exact on `km-final` on both routes (`m53`: all 40 unsatisfiable classes, 3,117 subsumptions; `m53tiny` pinned in `engine/tests/bridge_satcache.rs`).
- `nn1116`: wrong in 20 of 20 runs on both routes, as on the base (missing `X ⊑ Q3`; not a cache defect, see section 23).
- All 14 SELF fixtures (`data/seeds20/self20-final.tsv`, 560 runs) and all 7 `bridge_reflexive` fixtures (`data/seeds20/refl20-final.tsv`, 280 runs, including `merge1708_min`): 20 of 20 agree with HermiT on both routes.

### Sibling family (2,000 seeds, HermiT gold, three runs per seed and route)

Generator `tools/gen_sat.py` (functional and inverse-functional roles and inverses, `≤n R.⊤` and qualified `≤n R.C`, `∃R.{a}` and `∃R.∃S.{a}`, nominals, `DifferentIndividuals`, role equivalences and inverses). Gold `famgold/` (HermiT 1.4, 30 s cap): 1,883 of 2,000 (117 HermiT timeouts, `NOGOLD`). Runner `tools/fam_run.py`, 30 s automatic, 20 s `ht_bridge`. Data `data/family/` (`final1.tsv`, `final23-ht_bridge.tsv`, `final23-auto.tsv`, `base.tsv`, `final-summary.txt`, `paired-slow.tsv`).

| route | `km-final`, 3 runs | `km-base`, 1 run (2,000 rows per route) |
|---|---|---|
| automatic | 5,485 ok, **3 WRONG (1 seed)**, 55 TIMEOUT, 117 NOGOLD | 1,823 ok, **6 WRONG (6 seeds)**, 54 TIMEOUT, 117 NOGOLD |
| `ht_bridge` | 5,469 ok, **3 WRONG (1 seed)**, 52 TIMEOUT, 21 NOANSWER, 117 NOGOLD | 1,818 ok, **6 WRONG (6 seeds)**, 52 TIMEOUT, 7 NOANSWER, 117 NOGOLD |

(Runs 2 and 3 execute on every seed-route that answered in run 1, so `NOGOLD` and run-1 `TIMEOUT` appear once in the 3-run totals, while `NOANSWER` and `WRONG` appear three times.)

- 5 of the 6 wrong base seeds (10 of 12 wrong seed-routes: `sat1090`, `sat1096`, `sat1711`, `sat311`, `sat462`, both routes) are cache defects and agree with HermiT in 3 of 3 runs on both routes on `km-final`. No seed-route is wrong on `km-final` that was right on the base.
- The single remaining wrong seed is `sat578` (3 of 3 on both routes, missing `F ⊑ Q1`, `F ⊑ Q4`, identical on the base). It is wrong with `KM_HT_NO_SAT_EXP_CACHE=1` and `KM_HT_NO_SATURATION=1` as well, so it is not a satisfiable-expander-cache defect.
- The 7 `NOANSWER` seeds on `ht_bridge` (`sat1508`, `sat1544`, `sat1787`: inverse role meets a negative existential mirror; `sat21`, `sat335`, `sat711`, `sat798`: encoder defer) are identical on the base.
- Timeouts against the base (`data/family/paired-slow.tsv`, `tools/paired_time.py`, 3 paired runs per route): `sat1864` had 1 ok and 2 timeouts on `auto` in `final23-auto.tsv` under host load, and in paired runs answers in 0.01 s (`ht_bridge`) and 0.01 to 0.02 s (`auto`) on both `km-base` and `km-final`. Earlier unpaired timeouts `sat550` (13.0 to 13.6 s base vs 13.4 to 14.2 s new on `ht_bridge`; 21.1 to 21.3 s vs 21.3 to 21.6 s on `auto`) and `sat1363` (18.7 to 20.5 s vs 19.2 to 19.7 s on `ht_bridge`; 26.4 to 27.4 s vs 26.9 to 28.5 s on `auto`), along with `sat346`, `sat749` and `sat440`, have identical paired times on base and new.

### Differential pools (24 gold-backed pools, both routes, 60 s cap)

`tools/pools.sh`, `data/pools/` (`after/` on `km-final`, 19,821 seeds, 39,642 runs; `before/` on `km-base` over all 1,546 seeds not `ok` on some route after the fix plus the recovered seeds, reusing the byte-identical `km-base` runs from `bridge-nn-rule/data/pools/after/` for unchanged earlier pools and running `km-base` directly on `nonok-run.list`):

- `after` (`km-final`): 37,937 ok (19,662 `auto`, 18,275 `ht_bridge`), 1,492 `ERR` (4 `auto`, 1,488 forced-route refusals), 193 `TIMEOUT` (138 `auto`, 55 `ht_bridge`), 20 `WRONG` (17 `auto`, 3 `ht_bridge`).
- The 20 `WRONG` rows are all pre-existing on `km-base`:
  - 14 `auto` rows on the data-value seeds (`bridge-self-pools-res-data-values-3`: 6; `bridge-self-pools-res-lean-data-values`: 1; `bridge-m413-respool`: 7);
  - 4 rows (both routes) on `nn1116` (`bridge-nn-rule-fam` and `bridge-satcache-red`);
  - 2 rows (both routes) on `nn5` (`bridge-nn-rule-fam`, the HermiT error of section 22).
- Improvements from `before` (`km-base`) to `after` (`km-final`):
  - `bridge-nn-rule-fam`: `nn1064`, `nn1313` and `nn1348` move from `WRONG` to `ok` on both routes (6 seed-routes); `nn1811` moves from `WRONG` at 37.1 s (`ht_bridge`) and 54.9 s (`auto`) to `TIMEOUT` at 60 s on both routes (`km-base` with `KM_HT_NO_SAT_EXP_CACHE=1` also times out on `ht_bridge` instead of returning the wrong answer).
  - `bridge-satcache-red`: `nn1064`, `nn1064min`, `nn1313`, `nn1313min`, `nn1348`, `nn1348min`, `sat1096`, `sat1096min` move from `WRONG` to `ok` on both routes (16 seed-routes).
- Across all 20 pre-existing pools (35,594 seed-routes), every verdict is identical to `km-base` except two `auto` 60 s cap flips on `bridge-reflexive-fam` (`refl1575` and `refl352`). **0 new wrong answers.**

### The 16 held-out ORE inputs (240 s, paired)

`tools/heldout_pair.sh`, `data/heldout/summary.tsv`: all 15 inputs that answer on the base keep their exact reference verdicts (`compare_ref.py`: `agreement` with Konclude on all 15; `10926` times out at 240 s / 18.0 GiB on both).

- `ore_ont_12128` (240 s, four paired runs: three with `km-new`, one `final-base` / `final-new` with `km-final`): all eight runs agree with Konclude (4,716 unsatisfiable classes). Wall `km-base` / `km-final`: 38.7 s / 37.0 s (2.20 GiB RSS on both); earlier three pairs: 40.4 / 38.2 s, 38.9 / 37.7 s, 37.5 / 38.5 s, and 40.8 / 40.9 s in the full sweep.
- Paired wall times `pair-base` / `pair-new` (s) on the other 14 answering inputs: `4903` 6.6/6.1, `11647` 8.1/8.8, `4796` 3.9/4.9, `3917` 8.1/7.3, `11378` 18.3/8.0, `12191` 17.7/17.0, `9151` 103.3/98.6, `9577` 129.7/133.9, `6132` 44.4/44.4, `9899` 47.3/36.8, `16315` 36.8/37.7, `10838` 67.4/69.3, `3087` 70.7/70.8, `7557` 98.0/98.5. No time regression beyond noise.

### The 112 nominal ORE design-half inputs (300 s, paired)

`tools/ore_nominal_pair.sh` (`km-base` and `km-final` run simultaneously per input), `data/nominal/pair.txt`:

- 109 of 112 answered by both (`ore_ont_1833` and `ore_ont_2548` time out on both; `ore_ont_8250` is refused on both).
- **109 of 109 identical signatures**, 0 answer-status changes, 0 route changes, coverage guard fired 0 times.
- Time ratio `km-final` / `km-base` over the 26 inputs above 1 s: **mean 1.001, median 0.997, max 1.17**.

### Tests (`km-final`, clean environment, `KM_THREADS=1`, `--test-threads=1`)

`tools/tests.sh`, `data/tests/`:

- `cargo test --release --lib -- --test-threads=1`: 3,115 passed, 21 failed, 10 ignored (`data/tests/lib-failures.txt`), matching the 21 baseline checker-bound failures of `.work/worktrees/fix-bridge-defers/results/agents/2026-11-01/bridge-defers/data/lib-failures.txt` with 0 newly failing tests.
- Every integration target in `engine/tests/*.rs` (92 targets, `data/tests/summary.txt`): **92 of 92 passed**, including `bridge_satcache` (6 tests), `bridge_self`, `bridge_reflexive`, `bridge_nn_rule`, `completion_hot_path_env`, `empty_and_universal_data_ranges` and `source_incremental_rules`.
- Newly failing tests: **none**.

## Not done

- `nn1116` (not a cache defect: `⊤`-qualified `≤1 s⁻.⊤` takes the NN-rule's general arm instead of its functional arm; dropping the `⊤` operand fixes `nn1116` but makes five family seeds time out in the NN-rule's functional arm; handed to `fix/v155-bridge-nn-term`).
- `sat578` (family miss, not a cache defect: fails identically on the base and with `KM_HT_NO_SAT_EXP_CACHE=1`).
- The section 20 SELF gate stays on the satisfiable expander cache (`merge1708_min` shows that `isSatisfiableCachedCompatible` needs a SELF compatibility check before the gate can be lifted).
- `engine/target` and `engine/target-fast` deleted at the end; the worktree is kept.
