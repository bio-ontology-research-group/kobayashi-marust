# bridge-nn-rule: Konclude's NN-rule in the native bridge

Branch `fix/v155-bridge-nn-rule` from `development/v1.5.5` at 1ffee4a6,
worktree `.work/worktrees/fix-bridge-nn-rule`. Scratch:
`.work/agent-scratch/bridge-nn-rule/`. Release flags for every measurement:
`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`.
Binaries (`.work/agent-scratch/bridge-nn-rule/bin/`): `km-base` = 1ffee4a6,
`km-new` = `km-v7` = the code of ca64efb1 (later commits change docs,
results and tests only). Every "new" number below is `km-new`.

The argument for every change is in docs/HYBRID-CB-HT.md section 22.

## Gold

- `f1008` (`≤1 s.(∃p.{c}) ⊑ C`, `InverseFunctional(p)`): two `s`-successors
  of any element in `∃p.{c}` are `p`-predecessors of `c`, so they are equal;
  `⊤ ⊑ C`. HermiT's eight `X ⊑ C` are all the subsumptions (with every role
  empty and `C = Δ` the other classes are free).
- `f439`: for `x ∈ Q2 = {c} ⊓ ≤1 r` the only `r`-successor of `c` is `c`
  (reflexive `r`); every `E` element `e` has an `r`-predecessor `y` with
  `∀r⁻.{c}`, so `y = c` (its own predecessor) and `e = c`; two
  `s`-predecessors of `c` in `∃p.E` are then `p`-predecessors of `c` and
  equal. `Q2 ⊑ Q5`, and two small models (section 22) refute every other
  subsumption: HermiT's single answer.
- `nn1018min` (found by the family, three axioms): `Q1 ≡ ≥3 p⁻.(F ⊓ ∃r.{c})`,
  `⊤ ⊑ ≤1 r⁻`, `r(b,b)`. `c` has at most one `r`-predecessor, so `Q1` is
  unsatisfiable; `{b}` with `r(b,b)` and `c` without predecessors is a model.
  HermiT agrees.
- Konclude 0.7.0 does not finish within 30 s on these inputs (precomputation).
- The CB engine (`--route nominals`, the exact nominal CB stack) answers
  `f1008` and `f439` as HermiT (`data/cb/base-nominal-routes.tsv`). The plain
  CB routes (`cb_plain1`, `cb_absorb1`, `cb_trigger1`, `cb_plain16`,
  `production_all`) refuse inputs with nominals ("drops 1 nominal; the
  answer would be approximate"); `nominal_ni_abox` and
  `certified_card_proxy_abox` answer right; `certified_card_nominals` and
  `certified_nominals` run the bridge and were wrong on the base.

## Cause

`f1008` (graph dump, `data/traces/f1008-base-graph.txt`): in the `¬C` probe
the second `s`-successor is DIRECTBLOCKED by its sibling, whose
`p`-successor merged into `c`. `≤1 p⁻` holds at `c` (one neighbour), and the
blocked copy would be a second `p`-predecessor of `c`. Konclude's NN-rule
turns that blockable neighbour of the nominal into a nominal, which can
neither block nor be blocked; the port had it as W3-DEFER. `f439` is the
same twice (`≤1 r` at `c` over `e`, then `≤1 p⁻` at `c` over the blocked
`s⁻`-neighbour; `data/traces/f439-nn.txt`).

## What was ported (cpp = `~/konclude-build/.../CCalculationTableauCompletionTaskHandleAlgorithm.cpp`)

`completion/u08.rs` `ht_apply_nn_rule`, at the head of each iteration of the
production at-most loop (`ht_apply_atmost_merge`; also every merge
alternative):

1. Functional arm, unqualified `≤1 R` at a nominal: `applyFUNCTIONALRule`'s
   NN pre-scan (cpp 14756-14777, `requiresNNRule` when an `R`-link was created
   by another node, first nominal successor as target),
   `createNominalsSuccessorIndividuals(…, 1)` (cpp 14780-14789, 22314-22331;
   `u16.rs` port now returns the created node), deterministic merges into the
   target under `createFUNCTIONALDependency` with `getMergedIndividualNodes`'
   direction (cpp 14812-14857, 20993-21038), and the functional clash (cpp
   14858-14863). Applied only when a blockable successor exists.
2. General arm, every other at-most at a nominal: `fixedNominalMerging`
   (`isCandidateBlockableAndCreator`, cpp 15201) and the lazy new
   representatives (`LazyNewMergingNominalCreation`, cpp 15231-15233,
   15335-15470): blockable qualified candidates move into fresh nominals by
   `getIntoEmptyMergedIndividualNode(candidate, true, x)` (cpp 21047-21063),
   at most `cardinality` minus the qualified nominal neighbours; the new node
   inherits the candidate's creation dependency (merge phase 7, cpp
   21440-21442); the probe root is never moved (Konclude's constructed node
   is never merged away, cpp 21003-21006). At-most pairs of a blockable node
   and a nominal merge into the nominal (`ht_orient_nominal_merge_pair`).
3. `u36.rs` `native_cardinality_critical_roles`: a cached ABox nominal of the
   precomputation replay with a cached at-most on `R` and a live `R`-link to a
   blockable neighbour it did not create is cardinality critical, so its
   backend blocks are released and its at-most (with the NN-rule) runs
   (`nn1018`). Not a Konclude condition; releasing a block is exact (18.1).

`KM_HT_NO_NN_RULE=1` turns all three off (negative control), `KM_HT_NN_TRACE=1`
prints each application. The opt-in `KM_HT_ATMOST_REST` path keeps the NN
halves W3-DEFER.

## Commits (branch `fix/v155-bridge-nn-rule`, not pushed, not merged)

- 2cbd14aa fix(bridge): port Konclude's NN-rule for nominals under at-most restrictions
- d4f24782 fix(bridge): NN-rule guards, conversion dependency, regression tests, section 22 draft
- b9864b9a fix(bridge): a cached nominal with an NN-rule candidate link is cardinality critical
- ca64efb1 fix(bridge): bound the NN-rule's new nominals by the at-most slots
- final commit: docs, README, data

## The reductions and seeds, 20 runs, both routes

`data/seeds20/new-20runs.tsv`: `f1008`, `f439`, `refl1008`, `refl439`,
`nn1018`, `nn1018min`, `hang606`, `ht_bridge` and automatic, 20 runs each:
280 of 280 agree with HermiT. Base (`data/seeds20/base-1run-all-routes.tsv`):
`f1008`, `f439`, `refl1008`, `refl439` wrong on both routes; `nn1018` wrong on
both routes (family base run).

## Sibling family (2,000 seeds, HermiT gold, three runs per seed and route)

Generator `tools/gen_nn.py` (nominals under at-most and functional
restrictions, inverse-functional and functional roles and their inverses,
`≥n s.∃p.{c}` / `≤n s.∃p.{c}`, `{c} ⊓ ≤n r`, `∃r⁻.∀r⁻.{c}`, at-most class
assertions on individuals, role assertions, `DifferentIndividuals`,
reflexive roles in 35 %). Gold `tools/gold_batch.sh` (HermiT 1.4, one seed
per JVM, 30 s cap): 1,993 of 2,000 (7 HermiT timeouts, NOGOLD below).
Runner `tools/fam_run.py`, 60 s automatic, 30 s `ht_bridge`. Data
`data/family/` (gold in `gold.tgz`).

| route | new, 3 runs (6,000 rows per route) | base, 1 run (2,000 rows per route) |
|---|---|---|
| automatic | 5,901 ok, **16 WRONG (6 seeds)**, 62 TIMEOUT, 21 NOGOLD | 1,739 ok, **249 WRONG**, 5 TIMEOUT, 7 NOGOLD |
| `ht_bridge` | 5,875 ok, **15 WRONG (5 seeds)**, 83 TIMEOUT, 6 NOANSWER, 21 NOGOLD | 1,731 ok, **250 WRONG**, 10 TIMEOUT, 2 NOANSWER, 7 NOGOLD |

- 464 of the 499 wrong base seed-routes (234 seeds) agree with HermiT in all
  three new runs. No seed-route is wrong on the new binary that was right on
  the base.
- Every miss on the new binary (all wrong on the base as well,
  `data/family-misses/`):
  - `nn1064`, `nn1313`, `nn1348` (both routes, 3 of 3): reductions
    `nn1064min` (5 axioms), `nn1313min` (4), `nn1348min` (4). All three answer
    as HermiT with `KM_HT_NO_SAT_EXP_CACHE=1`, `KM_BRIDGE_FRESH_ENV=1` or
    `KM_HT_NO_SATURATION=1`, not with `KM_HT_NO_NN_RULE`: a satisfiable-expander
    cache entry reused next to nominals (the writer excludes nodes flagged
    `PRF_SUCCESSORNOMINALCONNECTION`; the entry that goes wrong was not
    isolated). Hand check of `nn1064min`: `Q1 ⊆ {b}`, `b ≠ a`, `p`
    inverse functional and `r = p⁻`, so no element is a `p`-successor of both
    `a` and `b`, and `b ∈ Q3 = ≤1 r⁻.(∃r.{a})`: `Q1 ⊑ Q3` holds.
  - `nn1116` (both routes, 3 of 3): not reduced.
  - `nn5` (both routes): HermiT says `B` unsatisfiable; the bridge says
    satisfiable. The reduction `nn5min` (4 axioms, HermiT still `B`
    unsatisfiable, `nn5min.hermit.json`) has a model in which `B` is not
    empty, checked mechanically: domain `{a, b, y, z1, z2, z3}`,
    `r = {(z1,b), (z2,b), (z3,b)}`, `p = {(b,a)}`, `s = {(y,b)}`, `B = {b}`,
    `Q1 = Δ`. HermiT's answer is wrong here; the bridge is right.
  - `nn1811` (automatic route only, 1 of 3 runs wrong, 2 timeouts; base
    times out): the HT worker hits the 18 GiB memcap at 28 s (base too), and
    the answer comes from the nominal CB stack of the `certified_nominals`
    portfolio, missing `A ⊑ Q1`, `A ⊑ Q4`. **A CB-engine miss, not bridge
    work; not investigated further (another task).** The forced `nominals`
    route exceeds its RSS limit.
  - NOANSWER: `nn1570` ("ABox conversion was incomplete"), `nn1962`
    (encoder defer), forced route only, as on the base.
- Slower than the base (base answered, new times out in all three runs):
  `nn1333` (base 0.5 s, both routes), `nn346` (0.02 s, both routes), `nn952`
  (0.02 s, `ht_bridge`; automatic answers through the CB stack), `nn745`
  (0.06 s, `ht_bridge`), `nn1957` (28 s, both), `nn777` (38 s automatic),
  `nn969` (28 s `ht_bridge`, 1 of 3 new runs ok). On these the NN-rule turns
  candidates into nominals and the at-most branching then searches over
  merges of nominals (trace of `hang952`: two at-most restrictions at the
  reflexive nominal `b` convert and merge the same candidate in alternation
  under backtracking); I did not find whether the search is infinite or only
  exponential. The first version of the branch (every candidate converted)
  did not terminate on 12 such seed-routes; the slot bound and the merge
  direction recovered six of them (`nn606`, `nn676`, `nn742`, `nn786`,
  `nn82`, `nn939`).

## Differential pools (gold-backed seeds of earlier agents), both routes

`tools/pools.sh` (the previous agent's 15,789 seeds plus the bridge-reflexive
family and its seeds20: 17,797 seeds, 35,594 runs, 60 s, two KM processes):

- New (`data/pools/after/summary.txt`): 33,942 ok, 1,486 ERR (forced-route
  refusals), 152 TIMEOUT, 14 WRONG. The 14 WRONG rows are the pre-existing
  data-value seeds of res-data-values-3 (6), res-lean-data-values (1) and
  their copies in the m413 residue pool (7), automatic route, the same as on
  the base and in the previous two agents' runs. The bridge-reflexive
  family, which had refl1008 and refl439 wrong, is now 0 wrong.
- Base on every seed that was not ok after the fix on some route (3,038
  runs, `data/pools/before/`): every verdict identical except three automatic
  ok/TIMEOUT flips on the reflexive family (refl1477 and refl651 ok on the
  base, timeout on the new run; refl1575 the reverse), the CB-near-cap seeds
  the previous agent already recorded as cap noise. **0 new differences.**

## The 16 held-out inputs (240 s, two at a time)

`data/heldout/summary.tsv`: identical output on all 15 that answer (10926
times out on both at 18 GiB), every reference verdict unchanged. Wall base /
new (s): 3087 59.3/57.7, 3917 4.2/4.2, 4796 3.0/2.8, 4903 3.5/3.4,
6132 16.4/18.3, 7557 87.8/81.3, 9151 54.2/53.9, 9577 65.1/62.7,
9899 17.8/20.4, 10838 56.9/47.7, 11378 6.1/5.5, 11647 4.1/4.0,
12128 35.6/34.0, 12191 6.3/5.7, 16315 22.1/20.6. No slowdown beyond noise
(largest 9899 +15 %, 6132 +12 %; 7557 RSS 3.74 to 3.18 GiB).

## The 112 nominal ORE design-half inputs (one at a time, 300 s)

`data/nominal/pair.txt`: 109 answered by both, 109 identical signatures, 0
answer-status changes, 0 route changes, coverage guard fired 0 times; time
ratio new/base over the 26 inputs above 1 s: mean 0.956, median 0.975, max
1.03 (largest: ore_ont_9662 2.4/2.4 s, ore_ont_699 4.7/4.8 s, ore_ont_16666
2.4/2.5 s). 1833 and 2548 time out on both, 8250 is refused on both.

## Tests (code of ca64efb1, clean environment, `KM_THREADS=1`, `--test-threads=1`)

`tools/tests.sh`, `data/tests/`. Library: 3,115 passed, 21 failed, 10
ignored, exactly the 21 checker-bound baseline failures (20 `tableau::` tests
and `cli::cb_derivation_candidate_tests::source_exact_taxonomy_uses_real_production_traces_and_models`).
Integration: 90 of the 91 targets passed in the suite run, including the new
`bridge_nn_rule` and `empty_and_universal_data_ranges`. `source_incremental_rules`
failed three tests in the suite run
(`incremental_rule_probe_matches_the_batch_checker_on_graph_rules`,
`rules_route_retains_taxonomy_across_abox_clash_and_retraction`,
`source_session_migrates_el_rules_el_and_rolls_back_a_declined_revision`)
with "could not start the rules-consistency thread with a 4160 MiB stack
after 10 attempt(s): Resource temporarily unavailable (os error 11)" while
the host load average was near 60 (strict overcommit); rerun alone on the
same build, all four tests passed. No other failing test.

New regression target `engine/tests/bridge_nn_rule.rs`: `f1008`, `f439`,
`nn1018min` with HermiT answers, automatic route and `ht_bridge` three runs
each, and a negative control that each fixture is wrong with
`KM_HT_NO_NN_RULE=1` on `ht_bridge`.

## Not done

- The family misses above: three satisfiable-expander-cache misses next to
  nominals (`nn1064`, `nn1313`, `nn1348`, reduced), `nn1116` (not reduced),
  `nn1811` (CB stack), all present on the base.
- The seven slower family seeds; the general arm is not shown to terminate
  (argued by analogy with SROIQ).
- The general arm moves candidates in scan order instead of Konclude's per
  candidate branch; the opt-in `KM_HT_ATMOST_REST` path has no NN-rule.
- No machine reference besides HermiT; Konclude 0.7.0 does not finish on the
  reductions. The bridge has no Lean model; the changes are argued, not
  proved.
- `engine/target` deleted at the end; the worktree is kept.
