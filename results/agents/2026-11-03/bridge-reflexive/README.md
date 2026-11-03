# bridge-reflexive: reflexive roles next to functional roles in the native Konclude bridge

Branch `fix/v155-bridge-reflexive` from `development/v1.5.5` at acf6df9a,
worktree `.work/worktrees/fix-bridge-reflexive`. Scratch:
`.work/agent-scratch/bridge-reflexive/`. Release flags for every
measurement: `KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`.
Binaries (`.work/agent-scratch/bridge-reflexive/bin/`): `km-base` = acf6df9a,
`km-v1` = fix 1 only, `km-v2` = fixes 1 and 2, `km-v3` = all three fixes
(the code of f7e67fad; later commits change comments, docs and results
only). Every "new" number below is `km-v3`.

The argument for every change is in docs/HYBRID-CB-HT.md section 21.

## Gold

Konclude 0.7.0 (`~/konclude-build/Release/Konclude`) does not finish on the
seeds nor on the four-axiom reductions within 30 s (precomputation), and
Openllet and JFact are not installed on ws, so the HermiT 1.4 answers were
checked by hand (section 21, "Gold"):

- `min1722`: `r = p⁻` is reflexive (from `p`) and functional (from
  `InverseFunctional(p)`), so `r` lies inside the identity; every element has
  exactly one `r`-predecessor and falls under `B` (`≤1 r⁻ ⊑ B`), and
  `B ⊑ ≥3 r` contradicts functionality. Inconsistent, as HermiT says.
- `min526`: `r` reflexive and inverse functional puts `r` (and `p = r⁻`)
  inside the identity: from `r(x,y)` and `r(y,y)`, inverse functionality
  gives `x = y`. So `∀p.Self(p)` and `≤1 p⁻` hold everywhere and
  `Q3 ≡ ⊤`; `F ⊑ ∃r.(C ⊓ Self(p))` gives `F ⊑ C`, `E ⊑ ∀p.F` gives
  `E ⊑ F`. These are HermiT's 11 subsumptions; the one-element model with
  every class true shows consistency.
- The three new reductions (`merge1322_min`, `merge1585_min`,
  `merge1708_min`) are proved in section 21.2 and 21.3.

## Cause and fix: three defects, all in the bridge's completion

1. **At-least rule** (`completion/u08.rs`, `apply_atleast_rule`): the port
   skipped `≥n R.C` when the node had `n` qualified `R`-neighbours, distinct
   or not; Konclude (cpp 16145, `hasDistinctRoleSuccessorConcepts`) counts
   only neighbours the distinct hash separates. A reflexive role makes the
   node its own neighbour, so `≥2 r⁻` was met by the node and one `∃r⁻`
   successor, which the functional `r` then merged into the node. Fix: skip
   only when `n` qualified neighbours are pairwise distinct (the SROIQ
   `≥`-rule condition; stricter than Konclude's star test, so only more rule
   applications). Fixes `min1722`, `min526`, merge526, merge1722.
2. **Optimized blocking** (`completion/u19.rs`,
   `is_label_concept_optimized_blocking`, B3/B5, cpp 18635–18705): the count
   of the blocker's `R`-neighbours against `≤n R.C` ignored the blocker's
   self link, but the copy of the blocker that replaces the blocked node in
   the model keeps its self edges. Fix: the self link counts
   (`KM-SOUNDNESS-GATE[self-blocker]`); this only refuses blocks. Fixes
   merge1322, merge1708.
3. **Saturation caching without saturated expansion** (`bridge.rs`, the
   section 20 SELF gate): section 20 turned off the expansion of created
   successors from saturated labels for SELF terminologies but kept caching
   them against saturation nodes; a cached successor without the copied
   label sends nothing back to its predecessor. Fix: both options go off
   together (Konclude's completion with both optimisations off). Fixes
   merge1585. ore_ont_12128 (the input the SELF gate exists for): 36.1 s with
   the caching, 35.9 s without.

## Commits (branch `fix/v155-bridge-reflexive`, not pushed, not merged)

- 3924c899 fix(bridge): at-least rule counts only pairwise distinct successors
- f7e67fad fix(bridge): count the blocker's self link; no saturation caching without expansion
  (adds `engine/tests/bridge_reflexive.rs` and its seven fixtures)
- 9f627d77 docs(hybrid): section 21, the three reflexive-role bridge defects; campaign tools
- final commit: README, data, doc results

## The five seeds and the reductions, 20 runs, both routes

`data/seeds20/final.tsv`: merge526, merge1322, merge1585, merge1708,
merge1722, `min1722`, `min526` and the three new reductions
(`r1322`, `r1585`, `r1708`), `ht_bridge` and automatic, 20 runs each: 400 of
400 agree with HermiT. Base: every one of them wrong on both routes
(`data/seeds20/base1.tsv`); with fix 1 alone merge1322, merge1585 and
merge1708 stayed wrong 20 of 20 (`data/seeds20/v1.tsv`).

## Sibling family (2,000 seeds, HermiT gold, three runs per seed)

Generator `tools/gen_reflexive.py` (reflexive, irreflexive, functional and
inverse-functional roles and their inverses, `ObjectHasSelf` and its
complement, at-least and at-most restrictions on a role and its inverse,
`≤n R⁻ ⊑ B` / `B ⊑ ≥m R` cores in the shape of `min1722`,
`∀R.Self(R) ⊓ ≤1 R⁻` definitions in the shape of `min526`, nominals in 25 %
of the seeds). Gold `tools/gold_batch.sh` (1,998 of 2,000; two HermiT
timeouts). Runner `tools/fam_run.py`, 60 s automatic, 30 s `ht_bridge`.
Data `data/family/` (`v3-all.tsv` = three runs of `km-v3`, `base-1.tsv` =
one run of `km-base`).

| route | new, 3 runs (5,994 rows) | base, 1 run (1,998 rows) |
|---|---|---|
| automatic | 5,939 ok, 49 timeout, **6 wrong (2 seeds × 3)** | 1,954 ok, 19 timeout, **25 wrong** |
| `ht_bridge` | 5,886 ok, 72 timeout, 30 refused, **6 wrong (2 seeds × 3)** | 1,935 ok, 28 timeout, 10 refused, **25 wrong** |

Base against new: 46 seed-routes wrong on the base are right in all three
new runs, 7 base timeouts answer in all three. No seed changed its answer
between runs; the only run-to-run differences are ok/timeout on the
automatic route for four seeds whose bridge times out on both binaries and
whose CB answer lands near the 60 s cap (refl1250, refl1477, refl352,
refl651, 30 to 40 s when they answer). Two of those (refl1250, refl1477)
answered in the single base run and timed out in one or two of the three new
runs; see "Borderline timeouts" below.

### Every miss: two seeds, both pre-existing, both nominal at-most merges

Both are wrong on the base too and keep the same wrong answer
(`data/reductions/`, reduced against HermiT with `tools/ddmin_hermit.py`):

- **refl1008** → `f1008.ofn`, two axioms:
  `≤1 s.(∃p.{c}) ⊑ C`, `InverseFunctional(p)`. HermiT: every class is under
  `C` (a non-`C` element has two distinct `s`-successors that are both
  `p`-predecessors of `c`, and inverse functionality identifies them). The
  bridge misses all `X ⊑ C`. The graph dump of the `A ⊑ C` test shows the
  second `s`-successor DIRECTBLOCKED by its sibling, whose `p`-successor was
  merged into the nominal `c`: the copy of the blocker would give `c` two
  `p⁻`-neighbours under `≤1 p⁻`. In Konclude this case belongs to the
  NN-rule (`applyFUNCTIONALRule`, `requiresNNRule`, cpp 14741–14790), which
  turns the nominal's blockable `p⁻`-neighbour into a new nominal; the port
  leaves it W3-DEFER (`u08.rs`, "The NN-rule for nominal predecessors stays
  W3-DEFER"). Not fixed here.
- **refl439** → `f439.ofn`, five axioms (`Q2 ≡ {c} ⊓ ≤1 r`, `r` reflexive,
  `InverseFunctional(p)`, `E ⊑ ∃r⁻.∀r⁻.{c}`, `Q5 ≡ ≤1 s⁻.(∃p.E)`). HermiT:
  `Q2 ⊑ Q5` (an `E` element `e` has an `r`-predecessor that equals `c` by
  reflexivity and `∀r⁻.{c}`, so `r(c,e)`, and `≤1 r` at `c` with `c`'s own
  self edge makes `e = c`; two `s⁻.(∃p.E)` neighbours of `c` are then two
  `p`-predecessors of `c`). The merge needs the at-most at the nominal `c`
  over a neighbour that `c` did not create, the same NN-rule territory; not
  traced further and not fixed.

## Differential pools (gold-backed seeds of earlier agents), both routes

`tools/pools.sh` (routes `ht_bridge` and automatic, 60 s, two KM processes,
`tools/diff_run.py`): the ten pools under `.work/agent-scratch/bridge-self/pools/`
(abox-probes-f/m, bridge-defers, bridge-defers-f, bridge-replay and the
`results/agents/2026-10-3*` probe pools res-data-values-3,
res-forced-nominal, res-fr282, res-lean-data-values, plus
sameindividual-bridge), the SELF pool, regress and micro sets of
bridge-self, the m413 residue pool and both m413 families (k, k2), and the
cb-s974 merge and vacuous families: 15,789 seeds, 31,578 runs.

- New (`km-v3`), `data/pools/after/summary.txt`: 29,975 ok, 1,474 ERR
  (forced-route refusals, almost all `ht_bridge`), 115 timeouts, 14 wrong.
  The 14 wrong rows are the pre-existing ones the cb-s974 and bridge-self
  agents recorded (m413 residue 7, res-data-values-3 6, res-lean-data-values
  1, all automatic route). The cb-s974 merge family, which had the five
  wrong seeds on the base, is now 0 wrong.
- Base (`km-base`) on every seed that was not ok after the fix on some route
  (1,485 seeds, 2,970 runs, `tools/pools.sh BASE before nonok.list`): every
  verdict identical to the new binary's (`data/pools/before/`). A seed that
  is ok after the fix on both routes agrees with HermiT and cannot be a new
  difference. **0 new differences.**

## The 16 held-out inputs (240 s, two at a time, 10926 and 12128 alone)

`tools/heldout.sh` with `tools/one.sh` and
`fix-bridge-defers/.../compare_ref.py`; `data/heldout/summary.tsv`. Every
input keeps its answer and its reference verdicts; 10926 times out on both
binaries (18 GiB). Wall times (s), base / new: 4903 3.3/3.3, 11647 4.0/4.2,
4796 2.9/3.0, 3917 4.3/4.4, 11378 5.5/5.7, 12191 5.8/5.8, 9151 54.4/56.2,
9577 64.3/78.9, 6132 18.4/18.2, 9899 20.6/19.1, 16315 25.6/20.7,
10838 60.9/58.2, 3087 65.5/61.2, 7557 98.3/93.5, 12128 35.3/36.8; RSS
unchanged except 7557 (4.02 to 3.33 GiB). 9577 has no SELF construct, so
only fix 1 can touch it; three further side-by-side pairs give base / new
80.6/80.5, 66.1/66.1, 78.2/79.3 s: the first pair's gap was host noise.
No regression beyond noise.

## The 112 nominal ORE design-half inputs (one at a time, 300 s)

`tools/ore_nominal.sh` (`ore_time.sh`, `ore_pair.py`, list
`tools/ore-design-nominal.txt`); `data/nominal/pair.txt`: 109 answered by
both, 109 identical signatures, 0 answer-status changes, 0 route changes;
time ratio new/base over the 26 inputs above 1 s: mean 0.983, median 0.986,
max 1.08. Coverage guard fired 0 times.

### Borderline timeouts in the family

refl1250 and refl1477 (automatic route) answer through the CB stack in 30
to 40 s after the bridge times out on both binaries. Three more runs each
(`data/family/border-*.tsv`): base refl1250 3 of 3 ok, refl1477 1 of 3 ok;
new refl1250 3 of 3 ok, refl1477 1 of 3 ok. Same behaviour, cap noise.

## Tests (code of f7e67fad, clean environment, `KM_THREADS=1`, `--test-threads=1`)

`tools/tests.sh` (no release flags exported; `env -i PATH HOME KM_THREADS=1
CARGO_TARGET_DIR=<worktree>/engine/target`). Library: 3,115 passed,
21 failed, 10 ignored, exactly the 21 checker-bound baseline failures (20
`tableau::` tests and
`cli::cb_derivation_candidate_tests::source_exact_taxonomy_uses_real_production_traces_and_models`,
`data/tests/lib-failures.txt`); no other failing test. Integration: all 90
targets pass (the 89 of the baseline plus the new `bridge_reflexive`);
`empty_and_universal_data_ranges` passed in 143 s
(`data/tests/summary.txt`). **No newly failing test.**

New regression target `engine/tests/bridge_reflexive.rs`: seven fixtures with
HermiT answers in `engine/tests/fixtures/bridge_reflexive/` (`min1722`,
`min526`, `merge1322_min`, `merge1585_min`, `merge1708_min`,
`selfloop_atleast`, `selfloop_blocker`), automatic route and `ht_bridge`,
three runs each. On `km-base` 12 of the 14 fixture-routes are wrong
(`data/tests/fixtures-on-base.tsv`; `merge1322_min` and `selfloop_blocker`
happen to be right on the base's automatic route).

## Not done

- refl1008 and refl439 stay wrong (pre-existing, also on the base and rc1):
  the NN-rule for a nominal's at-most over a blockable neighbour is not
  ported (`u08.rs`, W3-DEFER). Reductions with HermiT answers in
  `data/reductions/f1008.*` and `f439.*`; f439 was not traced. A fail-closed
  alternative (no blocking by a node whose subtree reaches a nominal, or a
  defer when the NN-rule would fire) would change the 112 nominal inputs'
  routes and was not attempted.
- No machine reference besides HermiT: Konclude 0.7.0 does not finish on the
  inputs, Openllet and JFact are not installed on ws. The golds of `min1722`,
  `min526` and the three new reductions are argued by hand
  (docs/HYBRID-CB-HT.md 21).
- The bridge has no Lean model; the three changes are argued, not proved.
- The diagnostic `BLOCK-TEST` line (`KM_HT_BLOCKING_SCAN_TRACE`) added to
  `is_individual_node_blocking` was not exercised on a blocked node after
  the fix (the u6 run blocks nothing).
- Termination after fix 2 is argued only empirically: family timeouts and
  pool timeouts match the base (the borderline family seeds behave the same
  on both binaries).
- `engine/target` deleted at the end; the worktree is kept.
