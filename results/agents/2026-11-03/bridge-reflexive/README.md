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

TODO

## The 16 held-out inputs

TODO

## The 112 nominal ORE design-half inputs

TODO

## Tests

TODO

## Not done

TODO
