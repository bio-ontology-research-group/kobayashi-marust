# sat578-opus: B6 and B4a of optimized blocking next to nominals

Branch `fix/v155-sat578-opus` from `development/v1.5.5` at `274faa6a`,
worktree `.work/worktrees/fix-sat578-opus`. Scratch:
`.work/agent-scratch/sat578-opus/`. Release flags for every measurement:
`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`.

Binaries (`.work/agent-scratch/sat578-opus/bin/`):

| name | source | sha256 |
|---|---|---|
| `km-274faa6a` | base `274faa6a` | `b5eec0c0de96a18e7abd68ad22d786769c70a7f8d070305963adff88c71ec4f7` |
| `km-b1fcbb93` | fix, code of `b1fcbb93` (later commits change tests and docs only) | `1caca2fa5cd53765d3ffcec206acb95a55750e2e19811561bca1634e949ce035` |

Every "fix" number below is `km-b1fcbb93`. The test build of `a63c0a4d`
rebuilt `engine/target/release/km` byte-identical to `km-b1fcbb93` (`cmp`).

The argument for the change is in `docs/HYBRID-CB-HT.md` section 25.

## Cause, in short

`F ⊑ Q1` and `F ⊑ Q4` need a node `y` (a tree successor of the nominal `c`,
in `≥2 s⁻.(∃s.{c})`) whose two `s⁻`-successors `w₁, w₂` both link to `c`. The
bridge blocked both by `y` itself before either linked:

1. B6 (cpp 18731): for `¬(≤n R.C)` at the parent Konclude keeps `w`
   c-blocked when `w ∈ C`; both `w` were redirected to `y`, which then has
   one successor where it needs two.
2. B4a (cpp 18788): the a-block counted `y`'s nominal parent `c` for `w`'s
   `∃s.{c}`, although the copy of `y` at `w` would be a new `s`-predecessor
   of `c` that `c`'s `≤1 s⁻.(∃s.{c})` never counts. The port also counted a
   tree successor that had merged into `c` (a ghost link Konclude removes,
   cpp 21283) as a deeper successor.

The first attempt's quoted cpp 18788 condition
(`hasIndividualsLink(wNode, succIndi, …)` on nominal successors) is not in
Konclude's source; see section 25.3.

## Change (`engine/src/konclude_ht/completion/u19.rs`, `mod.rs`)

- B6 count test `b6_redirect_collides` for the `¬(≤n R.C)` arm; switch
  `KM_HT_NO_B6_COLLISION_GUARD=1`.
- B4a nominal guard (skip ghosts of nodes merged into a nominal; count a
  nominal neighbour of the blocker only when the blocker created the link and
  is not the probe root, or the blocked node has the same link); switch
  `KM_HT_NO_B4A_NOMINAL_GUARD=1`.
- `KM_HT_NO_SAT578_FIX=1` turns both off.
- `KM_HT_SAT578_GUARD_TRACE=PATH` creates PATH when a guard refuses what the
  base accepted (used by the validation below).

## Gold

Section 25.1 (hand proofs of `min_q1`, `sat578`/`red_both`, `fx279`; the
other fixtures' proofs from the first attempt, checked). Konclude was not run
(it hangs on these fixtures, first attempt).

## Results

Full text in `docs/HYBRID-CB-HT.md` section 25.5. Files:

| check | result | data |
|---|---|---|
| 9 fixtures (8 of sat578 plus `fx279`), both routes, 3 runs | 54/54 ok; base 18/18 wrong | `data/fx-final.tsv`, `data/fx-base.tsv` |
| sat578 family, 1,968 seeds, both routes | 0 wrong | `data/pools/fix-sat578-fam.tsv.gz`, `data/pools/final-table.txt` |
| all pools (incl. bridge-satcache and bridge-nn-rule families), 47,344 seed-routes | 0 new wrong; 12 seed-routes ok on base become TIMEOUT/ERR (3 of 3 on both sides) | `data/pools/final-diff.tsv`, `data/pools/flips-*.tsv` |
| rows of `regressions-of-fbd1932c.txt`, 3 runs | all ok 3/3 except `nn969` `ht_bridge` (TIMEOUT 3/3) | `data/reg-final.tsv` |
| library | 21 failures = the known list | `data/tests/lib-results.txt` |
| 95 integration targets | all pass (`bridge_satcache` after its control change) | `data/tests/summary.txt`, `data/tests/*.log` |

Lost answers (base ok, fix not ok, 3 of 3 each): `nn1881` (both routes),
`nn969` (`ht_bridge`), `s578_1026` (both), `s578_1288` (both), `s578_171`
(both), `s578_733` (both), `s578_908` (`ht_bridge`). Cause: the B6 count test
refuses c-blocks that Konclude accepts (section 25.4); I have no exact
change that keeps both soundness and these answers.

Pool method: the fix ran every seed once with `KM_HT_SAT578_GUARD_TRACE`;
unmarked completed runs compute what the base computes, the base ran on the
7,032 marked runs and on fix timeouts (`tools/pools.sh`, `pools2.sh`,
`rows.sh`, `fired.py`, `final.py`). Not run: the 16 held-out ORE inputs and
the 112 nominal design-half inputs; no timing comparison beyond the 60 s
verdicts.
