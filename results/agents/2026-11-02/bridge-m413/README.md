# m413, the forced-bridge panic, and probe-time merges on the reused consistency model (agent `bridge-m413`, 2026-11-02)

Branch `fix/v155-bridge-m413` (from development/v1.5.5 63d6e63e), worktree
`.work/worktrees/fix-bridge-m413`. Design argument: docs/HYBRID-CB-HT.md
section 18. Measurements on ws, `KM_THREADS=1`, release flags
(`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1`), at most two KM
runs at a time, host shared with other agents (load 20 to 47). Binaries in
`.work/agent-scratch/bridge-m413/bin` (`km.base` = 63d6e63e, `km.final` =
the branch head).

## Outcome

| seed | HermiT | base (63d6e63e) forced / auto | branch forced / auto |
|---|---|---|---|
| m413 | `B ⊑ D` | WRONG (missing) / WRONG | ok / ok |
| m37 | inconsistent | panic / timeout (30 s) | ok / ok |
| m337 | consistent | panic / timeout | ok / ok |
| m593 | consistent | panic / timeout | ok / ok |
| m977 | consistent | panic / ok (6.7 s) | ok / ok |

`data/m413-min.ofn` (10 axioms) and the full seed answer on both routes,
with the restricted automaton arm on and off and with leaf reuse on and
off. The panic seeds answer in 0.01 to 0.02 s on both routes.

## Causes and fixes (docs/HYBRID-CB-HT.md section 18)

Four defects of the port, each argued in its subsection.

1. **18.1, m413.** With the precomputation replay on, an ABox nominal of a
   class job carries Konclude's backend blocks; its asserted edges exist
   only in the cached association. Two defects kept the blocks of a
   nominal that the probe changes:
   - the cardinality criticality test read a node-level role-successor
     count (`IndividualProcessNode::get_role_successor_count`) that was a
     stub returning 0, so `i3` with two `f`-successors (itself and the
     cached `i0`) was never critical and `i0` never merged; it now reads
     the arena count, and the stub is removed;
   - the concept criticality test required the concept to be
     deterministic in addition to Konclude's partition argument
     (`!nondeterministic && !has...(…, !nondeterministic)` where Konclude
     has `!has...(…, !nondeterministic)`), so the automaton state of
     `∀t⁻.D` that reached `i2` under the merge never released `i2`'s
     block and the asserted `s(i3,i2)` never appeared.
   The previous agent's suspect, the deferred nominal-neighbour
   backend-expansion sub-block of merge phase 5, is not the cause: `i2`
   had no materialized link to `i0`, so it was not in `i0`'s connection
   set and the sub-block would not have run (it stays deferred). The
   retained consistency leaf (section 16) is not exposed on the
   retained-base path: it exists only when the consistency completion is
   non-deterministic, and then the replay is off and no nominal carries a
   block (`data/m413-leaf{1,2,3}.ofn`: leaf built with 1 to 2 decisions,
   flags 0 on every nominal, correct before and after, leaf reuse on and
   off). On the per-job-reset leaf path the fixes act in the same code.
2. **18.2, the panic.** A withheld root cancellation (a sibling with an
   empty stored refutation and no witness) let the DDB analysis walk
   deterministic dependencies that a refuted sibling had derived, among
   them a merge dependency of a node that the sibling had created and the
   epoch pop had truncated (the dependency spine is epoch-exempt, the node
   arena is not). Dependencies of popped nodes now lose their individual
   at the pop (filed once per dependency under the epoch that allocated
   the node, so the work is linear), a read-time guard covers a
   dependency whose individual is set late, the null-individual path
   copies the parent descriptor's attribution as Konclude's overload does,
   and a line that met a released individual writes no unsat-cache entry.
3. **18.3, at-most reapplication in later alternatives** (k1414, sibling
   family). `apply_atmost_rule` installs the rule's reapplication inside
   the first alternative's epoch; the advance to a later alternative did
   not install it again, so a link added at the counted parent in that
   alternative never re-fired `≤n`. Both advance functions now re-arm it.
4. **18.4, one edge per neighbour** (k163, sibling family). The typed
   selective expansion installed only the expanded role toward a
   neighbour and then marked the neighbour as handled, so another role to
   the same neighbour (here the inverse-functional `g`) was never
   installed. It now installs every installable cached value toward that
   neighbour in both orientations, as Konclude's
   `expandIndividualNeighbourNodeFromBackendCache` does.

Minimal witnesses (with HermiT answers): `data/m413-min.ofn`,
`data/k163-min.ofn` (6 axioms, `P2 ⊑ C`), `data/k1414-min.ofn`
(7 axioms, `P1 ⊑ A`; `k1414-v2.ofn` without the inverse property).

## Sibling seed family (2,000 seeds, HermiT gold)

`tools/gen_m413.py` (seed mod 4): (0) functional `f` below `r`, `t` or `s`
with `r ∘ s ⊑ t`, `t` transitive, probe classes `P ⊑ ∃f.{a}` with
`P ⊑ ∃f.P` (or a class below `P`) and an asserted `f(a,b)`, so `a` and `b`
merge in the probe; (1) inverse-functional `g` with `P ⊑ ∃g.{a}` and
asserted `g(b,a)`; (2) at-most restrictions on nominal hubs
(`h : ≤1 r`, qualified or not) with an asserted successor and a probe
`P ⊑ ∃r⁻.{h}`; (3) mixtures with `DisjointClasses`, `SameIndividual`,
`DifferentIndividuals`. Universal restrictions over `t⁻`, chains and
inverses on the nominals throughout. HermiT 1.4.3: 1,904 consistent, 96
inconsistent. Seeds and gold: `data/seeds/kseeds-and-hermit-gold.tar.gz`.

| binary | forced `ht_bridge` | automatic |
|---|---|---|
| base 63d6e63e | 1,885 ok / **113 WRONG** / 2 error | 1,886 ok / **113 WRONG** / 1 timeout |
| after 18.1 and 18.2 | 1,981 ok / 19 WRONG | 1,981 ok / 19 WRONG |
| branch head | **2,000 ok** | **2,000 ok** |

Every miss was an omitted subsumption (no extra subsumption, no
consistency mismatch). By family (base, automatic route): 16 / 57 / 29 /
11. The 19 left after 18.1 and 18.2 split into one reuse case (k163;
`KM_BRIDGE_FRESH_ENV=1` recovers it) and 18 that a fresh environment
also misses (k1414 and others); 18.3 and 18.4 fix all of them. A second
batch of 2,000 seeds (2000 to 3999) is reported below.

Second batch (seeds 2000 to 3999, same generator, HermiT 1,916 consistent,
81 inconsistent, 3 without a HermiT answer at 120 s that `diff_run.py`
re-ran; `data/seeds/k2seeds-and-hermit-gold.tar.gz`,
`data/diff/k2-*.tsv.gz`):

| binary | forced `ht_bridge` | automatic |
|---|---|---|
| base 63d6e63e | 1,881 ok / **112 WRONG** / 7 error | 1,882 ok / **112 WRONG** / 6 timeouts |
| branch head | **2,000 ok** | **2,000 ok** |

So the family found 225 incomplete seeds in 4,000 on each route of the
base, all of the shape m413 stands for (merges of ABox nominals that only
a probe triggers), and 0 remain.

## Differentials against HermiT, before and after

`tools/diff_pools.sh` (HermiT 1.4.3 answers cached as gold, 30 s per KM
run, release flags, routes `ht_bridge` (forced) and `auto`); before =
`km.base` (63d6e63e), after = `km.final2` (branch head 30792b8d). Columns:
ok / WRONG / declined or error / timeout / no gold. Per-seed rows:
`data/diff/<pool>-{base,final2}.tsv.gz`; `tools/cmp_pools.py` lists every
change.

| pool | seeds | ht_bridge before | ht_bridge after | auto before | auto after |
|---|---|---|---|---|---|
| k (this agent, `gen_m413.py`) | 2,000 | 1,885 / 113 / 2 / 0 / 0 | **2,000** / 0 / 0 / 0 / 0 | 1,886 / 113 / 0 / 1 / 0 | **2,000** / 0 / 0 / 0 / 0 |
| mrest (bridge-abox-probes `gen_rest.py`) | 2,000 | 1,976 / 1 / 7 / 16 / 0 | 1,981 / 0 / 3 / 16 / 0 | 1,983 / 1 / 0 / 16 / 0 | 1,987 / 0 / 0 / 13 / 0 |
| same (sameindividual-bridge) | 2,000 | 1,935 / 0 / 11 / 0 / 54 | same | 1,946 / 0 / 0 / 0 / 54 | same |
| chain (sameindividual-bridge) | 2,000 | 1,986 / 0 / 14 / 0 / 0 | same | 2,000 / 0 / 0 / 0 / 0 | same |
| defers `dec` (bridge-defers) | 300 | 147 / 0 / 153 / 0 / 0 | same | 300 / 0 / 0 / 0 / 0 | same |
| defers `flt` (bridge-defers) | 200 | 155 / 0 / 45 / 0 / 0 | same | 163 / 0 / 0 / 37 / 0 | same |
| nominal-merge (bridge-nominal-merge) | 2,000 | 1,993 / 0 / 7 / 0 / 0 | same | 2,000 / 0 / 0 / 0 / 0 | same |
| replay (bridge-replay) | 1,000 | 997 / 0 / 3 / 0 / 0 | same | 999 / 0 / 0 / 1 / 0 | same |
| data-coverage-regression | 400 | 24 / 0 / 376 / 0 / 0 | same | 400 / 0 / 0 / 0 / 0 | same |
| nominal-coverage | 400 | 113 / 0 / 287 / 0 / 0 | same | 385 / 0 / 0 / 15 / 0 | same |
| data-values probes | 38 | 25 / 0 / 13 / 0 / 0 | same | 35 / 0 / 0 / 3 / 0 | same |
| forced-nominal-data-misses | 14 | 7 / 0 / 7 / 0 / 0 | same | 14 / 0 / 0 / 0 / 0 | same |
| top-nominal-data | 200 | 55 / 0 / 145 / 0 / 0 | same | 192 / 0 / 0 / 8 / 0 | same |
| results/agents/2026-10-3* (66 gold-bearing fixtures, `$S/respool`) | 66 | 14 / 1 / 51 / 0 / 0 | 15 / 0 / 51 / 0 / 0 | 56 / 8 / 2 / 0 / 0 | 57 / 7 / 2 / 0 / 0 |

No seed of any pool changed from ok to anything else on either route
(0 new differences). Changes: k 226 WRONG, 2 errors and 1 timeout to ok;
mrest m413 (both routes), the four panic seeds (forced: error to ok;
auto: m37, m337, m593 timeout to ok); `nominal-r1600/m1` WRONG to ok on
both routes. An intermediate binary (after 18.1 and 18.2 only) also
answered `nominal-coverage/m2371` on the automatic route where the base
timed out at 30 s; the head times it out again, a timing effect at the
cap.

Not changed and outside this branch: seven fixtures of the results pool
are wrong on the automatic route before and after (`data-values-3`:
`length_empty`, `length_exhaust`, `length_value`, `pattern_subsumption`,
`pattern_value`, `string_chain`; `lean-data-values/opaque_single`, a
consistency mismatch). The forced bridge declines all seven, so the CB
stack answers them; they concern data facets.

## The 16 held-out ORE inputs (docs/V1.5.5-STATUS.md)

`tools/ore16.sh`, release flags, `timeout 240`, one process at a time per
stream, base and branch head as two streams side by side (two KM runs at
a time); reference comparison with
`results/agents/2026-11-01/bridge-defers/tools/compare_ref.py`
(`data/ore/refcmp-*.txt`). Outputs compared after sorting:

| input | base (63d6e63e) | branch (30792b8d) | time ratio | outputs | references (branch) |
|---|---|---|---|---|---|
| 4796 | ok, 3.2 s, 0.20 GiB | ok, 3.2 s, 0.20 GiB | 1.013 | identical | konclude ok openllet ok jfact ok |
| 6132 | ok, 9.9 s, 0.51 GiB | ok, 9.7 s, 0.51 GiB | 0.987 | identical | konclude ok hermit ok |
| 9899 | ok, 11.1 s, 0.51 GiB | ok, 10.6 s, 0.51 GiB | 0.954 | identical | konclude ok hermit ok |
| 3917 | ok, 4.6 s, 0.26 GiB | ok, 4.8 s, 0.27 GiB | 1.044 | identical | konclude ok jfact differs |
| 11378 | ok, 5.9 s, 0.32 GiB | ok, 6.1 s, 0.32 GiB | 1.038 | identical | konclude ok jfact differs |
| 12191 | ok, 6.2 s, 0.32 GiB | ok, 6.2 s, 0.32 GiB | 0.999 | identical | konclude ok jfact differs |
| 9151 | ok, 57.9 s, 0.63 GiB | ok, 57.7 s, 0.63 GiB | 0.997 | identical | konclude ok jfact differs |
| 9577 | ok, 83.5 s, 0.66 GiB | ok, 80.1 s, 0.66 GiB | 0.960 | identical | konclude ok jfact differs |
| 12128 | ok, 213.8 s, 2.73 GiB | ok, 212.2 s, 2.74 GiB | 0.993 | identical | konclude DIFFERS |
| 4903 | ok, 3.5 s, 0.18 GiB | ok, 3.5 s, 0.18 GiB | 0.975 | identical | konclude ok |
| 11647 | ok, 4.4 s, 0.24 GiB | ok, 4.3 s, 0.24 GiB | 0.961 | identical | konclude ok hermit ok openllet ok |
| 3087 | ok, 63.2 s, 2.49 GiB | ok, 64.5 s, 2.49 GiB | 1.020 | identical | konclude ok |
| 10838 | ok, 62.1 s, 2.37 GiB | ok, 61.7 s, 2.36 GiB | 0.994 | identical | konclude ok |
| 16315 | ok, 30.5 s, 1.33 GiB | ok, 28.2 s, 1.33 GiB | 0.927 | identical | konclude ok |
| 7557 | ok, 98.1 s, 3.74 GiB | ok, 98.0 s, 3.74 GiB | 0.999 | identical | konclude ok |
| 10926 | exit 1, 228.4 s, 18.00 GiB | exit 1, 231.7 s, 18.00 GiB | 1.014 | identical | - |

All 16 inputs keep their answers (identical sorted output on every
input; 14 agree with Konclude's reference, as before). Times are equal
within noise (ratios 0.93 to 1.04, load 25 to 45); in a first pair of
runs (`data/ore/times-base-run1.tsv`) 12128 timed out at 240 s on both.

A first version of 18.2 (a rescan above the epoch mark at every pop) made
4796 slower: 3.3 s to 3.9 s over 8 alternating runs
(`data/ore/retime-4796.txt`); the linear filing of the head removes it
(5 alternating runs each, `data/ore/retime3-4796.txt`: base median
3.33 s, head 3.25 s, head with the 18.3 re-arm off 3.23 s).

12128 (pre-existing, not changed): when it finishes under the cap
(about 213 s on both binaries, route `production_all`, the HT-first
phase ended at 180 s without an answer), its answer disagrees with
Konclude's reference: KM reports 1,567 unsatisfiable classes, Konclude
4,716. The base gives the same output. Not investigated further here.

## Tests

On the head (326839e3 code), `KM_THREADS=1`, `--test-threads=1`, release
(`tools/run_tests.sh`; `data/test-lib-summary.txt`,
`data/test-lib-failures.txt`, `data/test-integration-summary.txt`):

- library: 3,112 passed, **21 failed**, 10 ignored. The 21 are exactly the
  baseline's checker-bound set (20 `tableau::` tests and
  `cli::cb_derivation_candidate_tests::source_exact_taxonomy_uses_real_production_traces_and_models`);
  no other failure. The two load-sensitive bridge tests
  (`conditional_full_class_probe_restores_all_root_consistency_base`,
  `production_read_off_keeps_open_or_disjuncts_nondeterministic`) passed
  in all three runs.
- integration: all **87 targets pass** (473 tests), including the new
  `bridge_probe_merge` (m413, a leaf variant, m37, m593, k163, k1414, each
  on both routes) and `completion_hot_path_env`. One earlier run failed
  `completion_hot_path_env` because the first version of the
  `KM_HT_DIAG_NO_ATMOST_REARM` switch read the environment inline in the
  completion; the switch now goes through `cached_completion_flag!`
  (326839e3).
- Newly failing tests versus the base: none.

## Commits (branch `fix/v155-bridge-m413`)

1. `f3e0fbd3` release dependency individuals of popped nodes (18.2,
   first version); arena-backed role-successor count (18.1, item 1);
   `KM_HT_GRAPH_DUMP`, `KM_HT_DIAG_NO_{NEIGHBOUR,SUCCESSOR}_BLOCK`.
2. `b0e92ea6` a non-deterministic concept releases the neighbour-expansion
   block as in Konclude (18.1, item 2); leaf variants and the generator.
3. `78a131e3` re-arm the at-most reapplication in later alternatives
   (18.3); expand every cached value toward a neighbour (18.4); regression
   test `engine/tests/bridge_probe_merge.rs`.
4. `9052f844` drop temporary traces; design section 18 (draft).
5. `30792b8d` linear release of popped-node dependencies, read-time guard,
   no duplicate re-arm (18.2, 18.3).
6. `326839e3` cached flag for the re-arm diagnostic; design section 18.6.
7. `a092684e` and the results commit after it (README, data, tools).

## Tools

`tools/run.sh` (one release-flag run), `tools/gen_m413.py` (seed family),
`tools/prime_gold.py` and `tools/diff_run.py` (HermiT gold and
differentials, copies of the bridge-abox-probes tools),
`tools/diff_pools.sh` (all pools, both routes), `tools/cmp_pools.py`
(before/after per seed and route), `tools/minimize.py` (greedy
minimization), `tools/ore16.sh` (the 16 held-out inputs with reference
comparison), `tools/run_tests.sh`. Diagnostics added on the branch:
`KM_HT_GRAPH_DUMP=1` (every node with flags, label tags and links at each
clash-free fixpoint, and every merge), `KM_HT_DIAG_NO_NEIGHBOUR_BLOCK=1`
and `KM_HT_DIAG_NO_SUCCESSOR_BLOCK=1` (turn one backend block off),
`KM_HT_DIAG_NO_ATMOST_REARM=1` (negative control for 18.3).

## Not done

- **12128** (pre-existing, outside the four defects): when it finishes
  inside 240 s, base and branch give the same answer, which disagrees
  with Konclude's reference (1,567 against 4,716 unsatisfiable classes).
  Not investigated; it should be, since it is a wrong answer of the
  release candidate whenever 12128 answers.
- Seven `data-values-3` / `lean-data-values` fixtures are wrong on the
  automatic route before and after (the bridge declines them; the CB
  stack answers). Not investigated (data facets, outside the bridge).
- The port routes an unqualified `≤1` through the general merge
  branching; Konclude dispatches it to `applyFUNCTIONALRule` (cpp 14934,
  the port's branch at u08 `apply_atmost_rule` is empty). After 18.3 no
  seed shows a difference, so it is recorded, not changed.
- `test_individual_node_backend_cache_concepts_synchronization` and the
  nominal-neighbour backend-expansion sub-block of merge phase 5 stay
  deferred; the first is inert in production (its flag is never set),
  the second is not on the path of any seed (section 18.1).
- The per-job-reset leaf path (no retained base, replay on) is covered
  by the argument only; no seed in the pools reaches it with a block
  released by these fixes.
- No Lean coverage (the bridge has no Lean model); all four arguments are
  written and checked only differentially against HermiT.
- Measurements used `km.final2` (30792b8d). The head (326839e3, a092684e)
  differs only in reading the `KM_HT_DIAG_NO_ATMOST_REARM` diagnostic
  through a cached flag (the hot-path guard of
  `completion_hot_path_env`), which does not change any rule.
