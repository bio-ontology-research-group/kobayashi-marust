# bridge-auto-data (2026-11-02, `fix/v155-bridge-auto-data`)

Base: `development/v1.5.5` at 68ad4132 (binary `bin/km-base` = the
held-out gap's `km-63d6e63e`, same engine source). Branch binary
`bin/km-fix` (`data/binaries.sha256`; both under
`.work/agent-scratch/bridge-auto-data/bin/`). Every measurement: release
flags, `KM_THREADS=1`, ws under its normal shared load, at most two KM runs
at a time. Design argument: docs/HYBRID-CB-HT.md section 19.

## Task A: ore_ont_6132 and ore_ont_9899 on the automatic route

**Decline reason.** The `certified_nominals` racer's bridge deferred with
`datatype gate: a linear value-encoding disjointness has an unsupported shape`
(`data/6132.diag.err`, read with `KM_HT_STATS`). The racer's input comes
from the nominal frontend (`KM_NOMINALS=1`), whose two-sorted encoding adds
`→ G ∨ __data__`, `G ⊓ __data__ ⊑ ⊥` and `X → __data__` for every data range
`X`. The complementary-definer elimination folds `__data__` into `¬G`, so each
`X → __data__` becomes `G ⊓ X ⊑ ⊥`, including 24 clauses on value helpers
(`Q_201 ⊓ __dt__aux__digit__p__d ⊑ ⊥`, `Q_201 ⊓ __dt__aux__profile__k ⊑ ⊥`).
The forced `ht_bridge` input is not built in nominal mode and has no such
clause. The automatic ground-rule data-source attempt declined at the same
gate after 0.2 s.

**Fix (exact admission).** `linear_value_encoding_exact` admits
`H ⊓ G ⊑ ⊥` (H a helper, G not) when every value `v` with `v → H` has the
clause `v ⊓ G ⊑ ⊥` in the input; otherwise it defers with a new named reason.
With H read as the union of its values, every model of the helper-free
clauses satisfies the new clause, so the helpers still add no consequence.
Unit test `value_helper_disjoint_from_a_folded_sort_needs_every_value_disjoint`.

**Reporting.** Under `KM_TIMING` the race pipes the HT worker's stderr and
repeats its error lines as `KM_TIMING race: HT worker reported: ...`
(`data/defer-forward.{base,fix}.err`: the base prints nothing, the branch
prints the defer line).

**Five runs each (automatic route, ws):**

| input | branch (s) | base, same host (s) |
|---|---|---|
| 6132 | 23.3, 21.7, 22.0, 20.7, 21.5 | 12.3, 10.6, 16.0, 12.8, 14.6 |
| 9899 | 25.2, 21.6, 24.0, 24.2, 23.9 | 13.3, timeout, timeout, timeout, timeout |

Every branch run answers through the ground-rule data source
(`automatic data source accepted: KM_GROUND_RULE_SOURCE`) with the Konclude
and HermiT answer (`data/five-fix.tsv`, `data/five-base.tsv`). The answer no
longer depends on whether the 8 s bridge-first attempt finishes in time, but
it is slower than the base's lucky case: the ground-rule bridge input probes
401 public subjects at 30 to 50 ms each (about 16 s), while the racer's input
answers in 6.7 s (`--route certified_nominals`, `data/6132.cn.fix1.err`). No
budget or routing change was made; the per-subject cost of the ground-rule
input is open.

## Task B: the two intermittent bridge tests

Cause: test isolation, not time. Measurement scripts export the release
flags before `cargo test` (for example `.work/v155-heldout-gap/combined/run.sh`).
`KM_HT_NATIVE_FULL=1` makes `conditional_full_class_probe_restores_all_root_consistency_base`
fail deterministically, alone, at its premise
`!native_cardinality_abox_profile(&legacy, ..)`; `KM_HT_DDB=1` makes
`production_read_off_keeps_open_or_disjuncts_nondeterministic` fail at its
premise `!algo.conf_dependency_backjumping`. With all release flags the
bridge module alone fails exactly these two. The premises now assert the
configuration the environment selects; the tested properties hold under
both (bridge module with flags: 174 passed). No wall-clock dependence of a
verdict was found. Section 19.5 has the details.

## Validation

- Library suite, three runs (`tools/tests.sh`, clean KM environment): 3113
  passed, 21 failed each, the 21 baseline checker-bound failures exactly
  (`data/tests/lib*.failures`). One further run with the release flags
  exported: the same 21. No newly failing test.
- Integration targets: 86 of 86 pass (`data/tests/integ.txt`).
- Seed pools with HermiT gold, `ht_bridge` and automatic routes, 60 s cap
  (`tools/pools.sh`, `data/pools-compare.txt`): 0 WRONG before and after.
  Data-bearing pools in full (bridge-defers seeds and fseeds, data-coverage-
  regression, nominal-coverage, data-values probes, forced-nominal-data-
  misses, top-nominal-data, and the 431 data seeds of sameindividual-bridge);
  the data-free pools (bridge-replay, bridge-nominal-merge, r3-unannounced)
  on their first 200 seeds, since the changed gate is unreachable without a
  value helper. 5,156 runs per binary; 3 transitions, all at the 60 s cap
  (m2157 57.1 to 60.1 s, m2242 and r1125 60.1 to 59.9 s; m2157 retimed:
  base 60.5/92.1 s, branch 64.9/84.0 s, identical output).
- 16 held-out inputs (`tools/heldout.sh`, `data/heldout-{base,fix}.tsv`):
  same answers; times within noise except 6132/9899 (above). ore_ont_12128
  published the same taxonomy on base (230 s, 400 s cap) and branch (224 s):
  1,567 unsatisfiable classes against Konclude's 4,716, `taxonomy_disagreement`.
  It has no data values, so this change is not involved; it is the
  `production_all` race's bridge answer (`data/12128/base.timing.txt`) and
  belongs to the 12128 `SELF` work.
- 112 nominal ORE design-half inputs (`tools/ore_time.sh`, `tools/ore_pair.py`,
  `data/ore/`): 109 answered by both, 109 identical signatures, no
  answer-status or route change; time ratio mean 1.041, median 0.987, max
  1.59 (13230, retimed back to back 2.01/2.01 and 1.93/1.99 s;
  `data/ore/ore-retime.txt`).

## Tools

`pools.sh`, `diff_run.py`, `seed_compare.py` (seed pools); `heldout.sh`,
`five.sh`, `five-seq.sh` (held-out and five-run timing); `ore_time.sh`,
`ore_pair.py` (112 ORE inputs); `compare_ref.py` (pinned references);
`tests.sh` (library and integration suites); `vaux.py`, `conc.py` (clause
shape analysis of a `KM_DUMP_TIN` dump).
