# SameIndividual in the native bridge (agent `sameindividual-bridge`, 2026-11-01/02)

Branch `fix/v155-sameindividual-bridge` (from development/v1.5.5 1427ce55),
worktree `.work/worktrees/fix-sameindividual-bridge`. Design argument:
docs/HYBRID-CB-HT.md section 13. Measurements on ws, `KM_THREADS=1`,
release flags (`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1`), `--lines`,
`timeout 240`, peak RSS from `/usr/bin/time -v`; ws load 25 to 55 during
the runs (shared host).

## Outcome in one paragraph

The pre-merge is implemented and exact (quotient of the typed ABox by its
`SameIndividual` classes, TBox nominals renamed), and it fixes 11 wrong
answers of the automatic route on generated seeds. It does not recover the
five held-out inputs on the default route: the generic HT racer still
declines `SameIndividual`, because the bridge does not finish these ABoxes
with its default machinery. Behind three diagnostic switches the bridge
answers ore_ont_16315 in 131 s (2.4 GB) with Konclude's taxonomy; 10838,
3087, 7557 and 15846 get through consistency in 22 to 30 s and then spend
the rest of the 240 s in subject probes; 10926 (which has no
`SameIndividual`) needs about 470 s. Four quadratic scans in the bridge were
found and three removed (exact, same outputs); one switch (Konclude's
restricted automaton re-fire) is not shown complete for this port, and the
last cost (blocking-candidate scans in the probes) is not addressed.

## What changed (commits on the branch)

1. `782dab9d` native ABox: exact `SameIndividual` pre-merge
   (`orchestrate/cb_to_ht.rs`, `quotient_same_individuals`,
   `rename_concept_individuals`; used by `install_nominal_abox_with_same`
   whenever equality is admitted; `KM_NO_SAME_PREMERGE=1` restores the
   run-time `{b}(a)` encoding). Three unit tests. `KM_HT_STOP_TRACE=1`
   names the site of an incomplete stop (`raise_stop(false)` is now
   `#[track_caller]`).
2. `a1f19f60` bridge: membership set for the duplicate check of
   `ht_all_rule_target_links` (was quadratic in node degree); index for the
   same-individual scan and the assertion-journal scan of
   `write_completed_native_representative_associations` (were quadratic in
   the ABox); diagnostics `KM_HT_AUTOMAT_REST_LINK(=_AUDIT)`,
   `KM_HT_CONDITIONAL_FULL_LIMIT`, `KM_HT_ADMIT_SAME` (all off by default).
   The generic racer keeps declining `SameIndividual`.
3. `5e39edf7` bridge: the saturation writer's assertion journal
   (`write_native_abox_representative_cache`) resolved once per call
   (was quadratic, with a role-list copy per assertion).
4. The last commit: the stop trace reads a cached flag (the
   `completion_hot_path_env` guard), design section, README, data.

## Exactness

The argument is in docs/HYBRID-CB-HT.md section 13: models of the quotient
are the models of the original up to the renaming in both directions, with
the same class and property extensions, so consistency, unsatisfiable
classes and class subsumptions are equal. `DifferentIndividuals` inside a
class becomes a self pair, which `native_nominal_consistency` reads as an
inconsistency before any completion; a nominal `{b}` of a merged-away `b`
denotes the representative (source axioms renamed, the proxy `{b}` is one
of the representative's proxies). TBox-forced equalities (functional
roles, at-most, nominal subsumptions) stay run-time merges.

The three index changes are implementation only: the indexes hold exactly
the elements the scans visited, are built from the immutable context the
writer reads, and fail exactly when the scans failed; the per-node visit
keeps the scan's order where the consumer is order-sensitive, and the
saturation writer's targets are sets.

## Seed differentials (HermiT 1.4.3.456 oracle, 30 s, KM_THREADS=1)

- `gen_same.py`, 2,000 seeds (equality classes, conflicting class
  assertions across a class, `DifferentIndividuals` inside and across
  classes, merged nominals in the TBox, functional and inverse-functional
  roles, negative and data assertions); HermiT: 1,385 consistent, 561
  inconsistent, 54 without an answer in 120 s.

  | binary | route | ok | wrong | declined | no oracle |
  |---|---|---|---|---|---|
  | RC (base) | auto | 1,935 | **11** | 0 | 54 |
  | RC (base) | ht_bridge | 1,935 | 0 | 11 | 54 |
  | branch (v7) | auto | 1,946 | 0 | 0 | 54 |
  | branch (v7) | ht_bridge | 1,935 | 0 | 11 | 54 |

  The 11 wrong base answers (s135, s732, s878, s1032, s1167, s1275, s1303,
  s1308, s1422, s1547, s1556) are all a functional data property with two
  values on two members of one equality class; HermiT: inconsistent, base
  automatic route (ground-rule data source, bridge with run-time merges):
  consistent. The pre-merge puts both values on one individual and the
  bridge finds the clash. The 11 bridge declines are a source-TBox
  construct the bridge does not support (`unsupported=1`), the same on
  base and branch.
- `gen_chain.py`, 2,000 seeds (transitive role, property chains,
  inverses, hubs, universal restrictions over complex roles, equality,
  nominals); HermiT 1,817 consistent, 183 inconsistent. Base, branch, and
  branch with `KM_HT_AUTOMAT_REST_LINK=1`: identical per seed, 2,000 auto
  ok, 1,986 ht_bridge ok, 14 declines, 0 wrong.
- Restricted-arm audit (`KM_HT_AUTOMAT_REST_LINK_AUDIT=1`,
  `data/audit-chain.tsv`): 3,203 of 4,000 chain-seed runs take the
  restricted arm; on 122 (61 seeds, both routes) the full arm would add an
  operand outside the restricting link at that point. This is why the
  switch stays off.

## The five held-out inputs (and 15846)

Before = RC `km-v1.5.5-rc-pgo`, after = branch default (non-PGO build),
diag = branch with `KM_HT_ADMIT_SAME=1 KM_HT_AUTOMAT_REST_LINK=1
KM_HT_CONDITIONAL_FULL_LIMIT=1000000` (v8). Konclude times from the task.

| input | Konclude | before | after (default) | diag (v8) |
|---|---|---|---|---|
| 16315 | 22 s | timeout, 18.0 GiB | timeout, 18.0 GiB | **131 s, 2.3 GiB, taxonomy = Konclude reference** |
| 10838 | 21 s | timeout, 18.0 GiB | timeout, 18.0 GiB | timeout, 4.0 GiB; consistency done at 22 s, 1,700 of 4,327 probes at 0.15 s each |
| 3087 | 20 s | timeout, 13.6 GiB | timeout, 18.0 GiB | timeout, 4.5 GiB; consistency at 22 s |
| 7557 | 52 s | timeout, 4.2 GiB | timeout, 18.0 GiB | timeout, 4.4 GiB; consistency at 29 s, 1,089 of 33,520 probes |
| 10926 | 63 s | timeout, 18.0 GiB | timeout, 18.0 GiB | timeout, 18.0 GiB; worker 6.1 GB, consistency at 119 s, 59,521 of 176,225 probes at about 500/s |
| 15846 | | timeout, 18.0 GiB | (not rerun) | timeout, 4.0 GiB (v7) |

Peak RSS "18.0 GiB" is the 18,866,228 to 18,886,564 kB plateau of the
whole run (the CB stack's memory watchdog); every run stays under the
20 GiB cap. 10926 has no `SameIndividual`: its frontend takes 43 s, the
3.5 million-clause conversion 18 s, the bridge environment 20 s; at the
measured probe rate it needs about 470 s on ws, out of reach at 240 s on
time, not on memory (the worker is 6.1 GB).

Where the time went on 16315 before each fix (forced bridge, traced):
consistency more than 19 minutes (automaton rule over hub nodes) to 15 s
with the restricted arm; legacy schedule 15 s per subject probe (the ABox
is completed again per probe) to 64 probes per 4 s on the conditional-full
schedule; representative writer 128 s to under 1 s (index); on 10838 the
saturation writer 130 s to 0.6 s (index). What remains on 10838, 3087,
7557: the first 1,700 subject probes cost 0.15 s each, mostly in
`get_anywhere_blocking_individual_node_canidate_hashed` and its linear scan
over the retained graph's nodes (`ProcessContext::node_mut` copies).

## ORE regression check

`ore_time.sh` of `results/agents/2026-10-30/r3-unannounced/`, 300 s,
release flags, base and branch side by side. The RC binary is a PGO build,
so the pairing uses a non-PGO build of 1427ce55 (`km.base-nopgo`, built
from a detached checkout); against the PGO RC the branch's non-PGO build
was 1.22 times slower on average, which is the PGO difference.

- 112 nominal ORE inputs of the paired design half
  (`data/ore-times-{basenp,v8}.tsv`): 108 answered by both, 108 identical
  signatures, no answer-status or route change; time ratio branch/base over
  the 26 inputs above 1 s: mean 0.965, median 0.985, max 1.05.
- 66 corpus inputs under 1 MB with `SameIndividual`
  (`data/same-small.txt`, `data/ore-times-same-{basenp,v8}.tsv`): 66
  answered by both, 66 identical, no route change; 59 of them take the
  pre-merge (forced or manual routes that admit equality); ratio over the
  14 inputs above 1 s: mean 1.008, median 1.011, max 1.12.

No frontend change, so no frontend clause differential was needed.

## Tests (`KM_THREADS=1`, `--test-threads=1`)

- Library: 3,103 passed, 21 failed, 10 ignored. The 21 are the baseline's
  checker-bound set (20 `tableau::` tests and
  `cli::cb_derivation_candidate_tests::source_exact_taxonomy_uses_real_production_traces_and_models`);
  no other test fails. The three new pre-merge tests pass.
- Integration: all 86 targets pass. `completion_hot_path_env` failed once
  on an inline `getenv` that the stop trace added in `clash.rs`; the trace
  now reads a cached flag and the target passes.

## Seeds and tools

`tools/gen_same.py`, `tools/gen_chain.py` (generators), `tools/diff_run.py`
(HermiT differential, oracle in `.work/agent-assets/2026-10-28-scratch/oracle`),
`tools/audit_seeds.sh` (restricted-arm audit), `tools/run1.sh`,
`tools/run1ts.sh` (one protocol run with peak RSS; the second with
timestamped stderr), `tools/pmp2.sh` (gdb stack samples of the worker),
`tools/lines2json.py` + `tools/refcmp.sh` (reference comparison through
`canonicalize.py`/`compare_taxonomies.py`), `tools/ore_pair.py`,
`tools/chain_*.sh` (the measurement chains as run). Seeds and HermiT
answers stay in `.work/agent-scratch/sameindividual-bridge/{seeds,gold,cseeds,cgold}`.

## Not done

- The default automatic route does not recover any of the five inputs.
- The restricted automaton arm needs a completeness argument for the port's
  link model (the audit misses point at run-time merges that relocate
  links without a restricted re-fire), and the conditional-full schedule
  above 10,000 individuals departs from Konclude's own schedule choice.
- The blocking-candidate scan cost in the subject probes.
- No Lean coverage (the bridge has no Lean model).
