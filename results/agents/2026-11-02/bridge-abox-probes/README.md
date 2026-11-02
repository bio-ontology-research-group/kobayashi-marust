# Restricted automaton arm, probe cost, and `SameIndividual` on the default route (agent `bridge-abox-probes`, 2026-11-02)

Branch `fix/v155-bridge-abox-probes` (from development/v1.5.5 92fcfb7d),
worktree `.work/worktrees/fix-bridge-abox-probes`. Design argument:
docs/HYBRID-CB-HT.md section 14; routing note in docs/ROUTING.md (typed-ABox
section). Measurements on ws, `KM_THREADS=1`, release flags
(`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1`), `--lines`,
`timeout 240`, peak RSS from `/usr/bin/time -v`; ws shared with other agents
(load 15 to 45). Binaries in `.work/agent-scratch/bridge-abox-probes/bin`
(`km.base0` = 92fcfb7d, `km.fix7` = the branch's final code).

## Outcome

The four inputs answer on `km classify` with no switches, each with the
Konclude reference taxonomy:

| input | Konclude | before (92fcfb7d, default) | after (branch, default) |
|---|---|---|---|
| 16315 | 22 s | timeout, 18.0 GiB | **24 s, 1.33 GiB** |
| 10838 | 21 s | timeout, 18.0 GiB | **59 s, 2.36 GiB** |
| 3087 | 20 s | timeout, 18.0 GiB | **61 s, 2.49 GiB** |
| 7557 | 52 s | timeout, 18.0 GiB | **97 s, 4.02 GiB** |

"Before" is the measurement of the previous agent on the same base code
(`results/agents/2026-11-01/sameindividual-bridge/data/final_auto_*`): the
generic racer declined `SameIndividual`, the CB stack ran into its memory
plateau. "After" is `km.fix7` (`data/fix7_*.summary`, traces
`data/fix7_*.err.gz`); reference agreement through `tools/refcmp.sh`
(canonicalize.py + compare_taxonomies.py against
`v150-refs/classification-audit-53234885/<chunk>/ore_ont_<n>/`):
`konclude=True` for all four (`data/fix7-four-refcmp.txt`). All four stay
under 120 s on ws.

## 1. The restricted automaton arm

Cause of the reported misses. There was no missed operand. The transient
audit of the previous agent (`KM_HT_AUTOMAT_REST_LINK_AUDIT=1`) compared the
two arms in the middle of a run, at each restricted re-fire. An operand that
the full arm would add there to another successor is either still due from
that successor's own re-fire, or belongs to a run that ends in a clash (the
seeds it named, c0 and c190, are inconsistent for HermiT, and the misses
fire on nominal hubs just before the clash). That audit cannot separate
these from a real gap, so it is the wrong test. The right one checks the
graph the arm leaves behind.

The check. `KM_HT_AUTOMAT_CLOSURE_AUDIT=1` (u10
`ht_automat_closure_audit`, called at every clash-free fixpoint of u02
`run_completion_on`) tests that the graph is closed under the
all-successors arm: for every live node, every automaton state (walked as
`apply_automat_transactions` recurses), every plain `∀`, and every live
neighbour the full arm reaches, the operand is in the neighbour's label.
Results (`data/closure-*.tsv`; columns: file, route, fixpoint runs, misses,
exit):

| pool | seeds | bridge runs with a clash-free fixpoint | misses |
|---|---|---|---|
| chain seeds (`gen_chain.py`, previous agent) | 2,000 | 1,804 | **0** |
| new merge families (`tools/gen_rest.py`) | 2,000 | 1,781 | **0** |
| negative control: chain seeds 0-299 with the restricted re-fire dropped (`KM_HT_AUTOMAT_REST_LINK_DROP=1`) | 300 | 274 | misses on **113** seeds |

The automatic route on these seeds answers through saturation without a
completion fixpoint, so its rows have no checks. The first version of the
check also counted purged targets (nodes pruned by a merge), 9 seeds of the
new families, all with target flag `PRF_PURGEDBLOCKED`: the full arm writes
into their stale labels, the model does not contain them, and
`ht_rule_target_of_link` skips them too. The check now skips merged and
purged targets (`closure-m-rl1.tsv` is the first version, `closure-*-fix3.tsv`
the final one, with the arm on by default).

New seed families (`tools/gen_rest.py`, seed mod 4): (0) a functional role
under a transitive role or inside a chain, with two successors that must
merge; (1) anonymous successors forced onto a nominal; (2) `≤1 r`
(qualified and unqualified) and inverse-functional roles merging
successors and predecessors that carry their own chain edges; (3) hubs under
at-most restrictions merging ABox individuals, with `DifferentIndividuals`.
All with universal restrictions over transitive roles, chains and inverses,
optional `SameIndividual`. HermiT: 1,784 consistent, 216 inconsistent.

The argument (docs/HYBRID-CB-HT.md 14.1): a state's first processing runs
the full arm and registers the state in the reapply queue under each
transition role; every production link install (u08
`ht_install_role_successor_edge`, u10 `create_new_individuals_links_reapplyed`
and `create_new_individuals_link_reapplyed`, merge relocation through u08,
the ABox assertion install through u10) fires the queue of the endpoint
that reads the link as that role; the non-reapplying installs of u35 have no
production caller; merges move labels with links; backtracking restores
graph, labels and queues together. The arm is on by default
(`KM_HT_NO_AUTOMAT_REST_LINK=1` restores the all-successors re-fire).

## 2. Subject-probe cost

Profile (gdb stack samples of the HT worker, `tools/pmp.sh`; `perf` is not
installed on ws), three defects in turn:

1. `data/pmp-base-10838.txt`: 19 of 25 samples in
   `get_anywhere_blocking_individual_node_canidate_hashed`, 15 in
   `ProcessContext::node_mut`, 6 in `pop_branch_epoch`. Read-only label and
   role-hash reads went through `node_mut`, which journals a copy of the node
   under the job's epoch; 32 such reads replaced by shared borrows (same
   value). 10838 with the switches: timeout to 152 s.
2. `data/pmp-fix2-7557.txt`, `data/blocking-scan-trace-7557.txt`: the lazy
   anywhere-blocking hash started every job with `max_valid=1` and walked
   all 119,132 base ids per initialization concept (0.1 s per scan). Fix: a
   `BlockingBaseIndex` built once at the retained base (0.07 to 0.21 s) seeds
   a job's fresh entry as a shared list; the iterator merges it with the
   job's map in key order.
3. `data/pmp-fix6-7557.txt`: after (2), 22 of 27 late samples in
   `cache_satisfiable_individual_nodes`, which offered every base id to the
   satisfiable caches after every probe. Konclude skips a cached base in this
   sweep; the bridge now does so after the first job. 7557: 189 s to 97 s.

`KM_HT_BLOCKING_SCAN_TRACE=1` prints the bounds of each long scan.

## 3. Schedule decision and admission

`native_conditional_full_abox_profile` now evaluates Konclude's whole
full-completion-graph decision (exclusion: at least 300,000 individuals or
50 individuals per concept; suggestion: fewer than 10,000 individuals or
fewer than 5 per concept), with the bridge's concept-name count; role-free
ABoxes of 10,000 or more individuals keep the independent-component
schedule. Argued in docs/HYBRID-CB-HT.md 14.3: both schedules are
complete-or-defer, and the bridge has no counterpart of Konclude's lazy
alternative. `orchestrate/race.rs` admits `SameIndividual` (the exact
pre-merge) on the automatic racer; `KM_HT_NO_ADMIT_SAME=1` restores the
decline. No rule of the general routing policy changed.

## A pre-existing incompleteness found by the new seeds (not fixed)

`data/min/m413-min.ofn` (minimized from `m413`, 10 axioms; no
`SameIndividual`):

    TransitiveObjectProperty(:t)
    SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)
    SubObjectPropertyOf(:f :r)
    FunctionalObjectProperty(:f)
    ObjectPropertyAssertion(:s :i3 :i2)
    ObjectPropertyAssertion(:t :i2 :i0)
    ObjectPropertyAssertion(:f :i3 :i0)
    SubClassOf(:B ObjectSomeValuesFrom(:f ObjectOneOf(:i3)))
    SubClassOf(:B ObjectSomeValuesFrom(:f :B))
    ClassAssertion(ObjectAllValuesFrom(ObjectInverseOf(:t) :D) :i3)

HermiT entails `B ⊑ D`: a `B` element's `f`-successor is `i3` and is a
`B`, so `i3` has `f`-successors `i3` and `i0`, which merge; then `t(i2,i3)`,
`r(x,i3)` and `s(i3,i2)` give `t(x,i3)`, and `∀t⁻.D` at `i3` gives `D(x)`.
The automatic route and the forced bridge omit it, on the base (92fcfb7d)
and on the branch alike, with the restricted arm on or off. With
`KM_BRIDGE_NO_PRECOMPUTATION_REPLAY=1` or `KM_BRIDGE_FRESH_ENV=1` the bridge
finds it, so the loss is in the reuse of the consistency model (the class
of section 10 of docs/HYBRID-CB-HT.md): a probe-time merge of two ABox
nominals (`i0` into `i3`, or the reverse) whose neighbour `i2` is kept by the
representative replay without its edge to the merged-away nominal. Konclude's
merge (cpp 21155-21178) expands such a nominal neighbour from the backend
cache before relocating the links; that sub-block is a recorded deferral of
the port (u15 merge phase 5, "the nominal neighbour backend-expansion
sub-block remains deferred"). This is the first lead for the fix; it is not
part of this branch.
