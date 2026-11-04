# bridge-nn-term: termination and search cost of the NN-rule port

**Status (2026-11-04 23:55, continuation by a second agent).** The first
agent committed the fix (7ae078c3, 68a1b917) and section 24 with the results
so far (5b50db3a), then stopped. Done at that point: the seven seeds (three
runs per route, 120 s cap), the NN family (2,000 seeds, three runs, both
routes), the 16 held-out inputs and the 112 nominal design-half inputs, all
with `km-new` (= `engine/target/release/km` of 68a1b917). Not done: the 20
runs per route of the target seeds and reductions, the differential pools
(only one pool of the "after" run had started), the test suites, and the
sections below marked TBD. Open findings: `nn1153` (both routes) and `nn568`
(automatic) lose answers that 48a has; `nn1333` stays about ten times slower
than the base; section 24's termination argument defers the bound on nominal
levels to the SROIQ proof. The continuation's results replace the TBD
sections below.

Branch `fix/v155-bridge-nn-term` from `development/v1.5.5` at 48a1113b,
worktree `.work/worktrees/fix-bridge-nn-term`. Scratch:
`.work/agent-scratch/bridge-nn-term/`. Release flags for every measurement:
`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`.
Binaries (`.work/agent-scratch/bridge-nn-term/bin/`, release profile with
LTO unless noted): `km-base` = 1ffee4a6 (the bridge-nn-rule agent's base,
before the NN-rule; `../bridge-nn-rule/bin/km-base`), `km-48a` = 48a1113b
(byte-identical to the bridge-nn-rule agent's `km-new`), `km-new` = the code
of 68a1b917. `km-v1` to `km-v11` are non-LTO experiment builds
(`buildfast.sh`).

The argument for every change is in docs/HYBRID-CB-HT.md section 24.

## Infinite or exponential, and why

Exponential, not infinite, on every input measured; but the 48a procedure had
no bound. The seven seeds on 48a with a 120 s cap (`data/seven/n48.tsv`,
one run): `nn346` 91 to 100 s, `nn1333` 95 s, `nn952` 58 s, `nn745` 30 to
38 s, `nn969` 8 s (auto) and 36 s (`ht_bridge`); `nn1957` and `nn777` over
120 s (`nn777` `ht_bridge`: the bridge defers at its 60 s budget). With the
NN trace, `hang952` ends after 25 s and its new nominals keep ids below 1050.

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
   `n745min` (five axioms) the 48a binary needs 13.5 s and 30.5 s (the
   latter is the 30 s verification budget), and with
   `KM_BRIDGE_NO_LEAF_REUSE=1` both answer in 0.03 s.

Konclude 0.7.0 answers all seven seeds in 14 to 75 ms of classification time
and agrees with HermiT on each (`data/konclude/`). The bridge-nn-rule
README's "Konclude does not finish" was the default worker count: Konclude
hangs at 0 % CPU on this host even on a one-axiom ontology; `-w 2` works.

## The fix (commits)

- 7ae078c3 fix(bridge): Konclude's per-candidate NN-rule decisions, fixed
  distinct set with slot budget, leaf jobs end on unattributed clashes
- 68a1b917 fix(bridge): NN distinct set follows merged representatives;
  regression target bridge_nn_term
- final commit: docs section 24, this README, data

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

Termination argument: section 24 (per restriction at most `n` new nominals
per branch line; the rest follows the SROIQ argument).

## The seven seeds, before and after (`data/seven/`, 120 s cap)

TBD

## The NN family (2,000 seeds, three runs, both routes)

TBD

## Differential pools

TBD

## The 16 held-out inputs

TBD

## The 112 nominal design-half inputs

TBD

## Tests

TBD

## Not done

TBD
