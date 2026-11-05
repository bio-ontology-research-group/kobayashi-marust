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

Branch `fix/v155-bridge-satcache` from `development/v1.5.5` at 48a1113b,
worktree `.work/worktrees/fix-bridge-satcache`. Scratch:
`.work/agent-scratch/bridge-satcache/`. Release flags for every measurement:
`KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`.
Binaries (`.work/agent-scratch/bridge-satcache/bin/`, LTO release builds):
`km-base` = 48a1113b, `km-new` = the code of 2cba8fbd (later commits change
docs, results and tests only). `km-trace` and `km-fix1` to `km-fix8` are
non-LTO diagnostic builds of intermediate states (used for traces and
ablations only, never for a timing).

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
- the satisfiable expander cache no longer takes the SELF gate of section 20
  (the associated-expansion cache and the saturated-label expansion keep it).

Each change only refuses a deferral or adds a rule application.
`KM_HT_SATEXP_ABSORB_LEGACY=1` (or `functional`, `top`, `label`, `value`,
`replay`) restores the former behaviour; `KM_BRIDGE_SELF_SATEXP_GATE=1`
restores the gate. A first version also built `≤n R.⊤` without its operand,
as Konclude does; it fixed `nn1116` but made the NN-rule's functional arm run
on those bounds, and five family seeds stopped finishing (`sat346`, `sat181`,
`sat1094`, `sat1496`, `sat1836`; base 0.5 to 12 s). It was dropped.

RESULTS-PLACEHOLDER
