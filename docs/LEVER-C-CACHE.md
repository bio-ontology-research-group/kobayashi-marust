# Lever C — successor-subtree saturation cache (the throughput-giant lever)

Status: design + code grounding (2026-06-25). Implementation = next focused
session, synthetic-test-first on ws, no giants mid-build (build-first rule), Lean
re-cert at the very end.

## The problem (re-confirmed from code + docs/THROUGHPUT-SATURATION.md)

P2.1 (`KM_HT_QO_SHIQ`) already makes the saturation SOUND for `∀`: under `shiq`,
`apply_head`'s `∃`-case (`hypertableau.rs:4370`) creates a **non-shared** successor
`f` owned by its source `n` (`qo_parent[f] = Some(n)`, `is_filler[f]=true`), so a
`∀R.C` write lands on an independent node — no shared-filler pollution, no
`qo_insufficient`. Expansion is bounded by ancestor subset blocking `qo_blocked`
(`:3351`, B1 `label[f] ⊆ label[ancestor]`).

The remaining wall is purely cost:
- **Global single pass** holding ALL named concepts' non-shared trees at once =
  ×#concepts memory -> 27 GB OOM on 7914 (blocking bounds DEPTH, not BREADTH).
- **Per-concept** `saturate(&[pos(A)])` (`:3301`) is memory-fine (~490 MB) but
  re-expands every successor subtree from scratch for each of the ~17-58k concepts
  -> orders-of-magnitude too slow (the "DECISIVE SCALE FINDING": >600 s on 7914/9724).

The two existing successor subtrees that recur across concepts are NOT reused. That
reuse is the missing lever (= Konclude `tryEstablishSaturationCaching`).

## The mechanism to build

A **content-addressed successor-subtree cache**, consumed in the per-concept
`saturate` path (the memory-bounded one):

1. **Key.** When `apply_head` `∃` creates a fresh successor `f` (`:4395`), its
   eventual saturated content is a function of `f`'s *initial forced label* — the
   filler concept `fil` PLUS every concept later written onto `f` by a `∀R.C` from
   its parent BEFORE `f` expands its own existentials. So the cache key must be the
   *complete* set of concepts forced on `f` by its creation context, captured at
   the point `f` becomes stable-but-unexpanded. Canonicalise to a sorted `Vec<CLit>`
   (or a 64-bit commutative signature + exact-set tiebreak, cf the mode-3
   `i3_signature`).

2. **Value.** The subtree's saturated summary: `f`'s final label (its subsumer
   set) + CLASHED/CLEAN status + the labels its own successors contributed back to
   `f` (for the parent's reads). Store `key -> summary`.

3. **Reuse.** Before expanding a fresh `f` whose key is already cached, splice the
   cached summary onto `f` instead of re-running its subtree fixpoint. Idempotent
   because the key captures all forcing.

## The soundness subtlety (do NOT skip)

A subtree is **not** purely a function of `f`'s forward label when inverse roles are
live: a `∀R⁻.C` operand propagates BACKWARD from `f` to its parent, and a backward
edge can make `f`'s saturation depend on the parent/seed context. Two sound options:

- **(S1) Forward-only cache.** Cache only subtrees with no inverse-backward operand
  reaching the parent (detect via the same inverse-bridge / `∀r⁻` machinery the
  QoSat path already tracks). Sound always; covers the inverse-inert majority
  (7914's hard core is small; 9724's inverse is composed away by INVCOMPOSE first).
- **(S2) Context-extended key.** Fold the relevant parent-edge + backward-operand
  context into the key so two creation contexts share a cache entry only when their
  inverse-relevant context matches. Larger key, broader hit rate; the Konclude-exact
  form.

Start with **S1** (smallest sound increment, measurable hit rate), then extend to
S2 if S1's hit rate is too low on 7914/9724.

## NOT the inert cache

This is DISTINCT from the self-node `(concept,neg)` cache that session 6g found
architecturally inert: that was the SHARED global forward pass, where each
`(concept,neg)` is saturated exactly once per classification (zero within-run hits).
Here the unit is the **successor subtree** in the NON-SHARED per-concept pass, which
genuinely recurs across the tens of thousands of per-concept saturations -> real hit
rate. (satcache3, the prior attempt, keyed self-nodes / the shared pass — not this.)

## Build plan (incremental, each step ws synthetic-tested)

1. Synthetic regression test locking P2.1's current sound non-shared `∀+∃` verdicts
   (the cache must preserve these byte-for-byte) — `KM_HT_QO_SHIQ` on a tiny KB.
2. Cache key + store + reuse for S1 (gated, e.g. `KM_HT_QO_SUBCACHE`); a
   `*_CHECK` mode asserting cached-splice == full-expansion (result-identical),
   as the incr-blocking work did.
3. Measure hit rate + wall on 7914 (smallest hard member) isolated (`km tableau`
   on a dumped TIN, group-safe). Target: per-concept pass within budget.
4. If S1 hit rate too low, extend to S2 (context-extended key).
5. Only once a member classifies sound+fast: full corpus sweep (rare, unimatrix)
   + Lean re-cert of the affected saturation rules.

Code anchors: `saturate` `:3301`, `apply_head` `∃`-shiq `:4370`, `qo_blocked`
`:3351`, `new_node`, `qo_parent`. Isolated run recipe: `KM_DUMP_TIN=t.json km
classify <ont>` (kill after TIN written) then `km tableau < t.json` under
`KM_HT=1 KM_HT_FORCE=1 KM_HT_QO=1 KM_HT_QO_SHIQ=1 ...`, group-safe.
