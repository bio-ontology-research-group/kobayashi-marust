# 2b — Konclude-style sound inverse saturation (KPSet G1/G2/G3) for the QO gate

Status: design (not implemented). This is the lever that takes the QO sound+complete
path on inverse onts from "under budget" (2a, ~tens of seconds) to **Konclude speed**
(~10s on 7581). It is a core-saturation extension, not a routing tweak.

## Why it is needed (measured, 2026-06-23, ore_ont_7581 on ws)

The QO fast path classifies via a forward-only global saturation in ~10s (gold-exact,
matches Konclude's saturation core). The *certified-complete* path adds a verify
funnel (forward L + structural suspects + per-concept inverse de-conflation +
complete-tableau verify of the tight candidates). 2a parallelised that funnel under
the 240s budget. But every certified path is bounded by one fact:

**KM's inverse-aware saturation is fundamentally expensive.**
- Forward-only global pass: ~10s.
- Inverse-augmented global pass: **111s** — it builds a 6.5M-fact model.
- Per-concept inverse: cheap on average (~1.7ms) but pollutes; the candidates it
  yields are the HARD pairs (~1-2s each to verify).

Root cause: KM's EL-style completion reads a shared filler's **runtime label** across
edges (the NF4 backward-link rule `∃r.D ⊑ E`). That is sound for forward EL (the
filler's label is its concept's global closure). But an inverse-bridge clause
`r1(x,y) → r2(y,x)` adds a back-edge `filler → r2 → predecessor`; the NF4 rule then
reads the *predecessor-specific* label across it, and because the filler is **shared**
across all predecessors that have `∃r1.filler`, the read conflates them — the 6.5M
spurious facts. Forward-only sidesteps this by dropping the inverse edges, which is
why it is the only fast saturation.

This is exactly the invariant Konclude maintains and KM violates.

## Konclude's mechanism (verified vs /tmp/Konclude source; see docs/KONCLUDE-STUDY.md)

ONE non-branching approximation saturation over the TBox, shared nodes, kept sound by:
- **G1** subsumers of a concept are read from its OWN self-node, never a shared
  successor (`CPrecomputedSaturationSubsumerExtractor`).
- **G2** from a successor, propagate only STATUS flags (sat / clash / insufficient),
  never concept labels — so a shared filler cannot conflate its predecessors.
- **G3** a ∀-forward / ≤n-merge / open-⊔ write that a node cannot soundly absorb marks
  it INSUFFICIENT (`isCriticalALLConceptDescriptorInsufficient` →
  `setInsufficientNodeOccured`). KPSet carries a 3-valued certain/possible/absent set.

Only INSUFFICIENT concepts reach the complete tableau (≈0 for 7581). The inverse
contributes through the tableau's **tree** expansion (bounded by blocking) for that
residue, never through dense back-edge label propagation in the saturation — so the
saturation stays forward-only-fast.

## STATUS 2026-06-23: Phase A (containment check) IMPLEMENTED + measured

`KM_HT_QO_KPSET` (gated, default off; 129 cargo tests incl. two new KPSet tests).
The port of Konclude's `isCriticalALLConceptDescriptorInsufficient`
(CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp:3451): KM now
KEEPS the inverse-bridge clauses (creates the back-edges, recorded in
`inv_edges`), but every concept-head write whose firing matched an inverse
back-edge becomes a **containment check** instead of a write (`kp_check_head` /
`kp_write`), re-evaluated at the saturation fixpoint (`kp_finalize`, Konclude's
post-pass `checkCriticalIndividuals`). A miss raises `kp_insufficient`; nothing is
written across a reversed edge, so the cross-concept shared-filler conflation
cannot form.

**Measured on ore_ont_7581 (ws):** the inverse-AWARE KPSet pass no longer blows
up — it runs at forward-only cost (whole `km classify` 37s / 1.0 GB, vs the old
inverse-augmented 111s / 6.5M-fact pollution). SOUNDNESS confirmed: it never
over-derives (unit tests + it falls back to the gold-exact forward-only result,
565317 = gold, 0 unsound / 0 incomplete).

**But it does NOT yet certify 7581.** `kp_miss = 929558` over `inv_edges =
898356`: KM's cb_to_ht encodes each inverse role as a materialised reversed edge
(`r1(x,y) → r2(y,x)`), and the 129k NF4 existential-subsumption clauses
(`∃r2.D ⊑ E`) then fire across those back-edges at the SHARED filler nodes,
producing ~930k predecessor-dependent consequences that are not forward-present
(all spurious, since NOINV = gold). The containment check correctly refuses to
write them (sound) — but the single global `kp_insufficient` bool is too coarse:
one missed check at any shared filler defers the WHOLE classification. So KPSet
defers and the pipeline falls back to forward-only (gold-exact, fast).

Konclude reaches insufficient ≈ 0 here because it does NOT materialise reversed
edges that trigger forward existential-subsumption at shared fillers; its inverse
is a backward-∀ annotation over forward links, and the residual possible-subsumers
are pruned by the **KPSet 3-valued possible set + pseudo-model merge**
(`isPseudoModelSubsumerPossible`, study doc P2) BEFORE any tableau test — not by a
global flag. So the remaining work to certify 7581 fast is:
  1. **Per-node insufficiency** (`HashSet<Node>`, not a global bool) so CLEAN
     query concepts certify while only genuinely-affected ones defer; and
  2. **Per-concept possible-subsumer tracking + pseudo-model-merge refutation**
     (study doc P2) to prune the ~930k spurious possible-subsumers cheaply, so the
     tableau residue is the few genuinely load-bearing pairs (≈ 0 for 7581).
Both are Konclude ports, not new research.

**Per-node granularity MEASURED INSUFFICIENT (2026-06-23).** Added per-node
insufficiency (`kp_insuff_nodes`) + a probe: a query concept is unaffected iff its
self-node does not forward-reach any insufficient node (NF4 propagates
filler→predecessor, so reverse-reach over `in_edges` marks every affected
ancestor). Result on 7581: **0 / 72989 concepts CLEAN** (`insuff_nodes = 36495`,
half the model; every query concept reaches one). So per-node + subtree-reachability
recovers nothing — the conservatism is total. This rules out item (1) as a
standalone lever and confirms item (2), the **pseudo-model-merge refutation of
per-concept possible-subsumers**, is the actual remaining port. Konclude refutes
`A ⊑ B` by a linear sorted-map merge (a deterministic concept of B's model absent
in A's ⇒ not subsumed; a role-cardinality-interval clash ⇒ not subsumed) — it does
NOT use subtree reachability, precisely because reachability is this conservative.
The ~930k possibles become possible-subsumers that the merge prunes cheaply; for
7581 (forward = gold) every one is refuted ⇒ residue 0 ⇒ certified fast.

## Implementation plan for KM (`engine/src/hypertableau.rs`, `QoSat`)

**Phase A — certain/possible label split + status-only reads (G1/G2).**
Give each node label a two-part split: `certain` (facts independent of which
predecessor reached the node — its concept's told + global Horn closure) and
`possible` (facts written via ∀/range/inverse from a *specific* predecessor). The
NF4-backward / ∀ rules read only `certain`. A derivation that would require a
`possible` fact at a successor marks the *reading* node INSUFFICIENT for that operand
instead of deriving it as certain. Inverse back-edge writes land in `possible`, never
`certain`, so they never propagate to other predecessors of a shared filler — the
6.5M conflation cannot form, and the saturation stays ~forward-only speed.

**Phase B — insufficient → complete-tableau residue (G3).**
Reuse the existing `qo_insufficient` plumbing and the per-concept complete-tableau
verify already wired behind `KM_HT_QO_VERIFY`: route only the concepts that Phase A
marked insufficient to `consistent(A ⊓ ¬B)`. The difference from 2a: the residue is
the *genuinely* insufficient concepts (small — 0 for 7581's inert inverse), not the
72,989 structural suspects, so the per-concept inverse de-conflation pass disappears
entirely.

**Phase C — KPSet 3-valued refinement (optional).**
Full possible-set tracking (certain / possible / absent) per node for a tighter
residue, matching Konclude's KPSet. Only needed if Phase A's binary split leaves too
large an insufficient set on some ont.

## Soundness + completeness

G1+G2+G3 are Konclude's certified saturation invariants. Reading only `certain` labels
never over-derives (sound); everything not soundly decided in the saturation is marked
insufficient and decided by the complete tableau (complete). Result = sound+complete,
identical truth to the current funnel, computed without the 6.5M pollution. The
forward-only gate is the special case "no possible facts, no insufficiency", so its
gold-exact behaviour is preserved by construction.

## Expected payoff

- 7581: ~10–15s (insufficient ≈ 0; saturation ≈ forward-only), matching Konclude.
- Generalises soundly to the SHIQ-without-live-disjunction class (the CB-timeout
  giants), not just inverse-inert onts.

## Risk / effort

Multi-day. It rewrites the core NF4 / ∀ propagation in `QoSat` to track
certain/possible and emit insufficiency rather than pollute. Validation: the
forward-only gate must stay gold-exact (it is the certain-only case); 7581 must reach
~Konclude speed with insufficient ≈ 0; full QO-routed corpus regression
(unsound/incomplete must not move). Re-derive the soundness argument against
docs/KONCLUDE-STUDY.md before any default-on.
