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
