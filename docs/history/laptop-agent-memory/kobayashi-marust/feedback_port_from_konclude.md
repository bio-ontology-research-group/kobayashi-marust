---
name: feedback_port_from_konclude
description: User HARD RULE — for the SHIQ/SROIQ engine, PORT mechanisms from the Konclude source, do NOT invent your own algorithm/heuristic
metadata:
  node_type: memory
  type: feedback
  originSessionId: f75fe881-cb21-41f6-8110-ddbbedcc36b5
---

For the SHIQ/SROIQ engine build ([[project_km_shiq_build]]), the user directs:
**PORT the mechanisms from the Konclude source — do NOT build your own
algorithm/heuristic.** (Stated 2026-06-25 when I was about to write a self-built
inverse→block-mode autorouter.) This applies to blocking, inverse handling,
cardinality, disjunction convergence, saturation caching — base each on
Konclude's actual code, not a textbook theorem or invented heuristic.

**Why:** Konclude is the gold competitor; its optimizations (optimized subset
blocking, saturation caching, disjunction delaying) are what make it fast and
correct at scale. A faithful port inherits that; a hand-rolled approximation
risks subtle unsoundness/incompleteness and won't match performance.

**How to apply:** Konclude source IS on the LAPTOP (reading source is laptop-safe,
no build/run) at `/home/leechuck/Public/software/Konclude/Source/Reasoner/Kernel/Algorithm/`.
The completion algorithm = `CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
Key blocking functions (line numbers approx):
- `isIndividualNodeBlocking` 18923 — dispatcher (calls optimized/subset/equal/pairwise).
- `isLabelConceptOptimizedBlocking` 18484 — the real blocking: B1 = L(w)⊆L(w')
  (`isLabelConceptSubSet`); B2 over inverse edges w→v (v=getAncestorIndividual(w)):
  B2a for ∀r.C / ¬∃ check v's label has the ∀-operands; B2b
  `hasOptimizedBlockingB2AutomateTransitionOperands` 17694 for AQAND automata/
  transitive; B3/B5 at-most cardinality (c-blocked / a-blocked).
- indirect blocking: `PRFINDIRECTBLOCKED` flag (~19003) +
  `reactivateIndirectBlockedSuccessors` 19847 (Konclude DOES have indirect
  blocking — corroborates the indirect-block fix in commit 99a21d1).
Cross-refs: docs/SHIQ-COMPLETION-DESIGN.md (traced file:line), docs/KONCLUDE-STUDY.md.
NB the mode-4 full-label pairwise blocking I committed (99a21d1) is theorem-based
(HST), NOT a Konclude port — supersede/realign it to isLabelConceptOptimizedBlocking.
