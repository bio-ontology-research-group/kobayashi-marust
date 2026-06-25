# Konclude disjunction processing — faithful port spec

Extracted from `Konclude/.../CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
(read-only). Ground truth to PORT (not approximate). See [[feedback_port_from_konclude]].
Companion to docs/KONCLUDE-BLOCKING-SPEC.md.

## The three Konclude mechanisms (and the KM gap)

KM's Ht ALREADY HAS: `PendingDisj` (deferred disjunction records), `eval_disj`
(unit propagation over a disjunction's live set), `push_disj`, DFS + dep-set
BACKJUMPING (`decisions`/`backjumps`/`conflicts`), `KM_HT_LEARN` (CDCL learning,
but documented INERT/broken — node-uid no-goods), `KM_HT_EAGER` (defer global
⊤-disjunctions to UNBLOCKED nodes), `KM_HT_NEGTRIED`, `KM_HT_ORD` (disjunct order),
`KM_HT_BLOCKSKIP`. So dependency-directed backtracking already exists.

The GAP vs Konclude (the convergence lever for 15672 / the disjunction family):

### 1. Trigger-based DELAYED branching — `planORProcessing` (16489)
Konclude does NOT branch a disjunction when it first fires. It:
- scans operands vs the node label → classifies into `containedOperand` (already
  satisfied ⇒ no branch), `firstNot…`/`secondNot…ContainedOperand` (live disjuncts),
  and clashing operands.
- UNIT/SAT (16562): if ≤1 live disjunct or one already satisfied → apply immediately
  (no branch). [KM's eval_disj does this.]
- TRIGGER DELAY (16598): else install a `CConceptRoleBranchingTrigger` — defer the
  branch until a specific trigger concept is asserted or a role successor appears
  (`searchNextConceptRoleBranchTrigger` 17217). The disjunction sleeps until new
  info makes it relevant. THIS is the piece KM lacks (KM only defers to unblocked
  nodes via EAGER, not by per-disjunction relevance trigger). It is "what keeps the
  branch count tiny."
- QUEUE DELAY (16610): if no trigger, re-queue with a priority offset
  (`getPriorityOffsetForDisjunctionDelayedProcessing`) to minimize live disjuncts.

### 2. Semantic branching — `executeORBranching` (16737)
When branching IS needed (≥2 live disjuncts, none satisfied): create N tasks, one per
live operand. Each task (16930) bumps the branching tag, gets a dependency track point,
and ADDS its positive operand. Negated other-operands are added ONLY under
`mConfSemanticBranching` (all) or `mConfAtomicSemanticBranching` (atomic only) — else
left implicit. (KM_HT_NEGTRIED is the nearest existing knob.) 0 live ⇒ clash; 1 live ⇒
single-option (no task).

### 3. Sound nogood cache — `writeClashDescriptorsToCache` (7400)
On a clash, the 3-phase backtrack (`backtrackFromTrackingLineStep` 6976: P1 det
prev-levels, P2 non-det prev-levels, P3 non-det current-level) filters clashes by the
non-det node's PROCESSING TAG (7126) so only clashes derived AFTER the choice are
learned, then writes a nogood — but ONLY if (7427-7498): caching on, single individual
node, NO nominal, NO propagation-type concept, NOT an atomic A∧¬A clash; sorted/
canonicalized (7530). Retrieval prunes a branch before expansion (16895/16903). KM's
KM_HT_LEARN is inert — a correct port of THESE soundness restrictions is the fix.

## Data structures (glossary)
- CDependencyTrackPoint: a derivation point, carries a BRANCHING TAG (decision level)
  + PROCESSING TAG (creation order). Every derived fact is paired with one. (KM ≈ DepSet.)
- CBranchingORProcessingRestrictionSpecification: per-disjunction plan state (first/
  second live operand, contained operand, trigger, accumulated clashes).
- CConceptRoleBranchingTrigger: a deferred-branch condition (a concept or a role succ).
- CTrackedClashedDependencyLine: clash buckets by level (independent / current-level /
  prev-level, det / non-det) → computes the backjump target. (KM ≈ dep-set max-level.)

## Port plan (gated, synthetic-tested, ws build — NEXT work cycle)
1. **Trigger-based delay** is the highest-leverage piece (convergence for 15672 /
   disjunction family). Map `CConceptRoleBranchingTrigger` to KM: a PendingDisj is not
   branched until one of its trigger concepts/roles is present on the node; pick the
   trigger as a not-yet-present operand-related concept. Reuse concept_triggers/
   role_triggers infra. Gate KM_HT_ORDELAY. Synthetic test: a disjunction that becomes
   unit after a later deterministic derivation must NOT create a branch (branch_pushes
   stays 0); a genuinely open one still branches.
2. **Semantic branching**: when branching, optionally add the atomic negated operands
   of the other disjuncts (port mConfAtomicSemanticBranching). Synthetic: earlier clash
   detection / fewer backtracks on a crafted case; result-identical SAT/UNSAT.
3. **Sound nogood cache**: re-do KM_HT_LEARN with Konclude's restrictions (single node,
   no nominal, no propagation concept, non-atomic, canonicalized). Synthetic: a repeated
   sub-conflict is pruned (conflicts drop) with identical verdict.
NB this touches the certified calculus core (what/when derived) → Lean re-cert at the
very end ([[feedback_lean_at_end]]); argue the derived set is unchanged (delay/cache are
search-order + redundancy, fixpoint-preserving; semantic branching adds sound negations).
