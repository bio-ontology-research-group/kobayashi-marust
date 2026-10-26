---
name: project-km-atmost-rest-port
description: "KM at-most resume port (branchingMergingProcRest, KM_HT_ATMOST_REST) — design, safety argument, validation state"
metadata: 
  node_type: memory
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

# KM at-most resume port (task #20, started 2026-07-08)

`KM_HT_ATMOST_REST` routes `applyATMOSTRule` (u08) through the ported
`CBranchingMergingProcessingRestrictionSpecification` machinery instead of the
legacy re-gather-per-fire spine. Data structures were ALREADY ported
(process/satellites.rs + bm1.rs, arena `restriction_specs` +
`branching_merging_candidate_linkers`, both epoch-managed); this port is the
WIRING. Related: [[project-km-bridge-disjunction-probe]] (3215/541 residual =
at-most search throughput).

## What it does (u08 new fns)
- `ht_atmost_resolve_rest`: resume from `con_pro_des.proc_spec` when it is a
  branching-merging rest (`is_branching_merging` discriminant — the collapsed
  C++ subclass split vs the link-restriction payload); else fresh
  createATMOSTDependency + non-det tp + rest.
- `ht_atmost_initialize_merging_nodes`: scans ONLY links with arena index ≥
  `scan_edge_watermark` (Konclude's history iterator ≡ edge-arena order);
  classifies each successor ONCE: counted → merging candidates linker chain,
  undecided → both_qualify, excluded → dropped. Ports the DISTINCT-CLIQUE
  greedy (cpp 15886–15928/15981–16021): > cardinality pairwise-distinct counted
  successors ⇒ immediate clash with the distinct edges' own deps — no merge
  search (the exponential saver vs legacy pairs-enumeration).
- `ht_atmost_qualify_merge_rest`: choose-branches both_qualify entries one at a
  time (validity re-check drops decided ones), then the pairwise merge spine
  over the PERSISTENT candidate lists (validity filter = merged-away/purged +
  edge intact, dedup by node). Same search tree as legacy.
- Reapply: STATIC descriptor carrying the rest via
  `add_concept_to_reapply_queue_role_restricted_static` (u10), installed once
  per (node, ≤n) under the legacy `is_concept_reapplied` guard.
- u02 advances re-enter the rest spine (`AtMostMergeBranch.rest`); qualify
  advance moves the positively-qualified succ into the candidates
  (cpp 15774–15780).

## Safety argument (the part that took thought)
- Konclude consumes+reinstalls a DYNAMIC descriptor per fire — safe only under
  task forking (per-task queue copies). KM in-place backtracking cannot restore
  a cross-node queue consumption ⇒ consumed-but-not-reinstalled = permanently
  disarmed ≤n = wrong SAT. Hence STATIC descriptor + in-place rest.
- Rest mutations roll back at branch points FOR FREE: `restriction_spec_mut`
  routes through `Arena::get_mut_journaled` and merge/qualify branch points
  always own a journaled epoch — the rest and the edge arena roll back
  TOGETHER, so `scan_edge_watermark` can never exceed the live arena (belt =
  defensive clamp). No per-branch snapshot, no generation counter needed.
- `ht_with_atmost_rest` (mem::take → mutate → put back) must not span an epoch
  push (documented; put-back would journal the placeholder).
- Rest-list leaks under failed OR alternatives (plain mode, no epoch) are the
  same accepted defect class as label/merge leaks — covered by the poison
  framework, not new.
- Choose-TRIGGER deferral (cpp 15934+, `CConceptRoleBranchingTrigger`) is the
  UNPORTED half — needs absorption-side trigger precompilation; would kill the
  eager 2-way branch per undecided successor. Next milestone if profiles say
  branching (not scanning) dominates.

## Validation state (2026-07-08)
- 4 selftests added (`atmost_rest_*` in completion/selftest.rs): distinct-clique
  clash (functional + qualified), reapply-resume-merge (∃R.C + ≤1 then ∃R.D →
  re-fire merges to ONE successor), choose-on-undecided.
- Dev-tree build+suite on IBEX: /ibex/scratch/hohndor/km-dev (job 48398190) —
  keeps production binaries untouched while panels run.
- NOT yet: oracle 6-mode matrix with flag on, A/B vs legacy on 3215/541
  probes, default-on decision.

## Complex-qualifier choose-trigger port: PARKED with analysis (2026-07-09)

Scoped during the unsatcache-48454415 wait; BIGGER than the "240 lines" note:

1. **The trigger list on a ≤n concept does NOT come from CBranchTriggerPreProcess.**
   The use site (cpp 15832-15835) reads `conProData->getConceptRoleBranchTrigger()`
   from the ≤n CONCEPT's process data. CBranchTriggerPreProcess only fills the
   MBox branchingTriggerVector for CCOR(pos)/CCAND/CCEQ(neg) concepts. The ≤n
   triggers come from the ABSORBER
   (`CTriggeredImplicationBinaryAbsorberPreProcess::
   createCardinalityQualificationPartialAbsorbedTriggers`) — a second, larger
   preprocess (partial absorption of the qualifier into CCIMPLTRIG cascades).
2. **CBranchTriggerPreProcess mechanics** (for when we port it): flatten the
   disjunction (pos-OR / neg-AND/EQ recursion); per flattened disjunct:
   negated CCSUB/CCATOM -> concept trigger (atom, positive); ∀/¬∃/≤/¬≥ ->
   ROLE trigger = fresh CCIMPLTRIG concept added to the role's DOMAIN list
   (stamped on every edge SOURCE at link install) — the readiness signal
   that the restriction became live.
3. **UNRESOLVED install-target question (completeness-critical)**: cpp 15954
   installs the ATMOST-reactivation hook on
   `processIndi->getConceptReapplyQueue(triggeringConcept, triggerNegation)`
   (the PARENT), for a trigger that `containsIndividualNodeConcept(succIndi,..)`
   found ALREADY CONTAINED on the SUCCESSOR — both facts look inverted vs the
   obvious "fire when the trigger lands on the successor" reading (which is
   what our all-atomic port does, validated). Fire path (cpp 26492+,
   applyExtendedReapplyConceptDescriptor) is fully understood + already ported:
   reads (parent, link) from the descriptor, records the link in the parent's
   SuccessorIndividualATMOSTReactivationData, re-fires the ≤n via the role
   reapply queue; the resumed scan walks exactly the reactivated links
   (cpp 15852-15877, the newTriggeredSuccLinker merge into the link loop —
   this RESUMED-SCAN half is NOT yet in our u08 port). DO NOT port the install
   on a guess: wrong target = hook never fires = undecided successor never
   counted = wrong SAT. Next step: read CReapplyConceptLabelSet::
   getConceptReapplyQueue + insertConceptReapplication semantics in
   Source/Reasoner/Kernel/Process/ to settle whose label set drains the queue.

### Update (same day, source reading): install-target puzzle PARTLY resolved
- `CReapplyConceptLabelSet::getConceptReapplyQueue` (Process/CReapplyConceptLabelSet.cpp
  422-460): per-NODE label-set queue, keyed by concept TAG, POS+NEG MERGED
  (`mPosNegReapplyQueue`; the polarity split is commented out — polarity
  filtering happens per-descriptor at drain). Queue drains on concept-add to
  the HOLDING node. So the cpp 15954 parent-install is INTENTIONAL: the hook
  fires when the trigger concept is later added to the PARENT.
- For that to signal "successor's Q-status may have changed", the cardinality
  triggers must be BACKWARD-PROPAGATING absorption stages (successor satisfies
  part of Q → cascade → inverse-role ∀ delivers the trigger to the parent).
  `createCardinalityQualificationPartialAbsorbedTriggers` (absorber cpp
  1083-1100) = per qualifier operand `getSimpleBranchTriggersForConcept` else
  `getBranchTiggers(getPartialTriggersForConcept(concept,negated))`.
- NEXT READING TARGET to unblock the port: `getPartialTriggersForConcept` +
  the trigger-implication cascade construction in
  CTriggeredImplicationBinaryAbsorberPreProcess.cpp — confirm the final stage
  is an inverse-∀ onto the counting role delivering the SAME trigger concept
  the use site keys on, then the port shape is: absorb qualifier → trigger
  cascade in bridged tbox + hook on the PARENT keyed by the final trigger +
  the resumed-scan half (cpp 15852-15877 newTriggeredSuccLinker walk) in u08.

### CLOSED (2026-07-09): complex-qualifier choose-trigger = suspected KONCLUDE BUG; KM keeps eager choose
- Trigger construction read end-to-end: `getSimpleBranchTriggersForConcept`
  (absorber cpp 4235) = atomic operand -> the atom itself (positive);
  role-restriction operand (∀/¬∃/≤/¬≥) -> role-DOMAIN trigger concept of the
  INNER role (lands on whichever node acquires an edge of that role).
  `getPartialTriggersForConcept` (cpp 4257) = CCIMPLTRIG unfolding cascades,
  SAME-NODE semantics. All triggers are SUCCESSOR-side readiness markers.
- The use site (cpp 15949-15957) installs the ATMOST-reactivation hook on
  the PARENT's per-tag reapply queue (`processIndi->getConceptReapplyQueue`)
  for a trigger found contained on the SUCCESSOR. Queue drains only on
  concept-add to the HOLDING node (settled earlier). The parent never
  receives a successor-side marker => hook ~never fires.
- Exhaustive check: `addReactivationSuccessorIndividualLink` has exactly ONE
  writer (the fire path) and `SuccessorChoiceTriggeringInstalled` has NO
  fallback reader — a choice-triggered successor that never fires is
  PERMANENTLY skipped by the ≤n scan (not merged, not qualified).
  => suspected genuine Konclude bug (`processIndi` for `succIndi` slip),
  signature = under-detected unsat / wrong-SAT on ≤n with NON-ATOMIC
  qualifiers whose undecided successors carry a partially-matched trigger.
  Same defect class as the contested-gold onts where HermiT beats Konclude
  (8941 under-detected-unsat family) — candidate explanation to test.
- KM DECISION: keep the eager qualify-choose for complex qualifiers (our
  current behavior — COMPLETE); all-atomic deferral (0c5848f) stays. Nothing
  sound to port; a successor-side reinvention has a subtle completeness gap
  for ∀-disjuncts (X-status changes on the successor's OWN successors do not
  re-stamp the domain trigger) and wrong-SAT risk. Investigation CLOSED.
