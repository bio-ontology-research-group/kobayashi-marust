# konclude_ht — current state & next steps

A direct, function-by-function Rust port of Konclude's hypertableau reasoning
kernel, incorporated as a self-contained KM module. This file is the at-a-glance
status; `PORT.md` holds the full wave-by-wave history (W0-W555) and the per-unit
status table. **License note:** Konclude is LGPL; this is a derivative work —
LGPL headers + attribution still need to be added (see Next steps §6).

_Last updated 2026-07-06. HEAD `d64e78b` on branch `payg-strategy` (pushed)._

> **First ORE timeout ontology closed by this port: ore_ont_12653, sound +
> complete in 1.0 s via the bridge (`d64e78b`; production km times out on it).
> Per-ontology solving recipes and the family diagnosis table live in
> [`docs/SOLVED-ONTOLOGIES.md`](../../../docs/SOLVED-ONTOLOGIES.md).** Bridge
> milestones: deterministic completion (`5099d52`, 10 port gaps closed);
> coverage wave = domain/range at link install + inverse-role hierarchy +
> first-class qualified `≥n/≤n` from `card_defs` (`d64e78b`); read-off
> soundness gate (`or_branch_open_count` — backtrack-free is NOT
> deterministic; 86 spurious on 3215 under the old gate). Diagnosed frontier:
> 541 needs the u29 dependency-directed backjump (chronological search is in
> a ~2^56 space, nodes flat); 7914 and the giants need blocking/lazy-∀ (46k
> nodes, drive cap); 3215 needs per-subject databox reuse (speed, not
> correctness).

## What it is

~100k LOC across 175 `.rs` files under `engine/src/konclude_ht/`, wired into
`lib.rs` (`pub mod konclude_ht;`). The entire Konclude kernel was translated
structurally (model + process + completion[36 units] + saturation[12 units] +
cache + task + calculation), then progressively brought to life. It is now a
**running, test-validated reasoner** for a usable fragment, not just a compiling
skeleton.

For strict function-by-function Konclude parity, the port is roughly **72-75%
ported/live** by function/unit surface, with roughly **25-28% remaining**. This
is deliberately more conservative than a raw architecture/LOC estimate because
many compiled units still carry explicit in-method deferrals.

Current source markers after W555: `715 W6-DEFER`, `652 W3-DEFER`,
`221 PORT-PENDING`, `106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`,
and `4 W8-DEFER`.

## Current state

### Works, and is tested (1183 `konclude_ht` tests, all green locally)
- **ALC consistency**: conjunction (`⊓`), disjunction (`⊔`) with **branch
  creation + SOUND same-node backtracking** (8796e2f: the OR push snapshots the
  node's label set + concept-processing queue as a coupled pair and the
  backtrack restores both, undoing the failed disjunct's downstream
  derivations; guarded on no-successor-created — successor-creating disjuncts
  still use chronological behaviour pending the task-fork/backjump port),
  negation, **clash detection**, TBox unfolding (`A ⊑ B` via the implication
  rule). The former unsoundness (a failed disjunct's derivation persisting and
  falsely closing an open branch) is pinned + fixed by the un-ignored
  `subsumption_via_disjunction_one_branch_open` negative control.
- **Roles / successors**: `∃R.C` creates a successor node + R-edge and labels it;
  `∀R.C` propagates over edges; **nested `∃` grows multi-node** (root→n1→n2…).
- **Termination**: ancestor subset blocking now stops the cyclic TBox pattern
  `A ⊑ ∃R.A` by direct-blocking the repeated anonymous successor.
- **SHIQ breadth**: qualified number restrictions `≥n R.C` (n distinct
  successors) and `≤n R.C` (merge-or-clash via the u15 merge); RBox — role
  **hierarchy** (`R⊑S`), **inverse** (`R⁻`), **transitivity** (`Trans(R)`).
- **Classification**: consistency-based subsumption (KM's actual task) —
  `A⊑B` iff `A ⊓ ¬B` unsatisfiable; direct, transitive, and conjunctive
  subsumption + unsatisfiable-concept all verified.

### Architecture in place (compiles clean on ws, `cargo check --release` exit 0)
- **Substrate**: `model/substrate.rs` — typed arena `Id<T>` + `Arena<T>` +
  watermark/truncate backtrack (replaces Konclude's raw `CXxx*` + memory pool).
- **`ProcessContext`** (62 arenas) — the per-test ownership root; **`CacheContext`**
  (64 arenas) — the cache pool root.
- All process/saturation satellites (variable-binding paths, distinct/connection-
  successor, blocking-candidate hashes, propagation/representative bindings,
  merge/condensed-reapply/successor-role hashes, saturation successor tower).
- **Dependency factory** (7 variant allocators) + **clash/stop propagation** via a
  cooperative `CalcSignal` on the context (KONCLUDE-PORT-NOTE[exceptions], avoids
  threading `Result` through ~450 rule signatures).
- **Live engine**: the driver loop (`handle_task`/`take_next_process_individual`),
  the processing-queue subsystem (4 queue kinds), the rule-dispatch jump table
  (`tableau_rule_choice`, ~60+17 opcode arms → `apply_*_rule`), and the test
  entry `run_completion_on(ctx)` (bypasses the still-deferred Task adapter).

### Blocking/reapply port fan-out (2026-06-30)
- Resolved the tracker/source inconsistency: this module is wired from `lib.rs`
  (`pub mod konclude_ht;`) and the recorded HEAD is `b8ad70a`.
- Ported more of the Konclude blocking path function-by-function:
  - `u35::propagate_individual_node_modified` now mirrors cpp 19634-19688,
    including direct/ancestor blocking-retest flags, cache-retest flags, backend
    synchronization retest flags, incremental expansion retest, and delayed
    nominal requeue.
  - `u03::propagate_adding_processing_restriction_to_successors`,
    `u03::propagate_clearing_processing_restriction_to_successors`, and
    `u03::propagate_individual_processed_and_reactivate` now use the live
    successor/localization/restriction-flag paths instead of whole-method stubs.
  - `u19::is_label_concept_optimized_blocking` now runs the B2 role-reapply
    forall/AQAND checks plus the B6 and B4 label-set scans through the ported
    role-reapply, label, and concept arenas.
  - `u19::is_individual_node_blocking` resolves the initialization-concept guard
    through the live descriptor/concept arenas instead of the old process-layer
    placeholder shims, so equivalent concept+polarity descriptors match across
    ancestor candidates.
  - `u18` signature-blocking search/candidate/establish/refresh/review-marking
    paths now use arena-backed candidate hashes and signature expansion data.
    Review-set bucket mutation and blocker expansion-count reads remain explicit
    lower-level API deferrals.
  - `u35::prune_successors` now mirrors cpp 19699-19758: it marks purge-blocked
    nodes, eliminates blocked descendants, removes non-ancestor nominal links
    through live successor/connection iterators, and recurses into strictly
    deeper blockable successors created by the pruned individual.
  - `u36::add_concept_to_individual` now ports the concept occurrence-statistics
    tail from Konclude's label insertion path: newly inserted labels update the
    F7 handler/writer/vector occurrence counters when both occurrence-stat flags
    are enabled; contained descriptors and clash-rejected descriptors do not
    double-count.
  - F7 occurrence-statistics readers now have live context-threaded accumulation
    paths: concept and role readers fold all written ontology-data vectors through
    `COccurrenceStatisticsCacheReader` instead of duplicating the fold in the
    completion handler.
  - `u36::add_concept_to_individual` now ports the `CCMARKER` label-insertion
    branch over a real `CMarkerIndividualNodeHash`: marker labels allocate/localize
    the databox marker hash, register `(marker concept, individual node,
    nondeterministic flag)`, preserve inherited marker linkers on copy-on-write,
    and use Konclude's head-prepend linker order. Non-marker labels do not
    allocate the hash and contained duplicate marker labels do not duplicate.
  - Unit 36 label insertion now fills and drains the real
    `CCondensedReapplyQueueIterator` at the Konclude `reapplyIt.hasNext()` call
    points for `addConceptToIndividual`,
    `addConceptToIndividualReturnConceptDescriptor`, and the primary
    `addConceptsToIndividual` linker overload. The dynamic condensed queue is
    cleared exactly at `getIterator(..., true)` time and drained through the live
    `applyReapplyQueueConcepts` condensed-iterator overload.
  - Unit 36 concept-label modification tagging is now live: label-set
    modification increments `CProcessTagger::incConceptLabelSetModificationTag`,
    updates the node's `CReapplyConceptLabelSet` modification tag, mirrors the
    Konclude min-modification candidate helpers, propagates the individual-node
    modified state, and `isIndividualNodeConceptLabelSetModified` now reads the
    label-set tag instead of conservatively returning true.
  - Unit 30 concept-clash descriptor creation is now live: the folded
    `CClashedDependencyDescriptor` arena carries the `CClashedConceptDescriptor`
    subtype payload, `createClashedConceptDescriptor` allocates and prepends a
    real descriptor in Konclude linker order, and raised clash signals now carry
    concept/node/trackpoint payloads instead of an unchanged empty chain.
  - Concept saturation reference linking is now live for the Unit 25/36
    saturated-unsat path: `CConceptProcessData`,
    `CConceptSaturationReferenceLinkingData`, and
    `CSaturationConceptReferenceLinking` are arena-backed model records;
    `isConceptUnsatisfiabilitySaturated` follows Konclude's concept-data →
    process-data → saturation-reference → saturation-node chain and checks the
    indirect clashed flag; Unit 36's saturated-unsat label-insertion tail now
    allocates a real `CClashedConceptDescriptor` and raises the clash at the
    original throw point.
  - Unit 22's `hasSaturatedClashedFlagForConcept` sibling lookup is now live
    over the same concept-process/saturation-reference substrate, matching
    cpp 16438-16459 and returning the saturation individual node's indirect
    clashed flag for the requested concept polarity.
  - Unit 30 individual-link clash descriptor creation is now live: the folded
    `CClashedDependencyDescriptor` arena carries the
    `CClashedIndividualLinkDescriptor` subtype payload, and
    `createClashedIndividualLinkDescriptor` allocates and prepends a real
    descriptor with its `CIndividualLinkEdge` and dependency track point.
  - Unit 30 individual-distinct clash descriptor creation is now live:
    `CClashedIndividualDistinctDescriptor` is folded into the clash descriptor
    arena, `createClashedIndividualDistinctDescriptor` allocates/prepends it in
    Konclude linker order, and the payload exposes its `CDistinctEdge`.
  - Unit 30 negation-disjoint clash descriptor creation is now live:
    `CClashedNegationDisjointLinkDescriptor` is folded into the clash descriptor
    arena, `createClashedNegationDisjointDescriptor` allocates/prepends it in
    Konclude linker order, and the payload exposes its `CNegationDisjointEdge`.
  - Unit 30 tracked-clash descriptor creation is now live for the creation
    dispatch slice: `CTrackedClashedDescriptor` is folded into the same
    `CClashedDependencyDescriptor` arena, caches the Konclude individual/level/
    dependency flags at initialization time, and
    `createTrackedClashesDescriptor{,s}` allocate/prepend typed tracked
    descriptors including the independent concept-descriptor copy branch.
  - `u35::generate_debug_individual_node_associated_concepts_string`,
    `generate_debug_individual_node_associated_concepts_set_string`, and
    `generate_debug_individual_nodes_list_associated_concepts_set_string` now
    mirror cpp 18390-18462 formatting: concept tags are rendered in ascending
    `QMap` order with duplicate tag overwrite/collapse, node groups are joined
    with `<br>\n`, and predecessor/nominal groups use Konclude's `"  |||  "`
    separators.
  - `u35::install_individual_node_role_link{,_reapplied}` now updates role
    occurrence statistics through a live `COccurrenceStatisticsCacheHandler` /
    F7 writer / ontology-data-vector path after successful first role-successor
    insertion. The update remains gated by the Konclude occurrence-stat flags and
    does not run after the disjoint-role clash throw boundary.
  - Unit 29 branch track-point creation is now live:
    `createNonDeterministicDependencyTrackPointBranch` allocates or reuses the
    branch-tree node exactly at Konclude's call split, allocates/prepends the
    dependency node's branch track point, increments the branch node, initializes
    the track point from the resulting branch level, and updates the context's
    current branch node on forced creation.
- Process-layer follow-up in this fan-out:
  - `process::rs1` now has live role-successor link/role iterators.
  - `process::reapply_sat` / `process::satellites` now carry live
    `CReapplyQueue` / `CReapplyQueueIterator` / `CReapplyConceptDescriptor`
    behaviour used by role-successor hashes.
  - `ProcessContext` exposes the successor/reapply queue accessors needed by the
    blocking loops.
  - `CSuccessorRoleHash` and `ProcessContext` now provide the node-level
    single-link/connection removal substrate needed by pruning.
- W18 role/concept reapply queue fidelity:
  - `ProcessContext` now has context-threaded lazy accessors for the node's
    `CReapplyRoleSuccessorHash` triple buffer, role-keyed reapply queues, and
    concept-keyed condensed reapply queues in the node label set.
  - `u10::add_concept_to_reapply_queue(_role)`,
    `u10::add_concept_to_reapply_queue_role_restricted`,
    `u10::is_concept_in_reapply_queue_role`, and
    `u10::apply_reapply_queue_concepts_role` are live over the process arenas:
    descriptors are allocated, inserted, iterated dynamic-then-static, and queued
    onto the node's concept-processing queue.
  - `u10::add_concept_to_reapply_queue_concept`,
    `u10::add_concept_to_reapply_queue_concept_restricted`,
    `u10::is_concept_in_reapply_queue_concept`, and
    `u10::apply_reapply_queue_concepts_concept` now use the real
    `CCondensedReapplyQueue` / `CCondensedReapplyQueueIterator` chain.
  - `process::ls1::get_concept_reapply_iterator` now reads and clears the actual
    condensed queue head instead of always returning an empty iterator; the
    condensed iterator polarity filter is aligned with the descriptor insertion
    polarity (`!negation`).
  - `u04::needs_processing_for_concept` now reads the real descriptor concept /
    polarity and rule table; `add_concept_to_processing_queue` plus the restricted
    priority overloads allocate real `ConceptProcessDescriptor`s instead of
    inserting `Id::NONE`.
  - New regression `role_reapply_queue_applies_to_concept_processing_queue`
    verifies add → membership → role apply → concept queue materialization.
  - New regression `concept_reapply_queue_applies_to_concept_processing_queue`
    verifies add → membership → concept apply → dynamic-queue clear → concept
    queue materialization.
  - W19 edge-install reapply fidelity:
    - `ProcessContext::node_install_individual_link` now ports the node-level
      `installIndividualLink` path for role edges: it installs the edge into the
      node's reapply role-successor hash, returns the role queue iterator for the
      newly installed edge, updates the topology successor-role hash, and records
      `last_added_link`.
    - `u35::install_individual_node_role_link_reapplied` now returns a real
      `CReapplyQueueIterator` instead of an opaque placeholder; `u08`'s
      role-successor edge helper uses the same install path.
    - New regression `role_link_install_returns_reapply_iterator` verifies
      edge-install → returned role reapply iterator → concept queue materialization.
  - W71 SELF/link-creation fidelity:
    - `u34::get_individual_node_link` now walks the live successor-role hash via
      `node_successor_role_iterator` and returns the first matching role edge.
    - `u10::create_new_individuals_links_reapplyed` and the single-role overload
      now iterate the supplied role linker, allocate/install real
      `CIndividualLinkEdge`s, handle inverse role-link entries, apply range/domain
      concept linkers through the existing concept-adder, and drain restricted
      role reapply iterators at the Konclude call point.
    - `u09::apply_self_rule` now calls the live link-restriction helper,
      self-link lookup, `createSELFDependency`, link creation, clash-descriptor
      helpers, `raise_clash`, and role reapply queue insertion for negative SELF.
    - New regressions cover direct/inverse/single-role link creation,
      successor-role lookup, positive SELF self-edge creation, negative SELF clash
      on an existing self edge, and negative SELF role-reapply installation.
  - W72 disjoint-role edge-install fidelity:
    - `DisjointEdge::init_negation_disjoint_edge` now ports Konclude's
      `CNegationDisjointEdge::initNegationDisjointEdge` initializer instead of
      relying on ad hoc field writes.
    - `ProcessContext::node_install_disjoint_link` now ports the node-level
      `installDisjointLink` path into the live `CDisjointSuccessorRoleHash`.
    - `u35::create_individual_node_disjoint_roles_links` and
      `u35::create_individual_node_negation_link` now allocate/install real
      negation-disjoint edges, set both nodes' disjoint-role flags, register
      negation connection successors, and raise clashes when the matching role
      edge already exists.
    - `u35::install_individual_node_role_link` and the reapplied overload now
      perform the inverse clash check against existing negation-disjoint edges
      before installing the role edge. Clash descriptor payload allocation remains
      in the existing Unit 30 factory deferral; the clash signal path is live.
    - New regressions cover disjoint-edge installation, disjoint-after-role clash,
      and role-after-negation-disjoint clash.
  - W73 non-reapplied link-creation fidelity:
    - `IndividualLinkEdge::init_individual_link_edge` now ports both
      `CIndividualLinkEdge::initIndividualLinkEdge` overloads instead of relying
      on direct field writes.
    - `u35::create_new_individuals_links` now ports cpp 22212-22247 over live
      role/disjoint/link/connection APIs: direct and inverse role edges are
      allocated, initialized, installed, ancestor-role links are returned, inverse
      generation registers the reverse connection successor, destination nodes
      always register the source connection successor, and the incremental
      neighbour-update hook is called at the Konclude call point when enabled.
    - `u35::create_new_individuals_link` now ports cpp 22355-22369 for the
      single-role non-reapplied overload, including disjoint-role prelude,
      allocate/init/install, destination connection-successor insertion, and
      incremental neighbour update.
    - Cooperative clash-signal throw boundaries are preserved after disjoint-link
      and role-link install calls, so later connection/incremental side effects do
      not run after a Konclude throw site.
    - New regressions cover direct/inverse multi-role non-reapplied creation,
      reverse connection registration, single-role non-reapplied creation, and
      clash-on-existing-negation-disjoint behavior.
  - W74 distinct-edge creation fidelity:
    - `DistinctEdge::init_distinct_edge` now ports Konclude's
      `CDistinctEdge::initDistinctEdge` initializer.
    - `u35::create_individuals_distinct_pair` now ports cpp 22401-22409:
      allocate one `CDistinctEdge`, initialize it with source/destination/dependency,
      and insert the same edge symmetrically into both nodes' `CDistinctHash` maps.
    - `u35::create_individuals_distinct` now ports cpp 22413-22430 by installing
      one edge for every unordered pair in the supplied processing list.
    - New regressions cover the pair overload's symmetric same-edge insertion and
      the list overload's all-pairs creation/counts.
  - W75 fresh-individual construction fidelity:
    - `IndividualProcessNodeVector::get_item_max_index` now returns the highest
      non-negative stored index, matching Konclude's `getItemMaxIndex`; this fixes
      `createNewEmptyIndividual` so the first fresh node after root id 0 receives
      id 1 instead of skipping to 2.
    - The already-live `u35::create_new_empty_individual`,
      `create_new_individual`, `get_available_up_to_date_individual`, and
      `get_up_to_date_individual` helpers are now documented as live instead of
      stale `PORT-PENDING` scaffolding.
    - New regressions cover sequential/floor id allocation, vector registration,
      consistence/incremental flags, object TOP and data TOP-range seeding, data
      node flags, and stale-relocalized node-vector resolution.
  - W76 role-successor concept scanner fidelity:
    - `u35::has_role_successor_concept`,
      `has_role_successor_concepts`, and `get_role_successor_with_concepts` now
      walk the live `CReapplyRoleSuccessorHash` role-successor link iterator,
      resolve successors through `get_successor_individual`, and test labels
      through the resolved concept-tag/descriptor helpers.
    - New regression covers positive/negative concept matches, role filtering,
      all-concepts matching, first matching successor return, and no-match
      `NodeId::NONE`.
  - W77 distinct role-successor concept scanner fidelity:
    - `u35::has_distinct_role_successor_concepts` now ports the Konclude
      role-successor scan, non-creating distinct-hash read, distinct-count
      pruning, signed individual-id ordering guard, by-id node resolution, and
      required-concept label checks.
    - `CReapplyRoleSuccessorHash::getCoupledIndividualID(link)` is now live over
      edge endpoints and node individual ids, and `has_individuals_link` uses the
      context-threaded live lookup instead of the old node stub.
    - New regression covers real role edges, real distinct edges, positive count,
      insufficient distinct count, role filtering, concept polarity failure, and
      the shared `hasIndividualsLink` predicate.
  - W78 SOME successor construction fidelity:
    - `u35::create_successor_individual` now ports cpp 21635-21670 for the
      default no-saturation path: SOME dependency continuation, fresh object/data
      successor creation, reapplied ancestor role links, ancestor link/depth
      setup, ancestor-cache flag inheritance, concept addition, and gated
      saturation expansion/cache calls.
    - New regression covers fresh successor creation, real ancestor role edge,
      ancestor depth, inherited ancestor satisfiable/signature/saturation cache
      flags, shared link lookup, and positive/negative concept labels.
  - W79 distinct successor construction fidelity:
    - `u35::create_distinct_successor_individuals` now ports cpp 22143-22186
      for the default no-saturation path: fresh successor allocation, saturation
      successor lookup call, all-pairs distinct edge creation, reapplied ancestor
      role links, ancestor link/depth setup, ancestor-cache flag inheritance,
      concept addition, and gated saturation expansion/cache calls.
    - New regression covers cardinality-sized successor creation, pairwise
      distinct hashes, real ancestor role edges, depth/flag inheritance, and
      matching concept labels through the distinct role-successor scanner.
  - W80 functional successor reuse fidelity:
    - `u35::try_extend_functional_successor_individual` now ports cpp
      21565-21632 for the default no-saturation path: existing functional
      role-successor detection, localized successor reuse, ALL dependency
      continuation, missing direct/inverse role link creation, modification
      propagation, concept addition, and gated saturation expansion/cache calls.
    - New regression covers reuse of an existing functional successor, missing
      direct and inverse role-link creation, requested labels, and modification
      retest marking.
  - W81-W82 Unit 35 blocking/pruning fidelity:
    - `u35::prune_successors` now ports cpp 19699-19758 over live successor,
      connection, and nominal-link removal substrate.
    - `u35::add_individual_node_candidate_for_concept_descriptor` and
      `add_individual_node_candidate_for_concept` now port cpp 19543-19568 over
      the real `CBlockingIndividualNodeCandidateHash`, including recursive
      non-negated `CCAND` / negated `CCOR` operand registration.
    - New regressions cover recursive purge + nominal-link cleanup and
      descriptor/linker candidate insertion into the blocking candidate hash.
  - W20 restricted reapply iterator fidelity:
    - `u10::apply_reapply_queue_concepts_restricted` now walks the live
      `CReapplyQueueIterator`, reads real reapply descriptors, lazily creates one
      link-processing restriction when needed, and queues real concept-process
      descriptors with that restriction.
    - The current restriction arena now carries the
      `CLinkProcessingRestrictionSpecification::mRestLink` payload used by this
      path. The full `CProcessingRestrictionSpecification` subtype family is still
      a larger process-layer cleanup.
    - New regression `restricted_reapply_queue_attaches_link_restriction` verifies
      restricted reapply → concept-processing descriptor → restriction carrying
      the triggering edge.
  - W21 condensed-iterator apply fidelity:
    - `u10::apply_reapply_queue_concepts_condensed_iterator` now walks the real
      `CCondensedReapplyQueueIterator`, reads condensed descriptor fields from the
      process arena, and queues matching descriptors onto the node's concept queue.
    - New regression `condensed_iterator_reapply_queues_matching_descriptors`
      verifies polarity-filtered condensed iteration and concept queue materialization.
  - W22 propagation-binding reapply fidelity:
    - `u10::apply_reapply_queue_concepts_propagation_binding` now walks the real
      `CPropagationBindingReapplyConceptDescriptor` linker, reads the target
      concept descriptor and individual node from the process arena, localizes
      non-current target nodes, and queues each descriptor onto the target node's
      concept-processing queue.
    - Deferred propagation-binding-map callers now use the typed reapply linker id
      placeholder instead of an opaque integer cursor, keeping the remaining map
      gap explicit while aligning with the live overload.
    - New regression `propagation_binding_reapply_linker_queues_concepts` verifies
      linker traversal and concept queue materialization for every descriptor.
  - W23 optimized-blocking B2 fidelity:
    - `u19::is_label_concept_optimized_blocking` now walks the blocker's real
      role-keyed `CReapplyQueueIterator` for each ancestor role edge and evaluates
      the B2 `∀R.C` / negated-`∃R.C` and AQAND transition checks against the
      ancestor label set.
    - The B2 dependency violation counters are live for real dependency track
      points; the signature-mirroring candidate payload that consumes those
      counters remains part of the existing blocking-alternative deferral.
    - New regression `optimized_blocking_b2_role_reapply_rejects_missing_forall_operand`
      verifies that B2 rejects a candidate blocker when the ancestor lacks the
      required forall operand from the blocker's role reapply queue.
  - W24 optimized-blocking B3/B5 fidelity:
    - `u19::is_label_concept_optimized_blocking` now ports the B3/B5
      blocker-successor cardinality loop over the live role-successor link
      iterator and `get_successor_individual`, rejecting candidate blockers when
      their existing matching successors meet the minimum cardinality.
    - `u35` node/label containment helpers now resolve concept tags through
      `OntologyArenas` and descriptor polarity through `ProcessContext`, closing
      the old arena-id-as-tag shim mismatch on live label sets.
    - New regression `optimized_blocking_b3_b5_counts_blocker_role_successors`
      verifies that a blocker carrying `≤1 R.Q` is rejected when it already has
      one qualifying R-successor.
  - W25 optimized-blocking B4a fidelity:
    - `u19::is_label_concept_optimized_blocking` now ports the B4a
      successor-count subloop over the blocker's live role-successor hash,
      rejecting candidate blockers that cannot satisfy their own at-least /
      existential restrictions with matching successors.
    - New regression `optimized_blocking_b4a_counts_insufficient_blocker_successors`
      verifies that a blocker carrying `≥2 R.Q` is rejected when it has only one
      matching R-successor and B4b does not discharge the restriction.
  - W26 propagation-binding fresh-producer fidelity:
    - `u34::propagate_fresh_propagation_bindings` now walks the previous
      propagation-binding map, adopts the propagate-all flag, allocates fresh
      `CPropagationBindingDescriptor` records for prev-only / descriptor-empty
      keys, installs them into the new map/set, and re-applies existing
      propagation-binding reapply linkers.
    - Dependency creation is still explicitly deferred to the remaining
      dependency-base port; the live producer carries the previous dependency
      track point exactly through the typed descriptor path.
    - New regression `propagation_binding_fresh_producer_applies_existing_reapply_linker`
      verifies fresh descriptor allocation plus reapply-linker concept queueing.
  - W27 PBIND implication existing-binding caller fidelity:
    - `u07::apply_bind_propagate_implication_rule` now resolves the existing
      binding-trigger descriptor through the node label set using the actual
      concept tag, localizes the concept propagation-binding-set hash, fetches
      previous/current propagation-binding sets, sets the binding set's concept
      descriptor, and calls the live W26 `propagate_fresh_propagation_bindings`.
    - The follow-up C++ sequence is live for label-set modification and binding
      concept requeueing. The dependency-base linker and condensed reapply-queue
      pointer returned by `getConceptDescriptorAndReapplyQueue` remain explicit
      deferrals because those underlying Konclude base types are not ported yet.
    - `u07::apply_bind_variable_rule` received the same resolved-label lookup and
      fresh-propagation call sequence for its existing-binding branch; the
      genuinely unported new variable-binding allocation no longer pretends to
      have created a binding.
    - New regression `pbind_implication_existing_binding_refreshes_fresh_bindings`
      drives the public PBIND implication rule and verifies fresh descriptor
      propagation plus reapply-linker queueing through the rule caller.
  - W28 propagation-binding initial-producer fidelity:
    - `u33::propagate_initial_propagation_bindings` now takes typed
      `PropagationBindingSetId`s, adopts the previous set's propagate-all flag,
      copies the previous propagation-binding map into the new set, clears copied
      reapply descriptors, allocates fresh `CPropagationBindingDescriptor`
      records for each copied binding, installs them into the new map/set, and
      appends the fresh descriptor linker to the set descriptor chain.
    - The C++ `createPROPAGATEBINDINGDependency(...)` call is still an explicit
      dependency-base deferral; until that base object lands, the port carries
      the previous dependency track point through the typed descriptor path.
    - New regression `propagation_binding_initial_producer_copies_prev_map_with_fresh_descriptors`
      verifies propagate-all adoption, map copy, reapply clearing, fresh
      descriptor allocation, preserved propagation binding, preserved dependency
      track point, and descriptor-linker installation.
  - W29 propagation-binding successor initial-producer fidelity:
    - `u33::propagate_initial_propagation_bindings_to_successor` now takes typed
      `PropagationBindingSetId`s, adopts the previous set's propagate-all flag,
      copies the previous propagation-binding map into the new successor set,
      clears copied reapply descriptors, allocates fresh
      `CPropagationBindingDescriptor` records, installs them into the new map/set,
      and appends the descriptor linker.
    - The C++ `createPROPAGATEBINDINGSSUCCESSORDependency(...)` call remains a
      dependency-base deferral; the call position is preserved and the previous
      dependency track point is carried when the base factory cannot materialize
      a track point yet.
    - New regression `propagation_binding_initial_successor_producer_copies_prev_map_with_fresh_descriptors`
      verifies the successor initial-copy path over a real edge.
  - W30 PBIND implication new-binding caller fidelity:
    - `u07::apply_bind_propagate_implication_rule` now ports the new-binding
      branch far enough to create the binding-trigger concept descriptor, localize
      the previous/current propagation-binding sets, set the binding-set concept
      descriptor, and call the live W28 initial producer in Konclude order.
    - `u07::apply_bind_variable_rule` now performs the same initial propagation
      sequence before the still-deferred fresh variable-binding allocation,
      matching the C++ order.
    - New regression `pbind_implication_new_binding_initializes_propagation_bindings`
      drives the public PBIND implication new-binding branch and verifies copied
      initial propagation descriptors through the trigger set.
  - W31 PBIND variable new-binding allocation fidelity:
    - `u07::apply_bind_variable_rule` now performs the fresh
      `CPropagationBinding` allocation in the new-binding branch after the
      initial propagation sequence, preserving the Konclude order:
      `getNextBindingPropagationID(true)`, `initPropagationBinding`, descriptor
      allocation, descriptor initialization, data assignment, map insertion, and
      set descriptor-linker insertion.
    - New regression `pbind_variable_new_binding_allocates_special_propagation_binding`
      drives the public PBIND variable new-binding branch and verifies the
      special descriptor, binding propagation id, bound individual, bound
      variable, and trigger-set map entry.
  - W32 propagation-binding successor fresh-producer fidelity:
    - `u33::propagate_fresh_propagation_bindings_to_successor` now takes typed
      `PropagationBindingSetId`s, adopts the previous set's propagate-all flag,
      walks previous/new binding maps in Konclude key order, allocates fresh
      successor `CPropagationBindingDescriptor` records for missing or
      descriptor-empty entries, preserves existing descriptors, installs missing
      map data, appends the descriptor linker, and applies existing reapply
      concept linkers.
    - The C++ `createPROPAGATEBINDINGSSUCCESSORDependency(...)` call position is
      preserved. Until the dependency-base object is materialized, the port
      carries the previous dependency track point with an explicit API deferral.
    - New regression `propagation_binding_fresh_successor_producer_updates_missing_entries_and_reapplies`
      verifies missing-entry insertion, descriptor-empty update, existing
      descriptor preservation, propagate-all adoption, and reapply queueing over
      a real successor edge.
  - W33 PBIND variable existing-binding allocation fidelity:
    - `u07::apply_bind_variable_rule` now ports the existing-binding branch under
      Konclude's `getNewSepcialPropagationBindingDescriptor()` guard. If the
      trigger set lacks the special descriptor, it creates the BINDVARIABLE
      dependency, allocates/initializes `CPropagationBinding`, allocates the
      descriptor, installs it with `addPropagationBinding(..., true)`, and sets
      `newVarBindCreated` so the binding concept is requeued.
    - New regression `pbind_variable_existing_binding_allocates_missing_special_propagation_binding`
      drives the public rule over a pre-existing trigger descriptor and verifies
      the missing special propagation-binding descriptor is allocated and mapped.
  - W34 propagation-binding successor dispatcher fidelity:
    - `u33::propagate_propagation_bindings_to_successor` now localizes the
      successor, walks the operand linker, distinguishes absent vs existing
      operand binding descriptors, creates the BINDPROPAGATEALL dependency at the
      Konclude point, and dispatches to the live W29 initial or W32 fresh
      successor producers before requeueing the successor when propagation
      occurs.
    - The dependency-base object and the condensed reapply queue pointer returned
      by `getConceptDescriptorAndReapplyQueue` remain explicit API deferrals.
    - New regressions
      `propagation_binding_successor_dispatcher_initializes_missing_operand_binding`
      and `propagation_binding_successor_dispatcher_refreshes_existing_operand_binding`
      verify both dispatcher branches over real successor edges.
  - W35 PBINDALL non-restricted role-successor fan-out fidelity:
    - `u07::apply_bind_propagate_all_rule` now ports Konclude's
      `getReapplyRoleSuccessorHash(false)` / `getRoleSuccessorLinkIterator(role)`
      loop for the no-link-restriction branch, calling the live W34 successor
      dispatcher for every matching role edge.
    - `u03::get_link_processing_restriction` now reads the descriptor's current
      processing restriction and returns the stored link restriction, matching the
      Konclude helper against the current collapsed restriction-spec arena.
    - New regression `pbind_all_nonrestricted_fans_out_over_role_successor_links`
      verifies the public PBINDALL rule fans out over a real installed role
      successor edge and creates the operand successor propagation descriptor.
  - W36 VARBINDALL non-restricted role-successor fan-out fidelity:
    - `u06::apply_varbind_propagate_all_rule` now ports the public
      `applyVARBINDPROPAGATEALLRule` control flow: real descriptor/concept/role
      reads, link-restriction handling, existing role-successor hash iteration,
      successor dispatch, and role reapply-queue registration.
    - `u11::propagate_variable_bindings_to_successor` plus the initial/fresh
      successor producers now operate on typed `CVariableBindingPathSet` and
      `CConceptVariableBindingPathSetHash` arenas, cloning source path maps or
      propagating missing path ids with fresh descriptors.
    - New regressions
      `varbind_all_nonrestricted_initializes_successor_variable_bindings` and
      `varbind_all_nonrestricted_refreshes_existing_successor_variable_bindings`
      verify both public VARBINDALL successor branches over real role edges.
  - W37 VARBINDAND same-node variable-binding propagation fidelity:
    - `u06::apply_variable_binding_and_rule` now ports the same-node
      `applyVARIABLEBINDINGANDRule` descriptor/concept/operand/label-set/hash
      reads and dispatches typed initial/fresh variable-binding propagation for
      missing and existing trigger descriptors.
    - `u11::propagate_initial_variable_bindings` and
      `u11::propagate_fresh_variable_bindings` now operate on typed
      `CVariableBindingPathSet` and `CConceptVariableBindingPathSetHash` arenas;
      the fresh path follows Konclude's sorted dual-cursor merge and only
      propagates source path ids missing from the trigger set.
    - `u36::add_concept_to_individual_return_concept_descriptor` now uses the
      context-threaded queue and label-set accessors, so the missing-trigger
      branch allocates real backing arenas before inserting the new descriptor.
    - New regressions `varbind_and_initializes_same_node_variable_bindings` and
      `varbind_and_refreshes_same_node_variable_bindings_in_merge_order` verify
      the public VARBINDAND missing/existing trigger branches and the fresh
      merge/linker ordering.
  - W38 VARBINDAND existing-trigger condensed reapply drain fidelity:
    - `process/ls1.rs` now uses the real `CCondensedReapplyQueue::isEmpty`
      equivalent, exposes the descriptor lookup's queue state by concept tag,
      and can take/clear the exact by-tag dynamic queue head used by the
      descriptor lookup.
    - `process/context.rs` adds by-tag context-threaded helpers for concept
      reapply iteration, concept reapply insertion, concept reapply membership,
      and the `getConceptDescriptorAndReapplyQueue` + `getConceptReapplyIterator`
      sequence. This avoids the old `concept.raw` shim when the completion layer
      has the real ontology concept tag.
    - `u10` concept-keyed reapply add/apply/is-in-queue overloads now compute
      `concept->getConceptTag()` from `OntologyArenas` before touching the
      label-set map.
    - `u06::apply_variable_binding_and_rule` now drains the existing trigger's
      condensed reapply queue after fresh same-node path propagation, matching
      Konclude's guarded `reapplyQueue->isEmpty()` /
      `getConceptReapplyIterator(bindingConDes)` /
      `applyReapplyQueueConcepts` sequence.
    - New regression
      `varbind_and_existing_trigger_drains_condensed_reapply_queue_after_fresh_paths`
      verifies the fresh trigger requeue, drained queued descriptor, and dynamic
      queue clearing.
  - W39 VARBIND implication same-node trigger propagation fidelity:
    - `u06::apply_varbind_propagate_implication_rule` now ports the public
      `applyVARBINDPROPAGATEIMPLICATIONRule` control flow for descriptor,
      operand, label-set, and variable-binding path-set access. The missing
      trigger branch installs the inverted trigger reapply entry; the all-triggers
      branch creates the binding-trigger descriptor and initializes its path set;
      the existing-binding branch performs fresh propagation and drains the
      trigger's condensed reapply queue through the W38 by-tag iterator path.
    - `u04::add_concept_preprocessed_to_processing_queue` binding-count overload
      now allocates a real `CConceptProcessDescriptor` and inserts it on the
      normal concept-processing queue path, matching the call shape used by the
      implication fresh branch. Batch/variable-binding queue special cases remain
      explicit W3 deferrals.
    - `process/varbind.rs` adds the `CPROCESSMAP::count` equivalent for
      `CVariableBindingPathMap`, used by the binding-count overload.
    - Strict deferral: trigger dependency-base chaining is still represented by
      the existing `DepLinkId::NONE` fallback because the underlying Konclude
      dependency base-link materialization is not ported yet.
    - New regressions
      `varbind_implication_installs_missing_trigger_reapply`,
      `varbind_implication_initializes_binding_paths_when_all_triggers_present`,
      and `varbind_implication_existing_binding_refreshes_and_drains_reapply`
      verify the three public implication branches over real label-set and
      variable-binding path arenas.
  - W40 VARBIND variable transition-extension fidelity:
    - `process::propagation_binding::PropagationVariableBindingTransitionExtension`
      now ports the C++ transition-extension fields and accessors directly:
      last analysed propagation-binding descriptor, last propagate-all flag,
      processing-completed flag, localized/used trigger and joining hashes,
      triggered variable/individual pair, and left/right join cursors.
    - `ProcessContext` owns arenas for the transition extension, variable-binding
      trigger hash, and variable-binding path joining hash. `PropagationBindingSet`
      now has context-threaded lazy allocation and previous-set copy/localization
      for the extension, matching the Konclude process-context allocation model.
    - `u06::apply_varbind_variable_rule` is now live over the real propagation
      binding set: it scans only the new descriptor segment since the extension
      cursor, checks the triggered variable/individual pair through
      `addAnalysedPropagationBindingDescriptorReturnMatched`, creates the
      binding-trigger descriptor when needed, allocates the typed
      `CVariableBinding` / descriptor / path / path-descriptor chain, inserts it
      into the binding-trigger path set, and marks the extension completed so a
      second application does not duplicate the path.
    - Strict deferrals: trigger and joining hashes are present for interop, but
      the full `applyVARBINDPROPAGATEJOINRule` join execution remains pending.
      Dependency-base materialization still uses the established dependency
      fallback until the Konclude base-link objects are ported.
    - New regressions
      `varbind_variable_without_propagation_set_does_not_create_binding_path`,
      `varbind_variable_matching_propagation_binding_creates_binding_path`, and
      `varbind_variable_completed_transition_extension_prevents_duplicate_path`
      verify the no-source-set guard, descriptor-match path creation, and
      completed-extension duplicate prevention.
  - W41 VARBIND join-helper fidelity:
    - `u11::create_variable_binding_path_key`,
      `u11::trigger_variable_binding_path_joining`,
      `u11::propagate_variable_bindings_joins`,
      `u11::force_variable_binding_join_created`, and
      `u11::get_joined_variable_binding_path` are now typed over the real
      variable-binding arenas instead of opaque integer placeholders.
    - `process::varbind::VariableBindingPathJoiningHasher` now uses the real
      `CConcept::getVariableLinker()` variable list, and
      `CVariableBindingPathJoiningHash` now has collision buckets with
      key-equivalence lookup instead of silently keying only by the raw hash
      value.
    - `ProcessContext` and `CProcessingDataBox` now use the real
      `CVariableBindingPathMergingHash` arena for symmetric merged-path caching.
      The merge helper faithfully sorted-merges descriptor chains, de-duplicates
      equal bindings, allocates a fresh path id on first merge, and reuses the
      cached path for `(left,right)` / `(right,left)`.
    - This slice made the public join rule executable rather than leaving its
      u11 callees as stubs.
    - New regressions
      `varbind_join_get_joined_path_merges_sorted_bindings_and_caches_symmetrically`
      and `varbind_join_propagate_records_one_side_then_combines_other_side`
      verify merged-path caching and the one-side-record / opposite-side-combine
      join-data flow.
  - W42 public VARBIND join-rule fidelity:
    - `u06::apply_varbind_propagate_join_rule` now ports the public
      `applyVARBINDPROPAGATEJOINRule` descriptor/trigger checks and the
      transition-extension scan/replay block from C++ lines 12002-12220.
    - The rule resolves the source descriptor/concept, join output concept, two
      trigger operands, node label set, propagation-binding set, and left/right
      variable-binding path sets through the live process and ontology arenas.
    - It mirrors the Konclude stale-state test against the transition extension:
      last propagate-all flag, last analysed propagation-binding descriptor, and
      left/right last joining cursors.
    - The propagate-all replay path drains queued trigger linkers, clears them
      in the trigger hash, and calls the W41 join helper for each queued side.
      The non-propagate-all path replays only new propagation-binding
      descriptors and either queues a trigger or propagates immediately, exactly
      as Konclude does.
    - The left/right path-set scans now trigger or propagate new path descriptors
      and then advance the extension cursors, so a second rule application does
      not duplicate the joined path.
    - Strict deferral: `createVARBINDPROPAGATEJOINDependency` still falls back to
      the existing dependency track point until the Konclude dependency base-link
      object family is ported.
    - New regressions
      `varbind_join_rule_combines_existing_left_and_right_paths` and
      `varbind_join_rule_completed_extension_prevents_duplicate_join_path` drive
      the public rule over real label-set, propagation-binding, and
      variable-binding path arenas.
  - W43 VARBIND grounding substrate fidelity:
    - `model::ontology` now ports `CNominalSchemaTemplate` and the
      `CNominalSchemaTemplateVector` lookup convention used by
      `concept->getParameter()` in the grounding handler.
    - `process::grounding_hash` now ports
      `CConceptNominalSchemaGroundingData`,
      `CConceptNominalSchemaGroundingHasher`, and
      `CConceptNominalSchemaGroundingHash`, including ordered bound-nominal list
      equivalence and previous-hash initialization.
    - `ProcessContext` owns grounding data/hash arenas, and `ProcessingDataBox`
      now carries typed grounding-hash ids instead of the old marker type.
    - `u06::apply_varbind_propagate_grounding_rule` now resolves the
      `conProDes` descriptor, dependency track point, concept, polarity, node
      label set, and source `CVariableBindingPathSet` through live arenas and
      preserves Konclude's null-hash guard before the handler call.
    - W44 starts replacing the placeholder
      `CConceptNominalSchemaGroundingHandler` with a real
      `completion::grounding` port. `collectAllNominalConcepts` now scans the
      ontology ABox individual arena for non-negated `CCNOMINAL` assertions, and
      `getNominalConcept` resolves the process-node vector slot, respects the
      `forceNotPruned`/`PRFPURGEDBLOCKED` guard, and returns the first
      non-negated nominal assertion concept from the node's nominal individual.
    - W45 ports the internal recursive grounding helper layer:
      template-concept-to-nominal-schema mapping is now multivalued like
      Konclude's `CBOXHASH`, the handler constructor default enables reuse,
      `createNominalSchemaConceptCopy`, `addConceptOperand`,
      structural `createGroundedNominalSchemaConcept`, linker-emitting
      `createGroundedNominalSchemaConcept`, and `forceExtensionLocalisation` are
      live over typed arenas and the grounding reuse hash.
    - W46 ports the top-level
      `getGroundingConceptLinker(CVariableBindingPathSet*,...)` overload:
      bound nominal-schema variables are extracted from each variable-binding
      path descriptor, unconstrained template variables fall back to
      `collectAllNominalConcepts`, the Cartesian grounding helper builds the
      grounded concept linkers, and `applyVARBINDPROPAGATEGROUNDINGRule` now
      consumes them instead of keeping `newGroundedLinker` empty.
    - W47 materializes the `createVARBINDPROPAGATEGROUNDINGDependency` wrapper:
      when dependency building is enabled it allocates a deterministic
      `DNTVARBINDPROPAGATEGROUNDINGDEPENDENCY` node, stores the previous
      dependency track point and optional additional dependency chain, and returns
      the materialized continuation track point used by the added grounded
      concept. The public rule now only falls back to the base dependency when
      dependency building is disabled, matching Konclude's null-return guard.
    - W48 ports the representative-variable-binding-path-map grounding overload:
      `getGroundingConceptLinker(CRepresentativeVariableBindingPathMap*,...)`
      now iterates representative path-map entries, extracts bound nominal
      variables from each `CVariableBindingPath`, fills unconstrained template
      variables with all ABox nominal concepts, emits grounded concept linkers,
      and records the selected `CVariableBindingPath` per grounded concept.
    - W49 ports the representative-select dependency payload and
      `createREPRESENTATIVEGROUNDINGDependency`: dependency nodes now carry the
      selected `CVariableBindingPath` equivalent, initialize
      `DNTREPRESENTATIVEGROUNDINGDEPENDENCY`, store the previous dependency
      track point, and return the materialized deterministic continuation track
      point.
    - W50 ports `CConceptRepresentativePropagationSetHash{Data}` plus the
      context-threaded node lazy getter, and replaces the
      `applyREPRESENTATIVEGROUNDINGRule` `todo!` with the exact Konclude guard
      chain: read the node's representative propagation set without
      localization, follow the outgoing descriptor to existing migrate data,
      ground its representative variable-binding path map, create
      `DNTREPRESENTATIVEGROUNDINGDEPENDENCY` nodes with selected paths, and add
      the grounded concepts to the individual.
    - Remaining strict representative deferral: the sibling representative JOIN
      rule is the active phase. W62 starts the faithful Konclude substrate by
      porting the joining-key data map/key map, common-key data/map, and all-data
      extension containers. W63 ports `CRepresentativeJoiningHash{Data}`,
      `CRepresentativeJoiningData`,
      `CRepresentativeVariableBindingPathSetJoiningHash{Data}`, and
      `CRepresentativeVariableBindingPathSetJoiningData`, including typed
      process-context arenas and ordered `(leftRepID,rightRepID)` joining-cache
      lookup. The owning `CRepresentativeVariableBindingPathSetData`
      `getJoiningHash(create)` / `hasJoiningData(joinConcept)` methods are also
      live over that real hash. W64 ports
      `CRepresentativeVariableBindingPathJoiningKeyHash{Data}`,
      `CRepresentativeVariableBindingPathJoiningKeyData`, and
      `CRepresentativeVariableBindingPathJoiningKeyHasher`, including selected
      binding-descriptor extraction and numeric joining-key interning by binding
      identity. W65 wires completion `getRepresentativeJoiningKeyData` through
      the real interning hash and per-representative joining maps, and ports
      `createCommonJoiningKeyMap` including Konclude's recursive smaller-map
      orientation behaviour and ordered merge walk. W66 ports
      `createCommonJoiningAll`: it allocates the joined representative path-set
      data, cross-products common-key buckets through `getJoinedVariableBindingPath`,
      fills left/right resolve maps and the joined migrate map, inserts the
      containing-map/signature/hash entries, and stores the result on the
      all-data extension. Still missing before the public rule are
      transition-extension plumbing and `applyREPRESENTATIVEJOINRule` itself.
      W67 ports `CREPRESENTATIVEJOINDependencyNode` /
      `createREPRESENTATIVEJOINDependency` over the existing one-back-edge
      deterministic dependency shape. W68 ports
      `CPropagationRepresentativeTransitionExtension` and its
      `CPropagationBindingSet` lazy allocation/copy path. W69 wires the public
      `applyREPRESENTATIVEJOINRule` propagate-all branch through Konclude's
      trigger scan/reapply installation, transition-extension cursor gate,
      representative joining cache, common-key/all-data materialization,
      RESOLVE/REPRESENTATIVEAND/REPRESENTATIVEJOIN dependency chain, incoming
      joined representative propagation, propagation-set update, and join-concept
      insertion/reapply path. W70 wires the exact
      `areRepresentativesJoinable` quick-fail and
      `hasCommonVariableBindings` representative path-map key scan. Grounding,
      JOIN, AND, ALL, IMPLICATION, and BINDVARIABLE are wired.
    - W51 ports the immediate representative-AND prerequisites:
      `createREPRESENTATIVEANDDependency` now materializes deterministic
      `DNTREPRESENTATIVEANDDEPENDENCY` nodes with continuation track points, and
      `propagateRepresentative` now allocates a typed representative propagation
      descriptor, copies the source representative set data with the new
      dependency track point, installs it as incoming on the target propagation
      set, and calls `updateRepresentativePropagationSet` at the original C++
      control-flow point.
    - W52 ports the first branch of `updateRepresentativePropagationSet`: if the
      incoming representative descriptor linker has not changed, the method
      returns; if there is exactly one incoming descriptor and no outgoing
      descriptor, it shares the incoming descriptor as outgoing, updates the
      last-processed cursor, and increments the representative set data share
      count when its localization tag is current.
    - New regressions cover nominal-schema template accessors/vector ids,
      grounding-data/hash equivalence and copy initialization, and the public
      VARBIND grounding no-source-path-set guard.
- Verification in this checkout: `cargo check --release` passes with the existing
  warning set; `cargo test --release cyclic_tbox_exists_blocks -- --nocapture`
  passes; `cargo test --release role_reapply_queue_applies_to_concept_processing_queue -- --nocapture`
  passes; `cargo test --release concept_reapply_queue_applies_to_concept_processing_queue -- --nocapture`
  passes; `cargo test --release role_link_install_returns_reapply_iterator -- --nocapture`
  passes; `cargo test --release restricted_reapply_queue_attaches_link_restriction -- --nocapture`
  passes; `cargo test --release condensed_iterator_reapply_queues_matching_descriptors -- --nocapture`
  passes; `cargo test --release propagation_binding_reapply_linker_queues_concepts -- --nocapture`
  passes; `cargo test --release optimized_blocking_b2_role_reapply_rejects_missing_forall_operand -- --nocapture`
  passes; `cargo test --release optimized_blocking_b3_b5_counts_blocker_role_successors -- --nocapture`
  passes; `cargo test --release optimized_blocking_b4a_counts_insufficient_blocker_successors -- --nocapture`
  passes; `cargo test --release --lib pbind_implication_existing_binding_refreshes_fresh_bindings -- --nocapture`
  passes; `cargo test --release --lib pbind_implication_new_binding_initializes_propagation_bindings -- --nocapture`
  passes; `cargo test --release --lib propagation_binding_initial_producer_copies_prev_map_with_fresh_descriptors -- --nocapture`
  passes; `cargo test --release --lib propagation_binding_initial_successor_producer_copies_prev_map_with_fresh_descriptors -- --nocapture`
  passes; `cargo test --release --lib propagation_binding_ -- --nocapture`
  passes; `cargo test --release --lib pbind_ -- --nocapture`
  passes; `cargo test --release --lib varbind_and_ -- --nocapture` passes;
  `cargo test --release --lib varbind_implication -- --nocapture` passes;
  `cargo test --release --lib varbind_join_ -- --nocapture` passes;
  `cargo test --release --lib varbind_variable -- --nocapture` passes;
  `cargo test --release --lib varbind_ -- --nocapture` passes;
  `cargo test --release --lib concept_reapply_queue -- --nocapture` passes;
  `cargo test --release --lib condensed_iterator_reapply -- --nocapture` passes;
  `cargo test --release --manifest-path engine/Cargo.toml --lib grounding -- --nocapture`
  passes (32 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representative_path_set_hash -- --nocapture` passes
  (4 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representative_common_key_data_reports_left_and_right_counts -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representative_path_set_joining_hash -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representative_path_set_data_lazily_creates_joining_hash -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representative_joining_hash_uses_ordered_representative_pair -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representative_joining_key_hash_extracts_key_descriptors -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representative_joining_key_hash_interns_by_selected_binding_identity -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representative_joining_key_data_builds_cached_key_map -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representative_common_joining_key_map_preserves_left_orientation_after_swap -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representative_common_joining_all_creates_joined_rep_and_resolve_maps -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib create_representative_join_dependency_records_other_dependency -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representative_transition_extension_copies_cursors_and_maps -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib apply_representative_join_rule_creates_joined_representative -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib representatives_joinable -- --nocapture` passes
  (2 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib create_new_individuals_link -- --nocapture` passes
  (3 tests, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib apply_self_rule -- --nocapture` passes (3 tests, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib konclude_ht -- --nocapture`
  passes (124 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib disjoint_role -- --nocapture` passes (2 tests, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  role_link_install_clashes_with_existing_negation_disjoint_edge -- --nocapture`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib create_new_individuals_link -- --nocapture` passes (7
  tests, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht -- --nocapture` passes (131 tests, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  create_individuals_distinct -- --nocapture` passes (2 tests, 0 failed);
  `cargo test --release --manifest-path engine/Cargo.toml --lib konclude_ht
  -- --nocapture` passes (133 tests, 0 failed); `cargo test --release
  --manifest-path engine/Cargo.toml --lib create_new_empty_individual --
  --nocapture` passes (2 tests, 0 failed); `cargo test --release
  --manifest-path engine/Cargo.toml --lib create_new_individual -- --nocapture`
  passes (9 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib up_to_date_individual_helpers -- --nocapture` passes
  (1 test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht -- --nocapture` passes (138 tests, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib
  role_successor_concept_scanners -- --nocapture` passes (1 test, 0 failed);
  `cargo test --release --manifest-path engine/Cargo.toml --lib konclude_ht
  -- --nocapture` passes (139 tests, 0 failed); `cargo test --release
  --manifest-path engine/Cargo.toml --lib
  distinct_role_successor_concept_scanner -- --nocapture` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht -- --nocapture` passes (140 tests, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib create_successor_individual
  -- --nocapture` passes (1 test, 0 failed); `cargo test --release
  --manifest-path engine/Cargo.toml --lib konclude_ht -- --nocapture` passes
  (141 tests, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib create_distinct_successor_individuals -- --nocapture` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht -- --nocapture` passes (142 tests, 0 failed); `git diff --check`
  passes; `cargo test --release --manifest-path engine/Cargo.toml --lib
  try_extend_functional_successor_individual -- --nocapture` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht -- --nocapture` passes (143 tests, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib
  prune_successors_recurses_and_removes_nominal_links -- --nocapture` passes (1
  test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht -- --nocapture` passes (144 tests, 0 failed); `cargo check
  --release --manifest-path engine/Cargo.toml` passes; `git diff --check`
  passes; `cargo test --release --manifest-path engine/Cargo.toml --lib
  add_individual_node_candidate_for_concept_populates_blocking_candidate_hash --
  --nocapture` passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib konclude_ht -- --nocapture` passes (145 tests, 0
  failed); `cargo check --release --manifest-path engine/Cargo.toml` passes;
  `git diff --check` passes; `cargo test --release --manifest-path
  engine/Cargo.toml --lib
  debug_associated_concepts_strings_match_konclude_tag_formatting --
  --nocapture` passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib konclude_ht` passes (146 tests, 0 failed); `cargo
  check --release --manifest-path engine/Cargo.toml` passes; `cargo test
  --release --manifest-path engine/Cargo.toml --lib role_link_ -- --nocapture`
  passes (6 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib konclude_ht` passes (149 tests, 0 failed); `cargo
  test --release --manifest-path engine/Cargo.toml --lib
  add_concept_to_individual_occurrence` passes (2 tests, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib
  add_concept_to_individual_updates_concept_occurrence_statistics` passes (1
  test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht` passes (152 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `git diff --check` passes; `cargo
  test --release --manifest-path engine/Cargo.toml --lib
  occurrence_statistics_reader_accumulates` passes (2 tests, 0 failed); `cargo
  test --release --manifest-path engine/Cargo.toml --lib role_link_` passes (6
  tests, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib add_concept_to_individual_occurrence` passes (2 tests, 0 failed);
  `cargo test --release --manifest-path engine/Cargo.toml --lib konclude_ht`
  passes (154 tests, 0 failed); `cargo check --release --manifest-path
  engine/Cargo.toml` passes; `git diff --check` passes; `cargo test --release
  --manifest-path engine/Cargo.toml --lib marker_` passes (5 tests, 0 failed);
  `cargo test --release --manifest-path engine/Cargo.toml --lib konclude_ht`
  passes (159 tests, 0 failed); `cargo check --release --manifest-path
  engine/Cargo.toml` passes; `git diff --check` passes; `cargo test --release
  --manifest-path engine/Cargo.toml --lib drains_condensed_reapply_iterator`
  passes (3 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib konclude_ht` passes (162 tests, 0 failed); `cargo
  check --release --manifest-path engine/Cargo.toml` passes; `git diff --check`
  passes; `cargo test --release --manifest-path engine/Cargo.toml --lib
  concept_label_set_modified` passes (2 tests, 0 failed); `cargo test --release
  --manifest-path engine/Cargo.toml --lib konclude_ht` passes (164 tests, 0
  failed); `cargo check --release --manifest-path engine/Cargo.toml` passes;
  `git diff --check` passes; `cargo test --release --manifest-path
  engine/Cargo.toml --lib clashed_concept_descriptor` passes (2 tests, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (166 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `git diff --check` passes; `cargo
  test --release --manifest-path engine/Cargo.toml --lib
  concept_unsatisfiability_saturated` passes (1 test, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib saturated_unsat` passes (1
  test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht` passes (168 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `git diff --check` passes; `cargo
  test --release --manifest-path engine/Cargo.toml --lib
  has_saturated_clashed_flag_for_concept` passes (1 test, 0 failed); `cargo
  test --release --manifest-path engine/Cargo.toml --lib konclude_ht` passes
  (169 tests, 0 failed); `cargo check --release --manifest-path
  engine/Cargo.toml` passes; `cargo test --release --manifest-path
  engine/Cargo.toml --lib create_clashed_individual_link_descriptor` passes (1
  test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht` passes (170 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo test --release
  --manifest-path engine/Cargo.toml --lib
  create_clashed_individual_distinct_descriptor` passes (1 test, 0 failed);
  `cargo test --release --manifest-path engine/Cargo.toml --lib konclude_ht`
  passes (171 tests, 0 failed); `cargo check --release --manifest-path
  engine/Cargo.toml` passes; `cargo test --release --manifest-path
  engine/Cargo.toml --lib create_clashed_negation_disjoint_descriptor` passes
  (1 test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht` passes (172 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo test --release
  --manifest-path engine/Cargo.toml --lib create_tracked_clashes` passes (3
  tests, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht` passes (175 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo test --release
  --manifest-path engine/Cargo.toml --lib tracked_clashed` passes (3 tests, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (178 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo fmt --manifest-path
  engine/Cargo.toml --check` passes; `git diff --check` passes; `cargo test
  --release --manifest-path engine/Cargo.toml --lib
  get_free_tracked_clashed_descriptor` passes (1 test, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib konclude_ht` passes (179
  tests, 0 failed); `cargo check --release --manifest-path engine/Cargo.toml`
  passes; `cargo test --release --manifest-path engine/Cargo.toml --lib
  initialize_tracking_line` passes (3 tests, 0 failed); `cargo test --release
  --manifest-path engine/Cargo.toml --lib get_sorted_clashed_descriptors` passes
  (1 test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht` passes (183 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo test --release
  --manifest-path engine/Cargo.toml --lib write_clash_descriptors_to_cache`
  passes (2 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib konclude_ht` passes (185 tests, 0 failed); `cargo
  test --release --manifest-path engine/Cargo.toml --lib
  write_clash_descriptors_to_cache` passes (6 tests, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib konclude_ht` passes (189
  tests, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib mark_relevance_for_tracked_clashed_descriptors` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (190 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo test --release
  --manifest-path engine/Cargo.toml --lib backtrack_from_tracking_line_step`
  passes (2 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib konclude_ht` passes (192 tests, 0 failed); `cargo
  check --release --manifest-path engine/Cargo.toml` passes; `cargo fmt
  --manifest-path engine/Cargo.toml --check` passes; `git diff --check` passes;
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  get_backtracked_deterministic_clashed_descriptors` passes (2 tests, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  backtrack_from_tracking_line_step` passes (2 tests, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib konclude_ht` passes (194
  tests, 0 failed); `cargo check --release --manifest-path engine/Cargo.toml`
  passes; `cargo test --release --manifest-path engine/Cargo.toml --lib
  get_collected_filtered_clashed_descriptors_from_branch` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (195 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo fmt --manifest-path
  engine/Cargo.toml --check` passes; `git diff --check` passes; `cargo test
  --release --manifest-path engine/Cargo.toml --lib
  get_backtracked_deterministic_clashed_descriptors_before_processing_tag`
  passes (2 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib konclude_ht` passes (197 tests, 0 failed); `cargo
  check --release --manifest-path engine/Cargo.toml` passes; `cargo fmt
  --manifest-path engine/Cargo.toml --check` passes; `git diff --check` passes;
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  backtrack_non_deterministic_branching_clashed_descriptor` passes (2 tests, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (199 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo test --release
  --manifest-path engine/Cargo.toml --lib
  clashed_backtracking_drives_non_deterministic_branch_core` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (200 tests, 0 failed); `cargo test --release
  --manifest-path engine/Cargo.toml --lib nondeterministic_track_point_branch`
  passes (2 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib konclude_ht` passes (202 tests, 0 failed); `cargo
  check --release --manifest-path engine/Cargo.toml`, `cargo fmt --manifest-path
  engine/Cargo.toml --check`, and `git diff --check` pass; `cargo test
  --release --manifest-path engine/Cargo.toml --lib
  create_dependend_branching_task_list` passes (2 tests, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib konclude_ht` passes (204
  tests, 0 failed); `cargo check --release --manifest-path engine/Cargo.toml`
  passes; `rustfmt --edition 2021 --check` on the W110-edited Rust files passes;
  `git diff --check` passes. Full `cargo fmt --manifest-path
  engine/Cargo.toml --check` is currently blocked by existing non-`konclude_ht`
  formatting diffs; `cargo test --release --manifest-path engine/Cargo.toml --lib
  create_merge_branching_task_allocates_dependent_child` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  create_distinct_branching_task_allocates_dependent_child` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (206 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `rustfmt --edition 2021 --check`
  on the W111-edited Rust files passes; `git diff --check` passes; `cargo test
  --release --manifest-path engine/Cargo.toml --lib task_priority_tests` passes
  (3 tests, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht` passes (209 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `rustfmt --edition 2021 --check`
  on `completion/strategy.rs` passes; `git diff --check` passes; `cargo test
  --release --manifest-path engine/Cargo.toml --lib context_init_tests` passes
  (3 tests, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht` passes (212 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; direct `rustfmt --edition 2021
  --check` on `completion/context.rs` and `completion/u01.rs` passes; `cargo
  test --release --manifest-path engine/Cargo.toml --lib
  create_merge_branching_task_allocates_dependent_child` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  create_distinct_branching_task_allocates_dependent_child` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  context_init_tests` passes (3 tests, 0 failed); `cargo test --release
  --manifest-path engine/Cargo.toml --lib task_priority_tests` passes (3 tests,
  0 failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (212 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo test --release
  --manifest-path engine/Cargo.toml --lib priority_for_concept_uses_context_strategy`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib context_init_tests` passes (3 tests, 0 failed);
  `cargo test --release --manifest-path engine/Cargo.toml --lib konclude_ht`
  passes (213 tests, 0 failed); `cargo check --release --manifest-path
  engine/Cargo.toml` passes; direct `rustfmt --edition 2021 --check` on the
  W115-edited Rust files passes; `git diff --check` passes; `cargo test
  --release --manifest-path engine/Cargo.toml --lib individual_priority_tests`
  passes (3 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib context_init_tests` passes (3 tests, 0 failed);
  `cargo test --release --manifest-path engine/Cargo.toml --lib konclude_ht`
  passes (216 tests, 0 failed); `cargo check --release --manifest-path
  engine/Cargo.toml` passes; direct `rustfmt --edition 2021 --check` on the
  W116-edited Rust files passes; `git diff --check` passes; `cargo test
  --release --manifest-path engine/Cargo.toml --lib
  unsat_cache_retrieval_strategy_tests` passes (1 test, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib context_init_tests` passes
  (3 tests, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib cache_unsatisfiable_retrieval` passes (1 test, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib
  take_next_process_individual_prefers_cache_test_queue` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (219 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; direct `rustfmt --edition 2021
  --check` on the W117-edited Rust files passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  unsat_occurrence_retrieval_data` passes (1 test, 0 failed); `cargo test
  --release --manifest-path engine/Cargo.toml --lib
  node_unsat_retrieval_data_points_to_real_process_context_arena` passes (1 test,
  0 failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (221 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo fmt --manifest-path
  engine/Cargo.toml --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib caching_tags`
  passes (2 tests, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib concept_process_data_unsat_tag_slots_are_polarity_specific`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib occurrence_unsat_write_cache_tags` passes (2 tests, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (227 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo fmt --manifest-path
  engine/Cargo.toml --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  unsat_cache_handler` passes (2 tests, 0 failed); `cargo test --release
  --manifest-path engine/Cargo.toml --lib konclude_ht` passes (229 tests, 0
  failed); `cargo check --release --manifest-path engine/Cargo.toml` passes;
  `cargo fmt --manifest-path engine/Cargo.toml --check` passes; `git diff
  --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  unsat_cache_handler` passes (3 tests, 0 failed); `cargo test --release
  --manifest-path engine/Cargo.toml --lib konclude_ht` passes (230 tests, 0
  failed); `cargo check --release --manifest-path engine/Cargo.toml` passes;
  `cargo fmt --manifest-path engine/Cargo.toml --check` passes; `git diff
  --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  unsat_cache_handler` passes (5 tests, 0 failed); `cargo test --release
  --manifest-path engine/Cargo.toml --lib konclude_ht` passes (232 tests, 0
  failed); `cargo check --release --manifest-path engine/Cargo.toml` passes;
  `cargo fmt --manifest-path engine/Cargo.toml --check` passes; `git diff
  --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  test_individual_node_unsatisfiable_cached` passes (2 tests, 0 failed); `cargo
  test --release --manifest-path engine/Cargo.toml --lib konclude_ht` passes
  (234 tests, 0 failed); `cargo check --release --manifest-path
  engine/Cargo.toml` passes; `cargo fmt --manifest-path engine/Cargo.toml
  --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  add_indi_node_signature_of_unsatisfiable_clashed_descriptors` passes (1 test, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht` passes (235 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo fmt --manifest-path
  engine/Cargo.toml --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  unsat_cache_handler_write_clashed_descriptors` passes (1 test, 0 failed);
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  write_clash_descriptors_to_cache_forwards_to_installed_unsat_handler` passes
  (1 test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib konclude_ht` passes (237 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo fmt --manifest-path
  engine/Cargo.toml --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  unsat_cache_handler_write_clashed_concept` passes (1 test, 0 failed); `cargo
  test --release --manifest-path engine/Cargo.toml --lib konclude_ht` passes
  (238 tests, 0 failed); `cargo check --release --manifest-path
  engine/Cargo.toml` passes; `cargo fmt --manifest-path engine/Cargo.toml
  --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  classification_message_adapter_tracks_testing_concept_and_flags` passes (1
  test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib root_unsatisfiability_write_caches_writes_testing_concept_to_unsat_cache`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib konclude_ht` passes (240 tests, 0 failed); `cargo
  check --release --manifest-path engine/Cargo.toml` passes; `cargo fmt
  --manifest-path engine/Cargo.toml --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  saturation_node_expansion_handler_queues_unsat_concept_write_data` passes (1
  test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib saturation_node_expansion_handler_skips_already_clashed_concept` passes
  (1 test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib root_unsatisfiability_write_caches_queues_saturation_unsat_concept`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib konclude_ht` passes (243 tests, 0 failed); `cargo
  check --release --manifest-path engine/Cargo.toml` passes; `cargo fmt
  --manifest-path engine/Cargo.toml --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  computed_consequences_handler_commits_type_write_data_when_cacheable` passes
  (1 test, 0 failed); `cargo test --release --manifest-path engine/Cargo.toml
  --lib root_unsatisfiability_write_caches_commits_computed_consequence_for_nominal_root`
  passes (1 test, 0 failed); `cargo test --release --manifest-path
  engine/Cargo.toml --lib konclude_ht` passes (254 tests, 0 failed); `cargo
  check --release --manifest-path engine/Cargo.toml` passes; `cargo fmt
  --manifest-path engine/Cargo.toml --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  saturation_node_expansion_cache_ -- --nocapture` passes (4 tests, 0 failed);
  `cargo test --release --manifest-path engine/Cargo.toml --lib konclude_ht
  --quiet` passes (255 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml --quiet` passes; `cargo fmt
  --manifest-path engine/Cargo.toml --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  saturation_node_expansion_handler_ -- --nocapture` passes (5 tests, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht --quiet` passes (257 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml --quiet` passes; `cargo fmt
  --manifest-path engine/Cargo.toml --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  saturation_node_expansion_handler_ -- --nocapture` passes (8 tests, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht --quiet` passes (261 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml --quiet` passes; `cargo fmt
  --manifest-path engine/Cargo.toml --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  saturation_node_expansion_handler_ -- --nocapture` passes (10 tests, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht --quiet` passes (263 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo fmt
  --manifest-path engine/Cargo.toml --check` passes; `git diff --check` passes.
  `cargo test --release --manifest-path engine/Cargo.toml --lib
  saturation_node_expansion_handler_ -- --nocapture` passes (10 tests, 0
  failed); `cargo test --release --manifest-path engine/Cargo.toml --lib
  konclude_ht --quiet` passes (263 tests, 0 failed); `cargo check --release
  --manifest-path engine/Cargo.toml` passes; `cargo fmt
  --manifest-path engine/Cargo.toml --check` passes; `git diff --check` passes.

W346 ports the descriptor-based backend concept-label reader slice:
`ConceptDescriptorRecord` carries Konclude's separate concept identity, concept
tag, negation, dependency branch tag, and nominal flag;
`getConceptDescriptorSignature` overloads now hash the signed concept tag with
deterministic/nondeterministic, exclusion, and positive-nominal filters; and
the descriptor `getConceptSetLabelCacheEntry` overloads now match labels through
descriptor-derived cache values that preserve the concept-tag versus
concept-identity split. Focused release-binary filters `concept_descriptor` (5
tests) and `concept_set_label` (7 tests) pass; direct release-binary
`konclude_ht --quiet` passes (762 tests, 0 failed); `cargo check --release
--manifest-path engine/Cargo.toml`, `cargo fmt --manifest-path
engine/Cargo.toml --check`, and `git diff --check` pass.

W347 corrects associated-label reader fidelity over the live backend cache
records. Concept-label visitors now identify negation through both deterministic
and nondeterministic negated concept cache-value identifiers; combined neighbour
role-set visitors now use the full inverse-role predicate, including asserted,
nominal-connected, and nondeterministic inverse identifiers; and neighbour-array
cursor visits now honor Konclude's deterministic-only filter. Focused
release-binary filters `associated_` (10 tests) and `neighbour_array` (2 tests)
pass; direct release-binary `konclude_ht --quiet` passes (763 tests, 0 failed);
`cargo check --release --manifest-path engine/Cargo.toml`, `cargo fmt
--manifest-path engine/Cargo.toml --check`, and `git diff --check` pass.

W348 ports the first arena-backed signature-satisfiable expander cache linker
operations. `appendExpanderCacheValueLinker` now has a context-threaded variant
that traverses and tail-splices real `CExpanderCacheValueLinker` arena chains;
`CSignatureSatisfiableExpanderCacheHasher` now has context-threaded construction
from linker chains, qHash accumulation over cache values, and linker/linker
cache-value equality over the arena. Focused release-binary filter
`sig_expander` passes (3 tests); direct release-binary `konclude_ht --quiet`
passes (766 tests, 0 failed); `cargo check --release --manifest-path
engine/Cargo.toml`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W349 promotes those signature-satisfiable expander linker/hasher operations to
the canonical Rust API instead of leaving parallel `_context` helpers beside the
opaque stubs. `appendExpanderCacheValueLinker`, the linker-chain hasher
constructor, `operator==`, `calculateHashValue(CExpanderCacheValueLinker*,
cint64)`, and linker/linker cache-value equality now all require the live
`CacheContext` where Konclude dereferences `CExpanderCacheValueLinker*` chains.
Focused release-binary filter `sig_expander` passes (3 tests); direct
release-binary `konclude_ht --quiet` passes (766 tests, 0 failed); `cargo check
--release --manifest-path engine/Cargo.toml`, `cargo fmt --manifest-path
engine/Cargo.toml --check`, and `git diff --check` pass.

W350 ports `appendExpanderBranchedLinker` over the live
`CExpanderBranchedLinker` arena. The Rust method now threads `CacheContext`,
finds the tail of the incoming branched chain, appends the previous branched
head behind it, and installs the incoming chain as the new head, matching
Konclude's `linker->append(mExpandBranchedLinker)` order instead of dropping the
old chain. Focused release-binary filter `sig_expander` passes (4 tests);
direct release-binary `konclude_ht --quiet` passes (767 tests, 0 failed);
`cargo check --release --manifest-path engine/Cargo.toml`, `cargo fmt
--manifest-path engine/Cargo.toml --check`, and `git diff --check` pass.

W351 ports the signature-satisfiable expander reader's slot-release side
effects over the live slot arena. `updateSlot` now decrements the previously
pending updated slot through `CacheContext`, and `switchToUpdatedSlotItem` now
decrements the previous current slot when installing the updated slot, matching
Konclude's `prevSlot->decReader()` calls. Focused release-binary filter
`sig_expander` passes (6 tests); direct release-binary `konclude_ht --quiet`
passes (769 tests, 0 failed); `cargo check --release --manifest-path
engine/Cargo.toml`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W352 ports the signature-satisfiable expander write-data chain count and direct
write-data drain over the live write-data arena. `CLinkerBase::getCount` for
`CSignatureSatisfiableExpanderCacheEntryWriteData` now walks `getNext()` through
`CacheContext`, and the direct `writeCachedData` drain now resolves each
write-data node from the arena and dispatches by the tagged Konclude write-data
kind to the existing expand or satisfiable-branch writer bodies. Focused
release-binary filter `sig_expander` passes (7 tests); direct release-binary
`konclude_ht --quiet` passes (770 tests, 0 failed); `cargo check --release
--manifest-path engine/Cargo.toml`, `cargo fmt --manifest-path
engine/Cargo.toml --check`, and `git diff --check` pass.

W353 ports the signature-satisfiable expander cache-entry creation gate's
per-signature reference counts and upstream default thresholds. The Rust facade
now stores `mSignatureReferCountSet` as a real signature-to-count map, initializes
the gate with Konclude's constructor defaults (`200 MiB`, `100 MiB`, `1`, `1`),
and `canCreateCacheEntryForSignature` increments the selected signature before
checking `getRequiredSignatureReferCountForNextCacheEntryCreation`. The memory
threshold helper preserves Konclude's one-threshold-step-per-call behaviour.
Focused release-binary filter `sig_expander` passes (9 tests); direct
release-binary `konclude_ht --quiet` passes (772 tests, 0 failed); `cargo check
--release --manifest-path engine/Cargo.toml`, `cargo fmt --manifest-path
engine/Cargo.toml --check`, and `git diff --check` pass.

W354 ports the signature-satisfiable expander reader's signature-slot lookup
path. `CSignatureSatisfiableExpanderCacheSlotItem::mSigItemHash` is now a real
signature-to-redirection-item map, `hasCacheEntry(cint64)` checks that map after
performing the Konclude updated-slot switch, and `getCacheEntry(cint64)` resolves
the redirection item through the live arena to return the cached entry id.
Focused release-binary filter `sig_expander` passes (11 tests); direct
release-binary `konclude_ht --quiet` passes (774 tests, 0 failed); `cargo check
--release --manifest-path engine/Cargo.toml`, `cargo fmt --manifest-path
engine/Cargo.toml --check`, and `git diff --check` pass.

W355 ports the signature-satisfiable expander cache reader factory over the live
reader arena. `createCacheReader` now allocates a
`CSignatureSatisfiableExpanderCacheReader`, prepends it to `mReaderLinker` via
the reader's intrusive `next` link, and returns the new reader id, matching
Konclude's mutex-protected `reader->append(mReaderLinker)` path in the
single-threaded port. Focused release-binary filter `sig_expander` passes (12
tests); direct release-binary `konclude_ht --quiet` passes (775 tests, 0
failed); `cargo check --release --manifest-path engine/Cargo.toml`, `cargo fmt
--manifest-path engine/Cargo.toml --check`, and `git diff --check` pass.

W356 ports the signature-satisfiable expander cache's unused-slot unlink
traversal. `cleanUnusedSlots` now walks `mSlotLinker` through the live slot
arena, removes every slot whose `hasCacheReaders()` is false, updates either the
cache head or the previous live slot's `next` pointer exactly as Konclude does,
and keeps the memory-pool release as the remaining explicit pool-management
deferral. Focused release-binary filter `sig_expander` passes (14 tests); direct
release-binary `konclude_ht --quiet` passes (777 tests, 0 failed); `cargo check
--release --manifest-path engine/Cargo.toml`, `cargo fmt --manifest-path
engine/Cargo.toml --check`, and `git diff --check` pass.

W357 ports `createReaderSlotUpdate` over the live sig-expander slot and reader
arenas. The cache-level `mSigItemHash` is now a concrete signature-to-redirection
map, the new slot clones/detaches that map into its snapshot hash, the slot is
tail-appended to `mSlotLinker`, and every registered reader receives the updated
slot while the slot reader count is incremented. Memory-pool allocation remains
the explicit deferred part. Focused release-binary filter `sig_expander` passes
(16 tests); direct release-binary `konclude_ht --quiet` passes (779 tests, 0
failed); `cargo check --release --manifest-path engine/Cargo.toml`, `cargo fmt
--manifest-path engine/Cargo.toml --check`, and `git diff --check` pass.

W358 ports the signature-map/redirection portion of
`writeExpanderCachingData(prevSignature,newSignature,...)`. The facade now keeps
`mIncompatibleSigSet` and `mAlreadyExpSigSet` as real signature sets, rejects
duplicate new signatures by marking them incompatible, reuses the previous
signature's entry through the live redirection arena, marks reused entries as
multiple-expanded when Konclude's already-expanded set contains the previous
signature, allocates new entries/redirection items through `CacheContext`, and
inserts the new signature into `mSigItemHash`. The tag-hash/cache-value-list body
remains the separate deferred expansion slice. Focused release-binary filter
`sig_expander` passes (19 tests); direct release-binary `konclude_ht --quiet`
passes (782 tests, 0 failed); `cargo check --release --manifest-path
engine/Cargo.toml`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W359 ports the empty-branched-list side of
`writeSatisfiableBranchedCachingData`. The writer now resolves the signature
through the live `mSigItemHash` redirection map, retrieves the entry from the
arena, preserves the Konclude expandability check, sets
`mSatisfiableWithoutBranchedConcept` when the branched value list is null/empty,
and marks the entry satisfiable. The nonempty `CCACHINGLIST<CCacheValue>`
iteration and `CExpanderBranchedLinker` allocation remain the next explicit
deferred branch. Focused release-binary filter `sig_expander` passes (21 tests);
direct release-binary `konclude_ht --quiet` passes (784 tests, 0 failed);
`cargo check --release --manifest-path engine/Cargo.toml`, `cargo fmt
--manifest-path engine/Cargo.toml --check`, and `git diff --check` pass.

W360 ports the collected write-data dispatch path inside the sig-expander
`processCustomsEvents(WRITE_CACHED_DATA_ENTRY, ...)` branch. The direct
`writeCachedData` arena-chain dispatch is now shared with the collected
`mCollectWriteData` drain, so collected expand/satisfiable-branch write-data
nodes traverse the live write-data arena and call the same writer bodies as the
direct path. Event payload extraction and memory-pool collection remain deferred.
Focused release-binary filter `sig_expander` passes (22 tests); direct
release-binary `konclude_ht --quiet` passes (785 tests, 0 failed); `cargo check
--release --manifest-path engine/Cargo.toml`, `cargo fmt --manifest-path
engine/Cargo.toml --check`, and `git diff --check` pass.

W361 ports the live front gate of `isCachingDataExpandable`. The helper now
checks the concrete `mIncompatibleSigSet` and dereferences the cache entry arena
for `hasMultipleExpanded()` before entering the still-deferred tag-hash/cache
value comparison branch. The opaque cache-value-list traversal remains the next
deeper slice. Focused release-binary filter `sig_expander` passes (24 tests);
direct release-binary `konclude_ht --quiet` passes (787 tests, 0 failed);
`cargo check --release --manifest-path engine/Cargo.toml`, `cargo fmt
--manifest-path engine/Cargo.toml --check`, and `git diff --check` pass.

W362 ports the sig-expander cache-writer forwarding wrapper. `createCacheWriter`
now returns a concrete `CSignatureSatisfiableExpanderCacheWriter` port, and the
writer's `writeCachedData`, `writeExpandCached`, and
`writeSatisfiableBranchCached` methods forward into the live facade methods.
Rust threads the owning facade explicitly instead of storing a raw `this`
pointer. Focused release-binary filter `sig_expander` passes (26 tests); direct
release-binary `konclude_ht --quiet` passes (789 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `RUSTFLAGS=-Awarnings cargo check --release --manifest-path
engine/Cargo.toml`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W363 ports the sig-expander hasher's `CCACHINGSET<CCacheValue>` side. The cache
context now owns a typed sig-expander cache-value-set arena; the hasher set
constructor reads the live set count, `calculateHashValue(set)` iterates and
extends the hash, set/set comparison walks both sets in order, and linker/set
comparison checks membership while advancing the linker chain. The reader
`getCacheEntry(CCACHINGSET*)` lookup remains deferred until `mHasherItemHash` is
typed. Focused release-binary filter `sig_expander` passes (29 tests); direct
release-binary `konclude_ht --quiet` passes (792 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `RUSTFLAGS=-Awarnings cargo check --release --manifest-path
engine/Cargo.toml`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W364 ports the sig-expander reader's value-set lookup path over a typed
`mHasherItemHash`. Slot and facade hasher-item hashes now carry
`(CSignatureSatisfiableExpanderCacheHasher, redirection)` entries instead of
opaque handles, and `getCacheEntry(CCACHINGSET*)` builds the same set hasher and
searches the slot hash using `qHash` plus Konclude's `operator==` behavior. The
upstream equality quirk is preserved: a content-identical copied key still does
not match because `operator==` returns `false` after all checks. Focused
release-binary filter `sig_expander` passes (30 tests); direct release-binary
`konclude_ht --quiet` passes (793 tests, 0 failed); `RUSTFLAGS=-Awarnings cargo
test --release --manifest-path engine/Cargo.toml --lib --no-run`,
`RUSTFLAGS=-Awarnings cargo check --release --manifest-path engine/Cargo.toml`,
`cargo fmt --manifest-path engine/Cargo.toml --check`, and `git diff --check`
pass.

W365 ports the nonempty branch side of
`writeSatisfiableBranchedCachingData`. `CacheContext` now owns a typed
sig-expander `CCACHINGLIST<CCacheValue>` arena for branch payloads, the branch
write-data/facade signatures use that typed list id, and a nonempty
`branchedValueList` allocates a `CExpanderBranchedLinker`, appends each cache
value in list order, prepends the new branch linker chain to the entry, and sets
the entry satisfiable without setting the without-branched flag. Focused
release-binary filter `sig_expander` passes (31 tests); direct release-binary
`konclude_ht --quiet` passes (794 tests, 0 failed); `RUSTFLAGS=-Awarnings cargo
test --release --manifest-path engine/Cargo.toml --lib --no-run`,
`RUSTFLAGS=-Awarnings cargo check --release --manifest-path engine/Cargo.toml`,
`cargo fmt --manifest-path engine/Cargo.toml --check`, and `git diff --check`
pass.

W366 ports the deterministic expander write body. Entry tag hashes now use a
typed `tag -> CExpanderCacheValueLinker` map, `CacheContext` owns a typed
sig-expander dependency multihash, and `writeExpanderCachingData(entry,...)`
clones the tag hash, allocates fresh expander-value linkers from the typed cache
value list, recursively materializes dependency linkers with
`addExpanderCachingData`, stores the new tag hash, and appends the constructed
chain to the entry. At W366 time the local sig-expander `CCacheValue` still
remained the file's opaque `cint64`; W368 supersedes that caveat by wiring the
real F0 value type. Focused release-binary filter `sig_expander` passes (33 tests);
direct release-binary `konclude_ht --quiet` passes (796 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `RUSTFLAGS=-Awarnings cargo check --release --manifest-path
engine/Cargo.toml`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W367 ports the expander-cache expandability deep comparison/drain. The typed
`CCACHINGLIST<CCacheValue>` now supports `takeFirst()`, and
`isCachingDataExpandable` follows Konclude's destructive list consumption: for
incompatible or multiple-expanded signatures it compares each previous cache
value against the entry's tag-expander hash, rejecting missing or mismatching
stored linkers; otherwise it drains the previous deterministic expansion count.
Focused release-binary filter `sig_expander` passes (35 tests); direct
release-binary `konclude_ht --quiet` passes (798 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `RUSTFLAGS=-Awarnings cargo check --release --manifest-path
engine/Cargo.toml`, and `cargo fmt --manifest-path engine/Cargo.toml --check`
pass.

W368 reconciles sig-expander cache values to the real F0 `CCacheValue` port.
`sigexpand.rs` now uses `cache::value::CacheValue` instead of the temporary
opaque `cint64` alias, so expander hashing calls the real `qHash(CCacheValue)`,
tag extraction calls `CCacheValue::getTag()`, and expandable-data comparisons
use structural `CCacheValue` equality. Focused release-binary filter
`sig_expander` passes (35 tests); direct release-binary `konclude_ht --quiet`
passes (798 tests, 0 failed); `RUSTFLAGS=-Awarnings cargo test --release
--manifest-path engine/Cargo.toml --lib --no-run`, `RUSTFLAGS=-Awarnings cargo
check --release --manifest-path engine/Cargo.toml`, `cargo fmt --manifest-path
engine/Cargo.toml --check`, and `git diff --check` pass.

W369 ports `CComputedConsequencesCache::createCacheReader` over the typed cache
arena. The facade now allocates a real `CComputedConsequencesCacheReader` in
`CacheContext` and prepends it to `mReaderLinker`, matching Konclude's
`new CComputedConsequencesCacheReader(); mReaderLinker =
readerLinker->append(mReaderLinker)` body. Focused release-binary filter
`computed_consequences` passes (2 tests); direct release-binary
`konclude_ht --quiet` passes (799 tests, 0 failed); `RUSTFLAGS=-Awarnings cargo
test --release --manifest-path engine/Cargo.toml --lib --no-run`,
`RUSTFLAGS=-Awarnings cargo check --release --manifest-path engine/Cargo.toml`,
`cargo fmt --manifest-path engine/Cargo.toml --check`, and `git diff --check`
pass.

W370 ports `CComputedConsequencesCacheWriter::writeCacheData`. The writer now
forwards to the owning `CComputedConsequencesCache::writeCacheData` facade via
an explicit owner argument, mirroring Konclude's `mCache->writeCacheData(...)`
while avoiding a raw long-lived `this` pointer in Rust. Focused release-binary
filter `computed_consequences` passes (3 tests); direct release-binary
`konclude_ht --quiet` passes (800 tests, 0 failed); `RUSTFLAGS=-Awarnings cargo
test --release --manifest-path engine/Cargo.toml --lib --no-run`,
`RUSTFLAGS=-Awarnings cargo check --release --manifest-path engine/Cargo.toml`,
`cargo fmt --manifest-path engine/Cargo.toml --check`, and `git diff --check`
pass.

W371 reconciles `CComputedConsequencesCache::createCacheWriter` with the now-live
writer forwarding path. The source no longer marks the factory as deferred: it
returns the structural writer object and documents the explicit-owner forwarding
used by W370 instead of a raw C++ `this` pointer. This was a comment/status-only
stale-marker cleanup after W370; `cargo fmt --manifest-path engine/Cargo.toml
--check` and `git diff --check` pass.

W372 ports the typed `CComputedConsequencesCacheWriteData` install chain through
`CComputedConsequencesCache::installWriteCacheData`. The base write-data object
now carries the same-family next link, the install loop resolves each write-data
node from `CacheContext`, dispatches by the Konclude write-data type tag, follows
`getNext()`, and the `CCWT_TYPE` branch reads individual/concept/negation from
the typed `CComputedConsequencesCacheWriteTypesData` payload. The remaining
boundary is the downstream individual-process-data cache-entry bridge plus
cache-entry concept-linker insertion, so the dispatch is live while the final
entry mutation remains explicitly deferred. Focused release-binary filter
`computed_consequences` passes (4 tests); direct release-binary
`konclude_ht --quiet` passes (801 tests, 0 failed); `RUSTFLAGS=-Awarnings cargo
test --release --manifest-path engine/Cargo.toml --lib --no-run`,
`RUSTFLAGS=-Awarnings cargo check --release --manifest-path engine/Cargo.toml`,
`cargo fmt --manifest-path engine/Cargo.toml --check`, and `git diff --check`
pass.

W373 ports the F8 computed-consequences write event payload into the live
`CComputedConsequencesCache::processCustomsEvents` branch. `CacheEvent` now
carries the real `CComputedConsequencesCacheWriteData` id instead of a local F8
placeholder, and `process_customs_cache_event` matches Konclude's event handler
body by reading `getWriteData()` / `getMemoryPools()` from the typed event,
installing the write-data chain, and leaving only memory-pool release deferred.
The old integer `process_customs_events` wrapper remains as an opaque Qt-style
compatibility path, but its stale payload-extraction deferrals are gone. Focused
release-binary filter `computed_consequences` passes (5 tests); direct
release-binary `konclude_ht --quiet` passes (802 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W399 ports the bounded computed-consequences individual entry bridge. The
previously deferred `CIndividualProcessData::get/setComputedConsequencesCachingData`
slot is represented as a minimal typed `CacheContext` association from
`IndividualId` to `CComputedConsequencesTypesCacheEntry`. The reader lookup,
`getComputedTypesCacheEntryForNode` reuse/create path, and
`addTypesExpansionData` concept-link insertion are live and preserve Konclude's
head-prepend concept-linker order. Focused validation only:
`cargo test --manifest-path engine/Cargo.toml computed_consequences --lib`
passes (8 tests, 1033 filtered out). This is not a full-port completion claim.

W400 ports the typed F8 sig-expander cache-event payload path for
`CSignatureSatisfiableExpanderCache::processCustomsEvents`. `CacheEvent` now
carries the real signature-expander value-list, dependency-hash, and write-data
ids for `CWriteExpandCachedEvent`, `CWriteSatisfiableBranchCachedEvent`, and
`CWriteCachedDataEvent`. The new `process_customs_cache_event` body extracts
the typed payloads, calls `writeExpanderCachingData`,
`writeSatisfiableBranchedCachingData`, and the collect/drain write-data path at
the Konclude branch points, while preserving the old opaque integer wrapper for
legacy call sites. Focused release filter `sig_expander_typed_` passes (3
tests). Direct release-binary `konclude_ht --quiet` now passes (853 tests, 0
failed). This is not a full-port completion claim.

W401 ports the first live read path of
`CSatisfiableExpanderCacheHandler::isIndividualNodeExpandCached` plus
`compareIndividualNodeCompatibility`. The handler now owns a typed
signature-expander cache reader/context, reads the node's reapply concept-label
set signature, retrieves the cached entry by signature, rejects entries whose
expander count is smaller than the label-set concept count, and compares cached
concept/tag/negation values against the live process descriptor arena. The
remaining satisfiable-expander writer/dependency collection methods are still
deferred. Focused release filter `satisfiable_expander_handler_` passes (3
tests). Release lib `--no-run` and direct release-binary `konclude_ht --quiet`
now pass (856 tests, 0 failed). This is not a full-port completion claim.

W402 ports the real
`CBranchingMergingIndividualNodeCandidateLinker` process class. The old
zero-size placeholder is replaced by a typed linker payload with `next`,
`mMergingIndiNodeCandidate`, and `mMergingLink`; the port now exposes the
Konclude init/copy, node/link getter-setter, `getNext`, `clearNext`,
`append`, `isCandidateBlockableAndCreator`, and always-true `operator<=`
surfaces. `ProcessContext` now owns an arena/accessor trio for candidate
linkers. The BM-1 restriction-spec caller methods still carry their
`W2-DEFER[api]` call-site markers until a follow-up pass threads
`ProcessContext` through those methods. Focused release filter
`branching_merging_candidate_linker_` passes (3 tests). Direct release-binary
`konclude_ht --quiet` now passes (859 tests, 0 failed). This is not a
full-port completion claim.

W403 ports the live reader/slot publication path for
`CReuseCompletionGraphCache`. `createCacheReader` now allocates real
`CReuseCompletionGraphCacheReader` records in `CacheContext`; `updateSlot` and
`switchToUpdatedSlotItem` now exchange typed slot ids and decrement previous
slots; `createReaderSlotUpdate` now clones `mEntyHash` into a real
`CReuseCompletionGraphCacheSlotItem`, records `mEntryCount`, appends the slot,
increments its reader count, and publishes it to every reader; `cleanUnusedSlots`
now filters by the real `hasCacheReaders`; and the event drain is
`CacheContext`-threaded so expand writes publish a slot. Focused release filter
`reuse_cache_` passes (5 tests). Direct release-binary `konclude_ht --quiet`
now passes (864 tests, 0 failed). Source marker counts now include `783
W6-DEFER`, `728 W3-DEFER`, `318 W2-DEFER`, `214 W4-DEFER`, and
`230 PORT-PENDING`. This is not a full-port completion claim.

W404 ports the live reader/slot publication path for
`CBackendRepresentativeMemoryCache`. `createReaderSlotUpdate` now copies the
ontology-id -> ontology-data hash into a real backend slot, updates the
published ontology data minimum-valid recomputation id, marks the slot update
integrated, appends the slot, increments ontology usage counts, and publishes
the slot to every reader. `BackendRepresentativeMemoryCacheReader::updateSlot`
now swaps typed slot ids and decrements a previously published slot, and the new
context-threaded `switchToUpdatedSlotItem` helper switches current slots,
decrements the old current slot, refreshes ontology data, and updates the
recomputation-reference linker. `cleanUnusedSlots` now filters by real
`hasCacheReaders`, decrements ontology usage counts, marks recomputation
references inactive when usage reaches zero, and bumps release counters. Focused
release filter `backend_cache_` passes (5 tests). Direct release-binary
`konclude_ht --quiet` now passes (867 tests, 0 failed). Source marker counts now
include `771 W6-DEFER`, `728 W3-DEFER`, `318 W2-DEFER`, `214 W4-DEFER`, and
`230 PORT-PENDING`. This is not a full-port completion claim.

W405 continues the backend representative-memory reader port. The reader lookup
surface now threads mutable `CacheContext` through the normal cache-entry,
label-entry, individual-association, associated-label, and nominal-indirect
connection methods, so pending reader slots are consumed by the real
`switchToUpdatedSlotItem` path before those reads. `checkRecomputationIdUsage`
now sets `mRecomputationId`, consumes an updated slot, resolves missing ontology
data from the current slot, rejects recomputation ids older than
`getMinimumValidRecomputationId`, and updates the ontology-data recomputation
reference linker. `setWorkingOntology(cint64)` now consumes an updated slot,
refreshes `mOntologyData` from the current slot, and then applies
`mFixedOntologyData`, matching Konclude's exact ordering; the shared slot-switch
helper was corrected not to apply the fixed-ontology override itself. The stale
no-context switch wrapper and stale reader lookup W6 comments are gone. Focused
release filter `backend_cache_` passes (8 tests). Direct release-binary
`konclude_ht --quiet` now passes (870 tests, 0 failed). Source marker counts now
include `762 W6-DEFER`, `728 W3-DEFER`, `318 W2-DEFER`, `214 W4-DEFER`, and
`230 PORT-PENDING`. This is not a full-port completion claim.

W406 ports the live context-threaded body of
`CBackendRepresentativeMemoryCache::getIndividualAssociationDataMemoryContext`.
The method now dereferences the localized individual association data through
`CacheContext`, returns the raw handle for an existing
`IndividualAssociationContext`, and sets `requiresDataCopying` when Konclude's
exact condition holds: usage count `<= 1` and previous memory-management count
`> 0`. Without a separate individual context it returns the ontology data's
ontology-context raw handle. The no-context deferred wrapper remains only for
older facade stubs whose surrounding methods still do not receive
`CacheContext`. Focused release filter
`individual_association_data_memory_context` passes (2 tests). Direct
release-binary `konclude_ht --quiet` now passes (872 tests, 0 failed). Source
marker counts now include `760 W6-DEFER`, `728 W3-DEFER`, `318 W2-DEFER`, `214
W4-DEFER`, and `230 PORT-PENDING`. This is not a full-port completion claim.

W407 ports the concrete process assertion linker records used by
`CIndividualProcessNode` add methods. `CProcessAssertedDataLiteralLinker`,
`CAdditionalProcessRoleAssertionsLinker`, and
`CAdditionalProcessDataAssertionsLinker` now have real records with `next`
links, payload fields, dependency track points, and Konclude init/getter
surfaces. `ProcessContext` owns typed arenas for the three linker classes.
`addAssertedDataLiteralLinker`, `addAdditionalRoleAssertionsLinker`, and
`addAdditionalDataAssertionsLinker` now take the process context, set the
incoming linker's `next` to the old head, and install it as the new head,
matching Konclude's `linker->append(oldHead)` semantics instead of replacing
the chain head. Focused release filter `process_assertion_linker_` passes
(3 tests). Direct release-binary `konclude_ht --quiet` now passes (875 tests,
0 failed). Source marker counts now include `760 W6-DEFER`, `728 W3-DEFER`,
`314 W2-DEFER`, `214 W4-DEFER`, and `230 PORT-PENDING`. This is not a full-port
completion claim.

W408 ports the candidate-linker-dependent parts of
`CBranchingMergingProcessingRestrictionSpecification`. The merging-candidate
and initialization-candidate take/add methods now resolve
`CBranchingMergingIndividualNodeCandidateLinker` through `ProcessContext`,
using the real `getNext`, `clearNext`, append-to-tail chain operation, edge
dependency-track lookup, and node nominal/blockable checks. The add path now
records the first blockable creator candidate's dependency track point, counts
incoming candidates, and routes nominal candidates to
`mNominalMergingNodesLinker` while blockable candidates go to
`mMergingNodesLinker`. The initialization and qualifier candidate-chain append
methods are live as well. The only `W2-DEFER` left in `bm1.rs` is the separate
base `CProcessingRestrictionSpecification::initProcessingRestriction` call.
Focused release filter `bm_` passes (2 tests). Direct release-binary
`konclude_ht --quiet` now passes (877 tests, 0 failed). Source marker counts
now include `760 W6-DEFER`, `728 W3-DEFER`, `279 W2-DEFER`, `214 W4-DEFER`,
and `230 PORT-PENDING`. This is not a full-port completion claim.

W409 reconciles the already-ported PN-6 satellite classes with
`CIndividualProcessNode`'s lazy accessor bodies. `getNominalCachingLossReactivationData`
now allocates `CNominalCachingLossReactivationData` through `ProcessContext`,
initializes it with the node id and previous `mUseReactivationData`, and stores
the new id in both local/use fields. `getSuccessorNominalConnectionSet`,
`hasSuccessorConnectionToNominal`, and `addSuccessorConnectionToNominal` now use
the typed `CSuccessorConnectedNominalSet` arena and preserve Konclude's lazy
copy-from-use behavior. `getIncrementalExpansionData` and
`getIndividualMergingHash` now allocate concrete
`CIndividualNodeIncrementalExpansionData` and `CIndividualMergingHash` records
initialized from their previous `mUse...` generations. The active
`addIndividualToIncrementalExpansionQueue` caller now reads existing incremental
expansion data through the context-threaded node helper. The only `W2-DEFER`
markers left in `pn6.rs` are the still-unported successor-ATMOST reactivation
data and datatype value-space data satellites. Focused release filter `pn6_`
passes (3 tests). Direct release-binary `konclude_ht --quiet` now passes
(880 tests, 0 failed). Source marker counts now include `760 W6-DEFER`,
`728 W3-DEFER`, `271 W2-DEFER`, `214 W4-DEFER`, and `230 PORT-PENDING`. This
is not a full-port completion claim.

W410 reconciles the remaining DB-4 candidate-hash lazy getters with
`CProcessingDataBox`'s Konclude allocation pattern.
`getSignatureBlockingCandidateHash`,
`getSignatureNominalDelayingCandidateHash`,
`getBlockingIndividualNodeCandidateHash`, and
`getBlockingIndividualNodeLinkedCandidateHash` now delegate through
`ProcessContext`, allocate the concrete hash records, initialize from the
previous `mUse...` generation when present, and store the new id in both
local/use fields. Completion-context wrappers now expose those four accessors,
and active completion callers use the wrappers instead of localized allocation
shims or stale self-only databox calls. `process/db4.rs` now has no `W2-DEFER`
markers. Focused release filter `db4_` passes (4 tests). Source marker counts
now include `760 W6-DEFER`, `728 W3-DEFER`, `266 W2-DEFER`, `214 W4-DEFER`,
and `230 PORT-PENDING`. This is not a full-port completion claim.

W411 closes the remaining BM-1 base-class deferral by porting the
`CProcessingRestrictionSpecification` methods used by
`CBranchingMergingProcessingRestrictionSpecification`.
`initProcessingRestriction(prev)` now copies `CLinkerBase<double>` data from
the previous restriction when present and resets it to `0.` otherwise, while
leaving the next-link untouched exactly as Konclude's `setData(...)` body does.
The collapsed Rust restriction record now exposes
`getNextProcessingRestrictionSpecification`, `getPriorityOffset`, and
`setPriorityOffset`; `initBranchingMergingProcessingRestriction` calls the base
init before copying subclass fields. `process/bm1.rs` now has no `W2-DEFER`
markers. Focused release filter `bm_` passes (3 tests). Source marker counts
now include `760 W6-DEFER`, `728 W3-DEFER`, `265 W2-DEFER`, `214 W4-DEFER`,
and `230 PORT-PENDING`. This is not a full-port completion claim.

W412 closes the last PN-6 lazy-allocation deferrals for `CIndividualProcessNode`.
`getSuccessorIndividualATMOSTReactivationData` and
`getDatatypesValueSpaceData` now thread `ProcessContext`, allocate typed
placeholder arena records, initialize from the previous `mUse...` generation,
and store the new id in both local/use fields. `ProcessContext` also exposes
create/existing node helpers for both satellites, so later completion/datatype
code can call these exact node accessors without self-only allocation shims.
`process/pn6.rs` now has no `W2-DEFER` markers; the two payload classes remain
zero-size placeholders until their own Konclude methods are ported. Focused
release filter `pn6_` passes (4 tests). Source marker counts now include
`760 W6-DEFER`, `728 W3-DEFER`, `263 W2-DEFER`, `214 W4-DEFER`, and
`230 PORT-PENDING`. This is not a full-port completion claim.

W413 reconnects DB-2 `CProcessingDataBox` lazy hash getters to the exact
`ProcessContext` helper bodies that were already ported and tested.
`getConceptNominalSchemaGroundingHash`,
`getVariableBindingPathMergingHash`,
`getRepresentativeVariableBindingPathSetHash`,
`getRepresentativeVariableBindingPathJoiningKeyHash`,
`getRepresentativeJoiningHash`, and `getMarkerIndividualNodeHash` now take
`ProcessContext` and delegate to the shared helper that allocates, initializes
from the previous `mUse...` generation, restores the previous object, and stores
the new local/use id. The helper-level tests already verify copied/restored
previous-generation content; the new DB-2 test covers the direct wrapper path
and reuse behavior. Remaining DB-2 W2 boundaries are the extended concept
vector, unported `CRepresentativeVariableBindingPathHash`, unported
`CNominalCachingLossReactivationHash`, and saturation-resolved successor id
seeding from saturation/ABox/triples data. Focused release filter `db2_` passes
(1 test). Source marker counts now include `760 W6-DEFER`, `728 W3-DEFER`,
`257 W2-DEFER`, `214 W4-DEFER`, and `230 PORT-PENDING`. This is not a
full-port completion claim.

W414 reconciles the PN-4 `CIndividualProcessNode` blocking-follow accessors
with the already-ported `CBlockingFollowSet` arena.
`getBlockingFollowSet(createOrLocalize)` now threads `ProcessContext`, allocates
a typed `CBlockingFollowSet`, initializes it from `mPrevSigBlockFollowSet`, and
stores the new id in both `mSigBlockFollowSet` and `mUseSigBlockFollowSet`.
`hasBlockingFollower` now follows Konclude's exact empty-state predicate:
false for no set, false for an allocated empty set, and true only when the
referenced follow set is non-empty. Active completion code still uses the
context-first `ProcessContext::node_*` helpers for arena-owned nodes. The only
`W2-DEFER` marker left in `process/pn4.rs` is the separate
`CIndividualNodeAnalizedConceptExpansionData` lazy allocation. Focused release
filter `pn4_` passes (2 tests). Source marker counts now include
`760 W6-DEFER`, `728 W3-DEFER`, `255 W2-DEFER`, `214 W4-DEFER`, and
`230 PORT-PENDING`. This is not a full-port completion claim.

W415 reconciles `CDependencyTrackPoint::addClashes` with Konclude's
`CClashedDependencyDescriptor::append(oldHead)` chain semantics. The Rust method
now threads `ProcessContext`, appends the existing clash chain after the
incoming chain tail, installs the incoming head, and ORs the clashed/irrelevant
flag only for non-null incoming chains. Null input remains a no-op. Focused
release filter `dep2_` passes (2 tests). Source marker counts now include
`760 W6-DEFER`, `728 W3-DEFER`, `254 W2-DEFER`, `214 W4-DEFER`, and
`230 PORT-PENDING`. This is not a full-port completion claim.

W416 reconciles three SAT-1 `CIndividualSaturationProcessNode` APIs with
their concrete Konclude substrates. `getRoleBackwardPropagationHash(create)`
now has a context-threaded allocation path through the existing
`CRoleBackwardSaturationPropagationHash` arena; `getReapplyConceptSaturationLabelSet(create)`
has a context-threaded allocation path through the existing
`CReapplyConceptSaturationLabelSet` arena; and
`take/addConceptSaturationProcessLinker` now preserve intrusive linker chains
instead of dropping or overwriting tails. Active saturation callers use the new
context helper for `takeConceptSaturationProcessLinker` to avoid aliasing the
node and linker arena. Focused release filter `sat1_` passes (8 tests). Source
marker counts now include `760 W6-DEFER`, `728 W3-DEFER`, `250 W2-DEFER`,
`214 W4-DEFER`, and `230 PORT-PENDING`. This is not a full-port completion
claim.

W417 reconciles the PN-3 role-successor read surface with the already-live
`CReapplyRoleSuccessorHash` backend. New `ProcessContext` wrappers expose
Konclude's `getRoleSuccessorLinkIterator`, `getRoleSuccessorCount`,
`getRoleSuccessorHistoryLinkIterator`, `hasRoleSuccessorToIndividual`,
`getRoleSuccessorToIndividualLink`, and `getRoleIterator` semantics while
preserving the Rust arena ownership boundary; the old self-only PN-3 methods now
point at these context-backed routes instead of carrying active W2 deferrals.
Focused debug filter `pn3_context_role_successor_wrappers_read_installed_links`
passes (1 test). Source marker counts now include `760 W6-DEFER`,
`728 W3-DEFER`, `244 W2-DEFER`, `214 W4-DEFER`, and `230 PORT-PENDING`. This is
not a full-port completion claim.

W418 reconciles the final DB-1 parent databox individual-process-node vector
handoff. `initProcessingDataBox(CProcessingDataBox*)` now applies Konclude's
`mIndiProcessVector->referenceVector(prevIndiProcVec)` step by installing the
saved parent `CIndividualProcessNodeVector` contents into the child databox's
owned Rust vector after reset/copy. Focused debug filter `db1_parent_init_`
passes (2 tests). Source marker counts now include `760 W6-DEFER`,
`728 W3-DEFER`, `243 W2-DEFER`, `214 W4-DEFER`, and `230 PORT-PENDING`. This is
not a full-port completion claim.

W419 ports the DEP-1/DEP-2 branch-tag propagation substrate:
`CDependencyNode::getDependedBranchingTag`,
`getDependedBranchingLevel`,
`updateDependencyTrackPointBranchingTag`,
`CDeterministicDependencyNode::updateBranchingTag`,
`CNonDeterministicDependencyNode::updateBranchingTags`, and the folded
`getDependencyTrackPointBranch` opener now run over the real dependency-link and
track-point arenas. Deterministic initializers update their process tag from
Konclude's walked dependency surface, representative additional dependencies
raise the tag through `mAdditionalAfterDepLinker`, missing additional
track-points force the `-1` sentinel, and OR/reuse-backend non-deterministic
branches raise existing branch track points. Focused debug filter `dep1_branch`
passes (5 tests). Source marker counts now include `760 W6-DEFER`,
`728 W3-DEFER`, `235 W2-DEFER`, `214 W4-DEFER`, and `230 PORT-PENDING`. This is
not a full-port completion claim; the remaining branch-tag W2 notes are
completion-factory call-site threading, not this DEP substrate.

W420 reconciles the Unit 32 extended-debug propagation-cut reader with the
already-live `CBackendNeighbourExpansionControllingData` port. The debug model
path now calls `getBackendNeighbourExpansionControllingData(false)`, walks
`getCutBackendNeighbourExpansionIndividualLinker()`, and records each cut
node's `getIndividualNodeID()` value just as Konclude does; the broader
individual-vector bounds and rendering passes remain explicitly deferred.
Focused debug filter `extended_debug_collects_backend_cut_individual_node_ids`
passes (1 test). Source marker counts now include `759 W6-DEFER`,
`728 W3-DEFER`, `235 W2-DEFER`, `214 W4-DEFER`, and `230 PORT-PENDING`. This is
not a full-port completion claim.

W421 wires the first completion dependency factory call sites into the live
branch-tag substrate. `ProcessContext` now exposes deterministic and
non-deterministic branch-tag update helpers that keep the raw dependency arenas
private. `createDATAASSERTIONDependency` updates before materializing its
continuation point, and deterministic continuation materialization copies the
node's current branching tag to match the C++ multiple-inheritance identity.
Unit 29's ready deterministic and non-deterministic factory wrappers now call
the helpers, including ATMOST/QUALIFY, the reuse family, ORONLYOPTION,
IMPLICATION, EXPANDED, CONNECTION, and the reuse-backend fixed/prioritized/value
wrappers. Focused debug filters for DATAASSERTION, ATMOST, QUALIFY, reuse
wrappers, and reuse-backend wrappers pass, with tests asserting nonzero
branch-tag propagation through clash/continuation points. Source marker counts
now include `759 W6-DEFER`, `728 W3-DEFER`, `222 W2-DEFER`, `214 W4-DEFER`, and
`230 PORT-PENDING`. This is not a full-port completion claim; Unit 28 factory
wrappers still carry the remaining branch-tag W2 call-site notes.

W422 wires Unit 28's dependency factory wrappers into the live branch-tag
substrate. The representative, variable-binding, binding-propagation,
nominal/value/role-assertion, automata, SOME/SELF, ALL/FUNCTIONAL/DISTINCT,
ATLEAST, and OR wrappers now call the context-owned branch-tag helpers after
their previous/additional dependency fields are installed and before
continuation materialization. Focused debug filters for representative,
varbind/propagate, AND, and OR wrappers pass; tests now assert nonzero
branch-tag propagation through deterministic continuation and OR clash track
points, including the `RESOLVEREPRESENTATIVE` additional-dependency max case.
Source marker counts now include `759 W6-DEFER`, `728 W3-DEFER`, `185 W2-DEFER`,
`214 W4-DEFER`, and `230 PORT-PENDING`. This is not a full-port completion
claim.

W423 continues SAT-1 by wiring additional `CIndividualSaturationProcessNode`
lazy getters to already-live context-owned substrates. The self-only
compatibility methods now point callers at exact context-threaded routes for
`getIndividualExtensionData`, `getLinkedRoleSuccessorHash`,
`getNominalHandlingData`, and `getSuccessorConnectedNominalSet`. Those routes
reuse the existing `CIndividualSaturationProcessNodeExtensionData`,
`CLinkedRoleSaturationSuccessorHash`,
`CSaturationIndividualNodeNominalHandlingData`, and
`CSuccessorConnectedNominalSet` arenas and preserve Konclude's create/reuse vs
`create == false` null-return behavior. Focused debug filter `sat1_` passes
(11 tests), including lazy allocation/reuse coverage for the new wrappers.
Source marker counts now include `759 W6-DEFER`, `728 W3-DEFER`,
`179 W2-DEFER`, `214 W4-DEFER`, and `230 PORT-PENDING`. This is not a
full-port completion claim.

W424 extends the PN-3 context-threaded successor/disjoint surface. The port now
exposes exact `CIndividualProcessNode` context wrappers for
`hasNegationDisjointToIndividual`, disjoint successor-role link lookup,
`removeDisjointLinks`, and `getConnectionSuccessorIterator`, all backed by the
already-ported `CDisjointSuccessorRoleHash` and `CConnectionSuccessorSet`
substrates. `node_remove_individual_link` was corrected to match Konclude's
body exactly: it removes only from `mUseReapplyRoleSuccHash`; topology removal
remains in `removeIndividualConnection`. Focused debug filter `pn3_context`
passes (2 tests), including disjoint install/read/iterate/remove and the
separate role-link vs successor-connection removal semantics. Source marker
counts remain `759 W6-DEFER`, `728 W3-DEFER`, `179 W2-DEFER`,
`214 W4-DEFER`, and `230 PORT-PENDING` because the old `pn3.rs` no-context
compatibility methods still carry their call-site W2 notes. This is not a
full-port completion claim.

W425 reconciles SAT-1's initialized/completed status-bit helpers with the
already-ported `CIndividualSaturationProcessNodeStatusFlags` substrate. The
node setters now call the exact Konclude masks `INDSATFLAGINITIALIZED` (`0x1000`)
and `INDSATFLAGCOMPLETED` (`0x2000`) via the live `hasFlags`/`setFlags`
helpers instead of the temporary `0x1`/`0x2` placeholder bits. Focused debug
filter `sat1_` passes (12 tests), including direct/indirect flag assertions for
the exact masks. Source marker counts now include `759 W6-DEFER`,
`728 W3-DEFER`, `178 W2-DEFER`, `214 W4-DEFER`, and `230 PORT-PENDING`. This is
not a full-port completion claim.

W426 ports the remaining SAT-1 append sites whose typed intrusive-link
substrates already exist. `addInitializingBackwardPropagationLinks` now threads
`ProcessContext` and appends the incoming `CBackwardSaturationPropagationLink`
chain tail to the old head, matching
`backwardPropLinks->append(mInitBackwardPropLinks)`. Likewise,
`addClashedConceptSaturationDescriptorLinker` appends the incoming
`CConceptSaturationDescriptor` chain through
`ProcessContext::append_concept_saturation_descriptor_chain`, matching
`clashConSatDes->append(mClashedConSatDesLinker)`. Focused debug filter
`sat1_` passes (14 tests), including explicit multi-link chain-order tests.
Source marker counts now include `759 W6-DEFER`, `728 W3-DEFER`,
`176 W2-DEFER`, `214 W4-DEFER`, and `230 PORT-PENDING`. This is not a full-port
completion claim.

W427 ports LS-1's plain-insert concept-signature side effect. The
`insertConceptIgnoreClash`, `insertConceptGetClash`, and
`insertConceptReturnClash` paths now call the already-ported
`CConceptSetSignature` formula through `add_concept_descriptor_signature` when a
descriptor is newly inserted, and the resolved insert overload updates the
signature from the caller's arena-backed concept/tag/negation data. Exact
focused filters `label_set_resolved_insert_updates_signature_once` and
`concept_set_signature_matches_konclude_formula` pass. This wave does not reduce
the LS-1 W2 marker count because the remaining comments now point at the still
deferred descriptor dereference, concept flags, structure, and linker-chain
gaps.

W428 reconciles PN-3 iterator return types with the already-ported iterator
substrates. The node-level empty-return methods for role successor, role
successor-link, successor-role, successor, disjoint-role, and role-reapply
iteration now use the real iterator implementations from `rs1`,
`succ_role_hash`, and `distinct`; the context-threaded `ProcessContext::node_*`
routes remain the live arena-backed dereference path. This removes stale local
placeholder iterator structs, three W2 markers, and one stale reconcile note.
Focused debug filter `pn3_context` passes (2 tests). Source marker counts after
the parallel W426-W428 work now include `759 W6-DEFER`, `728 W3-DEFER`,
`173 W2-DEFER`, `214 W4-DEFER`, `230 PORT-PENDING`, and
`32 RECONCILE-NEED`. This is not a full-port completion claim.

W374 ports
`CBackendRepresentativeMemoryCache::checkBasicPrecompuationModeActivation`.
The method now dereferences the backend `OntologyData` from `CacheContext` and
implements Konclude's exact guard: association not completed, activation not
already set, incompletely handled individual count positive, configured ratio
positive, merge count positive, and merge/direct-update ratio strictly greater
than `mConfBasicPrecomputationModeActivationUpdateMergesRatio`. Focused
release-binary filter `backend_basic_precomputation` passes (3 tests); direct
release-binary `konclude_ht --quiet` passes (805 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W375 ports
`CBackendRepresentativeMemoryCache::debugCheckNeighoursCorrectlyCounted`. The
method now walks the backend association-data neighbour-array graph from
`CacheContext`: association data -> role-set neighbour array -> index-data array
size -> per-slot neighbour data -> individual-id linker chain. It returns false
on the same mismatch Konclude checks, namely when the linker count differs from
the stored `getIndividualCount()`, and otherwise returns true; the local C++
`debug = false` file-dump branches remain inert. Focused release-binary filter
`backend_debug_neighbour_count` passes (3 tests); direct release-binary
`konclude_ht --quiet` passes (808 tests, 0 failed); `RUSTFLAGS=-Awarnings cargo
test --release --manifest-path engine/Cargo.toml --lib --no-run`,
`cargo fmt --manifest-path engine/Cargo.toml --check`, and `git diff --check`
pass.

W376 ports `CBackendRepresentativeMemoryCache::checkAssociationComplete`.
The method now evaluates Konclude's completion guard over live `OntologyData`,
sets association-completed, increments usage, publishes the ontology id into
`mFixedOntologyIdentifierDataHash`, preserves the log-data read and optional
late-index/debug call sites, and leaves only those sibling bodies deferred.
Focused release-binary filter `backend_check_association_complete` passes (3
tests); direct release-binary `konclude_ht --quiet` passes (811 tests, 0
failed); `RUSTFLAGS=-Awarnings cargo test --release --manifest-path
engine/Cargo.toml --lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml
--check`, and `git diff --check` pass.

W377 ports
`CBackendRepresentativeMemoryCache::debugTestingPrioritizedExpansionLinkDuplicates`.
The method now follows Konclude's read-only debug walk: resolve the neighbour
array index data, lookup the prioritized propagation mark label index, visit the
corresponding neighbour-individual linker chain, and record duplicate ids in the
same inert local debug branch while still returning true. Focused release-binary
filter `backend_debug_prioritized_duplicate` passes (2 tests); direct
release-binary `konclude_ht --quiet` passes (813 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W378 ports `CBackendRepresentativeMemoryCache::copyNeighbourIndividualIdLinkers`.
The method now deep-copies the Rust head-front linker chain that represents
Konclude's `CBackendRepresentativeMemoryCacheIndividualRoleSetNeighbourIndividualIdLinker*`
chain, allocates fresh linkers in `CacheContext`, preserves payload order, and
increments `mStatIndividualAssociationSeparateMemoryManagmentNeighbourLinkCopyingCount`
once per copied link. Focused release-binary filter `backend_copy_neighbour`
passes (2 tests); direct release-binary `konclude_ht --quiet` passes (815
tests, 0 failed); `RUSTFLAGS=-Awarnings cargo test --release --manifest-path
engine/Cargo.toml --lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml
--check`, and `git diff --check` pass.

W379 ports `CBackendRepresentativeMemoryCache::activateBasicPrecompuationMode`.
The method now reads and mutates live `OntologyData`, flips the basic
precomputation activation/mode flags once, snapshots the current individual-id
association-data vector into the basic-precomputation vector, preserves the
context/update-count/merge-count log-data reads, and returns false for repeated
or null activation. Focused release-binary filter
`backend_activate_basic_precomputation` passes (2 tests); direct release-binary
`konclude_ht --quiet` passes (817 tests, 0 failed); `RUSTFLAGS=-Awarnings cargo
test --release --manifest-path engine/Cargo.toml --lib --no-run`,
`cargo fmt --manifest-path engine/Cargo.toml --check`, and `git diff --check`
pass.

W380 ports `CBackendRepresentativeMemoryCache::getIndividualAssociationsExtensionData`
and `indexIndividualLabelAssociations`. The helper now lazily creates the
`INDIVIDUAL_ASSOCIATION_MAP` extension on a label item using live `CacheContext`
storage. Indexing now counts required label types, stores the indexing count,
runs Konclude's per-required-label-type association-vector scan inline, records
each association in the label's individual-association map extension, updates
the indexed counter after each label-type pass, and preserves the wait call
site. Focused release-binary filters
`backend_get_individual_associations_extension_data` and
`backend_index_individual_label_associations` pass (1 test each); direct
release-binary `konclude_ht --quiet` passes (819 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W381 ports
`CBackendRepresentativeMemoryCache::getIndividualNeighbourArrayIndexExtensionData`.
The helper now resolves the ontology context, reads the label item's
`INDIVIDUAL_NEIGHBOUR_ARRAY_INDEX` extension slot, lazily allocates and installs
a `NeighbourArrayIndex` extension when absent, and calls
`initNeighbourArrayIndexData(labelItem)` at the Konclude call point. W383
supersedes the earlier initializer-internal label-value-chain boundary. Focused release-binary filter
`backend_get_individual_neighbour_array_index_extension_data` passes (2 tests);
direct release-binary `konclude_ht --quiet` passes (821 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W382 ports
`CBackendRepresentativeMemoryCache::getNeighbourArrayRoleTagResolvingLabelExtensionData`.
The helper now resolves the ontology context, lazily creates the
`TAG_RESOLVING_HASH` extension, calls
`getIndividualNeighbourArrayIndexExtensionData(labelItem, ontologyData)`, walks
the indexed neighbour role-set labels, reads each label value linker's
`CCacheValue`, applies Konclude's six-role nondeterministic identifier test, and
appends a `LabelCacheItemTagLabelResolvingDataLinker` with the label, array
index, and deterministic flag. W383 supersedes the earlier neighbour-array
index initializer boundary. Focused release-binary filter
`backend_get_neighbour_array_role_tag_resolving_extension_populates_from_index`
passes (1 test); direct release-binary `konclude_ht --quiet` passes (822 tests,
0 failed); `RUSTFLAGS=-Awarnings cargo test --release --manifest-path
engine/Cargo.toml --lib --no-run`, `cargo fmt --manifest-path
engine/Cargo.toml --check`, and `git diff --check` pass.

W383 ports
`CBackendRepresentativeMemoryLabelCacheItemIndividualRoleSetNeighbourArrayIndexExtensionData::initNeighbourArrayIndexData`.
The initializer now stores the combined neighbour role-set label, sets
`mArraySize` from the combined label's cache-value count, allocates/fills the
index array with each value linker's `CCacheValue::getIdentification()` as a
`LabelCacheItemId`, and populates the neighbour-role-set-label-to-index hash.
The W381 facade helper writes the initialized extension back to the cache arena,
and the W382 tag-resolving helper now works from a missing index extension as
Konclude does. Focused release-binary filters
`backend_neighbour_array_index_initializer_builds_array_and_hash` and
`backend_get_neighbour_array_role_tag_resolving_extension_builds_missing_index`
pass (1 test each); direct release-binary `konclude_ht --quiet` passes (824
tests, 0 failed); `RUSTFLAGS=-Awarnings cargo test --release --manifest-path
engine/Cargo.toml --lib --no-run`, `cargo fmt --manifest-path
engine/Cargo.toml --check`, and `git diff --check` pass.

W384 ports `CBackendRepresentativeMemoryCache::createCacheReader` and
`createOntologyFixedCacheReader`. The plain reader factory now allocates a real
`BackendRepresentativeMemoryCacheReader` in `CacheContext` and prepends it to
`mReaderLinker` in Konclude's head-front order. The fixed-ontology reader
factory now allocates a reader, resolves the fixed ontology-data hash, increments
the ontology data usage count when present, fixes the reader's ontology-data
pointers, and calls the single-threaded
`waitIndividualLabelAssociationIndexed()` port at the C++ call point. Missing
ontology identifiers still produce a reader fixed to null. Focused release-binary
filters `backend_create_cache_reader` and
`backend_create_ontology_fixed_cache_reader` pass (1 and 2 tests); direct
release-binary `konclude_ht --quiet` passes (827 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W385 ports
`CBackendRepresentativeMemoryCache::getMinimumSlotReferreringInstalledValidRecomputationId`.
The method now resolves the query ontology identifier from live `OntologyData`,
walks the cache's slot chain, resolves each slot's referred ontology data for
that identifier, reads its minimum-valid-recomputation id, and returns the
minimum across installed slots. Empty slot chains and null ontology ids return
`CINT64_MAX`. Focused release-binary filter
`backend_minimum_slot_referring_recomputation_id` passes (2 tests); direct
release-binary `konclude_ht --quiet` passes (829 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W386 ports both
`CBackendRepresentativeMemoryCache::updateIndexedAssociationCount` overloads.
They now resolve old/new label entries through `CacheContext`, update
individual-association counts, and maintain exact individual-association maps
when required and late indexing is disabled, including the same-representative
merge-change branch. Focused release test filter
`backend_update_indexed_association_count` passes (2 tests).

W387 ports
`CBackendRepresentativeMemoryCache::isRoleNeighbourLinkLabelItemCompatibility`.
The predicate now checks equal cache-value counts, verifies each new role tag is
present in the previous label, preserves inverse-role parity, and rejects the
Konclude deterministic-to-nondeterministic weakening case. Focused release test
filter `backend_role_neighbour_link_label_compatibility` passes (1 test).

W388 ports
`CSaturationNodeAssociatedConceptExpansion::addConceptExpansionLinker`. The
method now resolves the associated concept linker, increments the concept
expansion count, prepends the linker to the head-front chain, and indexes it by
its `CCacheValue` payload. Focused release test filter
`add_concept_expansion_linker_prepends_counts_and_indexes_by_cache_value` passes
(1 test). Direct release-binary `konclude_ht --quiet` now passes (833 tests,
0 failed); `RUSTFLAGS=-Awarnings cargo test --release --manifest-path
engine/Cargo.toml --lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml
--check`, and `git diff --check` pass.

W389 ports
`CBackendRepresentativeMemoryCache::checkRequiresDeterministicSameAsAssociationUpdateInstallation`.
The predicate now resolves both association records and returns true on the same
Konclude early-outs: deterministic-same id mismatch, representative-same id
mismatch, role-set-neighbour-array mismatch, incompletely handled association,
or any associatable label-entry mismatch. Focused release test filter
`backend_check_requires_deterministic_same_update` passes (1 test).

W390 reconciles `CCacheValueHasher::getHashValue` and
`CCacheValueHasher::operator==`. The hasher methods now document the live
arena-resolved behavior and focused tests prove hash forwarding and
value-based equality across distinct arena ids. Focused release test filter
`cache_value_hasher_` passes (2 tests). Direct release-binary
`konclude_ht --quiet` now passes (836 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W391 ports
`CBackendRepresentativeMemoryCacheIndividualRoleSetNeighbourArray::initNeighbourArray(neighArray)`.
The Rust method now copies the source index data and allocates fresh
`IndividualRoleSetNeighbourData` entries in `CacheContext` for every source
array slot instead of sharing neighbour-data ids. Focused release test filter
`neighbour_array_init_from_array_copies_data_entries` passes (1 test). Direct
release-binary `konclude_ht --quiet` now passes (837 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W392 ports
`CBackendRepresentativeMemoryCacheOntologyData::getLastActiveRecomputationReferenceLinker`
and `CBackendRepresentativeMemoryCacheOntologyData::setRecomputationReferenceLinker`.
The recomputation reference linker now carries the intrusive next pointer, the
setter prepends new linkers in Konclude `CLinker::append` head order, and the
last-active getter lazily scans the chain, falls back to the last inactive
linker, caches the result, and marks the remaining tail as all-inactive at the
same C++ call points. Focused release test filter
`ontology_data_recomputation_reference_linker` passes (2 tests). Direct
release-binary `konclude_ht --quiet` now passes (839 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W393 ports the remaining local
`CBackendRepresentativeMemoryLabelCacheItemTagLabelResolvingExtensionData` and
`CBackendRepresentativeMemoryLabelCacheItemCardinalityExtensionData` init/linker
fidelity in `backend_data.rs`. `LabelCacheItemTagLabelResolvingDataLinker` now
carries the intrusive CLinker next pointer, `appendTagLabelResolvingDataLinker`
prepends through that pointer exactly like `linker->append(exLinker)`, and the
tag-resolving/cardinality extension initializers clear their inline Rust hashes
to match Konclude's fresh hash allocation. Focused release filters
`tag_label_resolving_extension` (2 tests) and
`cardinality_extension_init_resets_inline_hash` (1 test) pass. Direct
release-binary `konclude_ht --quiet` now passes (842 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W394 ports `CBackendRepresentativeMemoryCache::addCreatedLabelStatistics`.
The method now resolves `label->getCacheValueCount()` through `CacheContext`
instead of using the old zero placeholder, while preserving the five Konclude
statistics updates exactly: global label count, global max label-value count,
per-type label count, per-type max value count, and per-type accumulated value
count. Focused release filter
`add_created_label_statistics_uses_label_cache_value_count` passes (1 test).
Direct release-binary `konclude_ht --quiet` now passes (843 tests, 0 failed);
`RUSTFLAGS=-Awarnings cargo test --release --manifest-path engine/Cargo.toml
--lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml --check`, and
`git diff --check` pass.

W395 ports
`CBackendRepresentativeMemoryCache::queueIndividualAssociationMemoryContextDeletion`.
The method now appends the individual-association memory context to the
ontology-data release queue through `CacheContext`, preserving Konclude's
head-prepend linker order, and still increments both queued-checking counters at
the C++ call point. Focused release filter
`queue_individual_association_memory_context_deletion_prepends_to_ontology_queue`
passes (1 test). Direct release-binary `konclude_ht --quiet` now passes (844
tests, 0 failed); `RUSTFLAGS=-Awarnings cargo test --release --manifest-path
engine/Cargo.toml --lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml
--check`, and `git diff --check` pass.

W396 ports the context-threaded body of
`CBackendRepresentativeMemoryCache::storeIndividualIncompletelyMarked`. The live
helper now resolves association and ontology data through `CacheContext`, flips
the incompletely-marked flag, updates the ontology incompletely-handled count,
updates the minimum incompletely handled individual id, and inserts/removes
problematic-level individuals from the ontology problematic set at the same C++
branch points. The legacy no-context wrapper remains as a compatibility shim for
older facade stubs until those call sites are reconciled. Focused release filter
`store_individual_incompletely_marked_marks_and_clears_problematic_entries`
passes (1 test). Direct release-binary `konclude_ht --quiet` now passes (845
tests, 0 failed); `RUSTFLAGS=-Awarnings cargo test --release --manifest-path
engine/Cargo.toml --lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml
--check`, and `git diff --check` pass.

W397 ports the context-threaded body of
`CBackendRepresentativeMemoryCache::setUpdatedIndividualAssociationData`. The
live helper now grows the ontology individual-id association vector, preserves
old entries, stores the localized association at the individual id, updates the
max stored individual id, increments the association count only on first store,
and increments the association-data update count for the Konclude one-level
previous-data case. The Rust port keeps Konclude's growth intent while ensuring
the vector is at least `individualID + 1` before indexing. The legacy no-context
wrapper remains for older facade stubs until those call sites are reconciled.
Focused release filter
`set_updated_individual_association_data_grows_vector_and_counts_first_store`
passes (1 test). Direct release-binary `konclude_ht --quiet` now passes (846
tests, 0 failed); `RUSTFLAGS=-Awarnings cargo test --release --manifest-path
engine/Cargo.toml --lib --no-run`, `cargo fmt --manifest-path engine/Cargo.toml
--check`, and `git diff --check` pass.

W398 ports the context-threaded body of
`CReuseCompletionGraphCache::writeExpandCacheData`. The live helper now
allocates a real `CReuseCompletionGraphCacheEntry` in `CacheContext`, stores the
job instantiation and entry id, appends the entry id to `mEntyList`, lazily
materializes `mEntyHash` in the typed cache arena, prepends the entry into each
entailed `CCacheValue` hash bucket, and records the entailed/minimal value sets
on the entry. The older no-context wrapper remains for event-drain call sites
that still do not thread `CacheContext`. Focused release filter
`write_expand_cache_data_materializes_entry_and_hash` passes (1 test).

### Remaining deferral markers (code grep counts, the honest scope of "not yet live")
| marker | count | meaning |
|---|---|---|
| `W6-DEFER` | 753 | cache backend IO and remaining dependency-base materialization |
| `W3-DEFER` | 728 | completion in-method deferrals (mix: cache/datatype/Task-blocked tails) |
| `PORT-PENDING` | 221 | whole-method stubs awaiting siblings/subsystems |
| `W2-DEFER` | 107 | process-layer api gaps (hash population paths and remaining satellite APIs) |
| `W4-DEFER` | 136 | saturation bodies |
| `todo!` | 27 | unfilled method bodies (off the tested path) |
| `RECONCILE-NEED` | 31 | flagged sibling-method gaps (mostly stale — already ported under Rust names) |
| `W8-DEFER` | 4 | RBox/classification bridge remnants |
| `W14-DEFER` | 0 | qualified-number follow-up remnant |

## Build & test (ws only — NEVER on the laptop)

```bash
rsync -a engine/src/ ws:km-frontend/kobayashi-marust/engine/src/
ssh ws 'cd ~/km-frontend/kobayashi-marust/engine && cargo test --release konclude_ht 2>&1 | grep "test result"'
# or: cargo check --release 2>&1 | tail
```

## Next steps (priority order)

1. **Continue after W219 classification message linker/observer wave.** W93-W219 completed the
   non-datatype Unit 30 clash subtypes, tracked-clash creation dispatch, and the
   `CTrackedClashedDependencyLine` / `CTrackedClashedDescriptorHasher` bucketing
   substrate, `getFreeTrackedClashedDescriptor`, `initializeTrackingLine`, and
   `getSortedClashedDescriptors`, plus the two Unit 22
   `writeClashDescriptorsToCache` overload wrappers that drain/restore tracking
   lines and prepend/remove additional descriptors, and the core overload's
   descriptor validation/sort/cache-write gate up to the still-null unsat-cache
   handler, plus `markRelevanceForTrackedClashedDescriptors` and the Unit 29
   `backtrackFromTrackingLine` / `backtrackFromTrackingLineStep` dispatcher over
   the live tracking-line buckets, plus Unit 29's ordinary deterministic
   descriptor re-derivation over previous dependency track points and additional
   dependency links, and Unit 30's branch-filtered collected-clash path
   `getCollectedFilteredClashedDescriptorsFromBranch`, plus Unit 29's
   `getBacktrackedDeterministicClashedDescriptorsBeforeProcessingTag` iterator
   split/dedup/free-list loop, and the substrate-backed core of Unit 29's
   `backtrackNonDeterministicBranchingClashedDescriptor`: collect before-tag
   clashes, write/cache with the clashing descriptor as additional, install
   copied branch clashes/involved ids, detect when all branch track points are
   closed, collect filtered branch clashes, and reinitialize the tracking line,
   plus top-level `clashedBacktracking` over tracked-clash creation, extended
   dependence tracking, tracking-line initialization, root cancellation/current
   cache call points, and `backtrackFromTrackingLine`, plus the Unit 29
   `createNonDeterministicDependencyTrackPointBranch` branch-node/track-point
   allocation and binding path, plus `createDependendBranchingTaskList` over the
   typed task arena: branch-dependent task allocation, parent/root/depth/reference
   linking, shared task state/adapters, debug task ids below depth 90, and
   front-spliced returned task lists, plus the first consumers: OR multi-branch
   allocation, `createMergeBranchingTask`, `createDistinctBranchingTask`, and the
   two-task qualify-choose loop now call/traverse the live dependent task list
   instead of returning `Id::NONE`, and the task-priority strategies now resolve
   real parent task depth/priority from the task arena for branching, qualifying,
   merging, and reusing priorities, plus the direct
   `initTaskProcessContext`/`initCalculationAlgorithmContext` copy semantics for
   task/process aliases and strategy/factory/cache handles, the task-priority
   strategy is now a concrete value-owned strategy at the algorithm/context seam,
   the concept-priority strategy is now value-owned and read through the
   initialized context instead of reconstructed locally in `priorityForConcept`,
   and the individual-priority strategy is now value-owned at the
   algorithm/context seam with the exact `CIndividualProcessNodePriority`
   null/get/set/comparison helpers and queue-priority-aware
   `getPriorityForIndividual`, and the unsat-cache retrieval strategy is now
   value-owned at the algorithm/context seam with Konclude's generative
   non-deterministic truth table. `addIndividualNodeForCacheUnsatisfiableRetrieval`
   now enqueues nodes into the live databox cache-test queue, and
   `takeNextProcessIndividual` drains that queue first as `INQT_CACHETEST`, and
   `CIndividualNodeUnsatisfiableOccurenceCacheRetrievalData` is now a real
   process-context arena object rather than a marker stub. Node fields and PN4
   accessors still use the original `UnsatCacheRetId` alias, but it now points to
   the real occurrence retrieval data class with Konclude's last-caching-tag and
   last-concept-descriptor init/copy/get/set behaviour. `CCachingTags` and
   `CUnsatisfiableCachingTags` are now ported as ontology-layer records with
   Konclude's min/max/last tag and min-unsat-size candidate methods; the
   existing `CConceptProcessData::mUnsatCachingTags[2]` slots remain raw-compatible
   but have typed polarity-specific accessors. `COccurrenceUnsatisfiableCache`
   now writes cache tags through the ontology arenas at the original
   `writeCacheTags` call point, allocating missing `CUnsatisfiableCachingTags`
   and updating them for `CACHEVALTAGANDCONCEPT` /
   `CACHEVALTAGANDNEGATEDCONCEPT`. `CUnsatisfiableCacheHandler` is now a real
   Algorithm-layer struct instead of a marker, with reader/writer/config state,
   the initial `isIndividualNodeUnsatisfiableCached` memoization guard, the
   concept-data direct precheck-fail branch over typed unsat caching tags, and
   the final retrieval-data update for checked-negative results. The exact-tag
   precheck success branch is now live too: it performs the second
   `hasCandidateTags` scan, refines `unsatLineCount` through
   `candidateMinUnsatisfiableSize`, iterates the dependency-aware label set,
   creates clashed concept descriptors, and appends the generated clash chain to
   the incoming clash chain with Konclude's `clashedDepDesLinker->append`
   semantics. The occurrence-reader hash fallback in
   `isIndividualNodeUnsatisfiableCached` is now live: it builds the sorted
   cache-test value vector from label-set descriptors that have unsat caching
   tags, calls `COccurrenceUnsatisfiableCacheReader::getUnsatisfiableItems`,
   creates concept clash descriptors for returned cache values, and updates the
   retrieval memo on checked-negative null results. Unit 21's
   `testIndividualNodeUnsatisfiableCached` now consumes the live handler through a
   context-owned handler/cache bundle, preserves the node-signature gate, and
   raises the port's clash signal for cached-unsat hits instead of hardcoding
   `unsat_cached = false`. Unit 30's
   `addIndiNodeSignatureOfUnsatisfiableClashedDescriptors` is now live too: it
   reads the tracked descriptor's appropriated individual id, follows the corrected
   nominal-node resolver, reads the node label-set concept signature, and inserts
   it into `mUnsatCachingSignatureSet`. The writer side is now live for sorted
   tracked-clash chains: `CUnsatisfiableCacheHandler::writeUnsatisfiableClashedDescriptors`
   converts tracked concept descriptors into occurrence-cache `CCacheValue`s and
   drains them through `COccurrenceUnsatisfiableCache::processCustomsEvents`, and
   Unit 30's forwarding method now uses the context-owned handler/cache bundle.
  `CUnsatisfiableCacheHandler::writeUnsatisfiableClashedConcept` is live as the
  single-concept writer used by the root unsat cache branch: it writes the
  positive concept cache value through the same occurrence-cache event path and
  round-trips through the reader. `CSatisfiableTaskClassificationMessageAdapter`
  now carries the tested concept plus extraction flags, and
  `rootUnsatisfiabilityWriteCaches` uses that adapter's
  `EFEXTRACTSUBSUMERSROOTNODE` gate to call the live clashed-concept writer
  through the context-owned handler/cache bundle. The saturation-node expansion
  cache branch is now live up to Konclude's handler write-data queue:
  `CSaturationNodeExpansionCacheHandler::cacheUnsatisfiableConcept` resolves the
  positive saturation node, skips already-clashed nodes, and queues
  `CSaturationNodeAssociatedExpansionCacheUnsatisfiabilityWriteData` through the
  context-owned handler state. The root computed-consequences nominal tail is
  wired too: for a single constructed nominal root with exactly one initializing
  concept and a terminology-backed init concept, it calls
  `CComputedConsequencesCacheHandler::tryCacheTypeConcept(individual,
  initConcept, !conNegation, ctx)` through a context-owned handler. The handler
  now builds/commits `CComputedConsequencesCacheWriteTypesData`; its exact
  `canCacheTypeConcept` proof is still gated by the deferred ontology
  consistence-task bridge and defaults to false unless seeded by that proof seam.
  `CSaturationNodeCacheUpdater::propagateUnsatisfibility` is now live for the
  local status-flag propagation slice: it sets the clashed flag, updates direct
  and indirect saturation-node flags, walks copy-dependent saturation nodes, and
  walks non-inverse connected nodes for indirect propagation. The role-backward
  propagation hash traversal remains a later sat-node cache slice. The queued
  saturation-node unsat write-data drain is now live too: the handler carries
  its cache context, task-level `commitCacheMessages` calls the handler, and the
  typed cache-context facade dispatches queued unsat records to the updater.
  The role-backward propagation hash substrate is live for the cache-updater
  slice: `CRoleBackwardSaturationPropagationHash(Data)` and
  `CBackwardSaturationPropagationReapplyDescriptor` are real saturation
  satellites, `ProcessContext` owns their arenas and helpers, and
  `CSaturationNodeCacheUpdater::updateIndirectAddingIndividualStatusFlags` now
  walks `mLinkLinker` source individuals exactly at Konclude's cache-updater
  branch.
  The typed expansion-write side of the same saturation-node associated-expansion
  cache is live in `CacheContext`: deterministic expansion writes create/cache
  entries and associated concept expansions, second deterministic writes use the
  Konclude extend-only-new-values behaviour, nondeterministic writes consume the
  remaining-expansion budget and prepend nondeterministic expansion records, and
  concept linkers/dependent nominal metadata are copied through cache arenas.
   Merge/distinct branch-task creators and the two-task qualify loop now write
   Konclude's task priority onto the child `CTask` when a used task strategy is
   installed; OR branch priority remains blocked on typed branched operands and
   branch instruction/databox materialization. The remaining
   `createCalculationAlgorithmContext` gap is now precise: a fresh by-value Rust
   context cannot dereference a `satCalcTask` allocated in the caller's task
   arena, so per-child process-context/databox realization and scheduler
   communication need a faithful task-arena ownership bridge before branch-local
   concepts/restrictions/databox branching instructions can be populated.
   The root-unsat cache-writing method is now structurally covered. The next
   cache slices should replace the two remaining queue/proof seams: computed
   consequences needs the ontology consistence-task data bridge for exact
   `canCacheTypeConcept`, and sat-node unsat cache writes need the cache
   facade/updater path that installs queued unsat write data as clashed status
   flags. W130 ports the updater's local clashed-flag propagation over direct,
   copy-dependent, and non-inverse-connected saturation-node links; W131 drains
   queued saturation-node unsat write data through the task-level commit path and
   cache-context facade into that updater. W132 ports the role-backward
   propagation hash/data substrate and the cache-updater traversal over
   `CBackwardSaturationPropagationLink::getSourceIndividual`. W133 ports the
   typed deterministic/nondeterministic expansion-write drain through
   `CacheContext`, including cache-entry creation, fill, and deterministic
   extension. W134 reconciles the typed UNSAT+EXPAND write-data family with a
   single-thread Rust equivalent of Konclude's writer/facade/event/install
   dispatch: typed records preserve the C++ `getWriteDataType` split, route UNSAT
   records to the W131 updater path, and route EXPAND records to the W133
   expansion installer. W135 moves `CSaturationNodeExpansionCacheHandler` to the
   upstream single `mWriteData` chain shape: generic typed `addCacheMessages`
   prepends UNSAT or EXPAND records, commit reverses back into producer order,
   and the writer drains through W134's unified dispatcher. W136 ports
   `CIndividualNodeSaturationBlockingData` and the live part of
   `testNodeCachingPossible`: label set + saturation-blocking-data presence,
   completed saturation-node guard, cache-entry lookup through the typed context,
   deterministic-expansion rejection, and the signature/remaining-budget cases
   that require deterministic-only caching. The next saturation-node expansion
   cache slice is now inside the remaining `tryNodeSatisfiableCaching` producer
   body. W137 adds the minimal `CSaturationConceptDataItem` /
   `CExtendedConceptReferenceLinkingData` process arena, resolves the saturation
   concept descriptor from the node label set, ports the upstream deterministic
   dependency test over branching tags / appropriate individual levels, splits
   the descriptor chain at `lastPossiblyNonDeterministicConDes`, detects tight
   at-most restrictions from live role-successor counts, filters deterministic
   cache values already in the previous deterministic expansion, and queues
   nondeterministic-prefix plus deterministic-suffix expansion write data in
   Konclude order. W138 replaces the staged `cint64` cache-value encoding with
   real `CCacheValue` payloads on `CSaturationNodeAssociatedConceptLinker`,
   `AssociatedConceptExpansion`'s cache-value hash, and the W137 producer/writer
   path. W139 adds the real `CSuccessorConnectedNominalSet` process satellite,
   re-aliases `NominalConnectionSetId`, threads a `ProcessContext` arena plus
   context-owned lazy getter/add/has/snapshot helpers, ports the
   `testNodeCachingPossible` compatible-nominal loop, and copies successor
   nominal ids as negative ids into deterministic/nondeterministic expansion
   write data. W140 adds the saturation-node nominal-handling wrapper,
   context-threaded saturation-node successor-connected nominal accessors, and
   ports saturation `requiresAddingSuccessorConnectedNominals` plus both
   `updateAddingSuccessorConnectedNominal` overloads over copy-dependent,
   role-backward-source, and non-inverse-connected fan-out. Remaining exact-port
   work nearby. W141 routes completion `u16`'s dependent-nominal debug string
   and exact successor-nominal ancestor propagation through the real
   context-owned `CSuccessorConnectedNominalSet`, replacing the old node-local
   stub calls. W142 adds the real `CNominalCachingLossReactivationData`
   payload, context-owned lazy getter, `u16` queue reactivation drain, and
   `u21` saturation-caching reactivation install/try-install loops over
   dependent and successor-connected nominal sets. Remaining exact-port work
   nearby. W143 ports `CSaturationNodeExpansionCacheHandler::isNodeSatisfiableCached`
   and its `testNodeMatchingExpansion` helper over real installed expansion
   entries, then wires `detectIndividualNodeSaturationCached`'s cache-retest
   branch to consume the returned expansion, reject dependent nominals when
   `mConfSaturationCachingWithNominals` is false, install nominal
   caching-loss reactivation, and update the tight-at-most successor-creation
   flag exactly as Konclude does. W144 ports `CBlockingFollowSet` /
   `CBlockingFollowUpdateTag` as a process arena object, adds context-threaded
   lazy allocation/copy/add/remove/snapshot helpers for the node's
   `mSigBlockFollowSet` triple, wires the Unit 16 blocking-follower iterator
   arms in `propagateIndividualNodeNominalConnectionFlagsToAncestors` and
   `propagateIndividualNodeConnectedNominalToAncestors`, and hooks the live set
   into u18 signature-blocking following plus blocker-reactivation review. W145
   adds the context-threaded `CIndividualNodeIncrementalExpansionData` lazy
   getter and ports Unit 26's directly-changed-neighbour establishment,
   breadth-first propagation, and search helpers across successor,
   connection-successor, blocked, processing-blocked, blocking-follow, blocker,
   and following branches. W146 ports Unit 26's directly-changed clearing
   helpers, including propagated-list BFS cleanup with Konclude's unconditional
   `false` return for `clearPropagatedDirectlyChangedNeighbourConnection`, and
   wires `addIndividualToIncrementalCompatibilityCheckingQueue` to the live
   depth queue insertion path. W147 ports
   `generateDebugIncrementalExpansionString` over the live incremental-expansion
   satellite. W148 ports the Unit 26/34 variable-binding compatibility
   collection slice: `getConceptsForCompatibleVariablePropagationBindings`,
   `collectIndividualNodeVariablePropagationBindings`, and the typed
   `VarBindingPathId` handoff between them. W149 ports
   `hasCompatibleConceptSetSignature`, including shifted sorted-linker matching,
   signature-critical rejection, invalid-signature marking, and Konclude's
   fallback containment check. W150 ports `isLabelConceptSubSet` over the live
   sorted iterator and routes `hasCompatibleConceptSetReuse` through that helper
   and the existing signature-critical predicate. W151 ports
   `CConceptSetSignature`'s value fields, reset/add/equivalence behavior, and
   wires the live resolved label-set insertion path to update signatures. W152
   ports shared additional-map alias reads/snapshots plus Unit 34
   `isLabelConceptEqualSet` and `isPairwiseLabelConceptEqualSet` through full
   signature equivalence and sorted lockstep descriptor comparison. W153 ports
   Unit 16's nominal-clash-only equality helper over the same live sorted
   iterator, including Konclude's nominal-skip and clash-flag behavior. W154
   ports the Unit 26 compatibility-update dispatcher and the previous/current
   label-set recheck over already-loaded previous correspondence nodes, preserving
   Konclude's last-checked descriptor checkpoint and directly-changed propagation
   outcomes. W155 adds the previous deterministic task bridge for lazy
   previous-correspondence lookup through the incremental adapter, task-data
   record, deterministic satisfiable task, and task-owned processing databox.
   W156 ports the `initializeIncrementalIndividualExpansion` previous-graph
   BFS/list half and `getNextIncrementalExpansionIndividual`: Unit 26 now walks
   previous successor, connection-successor, and merged-individual links, appends
   missing nominal individuals to the real incremental expansion list, marks the
   list initialized, queues the node, and drains the list while skipping nominals
   already present in the current graph. W157 ports
   `areAllDependentFactsUnchanged` over the live dependency spine and wires the
   missing-previous-concept replay block in
   `initializeIncrementalIndividualExpansion` through the exact
   `remMaxBacktrackingCount = 15` helper call and `addConceptToIndividual`.
   W158 ports `incrementalNodeExpansion`'s
   `getUpToDateIndividual(-expIndi->getIndividualID())` return path through the
   algorithm-owned by-id nominal materialization path and wires the uninitialized
   incremental-expansion queue branch to the live depth queue. W159 ports
   `CIndividualCustomPriorityProcessingQueue`, wires the initialized-list
   `addIndividualToIncrementalExpansionQueue` branch to
   `insertIndiviudal(nextExpPriority, individual)`, and ports the now-unblocked
   `takeNextProcessIndividual` incremental compatibility, initializing, and
   expansion queue probes. W160 ports
   `CIndividualDepthConceptProcessDescriptorProcessingQueue`,
   `CIndividualConceptBatchProcessingData`, and
   `CIndividualConceptBatchProcessingQueue`, allocates the variable-binding
   concept-batch queue from the databox, and wires `takeNextProcessIndividual`
   Probe 11 so it transfers the returned `CConceptProcessDescriptor` into the
   localized node's concept-processing queue as `INQT_VARBINDBATCHQUE`. W161
   ports the Unit 02 nominal non-deterministic sort-prep arm: the driver now
   takes the databox nominal non-deterministic list, sorts by Konclude's
   `individualIDGreaterThan` comparator, rebuilds it through the existing
   prepend helper, marks the list sorted, and lets the later nominal probe drain
   the lowest individual node id first. W162 ports
   `CIndividualReactivationProcessingQueue`, wires the databox early/late
   reactivation queue getters to real process-context queues, updates the
   saturation-caching reactivation call site to use the context forwarders, and
   ports the Unit 02 early reactivation probe: the driver drains/localizes the
   queued node, performs the forced completion-cache invalidation branch with the
   existing absorbed-concept reapply helpers, and marks `INQT_COMPCACHEDREACT`.
   W163 reuses that exact reactivation body for the Unit 02 late reactivation
   probe, which now drains the live late `CIndividualReactivationProcessingQueue`
   and records `INQT_COMPCACHEDREACT` at the upstream cpp 2621-2640 point. W164
   ports `CIndividualProcessNodeDescriptor` and `CIndividualProcessingQueue`,
   wires `getIndividualProcessingQueue` to the real process-context queue arena,
   and enables Unit 02 Probe 20 so it resets
   `mMinConceptProcessingPriorityLevel`, drains the descriptor queue, returns the
   descriptor's individual, and records `INQT_OUTDATED`. W165 ports
   `CSignatureBlockingReviewData`, `CSignatureBlockingReviewDataIterator`, and
   `CSignatureBlockingReviewSet`, wires Unit 18 review marking to insert/remove
   review ids, and enables Unit 02 Probe 31 to drain review data, localize the
   blocked node, require identic concept-set review, and dispatch signature
   blocking status detection. W166 ports `CReusingReviewData`, wires
   `CProcessingDataBox::getReusingReviewData` through the real process-context
   arena, and preserves Konclude's upstream `hasNextIndividualID() ==
   mIndividualSet.isEmpty()` behavior exactly. W167 reconciles
   `CReusingIndividualNodeConceptExpansionData` to a real arena-backed derived
   satellite and wires Unit 02 Probe 32 through the upstream reusing-review loop
   while preserving that exact gate. W168 ports
   `CBackendNeighbourExpansionControllingData`, including reuse-mode flags,
   expanded-link count, dependency handles, the three individual-node linker
   heads, and `getBackendNeighbourExpansionControllingData` arena allocation/copy.
   W169 wires Unit 02's fixed-mode and prioritized-mode backend reuse queue
   probes through that controlling data and the real backend reuse queue,
   returning `INQT_BACKENDEXPANSIONREUSE` for both modes. W170 wires
   `addIndividualToBackendReuseExpansionQueue` to set the queued flag and insert
   into that real backend reuse queue. W171 wires
   `addIndividualToBackendIndirectCompatibilityExpansionQueue` to set its queued
   flag and insert into the real backend indirect-compatibility queue. W172
   wires `addIndividualToBackendSynchronisationRetestQueue` and
   `addIndividualToBackendDirectInfluenceExpansionQueue` to their real backend
   unsorted queues. W173 wires `addIndividualToBackendNeighbourExpansionQueue`
   to the real backend-neighbour rotation queue. W174 wires
   `addIndividualToBlockingUpdateReviewProcessingQueue` to the real
   blocking-update review depth queue. W175 wires `getAppliedANDRuleCount`.
   W176 wires the fixed backend reuse-expansion preparation path up to the
   still-deferred backend-sync reuse track-point setter. W177 wires the
   DATAASSERTION dependency wrapper and process-context factory shape. W178
   wires the remaining applied rule-count getter tail. W179 wires the AND
   dependency wrapper/factory shape. W180 wires the ATMOST dependency
   wrapper/factory shape. W181 wires the saturation extended-debug writer's
   QFile-equivalent file sink. W182 wires the AUTOMATCHOOSE, SOME, and SELF
   dependency wrappers/factory shapes. W183 wires VALUE, NEGVALUE, and ALL
   dependency wrappers/factory DetLink shapes. W184 wires the QUALIFY dependency
   wrapper/factory non-deterministic shape. W185 wires DISTINCT,
   AUTOMATTRANSACTION, and ATLEAST dependency wrappers/factory shapes. W186
   wires the OR dependency wrapper/factory shape and fixes the OR disjunct
   branch-stat null sentinel. W187 wires the REUSEINDIVIDUAL,
   REUSECOMPLETIONGRAPH, and REUSECONCEPTS dependency wrappers/factory shapes.
   W188 wires ORONLYOPTION, IMPLICATION, EXPANDED,
   REUSEBACKENDEXPANSIONMODES, REUSEBACKENDFIXEDINDIVIDUALEXPANSION, and
   REUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSION dependency wrappers/factory
   shapes. W189 wires ROLEASSERTION and FUNCTIONAL dependency wrappers/factory
   shapes. W190 stores ROLEASSERTION's base assertion role/individual payloads
   and wires the REUSEBACKENDVALUE dependency wrapper/factory shape. W191 wires
   eleven Unit 28 VARBIND/PROPAGATE connection, binding, successor, join, and
   grounding dependency wrappers/factory shapes. W192 wires eight Unit 28
   BINDPROPAGATE, PROPAGATEBINDING, BINDVARIABLE, and NOMINAL dependency
   wrappers/factory shapes. W193 wires Unit 26 incremental pruning, Unit 28
   same-individual dependency collection, and the Unit 29 recursive tracked-clash
   chain append preservation. W194 wires the process-layer
   `CReferredIndividualTrackingData`/`CReferredIndividualTrackingVector` payload
   and `ProcessContext` arena that Unit 28 individual-dependence tracking needs.
   W195 wires the task-level individual-dependence adapter holder and the
   already-installed-vector branch of `trackIndividualDependence`. W196 ports
   the concrete `CIndividualDependenceTrackingCollector` observer and types that
   observer through the task adapter/context arena. W197 wires Unit 28's lazy
   individual-dependence tracking-vector installation through the typed observer,
   the ABox individual-count bridge, the current ontology consistence-model-data
   bridge, and `CConsistenceTaskData::getDeterministicSatisfiableTask()` sizing.
   W198 ports the classifier testing-item marker facet
   (`mIndiDepTracked`, `setIndividualDependenceTracked`,
   `hasIndividualDependenceTracked`), types the adapter marker id, and wires the
   Unit 28 marker call point. W199 ports the job-level
   `CSatisfiableCalculationJob::mSatIndDepTrackAdapter` holder plus the generator
   copy to `CSatisfiableCalculationTask` and databox
   `setIndividualDependenceTrackingRequired(true)` activation. W200 ports the
   subclass classifier caller branch that allocates the typed
   `CSatisfiableTaskIndividualDependenceTrackingAdapter` on the job from an
   ontology-item collector and next satisfiable-test item marker. W201 ports the
   matching KPSet class classifier caller branches for `nextSatTestItem` and
   `subsumedItem`. W202 ports the KPSet role classifier observer-only caller
   branches that allocate the adapter from the ontology-item collector with no
   marker. W203 ports the live realizer observer-only caller branches that lazily
   allocate per-individual collectors when realization tracking is required and
   attach typed adapters to the satisfiable calculation job. W204 ports the
   realizer testing-item base plus the concept-instance, role-pair, and
   same-individual testing item constructor/getter/type-tag surfaces allocated
   around those W203 call sites. W205 ports the KPSet class/role
   possible-subsumption data, maps, and iterators used by the classifier
   ontology/testing item queues. W206 ports the KPSet class/role ontology item
   passive state-holder APIs: testing-item hash/container/top/bottom/list/set
   surfaces, get-or-create testing items, counters, and phase flags. W207 ports
   the KPSet class/role testing-item passive state-holder APIs around
   predecessor counters, subsumer/successor lists, satisfiable flags, lazy
   possible-subsumption maps, propagation sets, possible-subsumed containers,
   class fast-sat fields, and role temporary concept fields. W208 ports the
   role ontology item's temporary role-classification ontology handle, marker
   concept-to-role-item hash, temporary all-propagation concept, and temporary
   propagation/marker individual storage accessors. W209 ports the KPSet
   class/role testing-item subsumer-list sorting behavior over the W207 item
   count surfaces. W210 ports the KPSet class/role `tellConceptSupsumption`
   observer behavior through concept process-data and satisfiable-reference
   linking, including class invalidated-reference fallback through the ontology
   concept-reference-linking hash. W211 ports the passive
   `CClassificationClassPseudoModel` payload stack: deterministic flags,
   concept/role map data, role cardinality/successor-model bounds,
   per-node pseudomodel data/hash copy/init semantics, and the embedded KPSet
   class testing-item pseudomodel accessor. W212 ports the recursive
   `fastPseudoModelSubsumptionClassPrecheckTest` /
   `isPseudoModelSubsumerPossible` consumer over those payloads, including
   deterministic missing-concept pruning, role bound rejection, and successor
   model recursion. W213 ports the `CClassificationMessageData` /
   `CClassificationPseudoModelIdentifierMessageData` carrier and the KPSet class
   thread `TELLCLASSPSEUDOMODELIDENTIFIERS` receive branch: processed-message
   statistic, concept-to-testing-item lookup, `setPseudoModelHash`, initialized
   flag, and ontology-item memory-pool retention. W214 ports the complete
   `CSatisfiableTaskClassificationMessageAdapter` extraction flag surface,
   corrects `hasExtractionFlags` to Konclude's any-bit test, adds the opaque
   ontology/message-observer/concept-reference-linking payload, and adds the
   bounded analyser-side root pseudomodel producer helper that creates model id
   `0`, valid concept/role maps, and the outgoing pseudomodel identifier message
   from already-extracted root entries. W215 ports the analyser's root
   pseudomodel concept-map extraction loop over the real label-set iterator:
   non-negated named `CCATOM`, `CCSUB`, `CCIMPLTRIG`, and `CCEQCAND` insertion,
   dependency-branch-tag deterministic flagging, and non-deterministic
   connection demotion. W216 ports the analyser pseudomodel validity gate:
   blocked/cached nodes invalidate concept and role maps, valid completion-cache
   invalidation flags exempt cached nodes, nominal nodes invalidate only
   successors, and the depth/node-count caps invalidate successor maps. W217
   ports the analyser role-successor map traversal over the live
   `CReapplyRoleSuccessorHash` substrate: simple-role filtering, processed-role
   deduplication, per-node link-count bounds, branch-tag deterministic
   detection, concept-derived at-least/at-most bounds, fresh successor
   pseudomodel ids, and queued successor analyse items. W218 integrates the
   W215-W217 slices into the analyser-side pseudomodel producer queue: seed
   base model `0`, pop queued `CPseudoModelAnalyseProcessItem`s, set validity
   flags, populate concept/role maps for every model id, append successor
   analyse items, apply the nondeterministically-merged base-node gate, and
   wrap the completed hash in `CClassificationPseudoModelIdentifierMessageData`.
   W219 ports the typed `CClassificationMessageData` linker surface around that
   payload: payload enum, head-to-tail append semantics, final analyser merge
   order (`possible-subsumption -> pseudomodel -> subsumption`), a classifier-side
   `CClassificationMessageDataObserver` trait, pseudomodel message linker
   wrapping, and KPSet class receiver traversal that skips unsupported header-only
   messages while dispatching typed pseudomodel messages.
   W220 ports the typed class-side payloads for
   `CClassificationClassSubsumptionMessageData`,
   `CClassificationInitializePossibleClassSubsumptionData`,
   `CClassificationInitializePossibleClassSubsumptionMessageData`, and
   `CClassificationUpdatePossibleClassSubsumptionMessageData`, and wires the
   KPSet class receiver's shallow branches for class subsumption, possible
   subsumption initialization, and possible-subsumption update traversal.
   W221 ports the exact KPSet class pruning and downward-propagation helpers:
   `propagateDownSubsumption`, `prunePossibleSubsumptions`,
   `pruneDownSubsumption`, and `pruneUpNotSubsumption`, including recursive
   propagation-set traversal, equivalent-candidate `CCEQ` pruning, and
   Konclude's remaining/true/false possible-subsumption counter updates.
   W222 deepens the `TELLCLASSINITIALIZEPOSSIBLESUBSUM` receiver branch:
   empty initialization invalidates unknown possible-subsumption entries,
   initialization skips equivalent-candidate `CCEQ` entries, ontology-level
   equivalent non-candidates are inserted when the message has no explicit list,
   existing maps invalidate stale non-`CCEQ` candidates, and inserted candidates
   now update both remaining and total possible-subsumption counters.
   W223 completes the next receiver-side initialization slice: after a fresh
   possible-subsumption map is populated, ancestor maps are pruned by the
   Konclude sorted concept-tag comparison against the new map, descendant
   relationships invalidate newly initialized candidates missing from descendant
   maps, and already-initialized descendants without maps invalidate all
   compatible newly initialized candidates through the W221 pruning path.
   W224 starts the analyser-side producer port for these typed class messages:
   root deterministic class-subsumption message construction, null-list root
   class messages, possible-subsumption initialization payload construction, and
   initialized-map update-message emission for missing non-`CCEQ` candidates are
   now represented as bounded helpers over sorted label snapshots.
   W225 ports the duplicate possible-subsumption initialization-list pruning
   branch used by the analyser's `mMultiplePossSubsumInitAvoidHash`: existing
   init-list entries are compared to the current label set by sorted concept
   tag, missing entries are marked invalid, and no replacement message is
   allocated in that reuse branch.
   W226 ports the bounded other-node class-subsumption producer helper: for an
   already selected single-dependency analyse concept, it collects same-branch
   deterministic non-negated named subsumers, suppresses the message on lower
   branch-tag errors, and emits no message when no subsumer list is collected.
   W227 ports the bounded other-node analysed-concept scheduling guards from the
   analyser BFS: the outer other-node extraction flag check, nominal/invalidated
   blocker-node skip, descriptor filters for non-self named non-negated concepts
   with tag not `1`, the classifier-reference "more information required" gate,
   dependency branch-tag extraction, and the duplicate `analysedConceptSet`
   insertion guard.
   W228 ports the bounded classifier message observer delivery bridge: the
   analyser-side final delivery can now consume a typed message linker, read the
   testing ontology and opaque message-observer handle from
   `CSatisfiableTaskClassificationMessageAdapter`, call the typed
   `CClassificationMessageDataObserver` surface with the memory-pool handle, and
   skip null observer/empty linker cases.
   W229 ports the bounded analyser-side classifier-reference routing used by the
   other-node scheduling gate: concept process data first resolves a live
   `CConceptSatisfiableReferenceLinkingData` classifier pointer when not
   invalidated, invalidated/missing live references fall back through the task
   adapter's concept-reference-linking hash, and the resolved KPSet class testing
   item is queried for `isMoreConceptClassificationInformationRequired()`.
   W230 ports the bounded other-node traversal skeleton over explicit snapshots:
   the analyser now has a FIFO successor queue with processed-node suppression,
   nominal/invalidated-blocker node skip, successor expansion only from allowed
   nodes, extraction-flag driven multiple/single descriptor selection, and
   single-dependency descriptor marking for W226 class-subsumption production.
   W231 ports the bounded other-node visit-to-message production body: scheduled
   traversal visits now prepend class-subsumption messages through W226,
   prepend possible-subsumption messages through W224's producer with the
   other-node extraction flag, suppress duplicate analysed concepts through the
   W227 analysed set, and keep the class/possible linkers separate for the
   existing final merge-order helper.
   W232 ports live other-node snapshot extraction from `ProcessContext`: the
   analyser can now build W230 snapshots from node IDs, reapply concept-label
   sets, dependency branch tags, node nominal/blocker/successor-nominal flags,
   and successor iterators over the real successor-role hash.
   W233 ports Konclude's exact single-ancestor dependency descriptor resolver:
   `hasDependencyToAncestor(...)` now handles root independent-base
   dependencies, appropriate-individual ancestor-depth checks, and
   `DNTMERGEDCONCEPT` recursion through the previous track point, while
   `getIndividualProcessNodeConceptWithSingleAncestorDependency(...)` rejects
   successor-nominal nodes, null non-tag-1 descriptor dependencies, and multiple
   ancestor-dependent descriptors. The live snapshot wrapper now resolves the
   single-dependency label index from the process graph instead of taking it as
   an external seam.
   W234 ports the final analyser message-output tail: the three linker families
   are merged in Konclude order (`subsum`, then `pm` prepended, then
   `possible-subsumption` prepended), delivered through the classifier observer
   bridge when non-empty, and the no-message branch records the temporary memory
   pool release path until the task memory manager is live.
   W235 ports `getCorrectedIndividualID(...)` for the classification-message
   analyser: it resolves the constructed/base individual through the
   `IndividualProcessNodeVector`, follows merged-into ids to the representative,
   and marks the merge chain non-deterministic when a traversed merge has no
   dependency track point or a positive merge-branch tag.
   W236 wires that corrected base into the bounded root analyser branch:
   `create_root_classification_message_linkers_from_constructed_node` now clamps
   `maxDetBranchTag` to zero after non-deterministic merges, extracts live root
   labels from the representative node, emits Konclude's always-present root
   class-subsumption message whenever `considerRootNode` is true, and prepends
   root possible-subsumption messages for each eligible non-negated named root
   descriptor.
   W237 composes the live analyser slices into a bounded integration helper:
   root class/possible linkers from W236, bounded other-node snapshots/visits
   from W230-W233/W231, pseudomodel production from W218, final linker merge and
   observer delivery/release from W234, all driven from a constructed node plus
   explicit still-external classifier state.
   W238 removes the explicit "concepts requiring more information" input for the
   bounded other-node path: analyser visits now derive that set through the live
   classifier reference lookup (`CConceptProcessData` reference when valid,
   adapter hash fallback otherwise) and
   `COptimizedKPSetClassTestingItem::isMoreConceptClassificationInformationRequired`.
   It also closes the single-dependency-only traversal gap so Konclude's selected
   `analyseConDesSingleDep` descriptor is analysed even when multiple-dependency
   extraction is off.
   W239 removes another explicit analyser input: root/other possible-subsumption
   state is now snapshotted from the resolved KP-set classifier item, using
   `isPossibleSubsumptionMapInitialized()`, `getClassPossibleSubsumptionMap()`,
   `hasRemainingPossibleSubsumptions()`, and the map's ordered concept keys. The
   equivalent-non-candidate list remains explicit because the exact upstream
   source is the ontology TBox set filtered through
   `testSubsumerCandidatePossibleWithMergedSaturatedModel(...)`.
   W240 ports the terminology-side `CTBox::mEquivConNonCandidateSet` container
   into `OntologyArenas`, including `getEquivalentConceptNonCandidateSet(false)`
   no-create behavior and the lazy create/insert path. The analyser still does
   not consume it until the saturated-model merge filter is ported.
   W241 ports the analyser's `getSaturatedIndividualNodeForConcept(...)`
   reference lookup: concept data -> concept process data -> concept saturation
   reference data -> positive/negative saturation concept reference linking ->
   referenced saturation individual node. This intentionally ignores invalidated
   classifier reference state, matching the C++ saturated-node lookup.
   W242 ports the next gate in
   `testSubsumerCandidatePossibleWithMergedSaturatedModel(...)`: the resolved
   saturation node must be completed and its indirect status flags must not carry
   cardinality-problematic, insufficient, or nominal-connection flags before the
   downstream saturated-model merge probes are attempted.
   W243 ports the first downstream merge probe,
   `testConceptSetWithSaturatedModelMergable(...)`, including the saturation
   label-set iterator/read surface and the completion label-set descriptor-or-
   reapply-queue state needed for Konclude's polarity-clash and undecidable-
   reapply branches. W244 ports the second downstream probe,
   `testRoleSuccessorsWithSaturatedModelMergable(...)`, including the
   backward-propagation reapply walk over role successors and successor operand
   label checks. W245 ports the existential saturated-node resolver used by the
   final downstream probe: direct existential-successor reference-link lookup,
   single-operand fallback including the `CCALL` negation flip, and top-concept
   fallback for empty operand lists. W246 ports the trivial-propagation testing
   concept collector leaf used by both successor-collection overloads. W247
   ports `addAutomateTransactionConcepts(...)`: role-matching AQALL-family
   concepts now collect clean completed saturated operand nodes or fall back to
   trivial propagation tests, the AQAND-family branch recurses, and the
   successor-specific saturated-node gate rejects clashed nodes in addition to
   the cardinality-problematic/insufficient/nominal-connection flags. The
   W248 ports the first linked-role saturation successor substrate needed by
   those collectors: lazy node extension linked-role hash creation, role bucket
   lookup/create, successor-node data lookup, and active-successor checks over
   the already-ported `CSaturationSuccessorData` records. The
   W249 ports the completion-node overload of
   `collectSuccessorMergingNodesAndConcepts(...)`: indirect super-role
   iteration, completion role-reapply queue traversal, saturated/trivial operand
   collection, AQAND automate-transaction delegation, unsupported reapply
   rejection, and backward-role collection for inversed/missing successor-role
   paths are now live. W250 ports the recursive saturation-node overload:
   successor-influence concept scanning, substitute-node chasing/exclusion,
   successor backward-propagation reapply traversal, recursive saturated/trivial
   operand collection, inversed-role forwarding, and unsupported reapply
   rejection. W251 ports the first
   `testMultipleSaturatedSuccessorModelMergable(...)` preparation block:
   `CConceptNegationTriggerItem`, backward-role link blocking, and construction
   of the concept-negation trigger hash plus successor-influence concept list
   from trivial propagated concepts. W252 ports the successor saturation
   label-set trigger merge block: substitute-node resolution, iterator-based
   descriptor/implication-trigger merging, polarity/trigger conflict rejection,
   and first contributing saturation-node tracking. W253 ports the
   substitute-chain `CSaturationConceptDataItem` reference-linking merge before
   each substitute hop, including concept-tag trigger insertion, trigger/polarity
   conflict rejection, and first contributing saturation-node tracking. W254
   ports the next concept-trigger recursive-call preparation loop: existential
   trigger filtering by operator/cardinality, successor/trivial/backward
   collection, existential saturated-node resolution, and Konclude's `prepend`
   job shaping for the later `testSaturatedSuccessorModelMergable(...)` call. W255
   ports the dispatcher/gate prefix of `testSaturatedSuccessorModelMergable(...)`:
   by-value depth pre-decrement, shared-count pre-decrement, single-vs-multiple
   routing, and execution of W254 prepared jobs through that dispatcher payload.
   W256 ports the opening `testSingleSaturatedSuccessorModelMergable(...)` slice:
   substitute resolution, saturation label-set lookup, negated-`CCSUB`
   descriptor/implication/substitute-reference checks, and ALL-family successor
   influence collection/backward-role rejection. W257 ports the following
   non-extension saturation descriptor walk: direct successor-extension flag
   gating, `getConceptSaturationDescriptionLinker()` traversal, existential
   trigger filtering, successor collection, existential saturated-node
   resolution, and recursive job shaping. W258 ports the linked-role successor
   extension branch shared by the single/multiple successor helpers: direct
   extension-flag gating, linked-role hash traversal, active successor-data
   filtering, creation-role matching, and recursive job shaping from
   `mSuccIndiNode`. W259 wires the live W256-W258 single-successor slices and
   W250-W254/W258 multiple-successor slices into wrapper helpers that preserve
   Konclude's recursive-call ordering and shared merge-count/depth dispatcher
   payloads. W260 wires the immediate
   `testSaturatedExistentialsModelMergable(...)` recursive-call preparation
   layer over the completion-node successor collector for both saturation
   descriptor and linked-extension branches. W261 wires
   `testSubsumerCandidatePossibleWithMergedSaturatedModel(...)` through the
   merge-test eligibility gate, concept-set probe, role-successor probe, and
   W260 existential dispatch-preparation probe. W262 adds the live
   `testSaturatedSuccessorModelMergable(...)` dispatcher/body bridge over the
   currently ported single/multiple successor merge bodies, preserving
   Konclude's depth-by-value and shared-count predecrement gates. W263 threads
   that live executor into `testSaturatedExistentialsModelMergable(...)` and
   `testSubsumerCandidatePossibleWithMergedSaturatedModel(...)` live wrappers;
   the transitional dispatch-payload surfaces remain for compatibility tests
   while higher call sites migrate. W264 ports
   `testEquivalenceConceptAlternatives(...)` over the live merged-saturated
   model caller and records `CSaturatedMergedTestItem` state per alternative.
   W265 ports `collectEquivalenceConceptAlternatives(...)`: the work-list/set
   expansion for CCEQ/CCAND/CCOR and CCAQCHOOCE, node label-set containment with
   resolved descriptor polarity, cached saturated-merge short-circuiting, and
   the exact empty-alternative/all-unsatisfiable tail condition. W266 ports the
   recursive `checkCanHaveClashWithModel(...)` probe over resolved label-set
   descriptors/reapply queues, deterministic branch tags, propositional
   decomposition, CCAQCHOOCE filtering, and role-successor traversal. W267
   ports the live other-node BFS pre-pass that seeds from the corrected root's
   real successor iterator, snapshots reached nodes, expands successors only
   after the nominal/blocker guard, and wires a live-other-node classifier-state
   analyser wrapper. W268 ports the simple equivalent-subsumer saturated-merge
   overload and the equivalent-non-candidate possible-subsumer extraction block
   from `extractPossibleSubsumptionInformation`, including the TBox
   `getEquivalentConceptNonCandidateSet(false)` no-create path, per-concept
   filtering through the CCEQ alternative merge test, and Konclude's separate
   message flag/list semantics when the set exists but no element survives.
   W269 wires that live equivalent-non-candidate extraction into the root and
   other-node analyser message producers and adds a live-other-node wrapper that
   no longer requires the caller-supplied equivalent-non-candidate map. W270
   ports the `analyseSatisfiableTask` value-space-trigger gate that disables
   pseudo-model identifier extraction when ontology MBox value-space triggers
   exist, while preserving all other root/other-node message production. W271
   adds a task/context-facing analyser entry that reads the classification
   adapter and processing databox from `CSatisfiableCalculationTask` /
   `CalculationAlgorithmContext` and delegates to the live analyser path. W272
   ports the MBox-owned `CDatatypeValueSpacesTriggers` presence surface on
   `OntologyArenas`, preserves `CMBox::getValueSpacesTriggers(create)` lazy
   allocation semantics, and has the task/context analyser derive the
   pseudomodel suppression gate from ontology state instead of a caller-supplied
   shortcut boolean. W273 adds a classifier-side
   `CClassificationMessageDataObserver*` registry analogue, registered observer
   delivery, and a task/context analyser entry that resolves the adapter's
   observer handle through that registry before calling the W272 path. W274
   ports the KPSet class classifier's `interpreteSatisfiableResult` scheduler
   consumption slice: satisfiable-test counters/flags, satisfiable-item list
   insertion, successor unsat-derivation, predecessor decrementing, and
   next/next-candidate queue routing. W275 ports the matching KPSet role
   classifier `interpreteSatisfiableResult` queue/body slice over role testing
   items. W276 ports the classifier-facing computation-item and callback-event
   holders plus the class/role satisfiable-test branch of `interpreteTestResults`:
   received-callback counting, current-calculation decrementing, calculation-error
   failure flags, statistics reuse, and delegation into the W274/W275 satisfiable
   schedulers. W277 ports class `interpreteSubsumptionResult`: CCEQ candidate
   remapping, running possible-subsumption decrementing, true/false result
   marking, subsumer/up/down propagation links, `propagateDownSubsumption`,
   `prunePossibleSubsumptions`, and top-down/bottom-up queue maintenance with
   Konclude's constructor-default top-down ordering. W278 ports the matching
   role `interpreteSubsumptionResult` and role helper substrate: role possible
   subsumption map lookup/update, propagation/pruning helpers, interpreted
   subsumption counters, and top-down/bottom-up role queue maintenance. W279
   completes the local class/role `interpreteTestResults` dispatch body over the
   already-ported result handlers: satisfiable work items route to W274/W275 and
   subsumption work items route to W277/W278 with Konclude's `!testSat` inversion,
   while preserving received-callback counts, current-calculating decrements,
   error failure flags, and statistics reuse. W280 adds the ontology-side class
   `getWorkItemHash` / role `getComputationItemHash` equivalents and removes
   matching job/work-item entries during callback consumption, matching the C++
   cleanup point before statistics reuse. W281 ports the post-precheck
   class/role calculation registration blocks: satisfiable/subsumption work-item
   construction, work-hash insertion, satisfiable-test ordered marking,
   current-calculating increments, ordered-subsumption counters, created-task
   counters, and calculated-possible-subsumption increments for subsumption jobs.
   W282 ports the remaining job-level classification adapter holders on
   `CSatisfiableCalculationJob` plus the generator transfer into
   `CSatisfiableCalculationTask`, covering both class message and role-marked
   message adapters. W283 ports the adjacent KPSet job adapter setup calls:
   class satisfiable/subsumption registration now allocates and installs
   `CSatisfiableTaskClassificationMessageAdapter` equivalents with the upstream
   extraction flags and concept-reference hash, role satisfiable registration
   allocates and installs the concrete
   `CSatisfiableTaskClassificationRoleMarkedMessageAdapter` payload, and role
   subsumption intentionally leaves that adapter unset because the upstream
   function does. W284 ports the concrete allocation part of
   `createTemporaryRoleClassificationOntology`: temporary fake propagation/marker
   individuals, the `CCAND` all-propagation concept, per-role `CCMARKER`,
   `CCVALUE`, and `CCALL` concepts, operand wiring, marker-concept-to-item hash
   installation, and bottom-role exclusion. W285 adds the ordered
   `CSatisfiableCalculationJobGenerator` concept/individual assertion payload to
   `CSatisfiableCalculationJob` and ports the role satisfiable setup sequence:
   `existConcept` and `allPropConcept` on the propagation individual, then top
   object/data concept on the marker individual, plus the role-marked adapter.
   W286 adds the role-ontology data-role classification flag plus temporary top
   object/data concept storage and selects the correct top concept internally,
   matching the upstream `isDataRolesClassification()` branch. W287 ports the
   role `calculateSubsumption` job-generator assertion sequence: subsumed
   `existConcept`, possible-subsumer propagation concept, negated
   possible-subsumer marker concept, and selected top concept, while preserving
   upstream's absence of a role-marked adapter for subsumption. W288 adds the
   corresponding `SatisfiableCalculationTask` assertion storage and generator
   transfer so these job assertions survive task creation. W289 adds a typed
   `CProcessingDataBox` initialization-assertion staging surface and materializes
   the task's ordered concept/negation/individual triples into that databox state,
   preserving the exact construct payload for the following process-node/linker
   expansion slice. W290 ports the named-individual branch of that expansion:
   staged assertions now create/reuse nominal `CIndividualProcessNode` entries,
   install them in `CIndividualProcessNodeVector` under Konclude's negative
   individual node ids, set the constructed-node pointer, and prepend initializing
   concept linkers in C++ head order. W291 extends the construct target model to
   preserve named-individual, fixed-individual-id, and relative-new-node-id cases
   from `CSatisfiableCalculationConstruct`, expands fixed/relative targets into
   blockable process nodes, and updates `firstPossibleIndividualNodeID` with the
   same base-id/max-id rule as the C++ generator loop. W292 ports the adjacent
   node-initialization side effects: fresh nodes get the independent base
   dependency track point, materialized named individuals copy their concept/data/
   role/reverse-role assertion payloads onto the process node, anonymous/fixed/
   relative or base-task nodes receive `PRFINVALIDBLOCKINGORCACHING`, and every
   newly constructed node is inserted into the immediate processing queue. W293
   ports the base-task reference-node localization branch from the same C++
   construct loop: existing nodes are cloned through
   `initIndividualProcessNode(refIndiNode)` after following merged-into ids,
   queue-membership bits are cleared, `PRFCACHEDCOMPUTEDTYPESADDED` is removed,
   the clone is stored as local vector data, and repeated assertions reuse the
   localized node. W294 ports the adjacent ontology nominal-node recreation
   helper: `OntologyArenas` now carries active-individual and triples-index max
   state, the construct loop marks nominal triples assertions, and active or
   triples-indexed ABox individuals recreate nominal process nodes with copied
   assertion payloads and immediate-queue insertion. W295 ports the remaining
   construct-loop databox flag side effect:
   `setMultipleConstructionIndividualNodes(constructionIndiCount > 1)` is now
   mirrored when concept constructs are materialized into the databox.
   W296 removes one W2 process-layer deferral: the databox
   `getConceptNominalSchemaGroundingHash(true)` path now has a live
   context-threaded arena allocation/copy helper. W297 removes the adjacent
   `getRepresentativeVariableBindingPathSetHash(true)` deferral with the same
   live databox/context localization pattern over the concrete representative
   path-set hash arena. W298 removes the DB-2
   `getVariableBindingPathMergingHash(true)` deferral through the same
   arena-backed localize/copy/update helper pattern. W299 starts the DB-4
   blocking-hash getter cleanup: the signature-blocking and
   nominal-delaying candidate hashes now create fresh arena hashes from their
   previous hashes and publish the corresponding `use` ids. W300 ports the
   adjacent DB-4 `getBlockingIndividualNodeCandidateHash(true)` create/copy
   helper over the concrete blocking-candidate hash arena, preserving Konclude's
   copied-bucket COW semantics. W301 adds process-context DB-2 localization
   helpers for representative joining-key and representative joining hashes,
   mirroring the existing completion-context wrappers over the concrete
   representative hash arenas. W302 adds focused coverage for the existing
   marker-individual-node hash helper, verifying the same copied-bucket COW
   semantics used by the marker branch in label insertion. W303 adds direct
   DB-4 databox coverage for signature-blocking review-set creation from
   previous state and full clear semantics. W304 adds direct DB-4 databox
   coverage for early/late individual reactivation queue creation from previous
   queues and clear semantics. W305 adds direct DB-4 intrusive-linker coverage
   for cache-testing, sorted nominal non-deterministic, blocked-resolve,
   blockable-updated, and individual-process-node linker order/count behavior.
   W306 ports `CNodeSwitchHistory` as a real process-context arena object,
   adds the context-threaded DB-4 `getNodeSwitchHistory(true)` allocation/copy
   path, and verifies the switch-minimum/update semantics that the blocking
   callers need next. W307 ports `CBranchingTree` as a real process-context
   arena object, adds the DB-4 `getBranchingTree(true)` allocation/copy path,
   and verifies Konclude's task-copy, forced-child, previous-current, and base
   dependency behavior. W308 reconciles the main completion loop's node-switch
   sequence over the real `CNodeSwitchHistory`: the loop now creates the history,
   increments `CProcessTagger::mNodeSwitchTag`, records each individual switch,
   resets the min-modification baseline with `setMinModificationIndividual`, and
   applies the post-individual latest-switch update when the min-modification
   state was changed by rule processing.
   W309 reconciles `CCalculationAlgorithmContextBase`'s branch-tree initialization
   and forced-branch creation: `initTaskProcessContext` now initializes
   `mBranchTreeNode` and `mBaseDepNode` through the databox `CBranchingTree`, and
   `getNewBranchTreeNode` now forces child creation through that same tree instead
   of hand-allocating a branch child.
   W310 wires the real `CNodeSwitchHistory::getMinIndividualAncestorDepthAndNodeID`
   lookup into the optimized ancestor/anywhere blocking bounds in Units 19/20
   whenever a positive previous node-switch tag is already available, while
   leaving the separate tag-update protocol as the remaining follow-on.
   W311 ports that follow-on tag protocol for blocking data: the
   `CIndividualNodeBlockingTestData` and `CBlockingIndividualNodeCandidateData`
   node-switch / concept-label-set modification tag accessors now carry the
   Konclude `CProcessTag` semantics, and Unit 19 reads previous tags then updates
   localized block data from the live `CProcessTagger` at the ancestor/anywhere
   blocking entry points.
   W312 wires the Unit 20 candidate-hash half of that protocol: the typed
   `CBlockingIndividualNodeCandidateIterator` is returned and consumed by the
   hashed anywhere-blocking caller, `getBlockingIndividualNodeCandidateIterator`
   materializes candidate data through the arena-backed hash, reads max-valid /
   label-modification / node-switch tags in Konclude order, rebuilds candidate
   entries through the live label-set descriptor membership check, and updates
   label tag, node-switch tag, then max-valid id after the refresh loop.
   W313 completes the adjacent Unit 20 localized block-data bookkeeping:
   `getAnywhereBlockingIndividualNodeCanidateHashed` now allocates and initializes
   `CIndividualNodeBlockingTestData`, reads previous node-switch and
   concept-label modification tags from it, uses its previous blocker to skip the
   continue-tested candidate, stores the final blocker, and updates the tags from
   `CProcessTagger` when no blocker is found.
   W314 reconciles the linked-candidate wrapper around the same block-data
   substrate: `getAnywhereBlockingIndividualNodeLinkedCanidateHashed` now
   allocates/initializes localized block data, clears its stored blocker before
   the signature-cache test, reads any blocker restored by that test, uses the
   live label-set core-concept linker, and records the same last-core cursor
   defaults Konclude writes when the linked-candidate hash has no data.
   W315 wires Unit 20's blocked-successor propagation/reactivation loops to the
   real `CIndividualProcessNode::getSuccessorIterator` equivalent: both
   `propagateAddingBlockedProcessingRestrictionToSuccessors` and
   `reactivateIndirectBlockedSuccessors` now iterate the node successor-role hash,
   resolve successor individuals through the live edge API, and mutate only
   strictly deeper successors as Konclude does.
   W316 wires Unit 20's `addBlockingCoreConcept` through the live
   `CConceptProcessData::isCoreBlockingConcept` polarity flags and
   `CReapplyConceptLabelSet::addCoreConceptDescriptor`, while keeping the linked
   candidate-hash insertion explicitly deferred until the real
   `CBlockingIndividualNodeLinkedCandidateHash` lands. It also fixes this call
   site's concept-process-data null check to use the Rust `INVALID` id sentinel,
   so arena id `0` is not misread as null.
   W317 ports `CBlockingIndividualNodeLinker`,
   `CBlockingIndividualNodeLinkedCandidateData`, and
   `CBlockingIndividualNodeLinkedCandidateHash` as real process arenas, wires the
   databox linked-hash getter, and completes the linked candidate insertion in
   `addBlockingCoreConcept`. Unit 20's linked-candidate search now consumes the
   real linked data/linker chain for the representable core descriptor head; the
   remaining fidelity boundary is the still-folded `CCoreConceptDescriptor`
   wrapper, whose independent `next` chain is not split out yet.
   W318 ports that `CCoreConceptDescriptor` wrapper as a real process arena,
   changes label-set core-linkers and block-data last-added cursors to wrapper
   ids, and updates Unit 20's linked-candidate minimum-count search to traverse
   the real core-descriptor chain and unwrap each descriptor before hash lookup.
   W319 ports
   `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData` as a
   real process arena, re-aliases `BackendSyncDataId` to the typed object, and
   makes Unit 17's `getLocalizedIndividualBackendCacheSnychronisationData`
   allocate/copy the synchronisation snapshot instead of returning the marker
   `Id::NONE`. The new substrate exposes the exact Unit 20/25 criticality,
   synchronization, merged-node cursor, and reuse-state accessors needed for the
   backend-cache un-defer tail.
   W320 consumes that backend-sync substrate in Unit 20: the backend
   cardinality/neighbour criticality tests now read the live association-data
   pointer, criticality flags, merged-node cursors, last-tested concept/edge
   cursors, and all-neighbour forced-expansion flag, and write the localized
   last-critical-neighbour cursor plus criticality flags at the Konclude update
   points. Cache-handler label/cardinality semantics remain the explicit
   deferred boundary.
   W321 ports Unit 25's `validateBackendSynchronisationContinued` outer
   backend-sync state path: it now takes `BackendSyncDataId`, reads
   `isBackendCacheSynchron`, `getAssocitaionData`, and
   `getLastSynchronizationTestedConceptDescriptor`, uses the live label-set
   adding-sorted head, and writes `setLastSynchedConceptDescriptor`,
   `setLastSynchronizationTestedConceptDescriptor`, and
   `setBackendCacheSynchron`. The full descriptor-chain membership scan remains
   the explicit backend-cache-handler boundary.
   Remaining exact-port work nearby: continue the broader classifier/realizer
   scheduler/result-item surfaces around these adapter call sites, especially
   the full KPSet scheduler/event consumption of the W205-W206 queues, taxonomy/event routing above satisfiable-result interpretation, wiring the
   classifier-side observer registry to the full event/ontology routing layer,
   porting the full calculation-task analyser entry point around
   W230-W264, extending generated task assertion expansion into the remaining
   calculation-task assembly branches, role
   complex-role automata preprocessing for the temporary
   propagation concepts, replacing the temporary top concept stand-ins with real
   TBox handles, and realization queue/result mutations;
   continue the next Unit 26/driver tail after incremental expansion, especially
   incremental compatible-merge and the backend queue probes that still depend
   on backend helpers; Unit 04's propagation-operator enqueue branches remain
   gated by their existing deferred operator checks.
2. **Continue after representative JOIN.** The public
   `applyREPRESENTATIVEJOINRule` propagate-all branch is live as W69 and the
   exact `areRepresentativesJoinable` quick-fail is live as W70. The only known
   representative JOIN semantic gap is Konclude's own
   `propagateAllFlag == false` `ToDo!`, which should remain unimplemented unless
   the upstream code defines semantics.
3. **Continue propagation/PBIND fidelity tail.** The role-keyed and concept-keyed
   add/apply/is-in-queue paths plus the restricted role-iterator, condensed
   iterator, propagation-binding linker, propagation-binding fresh map producer,
   propagation-binding initial map producers, propagation-binding successor
   initial/fresh producers, the PBIND implication existing/new-binding callers,
   the PBIND variable new/existing special-binding allocation, the higher
   `propagatePropagationBindingsToSuccessor` dispatcher, the non-restricted
   `applyBINDPROPAGATEALLRule` role-successor fan-out, and the sibling
   `applyVARBINDPROPAGATEALLRule` successor fan-out with typed variable-binding
   successor producers, the same-node `applyVARIABLEBINDINGANDRule`
   missing/existing trigger paths, the existing-trigger condensed reapply drain,
   `applyVARBINDPROPAGATEIMPLICATIONRule` same-node trigger propagation, the
   variable-rule transition extension, the W41 VARBIND join helpers, the public
   `applyVARBINDPROPAGATEJOINRule` transition-extension block, and the public
   `applyVARBINDPROPAGATEGROUNDINGRule` path-set grounding call and its
   `createVARBINDPROPAGATEGROUNDINGDependency` deterministic dependency wrapper
   are now live. The representative
   `getGroundingConceptLinker(CRepresentativeVariableBindingPathMap*,...)`
   overload, `createREPRESENTATIVEGROUNDINGDependency` selected-path payload, and
   public `applyREPRESENTATIVEGROUNDINGRule` representative propagation-set/hash
   traversal are also live. The `createREPRESENTATIVEANDDependency` wrapper and
   `propagateRepresentative` helper are live as of W51, the W52 simple
   single-incoming `updateRepresentativePropagationSet` branch is live, the W53
   typed `CRepresentativeVariableBindingPathSetHash{Data}` substrate is live,
   W54 ports `createRESOLVEREPRESENTATIVEDependency` with resolve-map payloads
   and its conditional additional dependency, W55 ports the
   `updateRepresentativePropagationSet` merge/fold branch itself, W56 ports
   `requiresRepresentativePropagation` with the C++ direct-lookup and merge-walk
   map-subsumption branches, W57 wires public `applyREPRESENTATIVEANDRule`
   through missing-trigger and existing-trigger representative propagation, and
   W58 wires `createREPRESENTATIVEALLDependency` plus
   `propagateRepresentativeToSuccessor`'s missing-successor-label propagation
   branch, and W59 wires public `applyREPRESENTATIVEALLRule` through the live
   role-successor iterator and static role reapply queue, and W60 wires public
   `applyREPRESENTATIVEIMPLICATIONRule` through the C++ trigger-availability,
   binding-trigger insertion, trigger dependency-chain, and representative
   propagation branches, W61 wires public `applyREPRESENTATIVEBINDVARIABLERule`
   through the C++ transition-extension gate, binding-trigger insertion/reapply,
   new representative path-set data creation, incoming representative descriptor,
   and representative propagation-set update, and W62 starts the representative
   JOIN substrate with joining-key/common-key/all-data-extension containers.
   W63 adds the real representative joining hash/data and per-path-set joining
   hash/data containers over typed `ProcessContext` arenas. W64 adds the global
   representative variable-binding-path joining-key hash/data/hasher, W65 wires
   the completion-side joining-key data helper plus common-key map intersection,
   and W66 wires `createCommonJoiningAll` over the real common-key/resolve-map
   substrate. W67 wires the JOIN dependency wrapper, W68 wires the
   representative transition-extension substrate, W69 wires public
   `applyREPRESENTATIVEJOINRule` for the propagate-all branch, and W70 wires
   the exact representative-join quick-fail.
3. **Dependency-directed backjumping.** Keep replacing the chronological
   stand-ins with the faithful Unit 29 path: `clashedBacktracking` now drives the
   live tracking-line flow, branch track-point creation is live, and dependent
   branch task lists plus first OR/merge/distinct consumers can now be allocated,
   and task-priority strategy formulas read the real parent task depth. Child-
   context/databox realization plus backend/statistics surfaces are still
   incomplete.
4. **Drive a real ontology end-to-end.** Wire a thin entry that feeds KM's
   existing DL-clause/`ofn` output (or a hand-built `OntologyArenas`) into
   `run_completion_on`, and classify a small real ontology. Surfaces the next
   hot-path `todo!`s (the natural enqueue still has some W3-DEFER seams; a few
   edge-triggered paths still use direct scans/re-drive stand-ins).
5. **Broaden the un-defer tail** (toward "the entire port"):
   - Continue after W112 task-priority parent-depth wiring. The next nearby
     candidates are `createCalculationAlgorithmContext`/task process-context
     realization, databox branching instructions, scheduler communication,
     and the remaining task/backend/statistics branches inside
     `backtrackNonDeterministicBranchingClashedDescriptor`, the
     unsat-cache handler object/storage, the datatype clash path, the saturation
     occurrence collector skeleton, and the remaining Unit 35/36 `PORT-PENDING`
     installation/statistics tails.
   - Saturation un-defer (s02–s12, the W4-DEFER bodies) — the W4.5 satellites
     exist; the lazy-saturation pre-pass is what makes Konclude fast.
   - Cache backend (the 923 `W6-DEFER`): the F8 cache-event family + a single-
     thread write drain + the missing linker/counting APIs (see the W6.5 note in
     PORT.md). This is an optimization layer — the reasoner runs without it.
   - Datatypes, nominals (`O`) expansion, the `Self` and role-chain rules.
6. **Productionize**: add LGPL headers + attribution to `konclude_ht/`; expose a
   `km konclude_ht <ont>` subcommand or route the hybrid router to it; validate
   verdicts against Konclude on a small ORE fragment (the existing `.sig.gz`
   signature-diff harness).

## Recent accepted waves

W453 ports `CNominalCachingLossReactivationHashData` and
`CNominalCachingLossReactivationHash`, including the C++ copy constructor
semantics for previous/current data and DB-2 lazy localization that allocates
`CNominalCachingLossReactivationData` from the previous entry at the Konclude
create point.

W454 continues DB-1 `CProcessingDataBox` parent-copy fidelity: the ported
individual process/saturation vectors now perform the C++ `referenceVector`
handoff, a resolved ontology-init entry performs the exact getter-result field
assignments, and the already-ported DB-5 saturation satellites are copied from
the parent databox when a `ProcessContext` is supplied.

W455 ports `CCriticalSaturationConceptQueue`,
`CCriticalSaturationConceptTypeQueues`, and the critical queue type enum as real
process satellites with context-owned arenas, append/take helpers, lazy per-type
queue allocation, and queued-scan semantics.

Validation after W455: `cargo fmt --manifest-path engine/Cargo.toml --check`,
focused filters `nominal_caching_loss_reactivation_hash`,
`db2_context_threaded_hash_wrappers_allocate_and_reuse`,
`db1_parent_init_with_context`, and `critical_saturation`, `git diff --check`,
and `cargo test --quiet --manifest-path engine/Cargo.toml konclude_ht` all
pass. The broad filter is now 972 tests, 0 failed.

W456 ports `CRepresentativeVariableBindingPathHash` and its hash-data semantics:
entries are keyed by variable-binding path propagation id, copy/localization
preserves the previous use-data pointer while clearing the localized pointer,
and DB-2 `getRepresentativeVariableBindingPathHash` now allocates/localizes
through `ProcessContext`.

W457 ports `CIndividualNodeAnalizedConceptExpansionData` and
`CAnalizedConceptExpansionLinker`, including initialization from previous data,
null reset behavior, linker prepend/count semantics, context arenas, and PN-4
lazy localization through `CIndividualProcessNode`.

W458 wires the W455 critical saturation concept queue family into
`CIndividualSaturationProcessNode::getCriticalConceptTypeQueues`: the extension
data now stores the typed queue id, `ProcessContext` performs the lazy
allocation/init chain, and SAT-1 exposes the context-threaded exact accessor.

W459 ports `CSaturationIndividualNodeDatatypeData` and wires
`CIndividualSaturationProcessNode::getAppliedDatatypeData`: applied datatype and
data-literal pointers are represented as opaque ids, lazily allocated through
SAT-1 extension data, and copied during context-threaded saturation-node coping.

W460 ports `CLinkedDataValueAssertionSaturationData`, including the typed
`CXLinker<CRole*>` chain, Konclude's shallow copy/init/get behavior, and the
SAT-1/context lazy getter plus `addDataValueAssertion` prepend semantics.

W461 ports `CSaturationIndividualNodeSuccessorExtensionData`: its direct state,
reset, queued flag, resolve-data setter/getter, opaque dependent extension
handles, and SAT-1/context lazy `getSuccessorExtensionData` chain are now
arena-backed.

W462 ports `CSaturationSuccessorRoleAssertionLinker` and the SAT-1 role
assertion mutators: destination node, role, negation, next link, explicit
linker prepend, and allocated `addRoleAssertion` all follow the Konclude chain
semantics.

W463 ports `CCriticalPredecessorRoleCardinalityData` and
`CCriticalPredecessorRoleCardinalityHash`: role-keyed data lookup/creation,
hash copy, unproblematic concept neg-link prepend, and SAT-1/context lazy
`getCriticalPredecessorRoleCardinalityHash` are now arena-backed.

W464 ports `CSaturationDisjunctCommonConceptExtractionData`,
`CSaturationDisjunctCommonConceptCountHash{,Data}`, and
`CSaturationDisjunctExtractionLinker`: common-concept counting uses concept tags
and polarity guards, extraction continuation is initialized through
`CIndividualSaturationProcessNodeLinker`, extraction linkers preserve Konclude
prepend order, and SAT-1/context lazy `getDisjunctCommonConceptExtractionData`
is now arena-backed.

W465 ports `CSaturationATMOSTSuccessorMergingData`,
`CSaturationATMOSTSuccessorMergingHash`, and
`CSaturationATMOSTSuccessorMergingHashData`: the merging continuation linker,
concept-merging linker chain, concept-descriptor keyed merge-data hash, merged
linked-role successor hash, remaining-cardinality hash, merge-distinct hash, and
merge-distinct set now follow the Konclude lazy materialization boundary. The
SAT-1/context lazy `getATMOSTSuccessorMergingData` accessor is now arena-backed.

W466 resolves the databox ATMOST merging process-linker queue representation:
`mSaturationATMOSTMergingProcessLinker` now stores a real
`CIndividualSaturationProcessNodeLinker*` head id, `add` prepends by setting the
linker's `next`, and `take` advances to `getNext()` and clears the popped link,
matching `CProcessingDataBox.cpp` 2097-2122.

W467 ports the `tryATMOSTConceptSuccessorMerging` driver loop from
`CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp` 3969-4027.
The databox ATMOST merging worklist is now drained through the real
`CIndividualSaturationProcessNodeLinker` chain, queued flags are cleared after
`takeSaturationATMOSTMergingProcessLinker`, indirect insufficient/clashed nodes
are skipped, and each queued node's
`CSaturationATMOSTSuccessorMergingData` concept-linker chain is walked through
the typed `getATMOSTConceptMergingData` boundary before delegating to the still
deferred per-individual merge body.

W468 ports `CIndividualSaturationSuccessorLinkDataLinker` and the matching
SAT-11/DB-6 free-list helpers. The linker is now arena-backed with a
`CSaturationSuccessorData*` payload and intrusive `next` pointer; `mRemSatIndiSuccLinkDataLinker`
is now a real head id instead of a collapsed vector, `takeRemaining...` advances
to `getNext()` and clears the popped link, `addRemaining...` prepends through
`setNext(oldHead)`, and `create/releaseIndividualSaturationSuccessorLinkDataLinker`
reuse that free list or allocate a fresh linker through `ProcessContext`. The
ATMOST merging hash data field `mSuccessorLinkMergingLinker` is now typed to the
same linker id.

W469 starts the live port of `collectATMOSTConceptRelevantSuccessors`
(`CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
3779-3961). The function boundary is now typed for
`CConceptSaturationDescriptor*`, `CLinkedRoleSaturationSuccessorData*`, and
`CIndividualSaturationSuccessorLinkDataLinker*&`; it reads the ATMOST concept,
role, allowed cardinality, and operand list from the real arenas; detects
Konclude's trivial qualification (`CCATOM`/`CCSUB`, non-negated operands); walks
the active `CSaturationSuccessorData` map; checks ordinary saturation-successor
labels through `CReapplyConceptSaturationLabelSet` descriptor/tag lookup; updates
`minCardinality`; raises `INDSATFLAGCLASHED` for a single non-nominal successor
above the allowance; and prepends countable successors through the real
SAT-11 linker free-list helper. The remaining branches are still explicitly
deferred to their missing Konclude substrates: VALUE-nominal completion-graph
resolution, `CConceptRoleBranchingTrigger`, and `CSaturationConceptDataItem`
qualification-representative shortcuts.

W470 ports the `CSaturationConceptDataItem` qualification-representative checks
inside the live ordinary-successor branch of
`collectATMOSTConceptRelevantSuccessors`. The function now reads
`succNode->getSaturationConceptReferenceLinking()` through SAT-1's existing
`ExtendedConceptReferenceLinkingData` arena, compares operand concept/negation
and role ranges exactly like the C++ branch, and suppresses merge-link creation
when the successor is the representative individual. The no-operand branch also
recognizes the ontology top concept representative via the processing databox.
The still-deferred parts of this function are now narrowed to VALUE-nominal
completion-graph resolution and non-trivial `CConceptRoleBranchingTrigger`
handling.

Validation after W470: `cargo fmt --manifest-path engine/Cargo.toml --check`,
focused filters `representative_variable_binding_path_hash`,
`analized_concept_expansion`, and
`sat1_critical_concept_type_queues_context_allocates_through_extension_data`,
`sat1_applied_datatype_data`,
`sat1_coping_context_copies_applied_datatype_data`,
`sat1_linked_data_value_assertion`, and
`sat1_data_value_assertion_add_prepends_roles_and_copy_is_shallow`,
`sat1_successor_extension_data`, and
`sat1_role_assertion_linker_context_prepends_and_allocates`,
`sat1_critical_predecessor_role_cardinality`, `sat1_disjunct`, and
`sat1_atmost_successor_merging`, and
`db5_saturation_atmost_merging_process_linker`, and
`s08_atmost_merging_driver`,
`link_data_linker`, and `s08_collect_atmost`,
`git diff --check`, and `RUSTFLAGS=-Awarnings cargo test --quiet
--manifest-path engine/Cargo.toml konclude_ht` all pass. The broad filter is
now 1008 tests, 0 failed. Current source marker counts after W470 are
`759 W6-DEFER`, `727 W3-DEFER`, `230 PORT-PENDING`, `202 W4-DEFER`,
`108 W2-DEFER`, `32 RECONCILE-NEED`, and `4 W8-DEFER`.

W471 ports the SAT-8 cardinality-mergeability predicate cluster around
`isIndividualSuccessorLinkCardinalityMergeable` and
`isIndividualSuccessorLinkCardinalityExtendedMergeable`
(`CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
4467-4493 and 4599-4635). `s08.rs` now unwraps real
`CSaturationSuccessorData` ids to successor saturation nodes, rejects the same
VALUE-nominal, nominal-integrated, ABox-representation, and data-value-applied
cases as Konclude, checks creation-role subset containment through the live
`mCreationRoleLinker` vectors, and compares saturation label-set containment
with the C++ `ignoreANDConcepts` filters over AND/AQAND/IMPLAQAND/BRANCHAQAND
positives and OR negatives. The extended predicate now requires symmetric
creation-role subset containment and calls the still-deferred
`isIndividualNodeLabelMergingProblematic` in both directions at the original
Konclude decision points.

Validation after W471: focused filter `s08_` passes 11 tests; `cargo fmt
--manifest-path engine/Cargo.toml --check`, `git diff --check`, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` pass. The broad filter is now 1012 tests, 0 failed. Current
source marker counts after W471 are `759 W6-DEFER`, `728 W3-DEFER`,
`230 PORT-PENDING`, `195 W4-DEFER`, `108 W2-DEFER`, `32 RECONCILE-NEED`, and
`4 W8-DEFER`.

W472 ports `getIndividualNodeQualifiedSuccessorCount`
(`CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
4637-4713). The Rust signature now preserves the nullable
`CSortedNegLinker<CConcept*>*` qualification as `Option<&[NegLink<ConceptId>]>`,
then follows the live `CLinkedRoleSaturationSuccessorHash` role bucket, walks
active `CSaturationSuccessorData` entries, counts VALUE-nominal successors,
checks successor saturation label sets through the same concept/polarity
containment helper used by W469-W471, and preserves Konclude's trivial vs
non-trivial qualification branches. This removes the stale whole-body deferral
without touching the adjacent merge-distinct cardinality helpers, which still
need faithful multi-value hash semantics.

Validation after W472: focused filter `s08_` passes 13 tests; `cargo fmt
--manifest-path engine/Cargo.toml --check`, `git diff --check`, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` pass. The broad filter is now 1014 tests, 0 failed. Current
source marker counts after W472 are `759 W6-DEFER`, `728 W3-DEFER`,
`230 PORT-PENDING`, `194 W4-DEFER`, `108 W2-DEFER`, `32 RECONCILE-NEED`, and
`4 W8-DEFER`.

W473 ports the direct conflict prefix of
`isIndividualNodeLabelMergingProblematic`
(`CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
4716-4803). `CReapplyConceptSaturationLabelSet` now exposes the
`getConceptDescriptorAndReapplyQueue` tag lookup shape, and SAT-8 uses it to
walk the merging successor's saturation descriptors, find matching direct
descriptors in the problem-testing successor label, and report problematic
merges when the same concept occurs with opposite polarity. The branch that
requires a concrete `CImplicationReapplyConceptSaturationDescriptor` remains
deferred, as do the later criticality scans over predecessor cardinality
concepts, sibling `collectLinkedSuccessorNodes`, and
`CRoleBackwardSaturationPropagationHash`.

Validation after W473: focused filter `s08_` passes 15 tests; `cargo fmt
--manifest-path engine/Cargo.toml --check`, `git diff --check`, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` pass. The broad filter is now 1016 tests, 0 failed. Current
source marker counts after W473 are `759 W6-DEFER`, `728 W3-DEFER`,
`230 PORT-PENDING`, `194 W4-DEFER`, `108 W2-DEFER`, `32 RECONCILE-NEED`, and
`4 W8-DEFER`.

W474 ports the `CImplicationReapplyConceptSaturationDescriptor` substrate and
uses it in the next `isIndividualNodeLabelMergingProblematic` branch. The
saturation satellite now has a typed descriptor id, arena-backed descriptor
record (`getImplicationConcept`, `getNextTriggerConcept`, `getNext`/`setNext`),
typed `CConceptSaturationDescriptorReapplyData::mImpReapplyConSatDes`, iterator
and label-set lookup return types, a `ProcessContext` arena/accessor trio, and a
live SAT-11 factory allocation. SAT-8 now handles the Konclude branch where a
problem-testing label has no direct descriptor but has an implication reapply
queue: for positive merging concepts it reads the implication concept's first
operand and returns problematic when neither successor label contains that
operand. The remaining tail is still the absent-concept cardinality criticality
scan plus full label-set reapply insertion/replay.

Validation after W474: focused filter `s08_` passes 16 tests; `cargo fmt
--manifest-path engine/Cargo.toml --check`, `git diff --check`, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` pass. The broad filter is now 1017 tests, 0 failed. Current
source marker counts after W474 are `759 W6-DEFER`, `728 W3-DEFER`,
`230 PORT-PENDING`, `193 W4-DEFER`, `107 W2-DEFER`, `32 RECONCILE-NEED`, and
`4 W8-DEFER`.

W475 ports the implication-reapply trigger advancement leaf in SAT-11. The
context now has a faithful
`insertConceptReapplicationReturnTriggered` equivalent for saturation label sets:
it creates/copies the per-tag reapply data, reports whether a positive direct
concept descriptor already triggers the queued implication, increments
`mTotelCount` only for the first reapply chain on that tag, and prepends the
descriptor via the live implication-reapply `append` chain. SAT-11's
`updateImplicationReapplyConceptSaturationDescriptor` now advances the stored
trigger suffix, allocates/registers the next trigger, recursively fires when the
next trigger is already present, and executes the implication's first operand at
the final trigger through the existing `addConceptFilteredToIndividual` leaf.
The remaining implication boundary is now the larger
`insertConceptToIndividualConceptSet` orchestration:
`insertConceptReturnClashed`, replay of returned chains after new concept
insertion, implication seed generation, and modified-update linkers.

Validation after W475: focused filter `s11_` passes 2 tests; focused filter
`s08_` still passes 16 tests; `cargo fmt --manifest-path engine/Cargo.toml
--check`, `git diff --check`, and `RUSTFLAGS=-Awarnings cargo test --quiet
--manifest-path engine/Cargo.toml konclude_ht --lib` pass. The broad filter is
now 1019 tests, 0 failed. Current source marker counts after W475 are
`759 W6-DEFER`, `728 W3-DEFER`, `228 PORT-PENDING`, `192 W4-DEFER`,
`107 W2-DEFER`, `32 RECONCILE-NEED`, and `4 W8-DEFER`.

### W476 — SAT-11 label insertion and implication replay orchestration

W476 ports `CReapplyConceptSaturationLabelSet::insertConceptReturnClashed`
(`CReapplyConceptSaturationLabelSet.cpp` 246-280) as a context-threaded
`ProcessContext` helper and brings the main
`insertConceptToIndividualConceptSet` replay path live (`CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
7424-7535). `addConceptToIndividual` now initializes the freshly allocated
concept-saturation descriptor before insertion. SAT-11 now follows Konclude's
operator-code insertion/containment decisions, inserts into the saturation label
set, replays matching implication reapply chains, seeds implication-trigger and
implication-adding-skipping descriptors, calls the modified-update-linker hook,
and handles opposite-polarity clashes by linking the clashed descriptor and
setting `INDSATFLAGCLASHED`.

The remaining boundary is narrower: modified-update linker internals are still
opaque, `CConceptSetFlags` is not yet live, and deeper label-set copy/flag
helpers remain deferred.

Validation after W476: focused filter `s11_` passes 4 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1021 tests, 0 failed. Current source marker counts
after W476 are `759 W6-DEFER`, `728 W3-DEFER`, `228 PORT-PENDING`,
`190 W4-DEFER`, `107 W2-DEFER`, `32 RECONCILE-NEED`, and `4 W8-DEFER`.

### W477 — SAT modified-update linker and disjunct extraction enqueue

W477 ports `CSaturationModifiedProcessUpdateLinker` and the live parts of its
label-set integration: `createModifiedProcessUpdateLinker` now allocates a typed
per-test arena object, `CReapplyConceptSaturationLabelSet::addModifiedUpdateLinker`
is live as a context-threaded prepend helper, and
`processModificationUpdateLinkers` traverses the typed chain and dispatches
`UPDATEPDISJUNCTCOMMONCONCEPTSEXTRACTION`.

The disjunct-common-concept extraction continuation linker is now represented as
an arena ID, and `addDisjunctCommonConceptExtractionToProcessingQueue` performs
the Konclude idempotent enqueue: check queued flag, set it, and push the
continuation linker into the processing databox.

Remaining boundary: `initializeExtractDisjunctCommonConcept` still cannot wire
the full disjunct extraction graph until the disjunction concept-reference
linking derefs are live; `CConceptSetFlags` and deeper label-set copy/flag
helpers remain deferred.

Validation after W477: focused filter `s11_` passes 6 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1023 tests, 0 failed. Current source marker counts
after W477 are `759 W6-DEFER`, `728 W3-DEFER`, `227 PORT-PENDING`,
`186 W4-DEFER`, `107 W2-DEFER`, `32 RECONCILE-NEED`, and `4 W8-DEFER`.

### W478 — SAT-11 backward-propagation fan-out paths

W478 completes the now-unblocked `CRoleBackwardSaturationPropagationHash` fan-out
arms in SAT-11 status and cardinality propagation.
`updateDirectNotDependentAddingIndividualStatusFlags` now fans indirect flags out
through every `CBackwardSaturationPropagationLink` source before the
non-inverse-connected pass. `updateIndirectAddingIndividualStatusFlags` now
includes the same backward-source worklist arm. `updateMaxCardinalityCandidates`
now propagates maximum at-least/at-most candidates through copy-dependent,
role-backward-propagation, and non-inverse-connected sources.

Validation after W478: focused filter `s11_` passes 9 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1026 tests, 0 failed. Current source marker counts
after W478 are `759 W6-DEFER`, `728 W3-DEFER`, `227 PORT-PENDING`,
`182 W4-DEFER`, `107 W2-DEFER`, `32 RECONCILE-NEED`, and `4 W8-DEFER`.

### W479 — SAT successor-connected nominal marker cleanup

W479 removes stale `PORT-PENDING` documentation from
`updateAddingSuccessorConnectedNominal`. The method was already live after the
successor-connected nominal set substrate and W478 role-backward fan-out work:
it now explicitly stands as the Konclude worklist over copy-dependent,
role-backward-propagation, and non-inverse-connected source nodes, gated by
`requiresAddingSuccessorConnectedNominals`.

The SAT-11 module now carries local regressions for the nominal worklist:
backward-source fan-out is applied once, duplicate propagation is suppressed by
set membership, and the ABox representation-node guard skips backward/non-inverse
source fan-out while preserving the copy-dependent pass that occurs before the
guard in Konclude.

Validation after W479: focused filter `s11_` passes 11 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1028 tests, 0 failed. Current source marker counts
after W479 are `759 W6-DEFER`, `728 W3-DEFER`, `226 PORT-PENDING`,
`182 W4-DEFER`, `107 W2-DEFER`, `32 RECONCILE-NEED`, and `4 W8-DEFER`.

### W480 — SAT-3 implication rule

W480 ports `applyIMPLICATIONRule` now that the implication-reapply descriptor,
label-set creation path, and `updateImplicationReapplyConceptSaturationDescriptor`
tail are live. The rule now reads the concept-saturation descriptor from the
process linker, snapshots the implication concept's operand linker list as the
initial trigger suffix, allocates the Rust arena equivalent of Konclude's stack
`CImplicationReapplyConceptSaturationDescriptor`, gets/creates the node's
`CReapplyConceptSaturationLabelSet`, and delegates to the SAT-11 update helper.

Focused SAT-3 tests cover both Konclude branches reached through that helper:
a one-operand implication executes the first operand immediately, while a
multi-operand implication registers an implication-reapply entry for the next
trigger.

Validation after W480: focused filter `s03_` passes 2 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1030 tests, 0 failed. Current source marker counts
after W480 are `759 W6-DEFER`, `728 W3-DEFER`, `226 PORT-PENDING`,
`182 W4-DEFER`, `107 W2-DEFER`, `32 RECONCILE-NEED`, and `4 W8-DEFER`.

### W481 — SAT-3 tableau saturation rule dispatch

W481 ports `applyTableauSaturationRule`, replacing the remaining member-function
pointer jump-table placeholder with a Rust `match` that mirrors Konclude's
constructor assignments for the positive and negative jump vectors. The rule now
reads the concept-saturation descriptor, descriptor negation, and operator code,
then dispatches to the same sibling `apply*Rule` target or falls back to
`applyELSERule` when the jump-table slot is empty.

Focused SAT-3 tests cover live dispatch paths: positive `CCBOTTOM` reaches
`applyBOTTOMRule`, an unknown operator falls through to `applyELSERule`, and
positive `CCIMPL` reaches the W480 `applyIMPLICATIONRule` body.

Validation after W481: focused filter `s03_` passes 5 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1033 tests, 0 failed. Current source marker counts
after W481 are `759 W6-DEFER`, `728 W3-DEFER`, `226 PORT-PENDING`,
`180 W4-DEFER`, `107 W2-DEFER`, `32 RECONCILE-NEED`, and `4 W8-DEFER`.

### W482 — SAT-3 automaton transition addability test

W482 ports `testAutomateTransitionOperandsAddable`, removing the stale whole-body
deferral now that the SAT-1 reapply concept saturation label-set lookup is live.
The method mirrors Konclude's helper: recurse through `CCFS_AQAND_TYPE`
automaton states, then for a role-matching `CCFS_AQALL_TYPE` state scan the
operands and return true on the first concept/polarity pair not already present
in the node's saturation label set.

Focused SAT-3 tests cover missing AQALL operands, already-present operands with
matching negation, role mismatch, and AQAND recursion into an AQALL child.

Validation after W482: focused filter `s03_` passes 9 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1037 tests, 0 failed. Current source marker counts
after W482 are `759 W6-DEFER`, `728 W3-DEFER`, `225 PORT-PENDING`,
`178 W4-DEFER`, `107 W2-DEFER`, `32 RECONCILE-NEED`, and `4 W8-DEFER`.

### W483 — SAT-4 cardinality rule entry points

W483 ports `applyATMOSTRule` and `applyATLEASTRule` in SAT-4 now that the
concept-saturation descriptor chain, concept parameter/role reads, status flags,
max-cardinality candidate propagation, critical-concept hook, and the adjacent
functional-extension hooks are available. `applyATMOSTRule` now mirrors
Konclude's cardinality calculation, negative-cardinality clash, restricted flag,
max-atmost update, cardinality-one functional/qualified-functional branch, and
critical ATMOST registration. `applyATLEASTRule` now mirrors the parameter plus
negation cardinality calculation, max-atleast update, and successor-creation
delegation.

The successor constructor itself remains the recorded SAT-2 deferred body, so
the focused regression evidence is deliberately scoped to the live side effects:
max-cardinality candidates, negation adjustment, cardinality-restricted flag, and
negative-cardinality clash.

Validation after W483: focused filter `s04_` passes 4 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1041 tests, 0 failed. Current source marker counts
after W483 are `759 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`,
`176 W4-DEFER`, `107 W2-DEFER`, `32 RECONCILE-NEED`, and `4 W8-DEFER`.

### W484 — Unit 12 MERGEDCONCEPT dependency factory wrapper

W484 ports `createMERGEDCONCEPTDependency`, replacing the stale
`RECONCILE-NEED` note with the live factory-shaped allocation. With dependency
building disabled it still returns `Id::NONE` and leaves the continuation track
point untouched. With dependency building enabled it now allocates a
`DepKind::MergedConcept` DetLink dependency node, stores the concept dependency
track point on the dependency base, stores the merge-step dependency track point
on the DetLink predecessor link, updates the branching tag, and materializes the
continuation dependency track point.

Regression coverage pins both the disabled guard and the exact DetLink factory
shape, including base/link track-point placement and continuation materialization.

Validation after W484: focused filter `create_merged_concept_dependency` passes
2 tests, 0 failed. `RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path
engine/Cargo.toml konclude_ht --lib` passes 1043 tests, 0 failed. Current source
marker counts after W484 are `757 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `176 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W485 — SAT-7 successor-extension queue driver

W485 ports `processNextSuccessorExtensions`, removing the stale queue-level
deferral now that `CSaturationSuccessorExtensionIndividualNodeProcessingQueue`
is represented in the process context. The driver now mirrors Konclude's loop:
read the databox successor-extension queue without creating it, repeatedly take
the next current individual while no extension has processed, skip separated
nodes, conditionally call the ALL and FUNCTIONAL successor-extension processors
according to the configured flags, and clear the current queue entry when no
processor reports an update.

The per-node ALL/FUNCTIONAL processors themselves remain the recorded SAT-7
deferred bodies, so the focused regression evidence is scoped to live queue
semantics: missing queue returns false, an unprocessed queued node is cleared,
and separated nodes are skipped and cleared even when both extension flags are
enabled.

Validation after W485: focused filter `s07_` passes 3 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1046 tests, 0 failed. Current source marker counts
after W485 are `757 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`,
`175 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W486 — SAT-6 FUNCTIONAL extension queue-flag installer

W486 ports `installSuccessorPredecessorRoleFunctionalityConceptsExtension`, using
the now-live linked-role successor hash and role-backward propagation hash
satellites. The function now mirrors Konclude's two flag updates: when a linked
successor hash already exists, create/read the role bucket and set
`mRoleFUNCTIONALConceptsQueuingRequired`; always get/create the role-backward
propagation hash and set `mRolePredecessorMergingQueuingRequired` for the role.
It returns true only when either flag is newly installed.

Focused tests cover the backward-prop-only path, the existing linked-successor
bucket path, and idempotence on a second call.

Validation after W486: focused filter `s06_` passes 3 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1049 tests, 0 failed. Current source marker counts
after W486 are `756 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`,
`175 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W487 — SAT-6 FUNCTIONAL successor-role dispatcher

W487 ports `updateSuccessorRoleFUNCTIONALConceptsExtensions(role)`, the
role-keyed dispatcher overload. It now reads the node's linked-role successor
hash without creating it, gets the role bucket without creating it, checks
`mRoleFUNCTIONALConceptsQueuingRequired`, clears
`mRoleFUNCTIONALConceptsProcessingQueued`, and delegates to the `_for_succ_data`
worker only when `mSuccCount > 1`.

The `_for_succ_data` worker remains the recorded deep FUNCTIONAL merge boundary,
so regression evidence is scoped to the live dispatcher states: missing linked
hash, missing role bucket, and `succ_count <= 1` clearing the processing flag
without delegation.

Validation after W487: focused filter `s06_` passes 6 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1052 tests, 0 failed. Current source marker counts
after W487 are `755 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`,
`175 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W488 — SAT-6 FUNCTIONAL successor-data worker prefix

W488 ports the exact C++ prefix of
`updateSuccessorRoleFUNCTIONALConceptsExtensions(succData)` through the
successor-chain counting guard. The worker now takes the typed
`CLinkedRoleSaturationSuccessorData*` id, resolves the node's linked successor
hash, reads `mLastLink`, walks the `CSaturationSuccessorData::mNextLink` chain,
counts only active non-`mVALUENominalConnection` successors, and tracks the max
`mSuccCount` before the `succCount > 1 && maxSuccCardinality <= 1` merge branch.

The remaining merge/resolve/rewire block is still the recorded SAT-6 boundary
because it depends on the FUNCTIONAL extension-data cursor, resolve-data tower,
linker pool, subset-deactivation, and successor-link rewiring APIs. The C++
explorer confirmed this is the safest bounded slice: lines 1516-1538, stopping
at the merge guard without inventing missing PU-SAT-10/11 behavior.

Validation after W488: focused filter `s06_` passes 8 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1054 tests, 0 failed. Current source marker counts
after W488 are `755 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`,
`175 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W489 — FUNCTIONAL successor-extension cursor substrate

W489 ports the successor-facing slice of Konclude's
`CSaturationIndividualNodeFUNCTIONALConceptsExtensionData`,
`CSaturationLinkedSuccessorRoleFUNCTIONALConceptsExtensionHash`, and
`CSaturationSuccessorFUNCTIONALConceptExtensionData`. The process context now
owns typed arenas for the per-node FUNCTIONAL extension data and per-role
successor FUNCTIONAL extension records, with context-threaded lazy getters
matching the C++ create/get paths.

`CSaturationIndividualNodeSuccessorExtensionData::mFUNCTIONALConceptsExtensionData`
is now a typed id instead of an opaque integer. SAT-6's
`updateSuccessorRoleFUNCTIONALConceptsExtensions(succData)` now gets/creates the
FUNCTIONAL extension tower, gets/creates the role record, and reads the real
`mLastExaminedLinkedSucc` cursor instead of assuming a null cursor. The C++
explorer confirmed these fields and noted that this Konclude snapshot reads the
successor cursor but does not update it in this overload.

Validation after W489: focused filter `s06_` passes 9 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1055 tests, 0 failed. Current source marker counts
after W489 are `755 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`,
`175 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W490 — SAT-6 FUNCTIONAL merge-linker prefix

W490 ports the next exact slice of the SAT-6 FUNCTIONAL successor merge branch:
the C++ `succDataMap` traversal, temporary
`CIndividualSaturationSuccessorLinkDataLinker` construction, first-qualifying
copy-base selection, and head-linker release. The branch now iterates successor
map entries in key order, filters active non-`mVALUENominalConnection`
successors, reads each successor node's saturation label-set concept count, and
preserves Konclude's quirk of selecting only the first candidate with concept
count greater than zero rather than updating to a later larger label.

The wave stops before `collectResolveIndividualExtendableConceptMap`,
`getResolvedIndividualNodeExtension`, and successor-link rewiring, which remain
the recorded SAT-6 merge boundary. The C++ explorer confirmed this corresponds
to cpp lines 1543-1575 plus the cleanup call at 1585.

Validation after W490: focused filter `s06_` passes 10 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1056 tests, 0 failed. Current source marker counts
after W490 are `755 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`,
`175 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W491 — SAT-6 FUNCTIONAL concept-extension collection call-through

W491 ports the next exact call-through in the SAT-6 FUNCTIONAL merge branch.
After building the temporary merge-linker chain and choosing
`resolveLinkedSuccData`, the worker now traverses `mergingSuccDataLinker`,
skips the selected copy-base successor, and calls
`collectResolveIndividualExtendableConceptMap(copyIndiProcSatNode, succNode,
conExtMap, ctx)` for each remaining linked successor before releasing the
temporary linker head.

The collection helper itself is still the recorded SAT-10 descriptor/map
boundary: it reaches into `CReapplyConceptSaturationLabelSet` descriptor
iteration and the temporary `CPROCESSINGHASH<cint64,CConceptNegationPair>`.
The next required slice is therefore the typed resolve-data/hash plus concept
extension map substrate, then SAT-6 can port `getBaseExtensionResolveData(true)`,
`getResolvedIndividualNodeExtension(...)`, and
`setLastResolvedIndividualNode(...)`.

Validation after W491: focused filter `s06_` passes 10 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1056 tests, 0 failed. Current source marker counts
after W491 are `755 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`,
`175 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W492 — SAT-10 resolve substrate and concept-extension map collection

W492 ports the typed SAT-10 substrate needed by the SAT-6 FUNCTIONAL merge tail.
The process context now owns `CSaturationIndividualNodeExtensionResolveData`,
`CSaturationIndividualNodeExtensionResolveHash`, and the temporary
concept-extension map, and SAT-1 exposes context-threaded helpers for successor
extension resolve data. `collectResolveIndividualExtendableConceptMap` now
compares the copy-base and extension saturation labels and records only missing
or polarity-different concept descriptors.

Validation after W492: focused filter
`s10_collect_resolve_extendable_concept_map_diffs_extension_label_set` passes
1 test, 0 failed. Focused filter `s06_` passes 10 tests, 0 failed. Focused
filter `sat1_successor_extension_data` passes 4 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1057 tests, 0 failed. Current source marker counts
after W492 are `756 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`,
`174 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W493 — SAT-10 concept-extension-map overload traversal

W493 ports the `CPROCESSINGHASH<cint64,CConceptNegationPair>` overload of
`getResolvedIndividualNodeExtension`. The overload now consumes the typed
concept-extension map, performs the first resolve pass over every
concept/negation pair, creates a resolved node when the resolve record still has
no processing node, and performs the second add pass through
`addConceptFilteredToIndividual` before preprocessing the resolved node. The
extension-node overload now reuses the W492 collector instead of carrying a
duplicate deferred descriptor-diff block.

Validation after W493: focused filter
`s10_collect_resolve_extendable_concept_map_diffs_extension_label_set` passes
1 test, 0 failed. Focused filter `s06_` passes 10 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1057 tests, 0 failed. Current source marker counts
after W493 are `756 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`,
`171 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W494 — SAT-10 typed resolve-data leaf and create path

W494 migrates the SAT-10 resolve leaf from the older opaque integer path to
`SaturationIndividualNodeExtensionResolveDataId`. The concept/negation leaf now
checks the copy node's saturation label for an already-contained concept,
lazily allocates and caches child resolve records under the resolve hash, and
rebases the copy node when a cached child already has a processing node.
`createResolvedIndividualNode` records the newly allocated processing node on
the resolve data and stores the resolve record on the resolved node's successor
extension data. Neighbour resolve records now use the same typed hash substrate.

Validation after W494: focused filter `s10_` passes 2 tests, 0 failed. Focused
filter `s06_` passes 10 tests, 0 failed. Focused filter
`sat1_successor_extension_data` passes 4 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1058 tests, 0 failed. Current source marker counts
after W494 are `756 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`,
`142 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W495 — SAT-6 FUNCTIONAL resolved-node acquisition

W495 ports the next exact SAT-6 FUNCTIONAL merge-tail call sequence. After the
temporary successor merge linker has been built, collected into the
concept-extension map, and released, the worker now obtains
`getSuccessorExtensionData(true)->getBaseExtensionResolveData(true)` from the
selected copy-base successor, calls SAT-10's typed
`getResolvedIndividualNodeExtension(resolveData, conExtMap, copyNode, ctx)`, and
stores the resulting processing node in
`CSaturationSuccessorFUNCTIONALConceptExtensionData::mLastResolvedIndividualNode`.

The remaining SAT-6 FUNCTIONAL tail is still explicit: successor-link rewiring,
inactive-successor deactivation/add-extension, backward propagation link
installation, status/nominal/cardinality propagation, the non-inverse connected
fallback, and the final `updated = true` transition remain deferred until the
corresponding Konclude mutators are live. Coverage now asserts the current
resolved node follows Konclude's copy-base selection quirk when the collected
concept-extension map is empty.

Validation after W495: focused filter `s06_` passes 10 tests, 0 failed. Focused
filter `s10_` passes 2 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1058 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W495 are `756 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `142 W4-DEFER`, `107 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W496 — linked-role saturation successor mutator substrate

W496 ports the next process-layer substrate needed by the SAT-6 FUNCTIONAL
rewiring tail. `ProcessContext` now exposes context-threaded equivalents for the
core `CLinkedRoleSaturationSuccessorHash` mutators used by that tail:
individual-id-keyed successor-data lookup with Konclude's force-new
copy/inactivate behavior, active creation-role checks,
`hasActiveLinkedSuccessor`, `addExtensionSuccessor`, and
`deactivateLinkedSuccessor`.

The implementation preserves the C++ details that matter for later SAT-6
integration: successor map keys are saturation individual ids, extension adds
copy the previous successor record when forcing a new creation, active-count
increments are tied to non-negated creation-role presence, and deactivation
negates the creation-role link and zeroes the successor count when active count
falls to zero. The older raw-node lookup helper remains for pre-existing
scaffolding tests, but new SAT-6/SAT-7 code should use the hash-level
Konclude-shaped helpers.

Validation after W496: focused filter `sat1_linked_role_successor_hash` passes
2 tests, 0 failed. Focused filter `sat1_role_backward_propagation_hash` passes
3 tests, 0 failed. Current source marker counts after W496 remain
`756 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`, `142 W4-DEFER`,
`107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W497 — SAT-10 extension-node resolve hash cache

W497 ports the SAT-10 extension-node overload's
`CSaturationIndividualNodeExtensionResolveHash` cache path. The resolve hash now
has typed node-key accessors for `CIndividualSaturationProcessNode*`, and
`getResolvedIndividualNodeExtension(resolveData, extensionNode, ...)` now looks
up the cached resolve record before building the concept-extension map, stores a
newly resolved record under the extension node on a miss, and rebinds the copy
node when a cached record already owns a processing node.

While validating this slice, `createResolvedIndividualNode` was tightened to
use the arena-aware saturation-node copy initializer before invoking the older
SAT-2 wrapper. That gives resolved nodes the label-set substrate needed by the
second add pass while preserving the wrapper's existing accounting side effect.

Validation after W497: focused filter `s10_` passes 3 tests, 0 failed. Focused
filter `s06_` passes 10 tests, 0 failed.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1060 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W497 are `756 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `139 W4-DEFER`, `107 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W498 — SAT-6 FUNCTIONAL positive-super-role successor rewiring

W498 ports the next strict block inside SAT-6
`updateSuccessorRoleFUNCTIONALConceptsExtensions`: after the resolved successor
node is acquired, the Rust path now walks each active linked successor's
non-negated creation-role linkers, checks whether the resolved node already has
an active link for that creation role, suppresses duplicate insertion/removal in
Konclude's `connectionAlreadyExist` case, and then applies the positive
indirect-super-role rewiring through the linked-role successor hash.

The old successor is deactivated through the arena-backed
`deactivateLinkedSuccessor` substrate and the resolved node is inserted through
`addExtensionSuccessor`, preserving the individual-id keyed hash behaviour
ported in W496. The resolved node also receives the indirect status flags,
successor-connected nominal set, max-cardinality candidate flags, and the
non-inverse connection back-link when the C++ guard permits it.

The remaining SAT-6 FUNCTIONAL boundary is narrower: the negated-super-role
branch still requires the exact `installBackwardPropagationLink` path, and
downstream predecessor/reapply effects remain separate from this positive-role
rewire slice.

### W499 — SAT-10 successor concept-extension map

W499 ports the typed `CSaturationSuccessorConceptExtensionMapData` and
`CSaturationSuccessorConceptExtensionMap` substrate, adds its `ProcessContext`
arena, and replaces SAT-10's successor-extension placeholder in
`getResolvedIndividualNodeExtensionSuccessor`.

The method now mirrors Konclude's two map walks: first resolve every positive and
negative concept extension into the resolve-data chain, then, on a miss, create
the resolved node, allocate/get its saturation label set through the context, add
the same positive and negative concepts to that label set, and preprocess the
resolved node. Focused tests cover polarity tracking per concept tag and the
positive/negative successor resolver path.

Validation after W499: focused filter `s06_` passes 10 tests, focused filter
`s10_` passes 5 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1062 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W499 are `756 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `136 W4-DEFER`, `107 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W500 — SAT-6 backward propagation link installer

W500 ports the bounded negated-super-role branch inside SAT-6 FUNCTIONAL
successor rewiring. When an indirect creation super-role is negated and the C++
`makeNewSuccessorConnections` guard permits it, the Rust path now allocates a
typed `CBackwardSaturationPropagationLink`, initializes it from the source
saturation node and role, and calls the ported installer.

The new `installBackwardPropagationLink` slice installs the link into the
destination node's role-backward propagation hash, deduplicates by source
individual at the head walk, prepends fresh links, reads any existing reapply
descriptor, and sets the predecessor-merging queue flags. When functional
queueing is requested and the destination FUNCTIONAL extension data is already
initialized, it queues successor-extension processing and registers the
linked-predecessor-added role process linker.

The remaining boundary is now the replay call to
`applyBackwardPropagationConcepts`, which still depends on the unported
backward-propagation reapply descriptor drain. Focused tests cover direct
install/dedup/queueing and the FUNCTIONAL merge negated-super-role branch.

Validation after W500: focused filter `s06_` passes 13 tests, focused filter
`s10_` passes 5 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1065 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W500 are `755 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `136 W4-DEFER`, `107 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W501 — SAT-6 backward propagation reapply replay

W501 ports the exact `applyBackwardPropagationConcepts` drain behind W500's
installer. The Rust method now walks each
`CBackwardSaturationPropagationReapplyDescriptor`, reads its
`CConceptSaturationDescriptor`, obtains the reapply concept and polarity, then
iterates the concept operand list and calls `addConceptFilteredToIndividual` on
the source saturation node with Konclude's operand-negation xor descriptor
negation.

`installBackwardPropagationLink` now calls this replay method when a fresh link
is installed, the role bucket already has a reapply descriptor, and
`applyBackPropDes` is true. A focused regression verifies the replay through the
real saturation label-set insertion path, including the xor polarity case.

Validation after W501: focused filter `s06_` passes 14 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1066 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W501 are `754 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `136 W4-DEFER`, `107 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W502 — SAT-6 predecessor FUNCTIONAL dispatcher prefix

W502 ports the role-keyed
`updatePredecessorRoleFUNCTIONALConceptsExtensions` dispatcher now that the
role-backward propagation and linked-successor hashes are live. The method now
gets/creates the role-backward propagation hash, materializes the role bucket as
Konclude does, checks `mRolePredecessorMergingQueuingRequired`, clears
`mRolePredecessorMergingProcessingQueued`, reads the backward-link chain, and
dispatches to the worker only when the node has linked successor data for the
role with `mSuccCount >= 1`.

The worker overload now uses typed linked-successor data and typed backward
propagation links through the live prefix: it finds the first active successor,
reads its successor node and creation-role linker, walks the backward-link
chain, skips the `succIndiNode == predAncIndiNode` case, and reaches the exact
Konclude call boundary for `createAncestorSuccessorMergingExtension`.

The remaining side effect is deliberately left at the SAT-8 boundary because
`createAncestorSuccessorMergingExtension` is still a W4 skeleton. Focused
coverage verifies the dispatcher clears the processing flag and reaches the
typed boundary without inventing the SAT-8 merge result.

Validation after W502: focused filter `s06_` passes 15 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1067 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W502 are `753 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `136 W4-DEFER`, `107 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W503 — SAT-8 ancestor-successor merge extension

W503 ports the main body of Konclude's
`createAncestorSuccessorMergingExtension` and wires the W502 SAT-6 predecessor
dispatcher through to it. The SAT-8 method now performs the inverse-role
ancestor successor lookup, checks the active ancestor-successor data keyed by
the predecessor individual id, forwards the successor label concepts to the
ancestor once, adds the copy-depending linker, preprocesses the resolved
ancestor node, and records the forwarding-predecessor merge guard.

The functional extension satellite now carries Konclude's
`mForwardingPredMergedHash` as a typed node-to-role set, with the same
node-only and node+role membership checks plus the setter used by SAT-8. For
each non-negated creation role, SAT-8 resolves the inverse creation role and
then follows Konclude's indirect-super-role loop: positive super roles add the
extension successor in the ancestor's linked-role successor hash, while negated
super roles allocate and install a backward saturation propagation link.

Two Konclude call points are intentionally preserved as their own remaining
boundaries rather than shortcut locally:
`collectLinkedSuccessorNodes` and `addNewLinkedExtensionProcessingRole` are
still SAT-7 skeletons, but W503 now calls them at the exact places the C++ body
does.

Validation after W503: focused filter `s08_` passes 17 tests, focused filter
`s06_` passes 15 tests, and `RUSTFLAGS=-Awarnings cargo test --quiet
--manifest-path engine/Cargo.toml konclude_ht --lib` passes 1068 tests, 0
failed. `cargo fmt --manifest-path engine/Cargo.toml --check` passes, and
`git diff --check` passes. Current source marker counts after W503 are
`752 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`, `135 W4-DEFER`,
`107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W504 — SAT-7 role-assertion linked-successor leaf

W504 ports the role-assertion branch callee
`addLinkedSuccessorNodeForRoleAssertion`. The Rust body now mirrors the C++
loop over `role->getIndirectSuperRoleList()`: it applies the
`!superRoleIt->isNegated() ^ roleInversion` polarity test and adds the
destination node as a linked successor with cardinality 1 and the assertion role
as the creation role.

The process substrate now has a separate
`linked_role_successor_hash_add_linked_successor` helper for Konclude's ordinary
`addLinkedSuccessor` path, distinct from the W496/W503 extension-successor
helper. While validating this, the shared successor-data read helper was aligned
with Konclude's `mSuccNodeDataMap` keying: successor data lookups now use the
saturation node's individual id and return `NONE` for out-of-range node ids
instead of indexing the arena.

`collectLinkedSuccessorNodes` is intentionally still not partially wired:
porting only the role-assertion half would advance watermarks while leaving the
concept-successor branch (`addLinkedSuccessorNodeForConcept`, including VALUE
successors) unprocessed, which would diverge from Konclude.

Validation after W504: focused filter `s07_` passes 5 tests, focused filter
`linked_role_saturation_successor_data_reports_active_successor` passes, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1070 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W504 are `752 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `134 W4-DEFER`, `107 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W505 — SAT-7 concept linked-successor leaf

W505 ports `addLinkedSuccessorNodeForConcept` over the live concept-process
reference-linking substrate. The Rust body now follows Konclude's resolution
order exactly: the concept's existential-successor reference first, then every
operand with `operandNegation ^ conNegation`, and finally the object/data top
concept only when there was no special node and no operand linker. The C++ quirk
that merely having operands suppresses the top fallback is preserved.

VALUE nominal successors are now live through
`ProcessContext::linked_role_successor_hash_add_linked_value_successor`, which
keys `mSuccNodeDataMap` by nominal individual id, sets
`mVALUENominalConnection`/`mVALUENominalID`, leaves `mSuccIndiNode` empty, and
records the creation-role linker separately from ordinary and extension
successors.

Focused SAT-7 regressions now cover direct existential references, operand
fallback, top fallback suppression by operand presence, and VALUE nominal
successor insertion. `collectLinkedSuccessorNodes` remains the next SAT-7
boundary: with both role-assertion and concept callees live, it can now be
ported without advancing Konclude's watermarks past unprocessed concept-linked
successors.

Validation after W505: focused filter `s07_` passes 9 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1074 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W505 are `751 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `133 W4-DEFER`, `107 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W506 — SAT-7 linked-successor collector

W506 ports `collectLinkedSuccessorNodes` over the live SAT-7 callees and
process arenas. The collector now lazily creates the node's
`CLinkedRoleSaturationSuccessorHash`, scans the current
`CReapplyConceptSaturationLabelSet` descriptor head down to the previous
concept watermark, dispatches generating SOME/AQSOME/ALL/ATLEAST/ATMOST/VALUE
descriptors to `addLinkedSuccessorNodeForConcept`, then scans the
`CSaturationSuccessorRoleAssertionLinker` head down to the previous assertion
watermark and dispatches to `addLinkedSuccessorNodeForRoleAssertion`.

The Konclude watermark semantics are preserved: the collector captures both
current heads before traversal and updates `mLastExaminedConDes` and
`mLastExaminedRoleAssLinker` only after both scans complete. Head-prepended
chains therefore process only new descriptors/assertions on later calls and do
not skip the older unprocessed tail.

Focused SAT-7 regressions now cover concept collection, concept watermark
skipping on a second collection, role-assertion collection, and processing only
newly prepended role assertions after the assertion watermark has advanced. The
next SAT-7 boundary is now `addNewLinkedExtensionProcessingRole` and the
remaining successor-extension registration tower.

Validation after W506: focused filter `s07_` passes 11 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1076 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W506 are `751 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `132 W4-DEFER`, `107 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W507 — SAT-7 linked extension processing role queueing

W507 ports `addNewLinkedExtensionProcessingRole` and
`addSuccessorExtensionToProcessingQueue` over the live successor-extension
substrate. The node-level ALL-concepts extension data is now typed and
arena-backed, the ALL branch derives/caches queuing-required from role backward
propagation reapply data before installing the role-process linker, and the
FUNCTIONAL branch installs the role into both linked-successor-added and
linked-predecessor-added role-process linker chains.

The successor-extension processing queue insertion now creates the
successor-extension and ALL face on demand, marks extension processing queued
once, and inserts the node by individual-id priority. Focused SAT-7 regressions
cover queue idempotence, ALL queueing through a backward reapply linker, and
FUNCTIONAL queueing through both role-process linker chains.

Validation after W507: focused filter `s07_` passes 14 tests, focused filter
`sat1_successor_extension_data_context_create_allocates_and_initializes` passes
1 test, and `RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path
engine/Cargo.toml konclude_ht --lib` passes 1079 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W507 are `751 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `130 W4-DEFER`, `107 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W508 — SAT-7 dependent role-extension fan-out

W508 ports the remaining role-process portions of the SAT-7 dependent-node
fan-out helpers over the W507 successor-extension substrate. The ALL fan-out now
creates successor-extension and ALL-face data for each copy-dependent node,
unconditionally queues the dependent node, and installs an ALL role-process
linker only when the ALL face is already initialized and the role is not already
present.

The FUNCTIONAL linked-successor-added, linked-predecessor-added, and
functionality-added fan-outs now use the typed FUNCTIONAL extension data and
role-process linker chains. The linked-predecessor-added helper preserves
Konclude's important difference: it queues and registers only initialized
FUNCTIONAL faces. The linked-successor-added and functionality-added helpers
queue dependents unconditionally before their respective linker registration
checks.

Focused SAT-7 regressions cover ALL fan-out, FUNCTIONAL linked-successor fan-out,
FUNCTIONAL linked-predecessor guarded fan-out, and functionality-added fan-out
without an initialization guard.

Validation after W508: focused filter `s07_` passes 18 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1083 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W508 are `751 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `119 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W509 — SAT-7 FUNCTIONAL extension registrars

W509 ports `addFUNCTIONALConceptExtensionProcessingRole` and
`addQualifiedFUNCTIONALAtmostConceptExtensionProcessing` over the typed
successor-extension and FUNCTIONAL extension data. The role registrar now
honors `mConfFUNCTIONALConceptsExtensionProcessing`, creates the successor and
FUNCTIONAL extension records at the original call points, queues the node, and
installs a deduplicated functionality-added role-process linker.

The qualified-atmost registrar now uses the live `CConceptSaturationProcessLinker`
arena to queue a deduplicated concept saturation descriptor on the FUNCTIONAL
qualified-atmost linker chain. Focused SAT-7 regressions cover the disabled
configuration gate, queue creation, linker insertion, and duplicate suppression
for both registrars.

Validation after W509: focused filter `s07_` passes 20 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1085 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W509 are `751 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `117 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W510 — SAT-7 ALL extension registrar

W510 ports `addALLConceptExtensionProcessingRole` over the typed
`CRoleBackwardSaturationPropagationHashData` value and the W507 ALL extension
substrate. The C++ `CRoleBackwardSaturationPropagationHashData&` is represented
as a direct mutable Rust reference, since the hash-map value has no stable arena
id; the method then follows Konclude's control flow: honor
`mConfALLConceptsExtensionProcessing`, set
`mRoleALLConceptsProcessingQueued` once, create successor-extension and ALL-face
data, queue the node, and add a deduplicated ALL role-process linker when the
ALL face is already initialized.

Focused SAT-7 coverage verifies the disabled gate, queued flag mutation, queue
insertion, initialized ALL-face linker insertion, and duplicate suppression.

Validation after W510: focused filter `s07_` passes 21 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1086 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W510 are `751 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `116 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W511 — SAT-7 ALL extension queue processor

W511 ports `processSuccessorALLConceptsExtensions` over the typed
successor-extension and ALL-face substrate. The method now follows Konclude's
control flow: resolve the node successor-extension and ALL face, collect linked
successors, initialize the ALL face once, call the SAT-6 initializer at the
original point, fan out processing to copy-dependent individuals, increment
`mALLSuccExtInitializedCount`, drain the role-process linker chain through
`updateSuccessorRoleALLConceptsExtensions`, release each role linker through the
SAT-11 pool hook, clear the ALL and successor queued flags, and finally call
`updateSuccessorALLConceptsExtensions`.

The deeper SAT-6 propagation workers remain at their existing deferral
boundaries; W511 makes the SAT-7 queue/init/linker shell around those C++ call
sites live.

Focused SAT-7 coverage verifies first-time ALL initialization, queued flag
clearing, copy-dependent fan-out, role-process linker draining, linker `next`
clearing, and release into the remaining-role-linker pool.

Validation after W511: focused filter `s07_` passes 23 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1088 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W511 are `751 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `115 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W512 — SAT-7 FUNCTIONAL extension queue processor

W512 ports `processSuccessorFUNCTIONALConceptsExtensions` over the typed
successor-extension and FUNCTIONAL-face substrate. The method now follows
Konclude's worklist order: resolve the node successor-extension and FUNCTIONAL
face, collect linked successors, initialize the FUNCTIONAL face once, drain the
functionality-added role linker chain through
`installSuccessorPredecessorRoleFunctionalityConceptsExtension`, requeue the
installed role on the linked-successor worklist, fan out functionality-added
processing to copy-dependent individuals, and install predecessor-added and
copy-initializing role linkers. It then drains the linked-successor-added,
linked-predecessor-added, and qualified-functional-atmost worklists through the
original SAT-6 update hooks and SAT-11 release hooks, and clears the successor
queued flag.

The deeper SAT-6 merge/update workers remain at their existing deferral
boundaries. W512 makes the SAT-7 FUNCTIONAL queue/init/linker shell around those
C++ call sites live without substituting a different merge policy.

Focused SAT-7 coverage verifies FUNCTIONAL first initialization, successor queued
flag clearing, linked-successor/predecessor role-linker draining and release,
qualified-atmost concept-linker draining and release, and dependent-node
qualified-atmost fan-out.

Validation after W512: focused filter `s07_` passes 26 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1091 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W512 are `751 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `114 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W513 — SAT-7 ALL successor concept-extension sink

W513 ports `addSuccessorExtensionsALLConcept` over the typed ALL successor
concept-extension substrate. SAT-7 now allocates and resolves
`CSaturationLinkedSuccessorIndividualALLConceptsExtensionData` and
`CSaturationSuccessorALLConceptExtensionData` through `ProcessContext`, including
Konclude's `mOnlyRole` fast path and promotion to the role-keyed hash when a
second role is requested.

The method follows the C++ operator guards: positive `ALL/AQALL` concepts and
negated `SOME/AQSOME` concepts contribute their operands to the successor
extension map, operand polarity is xor-flipped for the negated-SOME case, and
the sink's concepts-updated flag drives the return value exactly as in Konclude.

Focused SAT-7 coverage verifies positive ALL operand insertion, negated SOME
polarity flipping, duplicate suppression after the update flag is cleared, and
the `mOnlyRole` to role-hash promotion path.

Validation after W513: focused filter `s07_` passes 29 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1094 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W513 are `751 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `113 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W514 — SAT-6 ALL role successor propagation

W514 ports the SAT-6 ALL role propagation boundary that feeds the W513
`addSuccessorExtensionsALLConcept` sink. `CSaturationSuccessorExtensionData` is
now a typed arena object with the two Konclude watermarks
`mLastExaminedLinkLinker` and `mLastExaminedALLConReaDes`, and
`CLinkedRoleSaturationSuccessorData::mExtensionData` now holds that typed id
instead of an opaque placeholder.

`initializeSuccessorALLConceptsExtensions` now creates the node ALL face, scans
the linked-role successor hash, clears `mRoleALLConceptsProcessingQueued` on
matching backward-propagation data, and delegates to the worker when a reapply
linker exists. The role-keyed overload now clears the linked-successor and
backward-propagation queue flags before dispatching, matching cpp 1831-1850.

The `succData` worker now follows cpp 943-1014: it reads the successor-extension
watermarks, decides whether to iterate full links and/or full reapply chains,
skips VALUE nominal links, visits each creation role, adds required successor
cardinality, replays backward-propagation ALL descriptors through the SAT-7
sibling, queues modified ALL successor-extension data on the node ALL worklist,
and advances both watermarks.

Focused SAT-6 coverage verifies required-cardinality insertion, ALL operand map
insertion, extension-process queuing, watermark advancement, and dispatcher queue
flag clearing.

Validation after W514: focused filter `s06_` passes 17 tests, focused filter
`s07_` passes 29 tests, and `RUSTFLAGS=-Awarnings cargo test --quiet
--manifest-path engine/Cargo.toml konclude_ht --lib` passes 1096 tests, 0
failed. `cargo fmt --manifest-path engine/Cargo.toml --check` passes, and
`git diff --check` passes. Current source marker counts after W514 are
`747 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`, `113 W4-DEFER`,
`107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W515 — SAT-6 ALL extension worklist drain

W515 ports `updateSuccessorALLConceptsExtensions` over the W513/W514 ALL
successor-extension substrate. The method now resolves the node linked-role
successor hash, successor-extension data, and ALL face, then drains
`mExtensionProcessLinker` in Konclude order. Each queued
`CSaturationSuccessorALLConceptExtensionData` has its queued flag cleared, its
successor concept-extension map and cardinality watermarks read, and its last
resolved node defaulted to the original successor node when unset.

The update branch follows cpp 1852-1966: concept-updated entries resolve through
`getResolvedIndividualNodeExtensionSuccessor`; positive indirect super-roles
deactivate the previous linked successor and add the resolved extension
successor with the required cardinality; negated super-roles install a backward
propagation link when the resolved node changed; status flags, successor
connected nominals, and cardinality candidates propagate from the resolved node;
and non-inverse connected-node links are installed when the change was not only
cardinality and no backward link was connected. Last-resolved and
last-connected-cardinality watermarks are advanced exactly at the C++ point.

Focused SAT-6 coverage verifies positive-super-role rewiring to the resolved
successor, cardinality watermark advancement, queued flag clearing,
non-inverse-connected fan-out, and negated-super-role backward propagation link
installation.

Validation after W515: focused filter `s06_` passes 19 tests, focused filter
`s07_` passes 29 tests, and `RUSTFLAGS=-Awarnings cargo test --quiet
--manifest-path engine/Cargo.toml konclude_ht --lib` passes 1098 tests, 0
failed. `cargo fmt --manifest-path engine/Cargo.toml --check` passes, and
`git diff --check` passes. Current source marker counts after W515 are
`746 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`, `113 W4-DEFER`,
`107 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W516 — SAT-6 qualified-FUNCTIONAL role dispatcher

W516 ports the role-keyed
`updateSuccessorRoleQualifiedFUNCTIONALConceptsExtensions` dispatcher overload
(cpp 1064-1075) now that W514's typed linked-role successor data is live. The
method reads the node's linked-role successor hash without creating it, resolves
the role bucket, checks Konclude's `mSuccCount > 1` guard, and delegates to the
qualified `_for_succ_data` worker with the typed
`LinkedRoleSaturationSuccessorDataId`.

The large qualified worker body remains the explicit SAT-6 boundary: it still
needs the qualifying concept-linker walk, label-set `containsConcept` predicate,
and the qualified merge/resolve/rewire flow from cpp 1690-1825. This wave does
not claim that worker is complete.

Focused SAT-6 coverage verifies the dispatcher no-hash, no-role-bucket,
single-successor, and multi-successor boundary cases. The multi-successor case
reaches the still-deferred worker and therefore still returns false until that
worker is ported.

Validation after W516: focused filter `s06_` passes 23 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1102 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W516 are `745 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `113 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W517 — SAT-9 critical concept queue insertion

W517 ports the live queueing half of
`addCriticalConceptDescriptor` (cpp 3386-3406). When
`mConfAddCriticalConceptsToQueues` is enabled, the method now creates a
`CConceptSaturationProcessLinker`, initializes it with the descriptor, obtains
the node's `CCriticalSaturationConceptTypeQueues`, resolves the typed per-kind
critical queue, prepends the descriptor linker, and inserts the node into the
databox critical individual processing queue only if it was not already queued.

This wave also reconciles the old opaque `CCT_*` placeholders with the real
Konclude queue enum order used by `CriticalSaturationConceptQueueType`
(`FORALL`, `ATMOST`, `DISJUNCTION`, `EQCANDIDATE`, `VALUE`, `NOMINAL`). The
direct-critical-to-insufficient branch remains live and unchanged.

The larger SAT-9 critical-concept checker remains explicitly deferred: draining
all per-type critical queues and applying the `isCritical*` tests still depends
on the surrounding descriptor/label/successor satellites.

Validation after W517: focused filter `s09_` passes 3 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1104 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W517 are `745 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `112 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W518 — SAT-9 critical concept dependent-node fan-out

W518 ports `addCriticalConceptForDependentNodes` (cpp 2985-2998). The method now
iterates the source node's copy-dependent individual node linker chain, selects
each dependent node's direct or indirect saturation status flags according to
Konclude's `directFlagsCheck`, and calls the W517 live
`addCriticalConceptDescriptor` helper when `checkFlags == 0` or the selected
flags do not contain `checkFlags`.

The port preserves the C++ fan-out boundary: it only propagates the descriptor to
dependent nodes. The larger `checkCriticalConceptsForNode` queue drain and the
per-kind `isCritical*` descriptor tests remain separate SAT-9 work.

Focused SAT-9 coverage verifies unconditional dependent-node propagation and
direct-vs-indirect status-flag filtering, including the `getIndividualID` queue
key used by the databox critical individual queue.

Validation after W518: focused filter `s09_` passes 5 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1106 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W518 are `745 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `111 W4-DEFER`, `107 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W519 — PN-3 successor-role hash accessor reconciliation

W519 reconciles the PN-3 `getSuccessorRoleHash`,
`getSuccessorRoleIterator`, and `hasSuccessorIndividualNode` overloads with the
already-live context-owned `CSuccessorRoleHash` backend. The legacy `&self`
compatibility methods remain empty where they cannot dereference arena-owned
hash ids, but new context-threaded PN-3 overloads now faithfully lazy-create the
successor-role hash, seed real `SuccessorRoleIterator`s, and test successor
individual ids through the same backend as Konclude.

Focused PN-3 coverage verifies non-creating lookup, one-time lazy allocation,
installed successor detection by id and node, and iterator return of the
installed edge. This preserves the C++ semantics while making the Rust ownership
boundary explicit.

Validation after W519: focused filter `pn3_` passes 4 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1108 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W519 are `745 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `111 W4-DEFER`, `105 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W520 — PN-3 individual-link topology wrappers

W520 reconciles PN-3's `installIndividualLink`, `removeIndividualLink`, and
`removeIndividualConnection` overloads with the already-live context-owned
topology helpers. New context-threaded PN-3 wrappers now drive Konclude's
reapply-role successor hash insertion/removal, successor-role hash insertion,
last-added-link update, and successor-connection removal through `ProcessContext`.

The legacy no-context compatibility methods remain explicit fallbacks because
they cannot dereference arena-owned role-successor hashes or edge payloads on
their own. Their stale W2 marker comments now point to the live context-threaded
route instead.

Focused PN-3 coverage verifies install return count and last-added-link update,
role-successor count changes, Konclude's `removeIndividualLink` behavior of not
removing the successor-role hash entry, and `removeIndividualConnection`
removing that successor entry.

Validation after W520: focused filter `pn3_` passes 5 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1109 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W520 are `745 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `111 W4-DEFER`, `99 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W521 — PN-3 disjoint successor-role wrappers

W521 reconciles PN-3's `hasNegationDisjointToIndividual`,
`getDisjointSuccessorRoleHash`, `installDisjointLink`,
`removeDisjointLinks`, and `getDisjointSuccessorRoleIterator` overloads with
the already-live context-owned `CDisjointSuccessorRoleHash` backend. New
context-threaded PN-3 wrappers now lazy-create the disjoint successor-role hash,
install negation-disjoint edges keyed by opposite individual id, test disjoint
role links by id or node, remove all links for a successor id, and seed real
`DisjointSuccessorRoleIterator`s.

The legacy no-context compatibility methods remain explicit fallbacks because
they cannot dereference arena-owned disjoint hashes or edge payloads on their
own. Their stale W2 marker comments now point to the live context-threaded route
instead.

Focused PN-3 coverage verifies non-creating lookup, one-time lazy allocation,
install/read by id and node, iterator successor id plus edge return order, and
removal of the successor's disjoint links.

Validation after W521: focused filter `pn3_` passes 7 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1111 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W521 are `745 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `111 W4-DEFER`, `94 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W522 — propagation-binding reapply concept hash

W522 ports `CPropagationBindingReapplyConceptHash`,
`CPropagationBindingReapplyConceptHashData`, and
`CPropagationBindingReapplyConceptIterator` in `process::propagation_binding`.
The hash is now an arena-owned `ProcessContext` object keyed by Konclude's
`TIndividualConceptPair` `(individual node id, concept)`, with live add, take,
has, init/copy, and iterator surfaces.

`CPropagationBindingSet::getPropagationBindingReapplyConceptHash` now
lazy-allocates the hash through `ProcessContext`, `initPropagationBindingSet`
copies a predecessor hash in the context-threaded path, and
`addPropagationBindingReapplyConceptDescriptor` now updates both the live reapply
hash and the existing propagation-binding map data chain.

Focused coverage verifies direct hash add/take/iterator behavior, Konclude's
value-copy behavior in `takePropagationBindingReapplyConceptDescriptor`,
set-level lazy hash allocation, hash+map insertion order, and predecessor-hash
copying during set initialization.

Validation after W522: focused filter `propagation_binding` passes 16 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1113 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W522 are `745 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `111 W4-DEFER`, `94 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W523 — blocking-candidate iterator backing-map removal

W523 reconciles `CBlockingIndividualNodeCandidateIterator::removeLastIndividualCandidate`
with the arena-owned `CBlockingIndividualNodeCandidateData` map. The existing
snapshot iterator remains available for read-only compatibility, but the
context-threaded iterator constructor now records the owning candidate-data id,
and `remove_last_individual_candidate_in_context` erases the last-yielded key
from the real `BTreeMap` just as Konclude erases through `mCandidateMap`.

Completion Unit 20's anywhere-blocking candidate cleanup now uses the
context-threaded removal path, so invalid or purged blocker candidates are
removed from the shared candidate hash rather than only from a local iterator
snapshot.

Focused coverage verifies context-backed removal mutates the arena map while
preserving the next-cursor behavior, and that the old snapshot-only fallback
remains local.

Validation after W523: focused filter `blocking_candidate_iterator` passes 2
tests, and `RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path
engine/Cargo.toml konclude_ht --lib` passes 1115 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W523 are `745 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `111 W4-DEFER`, `94 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W524 — PN-3 context-threaded lazy getter cluster

W524 reconciles PN-3's remaining node-owned lazy getter allocation stubs for
`getReapplyConceptLabelSet`, `getConnectionSuccessorSet`,
`getReapplyRoleSuccessorHash`, `getConceptPropagationBindingSetHash`,
`getConceptVariableBindingPathSetHash`,
`getConceptRepresentativePropagationSetHash`, `getConceptProcessingQueue`, and
`getDistinctHash`. New context-threaded PN-3 wrappers route the C++ create path
through the already-live `ProcessContext` arena helpers, while the old
no-context compatibility methods remain explicit ownership fallbacks.

The role and concept reapply iterator overloads also now have context-threaded
wrappers for the C++ `clearDynamicReapplyQueue && !mLocal` allocation branch.
The concept reapply wrapper returns the real `process::reapply_sat` condensed
iterator; the legacy no-context method keeps its placeholder return type.

Focused PN-3 coverage verifies that `create=false` does not allocate,
`create=true` allocates exactly once and updates the local/use fields, and that
the reapply iterator clear paths allocate their backing storage.

Validation after W524: focused filter `pn3_` passes 9 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1117 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W524 are `745 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `111 W4-DEFER`, `81 W2-DEFER`, `31 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W525 — SAT-1, PN-3, and LS-1 context-threaded reconciliation

W525 ports three disjoint Konclude-faithfulness gaps. SAT-1's arena-threaded
`initCopingIndividualSaturationProcessNode` now installs the copied-node
dependency linker on the source node, matching Konclude's
`indiNode->addCopyDependingIndividualNodeLinker(depCopyLinker)` tail. PN-3 now
has a context-threaded `isIndividualAncestor` companion that follows
`mAncestorLink` through the edge arena and compares source individual ids like
`CNodeEdge::isSourceIndividualID`; Unit 14 merge preference now uses that exact
route instead of the old compatibility stub.

LS-1 now exposes context-threaded shared-additional-map reads for the
`CReapplyConceptLabelSet` alias cases: additional-map size, cloned entry lookup,
content cloning for rebuild, label-set iterator snapshots, and reapply iterator
reads/clear paths can follow `Shared` aliases through `ProcessContext`. Legacy
arena-free methods remain explicit fallbacks.

Focused coverage verifies SAT-1 copy-dependency linker installation, PN-3
ancestor-edge source-id matching, and LS-1 shared additional-map size/rebuild,
iterator, and reapply-clear behavior.

Validation after W525: focused filter `sat1_` passes 37 tests, focused filter
`pn3_` passes 10 tests, focused filter `konclude_ht::process::ls1` passes 6
tests, and `RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path
engine/Cargo.toml konclude_ht --lib` passes 1123 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W525 are `746 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `111 W4-DEFER`, `71 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W526 — DEP-1 reuse-backend side fields

W526 reconciles the `CREUSEBACKENDEXPANSIONMODESDependencyNode` side fields that
Konclude clears and exposes separately from the generic non-deterministic branch
track points. The Rust `ReuseBackendModes` dependency variant now stores
`mFixedReuseDepTrackPoint`, `mPriorizedReuseDepTrackPoint`,
`mInvolvedIndividualIdLinker`, and `mAffectedIndividualIdLinker` explicitly.
The DEP-1 initializer clears all four fields like Konclude, DEP-1 exposes the
fixed/prioritized trackpoint getters/setters plus involved and affected linker
accessors, and the affected linker's atomic test-and-set is modelled as an
expected-slice compare before replacing the flattened vector.

The completion dependency factory and Unit 29's manual reuse-backend dependency
initializer now construct and clear the same fields, so the side-channel state is
not hidden behind `nd.branch_track_points`.

A DB-2 fan-out inspected `mLocExtendedConceptVector` and intentionally made no
code changes: faithful porting there needs real `ConceptVector` storage in
`ProcessContext` plus `referenceVector` behavior. The current Rust type is still
a zero-sized stub, so filling only `db2.rs` would invent behavior rather than
port Konclude.

Validation after W526: focused filter `dep1_` passes 8 tests, focused Unit 29 and
factory filters compile cleanly, and `RUSTFLAGS=-Awarnings cargo test --quiet
--manifest-path engine/Cargo.toml konclude_ht --lib` passes 1124 tests, 0
failed. `cargo fmt --manifest-path engine/Cargo.toml --check` passes, and
`git diff --check` passes. Current source marker counts after W526 are
`746 W6-DEFER`, `728 W3-DEFER`, `221 PORT-PENDING`, `111 W4-DEFER`,
`69 W2-DEFER`, `31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W527 — PN-1/SAT-1 cleanup and LS-1 descriptor-threaded routes

W527 reconciles three W2-era process gaps. PN-1's legacy constructor comment now
matches the already-live context-backed constructor: the Rust typed arenas are
the memory pool, so `mMemAllocMan` has no runtime allocator object to seed.

SAT-1 now ports `CReapplyConceptSaturationLabelSet::copyReapplyConceptSaturationLabelSet`
for the arena-threaded coping-node path. The copy helper preserves Konclude's
source-side flattening rule: when the source main hash is large enough, or
`tryFlatLabelCopy` is true with a non-empty main hash, the source main entries are
moved/merged into the source additional hash before the target copies the source's
resulting main/additional state.

LS-1 now has context-threaded descriptor/concept resolution routes for real
descriptor concept ids, concept tags, negation, and dependency track points. The
new `_in_context` variants cover concept presence checks, descriptor lookup,
descriptor-or-reapply lookup, and insert paths without relying on the legacy
arena-free shims that use descriptor ids as tags.

Validation after W527: focused filter `pn1_` passes 1 test, focused filter
`sat1_` passes 39 tests, focused filter `konclude_ht::process::ls1` passes 9
tests, and `RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path
engine/Cargo.toml konclude_ht --lib` passes 1129 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W527 are `746 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `111 W4-DEFER`, `65 W2-DEFER`,
`31 RECONCILE-NEED`, and `4 W8-DEFER`.

### W528 — Unit 9/15/17 and LS-1 targeted parity cleanup

W528 removes four stale or now-portable W2/reconcile boundaries and wires one
merge-driver side effect directly. Unit 9 no longer carries stale W2 wording for
the already-live context-threaded role-successor scan and real concept-tag
lookup in the ALL/IMPLICATION paths.

Unit 15 now propagates `PRFINVALIDBLOCKINGORCACHING` from the merged-away node to
the merge target during `mergeIndividualNodeInto` phase 9, matching Konclude's
post-prune flag propagation. A focused regression test covers the flag transfer.

Unit 17 now resolves `mergingData->getDependencyTrackPoint()` for backend-sync
visits through the live individual-merging hash: the merged node's nominal id is
used as the hash key, the callback receives the stored dependency track point,
and the old incoming track point remains the fallback when no merge data exists.

LS-1 now follows `Shared` additional-map aliases in the context-threaded
additional-map read/clone paths instead of treating shared aliases as absent.
This keeps the old arena-free fallbacks explicit while making the context-aware
paths match Konclude's raw shared-map pointer behavior.

Validation after W528: focused filter
`merge_individual_node_into_propagates_invalid_blocking_flag` passes 1 test,
focused filter
`visit_relevant_backend_sync_individuals_uses_merging_hash_dependency_track_point`
passes 1 test, focused filter `unit17_visit_relevant_backend_sync_individuals`
passes 2 tests, and focused filter `konclude_ht::process::ls1` passes 9 tests.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1131 tests, 0 failed. Targeted `rustfmt --check` on
the touched Rust files passes, and `git diff --check` passes. Current source
marker counts after W528 are `746 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `111 W4-DEFER`, `61 W2-DEFER`, `30 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W529 — Unit 15 distinct relocation and Unit 12 merge dependencies

W529 ports two merge-family slices that were previously marked reconcile-only.
Unit 15 phase 8 now allocates a real `DistinctEdge` when moving distinct
information from the merged-away node to the merge target. The relocated edge is
inserted into both the merge target's distinct hash and the counterpart
individual's distinct hash after removing the old reciprocal entry, matching the
Konclude `CDistinctEdge::initDistinctEdge` / `insertDistinctIndividual` sequence.

Unit 12 now wires the merge dependency wrappers whose factory pieces exist:
`createMERGEDLINKDependency`, `createMERGEDINDIVIDUALDependency`,
`createMERGEDependency`, and `createSAMEINDIVIDUALMERGEDependency` call the live
`ProcessContext` factory helpers. DEP-1 now has the corresponding merge
dependency initializers and focused tests for the DetLink track-point wiring. The
`MERGEPOSSIBLEINSTANCEINDIVIDUAL` wrapper remains explicitly deferred because the
Rust dependency node still lacks Konclude's separate `mMergingIndividualNode`
side payload.

Validation after W529: focused filter
`merge_individual_node_into_relocates_distinct_edges` passes 1 test, focused
filter `merge_individual_node_into_propagates_invalid_blocking_flag` passes 1
test, focused filter `dep1_` passes 9 tests, and focused filter `create_merge`
passes 3 tests. `RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path
engine/Cargo.toml konclude_ht --lib` passes 1135 tests, 0 failed. `cargo fmt
--manifest-path engine/Cargo.toml --check` passes, and `git diff --check`
passes. Current source marker counts after W529 are `746 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `111 W4-DEFER`, `61 W2-DEFER`,
`25 RECONCILE-NEED`, and `4 W8-DEFER`.

### W530 — Unit 15 exact-nominal copy and S08 status-flag reconcile

W530 wires Unit 15 phase 10 for exact nominal dependency tracking. When
`mConfExactNominalDependencyTracking` is enabled and both merge nodes are nominal,
`mergeIndividualNodeInto` now copies every successor-connected nominal id from
the merged-away node to the merge target and also adds the merged-away node's own
nominal individual id with Konclude's negative-id convention. The new regression
checks both inherited successor ids and the node's own nominal id.

SAT-1/S08 also reconciles the saturation status-flag boundary. SAT-1 now tests
the Konclude masks for `INDSATFLAGCLASHED`, `INDSATFLAGINSUFFICIENT`,
`INDSATFLAGINITIALIZED`, and `INDSATFLAGCOMPLETED`, and S08 records that the
status-flag masks/helpers are no longer a group-G blocker. The successor-data
parameter retyping marker remains because it still depends on the broader linked
role successor read/mutation surface.

Validation after W530: focused filter
`merge_individual_node_into_copies_exact_nominal_connections` passes 1 test,
focused Unit 15 distinct/flag filters still pass, focused filter `sat1_` passes
40 tests, and focused filter `s08` passes 17 tests.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1137 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W530 are `746 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `111 W4-DEFER`, `60 W2-DEFER`, `23 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W531 — Unit 12 merge-possible factory and Unit 15 assertion relocation

W531 wires the exact
`createMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode` path instead of leaving it
as a stale reconcile marker. The Rust dependency factory now allocates a
`DepKind::MergePossibleInstanceIndividual` non-deterministic node, initializes it
with the active branch node, merged-away process individual, and previous
dependency track point, and updates non-deterministic branching tags. Konclude's
`mergingIndi` parameter is intentionally accepted by the wrapper but not stored:
the upstream `CMERGEPOSSIBLEINSTANCEINDIVIDUALDependencyNode` init body also
does not read or store that argument.

Unit 15 phase 11 is also live for assertion-linker relocation during
`mergeIndividualNodeInto`. Role and reverse-role assertion heads are moved into
`AdditionalProcessRoleAssertionsLinker`; existing additional role/data assertion
chains are cloned with merged-individual dependencies; process-initializing
concept linkers and asserted data literal linkers are relocated. Unit 9's OR-rule
cached-disjunction guard now reads the live partial-processing restriction flags
for satisfiable/completion-graph cached nodes, and the stale Unit 12/15 reconcile
comments were removed.

Validation after W531: focused filter `dependency_factory` passes 2 tests,
focused filter `merge_individual_node_into` passes 4 tests, focused Unit 15
filter `merge_individual_node_into_relocates_assertion_linkers` passes 1 test,
and focused filter `u12` compiles with 0 matching tests.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1138 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W531 are `746 W6-DEFER`, `728 W3-DEFER`,
`221 PORT-PENDING`, `111 W4-DEFER`, `60 W2-DEFER`, `18 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W532 — Unit 15 stale blockers and S08 FUNCTIONAL merge subset

W532 reconciles Unit 15's merge-driver blocker text against APIs that have landed
since the original `mergeIndividualNodeInto` phase transcription. This is a
marker-accuracy wave, not a behavioral shortcut: phases 4, 5, 6, and 7 remain
deferred where their full Konclude control flow still depends on broader pieces.

The stale blockers removed were: the label-set iterator/contains/count surface
for phase 4, the pn3 role/disjoint-successor iterator surface for phase 5, the
`IndividualMergingHash` and nominal-node accessor surface for phase 6, and the
minimize-merging ancestor accessor surface for phase 7. The remaining blockers are
now stated as the actual missing pieces: full label-merge wiring, successor-role
hash backends plus the per-merge dependency-track-point hash, the condensed
reapply-queue drain, and the W6 backend-cache/datatype-handler pieces.

S08 also ports the previously deferred subset of
`collectLinkedSuccessorNodesFUNCTIONALConceptsMerging` that is now backed by live
satellite APIs: inverse-role resolution, linked successor lookup, active-count
guarding, functional forwarding-predecessor marking, copying successor
saturation labels to the ancestor, copy-dependency registration, preprocessing,
and extension/backward-propagation setup over creation-role linkers. The
remaining S08 group-G blocker is now the ATMOST mutating merge surface and
successor-data out-param/container typing, not status flags or the simple linked
successor read path.

Validation after W532: focused filter `merge_individual_node_into` passes 4
tests; focused filter `s08` passes 17 tests. `RUSTFLAGS=-Awarnings cargo test
--quiet --manifest-path engine/Cargo.toml konclude_ht --lib` passes 1138 tests,
0 failed. Current source marker counts after W532 are `746 W6-DEFER`,
`728 W3-DEFER`, `221 PORT-PENDING`, `108 W4-DEFER`, `59 W2-DEFER`,
`13 RECONCILE-NEED`, and `4 W8-DEFER`.

### W533 — Unit 6/7/33 reconcile cleanup and S08 subset/deactivation helpers

W533 removes stale representative/propagation-binding reconcile blockers from
Unit 6, Unit 7, and Unit 33 where the named APIs are now live. The
representative-propagation hash and set lookup, node role-successor hash,
concept-processing queue, grounding handler, u11 `hasCommonVariableBindings`, and
u11 `getJoinedVariableBindingPath` surfaces are no longer listed as missing. The
remaining Unit 33 blocker is the absent representative/propagation-binding
dependency-factory family; the remaining Unit 7 blockers are the answerer
adapter/steering controller and the u33/u34 propagation-binding emission
signature reconciliation.

S08 also ports another typed successor-data slice: the successor-data overload of
`isLinkedIndividualSuccessorNodeMergingSubset`, the explicit-node subset worker,
the creation-role subset helpers, the label-subset helper over saturation label
sets, and the link-deactivation scan over linked successor data. The remaining
S08 blocker is still the deeper ATMOST mutating merge containers and successor
data out-param plumbing, not the basic typed successor-data reads.

Validation after W533: focused filter `u06` compiles with 0 matching tests,
focused filter `u33` passes 4 tests, and focused filter `s08` passes 17 tests.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1138 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W533 are `746 W6-DEFER`, `727 W3-DEFER`,
`222 PORT-PENDING`, `107 W4-DEFER`, `59 W2-DEFER`, `4 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W534 — Final stale propagation-binding reconcile cleanup

W534 removes two stale reconcile blockers from Unit 33 and Unit 7. Unit 33 no
longer claims that the representative / propagation-binding dependency creators
are missing: the corresponding wrappers are live in Unit 28 and are already used
by Unit 33. The remaining limitation is narrower and correctly documented as the
opaque `CDependency*` additional-dependency base/back-edge representation at the
specific tail call sites. Unit 7 no longer claims that u33/u34
`propagate_initial/fresh_propagation_bindings` need retyping to
`PropagationBindingSetId`; those signatures are already typed. The real cycle-rule
blocker is now documented as the missing sorted dual-iteration accessor over
`CPropagationBindingMap`.

Validation after W534: focused filter `u07` compiles with 0 matching tests,
focused filter `u33` passes 4 tests, and focused filter `s08` passes 17 tests.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1138 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` passes, and `git diff --check` passes. Current source
marker counts after W534 are `746 W6-DEFER`, `727 W3-DEFER`,
`221 PORT-PENDING`, `107 W4-DEFER`, `59 W2-DEFER`, `2 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W535 — Propagation-binding dependency chains and S08 successor-data reconcile

W535 ports the non-successor propagation-binding dependency tail instead of
carrying the previous dependency track point. Unit 33/34 now type the C++
`CDependency* otherDependencies` parameter as the folded `DepLinkId` dependency
spine, null callers pass `DepLinkId::NONE`, and both non-successor
`propagateInitial/FreshPropagationBindings` paths call the live Unit 28
`create_propagate_binding_dependency` wrapper with the C++ predecessor track
point and additional-dependency chain. If dependency construction is disabled,
the port keeps the existing previous-track-point fallback.

The propagation-binding reapply-concept hash is also tightened to Konclude's
live map semantics: iterator `clear_reapply_descriptor` clears the stored hash
entry, and direct `takePropagationBindingReapplyConceptDescriptor` now mutates
the hash entry rather than clearing a copied value. The focused process tests
cover add/take/iterator/copy behavior over fresh intrusive descriptors.

S08 removes the stale successor-data out-param reconcile marker by typing the
safe `get_successor_link_simply_mergeable_cardinality_count` slice over
`SaturationSuccessorDataId` and the typed merge-cardinality/distinct containers.
The remaining S08 group-G boundary is the larger ATMOST mutating merge surface
and live reconnect/resolve integration, not this out-param typing.

Validation after W535: focused filter `u33` passes 4 tests, focused filter
`propagation_binding` passes 16 tests, focused filter `s08` passes 17 tests, and
fresh propagation-binding filter compiles with 0 matching tests.
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1138 tests, 0 failed. Current source marker counts
after W535 are `745 W6-DEFER`, `726 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W536 — Unit 20 blocking-candidate label-set descriptor lookup

W536 tightens Unit 20's anywhere-blocking candidate-hash rebuild to use the
context-threaded `containsConceptDescriptor` path. The live scan now resolves the
initialization descriptor through the descriptor arena and ontology concept tag,
instead of using the legacy LS-1 arena-free id-as-tag compatibility shim. This
matches Konclude's `containsConceptDescriptor` semantics when descriptor ids and
concept tags differ.

LS-1 now exposes the missing `contains_concept_descriptor_in_context` alias over
the already-live `has_concept_descriptor_in_context` implementation, and the new
Unit 20 regression forces a descriptor id / concept-tag mismatch to prove the
candidate is inserted into the hash and returned by
`get_blocking_individual_node_candidate_iterator`.

The remaining Unit 7 answerer `RECONCILE-NEED` was inspected in parallel and is
still a real blocker: the task-level answerer binding-propagation adapter exists
only as a marker and there is no typed answerer propagation steering controller
or arena/resolver yet.

Validation after W536: focused filter
`unit20_blocking_candidate_iterator_uses_descriptor_concept_tag` passes 1 test,
focused filter `unit20` passes 6 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1139 tests, 0 failed. Current source marker counts
after W536 are `745 W6-DEFER`, `726 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W537 — Unit 16 successor-backward nominal propagation

W537 ports the successor-backward-dependency branch of Unit 16's nominal
connection propagation onto the live successor topology. Both
`propagateIndividualNodeNominalConnectionFlagsToAncestors` and
`propagateIndividualNodeConnectedNominalToAncestors` now use the
context-threaded `has_successor_individual_node_in_context` check when deciding
whether a node listed in `mSuccessorIndiNodeBackwardDependencyLinker` is still a
real successor of the ancestor. The old node-only compatibility helper cannot
resolve the arena-backed successor-role hash and returned false for this branch.

The new regressions install a real role edge, add the successor to the
backward-dependency linker, and prove both propagation variants recurse through
that Konclude branch: one carries
`PRF_SUCCESSORNOMINALCONNECTION`, the other carries the connected nominal id.

Validation after W537: focused filters
`nominal_connection_flag_propagation_visits_successor_backward_dependencies`
and `connected_nominal_propagation_visits_successor_backward_dependencies` each
pass 1 test, focused filter `nominal_connection` passes 5 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1141 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W537 remain `745 W6-DEFER`, `726 W3-DEFER`,
`221 PORT-PENDING`, `106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and
`4 W8-DEFER`.

### W538 — Unit 16 nominal-aware label-set subset

W538 ports `isLabelConceptSubSetIgnoreNominals`'s deferred inner logic. The
direct-lookup branch now walks the live `CReapplyConceptLabelSetIterator`, uses
the context-resolved `containsConcept(..., &containedNegation)` equivalent, sets
`clashFlag` on opposite polarity, and ignores missing nominal concepts while
rejecting missing non-nominals.

The sorted merge-walk branch now mirrors Konclude's tag-ordered scan: advance
the super-set iterator while its concept tag is lower, compare polarity on tag
matches, set `clashFlag` for negation mismatches, and apply the same
missing-nominal exception. A small Rust guard handles an empty super iterator
without changing the intended missing-concept semantics.

New regressions force both branch choices. The direct-lookup test sets
`map_comparison_direct_lookup_factor = 1` and verifies missing nominals are
ignored while a polarity mismatch reports a clash. The merge-walk test uses the
default threshold and verifies the nominal exception plus rejection of a missing
atomic concept.

Validation after W538: focused filters
`label_subset_ignore_nominals_direct_lookup_ignores_nominals_and_reports_clash`
and `label_subset_ignore_nominals_merge_walk_ignores_nominals_and_rejects_missing_atoms`
each pass 1 test, focused filter `label_subset_ignore_nominals` passes 2 tests,
focused filter `nominal_connection` passes 5 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1143 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W538 are `742 W6-DEFER`, `726 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W539 — Unit 30 individual-node clash descriptor label-chain walk

W539 ports `createClashedIndividualNodeDescriptor`'s label-set walk over the
live `CReapplyConceptLabelSet::getAddingSortedConceptDescriptionLinker`
equivalent. The method no longer seeds `conDesIt` with `Id::NONE`; it resolves
the node's current reapply concept label set, obtains the adding-sorted concept
descriptor chain head, and walks `getNext()` while prepending one typed
`CClashedConceptDescriptor` per descriptor.

This matches Konclude cpp 4395-4405: `clashDes = prevClashes`,
`conSet = processIndi->getReapplyConceptLabelSet(false)`,
`conDesIt = conSet->getAddingSortedConceptDescriptionLinker()`, then
`createClashedConceptDescriptor(..., conDes->getDependencyTrackPoint(), ...)`
for each chain entry.

The regression seeds a two-descriptor label chain with distinct dependency track
points, installs it on the node, calls
`create_clashed_individual_node_descriptor`, and verifies the returned clash
chain contains both concept descriptors in Konclude prepend order with the
correct individual and dependency payloads.

Validation after W539: focused filter
`create_clashed_individual_node_descriptor_walks_adding_sorted_label_chain`
passes 1 test, focused filter `create_clashed` passes 5 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1144 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W539 are `741 W6-DEFER`, `726 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W540 — Unit 20 backend-neighbour critical concept-chain scan

W540 ports the descriptor-chain mechanics in
`testIndividualNodeBackendCacheNeighbourExpansionBlockingCritical`. The method
now obtains the node label set's adding-sorted descriptor head through the live
`getAddingSortedConceptDescriptionLinker` equivalent, walks `getNext()` until
the last-tested or last-synced cursor, calls the existing per-concept criticality
worker for each descriptor, and advances `newLastTestedConDes` to
`newLastTestedConDes->getNext()` after a critical descriptor.

The backend association completeness branch remains explicitly deferred; this
wave only ports the Konclude loop mechanics that are now backed by process
substrate. The regression installs a negated `SOME` descriptor as the chain head
with a second descriptor as its `next`, drives the neighbour-criticality method,
and verifies both the critical flag and the cursor advancement to the next
descriptor.

Validation after W540: focused filter
`unit20_backend_neighbour_criticality_walks_label_chain_and_advances_cursor`
passes 1 test, focused filter `unit20_backend_neighbour` passes 2 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1145 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W540 are `738 W6-DEFER`, `726 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W541 — Unit 30 label-set clash/subset comparison

W541 ports the label-set/label-set overload of `isLabelConceptClashSet`
(`cpp 17323-17391`). The direct-lookup branch now walks the live
`CReapplyConceptLabelSetIterator`, uses the context-resolved
`containsConcept(..., &containedNegation)` equivalent, returns true on opposite
polarity, and updates `subSetFlag` for missing non-nominals.

The sorted tag-merge branch now mirrors Konclude's merge walk: initialize the
super-set descriptor/tag cursor, advance while the super tag is lower, return
with `subSetFlag = false` if the super iterator is exhausted, detect polarity
clashes on matching tags, and apply the nominal-ignore exception only at the
Konclude `!conceptInSuperConSet` point.

New regressions force both branch choices. The direct-lookup test lowers
`map_comparison_direct_lookup_factor` and verifies both clash detection and
missing non-nominal subset reporting. The merge-walk test verifies the
non-exhausted nominal-miss exception, missing atom rejection, and polarity clash
detection.

Validation after W541: focused filters
`label_clash_set_direct_lookup_reports_clash_and_subset_miss` and
`label_clash_set_merge_walk_ignores_nominal_subset_miss_and_reports_clash` each
pass 1 test, focused filter `label_clash_set` passes 2 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1147 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W541 are `736 W6-DEFER`, `726 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W542 — Unit 4 processing-blocked reactivation drain

W542 ports the first concrete branch of
`searchReactivateIndividualsProcessedPropagated` (`cpp 19901-19956`). The
method now snapshots the node's processing-blocked individual linker, localizes
each blocked node, marks it with
`PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED`, and requeues it through the live
`addIndividualToProcessingQueue` path. The process layer now also exposes the
matching clear operation for the drained processing-blocked linker.

The successor/connection recursion in the same Konclude method remains
explicitly deferred; this wave only ports the processing-blocked linker drain
whose process substrate is now available. The regression verifies that both
blocked nodes are flagged and queued and that the source node's
processing-blocked linker is empty after traversal.

Validation after W542: focused filter
`unit04_search_reactivate_drains_processing_blocked_linker` passes 1 test,
focused filter `unit04` passes 1 test, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1148 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W542 are `736 W6-DEFER`, `722 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W543 — Unit 4 successor/connection reactivation scan

W543 ports the remaining successor/ancestor scan inside
`searchReactivateIndividualsProcessedPropagated` (`cpp 19901-19956`). The method
now reads the source node id and ancestor depth, snapshots the live successor
iterator, resolves each successor through `getSuccessorIndividual`, checks the
successor depth and `PRF_ANCESTORALLPROCESSED`, and scans the successor's
connection-successor ids through the up-to-date node-vector path.

When every relevant connected ancestor/nominal is already processing-completed
or ancestor-all-processed, the successor is localized, marked with
`PRF_ANCESTORALLPROCESSED`, and either requeued with
`PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED` if it is processing-blocked or
recursed into if it is already processing-completed. The only remaining boundary
inside this path is the broader deferred miss branch of
`getUpToDateIndividual(cint64)`, which still materializes temporary nominal
nodes outside this slice.

Validation after W543: focused filter `unit04_search_reactivate` passes 4 tests,
and `RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1151 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W543 are `736 W6-DEFER`, `708 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W544 — Unit 4 processed-state unpropagation

W544 ports the `propagateIndividualUnprocessed` bool-overload body
(`cpp 19968-19992`). The method now applies the cons-preparation gate,
tests and clears `PRF_PROCESSINGCOMPLETED`, checks
`PRF_ANCESTORALLPROCESSED`, snapshots the live successor iterator, resolves
successors through `getSuccessorIndividual`, compares ancestor depths, and
localizes/recurse-walks qualifying deeper successors.

The successor gate intentionally follows Konclude exactly: recursion happens
when the deeper successor does **not** have `PRF_ANCESTORALLPROCESSED`; the
localized successor then clears that flag and calls the cons-required overload.
This preserves the C++ branch as written rather than substituting the more
intuitive inverse condition.

Validation after W544: focused filter `unit04_propagate_unprocessed` passes 3
tests, focused filter `unit04` passes 7 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1154 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W544 are `736 W6-DEFER`, `698 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W545 — Unit 4 skip-AND concept insertion path

W545 ports `addConceptToIndividualSkipANDProcessing` (`cpp 26692-26722`) over
the same live substrate as Unit 36's primary `addConceptToIndividual` path. The
method now obtains the node's concept-processing queue and reapply label set,
allocates and initializes a real `CConceptDescriptor`, inserts it into the label
set through `insertConceptsToIndividualConceptSet`, updates insertion/contained
statistics, calls `addBlockingCoreConcept`, optionally marks the concept label
set modified, queues the concept through the skip-function preprocessing
overload, drains condensed reapply iterators, and releases contained duplicate
descriptors.

The `applyANDRule` member-function pointer remains represented by the existing
opaque rule-slot handle, but the descriptor/label/queue side effects of the
Konclude overload are now live. Regression coverage uses a processable OR
concept so the queue insertion path is exercised without depending on immediate
rule execution.

Validation after W545: focused filter `unit04_add_concept_skip` passes 3 tests,
focused filter `unit04` passes 10 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1157 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W545 are `736 W6-DEFER`, `690 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W546 — Unit 4 propagation descriptor batch routing

W546 ports the propagation-routing branches of both
`insertConceptProcessDescriptorToProcessingQueue` overloads (`cpp 27152-27179`).
The methods now resolve the process descriptor's concept, inspect Konclude's
operator flags, and route propagation concepts into the variable-binding concept
batch processing queue instead of the ordinary node concept queue. The
binding-count overload now distinguishes the `CCFS_PROPAGATION_ALL_TYPE |
CCFS_PROPAGATION_AND_TYPE` path from the general propagation path, matching
Konclude's call to `insertIndiviudalForBindingCount` versus
`insertIndiviudalForConcept`.

Existing PBIND/VARBIND regressions were updated to assert the exact split queue
behavior: non-propagation reapply descriptors remain in the node concept queue,
while propagation descriptors are drained from the variable-binding batch queue.

Validation after W546: focused filter
`unit04_insert_concept_process_descriptor` passes 2 tests, focused filter
`unit04` passes 12 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1159 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W546 are `736 W6-DEFER`, `680 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W547 — Unit 4 reinsert wrapper and blocked-node init guard

W547 ports the `addConceptToProcessingQueue(CConceptProcessDescriptor*)`
overload (`cpp 27278-27281`) and wires the already-ported
`isIndividualNodeProcessingBlocked` / `eliminiateBlockedIndividuals` guard into
`individualNodeInitializing` at the documented Konclude call point. The queue
wrapper now delegates to `CConceptProcessingQueue::reinsertConceptProcessDescriptor`
with the current process context, preserving the C++ take/reinsert path when
rule processing stops after a descriptor has already been popped. The Unit 3
initialization hook prevents directly blocked successors from draining their
concept queue again, which keeps the cyclic `A ⊑ ∃R.A` blocking regression
terminating under the faithful reinsert path.

Statistics remain macro-deferred like adjacent Unit 4 queue helpers. The
per-node cache/signature/backend setup in `initialNodeInitialize` and the
INQT cache/value-space/backend dispatch arms remain explicit Unit 3 deferrals.

Validation after W547: focused filter
`unit04_add_concept_to_processing_queue_reinsert` passes 2 tests, focused
filter `cyclic_tbox_exists_blocks` passes 1 test, focused filter `unit03`
passes 2 tests, focused filter `unit04` passes 14 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1161 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W547 are `736 W6-DEFER`, `679 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W548 — Unit 4 depth-oriented individual queueing

W548 ports the depth-oriented front branch of `addIndividualToProcessingQueue`
over live `CIndividualProcessNode` state. The method now reads
`isNominalIndividualNode`, `isExtendedQueueProcessing`, and `isProcessingQueued`
from the node instead of hard-coded placeholders; when deterministic expansion
preprocessing is enabled, it inspects the real concept-processing queue's next
priority before choosing the deterministic-expansion queue versus the regular
depth-first queue. Successful insertion now sets `setProcessingQueued(true)` at
Konclude's call point, so repeat calls do not duplicate the same node.

The non-depth blocked/cache/late-reactivation branch remains the next Unit 4
queueing boundary, along with the still-deferred data/assertion cursor checks in
`addIndividualToProcessingQueueBasedOnProcessingConcepts`.

Validation after W548: focused filter `unit04_add_individual_depth_oriented`
passes 4 tests, focused filter `unit04` passes 18 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1165 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W548 are `736 W6-DEFER`, `673 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W549 — Unit 4 immediate queueing from processing concepts

W549 ports the immediate-queue branch inside
`addIndividualToProcessingQueueBasedOnProcessingConcepts`. When a node has no
concept-processing queue, or when the still-deferred data/assertion cursor
checks eventually report pending assertion work, the method now follows
Konclude's guard: the current-node/no-current-queueing fast path reports an
insert without allocating a queue, otherwise the node's real
`isImmediatelyProcessingQueued` flag suppresses duplicates, successful insertion
sets `setImmediatelyProcessingQueued(true)`, and the node is inserted into the
live immediate processing queue.

The asserted data literal / assertion data cursor comparisons remain explicit
Unit 4 deferrals, so this wave validates the no-concept-queue arm that already
reaches the immediate-queue branch faithfully.

Validation after W549: focused filter `unit04_processing_concepts` passes 3
tests, focused filter `unit04` passes 21 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1168 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W549 are `736 W6-DEFER`, `670 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W550 — PN-3 connection-successor iterator wrapper

W550 adds the missing context-threaded PN-3 wrapper for
`CIndividualProcessNode::getConnectionSuccessorIterator`. The arena-free
compatibility method remains a safe empty fallback, while
`getConnectionSuccessorIteratorInContext` now delegates to the live
`ProcessContext::nodeConnectionSuccessorIterator` path and therefore iterates
the real `CConnectionSuccessorSet` substrate, including the single-ancestor-id
and promoted-set cases.

Validation after W550: focused filter `pn3_connection_successor_iterator`
passes 3 tests, focused filter `pn3` passes 15 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1171 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W550 remain `736 W6-DEFER`, `670 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W551 — Unit 18 reusing-blocker dereferences

W551 ports the remaining reusing-blocker dereferences in Unit 18 over the live
blocking expansion data substrate. `upgradeSignatureBlockingToIndividualReusing`
now reads the blocker individual from the signature-blocking expansion data
before calling `establishIndividualReusing`, and the reusing blocker follow
add/remove helpers now read the real blocker from
`CReusingIndividualNodeConceptExpansionData` instead of localizing `Id::NONE`.
Follower updates therefore target the actual blocker node and clear the blocked
node's following pointer on removal, matching the already-live signature-blocking
follow helpers.

Validation after W551: focused filter `reusing_blocker_following` passes 2
tests, focused filter `unit18` passes 2 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1173 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W551 are `733 W6-DEFER`, `670 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W552 — Unit 4 non-depth blocked individual queueing

W552 ports the non-depth branch of `addIndividualToProcessingQueue` over live
individual-node blocking, cache, retest, and queue flags. The method now reads
direct/indirect blocking, completion-graph cached state, ancestor satisfiable /
signature / saturation cached state, synchronized-backend successor expansion
blocking, and delayed-nominal queue state instead of hard-coded placeholders.
Retest and abolished flags now decide whether blocked/cached nodes are skipped
or requeued. Late blocking resolving sets and observes
`blockedReactivationProcessingQueued`; the non-late fallback sets and observes
`regularDepthProcessingQueued`.

Validation after W552: focused filter `unit04_add_individual_non_depth` passes
4 tests, focused filter `unit04` passes 25 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1177 tests, 0 failed. `cargo fmt --manifest-path
engine/Cargo.toml --check` and `git diff --check` pass. Current source marker
counts after W552 are `733 W6-DEFER`, `652 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W553 — Unit 18 signature-blocking candidate hash rebuild

W553 ports `rebuildSignatureBlockingCandidateHash` over the real
`CSignatureBlockingCandidateHash` arena. The method now snapshots the old
signature iterator, allocates a fresh candidate hash, resolves each candidate
individual through `getUpToDateIndividual`, filters candidates with the already
ported `isIndividualNodeValidBlocker`, inserts non-empty rebuilt candidate
chains with `insertSignatureBlockingCandidates`, and installs the fresh hash via
`CProcessingDataBox::setSignatureBlockingCandidateHash`.

The rebuilt chain keeps the existing port's head-front CLinker convention while
dropping invalid buckets entirely. The Unit 18 module note was also refreshed so
the already-ported signature-blocking hash/review/expansion data are no longer
described as zero-size placeholders.

Validation after W553: focused filter
`unit18_rebuild_signature_blocking_candidate_hash` passes 2 tests, focused
filter `unit18` passes 4 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1179 tests, 0 failed. Current source marker counts
after W553 are `730 W6-DEFER`, `652 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W554 — Unit 18/19 signature-blocking alternative data

W554 wires the already-ported `CBlockingAlternativeSignatureBlockingCandidateData`
into the blocking path instead of carrying it as an opaque `Cint64`. Units 18,
19, and 20 now use the real `BlockingAltDataId`; Unit 19's optimized-blocking
failure path allocates or updates the signature-blocking candidate alternative
with Konclude's weighted score, and Unit 18's `testAlternativeBlocked` reads the
candidate node from that data before establishing signature blocking.

This wave also removes several now-stale Unit 18 analyzed-expansion deferrals:
`establishIndividualNodeSignatureBlocking` and
`refreshIndividualNodeSignatureBlocking` read
`CIndividualNodeAnalizedConceptExpansionData::isInvalidBlocker`, refresh tests
the real analyzed expansion count against the last updated count, and
`updateSignatureBlockingConceptExpansion` uses the real expansion count when
setting its last-updated fields. The duplicate blocker-label count probes in the
signature-blocking search path now read the live reapply label set counts.

Validation after W554: focused filter `unit18` passes 6 tests, focused filter
`optimized_blocking_` passes 3 tests, focused filter `unit20` passes 7 tests,
and `RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1181 tests, 0 failed. Current source marker counts
after W554 are `719 W6-DEFER`, `652 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

### W555 — Unit 18 analyzed-expansion linker walk

W555 ports the main analyzed-expansion list traversal inside
`updateSignatureBlockingConceptExpansion`. The method now snapshots the real
`CIndividualNodeAnalizedConceptExpansionData` reverse linker chain, reads each
`CAnalizedConceptExpansionLinker` expansion descriptor and dependent descriptor
list, skips expansion concepts already present in the blocking label set via the
context-threaded containment check, and resolves dependency descriptors from the
blocking label set by concept tag with the context-threaded lookup. Dependency
negation mismatches or missing dependency descriptors skip that analyzed
expansion, matching Konclude's early-fail behavior for the item.

The dependency creation call sites remain in their original order. The remaining
reconciliation is the already-tagged dependency-link threading from the
connection dependencies into `createEXPANDEDDependency`; this wave deliberately
does not invent that chain shape.

Validation after W555: focused filter
`unit18_update_signature_blocking_expansion` passes 2 tests, focused filter
`unit18` passes 8 tests, and
`RUSTFLAGS=-Awarnings cargo test --quiet --manifest-path engine/Cargo.toml
konclude_ht --lib` passes 1183 tests, 0 failed. Current source marker counts
after W555 are `715 W6-DEFER`, `652 W3-DEFER`, `221 PORT-PENDING`,
`106 W4-DEFER`, `59 W2-DEFER`, `1 RECONCILE-NEED`, and `4 W8-DEFER`.

## Faithfulness deviations (tagged in-source as `KONCLUDE-PORT-NOTE[...]`)
- `[ownership]` raw pointers + memory pool → typed `Arena<T>`/`Id<T>` + watermark.
- `[exceptions]` `throw CCalculationClash/StopProcessing` → cooperative
  `CalcSignal` pending-signal on the context, drained at the loop boundary.
- Chronological backtrack stands in for dependency-directed backjump (next step 2).
- The role reapply queue is now live for role-keyed add/apply and edge-install
  iterator return, and the restricted role-iterator overload now attaches a real
  link restriction. The broader `∃`-rule still uses `ht_reapply_universal_restrictions`
  as a label-set scan stand-in for some edge-triggered paths; the inverse direction
  uses the ancestor link rather than an installed reverse edge.
- Classification still re-drives to a label-count fixpoint as a sound stand-in
  for the remaining edge-triggered reapply gaps.

## Commits this session (newest first)
```
c1e5e9a successor nodes drain - nested ∃ grows multi-node      (26 tests)
5751e72 SHIQ breadth + classification                          (24 tests)
b767ef1 ALC consistency complete - ∃/∀ + edges
527421c ALC propositional core (AND/OR/branch/unfold/clash)
dbe13ac rule engine drives - first inference over main loop
18c56fc FIRST RUN - port executes + produces verdicts
66abbb3 live processing-queue subsystem (inner drive loop)
a646ace main driver loop + merge/expansion satellites
7c7c07a checkpoint the compiling kernel
```
