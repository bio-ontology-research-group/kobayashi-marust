//! `completion::u25` — Caching / backend-cache / saturation family, batch
//! (port unit #25 of 36).
//!
//! Faithful port of the methods that the manifest (`01-completion-methods.md`,
//! "Unit 25") groups under the representative-memory backend-cache reuse /
//! synchronisation / expansion-queue feeding of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) per method are noted on each item.
//!
//! Methods (cpp order):
//!   * `canDelayRepresentativeNeighbourExpansion`                  [24645–24679]  (u24 left this for u25)
//!   * `delayingRepresentativeNeighbourExpansion`                  [24683–24700]  (u24 left this for u25)
//!   * the reuse-activation tail of
//!     `initializeIndividualNodeWithBackendCache`                  [22736–22771]  (shared by both call sites)
//!   * `prepareBackendIndividualFixedReuseExpansion`               [24889–24913]
//!   * `prepareBackendIndividualPrioritizedReuseExpansion`         [24916–25003]
//!   * `checkIndividualBackendExpansionReuseable`                  [25010–25086]
//!   * `reuseIndividualBackendExpansion`                           [25092–25373]
//!   * `testIndividualNodeBackendCacheConceptsSynchronization`     [26283–26362]
//!   * `validateBackendSynchronisationContinued`                   [26368–26407]
//!   * `isConceptUnsatisfiabilitySaturated`                        [26900–26921]
//!   * `addIndividualToBackendSynchronisationRetestQueue`          [27587–27596]
//!   * `addIndividualToBackendDirectInfluenceExpansionQueue`       [27598–27607]
//!   * `addIndividualToBackendIndirectCompatibilityExpansionQueue` [27609–27618]
//!   * `addIndividualToBackendReuseExpansionQueue`                 [27621–27630]
//!   * `addIndividualToBackendNeighbourExpansionQueue`             [27632–27641]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` out/in-out
//! pointer-references become `&mut NodeId`; a plain `CIndividualProcessNode*` value
//! parameter becomes `NodeId`; `bool&` out-params become `&mut bool`; a `CConcept*`
//! value parameter becomes `ConceptId` resolved against
//! `calc_alg_context.ontology_arenas()`. The per-test arenas are reached through the
//! context as `calc_alg_context.process_context()` / `_mut()`, the databox as
//! `calc_alg_context.processing_data_box{,_mut}()`.
//!
//! KONCLUDE-PORT-NOTE[api]: every not-yet-ported backend-cache class
//! (`CBackendNeighbourExpansionQueueDataLinker`,
//! `CPROCESSHASH<…, …LabelNeighbourExpansionData>`,
//! `CBackendRepresentativeMemoryLabelCacheItem`,
//! `CBackendRepresentativeMemoryCacheIndividualAssociationData`,
//! `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData` and its
//! `…LabelNeighbourExpansionData` satellite) appears in a faithful signature as an
//! opaque `Cint64` handle, the same convention u17/u23/u24 use for the
//! representative-memory backend-cache subsystem (the W6 Cache subtree).
//!
//! Backend-expansion REUSE is LIVE (Stage 9). `checkIndividualBackendExpansionReuseable`,
//! `reuseIndividualBackendExpansion` and the prioritized branching preparation run
//! against the typed native-ABox association (`NativeNominalBackendReplay`, projected
//! from `NativeAboxRepresentativeEntry`) instead of the unported W6 label cache items:
//! the recorded consistency model's merges, chosen disjuncts, neighbour links and
//! distinctions are replayed under ONE non-deterministic dependency track point, as
//! alternative 0 of a two-way in-process branch whose alternative 1 discards the reuse
//! and keeps the ordinary expansion. See `diagnostics/9540-konclude-trace/ANALYSIS.md`
//! "Stage 9" for the measurement that motivated it and the soundness invariants.
//!
//! ACTIVATION (Stage 10). Konclude activates the mechanism from exactly two
//! places, both funnelling into the activation tail of
//! `initializeIndividualNodeWithBackendCache` (cpp 22736-22771):
//!   * `getUpToDateIndividual(cint64)`, cpp 22524-22527 — the individual is
//!     MATERIALIZED for the first time in this task;
//!   * `initialNodeInitialize`, cpp 8713-8730 — the individual is actually TAKEN
//!     off a processing queue.
//! Stage 9 wired only the first (`u36::get_up_to_date_individual_by_id`), which a
//! RETAINED class job never takes: it inherits the whole ABox individual-node
//! vector by COW from the deterministic consistency base, so every lookup is a
//! HIT and no individual is ever materialized. That is why v49/v50 (job
//! `49443083`) measured the mechanism as behaviourally inert while 309910 branch
//! points still opened on retained nodes.
//! [`CompletionTaskHandleAlgorithm::activate_backend_individual_expansion_reuse`]
//! is the shared activation both sites now call; `u03::individual_node_initializing`
//! calls it from the second one, which is the only lazy access point a retained
//! job reaches, and the one that guarantees the node is actually
//! reached/influenced rather than merely resolved.
//!
//! Deferral landscape. Like u24, the REST of this unit is dominated by the
//! backend-cache subsystem that is NOT yet ported (W6 Cache subtree) plus the
//! saturation subsystem (W4): the synchronisation / delaying methods bottom out in the
//! per-node sync data, the association/label cache items, `mBackendCacheHandler`
//! visitors, and the saturation reference
//! linking. Those bodies are kept `// PORT-PENDING` with the faithful signature
//! and a structural transcription so a later wave fills them without re-reading the
//! source. The five `addIndividualTo*Queue` feeders ARE substrate-portable in their
//! decisive part — the per-node "already queued" flag guard that fixes the boolean
//! return — so that control flow is ported LIVE (direct access to the public node
//! flag field, since node.rs exposes no `is_/set_` wrapper for these and this unit
//! may write only `u25.rs`); only the databox queue getter + `insertIndiviudalProcessNode`
//! + `STATINC` are held `// W3-DEFER[api]` (process-layer queue stubs, no arena).
//! Logic is documented, never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::ConceptId;
use super::super::process::dependency::BranchTreeNode;
use super::super::process::node::IndividualProcessNode;
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::stubs::BackendSyncDataId;
use super::super::process::{BranchNodeId, ClashDescId, ConDescId, NodeId, SatNodeId, TrackPointId};
use super::algorithm::{BackendExpansionReuseBranch, BranchKind, OrBranchPoint};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Representative-neighbour-expansion delaying pair (cpp 24645–24700).
    // u24 (`queuedIndividualBackendNeighbourExpansion`) calls both of these as
    // "u25 (sibling)"; they live here.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::canDelayRepresentativeNeighbourExpansion`.
    /// cpp 24645–24679.
    ///
    /// For one queued neighbour-array expansion, decides whether the neighbour at
    /// `neighbourIndiId` should be (a) skipped because its nominal node already
    /// exists, (b) delayed because the label-representative expansion is already
    /// installed, (c) representatively expanded (label not yet fully scheduled), or
    /// (d) plainly expanded. It threads the per-label
    /// `…LabelNeighbourExpansionData` slot (allocated/initialised on first sight)
    /// back through `delayingLabelNeighbourExpansionData` and writes the
    /// `expansionDelaying` / `representativeExpansion` out-flags; it also bumps the
    /// matching representative-expansion statistic. Always returns `true`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `*&`/out-param
    /// `delayingLabelNeighbourExpansionData` becomes `&mut Cint64` (opaque backend
    /// handle); `expansionDelaying`/`representativeExpansion` become `&mut bool`.
    pub fn can_delay_representative_neighbour_expansion(
        &mut self,
        exp_indi_node: NodeId,
        backend_neighbour_exp_data_linker: Cint64,
        label_neighbour_exp_delay_data_hash: Cint64,
        expanding_label: Cint64,
        neighbour_ass_data: Cint64,
        array_pos: Cint64,
        last_cursor: Cint64,
        neighbour_indi_id: Cint64,
        delaying_label_neighbour_expansion_data: &mut Cint64,
        expansion_delaying: &mut bool,
        representative_expansion: &mut bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 24645–24679. Outline:
        //
        //   if labelNeighbourExpDelayDataHash:
        //     neighbourConSetLabel = neighbourAssData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
        //     if !expandingLabel || expandingLabel == neighbourConSetLabel:
        //       labelNeighbourExpansionData& = (*labelNeighbourExpDelayDataHash)[neighbourConSetLabel];
        //       delayingLabelNeighbourExpansionData = &labelNeighbourExpansionData;
        //       if labelNeighbourExpansionData.getNeighbourExpansionArrayId() < 0:
        //         labelNeighbourExpansionData.setNeighbourExpansionArrayId(arrayPos);
        //         labelNeighbourExpansionData.setConceptSetLabel(neighbourConSetLabel);
        //         labelNeighbourExpansionData.setExpandingIndividiaulNode(expIndiNode);
        //         labelNeighbourExpansionData.setExpandingQueueData(backendNeighbourExpDataLinker);
        //       if isNominalIndividualNodeAvailable(-neighbourIndiId, ctx):                 // u16 (sibling)
        //         expansionDelaying = false; representativeExpansion = false;
        //         ++mStatRepresentativeExpansionAlreadyExistingNeighbourIndividualCount;
        //       elif labelNeighbourExpansionData.isNeighbourLabelDelayedRepresentativeExpansion():
        //         expansionDelaying = true; representativeExpansion = false;
        //         ++mStatRepresentativeDelayedNeighbourIndividualExpansionCount;
        //       elif !labelNeighbourExpansionData.hasAllLabelNeighbourExpansionScheduled():
        //         expansionDelaying = false; representativeExpansion = true;
        //         ++mStatRepresentativeExpansionTryingNeighbourIndividualCount;
        //       else:
        //         expansionDelaying = false; representativeExpansion = false;
        //     else:
        //       expansionDelaying = true; representativeExpansion = false;
        //   return true;
        //
        // Held PORT-PENDING: `labelNeighbourExpDelayDataHash` /
        // `neighbourAssData->getLabelCacheEntry` /
        // `…LabelNeighbourExpansionData` are the not-yet-ported representative-memory
        // backend-cache classes (opaque `Cint64` here). The sibling
        // `is_nominal_individual_node_available` (u16) and the four stat counters
        // (`self.stat_representative_expansion_already_existing_neighbour_individual_count`
        // / `…_delayed_neighbour_individual_expansion_count` /
        // `…_expansion_trying_neighbour_individual_count`) become live on the
        // reconcile pass once the label-expansion data lands. The C++ ALWAYS returns
        // `true` (it never short-circuits the caller), so the faithful return is
        // `true` even while the body is deferred.
        let _ = (
            exp_indi_node,
            backend_neighbour_exp_data_linker,
            label_neighbour_exp_delay_data_hash,
            expanding_label,
            neighbour_ass_data,
            array_pos,
            last_cursor,
            neighbour_indi_id,
            &mut *delaying_label_neighbour_expansion_data,
            &mut *expansion_delaying,
            &mut *representative_expansion,
            calc_alg_context,
        );
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::delayingRepresentativeNeighbourExpansion`.
    /// cpp 24683–24700.
    ///
    /// The post-expansion bookkeeping companion of
    /// `can_delay_representative_neighbour_expansion`: if the neighbour was
    /// representatively expanded it records the representative-expanded individual on
    /// the label slot (and flags the node's sync data) once; if expansion is being
    /// delayed it remembers the cursor to resume from. Always returns `false`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `locBackendSyncData` /
    /// `labelNeighbourExpansionData` are opaque backend handles (`Cint64`).
    pub fn delaying_representative_neighbour_expansion(
        &mut self,
        loc_backend_sync_data: Cint64,
        expansion_delaying: bool,
        representative_expansion: bool,
        label_neighbour_expansion_data: Cint64,
        last_cursor: Cint64,
        neighbour_indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 24683–24700. Outline:
        //
        //   if labelNeighbourExpansionData:
        //     if representativeExpansion:
        //       ++mStatRepresentativeExpandedNeighbourIndividualCount;
        //       if !labelNeighbourExpansionData->isNeighbourLabelDelayedRepresentativeExpansion():
        //         labelNeighbourExpansionData->setNeighbourLabelDelayedRepresentativeExpansion(true);
        //         labelNeighbourExpansionData->setRepresentativeExpandedIndividual(neighbourIndiId);
        //         locBackendSyncData->setNeighbourLabelRepresentativeExpansion(true);
        //     if expansionDelaying:
        //       if labelNeighbourExpansionData->getNextLabelNeighbourExpansionIteratorCursor() < 0:
        //         labelNeighbourExpansionData->setNextLabelNeighbourExpansionIteratorCursor(lastCursor);
        //   return false;
        //
        // Held PORT-PENDING: the `…LabelNeighbourExpansionData` satellite and the
        // per-node `…BackendCacheSynchronisationData` are not yet ported; the stat
        // counter `self.stat_representative_expanded_neighbour_individual_count`
        // becomes live on the reconcile pass. The C++ ALWAYS returns `false`, so the
        // faithful return is `false`.
        let _ = (
            loc_backend_sync_data,
            expansion_delaying,
            representative_expansion,
            label_neighbour_expansion_data,
            last_cursor,
            neighbour_indi_id,
            calc_alg_context,
        );
        false
    }

    // =======================================================================
    // Backend-expansion-reuse ACTIVATION (cpp 22736-22771, the activation tail
    // of `initializeIndividualNodeWithBackendCache`), reached from BOTH of
    // Konclude's call sites:
    //   * `getUpToDateIndividual(cint64)`'s create path  (cpp 22524-22527) —
    //     `u36::get_up_to_date_individual_by_id`, an individual materialized
    //     for the first time in this task;
    //   * `initialNodeInitialize`                        (cpp 8713-8730) —
    //     `u03::individual_node_initializing`, an individual actually TAKEN off
    //     a processing queue. This is the site a retained class job needs, and
    //     the one Stage 9 left unwired.
    // =======================================================================

    /// Decide, once per individual per calculation job, whether the recorded
    /// consistency model of `indi_proc_node`'s ABox individual is adopted by
    /// putting the node on the backend-individual reuse-expansion queue.
    /// Returns `true` iff it was queued (the caller must then stop this
    /// individual's ordinary processing, see the timing note below).
    ///
    /// Faithful transcription of the activation tail (cpp 22736-22771):
    ///
    /// ```text
    /// if (indiAssData->isCompletelyHandled()):
    ///   hasReuseableElements = FULL_CONCEPT_SET_LABEL.hasNondeterministicElements()
    ///                       || NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL
    ///                       || NONDETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL
    ///                       || NONDETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL
    ///   reuse = mOptBackendExpansionReuse            // + the late-dynamic count arms
    ///   if (reuse && hasReuseableElements):
    ///     if (!mOptBackendExpansionReuse)
    ///       processingDataBox->setBackendIndividualLateReuseExpansionActivated(true);
    ///     addIndividualToBackendReuseExpansionQueue(indiNode, calcAlgContext);
    /// ```
    ///
    /// `replay.has_reusable_elements` is the projection of the four label
    /// probes and `association_present` (required by
    /// [`Self::native_association_tag`]) is `indiAssData != nullptr`; the
    /// bridge only sets `has_reusable_elements` for an entry that is
    /// `complete_for_precomputation`, which is `isCompletelyHandled`.
    ///
    /// KM-DEVIATION[activation]: Konclude's per-node one-shot is
    /// `!indiProcNode->isNominalIndividualRepresentativeBackendDataLoaded()`
    /// (cpp 8713) together with
    /// `!backendSyncData->isBackendConceptSetInitialized()` (cpp 8720). Both are
    /// COW-inherited (`CIndividualProcessNode.cpp:272/426`), and both are still
    /// `false` on a Konclude class job because that job's base is
    /// `statCalcTask->getRootTask()` — the consistency task as it stood at the
    /// FIRST non-deterministic fork, in which most ABox nodes had not been
    /// initialized yet. KM initializes every ABox individual EAGERLY before any
    /// fork (`bridge.rs::initialize_native_nominal_state_for_tags`), so on a KM
    /// retained base both bits are already set on all 198 roots and the literal
    /// guard can never fire again. The port therefore keeps the one-shot in
    /// [`Self::native_reuse_activated_individuals`], which is per ALGORITHM and
    /// hence per class job (`reset_classification_algorithm_on_retained_base`
    /// replaces the algorithm wholesale). Semantics are the same "at most one
    /// reuse decision per individual per job"; only the storage differs.
    ///
    /// KM-DEVIATION[fail-closed]: `reuse_replay_representable` is required in
    /// addition to Konclude's gates — a typed record the writer could not
    /// serialize exactly is DECLINED, never partially replayed.
    ///
    /// The activation is strictly LAZY: nothing here walks the association set,
    /// so an individual is decided only when a rule actually reached the node.
    /// The 198 retained roots of `ore_ont_9540` are NOT scheduled up front.
    pub(crate) fn activate_backend_individual_expansion_reuse(
        &mut self,
        indi_proc_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // Konclude's `mBackendCacheHandler` null check: without installed
        // associations there is nothing to reuse, and this runs for every node
        // taken off a queue on every route.
        if !self.conf_backend_expansion_reuse
            || self.native_nominal_backend_replay.is_empty()
            || calc_alg_context.has_pending_signal()
        {
            return false;
        }
        if indi_proc_node.is_none()
            || indi_proc_node.index() >= calc_alg_context.process_context().node_count()
        {
            return false;
        }
        // The C++ guard is `indiProcNode->getNominalIndividual() &&
        // !...->isFakeIndividual() && mBackendCacheHandler` (cpp 8713): only a
        // real ABox individual with a backend cache has an association.
        let Some(individual_tag) =
            self.native_nominal_tag_for_node(indi_proc_node, calc_alg_context)
        else {
            return false;
        };
        // The one-shot check comes FIRST: this runs for every nominal node taken
        // off any queue, and after the individual's single decision the whole
        // gate must cost one hash lookup (no record clone on the hot path).
        if self
            .native_reuse_activated_individuals
            .contains(&individual_tag)
        {
            self.native_reuse_activation_repeat_count += 1;
            return false;
        }
        // Read only the three gate bits — `NativeNominalBackendReplay` owns
        // several vectors and must not be cloned per processed node.
        let Some((association_present, has_reusable_elements, representable)) = self
            .native_nominal_backend_replay
            .get(&individual_tag)
            .map(|replay| {
                (
                    replay.association_present,
                    replay.has_reusable_elements,
                    replay.reuse_replay_representable,
                )
            })
        else {
            self.native_reuse_activation_no_record_count += 1;
            return false;
        };
        if !association_present {
            self.native_reuse_activation_no_record_count += 1;
            return false;
        }
        self.native_reuse_activation_reached_count += 1;
        self.native_reuse_activated_individuals
            .insert(individual_tag);
        if !has_reusable_elements {
            self.native_reuse_activation_no_elements_count += 1;
            return false;
        }
        if !representable {
            self.native_reuse_activation_unrepresentable_count += 1;
            return false;
        }
        // Already on the reuse path, or the two-way branch already chose its
        // discarding alternative for this node: re-queueing would either
        // duplicate the decision or overrule alternative 1.
        let node_flags_decided = {
            let node = calc_alg_context.process_context().node(indi_proc_node);
            node.backend_reuse_expansion_queued
                || node.has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_BACKENDEXPANSIONREUSEDISCARDED
                        | IndividualProcessNode::PRF_BACKENDEXPANSIONREUSINGINDIVIDUAL,
                )
        };
        let backend_sync_data = calc_alg_context
            .process_context()
            .node(indi_proc_node)
            .individual_backend_cache_synchronisation_data(false);
        let reuse_track_point_installed = backend_sync_data.is_some()
            && calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .get_backend_expansion_reuse_dependency_track_point()
                .is_some();
        if node_flags_decided || reuse_track_point_installed {
            self.native_reuse_activation_declined_state_count += 1;
            return false;
        }

        // if (!mOptBackendExpansionReuse)
        //   processingDataBox->setBackendIndividualLateReuseExpansionActivated(true);
        if !self.opt_backend_expansion_reuse {
            calc_alg_context
                .processing_data_box_mut()
                .set_backend_individual_late_reuse_expansion_activated(true);
            // cpp 783 re-derives `mOptBackendExpansionReuse` from that databox
            // flag at task start; the in-process drive derives it once per
            // `run_completion_on`, so the option is lifted here as well — u02's
            // Probes 18/19/34 (the reuse-modes preparation and the two queue
            // drains) are gated on it and must see it within THIS drive.
            self.opt_backend_expansion_reuse = true;
        }
        // addIndividualToBackendReuseExpansionQueue(indiNode, calcAlgContext);
        self.add_individual_to_backend_reuse_expansion_queue(indi_proc_node, calc_alg_context);
        self.native_reuse_activation_queued_count += 1;
        true
    }

    /// Is a reuse decision still PENDING on this node, i.e. is it sitting on the
    /// backend-individual reuse-expansion queue waiting for
    /// [`Self::handle_backend_expansion_reuse_queue_node`]?
    ///
    /// A pending node must not drain its own concept-processing queue: the whole
    /// point of the mechanism is that the recorded model is adopted (or
    /// explicitly discarded) BEFORE the individual opens its first disjunction.
    pub(crate) fn has_pending_backend_expansion_reuse(
        &self,
        indi_proc_node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        self.opt_backend_expansion_reuse
            && indi_proc_node.is_some()
            && indi_proc_node.index() < calc_alg_context.process_context().node_count()
            && calc_alg_context
                .process_context()
                .node(indi_proc_node)
                .backend_reuse_expansion_queued
    }

    // =======================================================================
    // Backend-individual reuse expansion preparation (cpp 24889–25003).
    // =======================================================================

    /// The `INQT_BACKENDEXPANSIONREUSE` arm of `individualNodeInitializing`
    /// (cpp 9119-9138), called from [`Self::individual_node_initializing`] (u03)
    /// BEFORE the individual's concept processing queue is drained.
    ///
    /// Returns `true` when the caller should continue processing this individual,
    /// `false` when it must stop — Konclude's prioritized preparation ends the task
    /// with `CCalculationStopProcessingException(true)` after forking, and the
    /// in-process equivalent re-queues the individual on the reuse queue under
    /// alternative 0's non-deterministic track point, so the very next
    /// `take_next_process_individual` picks it up again and reaches the replay with
    /// the track point already installed.
    pub(super) fn handle_backend_expansion_reuse_queue_node(
        &mut self,
        indi_proc_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        self.native_reuse_queue_drain_count += 1;
        // indiProcNode->setBackendReuseExpansionQueued(false);
        calc_alg_context
            .process_context_mut()
            .node_mut(indi_proc_node)
            .set_backend_reuse_expansion_queued(false);

        if calc_alg_context
            .process_context()
            .node(indi_proc_node)
            .has_purged_blocked_processing_restriction_flags()
        {
            return true;
        }

        let discarded = |ctx: &CalculationAlgorithmContextBase| {
            ctx.process_context()
                .node(indi_proc_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_BACKENDEXPANSIONREUSEDISCARDED,
                )
        };

        let reuse_track_point_installed = {
            let backend_sync_data = calc_alg_context
                .process_context()
                .node(indi_proc_node)
                .individual_backend_cache_synchronisation_data(false);
            backend_sync_data.is_some()
                && calc_alg_context
                    .process_context()
                    .backend_sync_data(backend_sync_data)
                    .get_backend_expansion_reuse_dependency_track_point()
                    .is_some()
        };

        if !discarded(calc_alg_context)
            && !reuse_track_point_installed
            && self.check_individual_backend_expansion_reuseable(indi_proc_node, calc_alg_context)
        {
            let exp_cont_data = calc_alg_context.backend_neighbour_expansion_controlling_data(true);
            let (fixed_mode, prioritized_mode) = {
                let data = calc_alg_context
                    .process_context()
                    .backend_neighbour_expansion_controlling_data(exp_cont_data);
                (
                    data.is_fixed_reuse_expansion_mode(),
                    data.is_prioritized_reuse_expansion_mode(),
                )
            };
            let mut node = indi_proc_node;
            if fixed_mode {
                self.prepare_backend_individual_fixed_reuse_expansion(&mut node, calc_alg_context);
            }
            if prioritized_mode {
                // Forks the two-way branch and re-queues under alternative 0; the C++
                // throws a stop-processing exception right after.
                if self.prepare_backend_individual_prioritized_reuse_expansion(
                    &mut node,
                    calc_alg_context,
                ) {
                    return false;
                }
            }
        }

        if !discarded(calc_alg_context) {
            self.reuse_individual_backend_expansion(indi_proc_node, calc_alg_context);
        }
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::prepareBackendIndividualFixedReuseExpansion`.
    /// cpp 24889–24913.
    ///
    /// In the fixed-reuse alternative: installs a `REUSEBACKENDFIXEDINDIVIDUALEXPANSION`
    /// non-deterministic dependency + branch track-point on a freshly localized copy
    /// of the node, flags it `PRFBACKENDEXPANSIONREUSINGINDIVIDUAL`, and stamps the
    /// localized backend sync data with the reuse track-point (the reuse expansion
    /// itself runs directly afterwards — clashes are not problematic here). Returns
    /// whether the reuse-modes dependency node was present.
    pub fn prepare_backend_individual_fixed_reuse_expansion(
        &mut self,
        indi_proc_node: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // expContData = ctx->getUsedProcessingDataBox()->getBackendNeighbourExpansionControllingData(true);
        let exp_cont_data = calc_alg_context.backend_neighbour_expansion_controlling_data(true);
        // reuseModesDepNode = expContData->getReuseModesDependencyNode();
        let reuse_modes_dep_node = calc_alg_context
            .process_context()
            .backend_neighbour_expansion_controlling_data(exp_cont_data)
            .get_reuse_modes_dependency_node();
        if reuse_modes_dep_node.is_some() {
            let reuse_continuing_dependency_track_point = calc_alg_context
                .process_context()
                .backend_neighbour_expansion_controlling_data(exp_cont_data)
                .get_reuse_continuing_dependency_track_point();
            // reuseDepNode = createREUSEBACKENDFIXEDINDIVIDUALEXPANSIONDependency(indiProcNode,
            //               expContData->getReuseContinuingDependencyTrackPoint(), ctx);
            let reuse_dep_node = self.create_reuse_backend_fixed_individual_expansion_dependency(
                indi_proc_node,
                reuse_continuing_dependency_track_point,
                calc_alg_context,
            );
            // newDependencyTrackPoint = createNonDeterministicDependencyTrackPointBranch(reuseDepNode, true, ctx);
            let new_dependency_track_point = self
                .create_non_deterministic_dependency_track_point_branch(
                    reuse_dep_node,
                    true,
                    calc_alg_context,
                );

            // newIndiProcNode = getLocalizedIndividual(indiProcNode, false, ctx);
            let new_indi_proc_node =
                self.get_localized_individual(*indi_proc_node, false, calc_alg_context);
            // newIndiProcNode->addProcessingRestrictionFlags(PRFBACKENDEXPANSIONREUSINGINDIVIDUAL);
            calc_alg_context
                .process_context_mut()
                .node_mut(new_indi_proc_node)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_BACKENDEXPANSIONREUSINGINDIVIDUAL,
                );
            // locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(newIndiProcNode, ctx);
            let loc_backend_sync_data = self
                .get_localized_individual_backend_cache_snychronisation_data(
                    new_indi_proc_node,
                    calc_alg_context,
                );
            calc_alg_context
                .process_context_mut()
                .backend_sync_data_mut(loc_backend_sync_data)
                .set_backend_expansion_reuse_dependency_track_point(new_dependency_track_point);
            // directly do reuse expansion here, clashes are not problematic
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::prepareBackendIndividualPrioritizedReuseExpansion`.
    /// cpp 24916–25003.
    ///
    /// In the prioritized-reuse alternative: forks two dependent branching tasks off
    /// a `REUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSION` dependency — task 0 is the
    /// fixed-reuse branch (localize, flag reusing, stamp reuse track-point, enqueue
    /// onto the backend-individual reuse-expansion queue), task 1 deactivates reuse
    /// (`PRFBACKENDEXPANSIONREUSEDISCARDED`) and enqueues onto the indirect-compatibility
    /// queue — sets each task's reuse priority, communicates the task creation, and
    /// aborts the current task with a stop-processing exception. Returns whether the
    /// reuse-modes dependency node was present.
    ///
    /// KONCLUDE-PORT-NOTE[exceptions]: the terminal `throw
    /// CCalculationStopProcessingException(true)` is control flow; in the port it
    /// becomes an early return once the task-fork machinery is wired.
    pub fn prepare_backend_individual_prioritized_reuse_expansion(
        &mut self,
        indi_proc_node: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // Faithful transcription of cpp 24916–25003. The branch-local task/context
        // split remains deferred, but the process-side dependency/flag/queue effects
        // for the two alternatives are live below.
        //
        //   expContData = ctx->getUsedProcessingDataBox()->getBackendNeighbourExpansionControllingData(true);
        //   reuseModesDepNode = expContData->getReuseModesDependencyNode();
        //   if reuseModesDepNode:
        //     processorContext  = ctx->getUsedTaskProcessorContext();
        //     processingDataBox = ctx->getUsedProcessingDataBox();
        //     taskCreationCount = 2;
        //     newTaskList = createDependendBranchingTaskList(taskCreationCount, ctx);                 // backtracking unit
        //     newTaskIt   = newTaskList;
        //     reuseDepNode = createREUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSIONDependency(indiProcNode,
        //                       expContData->getReuseContinuingDependencyTrackPoint(), ctx);          // dep unit
        //     for i in 0..taskCreationCount:
        //       newSatCalcTask = newTaskIt; fixedReusingAlternative = (i == 0);
        //       newProcessContext = newSatCalcTask->getProcessContext(processorContext);
        //       newCalcAlgContext = createCalculationAlgorithmContext(processorContext, newProcessContext, newSatCalcTask);  // core unit
        //       newAllocMemMan    = newCalcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        //       newProcessingDataBox = newSatCalcTask->getProcessingDataBox();
        //       if fixedReusingAlternative:
        //         newDependencyTrackPoint = createNonDeterministicDependencyTrackPointBranch(reuseDepNode, false, newCalcAlgContext);
        //         (re-fetch newProcessingDataBox / newProcessContext / newCalcAlgContext / newAllocMemMan)
        //         newProcessTagger = newCalcAlgContext->getUsedProcessTagger();
        //         newProcessTagger->incBranchingTag(); newProcessTagger->incLocalizationTag();
        //         newIndiProcNode = getLocalizedIndividual(indiProcNode, false, newCalcAlgContext);   // u17
        //         newIndiProcNode->addProcessingRestrictionFlags(PRFBACKENDEXPANSIONREUSINGINDIVIDUAL);
        //         locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(newIndiProcNode, calcAlgContext);  // u17
        //         locBackendSyncData->setBackendExpansionReuseDependencyTrackPoint(newDependencyTrackPoint);
        //         // add to reuse queue, don't do reuse expansion here in case of clashes
        //         newProcessingDataBox->getBackendIndividualReuseExpansionQueue(true)->insertIndiviudalProcessNode(newIndiProcNode);
        //         prepareBranchedTaskProcessing(newIndiProcNode, newSatCalcTask, newCalcAlgContext); // core unit
        //       else:
        //         newDependencyTrackPoint = createNonDeterministicDependencyTrackPointBranch(reuseDepNode, false, newCalcAlgContext);
        //         (re-fetch newProcessContext / newCalcAlgContext / newAllocMemMan)
        //         newIndiProcNode = getLocalizedIndividual(indiProcNode, false, newCalcAlgContext);   // u17
        //         newIndiProcNode->addProcessingRestrictionFlags(PRFBACKENDEXPANSIONREUSEDISCARDED);  // deactivate reuse
        //         newProcessingDataBox->getBackendIndirectCompatibilityExpansionQueue(true)->insertIndiviudalProcessNode(newIndiProcNode);
        //         prepareBranchedTaskProcessing(newIndiProcNode, newSatCalcTask, newCalcAlgContext);
        //       newTaskPriority = ctx->getUsedTaskPriorityStrategy()->getPriorityForTaskReusing(
        //                            newSatCalcTask, ctx->getUsedSatisfiableCalculationTask(), fixedReusingAlternative);
        //       newSatCalcTask->setTaskPriority(newTaskPriority);
        //       newTaskIt = newTaskIt->getNext();
        //     processorContext->getTaskProcessorCommunicator()->communicateTaskCreation(newTaskList);
        //     throw CCalculationStopProcessingException(true);   // [exceptions] -> early return once task-fork wired
        //   return false;
        //
        // KM-DEVIATION[branching]: KM has no Task/scheduler layer, so the two forked
        // child tasks become the two ALTERNATIVES of one in-process `OrBranchPoint`
        // (the same realisation `applyORRule` (u03) and the at-most merge/choose
        // rules (u08) use for their forks). Alternative 0 is the fixed-reusing
        // alternative, alternative 1 discards the reuse; the terminal
        // `CCalculationStopProcessingException(true)` becomes "this individual's
        // processing ends here" — the caller
        // (`individual_node_initializing`) returns early and the re-queued node is
        // picked up again from the reuse queue with its track point installed.
        //
        // W3-DEFER[task]: real dependent child task contexts, per-child process
        // tagger branch/localization increments, task priorities, scheduler
        // communication (`getPriorityForTaskReusing` / `communicateTaskCreation` /
        // `prepareBranchedTaskProcessing`).
        let exp_cont_data = calc_alg_context.backend_neighbour_expansion_controlling_data(true);
        let reuse_modes_dep_node = calc_alg_context
            .process_context()
            .backend_neighbour_expansion_controlling_data(exp_cont_data)
            .get_reuse_modes_dependency_node();
        if reuse_modes_dep_node.is_none() {
            return false;
        }

        let reuse_continuing_dependency_track_point = calc_alg_context
            .process_context()
            .backend_neighbour_expansion_controlling_data(exp_cont_data)
            .get_reuse_continuing_dependency_track_point();
        // reuseDepNode = createREUSEBACKENDPRIORITIZEDINDIVIDUALEXPANSIONDependency(
        //     indiProcNode, expContData->getReuseContinuingDependencyTrackPoint(), ctx);
        let reuse_dep_node = self.create_reuse_backend_prioritized_individual_expansion_dependency(
            indi_proc_node,
            reuse_continuing_dependency_track_point,
            calc_alg_context,
        );

        let individual_tag = self
            .native_nominal_tag_for_node(*indi_proc_node, calc_alg_context)
            .unwrap_or(INVALID);

        // --- the branch-tree spine + the two per-alternative non-deterministic
        //     dependency track points (Konclude's per-child-task
        //     `createNonDeterministicDependencyTrackPointBranch(reuseDepNode, false, …)`,
        //     minted UPFRONT for both alternatives so the tracked-clash analysis can
        //     read "every sibling of this reuse branch clashed"). ---
        let parent_used_branch_node = calc_alg_context.base.used_branch_tree_node;
        let parent_branch: BranchNodeId = self
            .or_branch_stack
            .last()
            .map(|bp| bp.branch_node)
            .unwrap_or(BranchNodeId::NONE);
        let root_branch: BranchNodeId = self
            .or_branch_stack
            .first()
            .map(|bp| bp.branch_node)
            .unwrap_or(BranchNodeId::NONE);
        let alt_track_points = self.ht_mint_alternative_track_points(
            reuse_dep_node,
            2,
            parent_used_branch_node,
            calc_alg_context,
        );
        let branch_node: BranchNodeId =
            calc_alg_context
                .process_context_mut()
                .alloc_branch_node(BranchTreeNode {
                    process_tag: 0,
                    parent_node: parent_branch,
                    root_node: root_branch,
                    branched_dep_track_point: Id::NONE,
                    sat_calc_task: INVALID,
                });
        let node_count_at_push = calc_alg_context.process_context().node_count();
        let first_alt_tp = alt_track_points.first().copied().unwrap_or(Id::NONE);

        // The reuse alternative merges, links and distinguishes across nodes; only an
        // epoch rollback can undo that, so this branch point ALWAYS owns an epoch
        // (the at-most merge precedent).
        calc_alg_context.push_branch_epoch();
        self.record_or_branch_open(*indi_proc_node, calc_alg_context);
        self.or_branch_stack.push(OrBranchPoint {
            node: *indi_proc_node,
            disjuncts: Vec::new(),
            alternative_order: Vec::new(),
            current_alt: 0,
            branching_concept: ConceptId::NONE,
            negate: false,
            next_alt: 1,
            dep_track_point: reuse_continuing_dependency_track_point,
            branch_node,
            or_dependency_node: reuse_dep_node,
            alt_track_points,
            parent_used_branch_node,
            node_label_snapshot: Default::default(),
            node_queue_snapshot: Default::default(),
            node_count_at_push,
            kind: BranchKind::BackendExpansionReuse(BackendExpansionReuseBranch {
                indi_node: *indi_proc_node,
                individual_tag,
            }),
            own_epoch: true,
        });

        // --- alternative 0: the fixed-reusing alternative (cpp 24950-24975). ---
        if first_alt_tp.is_some() {
            calc_alg_context.base.used_branch_tree_node = calc_alg_context
                .process_context()
                .track_point(first_alt_tp)
                .get_branch_node();
        }
        let new_indi_proc_node =
            self.enter_backend_expansion_reuse_alternative(*indi_proc_node, first_alt_tp, calc_alg_context);

        *indi_proc_node = new_indi_proc_node;
        self.native_reuse_branch_fork_count += 1;
        true
    }

    /// Alternative 0 of the reuse branch (cpp 24950-24975), shared by the initial
    /// push and — for symmetry of the record it writes — kept as one helper: localize
    /// the individual, flag it `PRFBACKENDEXPANSIONREUSINGINDIVIDUAL`, stamp
    /// `reuse_dependency_track_point` on its LOCALIZED backend-sync data, and re-queue
    /// it onto the backend-individual reuse-expansion queue.
    ///
    /// The stamped track point is the single non-deterministic anchor every write of
    /// [`Self::reuse_individual_backend_expansion`] hangs from. Passing `Id::NONE`
    /// (no dependency spine) therefore leaves the reuse INERT rather than replaying
    /// the recorded model deterministically.
    pub(super) fn enter_backend_expansion_reuse_alternative(
        &mut self,
        indi_proc_node: NodeId,
        reuse_dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let new_indi_proc_node =
            self.get_localized_individual(indi_proc_node, false, calc_alg_context);
        calc_alg_context
            .process_context_mut()
            .node_mut(new_indi_proc_node)
            .add_processing_restriction_flags(
                IndividualProcessNode::PRF_BACKENDEXPANSIONREUSINGINDIVIDUAL,
            );
        let loc_backend_sync_data = self
            .get_localized_individual_backend_cache_snychronisation_data(
                new_indi_proc_node,
                calc_alg_context,
            );
        calc_alg_context
            .process_context_mut()
            .backend_sync_data_mut(loc_backend_sync_data)
            .set_backend_expansion_reuse_dependency_track_point(reuse_dependency_track_point);
        // "add to reuse queue, don't do reuse expansion here in case of clashes"
        self.add_individual_to_backend_reuse_expansion_queue(new_indi_proc_node, calc_alg_context);
        new_indi_proc_node
    }

    /// Alternative 1 of the reuse branch (cpp 24977-24990): deactivate the reuse and
    /// let the ORDINARY expansion run on the individual.
    ///
    /// KM-DEVIATION[queue]: Konclude enqueues onto the backend
    /// indirect-compatibility expansion queue, whose drain (cpp 2743-2790, u02 Probe
    /// 36) is still `W3-DEFER[api]` here and would silently drop the node. The
    /// faithful enqueue is performed AND the node is additionally returned to the
    /// ordinary individual-processing queue, which is what Konclude's drain does with
    /// it once the indirect-compatibility expansion has run. Both feeders are
    /// flag-guarded, so a node already on either queue is not duplicated.
    pub(super) fn enter_backend_expansion_reuse_discard_alternative(
        &mut self,
        indi_proc_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let new_indi_proc_node =
            self.get_localized_individual(indi_proc_node, false, calc_alg_context);
        // set flag to deactivate reuse
        calc_alg_context
            .process_context_mut()
            .node_mut(new_indi_proc_node)
            .add_processing_restriction_flags(
                IndividualProcessNode::PRF_BACKENDEXPANSIONREUSEDISCARDED,
            );
        // add to indirect compatibility checking queue to ensure further expansion is
        // correctly handled
        self.add_individual_to_backend_indirect_compatibility_expansion_queue(
            new_indi_proc_node,
            calc_alg_context,
        );
        self.add_individual_to_processing_queue(new_indi_proc_node, calc_alg_context);
        new_indi_proc_node
    }

    // =======================================================================
    // Reuse reusability check + the reuse expansion itself (cpp 25010–25373).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::checkIndividualBackendExpansionReuseable`.
    /// cpp 25010–25086.
    ///
    /// Tests whether the node's backend-cached non-deterministic state can be reused:
    /// (a) no non-deterministic full-concept-set concept conflicts with the node's
    /// current label (a deterministically-present negation, or the negation already
    /// held, disables reuse), and (b) no non-deterministic different-individual is
    /// already deterministically merged into the node. On failure it flags the node
    /// `PRFBACKENDEXPANSIONREUSEDISCARDED`. Returns reusability.
    ///
    /// KM-BRIDGE STAGE 8/9: the gate of the replay in
    /// [`Self::reuse_individual_backend_expansion`]. LIVE against the typed
    /// native-ABox association (`NativeNominalBackendReplay`, itself projected
    /// from `NativeAboxRepresentativeEntry` by
    /// `bridge.rs::install_native_nominal_backend_replay`).
    ///
    /// Faithful transcription of cpp 25010–25086:
    ///
    /// ```text
    /// reusable = true;
    /// backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
    /// assocData = backendSyncData->getAssocitaionData();
    /// if assocData:
    ///   conLabel = assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
    ///   if conLabel && conLabel->hasNondeterministicElements():
    ///     conSetLabel = indiNode->getReapplyConceptLabelSet(false);
    ///     if conSetLabel:
    ///       visitConceptsOfAssociatedFullConceptSetLabel(assocData, conLabel,
    ///         |concept, negation, deterministic| {
    ///           if !deterministic:
    ///             if conSetLabel->getConceptDescriptor(concept, conDes, depTrackPoint):
    ///               if conDes->isNegated() != negation:
    ///                 if !hasNondeterministicDependency(depTrackPoint, ctx): reusable=false; return false;
    ///             if conSetLabel->hasConcept(concept, !negation): reusable=false; return false;
    ///           return true; }, false, true, ctx);
    ///   nonDetDiffIndiLabel = assocData->getLabelCacheEntry(NONDETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL);
    ///   detSameIndiLabel    = assocData->getLabelCacheEntry(DETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL);
    ///   if nonDetDiffIndiLabel:
    ///     mergedHash = indiNode->getIndividualMergingHash(false);
    ///     if mergedHash:
    ///       visitIndividualIdsOfAssociatedIndividualSetLabel(assocData, nonDetDiffIndiLabel,
    ///         |diffIndiId| {
    ///           mergingData = mergedHash->value(diffIndiId);
    ///           if diffIndiId != indiNode->getNominalIndividual()->getIndividualID()
    ///              && !hasIndividualIdsInAssociatedIndividualSetLabel(assocData, detSameIndiLabel, diffIndiId)
    ///              && mergingData.isMergedWithIndividual():
    ///             if !hasNondeterministicDependency(mergingData.getDependencyTrackPoint(), ctx): reusable=false; return false;
    ///           return true; }, ctx);
    /// if !reusable: indiNode->addProcessingRestrictionFlags(PRFBACKENDEXPANSIONREUSEDISCARDED);
    /// return reusable;
    /// ```
    ///
    /// KM-DEVIATION[fail-closed]: Konclude's representative cache is
    /// authoritative, so every label it reads is exact. The bridge's typed
    /// record marks a slot it could not serialize exactly as absent, and
    /// `reuse_replay_representable` is the conjunction of "all present". A
    /// record that is not fully representable is DECLINED here (rather than
    /// replayed with a silently dropped merge / link / distinction), which is
    /// the same outcome Konclude reaches by never queueing such an individual.
    pub fn check_individual_backend_expansion_reuseable(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut reusable = true;

        // backendSyncData->getAssocitaionData(): the typed association is the
        // replay record installed for this node's ABox individual.
        let assoc = self
            .native_association_tag(indi_node, calc_alg_context)
            .and_then(|tag| self.native_nominal_backend_replay.get(&tag).cloned());

        if let Some(replay) = assoc {
            if !replay.reuse_replay_representable {
                // KM-DEVIATION[fail-closed], see the doc comment.
                reusable = false;
            }

            // --- non-deterministic FULL_CONCEPT_SET values vs the current label ---
            if reusable && replay.cached_concept_values.iter().any(|v| !v.2) {
                let con_set_label = calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_node)
                    .get_reapply_concept_label_set(false);
                if con_set_label.is_some() {
                    for &(concept, negation, deterministic) in &replay.cached_concept_values {
                        if deterministic {
                            continue;
                        }
                        let mut con_des = ConDescId::NONE;
                        let mut dep_track_point = TrackPointId::NONE;
                        // KONCLUDE-PORT-NOTE[api]: `CReapplyConceptLabelSet` keys
                        // `mConceptDesDepMap` by `concept->getConceptTag()` (cpp
                        // CReapplyConceptLabelSet.cpp:165/189), so the lookup MUST go
                        // through the `_in_context` resolver. The bare
                        // `get_concept_descriptor` is the W2-DEFER shim that keys on
                        // `ConceptId::raw` and therefore never matches an inserted
                        // descriptor.
                        let present = {
                            let pc = calc_alg_context.process_context();
                            pc.label_set(con_set_label).get_concept_descriptor_in_context(
                                pc,
                                calc_alg_context.ontology_arenas(),
                                concept,
                                &mut con_des,
                                &mut dep_track_point,
                            )
                        };
                        if present {
                            let present_negated = calc_alg_context
                                .process_context()
                                .con_desc(con_des)
                                .is_negated();
                            if present_negated != negation {
                                // cpp 24996-25003. The negation of the cached value
                                // is already present; Konclude's comment says it
                                // disables the reuse only for a DETERMINISTIC
                                // dependency, "in order to ensure that
                                // problematic/involved individuals are correctly
                                // reported".
                                //
                                // KONCLUDE-PORT-NOTE[dead-branch]: that early-out
                                // changes nothing in practice, and the port keeps it
                                // only for structural fidelity. `mConceptDesDepMap`
                                // holds ONE descriptor per concept tag, so reaching
                                // here means `hasConcept(concept, !negation)` below
                                // is already true — the branch-dependent opposite is
                                // refused by that guard instead of this one. Do NOT
                                // "simplify" by dropping the guard below.
                                if !self.has_nondeterministic_dependency(
                                    dep_track_point,
                                    calc_alg_context,
                                ) {
                                    reusable = false;
                                    break;
                                }
                            }
                        }
                        // cpp 25005: `conSetLabel->hasConcept(concept, !negation)`.
                        // Same tag-resolution requirement as above; the bare
                        // `has_concept` shim additionally reads the descriptor
                        // polarity through `con_des_negated`, which is hard-wired to
                        // `false`.
                        let opposite_present = {
                            let pc = calc_alg_context.process_context();
                            pc.label_set(con_set_label).has_concept_in_context(
                                pc,
                                calc_alg_context.ontology_arenas(),
                                concept,
                                !negation,
                            )
                        };
                        if opposite_present {
                            reusable = false;
                            break;
                        }
                    }
                }
            }

            // --- non-deterministic different individuals vs existing merges ---
            if reusable && !replay.cached_nondeterministic_different_individuals.is_empty() {
                let merged_hash = calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .use_individual_merging_hash;
                if merged_hash.is_some() {
                    // indiNode->getNominalIndividual()->getIndividualID()
                    let own_tag = self.native_nominal_tag_for_node(indi_node, calc_alg_context);
                    for &diff_indi_id in &replay.cached_nondeterministic_different_individuals {
                        let merging_data = calc_alg_context
                            .process_context()
                            .individual_merging_hash(merged_hash)
                            .get(diff_indi_id)
                            .cloned()
                            .unwrap_or_default();
                        if Some(diff_indi_id) != own_tag
                            && !replay
                                .cached_deterministic_same_individuals
                                .contains(&diff_indi_id)
                            && merging_data.is_merged_with_individual()
                        {
                            if !self.has_nondeterministic_dependency(
                                merging_data.get_dependency_track_point(),
                                calc_alg_context,
                            ) {
                                reusable = false;
                                break;
                            }
                        }
                    }
                }
            }
        }

        if !reusable {
            self.native_reuse_check_decline_count += 1;
            calc_alg_context
                .process_context_mut()
                .node_mut(indi_node)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_BACKENDEXPANSIONREUSEDISCARDED,
                );
        } else {
            self.native_reuse_check_pass_count += 1;
        }
        reusable
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reuseIndividualBackendExpansion`.
    /// cpp 25092–25373.
    ///
    /// KM-BRIDGE STAGE 8/9 — the identified missing retained state, now PORTED.
    ///
    /// Konclude's class jobs start from the DETERMINISTIC consistency root
    /// (`consTaskData->getDeterministicSatisfiableTask()`), so the successful
    /// leaf's non-deterministic choices are not in the inherited graph — they
    /// are in the published backend associations, and THIS function is the only
    /// thing that puts them back. It replays four slots under ONE
    /// non-deterministic dependency track point
    /// (`getBackendExpansionReuseDependencyTrackPoint()`, installed by
    /// `prepareBackendIndividual{Fixed,Prioritized}ReuseExpansion`, cpp
    /// 25011–25110, as one alternative of a 2-way branch whose sibling discards
    /// the reuse):
    ///   1. `NONDETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL` — the model's merges;
    ///   2. the non-deterministic values of `FULL_CONCEPT_SET_LABEL` — the
    ///      model's CHOSEN DISJUNCTS;
    ///   3. `NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL` —
    ///      the model's non-deterministically created neighbour links;
    ///   4. `NONDETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL` — its distinctions.
    /// On ORE `ore_ont_9540` those slots are occupied on 86, 60 and 73 of the
    /// 198 associations respectively (`diagnostics/9540-konclude-trace/ANALYSIS.md`
    /// sections 4 and "Stage 8").
    ///
    /// KM's completion writeback ALREADY publishes all four
    /// (`bridge.rs::write_completed_native_representative_associations`, whose
    /// `NativeAboxConceptValue`/`NativeAboxRoleValue` carry the determinism bit,
    /// plus `nondeterministic_same_individuals` /
    /// `nondeterministic_different_individuals`), and
    /// `NativeNominalBackendReplay::cached_concept_values` carries them into
    /// each fresh task. `replay_native_representative_cache` filters to
    /// `value.deterministic`, which is correct on its own — that replay uses the
    /// BASE dependency track point, and replaying a model choice there would turn
    /// it into an entailment. The non-deterministic half needs THIS function's
    /// branch-alternative track point instead, and now gets it.
    ///
    /// LIVE against the typed native-ABox association.
    ///
    /// Materialises the reusable backend-cached non-deterministic state onto the
    /// (merged-into) node, once each: (1) merges all non-deterministic possibly-same
    /// individuals into the smallest representative id (clashes if not mergeable);
    /// (2) adds all non-deterministic full-concept-set concepts; (3) for every
    /// non-deterministic combined neighbour-instantiated role, creates the missing
    /// neighbour links (handling the inverse-role and merged-neighbour cases, under a
    /// `REUSEBACKENDVALUE` dependency), then re-queues the neighbour; (4) states all
    /// non-deterministic different individuals as distinct (clashes on a present
    /// merge). Returns `lazyNeighboursExpansionSucceded` (constant `true`).
    ///
    /// EVERY write here goes under `reuseExpDepTrackPoint` =
    /// `backendSyncData->getBackendExpansionReuseDependencyTrackPoint()`, the
    /// non-deterministic track point that
    /// [`Self::prepare_backend_individual_prioritized_reuse_expansion`] installed as
    /// alternative 0 of a two-way branch. The recorded model choices therefore enter
    /// the graph as one retractable assumption whose sibling alternative discards the
    /// reuse and expands normally — never as a deterministic consequence.
    ///
    /// KM-DEVIATION[fail-closed]: the replay is skipped entirely (returning `true`,
    /// the C++ constant result) unless BOTH
    ///   * the reuse dependency track point is present AND
    ///     `has_nondeterministic_dependency` holds for it, and
    ///   * the typed record is fully representable
    ///     (`NativeNominalBackendReplay::reuse_replay_representable`)
    /// hold. The first is the hard soundness invariant of this port: adding a model
    /// choice under the base dependency (or under a deterministic label entry) would
    /// publish a branch assumption as an entailment, which is exactly the failure the
    /// deterministic-only `replay_native_representative_cache` avoids. The second is
    /// the "a slot the writer could not serialize is unknown, not empty" rule.
    ///
    /// KONCLUDE-PORT-NOTE[exceptions]: the two
    /// `throw CCalculationClashProcessingException(clashDescriptors)` sites become
    /// `raise_clash` on the collected descriptors — the port's clash signal, which the
    /// drive loop routes into the same backtracking.
    ///
    /// W6-DEFER[api]: the `expandIndividualNeighbourNodeFromBackendCache` "ensure the
    /// deterministic links first" pre-pass (cpp 25209-25248) has no typed equivalent
    /// on this route: the deterministic neighbour edges of a native association are
    /// installed eagerly by `materialize_native_role_assertion_vectors` /
    /// `install_native_role_assertion_edge` when the node is materialised, and the
    /// per-neighbour `isNeighbourPossiblyInfluenced` bookkeeping it guards belongs to
    /// the unported neighbour-expansion-data hash. Its absence can only leave a
    /// deterministic edge uninstalled, which the ordinary expansion still derives;
    /// it cannot make the non-deterministic edge below wrong.
    pub fn reuse_individual_backend_expansion(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // bool lazyNeighboursExpansionSucceded = true;
        let lazy_neighbours_expansion_succeded = true;

        // locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);
        // backendSyncData = locBackendSyncData;
        let loc_backend_sync_data = self
            .get_localized_individual_backend_cache_snychronisation_data(
                indi_node,
                calc_alg_context,
            );

        // reuseExpDepTrackPoint = backendSyncData->getBackendExpansionReuseDependencyTrackPoint();
        let reuse_exp_dep_track_point = calc_alg_context
            .process_context()
            .backend_sync_data(loc_backend_sync_data)
            .get_backend_expansion_reuse_dependency_track_point();
        // KM-DEVIATION[fail-closed]: no non-deterministic reuse branch, no replay.
        if reuse_exp_dep_track_point.is_none()
            || !self.has_nondeterministic_dependency(reuse_exp_dep_track_point, calc_alg_context)
        {
            return lazy_neighbours_expansion_succeded;
        }

        // assocData = backendSyncData->getAssocitaionData();
        let Some(individual_tag) = self.native_association_tag(indi_node, calc_alg_context) else {
            return lazy_neighbours_expansion_succeded;
        };
        let Some(replay) = self
            .native_nominal_backend_replay
            .get(&individual_tag)
            .cloned()
        else {
            return lazy_neighbours_expansion_succeded;
        };
        if !replay.reuse_replay_representable {
            return lazy_neighbours_expansion_succeded;
        }
        self.native_reuse_replay_applied_count += 1;

        // ===================================================================
        // (1) merge all non-deterministic possibly-same individuals (cpp 25105-25133).
        // ===================================================================
        if !calc_alg_context
            .process_context()
            .backend_sync_data(loc_backend_sync_data)
            .has_reuse_non_deterministic_same_individual_merged()
            && !replay.cached_nondeterministic_same_individuals.is_empty()
        {
            // mergingIntoId = assocData->getRepresentativeSameIndividualId();
            // visit(...) { mergingIntoId = min(mergingIntoId, sameIndiId) }
            let mut merging_into_id = replay
                .cached_representative_same_individual_id
                .unwrap_or(individual_tag);
            for &same_indi_id in &replay.cached_nondeterministic_same_individuals {
                if same_indi_id < merging_into_id {
                    merging_into_id = same_indi_id;
                }
            }

            for &same_indi_id in &replay.cached_nondeterministic_same_individuals {
                if same_indi_id == merging_into_id {
                    continue;
                }
                if calc_alg_context.has_pending_signal() {
                    return lazy_neighbours_expansion_succeded;
                }
                // locMergingIntoIndiNode = getLocalizedForcedBackendInitializedNominalIndividualNode(mergingIntoId, ctx);
                let mut loc_merging_into_indi_node = self
                    .get_localized_forced_backend_initialized_nominal_individual_node_for_nominal_id(
                        merging_into_id,
                        calc_alg_context,
                    );
                if loc_merging_into_indi_node.is_none() {
                    continue;
                }
                if self.ht_merging_hash_contains(
                    loc_merging_into_indi_node,
                    same_indi_id,
                    calc_alg_context,
                ) {
                    continue;
                }
                // locMergingSameIndiNode = getLocalizedForcedBackendInitializedNominalIndividualNode(sameIndiId, ctx);
                let mut loc_merging_same_indi_node = self
                    .get_localized_forced_backend_initialized_nominal_individual_node_for_nominal_id(
                        same_indi_id,
                        calc_alg_context,
                    );
                if loc_merging_same_indi_node.is_none() {
                    continue;
                }
                // Konclude re-reads the merging hash: materialising the same-individual
                // node can itself have performed the merge.
                if self.ht_merging_hash_contains(
                    loc_merging_into_indi_node,
                    same_indi_id,
                    calc_alg_context,
                ) {
                    continue;
                }

                let mut clash_descriptors = ClashDescId::NONE;
                if self.ht_individuals_mergeable_with_clashes(
                    loc_merging_into_indi_node,
                    loc_merging_same_indi_node,
                    &mut clash_descriptors,
                    calc_alg_context,
                ) {
                    // mergingSameIndiDepTrackPoint = base continue TP, or the merging
                    // hash entry when the same-individual node is itself merged.
                    let mut merging_same_indi_dep_track_point =
                        calc_alg_context.get_or_create_base_dependency_track_point();
                    let same_node_id = calc_alg_context
                        .process_context()
                        .node(loc_merging_same_indi_node)
                        .individual_node_id();
                    if -same_indi_id != same_node_id {
                        // KONCLUDE-PORT-NOTE[api]: C++ uses
                        // `getIndividualMergingHash(true)` here, but only to READ the
                        // entry's dependency track point; the localized copy is
                        // content-identical to the used one, so the read goes through
                        // `mUseIndividualMergingHash` directly.
                        let hash = calc_alg_context
                            .process_context()
                            .node(loc_merging_same_indi_node)
                            .use_individual_merging_hash;
                        merging_same_indi_dep_track_point = if hash.is_some() {
                            calc_alg_context
                                .process_context()
                                .individual_merging_hash(hash)
                                .get(same_indi_id)
                                .map(|data| data.get_dependency_track_point())
                                .unwrap_or(TrackPointId::NONE)
                        } else {
                            TrackPointId::NONE
                        };
                    }

                    // createSAMEINDIVIDUALMERGEDependency(nextDepTrackPoint, into,
                    //     reuseExpDepTrackPoint, mergingSameIndiDepTrackPoint, ctx);
                    let mut next_dep_track_point = TrackPointId::NONE;
                    self.create_same_individual_merge_dependency(
                        &mut next_dep_track_point,
                        &mut loc_merging_into_indi_node,
                        reuse_exp_dep_track_point,
                        merging_same_indi_dep_track_point,
                        calc_alg_context,
                    );
                    if next_dep_track_point.is_none() {
                        // No dependency spine: the merge would land unattributed, and
                        // an unattributed merge is exactly a base-dependency write.
                        next_dep_track_point = reuse_exp_dep_track_point;
                    }
                    // locMergingIntoIndiNode = getMergedIndividualNodes(into, same, nextTP, ctx);
                    self.get_merged_individual_nodes(
                        &mut loc_merging_into_indi_node,
                        &mut loc_merging_same_indi_node,
                        next_dep_track_point,
                        calc_alg_context,
                    );
                } else {
                    // clashDescriptors = createClashedConceptDescriptor(clashDescriptors,
                    //     indiNode, nullptr, reuseExpDepTrackPoint, ctx);  [+ the two
                    //     merging-hash dependencies when either node is itself merged]
                    let mut clash_node = indi_node;
                    clash_descriptors = self.create_clashed_concept_descriptor(
                        clash_descriptors,
                        &mut clash_node,
                        ConDescId::NONE,
                        reuse_exp_dep_track_point,
                        calc_alg_context,
                    );
                    clash_descriptors = self.ht_reuse_merged_clash_descriptor(
                        clash_descriptors,
                        loc_merging_into_indi_node,
                        merging_into_id,
                        calc_alg_context,
                    );
                    clash_descriptors = self.ht_reuse_merged_clash_descriptor(
                        clash_descriptors,
                        loc_merging_same_indi_node,
                        same_indi_id,
                        calc_alg_context,
                    );
                    // throw CCalculationClashProcessingException(clashDescriptors);
                    calc_alg_context.raise_clash(clash_descriptors);
                    return lazy_neighbours_expansion_succeded;
                }
            }

            calc_alg_context
                .process_context_mut()
                .backend_sync_data_mut(loc_backend_sync_data)
                .set_reuse_non_deterministic_same_individual_merged(true);
        }

        // modifingIndiNode = getCorrectedMergedIntoIndividualNode(indiNode, ctx);
        let mut modifing_indi_node =
            self.get_corrected_merged_into_individual_node(indi_node, calc_alg_context);

        // ===================================================================
        // (2) add the non-deterministic FULL_CONCEPT_SET concepts (cpp 25140-25172):
        //     the recorded model's CHOSEN DISJUNCTS.
        // ===================================================================
        if !calc_alg_context
            .process_context()
            .backend_sync_data(loc_backend_sync_data)
            .has_reuse_non_deterministic_concepts_added()
        {
            for &(concept, negation, deterministic) in &replay.cached_concept_values {
                // if (!deterministic) addConceptToIndividual(concept, negation,
                //     modifingIndiNode, reuseExpDepTrackPoint, false, false, ctx);
                if deterministic {
                    continue;
                }
                self.add_concept_to_individual(
                    concept,
                    negation,
                    &mut modifing_indi_node,
                    reuse_exp_dep_track_point,
                    false,
                    false,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    break;
                }
            }
            calc_alg_context
                .process_context_mut()
                .backend_sync_data_mut(loc_backend_sync_data)
                .set_reuse_non_deterministic_concepts_added(true);
        }
        if calc_alg_context.has_pending_signal() {
            return lazy_neighbours_expansion_succeded;
        }

        // ===================================================================
        // (3) create the missing non-deterministic neighbour role links
        //     (cpp 25178-25292).
        // ===================================================================
        for &(neighbour_indi_id, role, inversed, deterministic) in &replay.cached_neighbour_roles {
            // if (nondeterministic && role && role->getRoleTag() > 1)
            if deterministic || role.is_none() {
                continue;
            }
            if calc_alg_context.ontology_arenas().role(role).get_role_tag() <= 1 {
                continue;
            }
            self.mark_individual_node_backend_non_concept_set_related_and_neighbour_label_related_processing(
                modifing_indi_node,
                calc_alg_context,
            );
            // if (isNominalIndividualNodeAvailable(-neighbourIndiId, ctx))
            if !self.is_nominal_individual_node_available(-neighbour_indi_id, calc_alg_context) {
                continue;
            }
            let neighbour_node =
                self.get_corrected_nominal_individual_node(-neighbour_indi_id, calc_alg_context);

            // requireLinkCreation: no neighbour node yet, or the (possibly inverse)
            // role link between the two is missing.
            let require_link_creation = if neighbour_node.is_none() {
                true
            } else if !inversed {
                !self.ht_reuse_has_role_link(
                    modifing_indi_node,
                    role,
                    neighbour_node,
                    true,
                    calc_alg_context,
                )
            } else {
                let inverse_role = calc_alg_context
                    .ontology_arenas()
                    .role(role)
                    .get_inverse_role();
                if inverse_role.is_some() {
                    !self.ht_reuse_has_role_link(
                        modifing_indi_node,
                        inverse_role,
                        neighbour_node,
                        true,
                        calc_alg_context,
                    )
                } else {
                    !self.ht_reuse_has_role_link(
                        neighbour_node,
                        inverse_role,
                        modifing_indi_node,
                        false,
                        calc_alg_context,
                    )
                }
            };
            if !require_link_creation {
                continue;
            }

            // locNeighbourNode = getLocalizedIndividual(neighbourNode, true, ctx);
            let loc_neighbour_node =
                self.get_localized_individual(neighbour_node, true, calc_alg_context);
            if loc_neighbour_node.is_none() {
                continue;
            }
            // nominalConDepTrackPoint = locNeighbourNode->getIndividualMergingHash(false)
            //     ->value(neighbourIndiId).getDependencyTrackPoint()   [when merged]
            let mut nominal_con_dep_track_point = TrackPointId::NONE;
            let loc_neighbour_node_id = calc_alg_context
                .process_context()
                .node(loc_neighbour_node)
                .individual_node_id();
            if -neighbour_indi_id != loc_neighbour_node_id {
                let hash = calc_alg_context
                    .process_context()
                    .node(loc_neighbour_node)
                    .use_individual_merging_hash;
                if hash.is_some() {
                    nominal_con_dep_track_point = calc_alg_context
                        .process_context()
                        .individual_merging_hash(hash)
                        .get(neighbour_indi_id)
                        .map(|data| data.get_dependency_track_point())
                        .unwrap_or(TrackPointId::NONE);
                }
            }

            // KM-DEVIATION[dependency]: Konclude picks `createVALUEDependency` when the
            // cached role value has `nominalLinkBase` (the link came from an ABox
            // assertion) and `createREUSEBACKENDVALUEDependency` otherwise. The typed
            // `NativeAboxRoleValue` carries no assertion-base bit, but an
            // assertion-based link is by construction DETERMINISTIC and therefore
            // never reaches this loop, so `REUSEBACKENDVALUE` is the exact arm here.
            let mut next_dep_track_point = TrackPointId::NONE;
            self.create_reuse_backend_value_dependency(
                &mut next_dep_track_point,
                &mut modifing_indi_node,
                ConDescId::NONE,
                reuse_exp_dep_track_point,
                nominal_con_dep_track_point,
                calc_alg_context,
            );
            if next_dep_track_point.is_none() {
                next_dep_track_point = reuse_exp_dep_track_point;
            }

            // createNewIndividualsLinksReapplyed(source, destination,
            //     role->getIndirectSuperRoleList(), role, nextDepTrackPoint, true, ctx);
            let mut super_roles = calc_alg_context
                .ontology_arenas()
                .role(role)
                .get_indirect_super_role_list()
                .to_vec();
            if !super_roles
                .iter()
                .any(|link| link.target == role && !link.negated)
            {
                super_roles.push(NegLink {
                    target: role,
                    negated: false,
                });
            }
            let (link_source, link_destination) = if !inversed {
                (modifing_indi_node, loc_neighbour_node)
            } else {
                (loc_neighbour_node, modifing_indi_node)
            };
            self.create_new_individuals_links_reapplyed(
                link_source,
                link_destination,
                &super_roles,
                role,
                next_dep_track_point,
                true,
                calc_alg_context,
            );

            // propagateIndividualNodeModified(locNeighbourNode, ctx);
            // addIndividualToProcessingQueue(locNeighbourNode, ctx);
            let mut propagated_neighbour = loc_neighbour_node;
            self.propagate_individual_node_modified(&mut propagated_neighbour, calc_alg_context);
            self.add_individual_to_processing_queue(loc_neighbour_node, calc_alg_context);
            if calc_alg_context.has_pending_signal() {
                return lazy_neighbours_expansion_succeded;
            }
        }

        // ===================================================================
        // (4) state the non-deterministic different individuals as distinct
        //     (cpp 25305-25340).
        // ===================================================================
        if !calc_alg_context
            .process_context()
            .backend_sync_data(loc_backend_sync_data)
            .has_reuse_non_deterministic_different_individual_stated()
            && !replay.cached_nondeterministic_different_individuals.is_empty()
        {
            let own_tag = self.native_nominal_tag_for_node(indi_node, calc_alg_context);
            for &diff_indi_id in &replay.cached_nondeterministic_different_individuals {
                // if (diffIndiId != nominalId && !hasIndividualIdsInAssociatedIndividualSetLabel(
                //         assocData, detSameIndiLabel, diffIndiId))
                if Some(diff_indi_id) == own_tag
                    || replay
                        .cached_deterministic_same_individuals
                        .contains(&diff_indi_id)
                {
                    continue;
                }
                let loc_different_indi_node = self
                    .get_localized_forced_backend_initialized_nominal_individual_node_for_nominal_id(
                        diff_indi_id,
                        calc_alg_context,
                    );
                if loc_different_indi_node.is_none() {
                    continue;
                }
                // corrIndiNode = getCorrectedMergedIntoIndividualNode(modifingIndiNode, ctx);
                let corr_indi_node = self
                    .get_corrected_merged_into_individual_node(modifing_indi_node, calc_alg_context);
                let merged_hash = calc_alg_context
                    .process_context()
                    .node(corr_indi_node)
                    .use_individual_merging_hash;
                let already_merged = merged_hash.is_some()
                    && calc_alg_context
                        .process_context()
                        .individual_merging_hash(merged_hash)
                        .has_merged_individual(diff_indi_id);
                if already_merged {
                    // The recorded model says "distinct", the current graph says
                    // "merged" — a clash of the reuse assumption against whatever
                    // justified the merge.
                    let merge_dep_track_point = calc_alg_context
                        .process_context()
                        .individual_merging_hash(merged_hash)
                        .get(diff_indi_id)
                        .map(|data| data.get_dependency_track_point())
                        .unwrap_or(TrackPointId::NONE);
                    let mut clash_descriptors = ClashDescId::NONE;
                    let mut different_for_clash = loc_different_indi_node;
                    clash_descriptors = self.create_clashed_concept_descriptor(
                        clash_descriptors,
                        &mut different_for_clash,
                        ConDescId::NONE,
                        reuse_exp_dep_track_point,
                        calc_alg_context,
                    );
                    let mut corr_for_clash = corr_indi_node;
                    clash_descriptors = self.create_clashed_concept_descriptor(
                        clash_descriptors,
                        &mut corr_for_clash,
                        ConDescId::NONE,
                        merge_dep_track_point,
                        calc_alg_context,
                    );
                    // throw CCalculationClashProcessingException(clashDescriptors);
                    calc_alg_context.raise_clash(clash_descriptors);
                    return lazy_neighbours_expansion_succeded;
                }
                // createIndividualsDistinct(corrIndiNode, locDifferentIndiNode,
                //     reuseExpDepTrackPoint, ctx);
                let mut distinct_source = corr_indi_node;
                let mut distinct_destination = loc_different_indi_node;
                self.create_individuals_distinct_pair(
                    &mut distinct_source,
                    &mut distinct_destination,
                    reuse_exp_dep_track_point,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    return lazy_neighbours_expansion_succeded;
                }
            }

            calc_alg_context
                .process_context_mut()
                .backend_sync_data_mut(loc_backend_sync_data)
                .set_reuse_non_deterministic_different_individual_stated(true);
        }

        lazy_neighbours_expansion_succeded
    }

    /// `locIndiNode->getIndividualMergingHash(false)` + `contains(id)` — the
    /// "is this individual already merged into that node" guard of cpp 25113/25119.
    fn ht_merging_hash_contains(
        &self,
        node: NodeId,
        individual_tag: Cint64,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let hash = calc_alg_context
            .process_context()
            .node(node)
            .use_individual_merging_hash;
        hash.is_some()
            && calc_alg_context
                .process_context()
                .individual_merging_hash(hash)
                .contains(individual_tag)
    }

    /// cpp 25146-25156: when the merge partner is itself a merged node, the clash
    /// explanation must carry the dependency that merged it.
    fn ht_reuse_merged_clash_descriptor(
        &mut self,
        clash_descriptors: ClashDescId,
        node: NodeId,
        individual_tag: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ClashDescId {
        let node_id = calc_alg_context
            .process_context()
            .node(node)
            .individual_node_id();
        if -individual_tag == node_id {
            return clash_descriptors;
        }
        // KONCLUDE-PORT-NOTE[api]: read-only use of `getIndividualMergingHash(true)`,
        // see the sibling note in the merge leg.
        let hash = calc_alg_context
            .process_context()
            .node(node)
            .use_individual_merging_hash;
        let dep_track_point = if hash.is_some() {
            calc_alg_context
                .process_context()
                .individual_merging_hash(hash)
                .get(individual_tag)
                .map(|data| data.get_dependency_track_point())
                .unwrap_or(TrackPointId::NONE)
        } else {
            TrackPointId::NONE
        };
        let mut node_for_clash = node;
        self.create_clashed_concept_descriptor(
            clash_descriptors,
            &mut node_for_clash,
            ConDescId::NONE,
            dep_track_point,
            calc_alg_context,
        )
    }

    /// `indiNode->getRoleSuccessorToIndividualLink(role, other, locateable)` — the
    /// link-presence probe of cpp 25188-25204. A `NONE` role (the missing-inverse
    /// arm) can have no link.
    fn ht_reuse_has_role_link(
        &mut self,
        source: NodeId,
        role: super::super::model::RoleId,
        destination: NodeId,
        locateable: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if source.is_none() || destination.is_none() || role.is_none() {
            return false;
        }
        let mut source_ref = source;
        let mut destination_ref = destination;
        self.has_individuals_link(
            &mut source_ref,
            &mut destination_ref,
            role,
            locateable,
            calc_alg_context,
        )
    }

    // =======================================================================
    // Backend-cache concept synchronisation tests (cpp 26283–26407).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testIndividualNodeBackendCacheConceptsSynchronization`.
    /// cpp 26283–26362.
    ///
    /// Re-checks whether the node is still fully synchronised with its backend-cached
    /// association: it requires a completely-handled association, that every newly
    /// merged deterministic representative shares the same full-concept-set label,
    /// and that every newly added (non-nominal) concept descriptor is present in the
    /// associated full-concept-set label (respecting determinism). It advances the
    /// last-tested-merged / last-tested-concept cursors and, on desync, clears the
    /// node's `backendCacheSynchron` flag. Returns the synchronisation verdict.
    pub fn test_individual_node_backend_cache_concepts_synchronization(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // Faithful transcription of cpp 26283–26362. The live process-side
        // backend-sync state is wired below; W6 cache association/label semantics
        // are still held at their exact Konclude call sites.
        //
        //   backendSynched = true;
        //   backendSyncData    = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //   locBackendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(true);
        //   if backendSyncData && backendSyncData->isBackendCacheSynchron():
        //     assocData = backendSyncData->getAssocitaionData();
        //     if !assocData || !assocData->isCompletelyHandled():
        //       backendSynched = false;
        //     else:
        //       conceptLabelItem = assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
        //       testIndividualNodeBackendCacheNewMergings(indiNode, ctx);                              // merge unit
        //       backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);
        //       if mergedLinker != lastSynchronizedConceptsTestedMergedNodeLinker:
        //         visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(indiNode,
        //             mergedLinker, lastSynchronizedConceptsTestedMergedNodeLinker, false,
        //             |base, locNode, backSyncTP| {
        //               mergedAssocData = locNode->getIndividualBackendCacheSynchronisationData(false)->getAssocitaionData();
        //               if mergedAssocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL) != conceptLabelItem: backendSynched=false;
        //               return false; }, ctx);
        //         locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);  // u17
        //         locBackendSyncData->setLastSynchronizedConceptsTestedMergedNodeLinker(mergedLinker);
        //       lastTestedConDes = backendSyncData->getLastSynchronizationTestedConceptDescriptor();
        //       conSet = indiNode->getReapplyConceptLabelSet(false);
        //       if conSet && backendSynched:
        //         conDesLinker = conSet->getAddingSortedConceptDescriptionLinker();
        //         if conDesLinker != lastTestedConDes:
        //           nominalConcept = indiNode->getNominalIndividual()->getIndividualNominalConcept();
        //           lastSyncConDes = lastTestedConDes;
        //           for conDesIt = conDesLinker; conDesIt && conDesIt != lastTestedConDes; conDesIt = conDesIt->getNext():
        //             if conDesIt->getConcept() != nominalConcept || conDesIt->isNegated():
        //               nondeterministic = hasNondeterministicDependency(conDesIt->getDependencyTrackPoint(), ctx);
        //               if !mBackendCacheHandler || !mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel(
        //                       assocData, conceptLabelItem, conDesIt->getConcept(), conDesIt->isNegated(), !nondeterministic, ctx):
        //                 backendSynched=false; lastSyncConDes=conDesIt;
        //           if !backendSynched && lastSyncConDes: lastSyncConDes = lastSyncConDes->getNext();
        //           locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);  // u17
        //           locBackendSyncData->setLastSynchronizationTestedConceptDescriptor(conDesLinker);
        //           locBackendSyncData->setLastSynchedConceptDescriptor(lastSyncConDes);
        //       else: backendSynched = false;
        //     if !backendSynched:
        //       locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);  // u17
        //       locBackendSyncData->setBackendCacheSynchron(backendSynched);
        //   else: backendSynched = false;
        //   return backendSynched;
        //
        // Held W6-DEFER[api]: assocData->isCompletelyHandled(),
        // assocData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL), the backend
        // cache-handler concept-membership query, nominal-concept filtering, and
        // the newly-merged deterministic representative visitor's association
        // label comparison. NB the C++ has a dead duplicated `return backendSynched;`.
        let mut backend_synched = true;
        let mut backend_sync_data = calc_alg_context
            .process_context()
            .node(indi_node)
            .individual_backend_cache_synchronisation_data(false);

        if backend_sync_data.is_some()
            && calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .is_backend_cache_synchron()
        {
            let assoc_data = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .get_associtaion_data();
            if assoc_data.is_none() {
                backend_synched = false;
            } else {
                // W6-DEFER[api]: assocData->isCompletelyHandled() and the
                // FULL_CONCEPT_SET_LABEL cache item read.
                self.test_individual_node_backend_cache_new_mergings(indi_node, calc_alg_context);
                backend_sync_data = calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .individual_backend_cache_synchronisation_data(false);

                let (merged_linker, last_synchronized_merged_linker) = {
                    let sync_data = calc_alg_context
                        .process_context()
                        .backend_sync_data(backend_sync_data);
                    (
                        sync_data.get_merged_individual_node_linker().to_vec(),
                        sync_data
                            .get_last_synchronized_concepts_tested_merged_node_linker()
                            .to_vec(),
                    )
                };
                if merged_linker != last_synchronized_merged_linker {
                    // W6-DEFER[api]: visitNewlyMergedOnlyDeterministicRepresentativeIndividualsBackendSynchronisationData(...)
                    // and merged association full-concept-label equality check.
                    let loc_backend_sync_data = self
                        .get_localized_individual_backend_cache_snychronisation_data(
                            indi_node,
                            calc_alg_context,
                        );
                    calc_alg_context
                        .process_context_mut()
                        .backend_sync_data_mut(loc_backend_sync_data)
                        .set_last_synchronized_concepts_tested_merged_node_linker(merged_linker);
                    backend_sync_data = loc_backend_sync_data;
                }

                let last_tested_con_des = calc_alg_context
                    .process_context()
                    .backend_sync_data(backend_sync_data)
                    .get_last_synchronization_tested_concept_descriptor();
                let con_set = calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_node)
                    .get_reapply_concept_label_set(false);
                if con_set.is_some() && backend_synched {
                    let con_des_linker = calc_alg_context
                        .process_context()
                        .label_set(con_set)
                        .get_adding_sorted_concept_description_linker();
                    if con_des_linker != last_tested_con_des {
                        // W6-DEFER[api]: nominalConcept lookup, exact descriptor-chain
                        // scan, nondeterminism test, and
                        // mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel(...).
                        // Until that query is live, preserve Konclude's cursor writes
                        // at this update point over the real backend-sync object.
                        let loc_backend_sync_data = self
                            .get_localized_individual_backend_cache_snychronisation_data(
                                indi_node,
                                calc_alg_context,
                            );
                        calc_alg_context
                            .process_context_mut()
                            .backend_sync_data_mut(loc_backend_sync_data)
                            .set_last_synchronization_tested_concept_descriptor(con_des_linker)
                            .set_last_synched_concept_descriptor(con_des_linker);
                        backend_sync_data = loc_backend_sync_data;
                    }
                } else {
                    backend_synched = false;
                }
            }
            if !backend_synched {
                let loc_backend_sync_data = self
                    .get_localized_individual_backend_cache_snychronisation_data(
                        indi_node,
                        calc_alg_context,
                    );
                calc_alg_context
                    .process_context_mut()
                    .backend_sync_data_mut(loc_backend_sync_data)
                    .set_backend_cache_synchron(backend_synched);
            }
        } else {
            backend_synched = false;
        }
        backend_synched
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::validateBackendSynchronisationContinued`.
    /// cpp 26368–26407.
    ///
    /// The incremental counterpart of the full re-check above, run right after a
    /// concept was added: from the last-synchronisation-tested descriptor it walks
    /// the newly added (non-nominal) concept descriptors (skipping the just-added one)
    /// and confirms each is present in the associated full-concept-set label; it
    /// advances the last-synched / last-tested cursors and writes the
    /// `backendCacheSynchron` flag. Returns the (continued) synchronisation verdict.
    ///
    /// KONCLUDE-PORT-NOTE[api]: backend-sync state and label-set head access are
    /// live. The backend-cache-handler membership query and the exact descriptor
    /// chain scan remain deferred.
    pub fn validate_backend_synchronisation_continued(
        &mut self,
        indi: NodeId,
        backend_sync_data: BackendSyncDataId,
        added_concept: ConceptId,
        added_concept_negation: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut backend_synched = true;
        if backend_sync_data.is_some()
            && calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .is_backend_cache_synchron()
        {
            let last_tested_con_des = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .get_last_synchronization_tested_concept_descriptor();
            let con_set = calc_alg_context
                .process_context_mut()
                .node_mut(indi)
                .get_reapply_concept_label_set(false);
            let assoc_data = calc_alg_context
                .process_context()
                .backend_sync_data(backend_sync_data)
                .get_associtaion_data();
            if con_set.is_some() && assoc_data.is_some() {
                let con_des_linker = calc_alg_context
                    .process_context()
                    .label_set(con_set)
                    .get_adding_sorted_concept_description_linker();
                let mut con_des_it: ConDescId = con_des_linker;
                if added_concept.is_some()
                    && con_des_it.is_some()
                    && con_des_it != last_tested_con_des
                {
                    if calc_alg_context
                        .process_context()
                        .con_desc(con_des_it)
                        .get_concept()
                        == added_concept
                        || calc_alg_context
                            .process_context()
                            .con_desc(con_des_it)
                            .is_negated()
                            == added_concept_negation
                    {
                        con_des_it = calc_alg_context.process_context().con_desc(con_des_it).next;
                    }
                }

                // W6-DEFER[api]: nominalConcept lookup, exact con-descriptor chain scan,
                // and mBackendCacheHandler->hasConceptInAssociatedFullConceptSetLabel(...).
                // With the cache-membership query still deferred, preserve the cursor
                // writes over the live backend-sync object at Konclude's update points.
                if backend_synched {
                    calc_alg_context
                        .process_context_mut()
                        .backend_sync_data_mut(backend_sync_data)
                        .set_last_synched_concept_descriptor(con_des_it);
                }
                calc_alg_context
                    .process_context_mut()
                    .backend_sync_data_mut(backend_sync_data)
                    .set_last_synchronization_tested_concept_descriptor(con_des_linker);
            } else {
                backend_synched = false;
            }
            calc_alg_context
                .process_context_mut()
                .backend_sync_data_mut(backend_sync_data)
                .set_backend_cache_synchron(backend_synched);
        } else {
            backend_synched = false;
        }
        backend_synched
    }

    // =======================================================================
    // Saturation-based concept-unsatisfiability test (cpp 26900–26921).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isConceptUnsatisfiabilitySaturated`.
    /// cpp 26900–26921.
    ///
    /// Decides whether the (possibly negated) concept is already known unsatisfiable
    /// from the approximate saturation pre-pass: it follows the concept's process
    /// data → concept reference linking → saturation reference linking → the
    /// saturation individual process node, and returns `true` iff that node's
    /// indirect status flags carry the clashed flag. Returns `false` when any hop is
    /// absent.
    ///
    pub fn is_concept_unsatisfiability_saturated(
        &mut self,
        concept: ConceptId,
        negation: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        //   conceptData = concept->getConceptData();
        //   saturationIndiNode = nullptr;
        let concept_data = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_data();
        let mut saturation_indi_node = SatNodeId::NONE;
        if concept_data != INVALID {
            // conProcData = (CConceptProcessData*)conceptData;
            let con_proc_data = Id::new(concept_data);
            // conRefLinking = conProcData->getConceptReferenceLinking();
            let con_ref_linking = calc_alg_context
                .ontology_arenas()
                .concept_process_data(con_proc_data)
                .get_concept_reference_linking();
            if con_ref_linking.is_some() {
                // confSatRefLinkingData = (CConceptSaturationReferenceLinkingData*)conRefLinking;
                let sat_calc_ref_link_data = calc_alg_context
                    .ontology_arenas()
                    .concept_saturation_reference_linking_data(con_ref_linking)
                    .get_concept_saturation_reference_linking_data(negation);
                if sat_calc_ref_link_data.is_some() {
                    saturation_indi_node = calc_alg_context
                        .ontology_arenas()
                        .saturation_concept_reference_linking(sat_calc_ref_link_data)
                        .get_individual_process_node_for_concept();
                }
            }
        }

        if saturation_indi_node.is_some() {
            return calc_alg_context
                .process_context()
                .sat_node(saturation_indi_node)
                .indirect_status_flags
                .has_flags_code(
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                    false,
                );
        }
        false
    }

    // =======================================================================
    // Backend-cache expansion / synchronisation queue feeders (cpp 27587–27641).
    // The per-node "already queued" flag guard fixes the boolean return and is
    // substrate-portable, so it is ported LIVE; only the databox queue
    // getter + `insertIndiviudalProcessNode` + `STATINC` are deferred.
    //
    // KONCLUDE-PORT-NOTE[api]: node.rs exposes the queued flags as public bool
    // FIELDS (`backend_*_queued`) with no `is_/set_` wrapper, and this unit may
    // edit only `u25.rs`, so the C++ `isX()`/`setX(true)` becomes a direct read /
    // assignment of the public field through the arena accessor.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBackendSynchronisationRetestQueue`.
    /// cpp 27587–27596.
    pub fn add_individual_to_backend_synchronisation_retest_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // if (!individual->isBackendSynchronRetestProcessingQueued()) {
        //   individual->setBackendSynchronRetestProcessingQueued(true);
        //   backendCacheSyncQueue = calcAlgContext->getProcessingDataBox()->getBackendCacheSynchronizationProcessingQueue(true);
        //   backendCacheSyncQueue->insertIndiviudalProcessNode(individual);
        //   STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT,calcAlgContext);
        //   return true; }
        // return false;
        if !calc_alg_context
            .process_context()
            .node(individual)
            .is_backend_synchron_retest_processing_queued()
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_backend_synchron_retest_processing_queued(true);
            let backend_cache_sync_queue =
                calc_alg_context.get_backend_cache_synchronization_processing_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_unsorted_proc_queue_mut(backend_cache_sync_queue)
                .insert_indiviudal_process_node(individual);
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBackendDirectInfluenceExpansionQueue`.
    /// cpp 27598–27607.
    pub fn add_individual_to_backend_direct_influence_expansion_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // if (!individual->isBackendDirectInfluenceExpansionQueued()) {
        //   individual->setBackendDirectInfluenceExpansionQueued(true);
        //   backendCacheSyncQueue = calcAlgContext->getProcessingDataBox()->getBackendDirectInfluenceExpansionQueue(true);
        //   backendCacheSyncQueue->insertIndiviudalProcessNode(individual);
        //   STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
        //   return true; }
        // return false;
        if !calc_alg_context
            .process_context()
            .node(individual)
            .is_backend_direct_influence_expansion_queued()
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_backend_direct_influence_expansion_queued(true);
            let backend_cache_sync_queue =
                calc_alg_context.get_backend_direct_influence_expansion_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_unsorted_proc_queue_mut(backend_cache_sync_queue)
                .insert_indiviudal_process_node(individual);
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBackendIndirectCompatibilityExpansionQueue`.
    /// cpp 27609–27618.
    pub fn add_individual_to_backend_indirect_compatibility_expansion_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // if (!individual->isBackendIndirectCompatibilityExpansionQueued()) {
        //   individual->setBackendIndirectCompatibilityExpansionQueued(true);
        //   backendCacheSyncQueue = calcAlgContext->getProcessingDataBox()->getBackendIndirectCompatibilityExpansionQueue(true);
        //   backendCacheSyncQueue->insertIndiviudalProcessNode(individual);
        //   STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
        //   return true; }
        // return false;
        if !calc_alg_context
            .process_context()
            .node(individual)
            .is_backend_indirect_compatibility_expansion_queued()
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_backend_indirect_compatibility_expansion_queued(true);
            let backend_cache_sync_queue =
                calc_alg_context.get_backend_indirect_compatibility_expansion_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_unsorted_proc_queue_mut(backend_cache_sync_queue)
                .insert_indiviudal_process_node(individual);
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBackendReuseExpansionQueue`.
    /// cpp 27621–27630.
    pub fn add_individual_to_backend_reuse_expansion_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // if (!individual->isBackendReuseExpansionQueued()) {
        //   individual->setBackendReuseExpansionQueued(true);
        //   backendCacheSyncQueue = calcAlgContext->getProcessingDataBox()->getBackendIndividualReuseExpansionQueue(true);
        //   backendCacheSyncQueue->insertIndiviudalProcessNode(individual);
        //   STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
        //   return true; }
        // return false;
        if !calc_alg_context
            .process_context()
            .node(individual)
            .backend_reuse_expansion_queued
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_backend_reuse_expansion_queued(true);
            let backend_cache_sync_queue =
                calc_alg_context.get_backend_individual_reuse_expansion_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_unsorted_proc_queue_mut(backend_cache_sync_queue)
                .insert_indiviudal_process_node(individual);
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToBackendNeighbourExpansionQueue`.
    /// cpp 27632–27641.
    ///
    /// KONCLUDE-PORT-NOTE[api]: this one feeds the
    /// `CIndividualLinkerRotationProcessingQueue` (vs the unsorted queue of the other
    /// four); the deferred insert targets `getBackendIndividualNeighbourExpansionQueue`.
    pub fn add_individual_to_backend_neighbour_expansion_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // if (!individual->isBackendNeighbourExpansionQueued()) {
        //   individual->setBackendNeighbourExpansionQueued(true);
        //   backendCacheSyncQueue = calcAlgContext->getProcessingDataBox()->getBackendIndividualNeighbourExpansionQueue(true);
        //   backendCacheSyncQueue->insertIndiviudalProcessNode(individual);
        //   STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
        //   return true; }
        // return false;
        if !calc_alg_context
            .process_context()
            .node(individual)
            .is_backend_neighbour_expansion_queued()
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual)
                .set_backend_neighbour_expansion_queued(true);
            let backend_cache_sync_queue =
                calc_alg_context.get_backend_individual_neighbour_expansion_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_rotation_proc_queue_mut(backend_cache_sync_queue)
                .insert_indiviudal_process_node(individual);
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT, calcAlgContext);
            return true;
        }
        false
    }
}
