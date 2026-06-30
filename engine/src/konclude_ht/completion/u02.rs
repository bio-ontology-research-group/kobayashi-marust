//! `completion::u02` — port unit #2 of the completion task-handle algorithm
//! (Core processing loop / driver family).
//!
//! Ports three methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`:
//!   - `continueIndividualProcessing`   (.cpp 2074–2094)
//!   - `takeNextProcessIndividual`      (.cpp 2190–2790)
//!   - `analyzeCompletionGraphStatistics` (.cpp 2794–2825)
//!
//! KONCLUDE-PORT-NOTE[ownership]: C++ threads the per-thread
//! `CCalculationAlgorithmContextBase*` through every method; the port passes it as
//! an explicit `&CalculationAlgorithmContextBase` / `&mut CalculationAlgorithmContextBase`
//! parameter (it owns the single `ProcessingDataBox`). `CIndividualProcessNode*`
//! becomes a `NodeId` (arena index). Individual nodes are resolved through the
//! not-yet-ported `getLocalizedIndividual`/node-arena subsystem, so the node-flag
//! and label-set reads below are `W3-DEFER[api]` stubs while the control flow is
//! kept verbatim.

#![allow(dead_code, unused_variables, unused_mut)]

use super::super::model::substrate::Cint64;
use super::super::process::{ConDescId, LabelSetId, NodeId, TrackPointId};
use super::algorithm::IndiNodeQueueType;
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::continueIndividualProcessing`.
    pub fn continue_individual_processing(
        &self,
        indi_proc_node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        // bool purgedIndiBlocked = indiProcNode->hasIndirectBlockedProcessingRestrictionFlags()
        //                          || indiProcNode->hasPurgedBlockedProcessingRestrictionFlags();
        let purged_indi_blocked = {
            let node = calc_alg_context.process_context().node(indi_proc_node);
            node.has_indirect_blocked_processing_restriction_flags()
                || node.has_purged_blocked_processing_restriction_flags()
        };
        if purged_indi_blocked {
            return false;
        }

        // W3-DEFER[api]: CConceptProcessingQueue* conProQue = indiProcNode->getConceptProcessingQueue(false);
        // STILL-MISSING: the `CConceptProcessingQueue` container is not yet ported
        // (only `ConceptProcessingQueueId` stub + a node field exist; no `isEmpty` /
        // `getNextConceptProcessPriority` / `getPriority`). Treated as absent/empty
        // (the `conProQue && !conProQue->isEmpty()` guard is false) until that wave.
        let con_pro_que_present_and_non_empty = false;
        if con_pro_que_present_and_non_empty {
            // W3-DEFER[api]: conProQue->getNextConceptProcessPriority(&conProPri)
            let got_next_priority = false;
            if got_next_priority {
                // W3-DEFER[api]: conProPri.getPriority()
                let priority: f64 = 0.0;
                if priority < self.min_concept_processing_priority_level {
                    return false;
                }
            }
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::takeNextProcessIndividual`.
    ///
    /// PORT-PENDING: the 601-line body probes ~40 distinct processing queues /
    /// review sets in a fixed priority order, none of whose container subsystems are
    /// ported yet (the Process-layer processing queues, the `IndividualProcessNodeVector`,
    /// the backend-neighbour-expansion controlling data, the signature-blocking /
    /// reusing review data, the nominal-non-deterministic sort linkers), and it
    /// dispatches into ~30 not-yet-ported algorithm helpers from other units
    /// (`getLocalizedIndividual`, `getUpToDateIndividual`,
    /// `queuedIndividualBackendNeighbourExpansion`,
    /// `detectIndividualNodeSignatureBlockingStatus`, `expand*FromBackendCache`,
    /// `reuseIndividualBackendExpansion`, `incrementalNodeExpansion`,
    /// `incrementalMergeWithPreviousDeterministicCompletionGraph`,
    /// `getCorrectedNominalIndividualNode`, ...). The signature is preserved; the
    /// fixed probe order is recorded for the eventual full port.
    ///
    /// Probe order (each guarded by `if (!indiProcNode)`, setting mIndiNodeFromQueueType):
    ///   1. cache-testing nodes                  (INQT_CACHETEST, sets concludeUnsatCaching)
    ///   2. immediately-processing queue         (INQT_IMMEDIATE)
    ///   3. delayed-backend-init queue           (INQT_DELAYEDBACKENDINIT)
    ///   4. role-assertion-expansion queue       (INQT_ROLEASS)
    ///   5. depth-deterministic-expansion queue  (INQT_DETEXP, min-pri=deterministic)
    ///   6. depth-first-deterministic-exp queue  (INQT_DEPTHFIRST)
    ///   7. distinct value-space sat-checking    (INQT_VSTSATTESTING)
    ///   8. value-space-triggering queue         (INQT_VSTRIGGERING)
    ///   9. backend-cache-sync retest queue      (INQT_BACKENDSYNCRETEST)
    ///  10. backend-direct-influence-expansion   (INQT_BACKENDDIRECTINFLUENCEEXPANSION)
    ///  11. variable-binding concept batch queue (INQT_VARBINDBATCHQUE)
    ///  12. incremental-compatibility checking   (drains, checkCompatibilityUpdate...)
    ///  13. incremental-expansion initializing   (drains, initializeIncremental...)
    ///  14. incremental-expansion queue          (incrementalNodeExpansion)
    ///  15. incremental compatible-merge         (incrementalMergeWithPreviousDeterministic...)
    ///  16. early individual-reactivation queue  (INQT_COMPCACHEDREACT)
    ///  17. sort nominal-non-deterministic nodes (qSort by id desc)
    ///  18. prepare backend-expansion-reuse branching
    ///  19. fixed-mode backend reuse-expansion   (INQT_BACKENDEXPANSIONREUSE)
    ///  20. individual processing queue          (INQT_OUTDATED, min-pri=0)
    ///  21. nominal processing queue             (INQT_NOMINAL)
    ///  22. backend individual neighbour expansion
    ///  23. propagation-cut backend expansion    (recurse into takeNextProcessIndividual)
    ///  24. sorted nominal-non-deterministic node (INQT_NOMINAL)
    ///  25. individual depth processing queue    (INQT_DEPTHNORMAL)
    ///  26. nominal-caching-loss reactivation     (INQT_NOMINALCACHINGLOSSREACTIVATION)
    ///  27. individual depth-first queue          (INQT_DEPTHFIRST)
    ///  28. late individual-reactivation queue    (INQT_COMPCACHEDREACT)
    ///  29. blocking-update review queue          (INQT_BLOCKUP)
    ///  30. blocked-reactivation queue            (INQT_BLOCKREACT)
    ///  31. signature-blocking review set
    ///  32. reusing review data
    ///  33. backend late neighbour expansion
    ///  34. prioritized-mode backend reuse-expansion (INQT_BACKENDEXPANSIONREUSE)
    ///  35. delaying-nominal processing queue     (INQT_DELAYEDNOMINAL)
    ///  36. backend indirect-compatibility expansion (INQT_BACKENDINDIRECTCOMPATIBILITYEXPANSION)
    pub fn take_next_process_individual(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // CIndividualProcessNode* indiProcNode = nullptr;
        let mut indi_proc_node: NodeId = NodeId::NONE;
        // mIndiNodeConcludeUnsatCaching = false;
        self.indi_node_conclude_unsat_caching = false;
        // mIndiNodeFromQueueType = INQT_NONE;
        self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_None;

        // --- Probe 1: cache-testing individual nodes (cpp 2195-2202). LIVE. ---
        // This arm is backed by the real `mIndividualNodeCacheTestingLinker`
        // (`process/db4.rs`), so it is ported in full.
        if indi_proc_node.is_none() {
            // mMinConceptProcessingPriorityLevel = mImmediatelyProcessPriority;
            self.min_concept_processing_priority_level =
                super::algorithm::IMMEDIATELY_PROCESS_PRIORITY as f64;
            if calc_alg_context
                .processing_data_box()
                .has_cache_testing_individual_nodes()
            {
                indi_proc_node = calc_alg_context
                    .processing_data_box_mut()
                    .take_next_cache_testing_individual_node();
                self.indi_node_conclude_unsat_caching = true;
                self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_CacheTest;
            }
        }

        // --- Probes 2-23 + 25-36: the triple-buffered processing-queue cascade. ---
        //
        // W3-DEFER[api]: every remaining probe (immediately-processing, delayed-
        // backend-init, role-assertion, depth-deterministic / depth-first-
        // deterministic expansion, distinct value-space sat-checking, value-space-
        // triggering, backend-cache-sync retest, backend direct/indirect-influence
        // expansion, variable-binding concept-batch, incremental-compatibility /
        // -expansion-initializing / -expansion / compatible-merge, early/late
        // individual-reactivation, fixed/prioritized backend reuse-expansion,
        // the INQT_OUTDATED individual-processing queue, nominal / nominal-caching-
        // loss-reactivation, backend individual-neighbour + propagation-cut
        // expansion, individual depth / depth-first, blocking-update / blocked-
        // reactivation review, signature-blocking review set, reusing review data,
        // backend late-neighbour expansion, delaying-nominal, backend indirect-
        // compatibility) probes a `CIndividual*ProcessingQueue` whose CONTENTS
        // subsystem is the not-yet-ported processing-queue layer: the `process/db3.rs`
        // lazy getters currently return `Id::NONE` (the queue is never allocated,
        // `initProcessingQueue` is `W2-DEFER`), and the queue stub types in
        // `process/stubs.rs` expose no `isEmpty` / `takeNextProcessIndividual*`.
        // Several arms additionally dispatch into still-deferred merge/nominal/
        // cache/backend helpers (`getUpToDateIndividual`, `incrementalNodeExpansion`,
        // `detectIndividualNodeSignatureBlockingStatus`,
        // `queuedIndividualBackendNeighbourExpansion`, `removeIndividualReusing`,
        // `getCorrectedNominalIndividualNode`, ...). They are therefore kept DEFERRED
        // and the trivial (non-merge / non-cache) consistency path never reaches them
        // (it finds either a cache-testing node above, a sorted nominal node below, or
        // — for a freshly-seeded immediately-processing root — nothing, and concludes).
        // The faithful, fixed probe ORDER is recorded verbatim in the doc-comment on
        // this method (probes 1-36) for the eventual full port once the queue-contents
        // layer lands.

        // --- Probe 24: sorted nominal-non-deterministic processing node
        // (cpp 2576-2581). LIVE (db4-backed `mSortedNominalNonDeterministicProcessing
        // NodeLinker`); reached only after the deferred sort-prep arm, so it is inert
        // until nominal non-deterministic nodes exist (none on the trivial path). ---
        if indi_proc_node.is_none()
            && calc_alg_context
                .processing_data_box()
                .has_sorted_nominal_non_deterministic_processing_nodes()
        {
            indi_proc_node = calc_alg_context
                .processing_data_box_mut()
                .take_sorted_nominal_non_deterministic_processing_node();
            self.indi_node_from_queue_type = IndiNodeQueueType::Inqt_Nominal;
        }

        // return indiProcNode;
        indi_proc_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::analyzeCompletionGraphStatistics`.
    pub fn analyze_completion_graph_statistics(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // CProcessingDataBox* processingDataBox = calcAlgContext->getProcessingDataBox();
        // CIndividualProcessNodeVector* indiNodeVec = processingDataBox->getIndividualProcessNodeVector();
        // cint64 indiCount = indiNodeVec->getItemCount();
        let indi_count: Cint64 = calc_alg_context
            .processing_data_box()
            .individual_process_node_vector()
            .get_item_count();
        // cint64 indiStart = indiNodeVec->getItemMinIndex();
        let indi_start: Cint64 = calc_alg_context
            .processing_data_box()
            .individual_process_node_vector()
            .get_item_min_index();

        let mut indi_idx = indi_start;
        while indi_idx < indi_count {
            // CIndividualProcessNode* indiNode = getLocalizedIndividual(indiIdx,calcAlgContext);
            let mut indi_node: NodeId = calc_alg_context.get_localized_individual_by_id(indi_idx);
            if indi_node.is_some() {
                // CReapplyConceptLabelSet* conSet = indiNode->getReapplyConceptLabelSet(false);
                let con_set: LabelSetId = calc_alg_context
                    .process_context_mut()
                    .node_mut(indi_node)
                    .get_reapply_concept_label_set(false);
                // cint64 conSigValue = indiNode->getReapplyConceptLabelSet(false)->getConceptSignatureValue();
                let con_sig_value: Cint64 = if con_set.is_some() {
                    calc_alg_context
                        .process_context()
                        .label_set(con_set)
                        .get_concept_signature_value()
                } else {
                    0
                };
                // cint64 processingRestrictionFlags = indiNode->getProcessingRestrictionFlags();
                let processing_restriction_flags: Cint64 = calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .processing_restriction_flags();
                // KONCLUDE-PORT-NOTE[api]: QHash::insertMulti (a multimap insert) →
                // HashMap::insert; `signature_indi_node_status_hash` is single-valued
                // (statistics-only field), so duplicate-key keeps only the last value.
                self.signature_indi_node_status_hash
                    .insert(con_sig_value, processing_restriction_flags);

                if !self.signature_indi_node_pred_dep_hash.contains_key(&con_sig_value) {
                    // cint64 indiAncestorDepth = indiNode->getIndividualAncestorDepth();
                    let indi_ancestor_depth: Cint64 = calc_alg_context
                        .process_context()
                        .node(indi_node)
                        .individual_ancestor_depth();
                    if con_set.is_some() && indi_ancestor_depth > 0 {
                        let mut con_from_pred_count: Cint64 = 0;
                        // CConceptDescriptor* conDesIt = conSet->getAddingSortedConceptDescriptionLinker();
                        let mut con_des_it: ConDescId = calc_alg_context
                            .process_context()
                            .label_set(con_set)
                            .get_adding_sorted_concept_description_linker();
                        while con_des_it.is_some() {
                            // cint64 conceptTag = conDesIt->getConceptTag();
                            let concept_tag: Cint64 = {
                                let onto = calc_alg_context.ontology_arenas();
                                calc_alg_context
                                    .process_context()
                                    .con_desc(con_des_it)
                                    .get_concept_tag(onto)
                            };
                            if concept_tag != 1 {
                                // CDependencyTrackPoint* depTrackPoint = conDesIt->getDependencyTrackPoint();
                                let dep_track_point: TrackPointId = calc_alg_context
                                    .process_context()
                                    .con_desc(con_des_it)
                                    .get_dependency_track_point();
                                // if (isConceptFromPredecessorDependent(indiNode,conDesIt,depTrackPoint,calcAlgContext))
                                if self.is_concept_from_predecessor_dependent(
                                    &mut indi_node,
                                    con_des_it,
                                    dep_track_point,
                                    calc_alg_context,
                                ) {
                                    con_from_pred_count += 1;
                                }
                            }
                            // conDesIt = conDesIt->getNext();
                            con_des_it = calc_alg_context
                                .process_context()
                                .con_desc(con_des_it)
                                .get_next_concept_descriptor();
                        }
                        self.signature_indi_node_pred_dep_hash
                            .insert(con_sig_value, con_from_pred_count);
                    }
                }
            }
            indi_idx += 1;
        }

        // mIndiNodeCountMap.insert(indiCount,mIndiNodeCountMap.value(indiCount,0)+1);
        let prev_count = *self.indi_node_count_map.get(&indi_count).unwrap_or(&0);
        self.indi_node_count_map.insert(indi_count, prev_count + 1);
        // mIndiNodeCountList.append(indiCount);
        self.indi_node_count_list.push(indi_count);
    }
}
