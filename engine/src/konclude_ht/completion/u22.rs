//! `completion::u22` — Caching / backend-cache / saturation family, batch
//! (port unit #22 of 36).
//!
//! Faithful port of the 20 methods the manifest (`01-completion-methods.md`,
//! "Unit 22") groups from Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! Each item notes its 1-based cpp line range.
//!
//! Methods (cpp order):
//!   * `rootUnsatisfiabilityWriteCaches`                                   [6865–6897]
//!   * `addIndividualNodeForCacheUnsatisfiableRetrieval`                   [7391–7396]
//!   * `writeClashDescriptorsToCache(line)`                               [7400–7408]
//!   * `writeClashDescriptorsToCache(des,additional,line)`               [7412–7423]
//!   * `writeClashDescriptorsToCache(des,line)`                          [7426–7542]
//!   * `addCachedComputedTypes`                                            [9042–9057]
//!   * `isGeneratingConceptSatisfiableCachedAbsorpable`                   [14175–14211]
//!   * `hasSaturatedClashedFlagForConcept`                                [16438–16459]
//!   * `getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindingsCached` [18088–18098]
//!   * `tryEstablishSaturationCaching`                                    [21674–21723]
//!   * `validateSaturationCachingPossible`                               [21866–21911]
//!   * `getCreationSuccessorSaturationNode`                              [21917–22013]
//!   * `getSaturationResolvedIndividualNodeExtension`                    [22054–22075]
//!   * `initializeIndividualNodeWithBackendCache`                        [22702–22814]
//!   * `getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher(assoc)` [22817–22823]
//!   * `getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher(node)`  [22825–22829]
//!   * `markIndividualNodeBackendNonConceptSetRelatedProcessing`         [22831–22909]
//!   * `tryDelayIndividualNodeInitializationWithBackendConceptSetLabel`  [22921–22966]
//!   * `registerProcessedIndividualForBackendConceptSetLabel`            [22971–22984]
//!   * `getBackendCacheRoleRepresentativeNeighbourCount`                 [23159–23193]
//!
//! KONCLUDE-PORT-NOTE[ownership]: every method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` in/out
//! pointer-references become `&mut NodeId`; a plain `CIndividualProcessNode*` value
//! parameter becomes `NodeId`; `CConcept*` → `ConceptId`, `CRole*` → `RoleId`,
//! `CConceptDescriptor*` → `ConDescId`, `CIndividualSaturationProcessNode*` →
//! `SatNodeId`, all resolved against `calc_alg_context.ontology_arenas()` /
//! `process_context()`. The databox is reached as
//! `calc_alg_context.processing_data_box{,_mut}()`.
//!
//! Deferral landscape. This unit is the unsatisfiable-cache-write + saturation-cache
//! + representative-memory-backend-cache slice of the caching family, and is among
//! the most deeply handler-dependent batches. Nearly every body bottoms out in a
//! subsystem scheduled for a later wave:
//!   * the **unsatisfiable / saturation / computed-consequences cache handlers**
//!     (`mUsedUnsatCacheHandler`, `mUsedSaturationNodeExpansionCacheHandler`,
//!     `mCompConsCacheHandler`, `mSatNodeExpCacheHandler`) — `completion::stubs`
//!     zero-size `Id` markers today (W6 Cache subtree);
//!   * the **classification message adapter** (`CSatisfiableTaskClassificationMessageAdapter`,
//!     reached from the `CSatisfiableCalculationTask`) — Task/analyser layer (W6);
//!   * the **saturation subsystem** (`CIndividualSaturationProcessNode`, its
//!     `CIndividualSaturationProcessNodeStatusFlags`, the
//!     `CReapplyConceptSaturationLabelSet`, the concept↔saturation reference linking
//!     `CConceptSaturationReferenceLinkingData`, the
//!     `CSaturationIndividualNodeExtensionResolveData` resolve hashes) — W4 saturation;
//!   * the **representative-memory backend cache** (the per-node
//!     `CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData`, the
//!     `CBackendRepresentativeMemoryCacheIndividualAssociationData` +
//!     `CBackendRepresentativeMemoryLabelCacheItem` family, the
//!     `CIndividualRepresentativeBackendCacheConceptSetLabelProcessingHash{,er}` and
//!     the delayed-init / queuing linkers) — reached only through
//!     `mBackendCacheHandler` (`self.backend_cache_handler`, a stub `Id`); W6 Cache;
//!   * the **tracked-clash cache/backtracking consumers** — the Unit 28/30
//!     descriptor and tracking-line substrate is live, while the cache handlers
//!     and Unit 29 dependency-directed backtracking integration remain pending.
//!
//! The substrate-portable pieces are live: the memoising
//! `getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindingsCached`
//! wrapper, `hasSaturatedClashedFlagForConcept`, and the two outer
//! `writeClashDescriptorsToCache` overload wrappers plus the core overload's
//! descriptor-validation/cache-write gate, and the root-task tested-concept
//! unsatisfiable-cache write branch. The remaining handler-driven bodies keep
//! faithful signatures and structural transcriptions under `// PORT-PENDING` so
//! later waves fill them without re-reading the source. Logic is documented,
//! never silently dropped.
//!
//! Deferred handler/Cache/Task/saturation pointer types that have no arena id yet
//! are carried as an opaque `Cint64` (`INVALID` == the C++ `nullptr`) tagged
//! `W6-DEFER[api]` (Cache/Task) or `W4-DEFER[api]` (saturation extension-resolve).
//! Rule/STAT counters use the
//! existing `algorithm.rs` getters; the `STATINC` statistic macro is a
//! `W3-DEFER[macro]` no-op note.

#![allow(dead_code)]
#![allow(unused_variables)]

use std::collections::HashMap;

use super::super::model::concept_process::ConceptProcessDataId;
use super::super::model::op::CCFS_PROPAGATION_TYPE;
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::super::process::node::IndividualProcessNode;
use super::super::process::sat_block::IndividualNodeSaturationBlockingData;
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::{ClashDescId, ConDescId, NodeId, SatNodeId};
use super::super::saturation::satellites::{
    ConceptNegationPair, SaturationIndividualNodeExtensionResolveDataId,
};
use super::super::task::adapters::EFEXTRACTSUBSUMERSROOTNODE;
use super::context::CalculationAlgorithmContextBase;
use super::stubs::SatisfiableCalculationTask;
use super::u30::TrackedClashedDependencyLine;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Root-task unsatisfiability cache writing (cpp 6865–6897).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::rootUnsatisfiabilityWriteCaches`.
    /// cpp 6865–6897.
    ///
    /// On an unsatisfiable ROOT task: if the task carries a classification message
    /// adapter with a testing concept and the `EFEXTRACTSUBSUMERSROOTNODE` extraction
    /// flag, write the clashed concept to the unsatisfiable cache and (optionally) to
    /// the saturation-node-expansion cache. Then, for a single-construction nominal
    /// node initialised by exactly one concept whose terminology is set, try caching
    /// the (negated) type consequence. Always returns `false`.
    ///
    /// PORT-PENDING: faithful transcription of cpp 6865–6897. Outline:
    ///
    ///   adapter = task->getClassificationMessageAdapter();              // W6-DEFER[api] Task/analyser
    ///   if adapter:
    ///       concept = adapter->getTestingConcept();
    ///       if concept && adapter->hasExtractionFlags(EFEXTRACTSUBSUMERSROOTNODE):
    ///           unsatCacheHandler = ctx->getUsedUnsatisfiableCacheHandler();   // W6-DEFER[api]
    ///           if unsatCacheHandler && mConfTestedConceptWriteUnsatCaching:
    ///               unsatCacheHandler->writeUnsatisfiableClashedConcept(concept, ctx);
    ///           satNodeExpanderCacheHandler = ctx->getUsedSaturationNodeExpansionCacheHandler();
    ///           if satNodeExpanderCacheHandler && mConfSaturationConceptUnsatisfiabilitySaturatedCacheWriting:
    ///               satNodeExpanderCacheHandler->cacheUnsatisfiableConcept(concept, ctx);
    ///   processingDataBox = ctx->getProcessingDataBox();
    ///   constIndiNode = processingDataBox->getConstructedIndividualNode();
    ///   if !processingDataBox->hasMultipleConstructionIndividualNodes()
    ///       && constIndiNode && constIndiNode->isNominalIndividualNode():
    ///       initConLinker = constIndiNode->getInitializingConceptLinker();
    ///       individual    = constIndiNode->getNominalIndividual();
    ///       if initConLinker && !initConLinker->hasNext():
    ///           initConcept = initConLinker->getData(); conNegation = initConLinker->isNegated();
    ///           if mConfCacheComputedConsequences && mCompConsCacheHandler && initConcept->getTerminology():
    ///               mCompConsCacheHandler->tryCacheTypeConcept(individual, initConcept, !conNegation, ctx); // W6-DEFER[api]
    ///   return false;
    pub fn root_unsatisfiability_write_caches(
        &mut self,
        task: Id<SatisfiableCalculationTask>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // CSatisfiableTaskClassificationMessageAdapter* adapter =
        //     task->getClassificationMessageAdapter();
        let adapter = calc_alg_context
            .base
            .try_sat_calc_task(task)
            .map(|task| task.get_classification_message_adapter())
            .unwrap_or(Id::NONE);

        if adapter.is_some() {
            let (concept, extract_subsumers_root_node) = {
                let adapter_ref = calc_alg_context.classification_message_adapter(adapter);
                (
                    adapter_ref.get_testing_concept(),
                    adapter_ref.has_extraction_flags(EFEXTRACTSUBSUMERSROOTNODE),
                )
            };

            if concept.is_some() && extract_subsumers_root_node {
                // CUnsatisfiableCacheHandler* unsatCacheHandler =
                //     calcAlgContext->getUsedUnsatisfiableCacheHandler();
                if self.conf_tested_concept_write_unsat_caching {
                    if let Some(mut handler_state) =
                        calc_alg_context.take_used_unsatisfiable_cache_handler()
                    {
                        handler_state.handler.write_unsatisfiable_clashed_concept(
                            concept,
                            calc_alg_context,
                            &mut handler_state.cache_context,
                        );
                        calc_alg_context.restore_used_unsatisfiable_cache_handler(handler_state);
                    }
                }

                // CSaturationNodeExpansionCacheHandler* satNodeExpanderCacheHandler =
                //     calcAlgContext->getUsedSaturationNodeExpansionCacheHandler();
                if self.conf_saturation_concept_unsatisfiability_saturated_cache_writing {
                    if let Some(mut handler_state) =
                        calc_alg_context.take_used_saturation_node_expansion_cache_handler()
                    {
                        handler_state
                            .handler
                            .cache_unsatisfiable_concept(concept, calc_alg_context);
                        calc_alg_context
                            .restore_used_saturation_node_expansion_cache_handler(handler_state);
                    }
                }
            }
        }

        // CProcessingDataBox* processingDataBox = calcAlgContext->getProcessingDataBox();
        // CIndividualProcessNode* constIndiNode = processingDataBox->getConstructedIndividualNode();
        let const_indi_node = calc_alg_context
            .processing_data_box()
            .constructed_individual_node();
        if !calc_alg_context
            .processing_data_box()
            .has_multiple_construction_individual_nodes()
            && const_indi_node.is_some()
            && calc_alg_context
                .process_context()
                .node(const_indi_node)
                .is_nominal_individual_node()
        {
            let (init_concept, con_negation, single_init_concept, individual) = {
                let const_node = calc_alg_context.process_context().node(const_indi_node);
                let init_con_linker = const_node.initializing_concept_linker();
                (
                    init_con_linker
                        .first()
                        .map(|linker| linker.target)
                        .unwrap_or(ConceptId::NONE),
                    init_con_linker
                        .first()
                        .map(|linker| linker.negated)
                        .unwrap_or(false),
                    init_con_linker.len() == 1,
                    const_node.nominal_individual(),
                )
            };

            if single_init_concept
                && init_concept.is_some()
                && self.conf_cache_computed_consequences
                && calc_alg_context
                    .ontology_arenas()
                    .concept(init_concept)
                    .get_terminology()
                    != INVALID
            {
                if let Some(mut handler_state) =
                    calc_alg_context.take_used_computed_consequences_cache_handler()
                {
                    handler_state.handler.try_cache_type_concept(
                        individual,
                        init_concept,
                        !con_negation,
                        calc_alg_context,
                    );
                    calc_alg_context
                        .restore_used_computed_consequences_cache_handler(handler_state);
                }
            }
        }
        false
    }

    // =======================================================================
    // Unsatisfiable-retrieval queueing + clash-descriptor cache writing
    // (cpp 7391–7542).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualNodeForCacheUnsatisfiableRetrieval`.
    /// cpp 7391–7396.
    ///
    /// Allocate a single-element `CXLinker<CIndividualProcessNode*>` from the per-task
    /// memory pool, init it with `indiNode`, and register it on the databox as a
    /// cache-testing linker.
    ///
    pub fn add_individual_node_for_cache_unsatisfiable_retrieval(
        &mut self,
        indi_node: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        calc_alg_context
            .processing_data_box_mut()
            .add_individual_node_cache_testing_linker(vec![*indi_node]);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::writeClashDescriptorsToCache`
    /// (the `CTrackedClashedDependencyLine*` overload). cpp 7400–7408.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: three C++ methods share the name
    /// `writeClashDescriptorsToCache`, dispatched by argument type; Rust cannot
    /// overload, so the dependency-line variant is named `*_from_line`, the
    /// additional-descriptor variant `*_with_additional`, and the core descriptor
    /// variant keeps the base name.
    ///
    ///   trackedClashedDesList = nullptr;
    ///   while trackingLine->hasMoreTrackedClashedList():
    ///       trackedClashedDesList = trackingLine->takeNextTrackedClashedList()->append(trackedClashedDesList);
    ///   cacheWrite = writeClashDescriptorsToCache(trackedClashedDesList, trackingLine, ctx);  // core overload
    ///   trackingLine->sortInTrackedClashedDescriptors(trackedClashedDesList, true);
    ///   return cacheWrite;
    pub fn write_clash_descriptors_to_cache_from_line(
        &mut self,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut tracked_clashed_des_list = ClashDescId::NONE;
        while tracking_line.has_more_tracked_clashed_list() {
            let list = tracking_line.take_next_tracked_clashed_list();
            if list.is_some() {
                let mut tail = list;
                while calc_alg_context
                    .process_context()
                    .clash_desc(tail)
                    .get_next_descriptor()
                    .is_some()
                {
                    tail = calc_alg_context
                        .process_context()
                        .clash_desc(tail)
                        .get_next_descriptor();
                }
                calc_alg_context
                    .process_context_mut()
                    .clash_desc_mut(tail)
                    .set_next(tracked_clashed_des_list);
                tracked_clashed_des_list = list;
            }
        }
        let cache_write = self.write_clash_descriptors_to_cache(
            &mut tracked_clashed_des_list,
            tracking_line,
            calc_alg_context,
        );
        tracking_line.sort_in_tracked_clashed_descriptors(
            tracked_clashed_des_list,
            true,
            calc_alg_context,
        );
        cache_write
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::writeClashDescriptorsToCache`
    /// (the additional-descriptor overload). cpp 7412–7423.
    /// KONCLUDE-PORT-NOTE[overload]: see `*_from_line`; `trackedClashedDes` is an
    /// in/out `CTrackedClashedDescriptor*&` → `&mut ClashDescId`.
    ///
    ///   separatTrackedClashedDes = additionalTrackedClashedDes;
    ///   trackedClashedDes = additionalTrackedClashedDes->append(trackedClashedDes);
    ///   cacheWrite = writeClashDescriptorsToCache(trackedClashedDes, trackingLine, ctx);  // core overload
    ///   if !cacheWrite:
    ///       trackedClashedDes = trackedClashedDes->getNextDescriptor();
    ///   else:
    ///       trackedClashedDes = trackedClashedDes->removeOne(additionalTrackedClashedDes);
    ///   additionalTrackedClashedDes->clearNext();
    ///   return cacheWrite;
    pub fn write_clash_descriptors_to_cache_with_additional(
        &mut self,
        tracked_clashed_des: &mut ClashDescId,
        additional_tracked_clashed_des: ClashDescId,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let separat_tracked_clashed_des = additional_tracked_clashed_des;
        calc_alg_context
            .process_context_mut()
            .clash_desc_mut(additional_tracked_clashed_des)
            .set_next(*tracked_clashed_des);
        *tracked_clashed_des = additional_tracked_clashed_des;

        let cache_write = self.write_clash_descriptors_to_cache(
            tracked_clashed_des,
            tracking_line,
            calc_alg_context,
        );
        if !cache_write {
            *tracked_clashed_des = calc_alg_context
                .process_context()
                .clash_desc(*tracked_clashed_des)
                .get_next_descriptor();
        } else if *tracked_clashed_des == separat_tracked_clashed_des {
            *tracked_clashed_des = calc_alg_context
                .process_context()
                .clash_desc(separat_tracked_clashed_des)
                .get_next_descriptor();
        } else {
            let mut prev = *tracked_clashed_des;
            while prev.is_some() {
                let next = calc_alg_context
                    .process_context()
                    .clash_desc(prev)
                    .get_next_descriptor();
                if next == separat_tracked_clashed_des {
                    let after = calc_alg_context
                        .process_context()
                        .clash_desc(separat_tracked_clashed_des)
                        .get_next_descriptor();
                    calc_alg_context
                        .process_context_mut()
                        .clash_desc_mut(prev)
                        .set_next(after);
                    break;
                }
                prev = next;
            }
        }
        calc_alg_context
            .process_context_mut()
            .clash_desc_mut(additional_tracked_clashed_des)
            .set_next(ClashDescId::NONE);
        cache_write
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::writeClashDescriptorsToCache`
    /// (the core `CTrackedClashedDescriptor*&` overload). cpp 7426–7542.
    ///
    /// The unsatisfiable-cache write gate. Validates the tracked clash chain — all
    /// descriptors share the appropriated individual id (else fail on nominals) and
    /// node level, every descriptor has a non-propagation terminology concept, and no
    /// atomic A/¬A clash — then (optionally) records the node signature, sorts the
    /// descriptors, and writes the unsatisfiable clashed-descriptor cache line.
    /// Returns whether a cache line was written.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: core variant; keeps the base name.
    /// W6-DEFER[api]: the unsat-cache handler writer is still deferred; the
    /// tracked descriptor/line substrate is live.
    ///
    /// PORT-PENDING: faithful transcription of cpp 7426–7542. Outline:
    ///
    ///   if mConfWriteUnsatCaching && trackedClashedDes:
    ///       STATINC(UNSATCACHEWRITINGREQUSTCOUNT)
    ///       (debug clash string under mBacktrackDebug)
    ///       it = trackedClashedDes;
    ///       nominalOccured  = it->isAppropriatedIndividualNominal();
    ///       minIndiID       = it->getAppropriatedIndividualID();   hasOtherIndiID = false;
    ///       minIndiLevel    = it->getAppropriatedIndividualLevel(); hasOtherIndiLevel = false;
    ///       hasNoInvalidConDes = it->getConceptDescriptor() != nullptr;
    ///       for it = it->getNextDescriptor(); it; it = it->getNextDescriptor():
    ///           conDes = it->getConceptDescriptor();
    ///           hasNoInvalidConDes &= conDes != nullptr;
    ///           if conDes:
    ///               concept = conDes->getConcept();
    ///               // op.rs: concept->getOperatorCode() / getConceptOperator()
    ///               if concept->getTerminology()==nullptr
    ///                   || conOperator->hasPartialOperatorCodeFlag(CCFS_PROPAGATION_TYPE):  // model::op
    ///                   hasNoInvalidConDes = false;
    ///           nominalOccured |= it->isAppropriatedIndividualNominal();
    ///           if it->getAppropriatedIndividualID() != minIndiID:
    ///               hasOtherIndiID = true;
    ///               if nominalOccured: STATINC(...DIFFNOMINALFAILED); return false;
    ///           if it->getAppropriatedIndividualLevel() != minIndiLevel:
    ///               STATINC(...DIFFNODELEVELFAILED); hasOtherIndiLevel = true; return false;
    ///       // TODO(Konclude): unsat caching with nominals currently deactivated
    ///       if hasNoInvalidConDes && !nominalOccured:
    ///           writeCacheLine = nominalOccured ? !hasOtherIndiID : !hasOtherIndiLevel;
    ///           atomicClash = false;
    ///           if writeCacheLine:
    ///               for it = trackedClashedDes; it && !atomicClash; it = it->getNextDescriptor():
    ///                   concept = it->getConceptDescriptor()->getConcept(); conNeg = ...->getNegation();
    ///                   for ot = it->getNextDescriptor(); ot && !atomicClash; ot = ot->getNextDescriptor():
    ///                       if ot->getConcept()==concept && ot->getNegation()!=conNeg:
    ///                           STATINC(...ATOMICCLASHFAILED); atomicClash = true; return false;
    ///           writeCacheLine &= !atomicClash;
    ///           if writeCacheLine:
    ///               if mConfUnsatCachingUseNodeSignatureSet:
    ///                   addIndiNodeSignatureOfUnsatisfiableClashedDescriptors(trackedClashedDes, ctx);
    ///               trackedClashedDes = getSortedClashedDescriptors(trackedClashedDes, ctx);
    ///               writeUnsatisfiableClashedDescriptors(trackedClashedDes, ctx);  // W6-DEFER[api]
    ///               return true;
    ///   return false;
    pub fn write_clash_descriptors_to_cache(
        &mut self,
        tracked_clashed_des: &mut ClashDescId,
        tracking_line: &mut TrackedClashedDependencyLine,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = tracking_line;
        if !self.conf_write_unsat_caching || tracked_clashed_des.is_none() {
            return false;
        }

        let first = *tracked_clashed_des;
        let first_desc = calc_alg_context.process_context().clash_desc(first);
        let mut nominal_occurred = first_desc.is_appropriated_individual_nominal();
        let min_indi_id = first_desc.get_appropriated_individual_id();
        let min_indi_level = first_desc.get_appropriated_individual_level();
        let mut has_other_indi_id = false;
        let mut has_no_invalid_con_des =
            self.is_valid_unsat_cache_tracked_concept_descriptor(first, calc_alg_context);

        let mut it = calc_alg_context
            .process_context()
            .clash_desc(first)
            .get_next_descriptor();
        while it.is_some() {
            let desc = calc_alg_context.process_context().clash_desc(it);
            has_no_invalid_con_des &=
                self.is_valid_unsat_cache_tracked_concept_descriptor(it, calc_alg_context);
            nominal_occurred |= desc.is_appropriated_individual_nominal();
            if desc.get_appropriated_individual_id() != min_indi_id {
                has_other_indi_id = true;
                if nominal_occurred {
                    return false;
                }
            }
            if desc.get_appropriated_individual_level() != min_indi_level {
                return false;
            }
            it = desc.get_next_descriptor();
        }

        if !has_no_invalid_con_des || nominal_occurred {
            return false;
        }

        let write_cache_line = if nominal_occurred {
            !has_other_indi_id
        } else {
            true
        };
        if !write_cache_line
            || self.has_unsat_cache_atomic_clash(*tracked_clashed_des, calc_alg_context)
        {
            return false;
        }

        if self.conf_unsat_caching_use_node_signature_set {
            self.add_indi_node_signature_of_unsatisfiable_clashed_descriptors(
                *tracked_clashed_des,
                calc_alg_context,
            );
        }
        *tracked_clashed_des =
            self.get_sorted_clashed_descriptors(*tracked_clashed_des, calc_alg_context);
        self.write_unsatisfiable_clashed_descriptors(*tracked_clashed_des, calc_alg_context)
    }

    fn is_valid_unsat_cache_tracked_concept_descriptor(
        &self,
        tracked_clashed_des: ClashDescId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let con_des = calc_alg_context
            .process_context()
            .clash_desc(tracked_clashed_des)
            .get_concept_descriptor();
        if con_des.is_none() {
            return false;
        }
        let concept = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        if concept.is_none() {
            return false;
        }
        let concept = calc_alg_context.ontology_arenas().concept(concept);
        concept.get_terminology() != INVALID
            && !concept
                .get_concept_operator()
                .has_partial_operator_code_flag(CCFS_PROPAGATION_TYPE)
    }

    fn has_unsat_cache_atomic_clash(
        &self,
        tracked_clashed_des: ClashDescId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let mut it = tracked_clashed_des;
        while it.is_some() {
            let con_des = calc_alg_context
                .process_context()
                .clash_desc(it)
                .get_concept_descriptor();
            let concept = calc_alg_context
                .process_context()
                .con_desc(con_des)
                .get_concept();
            let negated = calc_alg_context
                .process_context()
                .con_desc(con_des)
                .is_negated();
            let mut other_it = calc_alg_context
                .process_context()
                .clash_desc(it)
                .get_next_descriptor();
            while other_it.is_some() {
                let other_con_des = calc_alg_context
                    .process_context()
                    .clash_desc(other_it)
                    .get_concept_descriptor();
                let other_concept = calc_alg_context
                    .process_context()
                    .con_desc(other_con_des)
                    .get_concept();
                let other_negated = calc_alg_context
                    .process_context()
                    .con_desc(other_con_des)
                    .is_negated();
                if other_concept == concept && other_negated != negated {
                    return true;
                }
                other_it = calc_alg_context
                    .process_context()
                    .clash_desc(other_it)
                    .get_next_descriptor();
            }
            it = calc_alg_context
                .process_context()
                .clash_desc(it)
                .get_next_descriptor();
        }
        false
    }

    // =======================================================================
    // Cached computed types (cpp 9042–9057).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addCachedComputedTypes`.
    /// cpp 9042–9057.
    ///
    /// For a nominal node not yet flagged `PRFCACHEDCOMPUTEDTYPESADDED`, fetch the
    /// individual's cached type-concept linker from the computed-consequences cache
    /// and, if present, add those concepts to the node under a fresh AND dependency.
    /// Returns whether concepts were added.
    ///
    /// PORT-PENDING: faithful transcription of cpp 9042–9057. Outline:
    ///
    ///   addedConcepts = false;
    ///   individual = indiProcNode->getNominalIndividual();
    ///   if individual && mCompConsCacheHandler
    ///       && !indiProcNode->hasPartialProcessingRestrictionFlags(PRFCACHEDCOMPUTEDTYPESADDED):
    ///       indiProcNode->addProcessingRestrictionFlags(PRFCACHEDCOMPUTEDTYPESADDED);
    ///       typeConceptLinker = mCompConsCacheHandler->getCachedTypesConceptLinker(individual, ctx);  // W6-DEFER[api]
    ///       if typeConceptLinker:
    ///           depTrackPoint = ctx->getBaseDependencyNode()->getContinueDependencyTrackPoint();
    ///           createANDDependency(expDepTrackPoint, indiProcNode, nullptr, depTrackPoint, ctx);     // sibling (dependency unit)
    ///           addConceptsToIndividual(typeConceptLinker, false, indiProcNode, expDepTrackPoint, true, false, nullptr, ctx); // sibling
    ///           addedConcepts = true;
    ///   return addedConcepts;
    pub fn add_cached_computed_types(
        &mut self,
        indi_proc_node: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: `mCompConsCacheHandler` (computed-consequences cache, W6) is
        // a stub `Id`; `getCachedTypesConceptLinker` returns its concept linker. The
        // AND-dependency creation + `addConceptsToIndividual` are sibling methods in
        // later units. Body PORT-PENDING per outline.
        let _ = (indi_proc_node, calc_alg_context);
        false
    }

    // =======================================================================
    // Generating-concept satisfiable-cache absorbability (cpp 14175–14211).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isGeneratingConceptSatisfiableCachedAbsorpable`.
    /// cpp 14175–14211.
    ///
    /// A generating (SOME/ATLEAST) concept is satisfiable-cache absorbable unless the
    /// node already has a role successor (via some non-inverse super-role) to its
    /// ancestor under a functional role, or an ATMOST/ATLEAST reapply restriction on
    /// that super-role forces the effective cardinality to <= 1.
    ///
    /// Ported LIVE (task #24 wave 2b). Faithful transcription of cpp 14175–14211:
    ///
    ///   ancestorIndiNode = getAncestorIndividual(processIndi, ctx);   // sibling
    ///   if ancestorIndiNode:
    ///       concept = conDes->getConcept(); role = concept->getRole();          // model::concept
    ///       for superRoleIt in role->getIndirectSuperRoleList():                // model::role
    ///           if !superRoleIt->isNegated():
    ///               superRole = superRoleIt->getData();
    ///               if processIndi->hasRoleSuccessorToIndividual(superRole, ancestorIndiNode, true):  // node (PORT-PENDING accessor)
    ///                   if superRole->isFunctional(): return false;
    ///                   reapplyRoleSuccHash = processIndi->getReapplyRoleSuccessorHash(false);          // satellite
    ///                   for reapplyConceptDes in reapplyRoleSuccHash->getRoleReapplyIterator(superRole,false):
    ///                       reapplyConDes = reapplyConceptDes->getConceptDescriptor();
    ///                       reapplyConcept = reapplyConDes->getConcept(); reapplyConNeg = reapplyConDes->getNegation();
    ///                       opCode = reapplyConcept->getOperatorCode();
    ///                       if opCode == CCATMOST || opCode == CCATLEAST:                                // model::op
    ///                           cardinality = concept->getParameter() + 1*reapplyConNeg;
    ///                           if cardinality <= 1: return false;
    ///   return true;
    pub fn is_generating_concept_satisfiable_cached_absorpable(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        use super::super::model::op::{CCATLEAST, CCATMOST};
        use super::super::model::substrate::NegLink;
        let mut indi = *process_indi;
        let ancestor_indi_node = calc_alg_context.get_ancestor_individual(&mut indi);
        if ancestor_indi_node.is_some() {
            let concept = calc_alg_context
                .process_context()
                .con_desc(con_des)
                .get_concept();
            let role = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_role();
            // KONCLUDE-PORT-NOTE[identity]: Konclude's getIndirectSuperRoleList
            // STARTS with the role itself; the bridge builds STRICT lists, so the
            // role is walked explicitly first.
            let mut super_roles: Vec<NegLink<RoleId>> = vec![NegLink {
                target: role,
                negated: false,
            }];
            super_roles.extend(
                calc_alg_context
                    .ontology_arenas()
                    .role(role)
                    .get_indirect_super_role_list()
                    .iter()
                    .copied(),
            );
            let ancestor_indi_id = calc_alg_context
                .process_context()
                .node(ancestor_indi_node)
                .individual_node_id();
            for super_role_link in super_roles {
                if super_role_link.negated {
                    continue;
                }
                let super_role = super_role_link.target;
                if calc_alg_context
                    .process_context_mut()
                    .node_has_role_successor_to_individual_id(
                        *process_indi,
                        super_role,
                        ancestor_indi_id,
                        true,
                    )
                {
                    if calc_alg_context
                        .ontology_arenas()
                        .role(super_role)
                        .is_functional()
                    {
                        return false;
                    }
                    // check additional for ATMOST restriction
                    let mut reapply_queue_it =
                        IndividualProcessNode::get_role_reapply_iterator_in_context(
                            calc_alg_context.process_context_mut(),
                            *process_indi,
                            super_role,
                            false,
                        );
                    loop {
                        let reapply_concept_des =
                            reapply_queue_it.next(calc_alg_context.process_context(), true);
                        if reapply_concept_des.is_none() {
                            break;
                        }
                        let reapply_con_des = calc_alg_context
                            .process_context()
                            .reapply_con_desc(reapply_concept_des)
                            .get_concept_descriptor();
                        if reapply_con_des.is_none() {
                            continue;
                        }
                        let (reapply_concept, reapply_con_neg) = {
                            let d = calc_alg_context.process_context().con_desc(reapply_con_des);
                            (d.get_concept(), d.is_negated())
                        };
                        let op_code = calc_alg_context
                            .ontology_arenas()
                            .concept(reapply_concept)
                            .get_operator_code();
                        if op_code == CCATMOST || op_code == CCATLEAST {
                            // Faithful C++: the GENERATING concept's parameter (an ∃
                            // has parameter 0 ⇒ cardinality ≤ 1 ⇒ not absorbable).
                            let cardinality = calc_alg_context
                                .ontology_arenas()
                                .concept(concept)
                                .get_parameter()
                                + if reapply_con_neg { 1 } else { 0 };
                            if cardinality <= 1 {
                                return false;
                            }
                        }
                    }
                }
            }
        }
        true
    }

    // =======================================================================
    // Saturated-clashed flag for a concept (cpp 16438–16459).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::hasSaturatedClashedFlagForConcept`.
    /// cpp 16438–16459.
    ///
    /// Follow `concept`'s concept→saturation reference linking (for the given
    /// polarity) to its saturation individual node and report whether that node's
    /// indirect status flags carry the clashed flag.
    ///
    pub fn has_saturated_clashed_flag_for_concept(
        &mut self,
        concept: ConceptId,
        negation: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // conceptData = concept->getConceptData();
        // saturationIndiNode = nullptr;
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
            if calc_alg_context
                .process_context()
                .sat_node(saturation_indi_node)
                .indirect_status_flags
                .has_flags_code(
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                    false,
                )
            {
                return true;
            }
        }
        false
    }

    // =======================================================================
    // Cached associated-concept-set from variable-propagation bindings
    // (cpp 18088–18098) — FULLY PORTED.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindingsCached`.
    /// cpp 18088–18098.
    ///
    /// Memoising wrapper: returns the node's associated concept-set (the
    /// `QSet<QSet<CConcept*>>` used for analogous-propagation-path blocking),
    /// building it once via the sibling
    /// `getIndividualNodeAssociatedConceptsSetFromVariablePropagationBindings` and
    /// caching the result in `mCachedIndiAssociatedConceptSetHash`.
    pub fn get_individual_node_associated_concepts_set_from_variable_propagation_bindings_cached(
        &mut self,
        individual_node: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Vec<Vec<ConceptId>> {
        // C++: IndiAssociatedConceptSetCacheData& conceptSetCacheData = mCachedIndiAssociatedConceptSetHash[individualNode];
        // KONCLUDE-PORT-NOTE[ownership]: the C++ takes a `&` into the hash and mutates
        // it in place across the sibling builder call. The borrow checker forbids
        // holding that `&mut` over the `&mut self` sibling call, so we split: read the
        // `created` flag, build via the sibling when absent, then write the entry
        // back. Same key, same value, same statistic side-effects — only the borrow
        // shape differs. The `QSet<QSet<CConcept*>>` return is the insertion-ordered
        // `Vec<Vec<ConceptId>>` the cache field (`IndiAssociatedConceptSetCacheData`)
        // already stores.
        let created = self
            .cached_indi_associated_concept_set_hash
            .get(individual_node)
            .map(|d| d.created)
            .unwrap_or(false);
        if !created {
            // W3-DEFER[macro]: STATINC(SIMPLEANALOGOUSPROPAGATIONBLOCKINGCONCEPTSETSBUILDINGCOUNT, calcAlgContext)
            let concept_set = self
                .get_individual_node_associated_concepts_set_from_variable_propagation_bindings(
                    individual_node,
                    calc_alg_context,
                );
            let entry = self
                .cached_indi_associated_concept_set_hash
                .entry(*individual_node)
                .or_default();
            entry.concept_set = concept_set;
            entry.created = true;
        } else {
            // W3-DEFER[macro]: STATINC(SIMPLEANALOGOUSPROPAGATIONBLOCKINGCONCEPTSETSCACHEREUSECOUNT, calcAlgContext)
        }
        self.cached_indi_associated_concept_set_hash
            .get(individual_node)
            .map(|d| d.concept_set.clone())
            .unwrap_or_default()
    }

    // =======================================================================
    // Saturation caching establishment + validation (cpp 21674–22013).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::tryEstablishSaturationCaching`.
    /// cpp 21674–21723.
    ///
    /// If the successor's saturation node is initialised, completed and neither
    /// insufficient nor clashed, and the concept set is saturation-cache compatible
    /// (and nominal connections are reinstallable), install saturation-blocking
    /// caching on `succIndi`: record its blocking data, flag
    /// `PRFSATURATIONBLOCKINGCACHED` (+ successor-creation blocking if cardinality is
    /// unproblematic) and propagate the indirect-successor saturation-blocked flag.
    /// Returns whether caching was established.
    ///
    /// Ported LIVE (task #24 wave 2). Faithful transcription of cpp 21674–21723:
    ///
    ///   if saturationIndiNode && saturationIndiNode->isInitialized() && saturationIndiNode->isCompleted():
    ///       cachingEstablishmentPossible = false;
    ///       flags = saturationIndiNode->getIndirectStatusFlags();                       // W4-DEFER[api]
    ///       if !flags->hasFlags(INDSATFLAGINSUFFICIENT | INDSATFLAGCLASHED, false):
    ///           if validateSaturationCachingPossible(succIndi, saturationIndiNode, satCachingPossible, lastSatCachPossibleConDes, nullptr, false, ctx):
    ///               nominalNodesCompatible = true;
    ///               if flags->hasFlags(INDSATFLAGNOMINALCONNECTION, false):
    ///                   if !mConfSaturationCachingWithNominals: nominalNodesCompatible = false;
    ///                   succConnNominalSet = saturationIndiNode->getSuccessorConnectedNominalSet(false);
    ///                   if !succConnNominalSet
    ///                       || !tryInstallSaturationCachingReactivation(succIndi, succConnNominalSet, ctx):  // sibling (unit 21)
    ///                       nominalNodesCompatible = false;
    ///               if nominalNodesCompatible: cachingEstablishmentPossible = true;
    ///       succIndiConCount = succIndi->getReapplyConceptLabelSet(false)->getConceptCount();
    ///       satBlockingData = CObjectAllocator<CIndividualNodeSaturationBlockingData>::allocateAndConstruct(taskMemMan); // W6-DEFER[memory-pool]
    ///       satBlockingData->initSaturationBlockingData(succIndiConCount, *lastSatCachPossibleConDes, saturationIndiNode);
    ///       succIndi->setIndividualSaturationBlockingData(satBlockingData);
    ///       if cachingEstablishmentPossible:
    ///           STATINC(SATURATIONCACHEESTABLISHCOUNT)
    ///           succIndi->addProcessingRestrictionFlags(PRFSATURATIONBLOCKINGCACHED);
    ///           propagateIndirectSuccessorSaturationBlocked(succIndi, ctx);            // sibling
    ///           if !flags->hasFlags(INDSATFLAGCARDINALITYPROPLEMATIC, false):
    ///               succIndi->addProcessingRestrictionFlags(PRFSATURATIONSUCCESSORCREATIONBLOCKINGCACHED);
    ///           return true;
    ///   return false;
    pub fn try_establish_saturation_caching(
        &mut self,
        indi: &mut NodeId,
        succ_indi: NodeId,
        saturation_indi_node: SatNodeId,
        sat_caching_possible: &mut bool,
        last_sat_cach_possible_con_des: &mut ConDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = indi;
        type SatF = IndividualSaturationProcessNodeStatusFlags;
        let trace = std::env::var_os("KM_SAT_ABSORB_DEBUG").is_some()
            && calc_alg_context.process_context().node_count() <= 20;
        if saturation_indi_node.is_none() {
            if trace {
                eprintln!(
                    "SAT-CACHE-ESTABLISH successor={} sat=none established=false",
                    calc_alg_context
                        .process_context()
                        .node(succ_indi)
                        .individual_node_id(),
                );
            }
            return false;
        }
        let (initialized, completed, flags) = {
            let sat_node = calc_alg_context
                .process_context()
                .sat_node(saturation_indi_node);
            (
                sat_node.is_initialized(),
                sat_node.is_completed(),
                sat_node.indirect_status_flags.get_flags(),
            )
        };
        if initialized && completed {
            let mut caching_establishment_possible = false;

            if flags & (SatF::INDSATFLAGINSUFFICIENT | SatF::INDSATFLAGCLASHED) == 0 {
                let mut sat_node_ref = saturation_indi_node;
                if self.validate_saturation_caching_possible(
                    succ_indi,
                    &mut sat_node_ref,
                    Some(sat_caching_possible),
                    Some(last_sat_cach_possible_con_des),
                    Id::NONE,
                    false,
                    calc_alg_context,
                ) {
                    let mut nominal_nodes_compatible = true;

                    if flags & SatF::INDSATFLAGNOMINALCONNECTION != 0 {
                        if !self.conf_saturation_caching_with_nominals {
                            nominal_nodes_compatible = false;
                        }
                        let succ_conn_nominal_set = calc_alg_context
                            .process_context_mut()
                            .sat_node_successor_connected_nominal_set_existing(
                                saturation_indi_node,
                            );
                        if succ_conn_nominal_set.is_none() {
                            nominal_nodes_compatible = false;
                        } else if !self.try_install_saturation_caching_reactivation(
                            succ_indi,
                            succ_conn_nominal_set,
                            calc_alg_context,
                        ) {
                            nominal_nodes_compatible = false;
                        }
                    }

                    if nominal_nodes_compatible {
                        caching_establishment_possible = true;
                    }
                }
            }

            let succ_label = calc_alg_context
                .process_context()
                .node(succ_indi)
                .use_reapply_con_label_set;
            let succ_indi_con_count = if succ_label.is_some() {
                calc_alg_context
                    .process_context()
                    .label_set(succ_label)
                    .get_concept_count()
            } else {
                0
            };
            let mut sat_blocking_data = IndividualNodeSaturationBlockingData::new();
            sat_blocking_data.init_saturation_blocking_data(
                succ_indi_con_count,
                *last_sat_cach_possible_con_des,
                saturation_indi_node,
            );
            let sat_blocking_data_id = calc_alg_context
                .process_context_mut()
                .alloc_indi_sat_block_data(sat_blocking_data);
            calc_alg_context
                .process_context_mut()
                .node_mut(succ_indi)
                .set_individual_saturation_blocking_data(sat_blocking_data_id);

            if caching_establishment_possible {
                self.saturation_cache_establish_count += 1; // STATINC(SATURATIONCACHEESTABLISHCOUNT)
                calc_alg_context
                    .process_context_mut()
                    .node_mut(succ_indi)
                    .add_processing_restriction_flags(
                        IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHED,
                    );
                self.propagate_indirect_successor_saturation_blocked(succ_indi, calc_alg_context);

                if flags & SatF::INDSATFLAGCARDINALITYPROPLEMATIC == 0 {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(succ_indi)
                        .add_processing_restriction_flags(
                            IndividualProcessNode::PRF_SATURATIONSUCCESSORCREATIONBLOCKINGCACHED,
                        );
                }
                if trace {
                    eprintln!(
                        "SAT-CACHE-ESTABLISH successor={} sat={} flags={:#x} label={} cache-possible={} established=true",
                        calc_alg_context
                            .process_context()
                            .node(succ_indi)
                            .individual_node_id(),
                        saturation_indi_node.raw,
                        flags,
                        succ_indi_con_count,
                        *sat_caching_possible,
                    );
                }
                return true;
            }
        }

        if trace {
            let label = calc_alg_context
                .process_context()
                .node(succ_indi)
                .use_reapply_con_label_set;
            eprintln!(
                "SAT-CACHE-ESTABLISH successor={} sat={} flags={:#x} label={} cache-possible={} established=false",
                calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .individual_node_id(),
                saturation_indi_node.raw,
                flags,
                if label.is_some() {
                    calc_alg_context
                        .process_context()
                        .label_set(label)
                        .get_concept_count()
                } else {
                    0
                },
                *sat_caching_possible,
            );
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::validateSaturationCachingPossible`.
    /// cpp 21866–21911.
    ///
    /// Walk the node's newly added (sorted) concept descriptors down to the last
    /// previously tested one; saturation caching stays possible only while every such
    /// concept is also present (same polarity) in the saturation node's saturation
    /// label set. Updates `*satCachingPossible` and advances `*lastSatCachPossibleConDes`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ `bool* satCachingPossible` and
    /// `CConceptDescriptor** lastSatCachPossibleConDes` are NULLABLE; ported as
    /// `Option<&mut bool>` / `Option<&mut ConDescId>` to preserve the null checks.
    ///
    /// Ported LIVE (task #24 wave 2). Faithful transcription of cpp 21866–21911:
    ///
    ///   satCachingStillPossible = satCachingPossible ? *satCachingPossible : true;
    ///   if satCachingStillPossible:
    ///       if !saturationIndiNode->isCompleted(): satCachingStillPossible = false;
    ///       else:
    ///           conSet    = indi->getReapplyConceptLabelSet(false);                       // satellite
    ///           satConSet = saturationIndiNode->getReapplyConceptSaturationLabelSet(false); // W4-DEFER[api]
    ///           if conSet && satConSet:
    ///               conDesLinker = conSet->getAddingSortedConceptDescriptionLinker();
    ///               conDesIt = conDesLinker;
    ///               lastTestedConDesIt = lastSatCachPossibleConDes ? *lastSatCachPossibleConDes : nullptr;
    ///               if addedConcept && conDesIt != lastTestedConDesIt
    ///                   && (conDesIt->getConcept()==addedConcept || conDesIt->isNegated()==addedConceptNegation):
    ///                   conDesIt = conDesIt->getNext();
    ///               while conDesIt != lastTestedConDesIt && satCachingStillPossible:
    ///                   if !satConSet->hasConcept(conDesIt->getConcept(), conDesIt->isNegated()):
    ///                       satCachingStillPossible = false;
    ///                   conDesIt = conDesIt->getNext();
    ///               if lastSatCachPossibleConDes: *lastSatCachPossibleConDes = conDesLinker;
    ///           else: satCachingStillPossible = false;
    ///   if satCachingPossible: *satCachingPossible = satCachingStillPossible;
    ///   return satCachingStillPossible;
    pub fn validate_saturation_caching_possible(
        &mut self,
        indi: NodeId,
        saturation_indi_node: &mut SatNodeId,
        sat_caching_possible: Option<&mut bool>,
        last_sat_cach_possible_con_des: Option<&mut ConDescId>,
        added_concept: ConceptId,
        added_concept_negation: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut sat_caching_still_possible = match &sat_caching_possible {
            Some(p) => **p,
            None => true,
        };
        if sat_caching_still_possible {
            if !calc_alg_context
                .process_context()
                .sat_node(*saturation_indi_node)
                .is_completed()
            {
                sat_caching_still_possible = false;
            } else {
                let con_set = calc_alg_context
                    .process_context()
                    .node(indi)
                    .use_reapply_con_label_set;
                let sat_con_set = calc_alg_context
                    .process_context()
                    .sat_node(*saturation_indi_node)
                    .reapply_con_sat_label_set;
                if con_set.is_some() && sat_con_set.is_some() {
                    let pc = calc_alg_context.process_context();
                    let arenas = calc_alg_context.ontology_arenas();
                    let con_des_linker = pc
                        .label_set(con_set)
                        .get_adding_sorted_concept_description_linker();
                    let mut con_des_it = con_des_linker;
                    let last_tested_con_des_it = match &last_sat_cach_possible_con_des {
                        Some(p) => **p,
                        None => Id::NONE,
                    };
                    if added_concept.is_some()
                        && con_des_it != last_tested_con_des_it
                        && con_des_it.is_some()
                    {
                        // Faithful C++ condition (`getConcept()==addedConcept ||
                        // isNegated()==addedConceptNegation`) — the `||` is Konclude's.
                        let d = pc.con_desc(con_des_it);
                        if d.get_concept() == added_concept
                            || d.is_negated() == added_concept_negation
                        {
                            con_des_it = d.get_next_concept_descriptor();
                        }
                    }
                    // KONCLUDE-PORT-NOTE[defensive]: the `is_some()` guard has no C++
                    // twin (a pointer walk would just deref null) — the adding-sorted
                    // linker is head-grown, so `lastTested` (a previous head) is always
                    // reachable and the guard is only an arena-panic shield.
                    while con_des_it != last_tested_con_des_it
                        && con_des_it.is_some()
                        && sat_caching_still_possible
                    {
                        let (concept, negated, next) = {
                            let d = pc.con_desc(con_des_it);
                            (
                                d.get_concept(),
                                d.is_negated(),
                                d.get_next_concept_descriptor(),
                            )
                        };
                        // satConSet->hasConcept(concept, negated): tag lookup + descriptor
                        // negation compare (satellites.rs `has_concept_by_tag` semantics).
                        let con_tag = arenas.concept(concept).get_concept_tag();
                        let mut con_sat_des = Id::NONE;
                        let mut imp_reapply = Id::NONE;
                        let present = pc
                            .reapply_con_sat_label_set(sat_con_set)
                            .get_concept_saturation_descriptor_by_tag(
                                con_tag,
                                &mut con_sat_des,
                                &mut imp_reapply,
                            )
                            && con_sat_des.is_some()
                            && pc.con_sat_desc(con_sat_des).get_negation() == negated;
                        if !present {
                            if std::env::var_os("KM_SAT_ABSORB_DEBUG").is_some()
                                && pc.node_count() <= 20
                            {
                                eprintln!(
                                    "SAT-CACHE-VALIDATE-MISS successor={} sat={} concept-tag={} negated={}",
                                    pc.node(indi).individual_node_id(),
                                    saturation_indi_node.raw,
                                    con_tag,
                                    negated,
                                );
                            }
                            sat_caching_still_possible = false;
                        }
                        con_des_it = next;
                    }
                    if let Some(p) = last_sat_cach_possible_con_des {
                        *p = con_des_linker;
                    }
                } else {
                    sat_caching_still_possible = false;
                }
            }
        }
        if let Some(p) = sat_caching_possible {
            *p = sat_caching_still_possible;
        }
        sat_caching_still_possible
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getCreationSuccessorSaturationNode`.
    /// cpp 21917–22013.
    ///
    /// Resolve the saturation individual node a generating concept (or its single
    /// operand) would create, via the concept→saturation existential-successor
    /// reference linking, then — when successor-saturation-expansion-restriction
    /// resolving is on — refine it by collecting the predecessor's universal
    /// (automat-transaction) restrictions into a concept-extension map and resolving
    /// the extended saturation node.
    ///
    /// Ported LIVE (task #24 wave 2) except the extension-resolving refinement
    /// (see the body's W4-DEFER note). Faithful transcription of cpp 21917–22013:
    ///
    ///   concept = conDes->getConcept(); conceptNegation = conDes->isNegated();
    ///   existIndiNode = concept->getConceptData() ? existential-successor saturation ref linking node : nullptr;  // W4-DEFER[api]
    ///   if !existIndiNode:
    ///       // single-operand concept: resolve operand's saturation ref linking node (polarity ^ conceptNegation)
    ///   if mConfSuccessorSaturationExpansionRestrictionsResolving && existIndiNode:
    ///       extensionData = existIndiNode->getSuccessorExtensionData(false);
    ///       if extensionData && extensionData->getExtensionResolveData():
    ///           STATINC(NODESUCCESSOREXPANSIONSATURATIONRESOLVINGTRYINGCOUNT)
    ///           // collect universal restrictions from predecessor over creationRole's super-roles:
    ///           roleSuccHash = indi->getReapplyRoleSuccessorHash(false);
    ///           creationRole = conDes->getConcept()->getRole();
    ///           conSet = existIndiNode->getReapplyConceptSaturationLabelSet(false);
    ///           for roleLinkerIt in creationRole->getIndirectSuperRoleList():
    ///               if !roleLinkerIt->isNegated():
    ///                   for reapplyConceptDes in roleSuccHash->getRoleReapplyIterator(role, false):
    ///                       depTrackPoint = reapplyConceptDes->getDependencyTrackPoint();
    ///                       nondeterministically = !(depTrackPoint->getBranchingTag() <= ctx->getProcessingDataBox()->getMaximumDeterministicBranchTag()
    ///                                                || depTrackPoint == conDes->getDependencyTrackPoint());
    ///                       if !nondeterministically:
    ///                           collectReapplyAutomatTransactionsRestrictions(indi, role, reaConcept, reaConNegation, conExtensionMap, conSet, ctx); // sibling
    ///           resolvedIndiNode = getSaturationResolvedIndividualNodeExtension(resolveData, conExtensionMap, ctx);  // sibling (below)
    ///           if resolvedIndiNode && resolvedIndiNode != existIndiNode:
    ///               STATINC(NODESUCCESSOREXPANSIONSATURATIONRESOLVEDCOUNT); existIndiNode = resolvedIndiNode;
    ///   return existIndiNode;
    pub fn get_creation_successor_saturation_node(
        &mut self,
        indi: &mut NodeId,
        con_des: ConDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let _ = indi;
        // KONCLUDE-PORT-NOTE[defensive]: no C++ twin — every C++ caller passes a
        // live conDes; the arena would panic where the C++ pointer would crash.
        if con_des.is_none() {
            return Id::NONE;
        }
        let (concept, concept_negation) = {
            let d = calc_alg_context.process_context().con_desc(con_des);
            (d.get_concept(), d.is_negated())
        };
        // Resolve a (concept, negation)'s saturation node through the ontology-side
        // reference-linking chain (CConceptData → CConceptProcessData →
        // CConceptSaturationReferenceLinkingData → CSaturationConceptReferenceLinking).
        let ref_linking_of = |calc_alg_context: &CalculationAlgorithmContextBase,
                              c: ConceptId|
         -> super::super::model::concept_process::ConceptSaturationReferenceLinkingDataId {
            let arenas = calc_alg_context.ontology_arenas();
            let concept_data = arenas.concept(c).get_concept_data();
            if concept_data == INVALID {
                return Id::NONE;
            }
            arenas
                .concept_process_data(ConceptProcessDataId::new(concept_data))
                .get_concept_reference_linking()
        };

        let mut exist_indi_node: SatNodeId = Id::NONE;
        let ref_linking = ref_linking_of(calc_alg_context, concept);
        if ref_linking.is_some() {
            let ext_sat_calc_ref_link_data = calc_alg_context
                .ontology_arenas()
                .concept_saturation_reference_linking_data(ref_linking)
                .get_existential_successor_concept_saturation_reference_linking_data();
            if ext_sat_calc_ref_link_data.is_some() {
                exist_indi_node = calc_alg_context
                    .ontology_arenas()
                    .saturation_concept_reference_linking(ext_sat_calc_ref_link_data)
                    .get_individual_process_node_for_concept();
            }
        }

        if exist_indi_node.is_none() {
            // Single-operand fallback: the ∃/≥ filler's own (concept, polarity)
            // saturation node (cpp 21935–21952). The bridge's saturation seeds
            // (`build_saturation_seeds`) create exactly these per-filler nodes;
            // the existential-successor linking above is only installed by the
            // not-yet-ported precomputation job refinement.
            let operands = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            if operands.len() == 1 {
                let op_concept = operands[0].target;
                let op_con_negation = operands[0].negated ^ concept_negation;
                let op_ref_linking = ref_linking_of(calc_alg_context, op_concept);
                if op_ref_linking.is_some() {
                    let sat_calc_ref_link_data = calc_alg_context
                        .ontology_arenas()
                        .concept_saturation_reference_linking_data(op_ref_linking)
                        .get_concept_saturation_reference_linking_data(op_con_negation);
                    if sat_calc_ref_link_data.is_some() {
                        exist_indi_node = calc_alg_context
                            .ontology_arenas()
                            .saturation_concept_reference_linking(sat_calc_ref_link_data)
                            .get_individual_process_node_for_concept();
                    }
                }
            }
        }

        if self.conf_successor_saturation_expansion_restrictions_resolving
            && exist_indi_node.is_some()
        {
            let trace = std::env::var_os("KM_SAT_ABSORB_DEBUG").is_some()
                && calc_alg_context.process_context().node_count() <= 20;
            let successor_extension = calc_alg_context
                .process_context_mut()
                .sat_node_ext_successor_extension_data(exist_indi_node, false);
            if trace {
                eprintln!(
                    "SAT-CACHE-RESOLVE base={} successor-extension={}",
                    exist_indi_node.raw, successor_extension.raw,
                );
            }
            if successor_extension.is_some() {
                let resolve_data = calc_alg_context
                    .process_context()
                    .sat_indi_node_succ_ext_data(successor_extension)
                    .get_extension_resolve_data();
                if trace {
                    eprintln!("SAT-CACHE-RESOLVE base={} resolve-data={}", exist_indi_node.raw, resolve_data.raw);
                }
                if resolve_data.is_some() {
                    let creation_role = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_role();
                    let mut super_roles = calc_alg_context
                        .ontology_arenas()
                        .role(creation_role)
                        .get_indirect_super_role_list()
                        .to_vec();
                    if !super_roles
                        .iter()
                        .any(|link| !link.negated && link.target == creation_role)
                    {
                        // Konclude's indirect-super list is reflexive; bridge
                        // roles store only strict supers.
                        super_roles.insert(
                            0,
                            super::super::model::substrate::NegLink {
                                target: creation_role,
                                negated: false,
                            },
                        );
                    }
                    let saturation_label = calc_alg_context
                        .process_context()
                        .sat_node(exist_indi_node)
                        .reapply_con_sat_label_set;
                    let mut extension_map: Option<HashMap<Cint64, ConceptNegationPair>> = None;
                    let mut reapply_count = 0usize;
                    for super_role in super_roles {
                        if super_role.negated {
                            continue;
                        }
                        let mut iterator = calc_alg_context
                            .process_context_mut()
                            .node_role_reapply_iterator(*indi, super_role.target, false);
                        while iterator.has_next() {
                            let reapply = iterator.next(calc_alg_context.process_context(), true);
                            if reapply.is_none() {
                                continue;
                            }
                            reapply_count += 1;
                            let (reapply_con_des, dependency) = {
                                let descriptor =
                                    calc_alg_context.process_context().reapply_con_desc(reapply);
                                (
                                    descriptor.get_concept_descriptor(),
                                    descriptor.get_dependency_track_point(),
                                )
                            };
                            let deterministic = dependency
                                == calc_alg_context
                                    .process_context()
                                    .con_desc(con_des)
                                    .get_dependency_track_point()
                                || dependency.is_none()
                                || calc_alg_context
                                    .process_context()
                                    .track_point(dependency)
                                    .get_branching_tag()
                                    <= calc_alg_context
                                        .processing_data_box()
                                        .maximum_deterministic_branch_tag();
                            if deterministic && reapply_con_des.is_some() {
                                let (reapply_concept, reapply_negation) = {
                                    let descriptor = calc_alg_context
                                        .process_context()
                                        .con_desc(reapply_con_des);
                                    (descriptor.get_concept(), descriptor.is_negated())
                                };
                                self.collect_reapply_automat_transactions_restrictions(
                                    *indi,
                                    super_role.target,
                                    reapply_concept,
                                    reapply_negation,
                                    &mut extension_map,
                                    saturation_label.raw,
                                    calc_alg_context,
                                );
                            }
                        }
                    }
                    let resolved = self.get_saturation_resolved_individual_node_extension(
                        resolve_data,
                        extension_map.as_ref(),
                        calc_alg_context,
                    );
                    if trace {
                        let mut extensions: Vec<_> = extension_map
                            .as_ref()
                            .map(|map| {
                                map.iter()
                                    .map(|(&tag, pair)| (tag, pair.negation))
                                    .collect()
                            })
                            .unwrap_or_default();
                        extensions.sort_unstable();
                        eprintln!(
                            "SAT-CACHE-RESOLVE base={} reapply={} extensions={extensions:?} resolved={}",
                            exist_indi_node.raw, reapply_count, resolved.raw,
                        );
                    }
                    if resolved.is_some() && resolved != exist_indi_node {
                        exist_indi_node = resolved;
                    }
                }
            }
        }
        exist_indi_node
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getSaturationResolvedIndividualNodeExtension`.
    /// cpp 22054–22075.
    ///
    /// Walk the saturation extension-resolve hash for each (concept, negation) in the
    /// collected concept-extension map, following non-creating resolved-extension
    /// links, and return the last resolved saturation node found.
    ///
    /// PORT-PENDING: faithful transcription of cpp 22054–22075. Outline:
    ///
    ///   lastResolvedIndiNode = resolveData->getProcessingIndividualNode();
    ///   if conExtensionMap:
    ///       for (concept, negation) in conExtensionMap:
    ///           resolveHashData = resolveData->getIndividualNodeExtensionResolveHash(true)
    ///               ->getNonCreatingResolvedIndividualNodeExtensionData(concept, negation);
    ///           if resolveHashData.mResolveData:
    ///               STATINC(NODESUCCESSOREXPANSIONSATURATIONRESOLVEDCONCEPTCANDIDATECOUNT)
    ///               resolveData = resolveHashData.mResolveData;
    ///               if resolveData->hasProcessingIndividualNode():
    ///                   lastResolvedIndiNode = resolveData->getProcessingIndividualNode();
    ///   return lastResolvedIndiNode;
    pub fn get_saturation_resolved_individual_node_extension(
        &mut self,
        mut resolve_data: SaturationIndividualNodeExtensionResolveDataId,
        con_extension_map: Option<&HashMap<Cint64, ConceptNegationPair>>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        if resolve_data.is_none() {
            return Id::NONE;
        }
        let mut last_resolved = calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(resolve_data)
            .get_processing_individual_node();
        if let Some(extension_map) = con_extension_map {
            let mut extensions: Vec<(Cint64, ConceptNegationPair)> = extension_map
                .iter()
                .map(|(&tag, &pair)| (tag, pair))
                .collect();
            extensions.sort_unstable_by_key(|(tag, _)| *tag);
            for (_, extension) in extensions {
                let resolve_hash = calc_alg_context
                    .process_context_mut()
                    .sat_extension_resolve_hash(resolve_data, true);
                let next = calc_alg_context
                    .process_context()
                    .sat_indi_node_ext_resolve_hash(resolve_hash)
                    .get_non_creating_resolved_individual_node_extension_data(
                        extension.concept,
                        extension.negation,
                    )
                    .resolve_data;
                if next.is_some() {
                    resolve_data = next;
                    let data = calc_alg_context
                        .process_context()
                        .sat_indi_node_ext_resolve_data(resolve_data);
                    if data.has_processing_individual_node() {
                        last_resolved = data.get_processing_individual_node();
                    }
                }
            }
        }
        last_resolved
    }

    // =======================================================================
    // Representative-memory backend-cache node initialisation + processing
    // (cpp 22702–23193).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::initializeIndividualNodeWithBackendCache`.
    /// cpp 22702–22814.
    ///
    /// Initialise a node from its representative-memory backend-cache association:
    /// add every concept of the full-concept-set label (validating backend-sync
    /// continuation), add the individual's nominal assertions + nominal concept, mark
    /// the backend concept-set initialised, then — for a completely-handled
    /// association with reuseable (non-deterministic / same / different individual)
    /// label elements and an active/late reuse policy — queue reuse expansion, and
    /// always queue indirect-compatibility expansion + register for backend
    /// concept-set-label processing. Returns whether initialisation ran.
    ///
    /// PORT-PENDING: faithful transcription of cpp 22702–22814. Outline:
    ///
    ///   individual = indiNode->getNominalIndividual();
    ///   backendSyncData    = indiNode->getIndividualBackendCacheSynchronisationData(false);  // W6-DEFER[api]
    ///   locBackendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(true);
    ///   if backendSyncData:
    ///       if !locBackendSyncData: locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);  // sibling
    ///       indiAssData = locBackendSyncData->getAssocitaionData();
    ///       if indiAssData:
    ///           depTrackPoint = ctx->getBaseDependencyNode()->getContinueDependencyTrackPoint();
    ///           conceptSetLabelItem = indiAssData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
    ///           mBackendCacheHandler->visitConceptsOfAssociatedFullConceptSetLabel(indiAssData, conceptSetLabelItem,
    ///               |concept, conNegation, deterministic| {
    ///                   addConceptToIndividualSkipANDProcessing(concept, conNegation, indiNode, depTrackPoint, true, false, false, ctx);  // sibling
    ///                   validateBackendSynchronisationContinued(indiNode, backendSyncData, concept, conNegation, ctx);                    // sibling
    ///                   true }, true, false, ctx);
    ///           for conAssLinkerIt in individual->getAssertionConceptLinker():
    ///               if concept->getOperatorCode()==CCNOMINAL && (concept->getNominalIndividual()==individual || negation):
    ///                   addConceptToIndividualSkipANDProcessing(concept, negation, indiNode, depTrackPoint, true, false, false, ctx);
    ///           if nominalConcept = indiNode->getNominalIndividual()->getIndividualNominalConcept():
    ///               addConceptToIndividualSkipANDProcessing(nominalConcept, false, indiNode, depTrackPoint, true, true, false, ctx);
    ///           locBackendSyncData->setBackendConceptSetInitialized(true);
    ///           if indiAssData->isCompletelyHandled():
    ///               hasReuseableElements = (FULL_CONCEPT_SET_LABEL nondeterministic)
    ///                   || NONDETERMINISTIC_COMBINED_NEIGHBOUR_INSTANTIATED_ROLE_SET_LABEL
    ///                   || NONDETERMINISTIC_SAME_INDIVIDUAL_SET_LABEL
    ///                   || NONDETERMINISTIC_DIFFRENT_INDIVIDUAL_SET_LABEL;
    ///               reuse = mOptBackendExpansionReuse;
    ///               // late dynamic reuse activation by same-individual / neighbour counts vs config thresholds
    ///               if reuse && hasReuseableElements:
    ///                   if !mOptBackendExpansionReuse: ctx->getProcessingDataBox()->setBackendIndividualLateReuseExpansionActivated(true);
    ///                   addIndividualToBackendReuseExpansionQueue(indiNode, ctx);            // sibling
    ///           addIndividualToBackendIndirectCompatibilityExpansionQueue(indiNode, ctx);    // sibling
    ///           registerProcessedIndividualForBackendConceptSetLabel(indiNode, locBackendSyncData, indiAssData, ctx);  // below
    ///           return true;
    ///   return false;
    pub fn initialize_individual_node_with_backend_cache(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: the representative-memory backend cache subsystem (the
        // per-node sync data, the association data + label-cache-item family) reached
        // through `mBackendCacheHandler` (stub) is the W6 Cache subtree; the
        // concept-adding / validate-sync / queue-enqueue calls are siblings in later
        // units. Body PORT-PENDING per outline.
        let _ = (indi_node, calc_alg_context);
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher`
    /// (the association-data overload). cpp 22817–22823.
    ///
    /// Build the concept-set-label processing hasher from the association's
    /// full-concept-set label item + the neighbour-instantiated-role-set-combination
    /// label item.
    ///
    /// KONCLUDE-PORT-NOTE[overload]: two overloads (by association-data vs by node);
    /// named `*_from_assoc` and the base name. W6-DEFER[api]: the
    /// `CBackendRepresentativeMemoryCacheIndividualAssociationData` / label-cache-item
    /// and the returned `CIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher`
    /// are the W6 backend cache, carried opaque as `Cint64`.
    ///
    /// PORT-PENDING: faithful transcription of cpp 22817–22823. Outline:
    ///
    ///   conceptSetLabelItem = indiAssData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
    ///   neighbourRoleSetCombinationLabelItem = indiAssData->getLabelCacheEntry(NEIGHBOUR_INSTANTIATED_ROLE_SET_COMBINATION_LABEL);
    ///   // TODO(Konclude): also consider outgoing data-property set labels
    ///   return CIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher(conceptSetLabelItem, neighbourRoleSetCombinationLabelItem);
    pub fn get_individual_representative_backend_cache_concept_set_label_processing_hasher_from_assoc(
        &mut self,
        indi_ass_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // W6-DEFER[api]: backend association data + hasher unported.
        let _ = (indi_ass_data, calc_alg_context);
        super::super::model::substrate::INVALID
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher`
    /// (the node overload). cpp 22825–22829.
    /// KONCLUDE-PORT-NOTE[overload]: see `*_from_assoc`.
    ///
    /// PORT-PENDING: faithful transcription of cpp 22825–22829. Outline:
    ///
    ///   backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);   // W6-DEFER[api]
    ///   indiAssData = backendSyncData->getAssocitaionData();
    ///   return getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher(indiAssData, ctx);  // *_from_assoc
    pub fn get_individual_representative_backend_cache_concept_set_label_processing_hasher(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // W6-DEFER[api]: backend sync/association data unported.
        let _ = (indi_node, calc_alg_context);
        super::super::model::substrate::INVALID
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::markIndividualNodeBackendNonConceptSetRelatedProcessing`.
    /// cpp 22831–22909.
    ///
    /// Mark a node as having backend processing that is NOT only concept-set-label
    /// related; when delayed backend initialisation is on, decrement the
    /// concept-set-label processing group's only-concept-set count and, if it drops to
    /// zero, drain the group's root/branch queuing-node linkers into the delayed
    /// backend-initialisation processing queue (flagging each queued node's localized
    /// sync data init-queued). Returns whether the mark was newly set.
    ///
    /// PORT-PENDING: faithful transcription of cpp 22831–22909. Outline:
    ///
    ///   backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);  // W6-DEFER[api]
    ///   if backendSyncData && !backendSyncData->hasNonConceptSetBackendLabelRelatedProcessing() && backendSyncData->getAssocitaionData():
    ///       locIndiNode = getLocalizedIndividual(indiNode, false, ctx);                             // sibling
    ///       locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(locIndiNode, ctx);
    ///       locBackendSyncData->setNonConceptSetBackendLabelRelatedProcessing(true);
    ///       if mOptDelayedBackendInitializiation:
    ///           hash = ctx->getProcessingDataBox()->getBackendCacheConceptSetLabelProcessingHash(true);
    ///           hasher = getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher(indiNode, ctx);  // above
    ///           processingData = hash[hasher];
    ///           processingData.decOnlyConceptSetProcessedCount(1);
    ///           if processingData.getOnlyConceptSetProcessedCount() <= 0:
    ///               delayedBackendInitProcessingQueue = ctx->getProcessingDataBox()->getDelayedBackendConceptSetLabelProcessingInitializationQueue(true);
    ///               // drain rootQueuingNodeLinker then branchQueuingNodeLinker while queuedNodeInitializingCount <= 0:
    ///               //   getUpToDateIndividual / isBackendConceptSetInitialized{,ationQueued} checks,
    ///               //   addIndividualNodeQueuingLinker / insertIndiviudalProcessNode, setBackendConceptSetInitializationQueued(true),
    ///               //   incQueuedNodeInitializingCount(1), advance the linker
    ///       return true;
    ///   return false;
    pub fn mark_individual_node_backend_non_concept_set_related_processing(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: the per-node backend sync data, the concept-set-label
        // processing hash + its queuing-node linkers, the delayed-backend-init queue,
        // and the localized-individual siblings are the W6 Cache subtree. Body
        // PORT-PENDING per outline.
        let _ = (indi_node, calc_alg_context);
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::tryDelayIndividualNodeInitializationWithBackendConceptSetLabel`.
    /// cpp 22921–22966.
    ///
    /// Try to defer a node's backend init by registering it under the shared
    /// concept-set-label processing group: refuse for indirectly-connected or
    /// cardinality-extended associations; otherwise, once delaying is registered,
    /// queue the node (root linker when the delayed queue is the root, else a branch
    /// linker) iff another node in the group is still concept-set processing or
    /// queued. Returns whether the init was delayed.
    ///
    /// PORT-PENDING: faithful transcription of cpp 22921–22966. Outline:
    ///
    ///   individual = indiNode->getNominalIndividual();
    ///   backendSyncData = indiNode->getIndividualBackendCacheSynchronisationData(false);   // W6-DEFER[api]
    ///   indiAssData = backendSyncData->getAssocitaionData();
    ///   if indiAssData->hasIndirectlyConnectedIndividualIntegration(): return false;
    ///   conSetLabelItem = indiAssData->getLabelCacheEntry(FULL_CONCEPT_SET_LABEL);
    ///   if conSetLabelItem->getExtensionData(CARDINALITY_HASH): return false;
    ///   if !backendSyncData->isBackendConceptSetInitializationDelayingRegistered():
    ///       locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);
    ///       locBackendSyncData->setBackendConceptSetInitializationDelayingRegistered(true);
    ///       hash = ctx->getProcessingDataBox()->getBackendCacheConceptSetLabelProcessingHash(true);
    ///       processingData = hash[getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher(indiNode, ctx)];
    ///       if processingData.getOnlyConceptSetProcessedCount() <= 0 && processingData.getQueuedNodeInitializingCount() <= 0:
    ///           return false;
    ///       else:
    ///           delayedBackendInitProcessingQueue = ctx->getProcessingDataBox()->getDelayedBackendConceptSetLabelProcessingInitializationQueue(true);
    ///           if mOptDelayedBackendInitializiationWithRootLinkers && delayedBackendInitProcessingQueue->isRoot():
    ///               queuingNodeLinker = alloc CIndividualRepresentativeBackendCacheConceptSetLabelNodeQueuingLinker; set node; processingData.appendRootQueuingNodeLinker(...);
    ///           else:
    ///               indiNodeLinker = alloc CXLinker<CIndividualProcessNode*>; initLinker(indiNode); processingData.appendBranchQueuingNodeLinker(...);
    ///           return true;
    ///   return false;
    pub fn try_delay_individual_node_initialization_with_backend_concept_set_label(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: backend sync/association data + the concept-set-label
        // processing hash + queuing linkers (W6-DEFER[memory-pool]) are unported.
        // Body PORT-PENDING per outline.
        let _ = (indi_node, calc_alg_context);
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::registerProcessedIndividualForBackendConceptSetLabel`.
    /// cpp 22971–22984.
    ///
    /// When delayed backend init is on, register a processed node in its concept-set
    /// label processing group: append a pooled node linker as the group's initialized
    /// linker (also stored on the localized sync data) and bump the
    /// only-concept-set-processed count. Always returns true.
    ///
    /// PORT-PENDING: faithful transcription of cpp 22971–22984. Outline:
    ///
    ///   if mOptDelayedBackendInitializiation:
    ///       hash = ctx->getProcessingDataBox()->getBackendCacheConceptSetLabelProcessingHash(true);
    ///       processingData = hash[getIndividualRepresentativeBackendCacheConceptSetLabelProcessingHasher(individual, ctx)];
    ///       individualNodeLinker = alloc CXLinker<CIndividualProcessNode*>; initLinker(individual);   // W6-DEFER[memory-pool]
    ///       locBackendSyncData->setConceptSetLabelProcessedNodeLinker(individualNodeLinker);
    ///       processingData.appendInitializedNodeLinker(individualNodeLinker);
    ///       processingData.incOnlyConceptSetProcessedCount();
    ///   return true;
    pub fn register_processed_individual_for_backend_concept_set_label(
        &mut self,
        individual: NodeId,
        loc_backend_sync_data: Cint64,
        indi_ass_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W6-DEFER[api]: the concept-set-label processing hash + initialized node
        // linker (W6-DEFER[memory-pool]) + localized sync data are unported. Body
        // PORT-PENDING per outline; the C++ tail return is `true`.
        let _ = (
            individual,
            loc_backend_sync_data,
            indi_ass_data,
            calc_alg_context,
        );
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getBackendCacheRoleRepresentativeNeighbourCount`.
    /// cpp 23159–23193.
    ///
    /// Return the (representative) neighbour count for `role` from the backend cache:
    /// reuse the cached per-role count when present; otherwise ask the backend cache
    /// handler for the raw neighbour count and — when representative counting is on
    /// and the raw count exceeds 1 — recompute the representative count by visiting
    /// the role's neighbour individuals and excluding those with a deterministic
    /// same-individual merging, caching the result.
    ///
    /// PORT-PENDING: faithful transcription of cpp 23159–23193. Outline:
    ///
    ///   linkCount = 0; hash = backendSyncData->getRoleRepresentativeNeighbourCountHash(false);   // W6-DEFER[api]
    ///   if hash && hash->contains(role): linkCount = hash->value(role);
    ///   else:
    ///       linkCount = mBackendCacheHandler->getNeighbourCountForRole(assocData, role, ctx);
    ///       if !mConfCardinalityNeighbourExpansionRepresentativeCounting || linkCount <= 1: return linkCount;
    ///       else:
    ///           hash = backendSyncData->getRoleRepresentativeNeighbourCountHash(false);
    ///           if !hash || !hash->contains(role):
    ///               repNeighbourLinkCount = 0;
    ///               locBackendSyncData = getLocalizedIndividualBackendCacheSnychronisationData(indiNode, ctx);
    ///               hash = locBackendSyncData->getRoleRepresentativeNeighbourCountHash(true);
    ///               mBackendCacheHandler->visitNeighbourIndividualIdsForRole(assocData, role, |neighbourIndiId, neighbourRoleSetLabel, deterministic| {
    ///                   detNeighbourAssData = mBackendCacheHandler->getIndividualAssociationData(neighbourIndiId, false, ctx);
    ///                   if !detNeighbourAssData || !detNeighbourAssData->hasDeterministicSameIndividualMerging(): repNeighbourLinkCount++;
    ///                   true }, false, ctx);
    ///               hash->insert(role, repNeighbourLinkCount);
    ///               if linkCount != repNeighbourLinkCount: linkCount = repNeighbourLinkCount;
    ///           else: linkCount = hash->value(role);
    ///   return linkCount;
    pub fn get_backend_cache_role_representative_neighbour_count(
        &mut self,
        indi_node: NodeId,
        backend_sync_data: Cint64,
        assoc_data: Cint64,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // W6-DEFER[api]: the per-node backend sync data role-representative-neighbour
        // count hash, the association data, and `mBackendCacheHandler`
        // (getNeighbourCountForRole / visitNeighbourIndividualIdsForRole /
        // getIndividualAssociationData) are the W6 Cache subtree. Body PORT-PENDING
        // per outline; the C++ default is `0`.
        let _ = (
            indi_node,
            backend_sync_data,
            assoc_data,
            role,
            calc_alg_context,
        );
        0
    }
}
