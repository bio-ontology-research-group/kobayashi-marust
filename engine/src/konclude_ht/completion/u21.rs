//! `completion::u21` — Caching / backend-cache / saturation family, batch
//! (port unit #21 of 36).
//!
//! Faithful port of the 21 methods that the manifest (`01-completion-methods.md`,
//! "Unit 21") groups under the satisfiable-/saturation-/completion-graph caching
//! subsystem of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) per method are noted on each item.
//!
//! Methods (cpp order):
//!   * `installSaturationCachingReactivation`                        [2100–2126]
//!   * `tryInstallSaturationCachingReactivation`                     [2130–2149]
//!   * `isIndividualNodeCompletionGraphCached`                       [4210–4213]
//!   * `detectIndividualNodeBackendCacheSynchronized`               [4230–4280]
//!   * `clearCompletionGraphCaching`                                 [4284–4314]
//!   * `detectIndividualNodeCompletionGraphCached`                   [4317–4344]
//!   * `commitCacheMessages`                                         [4350–4359]
//!   * `testIndividualNodeUnsatisfiableCached`                       [4363–4392]
//!   * `cacheSatisfiableIndividualNodes`                             [4503–4625]
//!   * `testAllSuccessorsProcessedAndWriteSatisfiableCache`         [4670–4703]
//!   * `writeSatisfiableCachedIndividualNodesOfUnsatisfiableBranch`  [4706–4734]
//!   * `detectIndividualNodeSaturationCached`                        [4750–4817]
//!   * `detectIndividualNodeSatisfiableExpandedCached`              [4833–4949]
//!   * `addSatisfiableCachedAbsorbedDisjunctionConcept`             [6298–6304]
//!   * `addSatisfiableCachedAbsorbedGeneratingConcept`              [6308–6314]
//!   * `propagateIndirectSuccessorSatisfiableCached`                [6321–6323]
//!   * `isSatisfiableCachedAutomatConceptCompatible`                [6332–6356]
//!   * `isSatisfiableCachedCompatible`                              [6359–6420]
//!   * `expandCachedConcepts`                                       [6423–6482]
//!   * `reactivateIndirectSatisfiableCachedSuccessors`             [6527–6546]
//!   * `reactivateIndirectSaturationCachedSuccessors`             [6548–6567]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. A `CIndividualProcessNode*` (value or
//! in-out `*&`) parameter becomes `NodeId`; the in-out localisation pattern
//! (`individualNode = getLocalizedIndividual(individualNode, …)`) becomes a `mut`
//! local rebind. The per-test node/descriptor/label-set arenas are reached
//! through the context as `calc_alg_context.process_context()` / `_mut()`, the
//! databox as `calc_alg_context.processing_data_box{,_mut}()`, the static
//! terminology as `calc_alg_context.ontology_arenas()`. Sibling algorithm methods
//! are `self.x(…)`. Node processing-restriction-flag masks are the `Node::PRF_*`
//! associated consts.
//!
//! Deferral landscape. This is the caching family, so most bodies bottom out in
//! the W6 Cache subtree that is NOT yet ported:
//!   * the satisfiable-expander / saturation-node-expansion / unsatisfiable /
//!     completion-graph cache handlers (`mCompGraphCacheHandler`,
//!     `getUsedSatisfiableExpanderCacheHandler()`, … — `Id<…CacheHandler>` stub
//!     markers; their `cacheIndividualNodeSatisfiable` / `isIndividualNodeExpandCached`
//!     / `isNodeSatisfiableCached` / `commitCacheMessages` calls are `// W6-DEFER[api]`);
//!   * the cache entries / cache-value linkers (`CSignatureSatisfiableExpanderCacheEntry`,
//!     `CExpanderBranchedLinker`, `CExpanderCacheValueLinker`, `CCacheValue`,
//!     `CSaturationNodeAssociatedConceptExpansion`) and the saturation nominal sets
//!     (`CSaturationNodeAssociatedDependentNominalSet`, `CSuccessorConnectedNominalSet`);
//!   * the per-node processing queues (`CIndividualUnsortedProcessingQueue`,
//!     `CIndividualReactivationProcessingQueue`) and the node vector
//!     (`CIndividualProcessNodeVector`) — process-layer `stub!` markers, no arena yet;
//!   * the `CCalculationClashProcessingException` clash throw (`// PORT-PENDING[exceptions]`);
//!   * the successor / successor-role iterators (`process::stubs` zero-size markers,
//!     no `hasNext`/`nextLink` yet) — loops over them are deferred in place.
//! Substrate-portable bodies (flag logic, the `detect*` drivers, the
//! `*AutomatConceptCompatible` recursion, the propagate forwarder) are ported in
//! full; the cache-/iterator-bound remainder is held `// PORT-PENDING` with a
//! faithful structural transcription. Logic is documented, never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

use std::collections::HashSet;

use super::super::cache::context::CacheContext;
use super::super::cache::satnode::DependentNominalSetId;
use super::super::model::op::{CCALL, CCAQSOME, CCATLEAST, CCATMOST, CCSOME};
use super::super::model::op::{
    CCFS_ALL_TYPE, CCFS_AQALL_TYPE, CCFS_AQAND_AQALL_TYPE, CCFS_AQAND_TYPE,
};
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::RoleId;
use super::super::process::node::IndividualProcessNode as Node;
use super::super::process::reapply_sat::ReapplyConceptDescriptor;
use super::super::process::stubs::NominalConnectionSetId;
use super::super::process::{
    ClashDescId, ConDescId, LabelSetId, NodeId, RestrictionSpecId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;
use super::stubs::SatisfiableExpanderCacheHandler;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Saturation-caching reactivation install (cpp 2100–2149).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::installSaturationCachingReactivation`.
    /// cpp 2100–2126.
    ///
    /// For every dependent nominal of a saturation-cached node, record `indiProcNode`
    /// for reactivation when that nominal's completion-graph caching is lost — either
    /// onto the nominal's localized `CNominalCachingLossReactivationData`, or, if the
    /// nominal is itself no longer caching-eligible / already reactivated, onto the
    /// databox's global nominal-caching-loss reactivation queue.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `nominalSet` is owned by the cache arena, so
    /// the Rust port threads `cache_context` explicitly where the C++ pointer was
    /// directly dereferenceable.
    pub fn install_saturation_caching_reactivation(
        &mut self,
        indi_proc_node: NodeId,
        nominal_set: DependentNominalSetId,
        cache_context: &CacheContext,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if nominal_set.is_some() {
            let nominal_ids = cache_context
                .dependent_nominal_set(nominal_set)
                .nominal_set
                .clone();
            for nominal_id in nominal_ids {
                let nominal_node =
                    self.get_up_to_date_individual_by_id(-nominal_id, calc_alg_context);
                if nominal_node.is_none() {
                    continue;
                }
                calc_alg_context
                    .process_context_mut()
                    .node_mut(nominal_node)
                    .set_caching_loss_node_reactivation_installed(true);

                let loc_nominal_node =
                    self.get_localized_individual(nominal_node, true, calc_alg_context);
                let loc_nominal_reactivation_data = calc_alg_context
                    .process_context_mut()
                    .node_nominal_caching_loss_reactivation_data(loc_nominal_node, true);

                let mut nominal_based_caching_possible =
                    Self::nominal_based_caching_possible(nominal_node, calc_alg_context);
                if calc_alg_context
                    .process_context()
                    .nominal_caching_loss_reactivation_data(loc_nominal_reactivation_data)
                    .has_reactivated()
                {
                    nominal_based_caching_possible = false;
                }

                if !nominal_based_caching_possible {
                    let reactivation_queue = calc_alg_context
                        .get_nominal_caching_loss_reactivation_processing_queue(true);
                    calc_alg_context
                        .process_context_mut()
                        .indi_unsorted_proc_queue_mut(reactivation_queue)
                        .insert_indiviudal_process_node(indi_proc_node);
                } else {
                    calc_alg_context
                        .process_context_mut()
                        .nominal_caching_loss_reactivation_data_mut(loc_nominal_reactivation_data)
                        .add_reactivation_individual_node(indi_proc_node);
                }
            }
        }
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::tryInstallSaturationCachingReactivation`.
    /// cpp 2130–2149.
    ///
    /// Like `install_saturation_caching_reactivation` but ABORTS (returns false)
    /// the moment a successor-connected nominal is found to be no longer
    /// caching-eligible or already reactivated; otherwise installs the reactivation
    /// on every nominal's localized reactivation data and returns true.
    ///
    pub fn try_install_saturation_caching_reactivation(
        &mut self,
        indi_proc_node: NodeId,
        nominal_set: NominalConnectionSetId, // CSuccessorConnectedNominalSet*
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if nominal_set.is_some() {
            let nominal_ids = calc_alg_context
                .process_context()
                .nominal_conn_set(nominal_set)
                .iter_snapshot();
            for nominal_id in nominal_ids {
                let nominal_node =
                    self.get_up_to_date_individual_by_id(-nominal_id, calc_alg_context);
                if nominal_node.is_none()
                    || !Self::nominal_based_caching_possible(nominal_node, calc_alg_context)
                {
                    return false;
                }
                calc_alg_context
                    .process_context_mut()
                    .node_mut(nominal_node)
                    .set_caching_loss_node_reactivation_installed(true);

                let nominal_reactivation_data = calc_alg_context
                    .process_context_mut()
                    .node_nominal_caching_loss_reactivation_data(nominal_node, false);
                if nominal_reactivation_data.is_some()
                    && calc_alg_context
                        .process_context()
                        .nominal_caching_loss_reactivation_data(nominal_reactivation_data)
                        .has_reactivated()
                {
                    return false;
                }

                let loc_nominal_node =
                    self.get_localized_individual(nominal_node, true, calc_alg_context);
                let loc_nominal_reactivation_data = calc_alg_context
                    .process_context_mut()
                    .node_nominal_caching_loss_reactivation_data(loc_nominal_node, true);
                calc_alg_context
                    .process_context_mut()
                    .nominal_caching_loss_reactivation_data_mut(loc_nominal_reactivation_data)
                    .add_reactivation_individual_node(indi_proc_node);
            }
        }
        true
    }

    fn nominal_based_caching_possible(
        nominal_node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let nominal_node = calc_alg_context.process_context().node(nominal_node);
        !nominal_node.has_partial_processing_restriction_flags(
            Node::PRF_COMPLETIONGRAPHCACHINGINVALID | Node::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
        ) && (nominal_node
            .has_partial_processing_restriction_flags(Node::PRF_COMPLETIONGRAPHCACHED)
            || nominal_node.has_partial_processing_restriction_flags(
                Node::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED,
            ))
    }

    // =======================================================================
    // Completion-graph caching detection / clearing (cpp 4210–4344).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isIndividualNodeCompletionGraphCached`.
    /// cpp 4210–4213.
    pub fn is_individual_node_completion_graph_cached(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        self.detect_individual_node_completion_graph_cached(individual_node, calc_alg_context);
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::detectIndividualNodeBackendCacheSynchronized`.
    /// cpp 4230–4280.
    ///
    /// Re-validates each backend-synchronisation processing-restriction flag of a
    /// node that was previously marked backend-synchronised, but only when it was
    /// directly modified since (`PRFRETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED`):
    /// the concept-set synchronisation, the same-merged / neighbour-expansion /
    /// cardinality / indirect-nominal blocking-criticality re-tests each clear their
    /// blocking flag when satisfied. Finally re-checks nominal-caching-loss
    /// reactivation. Returns whether the node is still concept-set backend-synchronised.
    pub fn detect_individual_node_backend_cache_synchronized(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut synchronized = false;
        if calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                Node::PRF_SYNCHRONIZEDBACKEND
                    | Node::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
                    | Node::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
                    | Node::PRF_SYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION
                    | Node::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED,
            )
        {
            if calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    Node::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
                )
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .clear_processing_restriction_flags(
                        Node::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
                    );

                if calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .has_partial_processing_restriction_flags(Node::PRF_SYNCHRONIZEDBACKEND)
                {
                    if !self.test_individual_node_backend_cache_concepts_synchronization(
                        individual_node,
                        calc_alg_context,
                    ) {
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(individual_node)
                            .clear_processing_restriction_flags(Node::PRF_SYNCHRONIZEDBACKEND);
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(individual_node)
                            .clear_processing_restriction_flags(
                                Node::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED,
                            );
                    }
                }

                if calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
                    )
                {
                    if self.test_individual_node_backend_cache_same_merged_blocking_critical(
                        individual_node,
                        calc_alg_context,
                    ) {
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(individual_node)
                            .clear_processing_restriction_flags(
                                Node::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
                            );
                    }
                }

                if calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
                    )
                {
                    if self
                        .test_individual_node_backend_cache_neighbour_expansion_blocking_critical(
                            individual_node,
                            calc_alg_context,
                        )
                    {
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(individual_node)
                            .clear_processing_restriction_flags(
                                Node::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
                            );
                    }
                }

                if calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
                            | Node::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED,
                    )
                {
                    if self
                        .test_individual_node_backend_cache_expansion_blocking_critical_cardinality(
                            individual_node,
                            calc_alg_context,
                        )
                    {
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(individual_node)
                            .clear_processing_restriction_flags(
                                Node::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED,
                            );
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(individual_node)
                            .clear_processing_restriction_flags(
                                Node::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
                            );
                    }
                }

                if calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED,
                    )
                {
                    if self.test_individual_node_backend_cache_nominal_indirect_connection_blocking_critical(individual_node, calc_alg_context) {
                        calc_alg_context.process_context_mut().node_mut(individual_node)
                            .clear_processing_restriction_flags(Node::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED);
                    }
                }

                // TODO (Konclude comment): use same condition as indirectly connected
                // individual integration check
                if !calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED,
                    )
                {
                    if calc_alg_context
                        .process_context()
                        .node(individual_node)
                        .is_caching_loss_node_reactivation_installed()
                    {
                        self.check_individual_nodes_reactivation_due_to_nominal_caching_loss(
                            individual_node,
                            calc_alg_context,
                        );
                    }
                }
            }
        }
        synchronized = calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(Node::PRF_SYNCHRONIZEDBACKEND);
        synchronized
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::clearCompletionGraphCaching`.
    /// cpp 4284–4314.
    ///
    /// Invalidate the completion-graph caching of a node: track its extended
    /// dependence, optionally record it as a caching-updated blockable node, and if
    /// it was completion-graph cached, reapply its absorbed disjunction / generating
    /// concepts, mark it `…CACHINGINVALIDATED`, run nominal-caching-loss reactivation
    /// if installed, and finally collect the cache handler's reactivation individuals
    /// onto the (late or early) reactivation queue.
    pub fn clear_completion_graph_caching(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let indi_id = calc_alg_context
            .process_context()
            .node(individual_node)
            .individual_node_id();
        self.track_individual_extended_dependence(indi_id, calc_alg_context);

        if self.conf_collect_caching_updated_blockable_indi_nodes
            && calc_alg_context
                .process_context()
                .node(individual_node)
                .is_blockable_individual()
        {
            // CXLinker<CIndividualProcessNode*>* updatedCachedIndiNodeLinker =
            //     CObjectAllocator<…>::allocateAndConstruct(taskMemMan)->initLinker(individualNode);
            // KONCLUDE-PORT-NOTE[memory-pool]: the intrusive single-node linker becomes
            // the W2 `Vec<NodeId>` head-front linker the databox setter expects.
            calc_alg_context
                .processing_data_box_mut()
                .add_blockable_individual_node_updated_linker(vec![individual_node]);
        }

        if calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(Node::PRF_COMPLETIONGRAPHCACHED)
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual_node)
                .clear_processing_restriction_flags(Node::PRF_COMPLETIONGRAPHCACHED);
            self.reapply_satisfiable_cached_absorbed_disjunction_concepts(
                individual_node,
                calc_alg_context,
            );
            self.reapply_satisfiable_cached_absorbed_generating_concepts(
                individual_node,
                calc_alg_context,
            );
        }
        calc_alg_context
            .process_context_mut()
            .node_mut(individual_node)
            .add_processing_restriction_flags(Node::PRF_COMPLETIONGRAPHCACHINGINVALIDATED);

        if calc_alg_context
            .process_context()
            .node(individual_node)
            .is_caching_loss_node_reactivation_installed()
        {
            self.check_individual_nodes_reactivation_due_to_nominal_caching_loss(
                individual_node,
                calc_alg_context,
            );
        }

        // CIndividualReactivationProcessingQueue* reactProcQueue =
        //     mConfDelayCompletionGraphCachingReactivation
        //         ? processingDataBox->getLateIndividualReactivationProcessingQueue(true)
        //         : processingDataBox->getEarlyIndividualReactivationProcessingQueue(true);
        let _react_proc_queue = if self.conf_delay_completion_graph_caching_reactivation {
            calc_alg_context.late_individual_reactivation_processing_queue(true)
        } else {
            calc_alg_context.early_individual_reactivation_processing_queue(true)
        };
        // W6-DEFER[api]: bool reactivatedIndis =
        //     mCompGraphCacheHandler->getReactivationIndividuals(individualNode, reactProcQueue, calcAlgContext);
        let _reactivated_indis = false;
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::detectIndividualNodeCompletionGraphCached`.
    /// cpp 4317–4344.
    ///
    /// When completion-graph caching is enabled and the node is in the cached id
    /// range and not invalidated, consult the completion-graph cache handler for
    /// consistence-blocking; on a miss clear the caching, on a hit mark the node
    /// `…COMPLETIONGRAPHCACHED`.
    pub fn detect_individual_node_completion_graph_cached(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut indi_node_comp_graph_cached = false;
        if self.comp_graph_cache_handler.is_some() && self.conf_completion_graph_caching {
            let max_cached_id = calc_alg_context
                .base
                .max_completion_graph_cached_individual_node_id();
            if !calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    Node::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
                )
                && calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .individual_node_id()
                    <= max_cached_id
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .add_processing_restriction_flags(Node::PRF_COMPLETIONGRAPHCACHEDNODELOCATED);

                if calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_RETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED,
                    )
                {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(individual_node)
                        .clear_processing_restriction_flags(
                            Node::PRF_RETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED,
                        );
                }

                if !calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_COMPLETIONGRAPHCACHINGINVALID
                            | Node::PRF_INVALIDBLOCKINGORCACHING,
                    )
                {
                    let mut concept_set_extended = false;
                    // W6-DEFER[api]: indiNodeCompGraphCached =
                    //     mCompGraphCacheHandler->isIndividualNodeCompletionGraphConsistenceBlocked(
                    //         individualNode, conceptSetExtended, calcAlgContext);
                    indi_node_comp_graph_cached = false;
                    if concept_set_extended {
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(individual_node)
                            .add_processing_restriction_flags(
                                Node::PRF_COMPLETIONGRAPHCACHEDNODEEXTENDED,
                            );
                    }
                }
                if !indi_node_comp_graph_cached {
                    self.clear_completion_graph_caching(individual_node, calc_alg_context);
                } else {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(individual_node)
                        .add_processing_restriction_flags(Node::PRF_COMPLETIONGRAPHCACHED);
                }
            }
        }
        indi_node_comp_graph_cached
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::commitCacheMessages`.
    /// cpp 4350–4359.
    pub fn commit_cache_messages(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // CSatisfiableExpanderCacheHandler* satExpHandler = calcAlgContext->getUsedSatisfiableExpanderCacheHandler();
        if calc_alg_context.base.used_sat_exp_cache_handler.is_some() {
            // W6-DEFER[api]: satExpHandler->commitCacheMessages(calcAlgContext);
        }
        // CSaturationNodeExpansionCacheHandler* satNodeExpHandler = calcAlgContext->getUsedSaturationNodeExpansionCacheHandler();
        if calc_alg_context
            .base
            .used_sat_node_exp_cache_handler
            .is_some()
        {
            if let Some(mut handler_state) =
                calc_alg_context.take_used_saturation_node_expansion_cache_handler()
            {
                handler_state
                    .handler
                    .commit_cache_messages(calc_alg_context, &mut handler_state.cache_context);
                calc_alg_context
                    .restore_used_saturation_node_expansion_cache_handler(handler_state);
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testIndividualNodeUnsatisfiableCached`.
    /// cpp 4363–4392.
    ///
    /// If unsat caching is enabled and the node's concept set changed since the last
    /// probe, query the unsatisfiable cache; on a (signature-gated) hit raise the
    /// clash-processing exception with the cached / freshly-built clash descriptors.
    ///
    /// KONCLUDE-PORT-NOTE[exceptions]: `throw CCalculationClashProcessingException`
    /// is represented by `calc_alg_context.raise_clash`.
    pub fn test_individual_node_unsatisfiable_cached(
        &mut self,
        mut individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.conf_test_occur_unsat_cached {
            let label_set_id = calc_alg_context
                .process_context_mut()
                .node_mut(individual_node)
                .get_reapply_concept_label_set(false);
            let con_set_size = if label_set_id.is_some() {
                calc_alg_context
                    .process_context()
                    .label_set(label_set_id)
                    .get_concept_count()
            } else {
                0
            };
            if self.last_unsat_cache_tested_indi_node != individual_node
                && con_set_size != self.last_unsat_cache_tested_indi_node_concept_set_size
            {
                // CUnsatisfiableCacheHandler* unsatCacheHandler = calcAlgContext->getUsedUnsatisfiableCacheHandler();
                let mut clash_descriptors: ClashDescId = Id::NONE;
                if let Some(mut handler_state) =
                    calc_alg_context.take_used_unsatisfiable_cache_handler()
                {
                    // KONCLUCE_TASK_ALGORITHM_TIME_MEASURE_INSTRUCTION(mUnsatCacheRetrieval.start());  // W3-DEFER[api]
                    let unsat_cached = handler_state
                        .handler
                        .is_individual_node_unsatisfiable_cached(
                            individual_node,
                            &mut clash_descriptors,
                            calc_alg_context,
                            &mut handler_state.cache_context,
                        );
                    calc_alg_context.restore_used_unsatisfiable_cache_handler(handler_state);
                    // STATINCM(TIMEUNSATCACHERETRIVAL, …);  // W3-DEFER[api]
                    if unsat_cached {
                        let signature_value = calc_alg_context
                            .process_context()
                            .label_set(label_set_id)
                            .get_concept_signature_value();
                        if !self.conf_unsat_caching_use_node_signature_set
                            || self.unsat_caching_signature_set.contains(&signature_value)
                        {
                            if self.conf_unsat_caching_use_full_node_dependency {
                                clash_descriptors = self.create_clashed_individual_node_descriptor(
                                    Id::NONE,
                                    &mut individual_node,
                                    calc_alg_context,
                                );
                            }
                            // STATINC(UNSATCACHEUSEDCOUNT, …);  // W3-DEFER[api]
                            calc_alg_context.raise_clash(clash_descriptors);
                            return;
                        }
                    }
                }
                self.last_unsat_cache_tested_indi_node = individual_node;
                self.last_unsat_cache_tested_indi_node_concept_set_size = con_set_size;
            }
        }
    }

    // =======================================================================
    // Satisfiable-node caching writers (cpp 4503–4734).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::cacheSatisfiableIndividualNodes`.
    /// cpp 4503–4625.
    ///
    /// Walk all (non-nominal, not blocker-flag-invalidated, not nominal-connected)
    /// individual nodes of the completed graph and write each into the satisfiable
    /// expander cache and/or the saturation-node satisfiability-expansion cache,
    /// after localising. With `mConfCollectCachingUpdatedBlockableIndiNodes` the
    /// updated-blockable-node linker is swept first, then the residual id range.
    ///
    /// PORT-PENDING: the iteration bound comes from the unported
    /// `CIndividualProcessNodeVector` and every write bottoms out in the W6 cache
    /// handlers (`satisfiableExpHandler->cacheIndividualNodeSatisfiable`,
    /// `saturationExpHandler->tryNodeSatisfiableCaching`). Faithful outline:
    ///
    ///   nodeCached = false;
    ///   satExpHandler = ctx->getUsedSatisfiableExpanderCacheHandler();
    ///   saturationExpHandler = ctx->getUsedSaturationNodeExpansionCacheHandler();
    ///   if (mConfSatExpCacheWriting && satExpHandler
    ///       || mConfSaturationSatisfiabilitiyExpansionCacheWriting && saturationExpHandler) {
    ///     indiNodeVec = processingDataBox->getIndividualProcessNodeVector();
    ///     indiMax = indiNodeVec->getItemMaxIndex() + 1;
    ///     indiIdx = max(1, processingDataBox->getMaxIncrementalPreviousCompletionGraphNodeID());
    ///     if (mConfCollectCachingUpdatedBlockableIndiNodes) {
    ///       for (linker : processingDataBox->getBlockableIndividualNodeUpdatedLinker()) {
    ///         indiNode = linker->getData();
    ///         if (indiNode && indiNode->getIndividualNodeID() >= 0) {
    ///           indiNode = getUpToDateIndividual(indiIdx, ctx);            // NB: cpp uses indiIdx here
    ///           if (indiNode && !indiNode->isNominalIndividualNode()) {
    ///             … same two cache-write guards as the main loop …
    ///           }
    ///         }
    ///       }
    ///       indiIdx = max(ctx->getMaxCompletionGraphCachedIndividualNodeID()+1, indiIdx);
    ///     }
    ///     for (; indiIdx < indiMax; ++indiIdx) {
    ///       indiNode = getUpToDateIndividual(indiIdx, ctx);
    ///       if (indiNode && !indiNode->isNominalIndividualNode()) {
    ///         if (mConfSatExpCacheWriting && satExpHandler
    ///             && !indiNode->hasPartialProcessingRestrictionFlags(
    ///                    PRFINVALIDATEBLOCKERFLAGSCOMPINATION | PRFSUCCESSORNOMINALCONNECTION | PRFSATURATIONBLOCKINGCACHED)) {
    ///           if (!ctx->hasCompletionGraphCachedIndividualNodes()
    ///               || indiNode->hasPartialProcessingRestrictionFlags(PRFCOMPLETIONGRAPHCACHINGINVALIDATED)
    ///               || indiNode->getIndividualNodeID() > ctx->getMaxCompletionGraphCachedIndividualNodeID()) {
    ///             indiNode = getLocalizedIndividual(indiNode, false, ctx);
    ///             nodeCached |= satExpHandler->cacheIndividualNodeSatisfiable(indiNode, ctx);     // W6-DEFER[api]
    ///           }
    ///         }
    ///         if (mConfSaturationSatisfiabilitiyExpansionCacheWriting && saturationExpHandler
    ///             && !indiNode->hasPartialProcessingRestrictionFlags(
    ///                    PRFINVALIDATEBLOCKERFLAGSCOMPINATION | PRFSUCCESSORNEWNOMINALCONNECTION | PRFSATURATIONBLOCKINGCACHED)) {
    ///           if (!ctx->hasCompletionGraphCachedIndividualNodes()
    ///               || indiNode->hasPartialProcessingRestrictionFlags(PRFCOMPLETIONGRAPHCACHINGINVALIDATED)
    ///               || indiNode->getIndividualNodeID() > ctx->getMaxCompletionGraphCachedIndividualNodeID()) {
    ///             nodeCached |= saturationExpHandler->tryNodeSatisfiableCaching(indiNode, ctx);   // W6-DEFER[api]
    ///           }
    ///         }
    ///       }
    ///     }
    ///   }
    ///   return nodeCached;
    pub fn cache_satisfiable_individual_nodes(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let sat_exp_handler_available = calc_alg_context.base.used_sat_exp_cache_handler.is_some();
        let saturation_exp_handler_available = calc_alg_context
            .base
            .used_sat_node_exp_cache_handler
            .is_some();
        if !(self.conf_sat_exp_cache_writing && sat_exp_handler_available
            || self.conf_saturation_satisfiabilitiy_expansion_cache_writing
                && saturation_exp_handler_available)
        {
            return false;
        }

        let indi_max = calc_alg_context
            .processing_data_box()
            .individual_process_node_vector()
            .get_item_max_index()
            + 1;
        let mut indi_idx = 1.max(
            calc_alg_context
                .processing_data_box()
                .max_incremental_previous_completion_graph_node_id(),
        );
        let mut node_cached = false;

        // C++ sweeps this intrusive linker before the residual id range. Keep
        // the exact `getUpToDateIndividual(indiIdx)` quirk from cpp 4527 rather
        // than replacing it with the linker payload.
        if self.conf_collect_caching_updated_blockable_indi_nodes {
            let mut updated_nodes = Vec::new();
            while calc_alg_context
                .processing_data_box()
                .has_blockable_individual_node_updated_linker()
            {
                let updated_node = calc_alg_context
                    .processing_data_box_mut()
                    .blockable_individual_node_updated_linker();
                if updated_node.is_some()
                    && calc_alg_context
                        .process_context()
                        .node(updated_node)
                        .individual_node_id()
                        >= 0
                {
                    updated_nodes.push(updated_node);
                }
            }
            for _updated_node in updated_nodes {
                let indi_node = self.get_up_to_date_individual_by_id(indi_idx, calc_alg_context);
                node_cached |= self.write_satisfiable_node_cache_if_allowed(
                    indi_node,
                    calc_alg_context,
                    sat_exp_handler_available,
                    saturation_exp_handler_available,
                );
            }
            indi_idx = indi_idx.max(
                calc_alg_context
                    .base
                    .max_completion_graph_cached_individual_node_id()
                    + 1,
            );
        }

        while indi_idx < indi_max {
            let indi_node = self.get_up_to_date_individual_by_id(indi_idx, calc_alg_context);
            node_cached |= self.write_satisfiable_node_cache_if_allowed(
                indi_node,
                calc_alg_context,
                sat_exp_handler_available,
                saturation_exp_handler_available,
            );
            indi_idx += 1;
        }

        node_cached
    }

    fn write_satisfiable_node_cache_if_allowed(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        sat_exp_handler_available: bool,
        saturation_exp_handler_available: bool,
    ) -> bool {
        if indi_node.is_none()
            || calc_alg_context
                .process_context()
                .node(indi_node)
                .is_nominal_individual_node()
        {
            return false;
        }

        let mut node_cached = false;
        if self.conf_sat_exp_cache_writing
            && sat_exp_handler_available
            && !calc_alg_context
                .process_context()
                .node(indi_node)
                .has_partial_processing_restriction_flags(
                    Node::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION
                        | Node::PRF_SUCCESSORNOMINALCONNECTION
                        | Node::PRF_SATURATIONBLOCKINGCACHED,
                )
            && self.satisfiable_cache_write_in_completion_graph_range(indi_node, calc_alg_context)
        {
            let localized_indi = self.get_localized_individual(indi_node, false, calc_alg_context);
            let _ = localized_indi;
            // Deferred with the satisfiable-expander handler API:
            // satExpHandler->cacheIndividualNodeSatisfiable(localizedIndi, ctx).
        }

        if self.conf_saturation_satisfiabilitiy_expansion_cache_writing
            && saturation_exp_handler_available
            && !calc_alg_context
                .process_context()
                .node(indi_node)
                .has_partial_processing_restriction_flags(
                    Node::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION
                        | Node::PRF_SUCCESSORNEWNOMINALCONNECTION
                        | Node::PRF_SATURATIONBLOCKINGCACHED,
                )
            && self.satisfiable_cache_write_in_completion_graph_range(indi_node, calc_alg_context)
        {
            if let Some(mut handler_state) =
                calc_alg_context.take_used_saturation_node_expansion_cache_handler()
            {
                node_cached |= handler_state.handler.try_node_satisfiable_caching(
                    indi_node,
                    calc_alg_context,
                    &mut handler_state.cache_context,
                );
                calc_alg_context
                    .restore_used_saturation_node_expansion_cache_handler(handler_state);
            }
        }

        node_cached
    }

    fn satisfiable_cache_write_in_completion_graph_range(
        &self,
        indi_node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let max_cached_id = calc_alg_context
            .base
            .max_completion_graph_cached_individual_node_id();
        max_cached_id < 0
            || calc_alg_context
                .process_context()
                .node(indi_node)
                .has_partial_processing_restriction_flags(
                    Node::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
                )
            || calc_alg_context
                .process_context()
                .node(indi_node)
                .individual_node_id()
                > max_cached_id
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testAllSuccessorsProcessedAndWriteSatisfiableCache`.
    /// cpp 4670–4703.
    ///
    /// Depth-first probe (memoised via `processedNodeSet`) that, for a non-nominal
    /// node with no backward dependency to an ancestor and an empty concept-processing
    /// queue, recurses over its non-ancestor successors and, once all are confirmed
    /// processed, writes the localised node into the satisfiable expander cache.
    ///
    /// PORT-PENDING: the final satisfiable-expander writer call
    /// (`satExpHandler->cacheIndividualNodeSatisfiable`) has no live Rust API yet.
    /// Faithful outline:
    ///
    ///   if (!indiNode->isNominalIndividualNode() && !indiNode->hasBackwardDependencyToAncestorIndividualNode()) {
    ///     if (!indiNode->hasPartialProcessingRestrictionFlags(PRFINVALIDATEBLOCKERFLAGSCOMPINATION | PRFSUCCESSORNOMINALCONNECTION)) {
    ///       if (!ctx->hasCompletionGraphCachedIndividualNodes()
    ///           || indiNode->hasPartialProcessingRestrictionFlags(PRFCOMPLETIONGRAPHCACHINGINVALIDATED)
    ///           || indiNode->getIndividualNodeID() > ctx->getMaxCompletionGraphCachedIndividualNodeID()) {
    ///         conProQue = indiNode->getConceptProcessingQueue(false);
    ///         if (!conProQue || conProQue->isEmpty()) {
    ///           if (!processedNodeSet->contains(indiNode)) {
    ///             processedNodeSet->insert(indiNode);
    ///             ancIndi = getAncestorIndividual(indiNode, ctx);
    ///             for (succLink : indiNode->getSuccessorIterator()) {
    ///               succIndi = getSuccessorIndividual(indiNode, succLink, ctx);
    ///               if (!ancIndi || succIndi->getIndividualNodeID() != ancIndi->getIndividualNodeID()) {
    ///                 if (!testAllSuccessorsProcessedAndWriteSatisfiableCache(succIndi, processedNodeSet, satExpHandler, ctx))
    ///                   return false;
    ///               }
    ///             }
    ///             indiNode = getLocalizedIndividual(indiNode, false, ctx);
    ///             satExpHandler->cacheIndividualNodeSatisfiable(indiNode, ctx);   // W6-DEFER[api]
    ///             return true;
    ///           }
    ///         }
    ///       }
    ///     }
    ///   }
    ///   return false;
    pub fn test_all_successors_processed_and_write_satisfiable_cache(
        &mut self,
        indi_node: NodeId,
        processed_node_set: &mut HashSet<NodeId>, // CPROCESSINGSET<CIndividualProcessNode*>*
        sat_exp_handler: Id<SatisfiableExpanderCacheHandler>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if indi_node.is_none()
            || sat_exp_handler.is_none()
            || calc_alg_context
                .process_context()
                .node(indi_node)
                .is_nominal_individual_node()
            || calc_alg_context
                .process_context()
                .node(indi_node)
                .has_backward_dependency_to_ancestor_individual_node()
        {
            return false;
        }
        if calc_alg_context
            .process_context()
            .node(indi_node)
            .has_partial_processing_restriction_flags(
                Node::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION | Node::PRF_SUCCESSORNOMINALCONNECTION,
            )
            || !self.satisfiable_cache_write_in_completion_graph_range(indi_node, calc_alg_context)
        {
            return false;
        }

        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(indi_node, false);
        if con_pro_queue.is_some()
            && !calc_alg_context
                .process_context()
                .concept_proc_queue(con_pro_queue)
                .is_empty()
        {
            return false;
        }
        if processed_node_set.contains(&indi_node) {
            return false;
        }
        processed_node_set.insert(indi_node);

        let mut current_indi = indi_node;
        let anc_indi = self.get_ancestor_individual(&mut current_indi, calc_alg_context);
        let anc_indi_id = anc_indi.is_some().then(|| {
            calc_alg_context
                .process_context()
                .node(anc_indi)
                .individual_node_id()
        });

        let mut succ_it = calc_alg_context
            .process_context()
            .node_successor_iterator(current_indi);
        while succ_it.has_next() {
            let succ_indi_id = succ_it.next_individual_id(true);
            if anc_indi_id == Some(succ_indi_id) {
                continue;
            }
            let succ_indi = self.get_up_to_date_individual_by_id(succ_indi_id, calc_alg_context);
            if succ_indi.is_none()
                || !self.test_all_successors_processed_and_write_satisfiable_cache(
                    succ_indi,
                    processed_node_set,
                    sat_exp_handler,
                    calc_alg_context,
                )
            {
                return false;
            }
        }

        let localized_indi = self.get_localized_individual(current_indi, false, calc_alg_context);
        let _ = localized_indi;
        // Deferred with the satisfiable-expander handler API:
        // satExpHandler->cacheIndividualNodeSatisfiable(localizedIndi, ctx).
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::writeSatisfiableCachedIndividualNodesOfUnsatisfiableBranch`.
    /// cpp 4706–4734.
    ///
    /// For an unsatisfiable branch, write into the satisfiable cache every
    /// fully-processed non-nominal sub-tree whose every successor is also processed
    /// (via `test_all_successors_processed_and_write_satisfiable_cache`).
    ///
    /// PORT-PENDING: the final `satExpHandler->cacheIndividualNodeSatisfiable`
    /// call inside `test_all_successors_processed_and_write_satisfiable_cache`
    /// still has no live Rust writer API. Faithful outline:
    ///
    ///   nodeCached = false;
    ///   satExpHandler = ctx->getUsedSatisfiableExpanderCacheHandler();
    ///   if (mConfUnsatBranchSatisfiableCaching && mConfSatExpCacheWriting && satExpHandler) {
    ///     indiNodeVec = processingDataBox->getIndividualProcessNodeVector();
    ///     processedNodeSet = new CPROCESSINGSET<…>(…);
    ///     for (indiIdx = indiNodeVec->getItemMinIndex(); indiIdx < indiNodeVec->getItemCount(); ++indiIdx) {
    ///       indiNode = getUpToDateIndividual(indiIdx, ctx);
    ///       if (indiNode && !indiNode->isNominalIndividualNode()
    ///           && !indiNode->hasPartialProcessingRestrictionFlags(PRFINVALIDATEBLOCKERFLAGSCOMPINATION | PRFSUCCESSORNOMINALCONNECTION)) {
    ///         if (!ctx->hasCompletionGraphCachedIndividualNodes()
    ///             || indiNode->hasPartialProcessingRestrictionFlags(PRFCOMPLETIONGRAPHCACHINGINVALIDATED)
    ///             || indiNode->getIndividualNodeID() > ctx->getMaxCompletionGraphCachedIndividualNodeID()) {
    ///           conProQue = indiNode->getConceptProcessingQueue(false);
    ///           if (!conProQue || conProQue->isEmpty())
    ///             nodeCached |= testAllSuccessorsProcessedAndWriteSatisfiableCache(indiNode, processedNodeSet, satExpHandler, ctx);
    ///         }
    ///       }
    ///     }
    ///   }
    ///   return nodeCached;
    pub fn write_satisfiable_cached_individual_nodes_of_unsatisfiable_branch(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let sat_exp_handler = calc_alg_context.base.used_sat_exp_cache_handler;
        if !(self.conf_unsat_branch_satisfiable_caching
            && self.conf_sat_exp_cache_writing
            && sat_exp_handler.is_some())
        {
            return false;
        }

        let (mut indi_idx, indi_count) = {
            let indi_node_vec = calc_alg_context
                .processing_data_box()
                .individual_process_node_vector();
            (
                indi_node_vec.get_item_min_index(),
                indi_node_vec.get_item_count(),
            )
        };
        let mut processed_node_set = HashSet::new();
        let mut node_cached = false;

        while indi_idx < indi_count {
            let indi_node = self.get_up_to_date_individual_by_id(indi_idx, calc_alg_context);
            if indi_node.is_some()
                && !calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .is_nominal_individual_node()
                && !calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION
                            | Node::PRF_SUCCESSORNOMINALCONNECTION,
                    )
                && self
                    .satisfiable_cache_write_in_completion_graph_range(indi_node, calc_alg_context)
            {
                let con_pro_queue = calc_alg_context
                    .process_context_mut()
                    .node_concept_processing_queue(indi_node, false);
                if con_pro_queue.is_none()
                    || calc_alg_context
                        .process_context()
                        .concept_proc_queue(con_pro_queue)
                        .is_empty()
                {
                    node_cached |= self.test_all_successors_processed_and_write_satisfiable_cache(
                        indi_node,
                        &mut processed_node_set,
                        sat_exp_handler,
                        calc_alg_context,
                    );
                }
            }
            indi_idx += 1;
        }

        node_cached
    }

    // =======================================================================
    // Saturation- / satisfiable-expansion caching detection (cpp 4750–4949).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::detectIndividualNodeSaturationCached`.
    /// cpp 4750–4817.
    ///
    /// Re-validates the saturation-blocking caching of a node: an ancestor-cached
    /// node stays cached unless abolished; otherwise (unless invalidated) the
    /// saturation-node-expansion cache is re-consulted, installing the reactivation
    /// of any dependent nominals and adjusting the tight-at-most successor-creation
    /// block. Loss reactivates indirect saturation-cached successors and reapplies
    /// generating concepts; a fresh hit propagates the saturation block.
    pub fn detect_individual_node_saturation_cached(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(Node::PRF_SATURATIONBLOCKINGCACHED)
            && !calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    Node::PRF_RETESTSATURATIONBLOCKINGCACHEDDUEDIRECTMODIFIED,
                )
        {
            return true;
        }

        let prev_sat_cached = calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                Node::PRF_SATURATIONBLOCKINGCACHED | Node::PRF_ANCESTORSATURATIONBLOCKINGCACHED,
            );
        let prev_sat_succ_creation_blocked = calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                Node::PRF_SATURATIONSUCCESSORCREATIONBLOCKINGCACHED,
            );

        if calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(Node::PRF_ANCESTORSATURATIONBLOCKINGCACHED)
        {
            if calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    Node::PRF_ANCESTORSATURATIONBLOCKINGCACHEDABOLISHED,
                )
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .clear_processing_restriction_flags(
                        Node::PRF_ANCESTORSATURATIONBLOCKINGCACHEDABOLISHED,
                    );
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .clear_processing_restriction_flags(Node::PRF_ANCESTORSATURATIONBLOCKINGCACHED);
            } else {
                return true;
            }
        }
        if calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                Node::PRF_RETESTSATURATIONBLOCKINGCACHEDDUEDIRECTMODIFIED,
            )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual_node)
                .clear_processing_restriction_flags(
                    Node::PRF_RETESTSATURATIONBLOCKINGCACHEDDUEDIRECTMODIFIED,
                );
        }
        let mut still_saturation_cached = false;
        if !calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(Node::PRF_SATURATIONBLOCKINGCACHEDINVALIDATED)
        {
            // CSaturationNodeExpansionCacheHandler* satNodeExpCacheHandler = calcAlgContext->getSaturationNodeExpansionCacheHandler();
            if !still_saturation_cached
                && calc_alg_context.sat_node_exp_cache_handler.is_some()
                && self.conf_saturation_expansion_cache_reading
            {
                // CSaturationNodeAssociatedConceptExpansion* expansion = nullptr;
                if calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_SATURATIONBLOCKINGCACHEDRETESTDUETOMODIFICATION,
                    )
                {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(individual_node)
                        .clear_processing_restriction_flags(
                            Node::PRF_SATURATIONBLOCKINGCACHEDRETESTDUETOMODIFICATION,
                        );
                    if let Some(mut handler_state) =
                        calc_alg_context.take_used_saturation_node_expansion_cache_handler()
                    {
                        let (cached, expansion) = handler_state.handler.is_node_satisfiable_cached(
                            individual_node,
                            calc_alg_context,
                            &handler_state.cache_context,
                        );
                        if cached {
                            still_saturation_cached = true;
                            if expansion.is_some() {
                                let (dependent_nominal_set, has_tight_at_most_restriction) = {
                                    let expansion_ref = handler_state
                                        .cache_context
                                        .associated_concept_expansion(expansion);
                                    (
                                        expansion_ref.dependent_nominal_set,
                                        expansion_ref.get_has_tight_at_most_restriction(),
                                    )
                                };
                                if dependent_nominal_set.is_some()
                                    && !self.conf_saturation_caching_with_nominals
                                {
                                    still_saturation_cached = false;
                                } else {
                                    self.install_saturation_caching_reactivation(
                                        individual_node,
                                        dependent_nominal_set,
                                        &handler_state.cache_context,
                                        calc_alg_context,
                                    );

                                    if prev_sat_succ_creation_blocked
                                        && has_tight_at_most_restriction
                                    {
                                        calc_alg_context
                                            .process_context_mut()
                                            .node_mut(individual_node)
                                            .clear_processing_restriction_flags(
                                                Node::PRF_SATURATIONSUCCESSORCREATIONBLOCKINGCACHED,
                                            );
                                        self.reapply_satisfiable_cached_absorbed_generating_concepts(
                                            individual_node,
                                            calc_alg_context,
                                        );
                                    }
                                    if !prev_sat_succ_creation_blocked
                                        && !has_tight_at_most_restriction
                                    {
                                        calc_alg_context
                                            .process_context_mut()
                                            .node_mut(individual_node)
                                            .add_processing_restriction_flags(
                                                Node::PRF_SATURATIONSUCCESSORCREATIONBLOCKINGCACHED,
                                            );
                                    }
                                }
                            }
                        }
                        calc_alg_context
                            .restore_used_saturation_node_expansion_cache_handler(handler_state);
                    }
                }
            }
        }
        if !still_saturation_cached {
            if prev_sat_cached {
                // STATINC(SATURATIONCACHELOSECOUNT, …);  // W3-DEFER[api]
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .clear_processing_restriction_flags(Node::PRF_SATURATIONBLOCKINGCACHED);
                self.reactivate_indirect_saturation_cached_successors(
                    individual_node,
                    false,
                    calc_alg_context,
                );
            }
            if prev_sat_succ_creation_blocked {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .clear_processing_restriction_flags(
                        Node::PRF_SATURATIONSUCCESSORCREATIONBLOCKINGCACHED,
                    );
                self.reapply_satisfiable_cached_absorbed_generating_concepts(
                    individual_node,
                    calc_alg_context,
                );
            }
        } else if !prev_sat_cached {
            // STATINC(SATURATIONCACHEESTABLISHCOUNT, …);  // W3-DEFER[api]
            calc_alg_context
                .process_context_mut()
                .node_mut(individual_node)
                .add_processing_restriction_flags(Node::PRF_SATURATIONBLOCKINGCACHED);
            self.propagate_indirect_successor_saturation_blocked(individual_node, calc_alg_context);
        }
        still_saturation_cached
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::detectIndividualNodeSatisfiableExpandedCached`.
    /// cpp 4833–4949.
    ///
    /// Re-validates the satisfiable-expansion caching of a node: an ancestor-cached
    /// node stays cached unless abolished; otherwise (when there is no nominal /
    /// invalid-blocking / saturation-block flag) consults the satisfiable expander
    /// cache, expands cached concepts, and — if a compatible (per
    /// `is_satisfiable_cached_compatible`) branched entry exists — marks the node
    /// satisfiable-cached and propagates it; on a miss it writes the expansion. Loss
    /// reactivates indirect successors and reapplies absorbed concepts.
    pub fn detect_individual_node_satisfiable_expanded_cached(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let prev_sat_cached = calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                Node::PRF_SATISFIABLECACHED | Node::PRF_ANCESTORSATISFIABLECACHED,
            );

        if calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(Node::PRF_ANCESTORSATISFIABLECACHED)
        {
            if calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    Node::PRF_ANCESTORSATISFIABLECACHEDABOLISHED,
                )
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .clear_processing_restriction_flags(
                        Node::PRF_ANCESTORSATISFIABLECACHEDABOLISHED,
                    );
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .clear_processing_restriction_flags(Node::PRF_ANCESTORSATISFIABLECACHED);
            } else {
                return true;
            }
        }
        if calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                Node::PRF_RETESTSATISFIABLECACHEDDUEDIRECTMODIFIED,
            )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual_node)
                .clear_processing_restriction_flags(
                    Node::PRF_RETESTSATISFIABLECACHEDDUEDIRECTMODIFIED,
                );
        }

        let mut new_sat_cached = false;

        // CSatisfiableExpanderCacheHandler* satExpHandler = calcAlgContext->getUsedSatisfiableExpanderCacheHandler();
        if !calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                Node::PRF_SUCCESSORNOMINALCONNECTION
                    | Node::PRF_INVALIDBLOCKINGORCACHING
                    | Node::PRF_SATURATIONBLOCKINGCACHED,
            )
        {
            // can only be satisfiable-cached if there is no nominal
            if self.conf_sat_exp_cache_retrieval
                && calc_alg_context.base.used_sat_exp_cache_handler.is_some()
            {
                // STATINC(SATEXPCACHERETRIEVALCOUNT, …);  // W3-DEFER[api]
                // W6-DEFER[api]: if (satExpHandler->isIndividualNodeExpandCached(individualNode, &satisfiableCached, &entry, ctx)) {
                //   STATINC(SATEXPCACHERETRIEVALSUCCESSCOUNT, …);
                //   if (mConfSatExpCacheConceptExpansion) {
                //     expandCachedConcepts(individualNode, entry, ctx);
                //     if (mConfSatExpCacheSatisfiableBlocking && satisfiableCached
                //         && !individualNode->hasPartialProcessingRestrictionFlags(PRFINVALIDBLOCKINGORCACHING)) {
                //       STATINC(SATEXPCACHERETRIEVALFOUNDSATISFIABLECOUNT, …);
                //       satCompatible = false;
                //       if (entry->isSatisfiableWithoutBranchedConcepts()) {
                //         satCompatible = true;
                //       } else {
                //         satBranchLinker = entry->getExpanderBranchedLinker();
                //         if (!satBranchLinker) { satCompatible = true; }
                //         else {
                //           ancestorIndiNode = getAncestorIndividual(individualNode, ctx);
                //           for (satBranchLinkerIt = satBranchLinker; satBranchLinkerIt && !satCompatible;
                //                satBranchLinkerIt = satBranchLinkerIt->getNext()) {
                //             if (isSatisfiableCachedCompatible(individualNode, satBranchLinkerIt, ancestorIndiNode, ctx)) {
                //               satCompatible = true;
                //             }
                //           }
                //         }
                //       }
                //       if (satCompatible) {
                //         STATINC(SATEXPCACHERETRIEVALCOMPATIBLESATCOUNT, …);
                //         newSatCached = true;
                //         if (!prevSatCached) {
                //           individualNode->addProcessingRestrictionFlags(PRFSATISFIABLECACHED);
                //           propagateIndirectSuccessorSatisfiableCached(individualNode, ctx);
                //         }
                //       }
                //     }
                //   }
                // }
            }
            if self.conf_sat_exp_cache_writing && !new_sat_cached {
                if !calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_SIGNATUREBLOCKINGCACHED
                            | Node::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
                    )
                {
                    // W6-DEFER[api]: satExpHandler->cacheIndividualNodeExpansion(individualNode, ctx);
                }
            }
        }
        if !new_sat_cached {
            if prev_sat_cached {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .clear_processing_restriction_flags(Node::PRF_SATISFIABLECACHED);
                self.reactivate_indirect_satisfiable_cached_successors(
                    individual_node,
                    false,
                    calc_alg_context,
                );

                self.reapply_satisfiable_cached_absorbed_disjunction_concepts(
                    individual_node,
                    calc_alg_context,
                );
                self.reapply_satisfiable_cached_absorbed_generating_concepts(
                    individual_node,
                    calc_alg_context,
                );
            }
        }
        new_sat_cached
    }

    // =======================================================================
    // Absorbed-concept reapply registration (cpp 6298–6314).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addSatisfiableCachedAbsorbedDisjunctionConcept`.
    /// cpp 6298–6304.
    ///
    /// Allocates a `CReapplyConceptDescriptor`, initialises it with the processing
    /// restriction, and prepends it to
    /// `processIndi->addSatisfiableCachedAbsorbedDisjunctionsLinker(reapplyConDes)`.
    pub fn add_satisfiable_cached_absorbed_disjunction_concept(
        &mut self,
        concept_descriptor: ConDescId,
        process_indi: NodeId,
        // KONCLUDE-PORT-NOTE[api]: C++ `CProcessingRestrictionSpecification*` has no
        // dedicated ported type; `RestrictionSpecId` (the branching-merging spec) is
        // the closest ported analogue.
        proc_rest: RestrictionSpecId,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let previous_head = calc_alg_context
            .process_context()
            .node(process_indi)
            .satisfiable_cached_absorbed_disjunctions_linker();
        let mut reapply_con_des =
            ReapplyConceptDescriptor::new(concept_descriptor, dependency_track_point, false);
        reapply_con_des.init_reapply_descriptor_restricted(
            concept_descriptor,
            dependency_track_point,
            proc_rest.raw,
        );
        reapply_con_des.next = previous_head;
        let reapply_con_des = calc_alg_context
            .process_context_mut()
            .alloc_reapply_con_desc(reapply_con_des);
        calc_alg_context
            .process_context_mut()
            .node_mut(process_indi)
            .add_satisfiable_cached_absorbed_disjunctions_linker(reapply_con_des);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addSatisfiableCachedAbsorbedGeneratingConcept`.
    /// cpp 6308–6314.
    ///
    /// As above without the processing-restriction, then prepends it to
    /// `processIndi->addSatisfiableCachedAbsorbedGeneratingLinker(reapplyConDes)`.
    pub fn add_satisfiable_cached_absorbed_generating_concept(
        &mut self,
        concept_descriptor: ConDescId,
        process_indi: NodeId,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let previous_head = calc_alg_context
            .process_context()
            .node(process_indi)
            .satisfiable_cached_absorbed_generating_linker();
        let mut reapply_con_des =
            ReapplyConceptDescriptor::new(concept_descriptor, dependency_track_point, false);
        reapply_con_des.next = previous_head;
        let reapply_con_des = calc_alg_context
            .process_context_mut()
            .alloc_reapply_con_desc(reapply_con_des);
        calc_alg_context
            .process_context_mut()
            .node_mut(process_indi)
            .add_satisfiable_cached_absorbed_generating_linker(reapply_con_des);
    }

    // =======================================================================
    // Satisfiable-cached compatibility + propagation (cpp 6321–6482).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateIndirectSuccessorSatisfiableCached`.
    /// cpp 6321–6323.
    pub fn propagate_indirect_successor_satisfiable_cached(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.propagate_adding_blocked_processing_restriction_to_successors(
            indi,
            Node::PRF_ANCESTORSATISFIABLECACHED,
            true,
            Node::PRF_ANCESTORSATISFIABLECACHED,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isSatisfiableCachedAutomatConceptCompatible`.
    /// cpp 6332–6356.
    ///
    /// Recursively tests whether a (possibly automaton-conjunction) ∀-typed concept
    /// is compatible with reusing a satisfiable-cached node: for a `∀`-style operand
    /// reaching the ancestor over a role successor, the ancestor's label set must
    /// already contain the operand concepts.
    pub fn is_satisfiable_cached_automat_concept_compatible(
        &mut self,
        individual_node: NodeId,
        concept: super::super::model::ConceptId,
        negated: bool,
        ancestor_indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let con_operator = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_operator();
        // cint64 opCode = concept->getOperatorCode();  (read but only used by callers' switch)
        if !negated && con_operator.has_partial_operator_code_flag(CCFS_AQALL_TYPE) {
            let role: RoleId = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_role();
            let anc_con_set: LabelSetId = calc_alg_context
                .process_context_mut()
                .node_mut(ancestor_indi_node)
                .get_reapply_concept_label_set(false);
            let anc_id = calc_alg_context
                .process_context()
                .node(ancestor_indi_node)
                .individual_node_id();
            if calc_alg_context
                .process_context()
                .node(individual_node)
                .has_role_successor_to_individual_id(role, anc_id, true)
            {
                let op_con_linker: Vec<_> = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_operand_list()
                    .to_vec();
                if !self.contains_individual_node_concepts_for_label_set(
                    anc_con_set,
                    &op_con_linker,
                    false,
                    calc_alg_context,
                ) {
                    return false;
                }
            }
        } else if !negated && con_operator.has_partial_operator_code_flag(CCFS_AQAND_TYPE) {
            let op_con_linker: Vec<_> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            for link in &op_con_linker {
                let op_con = link.target;
                let op_neg = link.negated;
                if !self.is_satisfiable_cached_automat_concept_compatible(
                    individual_node,
                    op_con,
                    op_neg,
                    ancestor_indi_node,
                    calc_alg_context,
                ) {
                    return false;
                }
            }
        }
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isSatisfiableCachedCompatible`.
    /// cpp 6359–6420.
    ///
    /// Tests whether a satisfiable-cached entry's branched cache values are all
    /// compatible with reusing them at `individualNode` given the connection to its
    /// ancestor: for every `∀`/`≤`/`≥`/`∃`-typed cache value, if the node has the
    /// relevant role successor to the ancestor, the ancestor's label set must already
    /// subsume the operand concepts (else incompatible).
    ///
    /// PORT-PENDING: the body iterates `satBranchLinker->getCacheValueList()` of W6
    /// `CCacheValue`s and the ancestor successor-role iterator
    /// (`getSuccessorRoleIterator`, a process stub). The reusable substrate pieces it
    /// calls are `hasRoleSuccessorToIndividual`, `containsIndividualNodeConcepts`
    /// (sibling), `getIndirectSuperRoleList`, and
    /// `is_satisfiable_cached_automat_concept_compatible`. Faithful outline:
    ///
    ///   if (ancestorIndiNode) {
    ///     ancRoleIt = individualNode->getSuccessorRoleIterator(ancestorIndiNode);
    ///     if (!ancRoleIt.hasNext()) return true;
    ///     ancConSet = ancestorIndiNode->getReapplyConceptLabelSet(false);
    ///     for (cacheValue : satBranchLinker->getCacheValueList()) {
    ///       concept = (CConcept*)cacheValue.getIdentification();
    ///       conceptNeg = cacheValue.getCacheValueIdentifier() == CACHEVALTAGANDNEGATEDCONCEPT;
    ///       role = concept->getRole(); opCode = concept->getOperatorCode();
    ///       conOperator = concept->getConceptOperator(); opConLinker = concept->getOperandList();
    ///       if (!conceptNeg && conOperator->hasPartialOperatorCodeFlag(CCFS_ALL_TYPE) || conceptNeg && opCode == CCSOME) {
    ///         operandNeg = (opCode == CCSOME);
    ///         if (individualNode->hasRoleSuccessorToIndividual(role, ancestorIndiNode, true)
    ///             && !containsIndividualNodeConcepts(ancConSet, opConLinker, operandNeg, ctx)) return false;
    ///       } else if (!conceptNeg && opCode == CCATMOST || conceptNeg && opCode == CCATLEAST) {
    ///         if (!opConLinker) { if (individualNode->hasRoleSuccessorToIndividual(role, ancestorIndiNode, true)) return false; }
    ///         else if (individualNode->hasRoleSuccessorToIndividual(role, ancestorIndiNode, true)
    ///                  && !containsIndividualNodeConcepts(ancConSet, opConLinker, true, ctx)) return false;
    ///       } else if (!conceptNeg && (opCode == CCSOME || opCode == CCATLEAST || opCode == CCAQSOME)
    ///                  || conceptNeg && (opCode == CCALL || opCode == CCATMOST)) {
    ///         minSuperRole = null; minSuperRoleCount = 0;
    ///         for (superRole : role->getIndirectSuperRoleList()) {
    ///           c = superRole->getIndirectSuperRoleList()->getCount();
    ///           if (!minSuperRole || c < minSuperRoleCount) { minSuperRoleCount = c; minSuperRole = superRole; }
    ///         }
    ///         if (individualNode->hasRoleSuccessorToIndividual(minSuperRole, ancestorIndiNode, true)) return false;
    ///       } else if (!conceptNeg && conOperator->hasPartialOperatorCodeFlag(CCFS_AQAND_AQALL_TYPE)) {
    ///         if (!isSatisfiableCachedAutomatConceptCompatible(individualNode, concept, conceptNeg, ancestorIndiNode, ctx)) return false;
    ///       }
    ///     }
    ///   }
    ///   return true;
    pub fn is_satisfiable_cached_compatible(
        &mut self,
        individual_node: NodeId,
        sat_branch_linker: Cint64, // CExpanderBranchedLinker*
        ancestor_indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // referenced so the faithful operator codes above stay anchored to op.rs.
        let _ = (
            CCFS_ALL_TYPE,
            CCFS_AQAND_AQALL_TYPE,
            CCSOME,
            CCATMOST,
            CCATLEAST,
            CCALL,
            CCAQSOME,
        );
        let _ = (
            individual_node,
            sat_branch_linker,
            ancestor_indi_node,
            calc_alg_context,
        );
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::expandCachedConcepts`.
    /// cpp 6423–6482.
    ///
    /// Adds to the node's label set every concept of a satisfiable-expander cache
    /// entry beyond those already present, building the `CONNECTION`/`EXPANDED`
    /// dependency chain from the entry's per-value dependency tags, then
    /// `addConceptToIndividualSkipANDProcessing` for the concept.
    ///
    /// PORT-PENDING: drives `CSignatureSatisfiableExpanderCacheEntry` /
    /// `CExpanderCacheValueLinker` / `CCacheValue` (all W6). The reusable substrate
    /// pieces are the label set (`getReapplyConceptLabelSet`, `hasConcept`,
    /// `getConceptDescriptor(tag, …)`), the dependency factory
    /// (`create_connection_dependency` / `create_expanded_dependency`), and
    /// `add_concept_to_individual_skip_and_processing`. Faithful outline:
    ///
    ///   if (entry) {
    ///     conSet = individualNode->getReapplyConceptLabelSet(true);
    ///     conSetCount = conSet->getConceptCount(); expandCount = entry->getExpanderCacheValueCount();
    ///     expLinker = entry->getExpanderCacheValueLinker();
    ///     for (i = 0; i < conSetCount; ++i) expLinker = expLinker->getNext();   // skip already-present prefix
    ///     for (expLinkerIt = expLinker; expLinkerIt; expLinkerIt = expLinkerIt->getNext()) {
    ///       cacheValue = expLinkerIt->getCacheValue();
    ///       concept = (CConcept*)cacheValue->getIdentification();
    ///       conceptNeg = cacheValue->getCacheValueIdentifier() == CACHEVALTAGANDNEGATEDCONCEPT;
    ///       if (!conSet->hasConcept(concept)) {
    ///         dependencies = null; firstDepTrackPoint = null;
    ///         for (depLinker : expLinkerIt->getExpanderDependencyList()) {
    ///           depTag = depLinker->getCacheValue()->getTag();
    ///           conSet->getConceptDescriptor(depTag, depConDes, depTrackPoint);
    ///           connDepNode = createCONNECTIONDependency(individualNode, depConDes, depTrackPoint, ctx);
    ///           if (!firstDepTrackPoint) firstDepTrackPoint = connDepNode; else dependencies = connDepNode->append(dependencies);
    ///         }
    ///         expDepNode = createEXPANDEDDependency(expDepTrackPoint, individualNode, firstDepTrackPoint, dependencies, ctx);
    ///         addConceptToIndividualSkipANDProcessing(concept, conceptNeg, individualNode, expDepTrackPoint, true, false, true, ctx);
    ///       }
    ///     }
    ///   }
    pub fn expand_cached_concepts(
        &mut self,
        individual_node: NodeId,
        entry: Cint64, // CSignatureSatisfiableExpanderCacheEntry*
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = (individual_node, entry, calc_alg_context);
    }

    // =======================================================================
    // Indirect successor cache reactivation (cpp 6527–6567).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reactivateIndirectSatisfiableCachedSuccessors`.
    /// cpp 6527–6546.
    ///
    /// For every deeper (strictly larger ancestor depth) successor that is
    /// ancestor-satisfiable-cached but not yet abolished, mark the localized successor
    /// `…ANCESTORSATISFIABLECACHEDABOLISHED` and re-queue it for processing.
    ///
    pub fn reactivate_indirect_satisfiable_cached_successors(
        &mut self,
        indi: NodeId,
        recursive: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let anc_depth = calc_alg_context
            .process_context()
            .node(indi)
            .individual_ancestor_depth();
        // `recursive` is carried in the C++ signature; cpp 6527-6546 does not read it.
        let _ = recursive;
        let mut succ_it = calc_alg_context
            .process_context()
            .node_successor_iterator(indi);
        while succ_it.has_next() {
            let succ_indi_id = succ_it.next_individual_id(true);
            let succ_indi = self.get_up_to_date_individual_by_id(succ_indi_id, calc_alg_context);
            if succ_indi.is_none() {
                continue;
            }
            let succ_anc_depth = calc_alg_context
                .process_context()
                .node(succ_indi)
                .individual_ancestor_depth();
            if succ_anc_depth > anc_depth
                && calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .has_partial_processing_restriction_flags(Node::PRF_ANCESTORSATISFIABLECACHED)
                && !calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_ANCESTORSATISFIABLECACHEDABOLISHED,
                    )
            {
                let loc_indi_node =
                    self.get_localized_individual(succ_indi, false, calc_alg_context);
                calc_alg_context
                    .process_context_mut()
                    .node_mut(loc_indi_node)
                    .add_processing_restriction_flags(Node::PRF_ANCESTORSATISFIABLECACHEDABOLISHED);
                self.add_individual_to_processing_queue(loc_indi_node, calc_alg_context);
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reactivateIndirectSaturationCachedSuccessors`.
    /// cpp 6548–6567.
    ///
    /// As `reactivate_indirect_satisfiable_cached_successors` but for the
    /// `…ANCESTORSATURATIONBLOCKINGCACHED` / `…ABOLISHED` flag pair.
    ///
    pub fn reactivate_indirect_saturation_cached_successors(
        &mut self,
        indi: NodeId,
        recursive: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let anc_depth = calc_alg_context
            .process_context()
            .node(indi)
            .individual_ancestor_depth();
        // `recursive` is carried in the C++ signature; cpp 6548-6567 does not read it.
        let _ = recursive;
        let mut succ_it = calc_alg_context
            .process_context()
            .node_successor_iterator(indi);
        while succ_it.has_next() {
            let succ_indi_id = succ_it.next_individual_id(true);
            let succ_indi = self.get_up_to_date_individual_by_id(succ_indi_id, calc_alg_context);
            if succ_indi.is_none() {
                continue;
            }
            let succ_anc_depth = calc_alg_context
                .process_context()
                .node(succ_indi)
                .individual_ancestor_depth();
            if succ_anc_depth > anc_depth
                && calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_ANCESTORSATURATIONBLOCKINGCACHED,
                    )
                && !calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .has_partial_processing_restriction_flags(
                        Node::PRF_ANCESTORSATURATIONBLOCKINGCACHEDABOLISHED,
                    )
            {
                let loc_indi_node =
                    self.get_localized_individual(succ_indi, false, calc_alg_context);
                calc_alg_context
                    .process_context_mut()
                    .node_mut(loc_indi_node)
                    .add_processing_restriction_flags(
                        Node::PRF_ANCESTORSATURATIONBLOCKINGCACHEDABOLISHED,
                    );
                self.add_individual_to_processing_queue(loc_indi_node, calc_alg_context);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::cache::context::CacheContext;
    use super::super::super::cache::unsat::{OccurrenceUnsatisfiableCache, ReaderId, WriterId};
    use super::super::super::cache::value::{CacheValue, CacheValueIdentifier};
    use super::super::super::model::concept::Concept;
    use super::super::super::model::concept_process::{
        ConceptProcessData, UnsatisfiableCachingTags,
    };
    use super::super::super::process::descriptor::ConceptDescriptor;
    use super::super::super::process::node::IndividualProcessNode;
    use super::super::super::process::satellites::{
        ConceptDescriptorDependencyReapplyData, ReapplyConceptLabelSet,
    };
    use super::super::algorithm::CompletionTaskHandleAlgorithm;
    use super::super::clash::CalcSignal;
    use super::super::unsat_handler::UnsatisfiableCacheHandler;
    use super::*;

    fn cache_context_with_current_tag(tag: Cint64) -> (CacheContext, ReaderId, WriterId) {
        let mut cache_context = CacheContext::new();
        let cache = cache_context.alloc_unsat_cache(OccurrenceUnsatisfiableCache::new(1, "", 0));
        {
            let CacheContext {
                unsat_caches,
                unsat_cache_entries,
                unsat_cache_update_slot_items,
                ..
            } = &mut cache_context;
            unsat_caches
                .get_mut(cache)
                .thread_started(unsat_cache_entries, unsat_cache_update_slot_items);
            unsat_caches.get_mut(cache).caching_tag = tag;
        }
        let reader = {
            let CacheContext {
                unsat_caches,
                unsat_cache_readers,
                ..
            } = &mut cache_context;
            unsat_caches
                .get_mut(cache)
                .get_cache_reader(cache, unsat_cache_readers)
        };
        let writer = {
            let CacheContext {
                unsat_caches,
                unsat_cache_writers,
                ..
            } = &mut cache_context;
            unsat_caches
                .get_mut(cache)
                .get_cache_writer(cache, unsat_cache_writers)
        };
        (cache_context, reader, writer)
    }

    fn context_with_labelled_node() -> (CalculationAlgorithmContextBase, NodeId, ConDescId) {
        let mut calc = CalculationAlgorithmContextBase::new();
        let mut concept_data = Concept::new();
        concept_data.set_concept_tag(11);
        let concept = calc.base.ontology_arenas.alloc_concept(concept_data);
        let mut con_desc = ConceptDescriptor::new();
        con_desc.concept = concept;
        let con_desc = calc.process_context_mut().alloc_con_desc(con_desc);

        let mut label_set = ReapplyConceptLabelSet::new(0);
        label_set.concept_des_linker = con_desc;
        label_set.concept_count = 1;
        label_set.concept_des_dep_map.insert(
            11,
            ConceptDescriptorDependencyReapplyData {
                concept_descriptor: con_desc,
                ..Default::default()
            },
        );
        let label_set = calc.process_context_mut().alloc_label_set(label_set);

        let node = calc
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        calc.process_context_mut()
            .node_mut(node)
            .set_reapply_concept_label_set(label_set);

        (calc, node, con_desc)
    }

    fn add_unsat_tags_for_descriptor(
        calc: &mut CalculationAlgorithmContextBase,
        con_desc: ConDescId,
    ) {
        let concept = calc.process_context().con_desc(con_desc).get_concept();
        let con_proc = calc
            .base
            .ontology_arenas
            .alloc_concept_process_data(ConceptProcessData::new());
        calc.base
            .ontology_arenas
            .concept_mut(concept)
            .set_concept_data(con_proc.raw);
        let mut tags = UnsatisfiableCachingTags::new();
        tags.update_caching_tags(11, 0, 1);
        let tags = calc
            .base
            .ontology_arenas
            .alloc_unsatisfiable_caching_tags(tags);
        calc.base
            .ontology_arenas
            .concept_process_data_mut(con_proc)
            .set_unsatisfiable_caching_tags(false, tags);
    }

    fn write_unsat_cache_entry(
        cache_context: &mut CacheContext,
        reader: ReaderId,
        cache_values: &[CacheValue],
        calc: &mut CalculationAlgorithmContextBase,
    ) {
        let cache = cache_context.unsat_cache_reader(reader).cache;
        let CacheContext {
            unsat_caches,
            unsat_cache_entries,
            unsat_cache_entries_hashes,
            unsat_cache_update_slot_items,
            unsat_cache_readers,
            ..
        } = cache_context;
        unsat_caches.get_mut(cache).process_customs_events(
            cache_values,
            unsat_cache_entries,
            unsat_cache_entries_hashes,
            unsat_cache_update_slot_items,
            unsat_cache_readers,
            &mut calc.base.ontology_arenas,
        );
    }

    fn install_hash_hit_handler(calc: &mut CalculationAlgorithmContextBase, con_desc: ConDescId) {
        let (mut cache_context, reader, writer) = cache_context_with_current_tag(0);
        add_unsat_tags_for_descriptor(calc, con_desc);

        let concept = calc.process_context().con_desc(con_desc).get_concept();
        let cache_value =
            CacheValue::new_value(11, concept.raw, CacheValueIdentifier::CacheValTagAndConcept);
        write_unsat_cache_entry(&mut cache_context, reader, &[cache_value], calc);

        let mut handler = UnsatisfiableCacheHandler::new(reader, writer);
        handler.conf_concept_data_unsatisfiable_precheck = false;
        calc.install_used_unsatisfiable_cache_handler(handler, cache_context);
    }

    #[test]
    fn test_individual_node_unsatisfiable_cached_uses_live_handler_and_raises_clash() {
        let (mut calc, node, con_desc) = context_with_labelled_node();
        install_hash_hit_handler(&mut calc, con_desc);

        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_test_occur_unsat_cached = true;
        algo.test_individual_node_unsatisfiable_cached(node, &mut calc);

        match calc.pending_signal() {
            CalcSignal::Clash(clash) => {
                assert!(clash.is_some());
                assert_eq!(
                    calc.process_context()
                        .clash_desc(clash)
                        .get_concept_descriptor(),
                    con_desc
                );
            }
            sig => panic!("expected cache-hit clash signal, got {sig:?}"),
        }
    }

    #[test]
    fn test_individual_node_unsatisfiable_cached_signature_gate_blocks_hit() {
        let (mut calc, node, con_desc) = context_with_labelled_node();
        install_hash_hit_handler(&mut calc, con_desc);

        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_test_occur_unsat_cached = true;
        algo.conf_unsat_caching_use_node_signature_set = true;
        algo.test_individual_node_unsatisfiable_cached(node, &mut calc);

        assert_eq!(calc.pending_signal(), CalcSignal::Continue);
        assert!(calc.base.used_unsat_cache_handler_state.is_some());
        assert_eq!(algo.last_unsat_cache_tested_indi_node, node);
        assert_eq!(algo.last_unsat_cache_tested_indi_node_concept_set_size, 1);
    }
}
