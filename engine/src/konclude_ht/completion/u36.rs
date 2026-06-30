//! `completion::u36` — Generic helpers / accessors / label tests family, batch
//! (port unit #36 of 36 — the LAST completion unit).
//!
//! Faithful port of the 19 methods the manifest (`01-completion-methods.md`,
//! "Unit 36") groups under the individual-node localisation accessors + the
//! concept-adding helpers + the concept-descriptor pool of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) are noted on each item.
//!
//! Methods (cpp order):
//!   * `getUpToDateIndividual(cint64 indiID,…)`                  [22506–22583]
//!   * `getPropagationSteeringController`                        [25707–25723]
//!   * `getLocalizedIndividual(cint64 indiID,…)`                 [26412–26414]
//!   * `getLocalizedIndividual(CIndividualProcessNode*,bool,…)`  [26416–26444]
//!   * `getSuccessorIndividual`                                  [26446–26461]
//!   * `getLocalizedSuccessorIndividual`                         [26464–26477]
//!   * `getAncestorIndividual`                                   [26480–26488]
//!   * `addConceptToIndividual`                                  [26725–26753]
//!   * `addConceptToIndividualReturnConceptDescriptor`           [26757–26782]
//!   * `setIndividualNodeAncestorConnectionModified`            [26786–26788]
//!   * `setIndividualNodeConceptLabelSetModified`               [26790–26796]
//!   * `isIndividualNodeConceptLabelSetModified`                [26800–26802]
//!   * `createConceptDescriptor`                                 [26809–26817]
//!   * `releaseConceptDescriptor`                               [26820–26824]
//!   * `addConceptsToIndividual(CSortedNegLinker<CConcept*>*,…)` [26829–26869]
//!   * `insertConceptsToIndividualConceptSet`                   [26925–27021]
//!   * `addConceptsToIndividual(CConceptAssertionLinker*,…)`     [27026–27064]
//!   * `addConceptsToIndividual(CXNegLinker<CConcept*>*,…)`      [27068–27106]
//!   * `addConceptsToIndividual(CXSortedNegLinker<CConcept*>*,…)`[27110–27148]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` in/out
//! pointer-references become `&mut NodeId`; a plain `CIndividualProcessNode*`
//! value parameter becomes `NodeId`; `CConcept*` → `ConceptId` (resolved against
//! `calc_alg_context.ontology_arenas()`); `CIndividualLinkEdge*` → `EdgeId`;
//! `CConceptDescriptor*` → `ConDescId`; `CDependencyTrackPoint*` → `TrackPointId`.
//! The per-test arenas are reached through the context as
//! `calc_alg_context.process_context()` / `_mut()`, the databox as
//! `calc_alg_context.processing_data_box{,_mut}()`.
//!
//! KONCLUDE-PORT-NOTE[overload]: C++ overloads the same name on parameter type;
//! Rust cannot, so the port disambiguates by an explicit suffix while keeping the
//! C++ name as the anchor in each doc-comment:
//!   * `getUpToDateIndividual(cint64)`  → `get_up_to_date_individual_by_id`
//!     (the `CIndividualProcessNode*` overload, cpp 22485, is a sibling of another
//!     unit: `get_up_to_date_individual(node, ctx)`);
//!   * `getLocalizedIndividual(cint64)` → `get_localized_individual_by_id`;
//!   * `getLocalizedIndividual(node,bool)` → `get_localized_individual`;
//!   * the four `addConceptsToIndividual` linker overloads collapse to the same
//!     port representation `&[NegLink<ConceptId>]` (every Konclude concept-linker
//!     chain — `CSortedNegLinker`/`CConceptAssertionLinker`/`CXNegLinker`/
//!     `CXSortedNegLinker` — exposes `getData()`/`isNegated()`/`getNext()`, so
//!     they flatten to one slice, the u06/u14 convention) and are distinguished by
//!     the `…_from_*_linker` suffix. The primary `CSortedNegLinker` overload keeps
//!     the bare name `add_concepts_to_individual` (the name the existing u08/u34
//!     call sites use).
//!
//! Deferral landscape. Two leaf subsystems gate the localisation accessors:
//!   * the LOCALISATION tag protocol — `CIndividualProcessNode::isLocalizationTagUpToDate`
//!     / `CIndividualLinkEdge::isLocalizationTagUpToDate` /
//!     `…->getOppositeIndividual(indi)` / `…->getOppositeIndividualID(indi)` and the
//!     `CProcessTagger::getCurrentLocalizationTag` reader are NOT yet ported (the
//!     edge accessors + the tagger stub have no methods); and
//!   * the databox `getIndividualProcessNodeVector()` / `getIndividualVector()`
//!     trackers + their `getData()/setLocalData()` are process-layer stubs (no
//!     arena lookup yet).
//! So `getSuccessorIndividual`, `getLocalizedSuccessorIndividual`,
//! `getLocalizedIndividual(node,bool)` and `getUpToDateIndividual(cint64)` are kept
//! `// PORT-PENDING` with the faithful structural transcription + the C++ default
//! return; `getAncestorIndividual` and `getLocalizedIndividual(cint64)` ARE live
//! (pure delegation onto the in-unit siblings).
//!
//! The concept-adding helpers ARE substrate-portable in their decisive control
//! flow (the create-descriptor / insert / not-contained / release loop), calling
//! the in-unit siblings (`create_concept_descriptor`, `release_concept_descriptor`,
//! `insert_concepts_to_individual_concept_set`, `set_individual_node_concept_label_set_modified`)
//! and the cross-unit siblings (`add_blocking_core_concept`,
//! `add_concept_preprocessed_to_processing_queue`, `apply_reapply_queue_concepts`)
//! via `self.x(...)`; only the genuine leaves stay deferred: `STATINC` (W3-DEFER[macro]),
//! the `CConceptDescriptor::initConceptDescriptor` derived init (W2 descriptor
//! method — set the public fields directly), the `CCondensedReapplyQueueIterator::hasNext`
//! guard (the iterator is a zero-size stub), the marker-individual / occurrence-statistics
//! hooks (W6), and the `throw CCalculationClashProcessingException` channel
//! (W3-DEFER[exceptions], not yet established at this layer). Logic is documented,
//! never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id, INVALID, NegLink};
use super::super::model::ConceptId;
use super::super::process::ls1::CondensedReapplyQueueIterator;
use super::super::process::{ConDescId, EdgeId, LabelSetId, NodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

/// KONCLUDE-PORT-NOTE[api]: `CAnsweringPropagationSteeringController*` is a Task /
/// answerer-message subsystem class (W6) — until it lands the steering controller
/// is an opaque `Cint64` handle (`INVALID` == `nullptr`).
type PropagationSteeringController = Cint64;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // NODE-RESOLUTION SUPERSESSION: the node-resolution family below
    // (`get_up_to_date_individual_by_id` / `get_localized_individual{,_by_id}` /
    // `get_successor_individual` / `get_localized_successor_individual` /
    // `get_ancestor_individual`) was lifted onto `CalculationAlgorithmContextBase`
    // in `process/node_resolution.rs` (real node-vector + tagger). These
    // algorithm-method stubs are kept for diff-fidelity but are superseded by
    // `ctx.*` — the un-defer wave calls `calc_alg_context.get_up_to_date_individual(…)`
    // etc. directly.
    // =======================================================================
    // getUpToDateIndividual(cint64 indiID, …)  (cpp 22506–22583).
    // =======================================================================

    /// Port of `getUpToDateIndividual(cint64 indiID, CCalculationAlgorithmContextBase*)`.
    /// cpp 22506–22583. KONCLUDE-PORT-NOTE[overload]: the `cint64` overload — see
    /// the bare-`NodeId` sibling `get_up_to_date_individual` (cpp 22485, other unit).
    pub fn get_up_to_date_individual_by_id(
        &mut self,
        indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // W3-DEFER[macro]: STATINC(INDINODEUPDATELOADCOUNT, calcAlgContext);
        //
        // PORT-PENDING: faithful transcription of cpp 22506–22583. Outline:
        //
        //   indiProcNodeVec = calcAlgContext->getProcessingDataBox()->getIndividualProcessNodeVector();
        //   upToDateIndi = indiProcNodeVec->getData(indiID);
        //   if (!upToDateIndi) {
        //     indiVec = calcAlgContext->getProcessingDataBox()->getIndividualVector(false);
        //     if (indiVec && indiID <= 0) {
        //       individual = indiVec->getData(-indiID);
        //       if (!individual) individual = createNewTemporaryNominalIndividual(-indiID, ctx);   // sibling
        //       if (individual) {
        //         trackIndividualReferredDependence(indiID, ctx);                                   // dep sibling
        //         STATINC(INDINODELOCALIZEDLOADCOUNT, ctx);
        //         localicedIndi = ctx.used_process_context_mut().alloc_node(IndividualProcessNode::new(procCtx));
        //         depTrackPoint = ctx.getBaseDependencyNode()->getContinueDependencyTrackPoint();
        //         localicedIndi.init_dependency_tracker(depTrackPoint);
        //         localicedIndi.set_nominal_individual(individual);
        //         localicedIndi.set_individual_type(NOMINALINDIVIDUALTYPE);
        //         localicedIndi.set_individual_node_id(indiID);
        //         indiProcNodeVec->setLocalData(localicedIndi.individual_node_id(), localicedIndi);
        //         localicedIndi.set_assertion_role_linker(individual->getAssertionRoleLinker());
        //         localicedIndi.set_reverse_assertion_role_linker(individual->getReverseAssertionRoleLinker());
        //         localicedIndi.set_assertion_data_linker(individual->getAssertionDataLinker());
        //         localicedIndi.set_role_assertion_creation_id(databox.next_role_assertion_creation_id());
        //         localicedIndi.set_nominal_individual_triples_assertions(true);
        //         univConnNomValueConcept = databox->getOntology()->getTBox()->getUniversalConnectionNominalValueConcept();
        //         if (univConnNomValueConcept) self.add_concept_to_individual(univConnNomValueConcept,false,localicedIndi,depTrackPoint,true,true,ctx);
        //         nominalConcept = individual->getIndividualNominalConcept();
        //         if (nominalConcept) self.add_concept_to_individual(nominalConcept,false,localicedIndi,depTrackPoint,true,true,ctx);
        //         if (mOptConsistenceNodeMarking) localicedIndi.add_processing_restriction_flags(PRF_CONSNODEPREPARATIONINDINODE);
        //         if (!mOptIncrementalCompatibleExpansion) {
        //           expansionBlocked = false;
        //           if (loadIndividualNodeDataFromBackendCache(localicedIndi, ctx)) {              // backend siblings
        //             localicedIndi.set_nominal_individual_representative_backend_data_loaded(true);
        //             initializeIndividualNodeWithBackendCache(localicedIndi, ctx);
        //             expansionBlocked = tryEstablishExpansionBlockingWithBackendCacheSynchronisation(localicedIndi, ctx);
        //           }
        //           if (!expansionBlocked) self.add_individual_to_processing_queue(localicedIndi, ctx);
        //         } else {
        //           localicedIndi.set_assertion_concept_linker(individual->getAssertionConceptLinker());
        //           localicedIndi.set_incremental_expansion_id(databox.incremental_expansion_id());
        //           localicedIndi.add_processing_restriction_flags(PRF_INCREMENTALEXPANDING);
        //           expData = localicedIndi.incremental_expansion_data(true);
        //           expData->setExpansionID(databox.next_incremental_individual_expansion_id(true));
        //         }
        //         upToDateIndi = localicedIndi;
        //       }
        //     }
        //   }
        //   return upToDateIndi;
        //
        // NOW LIVE: superseded by the node-resolution keystone on
        // `CalculationAlgorithmContextBase` (`process/node_resolution.rs`). The
        // vector-hit path is delegated to `ctx.get_up_to_date_individual_by_id`; the
        // miss path (createNewTemporaryNominalIndividual + backend-cache load) stays
        // deferred INSIDE the keystone (W3-DEFER there), so the verdicts match.
        calc_alg_context.get_up_to_date_individual_by_id(indi_id)
    }

    // =======================================================================
    // getPropagationSteeringController  (cpp 25707–25723).
    // =======================================================================

    /// Port of `getPropagationSteeringController`. cpp 25707–25723.
    pub fn get_propagation_steering_controller(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> PropagationSteeringController {
        // answererMessageAdapter = ctx->getSatisfiableCalculationTask()->getSatisfiableAnswererBindingPropagationAdapter();
        // if (answererMessageAdapter) {
        //   propagationSteeringController = answererMessageAdapter->getAnswererPropagationSteeringController();
        //   if (propagationSteeringController) return propagationSteeringController;
        // }
        // answererPropMessageAdapter = ctx->getSatisfiableCalculationTask()->getSatisfiableAnswererInstancePropagationMessageAdapter();
        // if (answererPropMessageAdapter) {
        //   propagationSteeringController = answererPropMessageAdapter->getAnswererPropagationSteeringController();
        //   if (propagationSteeringController) return propagationSteeringController;
        // }
        // return nullptr;
        //
        // W6-DEFER[api]: the `CSatisfiableCalculationTask` answerer binding-propagation /
        // instance-propagation message adapters and their `getAnswererPropagationSteeringController`
        // are the Task / answerer-message subsystem (W6); none reachable here. The two
        // null-guarded fall-throughs collapse to the C++ default of `nullptr`.
        let _ = calc_alg_context;
        INVALID
    }

    // =======================================================================
    // getLocalizedIndividual overloads + successor/ancestor (cpp 26412–26488).
    // =======================================================================

    /// Port of `getLocalizedIndividual(cint64 indiID, CCalculationAlgorithmContextBase*)`.
    /// cpp 26412–26414. KONCLUDE-PORT-NOTE[overload]: the `cint64` overload —
    /// pure delegation: `getLocalizedIndividual(getUpToDateIndividual(indiID,ctx),false,ctx)`.
    pub fn get_localized_individual_by_id(
        &mut self,
        indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let up_to_date = self.get_up_to_date_individual_by_id(indi_id, calc_alg_context);
        self.get_localized_individual(up_to_date, false, calc_alg_context)
    }

    /// Port of `getLocalizedIndividual(CIndividualProcessNode* indi, bool updateIndividual,
    /// CCalculationAlgorithmContextBase*)`. cpp 26416–26444.
    pub fn get_localized_individual(
        &mut self,
        indi: NodeId,
        update_individual: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 26416–26444. Outline:
        //
        //   if (!indi->isLocalizationTagUpToDate(ctx->getUsedProcessTagger()->getCurrentLocalizationTag())) {
        //     if (updateIndividual) indi = self.get_up_to_date_individual(indi, ctx);          // node overload sibling
        //     if (!indi->isLocalizationTagUpToDate(...)) {
        //       STATINC(INDINODELOCALIZEDLOADCOUNT, ctx);
        //       indiProcNodeVec = ctx->getProcessingDataBox()->getIndividualProcessNodeVector();
        //       localicedIndi = ctx.used_process_context_mut().alloc_node(IndividualProcessNode::new(procCtx));
        //       localicedIndi.init_individual_process_node(indi);
        //       indiProcNodeVec->setLocalData(localicedIndi.individual_node_id(), localicedIndi);
        //       if (ctx->hasCompletionGraphCachedIndividualNodes() && mConfCompletionGraphCaching) {
        //         if (localicedIndi.individual_node_id() <= ctx.max_completion_graph_cached_individual_node_id()) {
        //           if (indi->getLocalizationTag() <= ctx.completion_graph_cached_localization_tag()) {
        //             trackIndividualReferredDependence(indi.individual_node_id(), ctx);          // dep sibling
        //             localicedIndi.clear_processing_queued();
        //             localicedIndi.clear_processing_restriction_flags(PRF_CACHEDCOMPUTEDTYPESADDED);
        //             localicedIndi.add_processing_restriction_flags(PRF_COMPLETIONGRAPHCACHED);
        //           }
        //         }
        //       }
        //       return localicedIndi;
        //     }
        //   }
        //   return indi;
        //
        // NOW LIVE: superseded by `ctx.get_localized_individual` (node-resolution
        // keystone) — the tagger reader + node arena + databox node-vector setLocalData
        // + `init_individual_process_node` are wired there. The completion-graph-cache
        // re-flag branch (.cpp 26430–26439) stays deferred inside the keystone.
        calc_alg_context.get_localized_individual(indi, update_individual)
    }

    /// Port of `getSuccessorIndividual`. cpp 26446–26461.
    /// KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode*& indi` → `&mut NodeId`;
    /// `CIndividualLinkEdge* link` → `EdgeId`.
    pub fn get_successor_individual(
        &mut self,
        indi: &mut NodeId,
        link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 26446–26461. Outline:
        //
        //   succIndi = nullptr;
        //   if (link->isLocalizationTagUpToDate(ctx->getUsedProcessTagger()->getCurrentLocalizationTag())) {
        //     succIndi = link->getOppositeIndividual(indi);
        //   } else {
        //     STATINC(INDINODEUPDATELOADCOUNT, ctx);
        //     succIndi = link->getOppositeIndividual(indi);
        //     if (!succIndi->isLocalizationTagUpToDate(...) && succIndi->isRelocalized()) {       // is_relocalized() IS live (pn1)
        //       succIndiId = link->getOppositeIndividualID(indi);
        //       indiProcNodeVec = ctx->getProcessingDataBox()->getIndividualProcessNodeVector();
        //       succIndi = indiProcNodeVec->getData(succIndiId);
        //     }
        //   }
        //   return succIndi;
        //
        // NOW LIVE: superseded by `ctx.get_successor_individual` (node-resolution
        // keystone) — the edge localisation-tag protocol + opposite-individual
        // resolution + databox node-vector are wired there.
        calc_alg_context.get_successor_individual(indi, link)
    }

    /// Port of `getLocalizedSuccessorIndividual`. cpp 26464–26477.
    pub fn get_localized_successor_individual(
        &mut self,
        indi: &mut NodeId,
        link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 26464–26477. Outline:
        //
        //   succIndi = nullptr;
        //   if (link->isLocalizationTagUpToDate(ctx->getUsedProcessTagger()->getCurrentLocalizationTag())) {
        //     succIndi = link->getOppositeIndividual(indi);
        //   } else {
        //     STATINC(INDINODEUPDATELOADCOUNT, ctx);
        //     succIndiId = link->getOppositeIndividualID(indi);
        //     indiProcNodeVec = ctx->getProcessingDataBox()->getIndividualProcessNodeVector();
        //     succIndi = indiProcNodeVec->getData(succIndiId);
        //     succIndi = self.get_localized_individual(succIndi, false, ctx);
        //   }
        //   return succIndi;
        //
        // NOW LIVE: superseded by `ctx.get_localized_successor_individual`
        // (node-resolution keystone), which resolves the opposite individual through
        // the node vector and then localises it.
        calc_alg_context.get_localized_successor_individual(indi, link)
    }

    /// Port of `getAncestorIndividual`. cpp 26480–26488.
    pub fn get_ancestor_individual(
        &mut self,
        indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // ancIndi = nullptr;
        // ancLink = indi->getAncestorLink();
        // if (ancLink) ancIndi = getSuccessorIndividual(indi, ancLink, ctx);
        // return ancIndi;
        //
        // NOW LIVE: superseded by `ctx.get_ancestor_individual` (node-resolution
        // keystone), which follows the ancestor link through `get_successor_individual`.
        calc_alg_context.get_ancestor_individual(indi)
    }

    // =======================================================================
    // addConceptToIndividual + …ReturnConceptDescriptor (cpp 26725–26782).
    // =======================================================================

    /// Port of `addConceptToIndividual`. cpp 26725–26753.
    /// KONCLUDE-PORT-NOTE[ownership]: `CConcept* addingConcept` → `ConceptId`;
    /// `CIndividualProcessNode*& processIndi` → `&mut NodeId`.
    pub fn add_concept_to_individual(
        &mut self,
        adding_concept: ConceptId,
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // conProQueue = processIndi->getConceptProcessingQueue(true);
        // conLabelSet = processIndi->getReapplyConceptLabelSet(true);
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_concept_processing_queue(true);
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_reapply_concept_label_set(true);
        // KONCLUDE_ASSERT_X(dependencyTrackPoint / addingConcept) — debug asserts, elided.

        // conceptDescriptor = createConceptDescriptor(ctx);
        // conceptDescriptor->initConceptDescriptor(addingConcept, negate, dependencyTrackPoint);
        let concept_descriptor = self.create_concept_descriptor(calc_alg_context);
        self.init_concept_descriptor_fields(
            concept_descriptor,
            adding_concept,
            negate,
            dependency_track_point,
            calc_alg_context,
        );
        let mut reapply_it = CondensedReapplyQueueIterator;
        let contained = self.insert_concepts_to_individual_concept_set(
            concept_descriptor,
            dependency_track_point,
            process_indi,
            con_label_set,
            Some(&mut reapply_it),
            allow_initalization,
            calc_alg_context,
        );
        if !contained {
            // W3-DEFER[macro]: STATINC(CONCEPTSADDEDINDINODELABELSETCOUNT, ctx);
            self.stat_con_des_insertion_count += 1;
            self.add_blocking_core_concept(
                concept_descriptor,
                *process_indi,
                con_label_set,
                calc_alg_context,
            );
            self.set_individual_node_concept_label_set_modified(process_indi, calc_alg_context);
            // KONCLUDE-PORT-NOTE[overload]: the C++ `addConceptPreprocessedToProcessingQueue`
            // call here is the `bool allowPreprocessing` overload (cpp 27228) — ported as
            // the `…_skip` sibling (u04); the `cint64 bindingCount` overload keeps the bare name.
            self.add_concept_preprocessed_to_processing_queue_skip(
                concept_descriptor,
                dependency_track_point,
                con_pro_queue,
                *process_indi,
                allow_preprocessing,
                calc_alg_context,
                INVALID,
            );
            // if (reapplyIt.hasNext()) { applyReapplyQueueConcepts(processIndi, &reapplyIt, ctx); }
            // W3-DEFER[api]: `CCondensedReapplyQueueIterator::hasNext` — the iterator is a
            // zero-size stub (no populated entries yet); the guarded reapply
            // (`apply_reapply_queue_concepts(process_indi, &mut reapply_it, ctx)`) lands
            // once the condensed-reapply-queue iterator is ported.
        } else {
            self.stat_con_des_contained_count += 1;
            self.release_concept_descriptor(concept_descriptor, calc_alg_context);
        }
    }

    /// Port of `addConceptToIndividualReturnConceptDescriptor`. cpp 26757–26782.
    pub fn add_concept_to_individual_return_concept_descriptor(
        &mut self,
        adding_concept: ConceptId,
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ConDescId {
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_concept_processing_queue(true);
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_reapply_concept_label_set(true);
        // KONCLUDE_ASSERT_X(…) — debug asserts, elided.

        let concept_descriptor = self.create_concept_descriptor(calc_alg_context);
        self.init_concept_descriptor_fields(
            concept_descriptor,
            adding_concept,
            negate,
            dependency_track_point,
            calc_alg_context,
        );
        let mut reapply_it = CondensedReapplyQueueIterator;
        // NB: this variant does NOT branch on `contained` — it always treats the
        // concept as freshly inserted (the C++ ignores the return).
        self.insert_concepts_to_individual_concept_set(
            concept_descriptor,
            dependency_track_point,
            process_indi,
            con_label_set,
            Some(&mut reapply_it),
            allow_initalization,
            calc_alg_context,
        );
        self.stat_con_des_insertion_count += 1;

        // W3-DEFER[macro]: STATINC(CONCEPTSADDEDINDINODELABELSETCOUNT, ctx);
        self.add_blocking_core_concept(
            concept_descriptor,
            *process_indi,
            con_label_set,
            calc_alg_context,
        );
        self.set_individual_node_concept_label_set_modified(process_indi, calc_alg_context);
        // KONCLUDE-PORT-NOTE[overload]: `bool allowPreprocessing` overload (cpp 27228) → `…_skip` sibling.
        self.add_concept_preprocessed_to_processing_queue_skip(
            concept_descriptor,
            dependency_track_point,
            con_pro_queue,
            *process_indi,
            allow_preprocessing,
            calc_alg_context,
                INVALID,
        );
        // if (reapplyIt.hasNext()) applyReapplyQueueConcepts(processIndi, &reapplyIt, ctx);
        // W3-DEFER[api]: condensed-reapply-queue iterator stub (see add_concept_to_individual).
        concept_descriptor
    }

    // =======================================================================
    // Modification flags + label-set modification tests (cpp 26786–26802).
    // =======================================================================

    /// Port of `setIndividualNodeAncestorConnectionModified`. cpp 26786–26788.
    pub fn set_individual_node_ancestor_connection_modified(
        &mut self,
        indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // propagateIndividualNodeModified(indi, ctx);
        self.propagate_individual_node_modified(indi, calc_alg_context);
    }

    /// Port of `setIndividualNodeConceptLabelSetModified`. cpp 26790–26796.
    pub fn set_individual_node_concept_label_set_modified(
        &mut self,
        indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // processTagger = ctx->getUsedProcessTagger();
        // processTagger->incConceptLabelSetModificationTag();
        // indi->getReapplyConceptLabelSet(true)->updateConceptLabelSetModificationTag(processTagger);
        // ctx->setMinModificationIndividualCandidate(indi);
        // propagateIndividualNodeModified(indi, ctx);
        //
        // W3-DEFER[api]: `CProcessTagger::incConceptLabelSetModificationTag` (tagger stub
        // has no methods), `CReapplyConceptLabelSet::updateConceptLabelSetModificationTag`
        // (label-set modification-tag protocol not yet ported), and
        // `CCalculationAlgorithmContext::setMinModificationIndividualCandidate` (no ctx
        // setter yet). The label-set is still materialised (matching the C++
        // `getReapplyConceptLabelSet(true)` side effect) and the node-modified
        // propagation IS live.
        let _con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*indi)
            .get_reapply_concept_label_set(true);
        self.propagate_individual_node_modified(indi, calc_alg_context);
    }

    /// Port of `isIndividualNodeConceptLabelSetModified`. cpp 26800–26802.
    pub fn is_individual_node_concept_label_set_modified(
        &mut self,
        indi: &mut NodeId,
        mod_tag: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // return indi->getReapplyConceptLabelSet(false)->isConceptLabelSetModificationTagUpToDate(modTag);
        //
        // W3-DEFER[api]: `CReapplyConceptLabelSet::isConceptLabelSetModificationTagUpToDate`
        // — the label-set modification-tag protocol is not yet ported. C++ default (an
        // unmodified / tag-up-to-date label set) is `false` here (no modification seen).
        let _label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*indi)
            .get_reapply_concept_label_set(false);
        let _ = mod_tag;
        false
    }

    // =======================================================================
    // Concept-descriptor pool (cpp 26809–26824).
    // =======================================================================

    /// Port of `createConceptDescriptor`. cpp 26809–26817.
    pub fn create_concept_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ConDescId {
        // processingDataBox = ctx->getUsedProcessingDataBox();
        // conDes = processingDataBox->takeRemainingConceptDescriptor();
        // if (!conDes) conDes = CObjectAllocator<CConceptDescriptor>::allocateAndConstruct(taskMemMan);
        // return conDes;
        let con_des = calc_alg_context
            .processing_data_box_mut()
            .take_remaining_concept_descriptor();
        if con_des == ConDescId::NONE {
            // KONCLUDE-PORT-NOTE[memory-pool]: the pool allocator becomes an arena
            // allocation from the per-test concept-descriptor arena.
            calc_alg_context
                .process_context_mut()
                .alloc_con_desc(super::super::process::descriptor::ConceptDescriptor::new())
        } else {
            con_des
        }
    }

    /// Port of `releaseConceptDescriptor`. cpp 26820–26824.
    pub fn release_concept_descriptor(
        &mut self,
        con_des: ConDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // conDes->clearNext();
        // processingDataBox = ctx->getUsedProcessingDataBox();
        // processingDataBox->addRemainingConceptDescriptor(conDes);
        calc_alg_context
            .process_context_mut()
            .con_desc_mut(con_des)
            .set_next(ConDescId::NONE); // clearNext()
        calc_alg_context
            .processing_data_box_mut()
            .add_remaining_concept_descriptor(con_des);
    }

    // =======================================================================
    // addConceptsToIndividual linker overloads (cpp 26829, 27026, 27068, 27110)
    // + insertConceptsToIndividualConceptSet (cpp 26925).
    // =======================================================================

    /// Port of `addConceptsToIndividual(CSortedNegLinker<CConcept*>* conceptAddLinkerIt, …)`.
    /// cpp 26829–26869. The primary linker overload (keeps the bare name).
    /// KONCLUDE-PORT-NOTE[overload]: the `CSortedNegLinker<CConcept*>` chain →
    /// `&[NegLink<ConceptId>]` (head→tail). This overload (and ONLY this one)
    /// increments `conCount` and writes it back through `concept_count`.
    pub fn add_concepts_to_individual(
        &mut self,
        concept_add_linker_it: &[NegLink<ConceptId>],
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        concept_count: Option<&mut Cint64>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_concept_processing_queue(true);
        // KONCLUDE_ASSERT_X(dependencyTrackPoint) — elided.

        let mut con_count: Cint64 = 0;
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_reapply_concept_label_set(true);
        for link in concept_add_linker_it {
            let concept = link.target;
            let con_neg = link.negated ^ negate;
            // KONCLUDE_ASSERT_X(concept) — elided.
            self.add_one_concept_to_individual_concept_set(
                concept,
                con_neg,
                process_indi,
                dependency_track_point,
                con_label_set,
                con_pro_queue,
                allow_preprocessing,
                allow_initalization,
                calc_alg_context,
            );
            con_count += 1;
        }
        if let Some(out) = concept_count {
            *out = con_count;
        }
    }

    /// Port of `addConceptsToIndividual(CConceptAssertionLinker* conceptAddLinkerIt, …)`.
    /// cpp 27026–27064. KONCLUDE-PORT-NOTE[overload]: the `CConceptAssertionLinker`
    /// chain → `&[NegLink<ConceptId>]`. NB this overload computes `conCount` but
    /// never increments it (the C++ loop has no `++conCount`), so `*conceptCount`
    /// is always written `0` — ported EXACTLY.
    pub fn add_concepts_to_individual_from_assertion_linker(
        &mut self,
        concept_add_linker_it: &[NegLink<ConceptId>],
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        concept_count: Option<&mut Cint64>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_concept_processing_queue(true);
        let con_count: Cint64 = 0; // C++ never increments conCount in this overload.
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_reapply_concept_label_set(true);
        for link in concept_add_linker_it {
            let concept = link.target;
            let con_neg = link.negated ^ negate;
            self.add_one_concept_to_individual_concept_set(
                concept,
                con_neg,
                process_indi,
                dependency_track_point,
                con_label_set,
                con_pro_queue,
                allow_preprocessing,
                allow_initalization,
                calc_alg_context,
            );
        }
        if let Some(out) = concept_count {
            *out = con_count;
        }
    }

    /// Port of `addConceptsToIndividual(CXNegLinker<CConcept*>* conceptAddLinkerIt, …)`.
    /// cpp 27068–27106. KONCLUDE-PORT-NOTE[overload]: `CXNegLinker<CConcept*>` chain
    /// → `&[NegLink<ConceptId>]`. Same as the assertion-linker overload, this one
    /// also never increments `conCount`.
    pub fn add_concepts_to_individual_from_neg_linker(
        &mut self,
        concept_add_linker_it: &[NegLink<ConceptId>],
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        concept_count: Option<&mut Cint64>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_concept_processing_queue(true);
        let con_count: Cint64 = 0; // C++ never increments conCount in this overload.
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_reapply_concept_label_set(true);
        for link in concept_add_linker_it {
            let concept = link.target;
            let con_neg = link.negated ^ negate;
            self.add_one_concept_to_individual_concept_set(
                concept,
                con_neg,
                process_indi,
                dependency_track_point,
                con_label_set,
                con_pro_queue,
                allow_preprocessing,
                allow_initalization,
                calc_alg_context,
            );
        }
        if let Some(out) = concept_count {
            *out = con_count;
        }
    }

    /// Port of `addConceptsToIndividual(CXSortedNegLinker<CConcept*>* conceptAddLinkerIt, …)`.
    /// cpp 27110–27148. KONCLUDE-PORT-NOTE[overload]: `CXSortedNegLinker<CConcept*>`
    /// chain → `&[NegLink<ConceptId>]`. Identical body to the `CXNegLinker` overload
    /// except the C++ reads `getData()` before the negation (immaterial); also never
    /// increments `conCount`.
    pub fn add_concepts_to_individual_from_sorted_neg_linker(
        &mut self,
        concept_add_linker_it: &[NegLink<ConceptId>],
        negate: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        concept_count: Option<&mut Cint64>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_concept_processing_queue(true);
        let con_count: Cint64 = 0; // C++ never increments conCount in this overload.
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*process_indi)
            .get_reapply_concept_label_set(true);
        for link in concept_add_linker_it {
            let concept = link.target;
            let con_neg = link.negated ^ negate;
            self.add_one_concept_to_individual_concept_set(
                concept,
                con_neg,
                process_indi,
                dependency_track_point,
                con_label_set,
                con_pro_queue,
                allow_preprocessing,
                allow_initalization,
                calc_alg_context,
            );
        }
        if let Some(out) = concept_count {
            *out = con_count;
        }
    }

    /// The shared inner body of the four `addConceptsToIndividual` linker overloads
    /// (the per-element create-descriptor / insert / not-contained / release block,
    /// cpp 26845–26864 and the byte-identical copies at 27041–27058 / 27083–27100 /
    /// 27125–27142). KONCLUDE-PORT-NOTE[overload]: factored out because the four C++
    /// overloads differ ONLY in their linker iteration; the per-concept work is
    /// literally identical. This is a port-internal helper, not a Konclude method.
    fn add_one_concept_to_individual_concept_set(
        &mut self,
        concept: ConceptId,
        con_neg: bool,
        process_indi: &mut NodeId,
        dependency_track_point: TrackPointId,
        con_label_set: LabelSetId,
        con_pro_queue: super::super::process::stubs::ConceptProcessingQueueId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // conceptDescriptor = createConceptDescriptor(ctx);
        // conceptDescriptor->initConceptDescriptor(concept, conNeg, dependencyTrackPoint);
        let concept_descriptor = self.create_concept_descriptor(calc_alg_context);
        self.init_concept_descriptor_fields(
            concept_descriptor,
            concept,
            con_neg,
            dependency_track_point,
            calc_alg_context,
        );
        let mut reapply_it = CondensedReapplyQueueIterator;
        let contained = self.insert_concepts_to_individual_concept_set(
            concept_descriptor,
            dependency_track_point,
            process_indi,
            con_label_set,
            Some(&mut reapply_it),
            allow_initalization,
            calc_alg_context,
        );
        if !contained {
            self.stat_con_des_insertion_count += 1;
            // W3-DEFER[macro]: STATINC(CONCEPTSADDEDINDINODELABELSETCOUNT, ctx);
            self.add_blocking_core_concept(
                concept_descriptor,
                *process_indi,
                con_label_set,
                calc_alg_context,
            );
            self.set_individual_node_concept_label_set_modified(process_indi, calc_alg_context);
            // KONCLUDE-PORT-NOTE[overload]: the C++ `addConceptPreprocessedToProcessingQueue`
            // call here is the `bool allowPreprocessing` overload (cpp 27228) — ported as
            // the `…_skip` sibling (u04); the `cint64 bindingCount` overload keeps the bare name.
            self.add_concept_preprocessed_to_processing_queue_skip(
                concept_descriptor,
                dependency_track_point,
                con_pro_queue,
                *process_indi,
                allow_preprocessing,
                calc_alg_context,
                INVALID,
            );
            // if (reapplyIt.hasNext()) applyReapplyQueueConcepts(processIndi, &reapplyIt, ctx);
            // W3-DEFER[api]: condensed-reapply-queue iterator stub (see add_concept_to_individual).
        } else {
            self.stat_con_des_contained_count += 1;
            self.release_concept_descriptor(concept_descriptor, calc_alg_context);
        }
    }

    /// Port of `insertConceptsToIndividualConceptSet`. cpp 26925–27021.
    /// KONCLUDE-PORT-NOTE[ownership]: `CConceptDescriptor*` → `ConDescId`,
    /// `CReapplyConceptLabelSet*` → `LabelSetId`,
    /// `CCondensedReapplyQueueIterator*` → `Option<&mut CondensedReapplyQueueIterator>`.
    pub fn insert_concepts_to_individual_concept_set(
        &mut self,
        concept_descriptor: ConDescId,
        dependency_track_point: TrackPointId,
        process_indi: &mut NodeId,
        con_label_set: LabelSetId,
        reapply_it: Option<&mut CondensedReapplyQueueIterator>,
        allow_initalization: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // clashedConceptDescriptor = nullptr; clashedDependencyTrackPoint = nullptr;
        let mut clashed_concept_descriptor: ConDescId = Id::NONE;
        let mut clashed_dependency_track_point: TrackPointId = Id::NONE;

        // if (mConfConceptUnsatisfiabilitySaturatedTesting) {
        //   if (isConceptUnsatisfiabilitySaturated(conceptDescriptor->getConcept(), conceptDescriptor->isNegated(), ctx)) {
        //     clashConDesLinker = createClashedConceptDescriptor(nullptr, processIndi, conceptDescriptor, dependencyTrackPoint, ctx);
        //     throw CCalculationClashProcessingException(clashConDesLinker);
        //   }
        // }
        if self.conf_concept_unsatisfiability_saturated_testing {
            let con = calc_alg_context
                .process_context()
                .con_desc(concept_descriptor)
                .get_concept();
            let neg = calc_alg_context
                .process_context()
                .con_desc(concept_descriptor)
                .is_negated();
            if self.is_concept_unsatisfiability_saturated(con, neg, calc_alg_context) {
                // W3-DEFER[exceptions]: createClashedConceptDescriptor (clash unit) +
                //   throw CCalculationClashProcessingException — the clash-exception channel
                //   is not yet established at this layer. The saturated-unsatisfiability
                //   clash is detected (the guard is live) but the non-local throw is deferred;
                //   the C++ would not fall through, so we early-return `false` (concept not
                //   contained) as the closest local behaviour.
                let _ = (clashed_concept_descriptor, clashed_dependency_track_point);
                return false;
            }
        }

        // contained = conLabelSet->insertConceptGetClash(conceptDescriptor, dependencyTrackPoint,
        //                 reapplyIt, &clashedConceptDescriptor, &clashedDependencyTrackPoint);
        let contained = calc_alg_context
            .process_context_mut()
            .label_set_mut(con_label_set)
            .insert_concept_get_clash(
                concept_descriptor,
                dependency_track_point,
                reapply_it,
                Some(&mut clashed_concept_descriptor),
                Some(&mut clashed_dependency_track_point),
            );

        if !contained {
            // if (allowInitalization && !processIndi->getIndividualInitializationConcept())
            //     processIndi->setIndividualInitializationConcept(conceptDescriptor);
            if allow_initalization {
                let has_init = calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .individual_initialization_concept();
                if has_init == ConDescId::NONE {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(*process_indi)
                        .set_individual_initialization_concept(concept_descriptor);
                }
            }
            // nondeterministically = hasNondeterministicDependency(dependencyTrackPoint, ctx);
            let _nondeterministically =
                self.has_nondeterministic_dependency(dependency_track_point, calc_alg_context);
            // if (conceptDescriptor->getConcept()->getOperatorCode() == CCMARKER)
            //   ctx->getProcessingDataBox()->getMarkerIndividualNodeHash(true)
            //       ->addMarkerIndividualNode(conceptDescriptor->getConcept(), processIndi, nondeterministically);
            // W6-DEFER[api]: the marker-individual-node hash (`getMarkerIndividualNodeHash`
            //   + `addMarkerIndividualNode`) and the `CCMARKER` operator-code dispatch are the
            //   marker subsystem — held until the marker hash is wired.
            //
            // if (mConfOccurrenceStatisticsCollecting && mOptCollectOccurrenceStatistics)
            //   mOccStatsCacheHandler->incConceptInstanceOccurrencceStatistics(
            //       conceptDescriptor->getConcept(), nondeterministically, processIndi->getNominalIndividual() == nullptr);
            // W6-DEFER[api]: the occurrence-statistics cache handler (W6 Cache subtree).
        }

        // if (contained && clashedConceptDescriptor) {
        //   clashConDesLinker = createClashedConceptDescriptor(nullptr, processIndi, clashedConceptDescriptor, clashedDependencyTrackPoint, ctx);
        //   clashConDesLinker = createClashedConceptDescriptor(clashConDesLinker, processIndi, conceptDescriptor, dependencyTrackPoint, ctx);
        //   throw CCalculationClashProcessingException(clashConDesLinker);
        // }
        if contained && clashed_concept_descriptor != ConDescId::NONE {
            // W3-DEFER[exceptions]: the two `createClashedConceptDescriptor` links (clash
            //   unit) + `throw CCalculationClashProcessingException` — clash-exception channel
            //   not yet established. The clash IS detected (the guard is live); the non-local
            //   throw is deferred. (The KTRACE debug print is elided.)
            let _ = clashed_dependency_track_point;
        }

        // (the large commented-out biotop/amount-of-substance debug block in the C++ is
        //  dead debug code and is intentionally not ported.)
        contained
    }

    // -----------------------------------------------------------------------
    // Port-internal helper: `CConceptDescriptor::initConceptDescriptor`.
    // -----------------------------------------------------------------------

    /// KONCLUDE-PORT-NOTE[api]: `conceptDescriptor->initConceptDescriptor(concept, negate,
    /// depTrackPoint)` (cpp `CConceptDescriptor::initConceptDescriptor` =
    /// `initNegLinker(concept,negated)` + `initDependencyTracker(depTrackPoint)`) is a
    /// W2-deferred `CConceptDescriptor` derived method (descriptor.rs leaves it pending
    /// because the derived form also computes terminology tags). This unit only needs
    /// the field-init effect, so it writes the public descriptor fields directly through
    /// the arena accessor (the same convention u25 uses for wrapper-less node fields).
    fn init_concept_descriptor_fields(
        &mut self,
        concept_descriptor: ConDescId,
        concept: ConceptId,
        negate: bool,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let cd = calc_alg_context
            .process_context_mut()
            .con_desc_mut(concept_descriptor);
        cd.concept = concept; // initNegLinker data
        cd.negated = negate; // initNegLinker negation
        cd.next = ConDescId::NONE; // initNegLinker next = nullptr
        cd.dep_track_point = dependency_track_point; // initDependencyTracker
    }
}
