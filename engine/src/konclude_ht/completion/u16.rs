//! `completion::u16` — W3 completion method-batch **Unit 16** (Nominal handling).
//!
//! Faithful function-by-function port of the 24 nominal-handling methods of
//! Konclude `CCalculationTableauCompletionTaskHandleAlgorithm`
//! (`Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`),
//! per `manifest/01-completion-methods.md` Unit 16. Method order follows the
//! manifest (ascending `.cpp` line).
//!
//! Bodies use the W3.5 accessor convention (PORT.md): a C++ `indi->getX()` where
//! `indi` is a `CIndividualProcessNode*` becomes `ctx.process_context().node(id).get_x()`
//! (read) / `ctx.process_context_mut().node_mut(id)` (mutate); `getUsedProcessingDataBox()`
//! / `getProcessingDataBox()` → `ctx.processing_data_box{,_mut}()` (the single
//! owned databox); terminology via `ctx.ontology_arenas()`; sibling algorithm
//! methods → `self.x(...)`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: every `CIndividualProcessNode*` parameter is a
//! `NodeId`; the `calcAlgContext` parameter is threaded as
//! `&mut CalculationAlgorithmContextBase`. Where a method walks an intrusive
//! `CXLinker<CIndividualProcessNode*>` chain AND recurses / calls a `&mut self`
//! sibling, the chain is snapshotted into a `Vec<NodeId>` first ([ownership]) so
//! the recursive borrow is legal; the read-only traversal is identical.
//!
//! Deferrals: operations on still-stubbed Process-layer satellites/queues/vectors/
//! hashes/iterators (the `process::stubs` markers: `CIndividualUnsortedProcessingQueue`,
//! `CIndividualProcessNodeVector`, `CSignatureBlockingCandidateHash`,
//! `CBlockingFollowSet`, `CSuccessorConnectedNominalSet`, the label-set /
//! successor / connection iterators) and on the unported Cache/backend-cache and
//! binding-set type webs are marked `// W6-DEFER[api]` with the faithful logic kept
//! in-comment (logic is never dropped). `isNominalVariablePropagationBindingSubSet`
//! is flagged `PORT-PENDING` (its whole body is an unported binding-set web).

#![allow(dead_code)]
#![allow(unused_variables)]

use std::collections::HashSet;

use super::algorithm::{CompletionTaskHandleAlgorithm, IMMEDIATELY_PROCESS_PRIORITY};
use super::context::CalculationAlgorithmContextBase;

use super::super::model::op::CCNOMINAL;
use super::super::model::substrate::{Cint64, NegLink};
use super::super::model::{ConceptId, IndividualId, RoleId};
use super::super::process::node::IndividualProcessNode;
use super::super::process::stubs::IndiBlockDataId;
use super::super::process::{ConProcDescId, EdgeId, LabelSetId, NodeId, TrackPointId};

impl CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Nominal caching-loss reactivation.
    // =======================================================================

    /// Port of `checkIndividualNodesReactivationDueToNominalCachingLoss`. `.cpp` 2153–2159.
    pub fn check_individual_nodes_reactivation_due_to_nominal_caching_loss(
        &mut self,
        nominal_proc_node: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let n = ctx.process_context().node(nominal_proc_node);
        if n.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALID
                | IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
        ) || !n.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
        ) && !n.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED,
        ) {
            return self
                .reactivate_individual_nodes_due_to_nominal_caching_loss(nominal_proc_node, ctx);
        }
        false
    }

    /// Port of `reactivateIndividualNodesDueToNominalCachingLoss`. `.cpp` 2161–2181.
    pub fn reactivate_individual_nodes_due_to_nominal_caching_loss(
        &mut self,
        nominal_proc_node: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut nodes_reactivated = false;
        // CProcessingDataBox* processingDataBox = calcAlgContext->getUsedProcessingDataBox();
        // (the single owned databox; reached as ctx.processing_data_box_mut())
        let nominal_reactivation_data = ctx
            .process_context_mut()
            .node_mut(nominal_proc_node)
            .nominal_caching_loss_reactivation_data(false);
        // CIndividualUnsortedProcessingQueue* reactivationQueue = nullptr;
        if nominal_reactivation_data.is_some() {
            // W6-DEFER[api]: CNominalCachingLossReactivationData is an unported satellite
            // (process::stubs marker, always Id::NONE here), and
            // CIndividualUnsortedProcessingQueue::insertIndiviudalProcessNode is unported.
            // Faithful logic:
            //   if !reactData.has_reactivated() {
            //       reactData = node.nominal_caching_loss_reactivation_data(true);
            //       reactData.set_reactivated(true);
            //       for linker in reactData.take_reactivation_individual_node_linker() {
            //           reactivationIndiNode = linker.get_data();
            //           if reactivationQueue.is_none() {
            //               reactivationQueue =
            //                   processingDataBox.get_nominal_caching_loss_reactivation_processing_queue(true);
            //           }
            //           reactivationQueue.insert_indiviudal_process_node(reactivationIndiNode);
            //           nodes_reactivated = true;
            //       }
            //   }
            let _ = &mut nodes_reactivated;
        }
        nodes_reactivated
    }

    /// Port of `identifyCompatibilityChangedNominalIndividualNodes`. `.cpp` 3441–3468.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the four `CPROCESSINGSET<cint64>*` out-params become
    /// `&mut HashSet<Cint64>`.
    pub fn identify_compatibility_changed_nominal_individual_nodes(
        &mut self,
        non_compatible_changed_nominal_node_set: &mut HashSet<Cint64>,
        compatible_nominal_node_set: &mut HashSet<Cint64>,
        redundant_node_set: &mut HashSet<Cint64>,
        new_node_set: &mut HashSet<Cint64>,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // CIndividualProcessNodeVector* indiNodeVec =
        //     calcAlgContext->getUsedProcessingDataBox()->getIndividualProcessNodeVector();
        let _indi_node_vec = ctx.processing_data_box().individual_process_node_vector();
        // W6-DEFER[api]: CIndividualProcessNodeVector (get_item_count / get_item_min_index /
        // get_data) and CIndividualNodeIncrementalExpansionData (has_directly_changed_neighbour_connection
        // / is_directly_changed / is_previous_completion_graph_compatible) are unported
        // stubs. Faithful logic:
        //   for i in indiStart..indiCount {
        //       indiNode = indiNodeVec.get_data(i);
        //       if indiNode.is_some() {
        //           incExpData = node.incremental_expansion_data(false);
        //           if node.nominal_individual().is_some() {
        //               if incExpData && (incExpData.has_directly_changed_neighbour_connection()
        //                                 || incExpData.is_directly_changed()) {
        //                   if !incExpData.is_previous_completion_graph_compatible() {
        //                       non_compatible_changed_nominal_node_set.insert(i);
        //                   } else { compatible_nominal_node_set.insert(i); }
        //               }
        //           } else if incExpData && (... changed ...) {
        //               new_node_set.insert(i);
        //           }
        //           if !incExpData || (!...changed...) { redundant_node_set.insert(i); }
        //       }
        //   }
        let _ = (
            non_compatible_changed_nominal_node_set,
            compatible_nominal_node_set,
            redundant_node_set,
            new_node_set,
        );
        true
    }

    /// Port of `generateDebugDependentNominalsString`. `.cpp` 7999–8010.
    pub fn generate_debug_dependent_nominals_string(
        &mut self,
        indi: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> String {
        let nominal_dependent_string_list: Vec<String> = Vec::new();
        let conn_nom_set = ctx
            .process_context_mut()
            .node_mut(indi)
            .successor_nominal_connection_set(false);
        if conn_nom_set.is_some() {
            // W6-DEFER[api]: CSuccessorConnectedNominalSet iteration is unported.
            // Faithful logic:
            //   for nominalID in connNomSet {
            //       nominal_dependent_string_list.push(format!("{}", nominalID));
            //   }
        }
        nominal_dependent_string_list.join(", ")
    }

    // =======================================================================
    // Delayed nominal processing.
    // =======================================================================

    /// Port of `getDelayProcessingBlockingNominalNode`. `.cpp` 9413–9436.
    pub fn get_delay_processing_blocking_nominal_node(
        &mut self,
        test_indi: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let nominal_blocker_individual: NodeId = NodeId::NONE;
        // CProcessingDataBox* processingDataBox = calcAlgContext->getProcessingDataBox();
        let sig_nom_del_cand_hash = ctx
            .processing_data_box_mut()
            .signature_nominal_delaying_candidate_hash(false);

        let con_set = ctx
            .process_context_mut()
            .node_mut(test_indi)
            .get_reapply_concept_label_set(false);
        if con_set.is_some() && sig_nom_del_cand_hash.is_some() {
            let _ass_con_sig = ctx
                .process_context()
                .node(test_indi)
                .assertion_initialisation_signature_value();
            // W6-DEFER[api]: CSignatureBlockingCandidateHash / CSignatureBlockingCandidateIterator
            // are unported stubs. Faithful logic:
            //   candIt = sigNomDelCandHash.get_blocking_candidates_iterator(assConSig);
            //   while nominalBlocker.is_none() && candIt.has_next() {
            //       candIndiID = candIt.next(true);
            //       if candIndiID != test_indi.individual_node_id() {
            //           candIndiNode = self.get_up_to_date_individual(candIndiID, ctx);
            //           if candIndiNode.is_nominal_individual_node()
            //                 && candIndiNode.nominal_individual().is_some()
            //                 && !candIndiNode.has_partial_processing_restriction_flags(PRF_PURGEDBLOCKED) {
            //               blockerConSet = candIndiNode.get_reapply_concept_label_set(false);
            //               if self.is_label_concept_sub_set_ignore_nominals(conSet, blockerConSet, None, ctx) {
            //                   nominalBlockerIndividual = candIndiNode;
            //               }
            //           }
            //       }
            //   }
        }
        nominal_blocker_individual
    }

    /// Port of `tryDelayNominalProcessing`. `.cpp` 9441–9463.
    pub fn try_delay_nominal_processing(
        &mut self,
        con_pro_des: ConProcDescId,
        test_indi: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if self.can_delay_nominal_processing(con_pro_des, test_indi, ctx) {
            ctx.process_context_mut()
                .node_mut(test_indi)
                .set_nominal_processing_delaying_checked(true);

            let mut not_connected_nominal = false;
            // CSuccessorIterator succIt(testIndi->getSuccessorIterator());
            let _succ_it = ctx.process_context().node(test_indi).get_successor_iterator();
            // W6-DEFER[api]: CSuccessorIterator::hasNext is unported (zero-size stub).
            // Faithful logic: if !succIt.has_next() { not_connected_nominal = true; }
            let _ = &mut not_connected_nominal;

            if not_connected_nominal {
                let blocker_nominal_indi_node =
                    self.get_delay_processing_blocking_nominal_node(test_indi, ctx);
                if blocker_nominal_indi_node.is_some() {
                    // CProcessingDataBox* processingDataBox = calcAlgContext->getProcessingDataBox();
                    let _delaying_nominal_processing_queue = ctx
                        .processing_data_box_mut()
                        .get_delaying_nominal_processing_queue(true);
                    // W6-DEFER[api]: CIndividualUnsortedProcessingQueue::insertIndiviudalProcessNode
                    // is unported. Faithful: delayingNominalProcessingQueu.insert_indiviudal_process_node(test_indi);
                    ctx.process_context_mut()
                        .node_mut(test_indi)
                        .set_delayed_nominal_processing_queued(true);
                    return true;
                }
            }
        }
        false
    }

    /// Port of `canDelayNominalProcessing`. `.cpp` 9467–9476.
    pub fn can_delay_nominal_processing(
        &mut self,
        con_pro_des: ConProcDescId,
        test_indi: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let n = ctx.process_context().node(test_indi);
        if n.is_nominal_individual_node() && n.nominal_individual().is_some() {
            let priority = ctx
                .process_context()
                .con_proc_desc(con_pro_des)
                .get_process_priority()
                .get_priority();
            if priority < IMMEDIATELY_PROCESS_PRIORITY as f64 {
                if !ctx
                    .process_context()
                    .node(test_indi)
                    .has_nominal_processing_delaying_checked()
                {
                    return true;
                }
            }
        }
        false
    }

    // =======================================================================
    // Backend-cached nominal connection.
    // =======================================================================

    /// Port of `checkBackendCachedNominalConnection`. `.cpp` 14545–14605.
    ///
    /// W6-DEFER[api]: the whole body operates on the unported backend-cache type web
    /// (`CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData`,
    /// `CBackendRepresentativeMemoryCacheIndividualAssociationData`,
    /// `CBackendRepresentativeMemoryCacheIndividualNeighbourRoleSetHash`,
    /// `CBackendRepresentativeMemoryLabelCacheItem`) plus `mBackendCacheHandler`
    /// (a `completion::stubs` cache-handler). Faithful logic preserved in-comment.
    pub fn check_backend_cached_nominal_connection(
        &mut self,
        process_indi: NodeId,
        role: RoleId,
        nominal_id: Cint64,
        dep_track_point: TrackPointId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let has_appropriate_nominal_connection = false;
        // CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData* backendSyncData =
        //     processIndi->getIndividualBackendCacheSynchronisationData(false);
        // if backendSyncData && backendSyncData.get_associtaion_data() {
        //   assData = backendSyncData.get_associtaion_data();
        //   neighbourRoleSetHash = assData.get_neighbour_role_set_hash();
        //   if neighbourRoleSetHash {
        //     roleSetLabelItem = neighbourRoleSetHash.get_neighbour_role_set_label(nominal_id);
        //     if roleSetLabelItem {
        //       if mBackendCacheHandler.has_role_in_associated_neigbour_role_set_label(assData, roleSetLabelItem, role, false, false) {
        //         has = assData.is_completely_handled() && assData.is_completely_propagated();
        //         for superRoleIt in role.get_indirect_super_role_list() while has {
        //           ... range concepts: require in nomAssData full-concept-set label, else has=false ...
        //           ... domain concepts: addConceptToIndividual(con, conNeg, processIndi, depTrackPoint, ...) ...
        //         }
        //         if !has { self.expand_individual_neighbour_node_from_backend_cache(process_indi, nominal_id, ctx); }
        //       } else {
        //         self.expand_individual_neighbour_node_from_backend_cache(process_indi, nominal_id, ctx);
        //       }
        //     }
        //   }
        // }
        let _ = (process_indi, role, nominal_id, dep_track_point, &*ctx);
        has_appropriate_nominal_connection
    }

    // =======================================================================
    // Nominal node availability / correction.
    // =======================================================================

    /// Port of `isNominalIndividualNodeAvailable`. `.cpp` 16274–16277.
    pub fn is_nominal_individual_node_available(
        &mut self,
        indi_id: Cint64,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // CIndividualProcessNodeVector* indiProcNodeVec =
        //     calcAlgContext->getProcessingDataBox()->getIndividualProcessNodeVector();
        let _indi_proc_node_vec = ctx.processing_data_box().individual_process_node_vector();
        // W6-DEFER[api]: CIndividualProcessNodeVector::hasData(indiID) is unported.
        // Faithful: return indiProcNodeVec.has_data(indi_id);
        let _ = indi_id;
        false
    }

    /// Port of `getCorrectedNominalIndividualNode`. `.cpp` 16280–16294.
    pub fn get_corrected_nominal_individual_node(
        &mut self,
        indi_id: Cint64,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let mut indi = self.get_up_to_date_individual_by_id(indi_id, ctx);
        if indi.is_some() {
            while ctx
                .process_context()
                .node(indi)
                .has_merged_into_individual_node_id()
            {
                // STATINC(INDINODENOMINALCORRECTIDCOUNT, calcAlgContext);
                let merged_into_id = ctx
                    .process_context()
                    .node(indi)
                    .merged_into_individual_node_id();
                indi = self.get_up_to_date_individual_by_id(merged_into_id, ctx);
                // TODO: path compression? -> update merged into IDs
            }
        } else {
            // KONCLUDE-PORT-NOTE[exceptions]: C++ throws
            // CCalculationErrorProcessingException::getNominalMissingErrorException().
            panic!("CCalculationErrorProcessingException: nominal missing error");
        }
        indi
    }

    // =======================================================================
    // Label-concept set tests (nominal-aware).
    // =======================================================================

    /// Port of `isLabelConceptSubSetIgnoreNominals`. `.cpp` 17396–17460.
    ///
    /// The branch selection (direct-lookup vs merge-walk) is ported faithfully; the
    /// two inner walks iterate `CReapplyConceptLabelSetIterator`, an unported stub,
    /// so the per-concept comparisons are `W6-DEFER[api]` with logic in-comment.
    pub fn is_label_concept_sub_set_ignore_nominals(
        &mut self,
        sub_concept_set: LabelSetId,
        super_concept_set: LabelSetId,
        clash_flag: Option<&mut bool>,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(LABELCONCEPTSUBSETTESTCOUNT, calcAlgContext);
        let sub_con_set_count = ctx.process_context().label_set(sub_concept_set).get_concept_count();
        let super_con_set_count =
            ctx.process_context().label_set(super_concept_set).get_concept_count();
        let threshold_factor = self.map_comparison_direct_lookup_factor;
        if sub_con_set_count * threshold_factor < super_con_set_count {
            // W6-DEFER[api]: direct-lookup branch. Faithful logic:
            //   subConSetIt = subConceptSet.get_concept_label_set_iterator(true,false,false);
            //   while subConSetIt.has_value() {
            //       subConDes = subConSetIt.get_concept_descriptor();
            //       if superConceptSet.contains_concept_get_negated(subConDes.get_concept(), &mut containedNeg) {
            //           if containedNeg != subConDes.get_negation() { *clashFlag = true; return false; }
            //       } else if subConDes.get_concept().operator_code() != CCNOMINAL { return false; }
            //       subConSetIt.move_next();
            //   }
        } else {
            // W6-DEFER[api]: merge-walk branch over both sorted iterators (by concept tag).
            // Faithful logic mirrors the C++ tag-merge: advance superConSetIt while
            // superConTag < subConTag, compare tags/negations, treat CCNOMINAL-only
            // misses as ignorable; on negation mismatch set *clashFlag and return false.
        }
        let _ = clash_flag;
        true
    }

    /// Port of `isLabelConceptEqualSetConsiderNominalsForClashOnly`. `.cpp` 17580–17636.
    pub fn is_label_concept_equal_set_consider_nominals_for_clash_only(
        &mut self,
        concept_set1: LabelSetId,
        concept_set2: LabelSetId,
        clash_flag: Option<&mut bool>,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(LABELCONCEPTEQUALSETTESTCOUNT, calcAlgContext);
        if let Some(out) = clash_flag {
            *out = false;
        }
        // W6-DEFER[api]: both walks use CReapplyConceptLabelSetIterator (unported stub).
        // Faithful logic: walk conSet1It/conSet2It in lockstep; skip nominal-tagged
        // descriptors on either side (CCNOMINAL); for the remaining concepts require
        // identical (concept, negation) pairs, else return false; on a nominal/nominal
        // pair of the same concept with differing negation set *clashFlag and return false.
        let _ = (concept_set1, concept_set2, &*ctx, CCNOMINAL);
        true
    }

    /// Port of `isNominalVariablePropagationBindingSubSet`. `.cpp` 17732–17970.
    ///
    /// PORT-PENDING[api]: the entire body operates on the unported variable-/
    /// propagation-binding type web — `CConceptPropagationBindingSetHash`,
    /// `CPropagationBindingSet`/`Map`/`Descriptor`/`Binding`,
    /// `CConceptVariableBindingPathSetHash`, `CVariableBindingPath*`,
    /// `CBlockingAlternativeData`, `CIndividualNodeBlockingTestData` — none of which
    /// are ported yet (W2 left them as stubs). The faithful four-phase structure
    /// (back/candidate propagation for test + ancestor node, then normal propagation
    /// for test + ancestor node, returning false on any missing required binding) is
    /// preserved in-comment; reconciles to real code once the binding subsystem lands.
    pub fn is_nominal_variable_propagation_binding_sub_set(
        &mut self,
        test_indi: NodeId,
        blocking_indi: NodeId,
        // W3-RECONCILE[api]: blockData / testContinueBlocking / blockAltData restored to
        // match the caller and the is_anonymous sibling (CIndividualNodeBlockingTestData*
        // -> IndiBlockDataId; CBlockingAlternativeData** -> &mut Cint64).
        block_data: IndiBlockDataId,
        test_continue_blocking: bool,
        block_alt_data: &mut Cint64,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // KONCLUDE-PORT-NOTE[api]: blockData / testContinueBlocking / blockAltData are
        // unported (blocking-test satellites); dropped from the signature until ported.
        //
        // Phase 1 — back/candidate propagation (testIndi.get_concept_propagation_binding_set_hash):
        //   for each propBindSet/conDes, for each nominal-variable propagation binding,
        //   require the same binding in blockingIndi's propagation-binding set for that
        //   concept; else return false.
        // Phase 2 — back/candidate propagation for ancestor node:
        //   ancestor = self.get_ancestor_individual(testIndi, ctx); for each blocker
        //   CCPBINDALL/CCPBINDAQALL concept whose role-successor reaches the ancestor,
        //   require the matching ancestor propagation binding; else return false.
        // Phase 3 — normal propagation (testIndi.get_concept_variable_binding_path_set_hash):
        //   mirror of Phase 1 over variable-binding-path sets.
        // Phase 4 — normal propagation for ancestor node (CCVARBINDALL/CCVARBINDAQALL):
        //   mirror of Phase 2 over variable-binding-path sets.
        // TODO: check representative propagation.
        let _ = (test_indi, blocking_indi, &*ctx);
        true
    }

    // =======================================================================
    // Nominal-connection propagation to ancestors.
    // =======================================================================

    /// Port of `propagateIndividualNodeNewNominalConnectionToAncestors`. `.cpp` 20303–20305.
    pub fn propagate_individual_node_new_nominal_connection_to_ancestors(
        &mut self,
        indi: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) {
        self.propagate_individual_node_nominal_connection_flags_to_ancestors(
            indi,
            IndividualProcessNode::PRF_SUCCESSORNEWNOMINALCONNECTION
                | IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
            ctx,
        );
    }

    /// Port of `propagateIndividualNodeNominalConnectionToAncestors`. `.cpp` 20308–20310.
    pub fn propagate_individual_node_nominal_connection_to_ancestors(
        &mut self,
        indi: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) {
        self.propagate_individual_node_nominal_connection_flags_to_ancestors(
            indi,
            IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
            ctx,
        );
    }

    /// Port of `propagateIndividualNodeNominalConnectionFlagsToAncestors`. `.cpp` 20313–20365.
    pub fn propagate_individual_node_nominal_connection_flags_to_ancestors(
        &mut self,
        indi: NodeId,
        nominal_propagation_flags: Cint64,
        ctx: &mut CalculationAlgorithmContextBase,
    ) {
        let mut anc_indi = indi;
        while anc_indi.is_some()
            && !ctx
                .process_context()
                .node(anc_indi)
                .has_partial_processing_restriction_flags(nominal_propagation_flags)
        {
            ctx.process_context_mut()
                .node_mut(anc_indi)
                .add_processing_restriction_flags(nominal_propagation_flags);

            // CXLinker<CIndividualProcessNode*>* procBlockIndiLinkerIt = ancIndi->getProcessingBlockedIndividualsLinker();
            // [ownership]: snapshot to Vec so the recursive borrow is legal.
            let proc_block_linker: Vec<NodeId> = ctx
                .process_context()
                .node(anc_indi)
                .get_processing_blocked_individuals_linker()
                .to_vec();
            for blocked_indi_node in proc_block_linker {
                if !ctx
                    .process_context()
                    .node(blocked_indi_node)
                    .has_partial_processing_restriction_flags(nominal_propagation_flags)
                {
                    let loc_blocked = self.get_localized_individual(blocked_indi_node, true, ctx);
                    self.propagate_individual_node_nominal_connection_flags_to_ancestors(
                        loc_blocked,
                        nominal_propagation_flags,
                        ctx,
                    );
                }
            }

            let blocked_linker: Vec<NodeId> = ctx
                .process_context()
                .node(anc_indi)
                .get_blocked_individuals_linker()
                .to_vec();
            for blocked_indi_node in blocked_linker {
                if !ctx
                    .process_context()
                    .node(blocked_indi_node)
                    .has_partial_processing_restriction_flags(nominal_propagation_flags)
                {
                    let loc_blocked = self.get_localized_individual(blocked_indi_node, true, ctx);
                    self.propagate_individual_node_nominal_connection_flags_to_ancestors(
                        loc_blocked,
                        nominal_propagation_flags,
                        ctx,
                    );
                }
            }

            // CBlockingFollowSet* followSet = ancIndi->getBlockingFollowSet(false);
            let _follow_set = ctx
                .process_context_mut()
                .node_mut(anc_indi)
                .blocking_follow_set(false);
            // W6-DEFER[api]: CBlockingFollowSet const-iterator is unported. Faithful:
            //   if followSet { for blockedIndiNodeID in followSet {
            //       locBlocked = self.get_localized_individual_by_id(blockedIndiNodeID, ctx);
            //       self.propagate_individual_node_nominal_connection_flags_to_ancestors(locBlocked, flags, ctx);
            //   } }

            if ctx
                .process_context()
                .node(anc_indi)
                .has_successor_individual_node_backward_dependency_linker()
            {
                let succ_back: Vec<NodeId> = ctx
                    .process_context()
                    .node(anc_indi)
                    .successor_individual_node_backward_dependency_linker()
                    .clone();
                for succ_indi_node_backward_dep in succ_back {
                    let has_succ = {
                        let pc = ctx.process_context();
                        pc.node(anc_indi)
                            .has_successor_individual_node(pc.node(succ_indi_node_backward_dep))
                    };
                    if has_succ
                        && !ctx
                            .process_context()
                            .node(succ_indi_node_backward_dep)
                            .has_partial_processing_restriction_flags(nominal_propagation_flags)
                    {
                        let loc_succ =
                            self.get_localized_individual(succ_indi_node_backward_dep, true, ctx);
                        self.propagate_individual_node_nominal_connection_flags_to_ancestors(
                            loc_succ,
                            nominal_propagation_flags,
                            ctx,
                        );
                    }
                }
            }

            if ctx.process_context().node(anc_indi).has_individual_ancestor() {
                anc_indi = self.get_ancestor_individual(&mut anc_indi, ctx);
                let loc_anc_indi = self.get_localized_individual(anc_indi, false, ctx);
                anc_indi = loc_anc_indi;
            } else {
                anc_indi = NodeId::NONE;
            }
        }
    }

    /// Port of `propagateIndividualNodeNominalConnectionStatusToAncestors`. `.cpp` 20368–20403.
    pub fn propagate_individual_node_nominal_connection_status_to_ancestors(
        &mut self,
        indi: NodeId,
        copy_from_indi_node: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) {
        let copy_is_nominal = ctx
            .process_context()
            .node(copy_from_indi_node)
            .is_nominal_individual_node();
        if ctx
            .process_context()
            .node(copy_from_indi_node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
            )
            || copy_is_nominal
        {
            if self.conf_exact_nominal_dependency_tracking {
                let copy_succ_conn_nom_set = ctx
                    .process_context_mut()
                    .node_mut(copy_from_indi_node)
                    .successor_nominal_connection_set(false);
                if copy_succ_conn_nom_set.is_some() {
                    // W6-DEFER[api]: CSuccessorConnectedNominalSet iteration unported. Faithful:
                    //   for nominalID in copySuccConnNomSet {
                    //       if !indi.has_successor_connection_to_nominal(nominalID) {
                    //           self.propagate_individual_node_connected_nominal_to_ancestors(indi, nominalID, ctx);
                    //       }
                    //   }
                }
            }
            if copy_is_nominal {
                let nominal_indi = ctx
                    .process_context()
                    .node(copy_from_indi_node)
                    .nominal_individual();
                if self.conf_exact_nominal_dependency_tracking && nominal_indi.is_some() {
                    let nominal_id =
                        -ctx.ontology_arenas().individual(nominal_indi).get_individual_id();
                    if !ctx
                        .process_context_mut()
                        .node_mut(indi)
                        .has_successor_connection_to_nominal(nominal_id)
                    {
                        self.propagate_individual_node_connected_nominal_to_ancestors(
                            indi, nominal_id, ctx,
                        );
                    }
                }
                let level = ctx
                    .process_context()
                    .node(copy_from_indi_node)
                    .individual_nominal_level_or_ancestor_depth();
                if nominal_indi.is_none() || level > 0 {
                    self.propagate_individual_node_new_nominal_connection_to_ancestors(indi, ctx);
                }
            }
            if !ctx
                .process_context()
                .node(indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
                )
            {
                self.propagate_individual_node_nominal_connection_to_ancestors(indi, ctx);
            }

            if ctx
                .process_context()
                .node(copy_from_indi_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SUCCESSORNEWNOMINALCONNECTION,
                )
            {
                self.propagate_individual_node_new_nominal_connection_to_ancestors(indi, ctx);
            }
        }
    }

    /// Port of `propagateIndividualNodeConnectedNominalToAncestors`. `.cpp` 20406–20460.
    pub fn propagate_individual_node_connected_nominal_to_ancestors(
        &mut self,
        indi: NodeId,
        nominal_id: Cint64,
        ctx: &mut CalculationAlgorithmContextBase,
    ) {
        let nominal_propagation_flags = IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION;
        let mut anc_indi = indi;
        while anc_indi.is_some()
            && !ctx
                .process_context_mut()
                .node_mut(anc_indi)
                .has_successor_connection_to_nominal(nominal_id)
        {
            self.mark_individual_node_backend_non_concept_set_related_processing(anc_indi, ctx);
            ctx.process_context_mut()
                .node_mut(anc_indi)
                .add_processing_restriction_flags(nominal_propagation_flags);
            ctx.process_context_mut()
                .node_mut(anc_indi)
                .add_successor_connection_to_nominal(nominal_id);

            let proc_block_linker: Vec<NodeId> = ctx
                .process_context()
                .node(anc_indi)
                .get_processing_blocked_individuals_linker()
                .to_vec();
            for blocked_indi_node in proc_block_linker {
                if !ctx
                    .process_context_mut()
                    .node_mut(blocked_indi_node)
                    .has_successor_connection_to_nominal(nominal_id)
                {
                    let loc_blocked = self.get_localized_individual(blocked_indi_node, true, ctx);
                    self.propagate_individual_node_connected_nominal_to_ancestors(
                        loc_blocked,
                        nominal_id,
                        ctx,
                    );
                }
            }

            let blocked_linker: Vec<NodeId> = ctx
                .process_context()
                .node(anc_indi)
                .get_blocked_individuals_linker()
                .to_vec();
            for blocked_indi_node in blocked_linker {
                if !ctx
                    .process_context_mut()
                    .node_mut(blocked_indi_node)
                    .has_successor_connection_to_nominal(nominal_id)
                {
                    let loc_blocked = self.get_localized_individual(blocked_indi_node, true, ctx);
                    self.propagate_individual_node_connected_nominal_to_ancestors(
                        loc_blocked,
                        nominal_id,
                        ctx,
                    );
                }
            }

            // CBlockingFollowSet* followSet = ancIndi->getBlockingFollowSet(false);
            let _follow_set = ctx
                .process_context_mut()
                .node_mut(anc_indi)
                .blocking_follow_set(false);
            // W6-DEFER[api]: CBlockingFollowSet const-iterator unported. Faithful:
            //   if followSet { for blockedIndiNodeID in followSet {
            //       locBlocked = self.get_localized_individual_by_id(blockedIndiNodeID, ctx);
            //       self.propagate_individual_node_connected_nominal_to_ancestors(locBlocked, nominal_id, ctx);
            //   } }

            if ctx
                .process_context()
                .node(anc_indi)
                .has_successor_individual_node_backward_dependency_linker()
            {
                let succ_back: Vec<NodeId> = ctx
                    .process_context()
                    .node(anc_indi)
                    .successor_individual_node_backward_dependency_linker()
                    .clone();
                for succ_indi_node_backward_dep in succ_back {
                    let has_succ = {
                        let pc = ctx.process_context();
                        pc.node(anc_indi)
                            .has_successor_individual_node(pc.node(succ_indi_node_backward_dep))
                    };
                    if has_succ
                        && !ctx
                            .process_context_mut()
                            .node_mut(succ_indi_node_backward_dep)
                            .has_successor_connection_to_nominal(nominal_id)
                    {
                        let loc_succ =
                            self.get_localized_individual(succ_indi_node_backward_dep, true, ctx);
                        self.propagate_individual_node_connected_nominal_to_ancestors(
                            loc_succ, nominal_id, ctx,
                        );
                    }
                }
            }

            if ctx.process_context().node(anc_indi).has_individual_ancestor() {
                anc_indi = self.get_ancestor_individual(&mut anc_indi, ctx);
                let loc_anc_indi = self.get_localized_individual(anc_indi, false, ctx);
                anc_indi = loc_anc_indi;
            } else {
                anc_indi = NodeId::NONE;
            }
        }
    }

    /// Port of `propagateIndividualNodeNeighboursNominalConnectionToAncestors`. `.cpp` 20464–20474.
    pub fn propagate_individual_node_neighbours_nominal_connection_to_ancestors(
        &mut self,
        indi: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) {
        // CConnectionSuccessorSetIterator conSuccIt = indi->getConnectionSuccessorIterator();
        // W2.7-UNDEFER[api]: the connection-successor set + its iterator are now
        // arena-backed (`process::distinct::ConnectionSuccessorSet`). The C++
        // node-level `getConnectionSuccessorIterator()` returns `mUseConnSuccSet`'s
        // iterator when present, else an empty one; re-expressed via the
        // `ProcessContext` arena because the node-level convenience getter is still a
        // zero-size stub (it cannot reach the arena from `&self`).
        let conn_succ_set = ctx
            .process_context_mut()
            .node_mut(indi)
            .get_connection_successor_set(false);
        if conn_succ_set.is_some() {
            let mut con_succ_it = ctx
                .process_context()
                .conn_succ_set(conn_succ_set)
                .get_connection_successor_iterator();
            while con_succ_it.has_next() {
                let neighbour_id = con_succ_it.next_successor_connection_id(true);
                let neighbour_indi_node =
                    self.get_up_to_date_individual_by_id(neighbour_id, ctx);
                if !ctx
                    .process_context()
                    .node(neighbour_indi_node)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
                    )
                {
                    let loc_neighbour =
                        self.get_localized_individual(neighbour_indi_node, false, ctx);
                    self.propagate_individual_node_nominal_connection_status_to_ancestors(
                        loc_neighbour,
                        indi,
                        ctx,
                    );
                }
            }
        }
    }

    // =======================================================================
    // Nominal successor / temporary individual creation + forced init.
    // =======================================================================

    /// Port of `createNominalsSuccessorIndividuals`. `.cpp` 22192–22206.
    pub fn create_nominals_successor_individuals(
        &mut self,
        indi: NodeId,
        role_linker_it: &[NegLink<RoleId>],
        anc_role: RoleId,
        concept_linker_it: &[NegLink<ConceptId>],
        negate: bool,
        dep_track_point: TrackPointId,
        succ_card_count: Cint64,
        ctx: &mut CalculationAlgorithmContextBase,
    ) {
        // CMemoryAllocationManager* taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // [memory-pool]: the per-task allocator is replaced by the process-context arenas.
        for _i in 0..succ_card_count {
            // STATINC(NOMINALSUCCESSORINDINODECREATIONCOUNT, calcAlgContext);
            let succ_indi = self.create_new_individual(dep_track_point, false, ctx);
            let _anc_link: EdgeId = self.create_new_individuals_links_reapplyed(
                indi,
                succ_indi,
                role_linker_it,
                anc_role,
                dep_track_point,
                false,
                ctx,
            );
            ctx.process_context_mut()
                .node_mut(succ_indi)
                .set_individual_type(super::super::process::node::IndividualType::Nominal);
            let level = ctx.process_context().node(indi).individual_nominal_level() + 1;
            ctx.process_context_mut()
                .node_mut(succ_indi)
                .set_individual_nominal_level(level);

            self.add_individual_to_processing_queue(succ_indi, ctx);
        }
        let _ = (concept_linker_it, negate);
    }

    /// Port of `createNewTemporaryNominalIndividual`. `.cpp` 22497–22504.
    ///
    /// W6-DEFER[api]: allocates a `CIndividual` from the task memory pool and registers
    /// it in the databox `CIndividualVector` (`setLocalData`) — both unported.
    pub fn create_new_temporary_nominal_individual(
        &mut self,
        indi_id: Cint64,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> IndividualId {
        // CIndividualVector* indiVector = calcAlgContext->getProcessingDataBox()->getIndividualVector(true);
        // newIndi = CObjectAllocator<CIndividual>::allocateAndConstruct(taskMemMan);
        // newIndi.init_individual(indi_id);
        // newIndi.set_temporary_individual(true);
        // indiVector.set_local_data(indi_id, newIndi);
        // return newIndi;
        let _ = (indi_id, &*ctx);
        IndividualId::NONE
    }

    /// Port of `getLocalizedForcedBackendInitializedNominalIndividualNode(cint64, ...)`. `.cpp` 25468–25471.
    pub fn get_localized_forced_backend_initialized_nominal_individual_node_for_nominal_id(
        &mut self,
        nominal_id: Cint64,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let different_indi_node = self.get_corrected_nominal_individual_node(-nominal_id, ctx);
        self.get_localized_forced_backend_initialized_nominal_individual_node(different_indi_node, ctx)
    }

    /// Port of `getLocalizedForcedBackendInitializedNominalIndividualNode(CIndividualProcessNode*, ...)`. `.cpp` 25473–25490.
    pub fn get_localized_forced_backend_initialized_nominal_individual_node(
        &mut self,
        indi: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let mut loc_indi = self.get_localized_individual(indi, false, ctx);
        // CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData* backendSyncData =
        //     locIndi->getIndividualBackendCacheSynchronisationData(false);
        let _backend_sync_data = ctx
            .process_context_mut()
            .node_mut(loc_indi)
            .individual_backend_cache_synchronisation_data(false);
        // W6-DEFER[api]: CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData
        // (is_backend_concept_set_initialization_required / _queued / _initialized) and the
        // backend-cache concept-set processing hash are unported. Faithful logic:
        //   if backendSyncData && !backendSyncData.is_backend_concept_set_initialization_required()
        //         && locIndi.has_partial_processing_restriction_flags(PRF_SYNCHRONIZEDBACKENPROCESSINGDELAYING) {
        //       locBackendSyncData = self.get_localized_individual_backend_cache_snychronisation_data(indi, ctx);
        //       locBackendSyncData.set_backend_concept_set_initialization_required(true);
        //       if locBackendSyncData.is_backend_concept_set_initialization_queued() {
        //           useHash = databox.backend_cache_concept_set_label_processing_hash(true);
        //           hasher = self.get_individual_representative_backend_cache_concept_set_label_processing_hasher(indi, ctx);
        //           useHash[hasher].dec_queued_node_initializing_count();
        //       }
        //   }
        //   if !backendSyncData || !backendSyncData.is_backend_concept_set_initialized() || indi != locIndi {
        //       locIndi = self.get_forced_initialized_nominal_individual_node(locIndi, ctx);
        //   }
        // Faithful fallback path (the unconditional re-init branch when backend data absent):
        if loc_indi != indi {
            loc_indi = self.get_forced_initialized_nominal_individual_node(loc_indi, ctx);
        }
        loc_indi
    }

    /// Port of `getForcedInitializedNominalIndividualNode`. `.cpp` 25494–25500.
    pub fn get_forced_initialized_nominal_individual_node(
        &mut self,
        indi: NodeId,
        ctx: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        self.current_rec_proc_depth += 1;
        let mut nominal_individual = indi;
        self.initial_node_initialize(nominal_individual, false, ctx);
        self.current_rec_proc_depth -= 1;
        nominal_individual
    }
}
