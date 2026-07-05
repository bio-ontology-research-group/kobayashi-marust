//! `completion::u18` — port unit #18 of the completion task-handle algorithm
//! (family: Blocking (pairwise / label-optimized / dynamic); 25 methods,
//! cpp ranges 4049–9408).
//!
//! Source (READ-ONLY): Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! Ported methods (in cpp order):
//!   - `testCompletionGraphCachingAndBlocking`                      [4049]
//!   - `isIndividualNodeValidBlocker`                               [4193]
//!   - `isIndividualNodeBackendCacheSynchronizationProcessingBlocked` [4216]
//!   - `isSaturationCachedProcessingBlocked`                        [4739]
//!   - `isSatisfiableCachedProcessingBlocked`                       [4822]
//!   - `upgradeSignatureBlockingToIndividualReusing`               [5181]
//!   - `addReusingBlockerFollowing`                                 [5303]
//!   - `removeReusingBlockerFollowing`                              [5317]
//!   - `isSignatureBlockedProcessingBlocked`                        [5331]
//!   - `testAlternativeBlocked`                                     [5344]
//!   - `detectIndividualNodeSignatureBlockingStatus`               [5385]
//!   - `addSignatureBlockingBlockerFollowing`                       [5472]
//!   - `removeSignatureBlockingBlockerFollowing`                    [5486]
//!   - `rebuildSignatureBlockingCandidateHash`                      [5502]
//!   - `searchSignatureIndividualNodeBlocker`                       [5537]
//!   - `addSignatureIndividualNodeBlockerCandidate`                 [5589]
//!   - `establishIndividualNodeSignatureBlocking`                   [5612]
//!   - `refreshIndividualNodeSignatureBlocking`                     [5685]
//!   - `updateBlockingReviewMarking`                                [5776]
//!   - `updateSignatureBlockingConceptExpansion`                    [5846]
//!   - `isConceptSignatureBlockingCritical`                         [6098]
//!   - `propagateIndirectSuccessorSignatureBlocked`                 [6317]
//!   - `propagateIndirectSuccessorReuseBlocked`                     [6326]
//!   - `reactivateIndirectSignatureBlockedSuccessors`              [6505]
//!   - `eliminiateBlockedIndividuals`                               [9384]
//!
//! KONCLUDE-PORT-NOTE[ownership]: pointers become arena ids
//! (`CIndividualProcessNode*` → `NodeId`, `CConceptDescriptor*` → `ConDescId`,
//! `CDependencyTrackPoint*` → `TrackPointId`, `CIndividualLinkEdge*` → `EdgeId`);
//! the `calcAlgContext` pointer becomes a threaded
//! `&mut CalculationAlgorithmContextBase`. Per the W3.5 accessor convention a
//! C++ `indi->getX()` resolves to `calc_alg_context.process_context().node(id).get_x()`
//! (read) / `…process_context_mut().node_mut(id).set_x(v)` (mutate); the static
//! `concept->...` resolves through `calc_alg_context.ontology_arenas().concept(id)`;
//! the databox is reached via `calc_alg_context.processing_data_box_mut()`.
//!
//! KONCLUDE-PORT-NOTE[api]: the blocking family is built around per-node SATELLITE
//! extension structs. Several are now real ports (`CSignatureBlockingCandidateHash`,
//! `CSignatureBlockingIndividualNodeConceptExpansionData`,
//! `CReusingIndividualNodeConceptExpansionData`, `CSignatureBlockingReviewSet`,
//! and `CReapplyConceptLabelSet`-via-node), while others such as
//! `CBlockingFollowSet`, `CIndividualNodeAnalizedConceptExpansionData`, and
//! `CBlockingAlternativeData` still have control-flow-preserving `W6-DEFER[api]`
//! placeholders. The branch/loop structure, the node flag ops, the databox
//! getters, and the cross-unit `self.x(...)` sibling calls are reproduced
//! verbatim; only the not-yet-ported satellite-method dereferences remain stubbed.
//!
//! Cross-unit sibling calls land in later units and are invoked as `self.x(...)`
//! per the port convention (`get_localized_individual`, `get_up_to_date_individual`,
//! `get_successor_individual`, `get_ancestor_individual`, `detect_*`,
//! `anlyze_indiviudal_nodes_concept_expansion`, `has_compatible_concept_set_signature`,
//! `establish_individual_reusing`, `reapply_satisfiable_cached_absorbed_generating_concepts`,
//! `add_individual_to_blocking_update_review_processing_queue`,
//! `propagate_individual_node_nominal_connection_status_to_ancestors`,
//! `propagate_adding_blocked_processing_restriction_to_successors`,
//! `reactivate_blocked_individuals`, `add_individual_to_processing_queue`,
//! `add_concept_to_individual_skip_and_processing`, `create_connection_dependency`,
//! `create_expanded_dependency`); the in-unit siblings resolve here.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::op::{CCATLEAST, CCATMOST};
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::process::blocking_hash::SignatureBlockingIndividualNodeConceptExpansionData;
use super::super::process::node::IndividualProcessNode;
use super::super::process::reapply_sat::{BlockingAltDataId, SignatureBlockingCandidateHash};
use super::super::process::stubs::{AnalizedConExpDataId, SigBlockConExpDataId};
use super::super::process::dependency::DependencyLink;
use super::super::process::{
    ConDescId, DepLinkId, DependencyId, EdgeId, LabelSetId, NodeId, TrackPointId,
};

use super::context::CalculationAlgorithmContextBase;

type BlockingAlternativeDataHandle = BlockingAltDataId;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    fn get_or_create_signature_blocking_candidate_hash(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> super::super::process::reapply_sat::SigBlockCandHashId {
        calc_alg_context.signature_blocking_candidate_hash(true)
    }

    /// Localized equivalent of
    /// `blockingIndividualNode->getSignatureBlockingIndividualNodeConceptExpansionData(true)`.
    pub(crate) fn get_or_create_signature_blocking_concept_expansion_data(
        &mut self,
        blocking_individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SigBlockConExpDataId {
        let current = calc_alg_context
            .process_context()
            .node(blocking_individual_node)
            .signature_blocking_individual_node_concept_expansion_data(true);
        if current.is_some() {
            return current;
        }

        let prev = calc_alg_context
            .process_context()
            .node(blocking_individual_node)
            .signature_blocking_individual_node_concept_expansion_data(false);
        let new_data = calc_alg_context
            .process_context_mut()
            .alloc_sig_block_con_exp_data(
                SignatureBlockingIndividualNodeConceptExpansionData::new(),
            );
        if prev.is_some() {
            let taken = std::mem::replace(
                calc_alg_context
                    .process_context_mut()
                    .sig_block_con_exp_data_mut(prev),
                SignatureBlockingIndividualNodeConceptExpansionData::new(),
            );
            calc_alg_context
                .process_context_mut()
                .sig_block_con_exp_data_mut(new_data)
                .init_blocking_expansion_data(Some(&taken));
            *calc_alg_context
                .process_context_mut()
                .sig_block_con_exp_data_mut(prev) = taken;
        } else {
            calc_alg_context
                .process_context_mut()
                .sig_block_con_exp_data_mut(new_data)
                .init_blocking_expansion_data(None);
        }
        calc_alg_context
            .process_context_mut()
            .node_mut(blocking_individual_node)
            .set_signature_blocking_individual_node_concept_expansion_data(new_data);
        new_data
    }

    fn node_reapply_concept_label_set(
        &self,
        node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> LabelSetId {
        calc_alg_context
            .process_context()
            .node(node)
            .use_reapply_con_label_set
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testCompletionGraphCachingAndBlocking`.
    ///
    /// KONCLUDE-PORT-NOTE[unclear]: this is a debug-only verifier (every branch
    /// ends in `bool bug = true;` after writing `caching-error.txt`). The loop and
    /// the ancestor `PRFANCESTORSATISFIABLECACHED` consistency check are reproduced;
    /// the concept-processing-queue probe and the `QFile` writes are deferred.
    pub fn test_completion_graph_caching_and_blocking(
        &mut self,
        except_individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // processingDataBox = calcAlgContext->getProcessingDataBox();
        // indiNodeVec = processingDataBox->getIndividualProcessNodeVector();
        let _indi_node_vec = calc_alg_context
            .processing_data_box_mut()
            .individual_process_node_vector();
        // W6-DEFER[api]: indiCount = indiNodeVec->getItemCount(); indiStart = indiNodeVec->getItemMinIndex();
        let indi_count: Cint64 = 0;
        let indi_start: Cint64 = 0;
        let mut indi_idx = indi_start;
        while indi_idx < indi_count {
            // indiNode = getLocalizedIndividual(indiIdx,calcAlgContext);
            let mut indi_node = self.get_localized_individual_by_id(indi_idx, calc_alg_context);
            if indi_node != Id::NONE && indi_node != except_individual_node {
                // conProQue = indiNode->getConceptProcessingQueue(false);
                // W6-DEFER[api]: node has no concept_processing_queue accessor yet; the
                //   inner !conProQue->isEmpty() consistency probe (queue-state flags +
                //   QFile write of generateExtendedDebugIndiModelStringList) is deferred.
                if calc_alg_context
                    .process_context()
                    .node(indi_node)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED,
                    )
                {
                    // ancNode = getAncestorIndividual(indiNode,calcAlgContext);
                    let anc_node = self.get_ancestor_individual(&mut indi_node, calc_alg_context);
                    if !calc_alg_context
                        .process_context()
                        .node(anc_node)
                        .has_partial_processing_restriction_flags(
                            IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED
                                | IndividualProcessNode::PRF_SATISFIABLECACHED,
                        )
                    {
                        // W6-DEFER[api]: mEndTaskDebugIndiModelString = generateExtendedDebugIndiModelStringList(...); bool bug = true;
                    }
                }
            }
            indi_idx += 1;
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isIndividualNodeValidBlocker`.
    pub fn is_individual_node_valid_blocker(
        &self,
        individual_node: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        if calc_alg_context
            .process_context()
            .node(individual_node)
            .is_nominal_individual_node()
        {
            return false;
        }
        if calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION,
            )
        {
            return false;
        }

        // W6-DEFER[api]: calcAlgContext->hasCompletionGraphCachedIndividualNodes() — ctx
        //   predicate not yet ported; defaults to `false` (no cached nodes).
        let has_completion_graph_cached_individual_nodes = false;
        if has_completion_graph_cached_individual_nodes
            && !calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
                )
            && calc_alg_context
                .process_context()
                .node(individual_node)
                .individual_node_id()
                <= calc_alg_context
                    .base
                    .max_completion_graph_cached_individual_node_id()
        {
            return false;
        }
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isIndividualNodeBackendCacheSynchronizationProcessingBlocked`.
    pub fn is_individual_node_backend_cache_synchronization_processing_blocked(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let was_neigbour_expansion_blocked = calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
            );
        self.detect_individual_node_backend_cache_synchronized(individual_node, calc_alg_context);
        if was_neigbour_expansion_blocked {
            if !calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
                )
            {
                let has_reverse_assertion = !calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .reverse_assertion_role_linker()
                    .is_none();
                let has_assertion = !calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .assertion_role_linker()
                    .is_none();
                let has_additional = !calc_alg_context
                    .process_context()
                    .node(individual_node)
                    .additional_role_assertions_linker()
                    .is_none();
                if has_reverse_assertion || has_assertion || has_additional {
                    let _role_ass_queue =
                        calc_alg_context.get_role_assertion_expansion_processing_queue(true);
                    // W6-DEFER[api]: roleAssertionExpansionProcessingQueue->insertIndiviudalProcessNode(individualNode);
                }
            }
        }
        calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED,
            )
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isSaturationCachedProcessingBlocked`.
    pub fn is_saturation_cached_processing_blocked(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut processing_blocked = false;
        let saturation_cached =
            self.detect_individual_node_saturation_cached(individual_node, calc_alg_context);
        if saturation_cached {
            // block processing only for successors of saturation cached nodes
            processing_blocked = calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED,
                );
        }
        processing_blocked
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isSatisfiableCachedProcessingBlocked`.
    pub fn is_satisfiable_cached_processing_blocked(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut processing_blocked = false;
        let satisfiable_cached = self
            .detect_individual_node_satisfiable_expanded_cached(individual_node, calc_alg_context);
        if satisfiable_cached {
            // block processing only for successors of satisfiable cached nodes
            processing_blocked = calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED,
                );
        }
        processing_blocked
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::upgradeSignatureBlockingToIndividualReusing`.
    pub fn upgrade_signature_blocking_to_individual_reusing(
        &mut self,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // sigBlockData = processIndi->getSignatureBlockingIndividualNodeConceptExpansionData(false);
        let sig_block_data = calc_alg_context
            .process_context()
            .node(process_indi)
            .signature_blocking_individual_node_concept_expansion_data(false);
        let reuse_indi = if sig_block_data.is_some() {
            calc_alg_context
                .process_context()
                .sig_block_con_exp_data(sig_block_data)
                .get_blocker_individual_node()
        } else {
            Id::NONE
        };

        calc_alg_context
            .process_context_mut()
            .node_mut(process_indi)
            .clear_processing_restriction_flags(IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED);
        self.reactivate_indirect_signature_blocked_successors(
            process_indi,
            false,
            calc_alg_context,
        );
        self.reapply_satisfiable_cached_absorbed_generating_concepts(
            process_indi,
            calc_alg_context,
        );

        self.establish_individual_reusing(process_indi, reuse_indi, calc_alg_context);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addReusingBlockerFollowing`.
    pub fn add_reusing_blocker_following(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let reusing_data = calc_alg_context
            .process_context()
            .node(individual_node)
            .reusing_individual_node_concept_expansion_data(false);
        if !reusing_data.is_none() {
            let blocker_individual_node = calc_alg_context
                .process_context()
                .reusing_con_exp_data(reusing_data)
                .get_blocker_individual_node();
            let loc_blocker_individual_node =
                self.get_localized_individual(blocker_individual_node, true, calc_alg_context);
            let indi_id = calc_alg_context
                .process_context()
                .node(individual_node)
                .individual_node_id();
            calc_alg_context
                .process_context_mut()
                .node_add_blocking_follower(loc_blocker_individual_node, indi_id);
            calc_alg_context
                .process_context_mut()
                .node_mut(individual_node)
                .set_following_individual_node(loc_blocker_individual_node);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::removeReusingBlockerFollowing`.
    pub fn remove_reusing_blocker_following(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        calc_alg_context
            .process_context_mut()
            .node_mut(individual_node)
            .set_following_individual_node(Id::NONE);
        let reusing_data = calc_alg_context
            .process_context()
            .node(individual_node)
            .reusing_individual_node_concept_expansion_data(false);
        if !reusing_data.is_none() {
            let blocker_individual_node = calc_alg_context
                .process_context()
                .reusing_con_exp_data(reusing_data)
                .get_blocker_individual_node();
            let loc_blocker_individual_node =
                self.get_localized_individual(blocker_individual_node, true, calc_alg_context);
            let indi_id = calc_alg_context
                .process_context()
                .node(individual_node)
                .individual_node_id();
            calc_alg_context
                .process_context_mut()
                .node_remove_blocking_follower(loc_blocker_individual_node, indi_id);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isSignatureBlockedProcessingBlocked`.
    pub fn is_signature_blocked_processing_blocked(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut processing_blocked = false;
        let sig_blocked = self
            .detect_individual_node_signature_blocking_status(individual_node, calc_alg_context);
        if sig_blocked {
            // block processing only for successors of satisfiable cached nodes
            processing_blocked = calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
                );
        }
        processing_blocked
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::testAlternativeBlocked`.
    pub fn test_alternative_blocked(
        &mut self,
        individual_node: NodeId,
        block_alt_data: BlockingAlternativeDataHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut blocked = false;

        let is_signature_blocking_candidate = block_alt_data.is_some();
        if is_signature_blocking_candidate {
            if self.conf_signature_mirroring_blocking {
                let blocker_node = calc_alg_context
                    .process_context()
                    .blocking_alt_data(block_alt_data)
                    .get_signature_blocking_candidate_node();

                // W6-DEFER[api]: STATINC(SIGNATUREMIRRORINGBLOCKINGESTABLISHCOUNT,...)
                let prev_blocker_con_set =
                    self.node_reapply_concept_label_set(blocker_node, calc_alg_context);
                let prev_blocker_con_set_count = if prev_blocker_con_set.is_some() {
                    calc_alg_context
                        .process_context()
                        .label_set(prev_blocker_con_set)
                        .get_concept_count()
                } else {
                    0
                };
                if self.establish_individual_node_signature_blocking(
                    individual_node,
                    blocker_node,
                    calc_alg_context,
                ) {
                    if calc_alg_context
                        .process_context()
                        .node(blocker_node)
                        .has_partial_processing_restriction_flags(
                            IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
                        )
                    {
                        self.propagate_individual_node_nominal_connection_status_to_ancestors(
                            individual_node,
                            blocker_node,
                            calc_alg_context,
                        );
                    }

                    let new_blocker_con_set =
                        self.node_reapply_concept_label_set(blocker_node, calc_alg_context);
                    let new_blocker_con_set_count = if new_blocker_con_set.is_some() {
                        calc_alg_context
                            .process_context()
                            .label_set(new_blocker_con_set)
                            .get_concept_count()
                    } else {
                        0
                    };
                    if prev_blocker_con_set_count != new_blocker_con_set_count {
                        self.add_individual_to_blocking_update_review_processing_queue(
                            individual_node,
                            calc_alg_context,
                        );
                    }
                    self.add_signature_blocking_blocker_following(
                        individual_node,
                        calc_alg_context,
                    );
                    // W6-DEFER[api]: STATINC(SIGNATUREMIRRORINGBLOCKINGADDFOLLOWINGCOUNT,...);
                    //   calcAlgContext->getProcessTagger()->incCurrentBlockingFollowTag();

                    calc_alg_context
                        .process_context_mut()
                        .node_mut(individual_node)
                        .add_processing_restriction_flags(
                            IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED,
                        );
                    self.propagate_indirect_successor_signature_blocked(
                        individual_node,
                        calc_alg_context,
                    );

                    self.update_blocking_review_marking(individual_node, true, calc_alg_context);
                    blocked = true;
                }
            }
        }

        blocked
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::detectIndividualNodeSignatureBlockingStatus`.
    pub fn detect_individual_node_signature_blocking_status(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // TODO (Konclude): 1. search nodes with identical signatures, 2. check signature
        // compatibility, 3. expand concepts and establish blocking status, 4. block
        // successor generation, 5. hold blocking status as long subset, 6. validate or
        // remove blocking status at the end of completion graph construction.

        let was_blocking_cached = calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED
                    | IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
            );

        if calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
            )
        {
            if calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHEDABOLISHED,
                )
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .clear_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHEDABOLISHED,
                    );
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .clear_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
                    );
            } else {
                return true;
            }
        }
        if calc_alg_context
            .process_context()
            .node(individual_node)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_RETESTSIGNATUREBLOCKINGCACHEDDUEDIRECTMODIFIED,
            )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(individual_node)
                .clear_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTSIGNATUREBLOCKINGCACHEDDUEDIRECTMODIFIED,
                );
        }

        let mut new_blocking_cached = was_blocking_cached;

        if self.conf_signature_mirroring_blocking {
            let mut continue_blocker_search = true;
            if calc_alg_context
                .process_context()
                .node(individual_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING
                        | IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHED,
                )
            {
                continue_blocker_search = false;
            }
            if was_blocking_cached {
                // W6-DEFER[api]: STATINC(SIGNATUREMIRRORINGBLOCKINGREFRESHCOUNT,...)
                if continue_blocker_search {
                    new_blocking_cached = self.refresh_individual_node_signature_blocking(
                        individual_node,
                        calc_alg_context,
                    );
                }
                if !new_blocking_cached {
                    // remove connection from blocker node
                    // W6-DEFER[api]: STATINC(SIGNATUREMIRRORINGBLOCKINGREFRESHLOSEDCOUNT/REMOVEFOLLOWINGCOUNT,...)
                    self.remove_signature_blocking_blocker_following(
                        individual_node,
                        calc_alg_context,
                    );
                } else {
                    // W6-DEFER[api]: calcAlgContext->getProcessTagger()->incCurrentBlockingFollowTag();
                }
            }

            while continue_blocker_search && !new_blocking_cached {
                // W6-DEFER[api]: STATINC(SIGNATUREMIRRORINGBLOCKINGSEARCHCOUNT,...)
                let blocker_node = self
                    .search_signature_individual_node_blocker(individual_node, calc_alg_context);
                if blocker_node != Id::NONE {
                    // W6-DEFER[api]: STATINC(SIGNATUREMIRRORINGBLOCKINGESTABLISHCOUNT,...)
                    let prev_blocker_con_set =
                        self.node_reapply_concept_label_set(blocker_node, calc_alg_context);
                    let prev_blocker_con_set_count = if prev_blocker_con_set.is_some() {
                        calc_alg_context
                            .process_context()
                            .label_set(prev_blocker_con_set)
                            .get_concept_count()
                    } else {
                        0
                    };
                    if self.establish_individual_node_signature_blocking(
                        individual_node,
                        blocker_node,
                        calc_alg_context,
                    ) {
                        if calc_alg_context
                            .process_context()
                            .node(blocker_node)
                            .has_partial_processing_restriction_flags(
                                IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
                            )
                        {
                            self.propagate_individual_node_nominal_connection_status_to_ancestors(
                                individual_node,
                                blocker_node,
                                calc_alg_context,
                            );
                        }

                        new_blocking_cached = true;
                        let new_blocker_con_set =
                            self.node_reapply_concept_label_set(blocker_node, calc_alg_context);
                        let new_blocker_con_set_count = if new_blocker_con_set.is_some() {
                            calc_alg_context
                                .process_context()
                                .label_set(new_blocker_con_set)
                                .get_concept_count()
                        } else {
                            0
                        };
                        if prev_blocker_con_set_count != new_blocker_con_set_count {
                            self.add_individual_to_blocking_update_review_processing_queue(
                                individual_node,
                                calc_alg_context,
                            );
                        }
                        self.add_signature_blocking_blocker_following(
                            individual_node,
                            calc_alg_context,
                        );
                        // W6-DEFER[api]: STATINC(SIGNATUREMIRRORINGBLOCKINGADDFOLLOWINGCOUNT,...);
                        //   calcAlgContext->getProcessTagger()->incCurrentBlockingFollowTag();
                    }
                } else {
                    continue_blocker_search = false;
                }
            }

            self.update_blocking_review_marking(
                individual_node,
                new_blocking_cached,
                calc_alg_context,
            );

            if new_blocking_cached && !was_blocking_cached {
                // activate caching status
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .add_processing_restriction_flags(
                        IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED,
                    );
                self.propagate_indirect_successor_signature_blocked(
                    individual_node,
                    calc_alg_context,
                );
            } else if was_blocking_cached && !new_blocking_cached {
                // deactivate caching status
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual_node)
                    .clear_processing_restriction_flags(
                        IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED,
                    );
                self.reactivate_indirect_signature_blocked_successors(
                    individual_node,
                    false,
                    calc_alg_context,
                );
                self.reapply_satisfiable_cached_absorbed_generating_concepts(
                    individual_node,
                    calc_alg_context,
                );
            }
        }
        new_blocking_cached
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addSignatureBlockingBlockerFollowing`.
    pub fn add_signature_blocking_blocker_following(
        &mut self,
        blocking_individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let sig_blocking_data = calc_alg_context
            .process_context()
            .node(blocking_individual_node)
            .signature_blocking_individual_node_concept_expansion_data(false);
        if !sig_blocking_data.is_none() {
            let blocker_individual_node = calc_alg_context
                .process_context()
                .sig_block_con_exp_data(sig_blocking_data)
                .get_blocker_individual_node();
            let loc_blocker_individual_node =
                self.get_localized_individual(blocker_individual_node, true, calc_alg_context);
            let indi_id = calc_alg_context
                .process_context()
                .node(blocking_individual_node)
                .individual_node_id();
            calc_alg_context
                .process_context_mut()
                .node_add_blocking_follower(loc_blocker_individual_node, indi_id);
            calc_alg_context
                .process_context_mut()
                .node_mut(blocking_individual_node)
                .set_following_individual_node(loc_blocker_individual_node);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::removeSignatureBlockingBlockerFollowing`.
    pub fn remove_signature_blocking_blocker_following(
        &mut self,
        blocking_individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        calc_alg_context
            .process_context_mut()
            .node_mut(blocking_individual_node)
            .set_following_individual_node(Id::NONE);
        let sig_blocking_data = calc_alg_context
            .process_context()
            .node(blocking_individual_node)
            .signature_blocking_individual_node_concept_expansion_data(false);
        if !sig_blocking_data.is_none() {
            let blocker_individual_node = calc_alg_context
                .process_context()
                .sig_block_con_exp_data(sig_blocking_data)
                .get_blocker_individual_node();
            let loc_blocker_individual_node =
                self.get_localized_individual(blocker_individual_node, true, calc_alg_context);
            let indi_id = calc_alg_context
                .process_context()
                .node(blocking_individual_node)
                .individual_node_id();
            calc_alg_context
                .process_context_mut()
                .node_remove_blocking_follower(loc_blocker_individual_node, indi_id);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::rebuildSignatureBlockingCandidateHash`.
    pub fn rebuild_signature_blocking_candidate_hash(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W6-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        //                        processContext = calcAlgContext->getUsedProcessContext();

        let sig_block_cand_hash = calc_alg_context.signature_blocking_candidate_hash(false);

        if !sig_block_cand_hash.is_none() {
            let mut sig_it = calc_alg_context
                .process_context()
                .sig_block_cand_hash(sig_block_cand_hash)
                .get_signature_iterator();
            let mut signatures: Vec<(Cint64, Vec<Cint64>)> = Vec::new();
            while sig_it.has_next() {
                signatures.push((
                    sig_it.get_signature(),
                    sig_it.get_candidate_linker().to_vec(),
                ));
                sig_it.move_next();
            }

            let new_sig_block_cand_hash = calc_alg_context
                .process_context_mut()
                .alloc_sig_block_cand_hash(SignatureBlockingCandidateHash::new(INVALID));
            for (signature, candidate_linker) in signatures {
                let mut new_candidate_linker: Vec<Cint64> = Vec::new();
                for cand_indi_id in candidate_linker {
                    let cand_indi_node =
                        self.get_up_to_date_individual_by_id(cand_indi_id, calc_alg_context);
                    if !cand_indi_node.is_none()
                        && self.is_individual_node_valid_blocker(cand_indi_node, calc_alg_context)
                    {
                        let cand_node_id = calc_alg_context
                            .process_context()
                            .node(cand_indi_node)
                            .individual_node_id();
                        // CLinker front-splice (head-front prepend).
                        new_candidate_linker.insert(0, cand_node_id);
                    }
                }
                if !new_candidate_linker.is_empty() {
                    calc_alg_context
                        .process_context_mut()
                        .sig_block_cand_hash_mut(new_sig_block_cand_hash)
                        .insert_signature_blocking_candidates(signature, new_candidate_linker);
                }
            }
            calc_alg_context
                .processing_data_box_mut()
                .set_signature_blocking_candidate_hash(new_sig_block_cand_hash);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::searchSignatureIndividualNodeBlocker`.
    pub fn search_signature_individual_node_blocker(
        &mut self,
        blocking_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let sig_block_cand_hash = calc_alg_context.signature_blocking_candidate_hash(false);
        // conSet = blockingNode->getReapplyConceptLabelSet(false);
        let con_set = self.node_reapply_concept_label_set(blocking_node, calc_alg_context);
        if !sig_block_cand_hash.is_none() && !con_set.is_none() {
            let con_count = calc_alg_context
                .process_context()
                .label_set(con_set)
                .get_concept_count();
            if !calc_alg_context
                .process_context()
                .node(blocking_node)
                .is_invalid_signature_blocking()
                && calc_alg_context
                    .process_context()
                    .node(blocking_node)
                    .last_concept_count_search_blocking_candidate()
                    != con_count
            {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(blocking_node)
                    .set_last_concept_count_search_blocking_candidate(con_count);

                let con_sig = calc_alg_context
                    .process_context()
                    .label_set(con_set)
                    .get_concept_signature_value();
                let new_cand_count = calc_alg_context
                    .process_context()
                    .sig_block_cand_hash(sig_block_cand_hash)
                    .get_blocking_candidates_count(con_sig);
                let mut last_cand_count = calc_alg_context
                    .process_context()
                    .node(blocking_node)
                    .last_search_blocker_candidate_count();
                let last_cand_signature = calc_alg_context
                    .process_context()
                    .node(blocking_node)
                    .last_search_blocker_candidate_signature();
                if last_cand_signature != con_sig {
                    last_cand_count = 0;
                }
                calc_alg_context
                    .process_context_mut()
                    .node_mut(blocking_node)
                    .set_last_search_blocker_candidate_signature(con_sig);
                if new_cand_count != last_cand_count {
                    let mut cand_diff_count = new_cand_count - last_cand_count;

                    let mut cand_it = calc_alg_context
                        .process_context()
                        .sig_block_cand_hash(sig_block_cand_hash)
                        .get_blocking_candidates_iterator(con_sig);
                    let blocking_node_id = calc_alg_context
                        .process_context()
                        .node(blocking_node)
                        .individual_node_id();
                    while cand_it.has_next()
                        && cand_diff_count > 0
                        && !calc_alg_context
                            .process_context()
                            .node(blocking_node)
                            .is_invalid_signature_blocking()
                    {
                        cand_diff_count -= 1;
                        let cand_indi_id = cand_it.next(true);
                        if cand_indi_id != blocking_node_id {
                            let cand_indi_node = self
                                .get_up_to_date_individual_by_id(cand_indi_id, calc_alg_context);
                            // W6-DEFER[api]: STATINC(SIGNATUREMIRRORINGBLOCKINGCANDIDATEREGARDEDCOUNT,...)
                            if self
                                .is_individual_node_valid_blocker(cand_indi_node, calc_alg_context)
                            {
                                let mut mutable_blocking_node = blocking_node;
                                let compatible = self.has_compatible_concept_set_signature(
                                    &mut mutable_blocking_node,
                                    con_set,
                                    cand_indi_node,
                                    calc_alg_context,
                                );
                                if compatible {
                                    calc_alg_context
                                        .process_context_mut()
                                        .node_mut(blocking_node)
                                        .set_last_search_blocker_candidate_count(
                                            new_cand_count - cand_diff_count,
                                        );
                                    return cand_indi_node;
                                } else {
                                    // W6-DEFER[api]: STATINC(...CANDIDATEREGARDEDINCOMPATIBLECOUNT,...)
                                }
                            } else {
                                // W6-DEFER[api]: STATINC(...CANDIDATEREGARDEDINVALIDCOUNT,...)
                            }
                        }
                    }
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(blocking_node)
                        .set_last_search_blocker_candidate_count(new_cand_count);
                }
            }
        }
        Id::NONE
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addSignatureIndividualNodeBlockerCandidate`.
    pub fn add_signature_individual_node_blocker_candidate(
        &mut self,
        indi_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if calc_alg_context
            .process_context()
            .node(indi_node)
            .blocking_caching_saved_candidate_count()
            <= self.max_blocking_caching_saved_candidate_count
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(indi_node)
                .inc_blocking_caching_saved_candidate_count(1);
            if self.is_individual_node_valid_blocker(indi_node, calc_alg_context) {
                // conSet = indiNode->getReapplyConceptLabelSet(false);
                let con_set = self.node_reapply_concept_label_set(indi_node, calc_alg_context);
                if !con_set.is_none() {
                    let con_count = calc_alg_context
                        .process_context()
                        .label_set(con_set)
                        .get_concept_count();
                    if calc_alg_context
                        .process_context()
                        .node(indi_node)
                        .last_concept_count_cached_blocking_candidate()
                        != con_count
                    {
                        // W6-DEFER[api]: STATINC(SIGNATURESAVINGCOUNT,...)
                        let con_sig = calc_alg_context
                            .process_context()
                            .label_set(con_set)
                            .get_concept_signature_value();
                        let sig_block_cand_hash =
                            self.get_or_create_signature_blocking_candidate_hash(calc_alg_context);
                        let indi_cand_id = calc_alg_context
                            .process_context()
                            .node(indi_node)
                            .individual_node_id();
                        let data = calc_alg_context
                            .process_context_mut()
                            .sig_block_cand_hash_mut(sig_block_cand_hash)
                            .sig_block_candidate_hash
                            .entry(con_sig)
                            .or_default();
                        data.candidate_indi_linker.insert(0, indi_cand_id);
                        data.candidate_count += 1;
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(indi_node)
                            .set_last_concept_count_cached_blocking_candidate(con_count);
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::establishIndividualNodeSignatureBlocking`.
    pub fn establish_individual_node_signature_blocking(
        &mut self,
        blocking_individual_node: NodeId,
        mut blocker_individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut blocking_established = false;
        self.anlyze_indiviudal_nodes_concept_expansion(
            &mut blocker_individual_node,
            calc_alg_context,
        );
        let blocker_analized_con_exp_data = calc_alg_context
            .process_context_mut()
            .node_mut(blocker_individual_node)
            .analized_concept_expansion_data(false);
        if !blocker_analized_con_exp_data.is_none() {
            let blocker_is_invalid = calc_alg_context
                .process_context()
                .analized_con_exp_data(blocker_analized_con_exp_data)
                .is_invalid_blocker();
            if !blocker_is_invalid {
                let blocking_con_set = calc_alg_context
                    .process_context_mut()
                    .node_reapply_concept_label_set(blocking_individual_node);
                let blocking_con_set_count = calc_alg_context
                    .process_context()
                    .label_set(blocking_con_set)
                    .get_concept_count();
                let blocking_con_set_signature = calc_alg_context
                    .process_context()
                    .label_set(blocking_con_set)
                    .get_concept_signature_value();
                let blocking_last_con_des = calc_alg_context
                    .process_context()
                    .label_set(blocking_con_set)
                    .get_adding_sorted_concept_description_linker();
                let loc_sig_blocking_data = self
                    .get_or_create_signature_blocking_concept_expansion_data(
                        blocking_individual_node,
                        calc_alg_context,
                    );
                calc_alg_context
                    .process_context_mut()
                    .sig_block_con_exp_data_mut(loc_sig_blocking_data)
                    .set_blocking_concept_count(blocking_con_set_count)
                    .set_blocking_concept_signature(blocking_con_set_signature)
                    .set_last_subset_tested_concept_descriptor(blocking_last_con_des)
                    .set_continuous_expanded_contained_concept_count(0)
                    .set_blocker_individual_node(blocker_individual_node)
                    .set_last_updated_concept_count(0)
                    .set_last_updated_concept_expansion_count(0);

                self.update_signature_blocking_concept_expansion(
                    blocking_individual_node,
                    loc_sig_blocking_data,
                    blocker_individual_node,
                    blocker_analized_con_exp_data,
                    calc_alg_context,
                );

                // set blocking status
                blocking_established = true;

                // is still subset after added expansions concepts
                let blocker_con_set =
                    self.node_reapply_concept_label_set(blocker_individual_node, calc_alg_context);
                if !blocker_con_set.is_none() {
                    if calc_alg_context
                        .process_context()
                        .sig_block_con_exp_data(loc_sig_blocking_data)
                        .is_identic_concept_set_required()
                    {
                        if calc_alg_context
                            .process_context()
                            .label_set(blocking_con_set)
                            .get_concept_signature_value()
                            != calc_alg_context
                                .process_context()
                                .label_set(blocker_con_set)
                                .get_concept_signature_value()
                        {
                            return false;
                        }
                        if calc_alg_context
                            .process_context()
                            .label_set(blocking_con_set)
                            .get_concept_count()
                            != calc_alg_context
                                .process_context()
                                .label_set(blocker_con_set)
                                .get_concept_count()
                        {
                            return false;
                        }
                    }
                    let last_subset_test_con_des = calc_alg_context
                        .process_context()
                        .sig_block_con_exp_data(loc_sig_blocking_data)
                        .get_last_subset_tested_concept_descriptor();
                    let adding_sorted_con_des = calc_alg_context
                        .process_context()
                        .label_set(blocking_con_set)
                        .get_adding_sorted_concept_description_linker();
                    if adding_sorted_con_des != last_subset_test_con_des {
                        let mut still_subset = true;
                        let mut adding_sorted_con_des_it = adding_sorted_con_des;
                        while blocking_established
                            && adding_sorted_con_des_it != last_subset_test_con_des
                            && still_subset
                            && !adding_sorted_con_des_it.is_none()
                        {
                            let concept = calc_alg_context
                                .process_context()
                                .con_desc(adding_sorted_con_des_it)
                                .get_concept();
                            if !calc_alg_context
                                .process_context()
                                .label_set(blocker_con_set)
                                .contains_concept_get_negated(concept, None)
                            {
                                still_subset = false;
                            }
                            adding_sorted_con_des_it = calc_alg_context
                                .process_context()
                                .con_desc(adding_sorted_con_des_it)
                                .get_next_concept_descriptor();
                        }
                        if !still_subset && self.opt_signature_mirroring_blocking_force_subset {
                            blocking_established = false;
                        }
                        let loc_data = calc_alg_context
                            .process_context_mut()
                            .sig_block_con_exp_data_mut(loc_sig_blocking_data);
                        loc_data.set_concept_set_still_subset(still_subset);
                        if still_subset {
                            loc_data
                                .set_last_subset_tested_concept_descriptor(adding_sorted_con_des);
                        }
                    }
                }
            } else {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(blocking_individual_node)
                    .set_invalid_signature_blocking(true);
                blocking_established = false;
            }
        }
        blocking_established
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::refreshIndividualNodeSignatureBlocking`.
    pub fn refresh_individual_node_signature_blocking(
        &mut self,
        blocking_individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let sig_blocking_data = calc_alg_context
            .process_context()
            .node(blocking_individual_node)
            .signature_blocking_individual_node_concept_expansion_data(false);
        if !sig_blocking_data.is_none() {
            let blocker_individual_node = calc_alg_context
                .process_context()
                .sig_block_con_exp_data(sig_blocking_data)
                .get_blocker_individual_node();
            let mut blocker_individual_node =
                self.get_up_to_date_individual(blocker_individual_node, calc_alg_context);
            if !self.is_individual_node_valid_blocker(blocker_individual_node, calc_alg_context) {
                return false;
            }
            if calc_alg_context
                .process_context()
                .node(blocking_individual_node)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_INVALIDBLOCKINGORCACHING,
                )
            {
                return false;
            }
            self.anlyze_indiviudal_nodes_concept_expansion(
                &mut blocker_individual_node,
                calc_alg_context,
            );
            let blocking_con_set =
                self.node_reapply_concept_label_set(blocking_individual_node, calc_alg_context);
            let blocker_con_set =
                self.node_reapply_concept_label_set(blocker_individual_node, calc_alg_context);
            if blocking_con_set.is_none() || blocker_con_set.is_none() {
                return false;
            }
            let last_subset_test_con_des = calc_alg_context
                .process_context()
                .sig_block_con_exp_data(sig_blocking_data)
                .get_last_subset_tested_concept_descriptor();
            let adding_sorted_con_des = calc_alg_context
                .process_context()
                .label_set(blocking_con_set)
                .get_adding_sorted_concept_description_linker();
            let blocker_analized_con_exp_data = calc_alg_context
                .process_context_mut()
                .node_mut(blocker_individual_node)
                .analized_concept_expansion_data(false);
            if blocker_analized_con_exp_data.is_none() {
                return false;
            }
            let blocker_is_invalid = calc_alg_context
                .process_context()
                .analized_con_exp_data(blocker_analized_con_exp_data)
                .is_invalid_blocker();
            if !blocker_is_invalid {
                let expansion_count_changed = calc_alg_context
                    .process_context()
                    .analized_con_exp_data(blocker_analized_con_exp_data)
                    .get_expansion_concept_count()
                    > calc_alg_context
                        .process_context()
                        .sig_block_con_exp_data(sig_blocking_data)
                        .get_last_updated_concept_expansion_count();
                let identic_count_changed = calc_alg_context
                    .process_context()
                    .sig_block_con_exp_data(sig_blocking_data)
                    .is_identic_concept_set_required()
                    && calc_alg_context
                        .process_context()
                        .label_set(blocking_con_set)
                        .get_concept_count()
                        != calc_alg_context
                            .process_context()
                            .label_set(blocker_con_set)
                            .get_concept_count();
                if adding_sorted_con_des != last_subset_test_con_des
                    || expansion_count_changed
                    || identic_count_changed
                {
                    let mut still_subset = true;
                    let mut adding_sorted_con_des_it = adding_sorted_con_des;
                    while adding_sorted_con_des_it != last_subset_test_con_des
                        && still_subset
                        && !adding_sorted_con_des_it.is_none()
                    {
                        let concept = calc_alg_context
                            .process_context()
                            .con_desc(adding_sorted_con_des_it)
                            .get_concept();
                        let con_negation = calc_alg_context
                            .process_context()
                            .con_desc(adding_sorted_con_des_it)
                            .is_negated();
                        if !calc_alg_context
                            .process_context()
                            .label_set(blocker_con_set)
                            .contains_concept(concept, con_negation)
                        {
                            still_subset = false;
                        }
                        adding_sorted_con_des_it = calc_alg_context
                            .process_context()
                            .con_desc(adding_sorted_con_des_it)
                            .get_next_concept_descriptor();
                    }
                    if !still_subset && self.opt_signature_mirroring_blocking_force_subset {
                        return false;
                    }
                    let loc_sig_blocking_data = self
                        .get_or_create_signature_blocking_concept_expansion_data(
                            blocking_individual_node,
                            calc_alg_context,
                        );
                    calc_alg_context
                        .process_context_mut()
                        .sig_block_con_exp_data_mut(loc_sig_blocking_data)
                        .set_last_subset_tested_concept_descriptor(adding_sorted_con_des);

                    self.update_signature_blocking_concept_expansion(
                        blocking_individual_node,
                        loc_sig_blocking_data,
                        blocker_individual_node,
                        blocker_analized_con_exp_data,
                        calc_alg_context,
                    );

                    if self.conf_direct_rule_preprocessing
                        || calc_alg_context
                            .process_context()
                            .sig_block_con_exp_data(loc_sig_blocking_data)
                            .is_identic_concept_set_required()
                    {
                        let blocking_con_set = self.node_reapply_concept_label_set(
                            blocking_individual_node,
                            calc_alg_context,
                        );
                        if calc_alg_context
                            .process_context()
                            .sig_block_con_exp_data(loc_sig_blocking_data)
                            .is_identic_concept_set_required()
                        {
                            if calc_alg_context
                                .process_context()
                                .label_set(blocking_con_set)
                                .get_concept_signature_value()
                                != calc_alg_context
                                    .process_context()
                                    .label_set(blocker_con_set)
                                    .get_concept_signature_value()
                            {
                                return false;
                            }
                            if calc_alg_context
                                .process_context()
                                .label_set(blocking_con_set)
                                .get_concept_count()
                                != calc_alg_context
                                    .process_context()
                                    .label_set(blocker_con_set)
                                    .get_concept_count()
                            {
                                return false;
                            }
                        }
                        let adding_sorted_con_des = calc_alg_context
                            .process_context()
                            .label_set(blocking_con_set)
                            .get_adding_sorted_concept_description_linker();
                        let last_subset_test_con_des = calc_alg_context
                            .process_context()
                            .sig_block_con_exp_data(loc_sig_blocking_data)
                            .get_last_subset_tested_concept_descriptor();
                        if adding_sorted_con_des != last_subset_test_con_des {
                            let mut adding_sorted_con_des_it = adding_sorted_con_des;
                            while adding_sorted_con_des_it != last_subset_test_con_des
                                && still_subset
                                && !adding_sorted_con_des_it.is_none()
                            {
                                let concept = calc_alg_context
                                    .process_context()
                                    .con_desc(adding_sorted_con_des_it)
                                    .get_concept();
                                let con_negation = calc_alg_context
                                    .process_context()
                                    .con_desc(adding_sorted_con_des_it)
                                    .is_negated();
                                if !calc_alg_context
                                    .process_context()
                                    .label_set(blocker_con_set)
                                    .contains_concept(concept, con_negation)
                                {
                                    still_subset = false;
                                }
                                adding_sorted_con_des_it = calc_alg_context
                                    .process_context()
                                    .con_desc(adding_sorted_con_des_it)
                                    .get_next_concept_descriptor();
                            }
                            let loc_data = calc_alg_context
                                .process_context_mut()
                                .sig_block_con_exp_data_mut(loc_sig_blocking_data);
                            loc_data.set_concept_set_still_subset(still_subset);
                            if still_subset {
                                loc_data.set_last_subset_tested_concept_descriptor(
                                    adding_sorted_con_des,
                                );
                            } else if self.opt_signature_mirroring_blocking_force_subset {
                                return false;
                            }
                        }
                    }
                }
                return true;
            } else {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(blocking_individual_node)
                    .set_invalid_signature_blocking(true);
                return false;
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::updateBlockingReviewMarking`.
    pub fn update_blocking_review_marking(
        &mut self,
        blocking_individual_node: NodeId,
        is_blocked: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let sig_blocking_data = calc_alg_context
            .process_context()
            .node(blocking_individual_node)
            .signature_blocking_individual_node_concept_expansion_data(false);
        let indi_id = calc_alg_context
            .process_context()
            .node(blocking_individual_node)
            .individual_node_id();
        if !sig_blocking_data.is_none() {
            let blocker_node = calc_alg_context
                .process_context()
                .sig_block_con_exp_data(sig_blocking_data)
                .get_blocker_individual_node();
            let blocker_node = self.get_up_to_date_individual(blocker_node, calc_alg_context);
            let blocker_con_set =
                self.node_reapply_concept_label_set(blocker_node, calc_alg_context);
            let blocking_con_set =
                self.node_reapply_concept_label_set(blocking_individual_node, calc_alg_context);
            if blocker_con_set.is_none() || blocking_con_set.is_none() {
                return false;
            }
            let blocker_count = calc_alg_context
                .process_context()
                .label_set(blocker_con_set)
                .get_concept_count();
            let blocking_count = calc_alg_context
                .process_context()
                .label_set(blocking_con_set)
                .get_concept_count();
            let still_subset = calc_alg_context
                .process_context()
                .sig_block_con_exp_data(sig_blocking_data)
                .is_concept_set_still_subset();
            let review_marked = calc_alg_context
                .process_context()
                .sig_block_con_exp_data(sig_blocking_data)
                .is_blocking_review_marked();
            let individual_ancestor_depth = calc_alg_context
                .process_context()
                .node(blocking_individual_node)
                .individual_ancestor_depth();
            if is_blocked && !review_marked {
                if blocker_count != blocking_count || !still_subset {
                    let rev_set = calc_alg_context.signature_blocking_review_set(true);
                    calc_alg_context
                        .process_context_mut()
                        .signature_blocking_review_set_mut(rev_set)
                        .get_review_data(still_subset)
                        .insert(individual_ancestor_depth, indi_id);
                    let loc_sig_blocking_data = self
                        .get_or_create_signature_blocking_concept_expansion_data(
                            blocking_individual_node,
                            calc_alg_context,
                        );
                    calc_alg_context
                        .process_context_mut()
                        .sig_block_con_exp_data_mut(loc_sig_blocking_data)
                        .set_blocking_review_marked(true)
                        .set_blocking_subset_review_marked(still_subset);
                    let _ = indi_id;
                    return true;
                }
            }
            if review_marked {
                if !is_blocked || blocker_count == blocking_count && still_subset {
                    let review_subset_marked = calc_alg_context
                        .process_context()
                        .sig_block_con_exp_data(sig_blocking_data)
                        .is_blocking_subset_review_marked();
                    let rev_set = calc_alg_context.signature_blocking_review_set(true);
                    calc_alg_context
                        .process_context_mut()
                        .signature_blocking_review_set_mut(rev_set)
                        .get_review_data(review_subset_marked)
                        .remove(indi_id);
                    let loc_sig_blocking_data = self
                        .get_or_create_signature_blocking_concept_expansion_data(
                            blocking_individual_node,
                            calc_alg_context,
                        );
                    calc_alg_context
                        .process_context_mut()
                        .sig_block_con_exp_data_mut(loc_sig_blocking_data)
                        .set_blocking_review_marked(false)
                        .set_blocking_subset_review_marked(still_subset);
                    let _ = indi_id;
                    return true;
                } else if calc_alg_context
                    .process_context()
                    .sig_block_con_exp_data(sig_blocking_data)
                    .is_blocking_subset_review_marked()
                    != still_subset
                {
                    let review_subset_marked = calc_alg_context
                        .process_context()
                        .sig_block_con_exp_data(sig_blocking_data)
                        .is_blocking_subset_review_marked();
                    let rev_set = calc_alg_context.signature_blocking_review_set(true);
                    {
                        let rev_set_mut = calc_alg_context
                            .process_context_mut()
                            .signature_blocking_review_set_mut(rev_set);
                        rev_set_mut
                            .get_review_data(review_subset_marked)
                            .remove(indi_id);
                        rev_set_mut
                            .get_review_data(still_subset)
                            .insert(individual_ancestor_depth, indi_id);
                    }
                    let loc_sig_blocking_data = self
                        .get_or_create_signature_blocking_concept_expansion_data(
                            blocking_individual_node,
                            calc_alg_context,
                        );
                    calc_alg_context
                        .process_context_mut()
                        .sig_block_con_exp_data_mut(loc_sig_blocking_data)
                        .set_blocking_review_marked(false)
                        .set_blocking_subset_review_marked(still_subset);
                    let _ = indi_id;
                    return true;
                }
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::updateSignatureBlockingConceptExpansion`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the body is dominated by the stub
    /// `CSignatureBlockingIndividualNodeConceptExpansionData` /
    /// `CIndividualNodeAnalizedConceptExpansionData` / `CReapplyConceptLabelSet`
    /// accessors and the `CAnalizedConceptExpansionLinker` chain walk. The outer
    /// update gate, the dependency-collection loop, and the three sibling calls
    /// (`create_connection_dependency`, `create_expanded_dependency`,
    /// `add_concept_to_individual_skip_and_processing`) are reproduced; every
    /// satellite deref is `// W6-DEFER[api]`.
    pub fn update_signature_blocking_concept_expansion(
        &mut self,
        mut blocking_individual_node: NodeId,
        sig_blocking_data: SigBlockConExpDataId,
        blocker_individual_node: NodeId,
        blocker_analized_con_exp_data: AnalizedConExpDataId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let blocking_con_set = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(blocking_individual_node);
        let blocking_concept_count = calc_alg_context
            .process_context()
            .label_set(blocking_con_set)
            .get_concept_count();
        let last_updated_con_exp_count = calc_alg_context
            .process_context()
            .sig_block_con_exp_data(sig_blocking_data)
            .get_last_updated_concept_expansion_count();

        let update_due_changed_concepts = blocking_concept_count
            != calc_alg_context
                .process_context()
                .sig_block_con_exp_data(sig_blocking_data)
                .get_last_updated_concept_count();
        let blocker_expansion_concept_count = calc_alg_context
            .process_context()
            .analized_con_exp_data(blocker_analized_con_exp_data)
            .get_expansion_concept_count();
        let update_due_changed_expansions =
            blocker_expansion_concept_count > last_updated_con_exp_count;
        let _ = (blocker_analized_con_exp_data, blocker_individual_node);

        if update_due_changed_concepts || update_due_changed_expansions {
            let mut analized_con_exp_list: Vec<(ConDescId, Vec<ConDescId>)> = Vec::new();
            let mut analized_con_exp_linker = calc_alg_context
                .process_context()
                .analized_con_exp_data(blocker_analized_con_exp_data)
                .get_reverse_analized_concept_expansion_linker();
            while analized_con_exp_linker.is_some() {
                let linker = calc_alg_context
                    .process_context()
                    .analized_con_exp_linker(analized_con_exp_linker);
                analized_con_exp_list.push((
                    linker.get_concept_descriptor(),
                    linker.get_dependend_concept_descriptor_linker().to_vec(),
                ));
                analized_con_exp_linker = linker.get_next();
            }
            for (exp_con_des, dependend_con_des_linker) in analized_con_exp_list {
                let exp_concept = calc_alg_context
                    .process_context()
                    .con_desc(exp_con_des)
                    .get_concept();
                let exp_con_negation = calc_alg_context
                    .process_context()
                    .con_desc(exp_con_des)
                    .is_negated();
                let already_contained = calc_alg_context
                    .process_context()
                    .label_set(blocking_con_set)
                    .contains_concept_in_context(
                        calc_alg_context.process_context(),
                        calc_alg_context.ontology_arenas(),
                        exp_concept,
                        exp_con_negation,
                    );
                if !already_contained {
                    let mut all_dependencies_existings = true;
                    let mut dependencies: DepLinkId = Id::NONE;
                    let mut first_dep_track_point: TrackPointId = Id::NONE;

                    for dep_exp_con_des in dependend_con_des_linker {
                        if !all_dependencies_existings {
                            break;
                        }
                        // KONCLUDE-PORT-NOTE[api]: C++ calls `depExpConDes->getConceptTag()`
                        // directly on the descriptor; the ported `ConceptDescriptor` has no
                        // `get_concept_tag` accessor yet, so the tag is resolved through the
                        // wrapped concept (`CConceptDescriptor` forwards to its concept's tag).
                        let dep_con_tag = {
                            let dep_concept = calc_alg_context
                                .process_context()
                                .con_desc(dep_exp_con_des)
                                .get_concept();
                            calc_alg_context
                                .ontology_arenas()
                                .concept(dep_concept)
                                .get_concept_tag()
                        };
                        let mut dep_con_des: ConDescId = Id::NONE;
                        let mut dep_dep_track_point: TrackPointId = Id::NONE;
                        let con_descriptor_found = calc_alg_context
                            .process_context()
                            .label_set(blocking_con_set)
                            .get_concept_descriptor_by_tag_in_context(
                                calc_alg_context.process_context(),
                                dep_con_tag,
                                &mut dep_con_des,
                                &mut dep_dep_track_point,
                            );
                        if con_descriptor_found {
                            let same_negation = calc_alg_context
                                .process_context()
                                .con_desc(dep_con_des)
                                .is_negated()
                                == calc_alg_context
                                    .process_context()
                                    .con_desc(dep_exp_con_des)
                                    .is_negated();
                            if same_negation {
                                debug_assert!(
                                    dep_dep_track_point != Id::NONE,
                                    "expandCachedConcepts: missing dependency"
                                );
                                let conn_dep_node = self.create_connection_dependency(
                                    &mut blocking_individual_node,
                                    dep_con_des,
                                    dep_dep_track_point,
                                    calc_alg_context,
                                );
                                if conn_dep_node.is_some() {
                                    let conn_dep_track_point = calc_alg_context
                                        .process_context_mut()
                                        .materialize_continue_dependency_track_point(conn_dep_node);
                                    if first_dep_track_point == Id::NONE {
                                        first_dep_track_point = conn_dep_track_point;
                                    } else {
                                        let dep_link = calc_alg_context
                                            .process_context_mut()
                                            .alloc_dep_link(DependencyLink::new());
                                        {
                                            let proc_ctx = calc_alg_context.process_context_mut();
                                            proc_ctx
                                                .dep_link_mut(dep_link)
                                                .init_dependency(conn_dep_track_point);
                                            proc_ctx.dep_link_mut(dep_link).next = dependencies;
                                        }
                                        dependencies = dep_link;
                                    }
                                }
                            } else {
                                all_dependencies_existings = false;
                            }
                        } else {
                            all_dependencies_existings = false;
                        }
                        let _ = dep_con_tag;
                    }

                    if all_dependencies_existings {
                        // W6-DEFER[api]: STATINC(SIGNATUREMIRRORINGBLOCKINGCONCEPTEXPANSIONCOUNT,...)
                        debug_assert!(
                            first_dep_track_point != Id::NONE,
                            "expandCachedConcepts: missing dependency"
                        );
                        let mut exp_dep_track_point: TrackPointId = Id::NONE;
                        let _exp_dep_node = self.create_expanded_dependency(
                            &mut exp_dep_track_point,
                            &mut blocking_individual_node,
                            first_dep_track_point,
                            dependencies,
                            calc_alg_context,
                        );
                        self.add_concept_to_individual_skip_and_processing(
                            exp_concept,
                            exp_con_negation,
                            blocking_individual_node,
                            exp_dep_track_point,
                            true,
                            false,
                            true,
                            calc_alg_context,
                        );
                    }
                }
            }
            calc_alg_context
                .process_context_mut()
                .sig_block_con_exp_data_mut(sig_blocking_data)
                .set_last_updated_concept_expansion_count(blocker_expansion_concept_count)
                .set_last_updated_concept_count(blocking_concept_count);
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isConceptSignatureBlockingCritical`.
    pub fn is_concept_signature_blocking_critical(
        &self,
        con_des: ConDescId,
        dep_track_point: TrackPointId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = dep_track_point;
        let concept = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let con_neg = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .is_negated();
        let op_code = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        let _param = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_parameter();
        let cardinality = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_parameter()
            + 1 * (con_neg as Cint64);
        if cardinality > 1
            && ((!con_neg && op_code == CCATMOST) || (con_neg && op_code == CCATLEAST))
        {
            return true;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateIndirectSuccessorSignatureBlocked`.
    pub fn propagate_indirect_successor_signature_blocked(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.propagate_adding_blocked_processing_restriction_to_successors(
            indi,
            IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
            true,
            IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateIndirectSuccessorReuseBlocked`.
    pub fn propagate_indirect_successor_reuse_blocked(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.propagate_adding_blocked_processing_restriction_to_successors(
            indi,
            IndividualProcessNode::PRF_REUSINGINDIVIDUAL,
            true,
            IndividualProcessNode::PRF_ANCESTORREUSINGINDIVIDUALBLOCKED,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reactivateIndirectSignatureBlockedSuccessors`.
    pub fn reactivate_indirect_signature_blocked_successors(
        &mut self,
        mut indi: NodeId,
        recursive: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = recursive;
        // W6-DEFER[api]: succIt = indi->getSuccessorIterator(); — node has no successor_iterator accessor yet.
        let succ_it: Vec<EdgeId> = Vec::new();
        let anc_depth = calc_alg_context
            .process_context()
            .node(indi)
            .individual_ancestor_depth();
        for succ_link in succ_it {
            let succ_indi = self.get_successor_individual(&mut indi, succ_link, calc_alg_context);
            let succ_anc_depth = calc_alg_context
                .process_context()
                .node(succ_indi)
                .individual_ancestor_depth();
            if succ_anc_depth > anc_depth {
                if calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
                    )
                {
                    if !calc_alg_context
                        .process_context()
                        .node(succ_indi)
                        .has_partial_processing_restriction_flags(
                            IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHEDABOLISHED,
                        )
                    {
                        let loc_indi_node =
                            self.get_localized_individual(succ_indi, false, calc_alg_context);
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(loc_indi_node)
                            .add_processing_restriction_flags(
                                IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHEDABOLISHED,
                            );
                        self.add_individual_to_processing_queue(loc_indi_node, calc_alg_context);
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::eliminiateBlockedIndividuals`.
    pub fn eliminiate_blocked_individuals(
        &mut self,
        indi_proc_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if calc_alg_context
            .process_context()
            .node(indi_proc_node)
            .has_blocked_individuals_linker()
        {
            // reactivate all blocked individuals
            self.reactivate_blocked_individuals(indi_proc_node, calc_alg_context);
        }
        if calc_alg_context
            .process_context()
            .node_has_blocking_follower(indi_proc_node)
        {
            let follower_set = calc_alg_context
                .process_context()
                .node_blocking_followers(indi_proc_node);
            for blocking_indi_node_id in follower_set {
                let blocking_indi_node =
                    self.get_up_to_date_individual_by_id(blocking_indi_node_id, calc_alg_context);
                self.add_individual_to_blocking_update_review_processing_queue(
                    blocking_indi_node,
                    calc_alg_context,
                );
            }
        }
        // processingBlockedNodeLinker = indiProcNode->getProcessingBlockedIndividualsLinker();
        let processing_blocked_node_linker: Vec<NodeId> = calc_alg_context
            .process_context()
            .node(indi_proc_node)
            .get_processing_blocked_individuals_linker()
            .to_vec();
        for blocked_node in processing_blocked_node_linker {
            let loc_blocked_node =
                self.get_localized_individual(blocked_node, true, calc_alg_context);
            calc_alg_context
                .process_context_mut()
                .node_mut(loc_blocked_node)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED,
                );
            self.add_individual_to_processing_queue(loc_blocked_node, calc_alg_context);
        }
        calc_alg_context
            .process_context_mut()
            .node_mut(indi_proc_node)
            .clear_blocked_individuals_linker();
    }
}
