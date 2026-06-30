//! `process::pn5` — method-batch unit **PN-5** of `CIndividualProcessNode`:
//! invalid-signature blocking + successor backward-dependency linkers +
//! role-backward-propagation / individual-process / concept-process linkers +
//! substitute-node + queue-membership flags + last-processing priority
//! (`Source/Reasoner/Kernel/Process/CIndividualProcessNode.cpp` lines 1673–2009).
//!
//! Faithful, method-by-method port (snake_case of each C++ name, same control
//! flow). The methods here are mostly trivial field getters/setters/flag
//! toggles; the few that touch not-yet-ported linker/allocator classes carry a
//! `W2-DEFER[api]` marker plus the closest minimal stub, matching the PN-1
//! convention.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ `mSuccessorIndiNodeBackwardDependencyLinker`
//! is an intrusive `CXLinker<CIndividualProcessNode*>` chain; per `substrate.rs`
//! and `node.rs` it is modelled as an owned `Vec<NodeId>` (one chain cell == one
//! `NodeId`). `add*` prepends (the C++ `linker->append(existing)` returns the new
//! head with the freshly-passed cell at the front); `set*` replaces the whole
//! chain; `get*` borrows it; `clear*` empties it. Iteration order is preserved.

#![allow(dead_code)]

use super::super::model::{Cint64, Id};
use super::node::{IndividualProcessNode, IndividualProcessNodePriority};
use super::stubs::{ConceptProcessLinkerId, IndividualProcessNodeLinkerId, RoleBackPropHashId};
use super::NodeId;

impl IndividualProcessNode {
    // ===================================================================
    // Invalid-signature blocking.
    // ===================================================================

    /// Port of `CIndividualProcessNode::isInvalidSignatureBlocking`.
    pub fn is_invalid_signature_blocking(&self) -> bool {
        self.invalid_signature_blocking
    }

    /// Port of `CIndividualProcessNode::setInvalidSignatureBlocking`.
    pub fn set_invalid_signature_blocking(&mut self, invalid: bool) -> &mut Self {
        self.invalid_signature_blocking = invalid;
        self
    }

    // ===================================================================
    // Successor-individual-node backward-dependency linker chain
    // (`Vec<NodeId>`; see module note).
    // ===================================================================

    /// Port of `CIndividualProcessNode::addSuccessorIndividualNodeBackwardDependencyLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `linker->append(existing)` prepends
    /// the passed chain cell; ported as a front-insert of a single `NodeId`.
    pub fn add_successor_individual_node_backward_dependency_linker(
        &mut self,
        linker: NodeId,
    ) -> &mut Self {
        if linker != Id::NONE {
            // mSuccessorIndiNodeBackwardDependencyLinker = linker->append(mSuccessorIndiNodeBackwardDependencyLinker);
            self.successor_indi_node_backward_dependency_linker.insert(0, linker);
        }
        self
    }

    /// Port of `CIndividualProcessNode::setSuccessorIndividualNodeBackwardDependencyLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ assigns a `CXLinker*` chain head;
    /// the port replaces the owned `Vec<NodeId>` representing that chain.
    pub fn set_successor_individual_node_backward_dependency_linker(
        &mut self,
        linker: Vec<NodeId>,
    ) -> &mut Self {
        self.successor_indi_node_backward_dependency_linker = linker;
        self
    }

    /// Port of `CIndividualProcessNode::getSuccessorIndividualNodeBackwardDependencyLinker`.
    pub fn successor_individual_node_backward_dependency_linker(&self) -> &Vec<NodeId> {
        &self.successor_indi_node_backward_dependency_linker
    }

    /// Port of `CIndividualProcessNode::hasSuccessorIndividualNodeBackwardDependencyLinker`.
    pub fn has_successor_individual_node_backward_dependency_linker(&self) -> bool {
        !self.successor_indi_node_backward_dependency_linker.is_empty()
    }

    /// Port of `CIndividualProcessNode::clearSuccessorIndividualNodeBackwardDependencyLinker`.
    pub fn clear_successor_individual_node_backward_dependency_linker(&mut self) -> &mut Self {
        self.successor_indi_node_backward_dependency_linker.clear();
        self
    }

    /// Port of `CIndividualProcessNode::hasBackwardDependencyToAncestorIndividualNode`.
    pub fn has_backward_dependency_to_ancestor_individual_node(&self) -> bool {
        self.backward_dependency_to_ancestor_individual_node
    }

    /// Port of `CIndividualProcessNode::setBackwardDependencyToAncestorIndividualNode`.
    pub fn set_backward_dependency_to_ancestor_individual_node(
        &mut self,
        backward_dependency: bool,
    ) -> &mut Self {
        self.backward_dependency_to_ancestor_individual_node = backward_dependency;
        self
    }

    // ===================================================================
    // Role-backward-propagation hash (lazy-allocated).
    // ===================================================================

    /// Port of `CIndividualProcessNode::getRoleBackwardPropagationHash`.
    pub fn role_backward_propagation_hash(&mut self, create: bool) -> RoleBackPropHashId {
        if create && self.role_back_prop_hash == Id::NONE {
            // mRoleBackPropHash = CObjectParameterizingAllocator<CRoleBackwardPropagationHash,CProcessContext*>
            //     ::allocateAndConstructAndParameterize(mMemAllocMan, mProcessContext);
            // W2-DEFER[api]: allocate a RoleBackwardPropagationHash in the per-test
            // arena (over mem_alloc_man / process_context) and store its id here.
        }
        self.role_back_prop_hash
    }

    // ===================================================================
    // Individual-process-node linker.
    // ===================================================================

    /// Port of `CIndividualProcessNode::getIndividualProcessNodeLinker`.
    pub fn individual_process_node_linker(&self) -> IndividualProcessNodeLinkerId {
        self.indi_process_linker
    }

    /// Port of `CIndividualProcessNode::setIndividualProcessNodeLinker`.
    pub fn set_individual_process_node_linker(
        &mut self,
        process_node_linker: IndividualProcessNodeLinkerId,
    ) -> &mut Self {
        self.indi_process_linker = process_node_linker;
        self
    }

    // ===================================================================
    // Concept-process linker chain.
    // ===================================================================

    /// Port of `CIndividualProcessNode::getConceptProcessLinker`.
    pub fn concept_process_linker(&self) -> ConceptProcessLinkerId {
        self.concept_process_linker
    }

    /// Port of `CIndividualProcessNode::takeConceptProcessLinker`.
    pub fn take_concept_process_linker(&mut self) -> ConceptProcessLinkerId {
        let con_proc_linker = self.concept_process_linker;
        if self.concept_process_linker != Id::NONE {
            // mConceptProcessLinker = mConceptProcessLinker->getNext();
            // W2-DEFER[api]: CConceptProcessLinker::get_next over the per-test arena;
            // until the linker class is ported, advance to NONE (head pop only).
            self.concept_process_linker = Id::NONE;
        }
        con_proc_linker
    }

    /// Port of `CIndividualProcessNode::setConceptProcessLinker`.
    pub fn set_concept_process_linker(
        &mut self,
        con_process_linker: ConceptProcessLinkerId,
    ) -> &mut Self {
        self.concept_process_linker = con_process_linker;
        self
    }

    /// Port of `CIndividualProcessNode::addConceptProcessLinker`.
    pub fn add_concept_process_linker(
        &mut self,
        con_process_linker: ConceptProcessLinkerId,
    ) -> &mut Self {
        // mConceptProcessLinker = conProcessLinker->append(mConceptProcessLinker);
        // W2-DEFER[api]: CConceptProcessLinker::append (chain the existing head
        // behind the passed linker over the per-test arena); until ported, set head.
        self.concept_process_linker = con_process_linker;
        self
    }

    /// Port of `CIndividualProcessNode::clearConceptProcessLinker`.
    pub fn clear_concept_process_linker(&mut self) -> &mut Self {
        self.concept_process_linker = Id::NONE;
        self
    }

    // ===================================================================
    // Required-backward-propagation + substitute node.
    // ===================================================================

    /// Port of `CIndividualProcessNode::getRequiredBackwardPropagation`.
    pub fn required_backward_propagation(&self) -> bool {
        self.required_back_prop
    }

    /// Port of `CIndividualProcessNode::setRequiredBackwardPropagation`.
    pub fn set_required_backward_propagation(&mut self, required_back_prop: bool) -> &mut Self {
        self.required_back_prop = required_back_prop;
        self
    }

    /// Port of `CIndividualProcessNode::hasSubstituteIndividualNode`.
    pub fn has_substitute_individual_node(&self) -> bool {
        self.substitute_indi_node != Id::NONE
    }

    /// Port of `CIndividualProcessNode::getSubstituteIndividualNode`.
    pub fn substitute_individual_node(&self) -> NodeId {
        self.substitute_indi_node
    }

    /// Port of `CIndividualProcessNode::setSubstituteIndividualNode`.
    pub fn set_substitute_individual_node(&mut self, indi_node: NodeId) -> &mut Self {
        self.substitute_indi_node = indi_node;
        self
    }

    // ===================================================================
    // Queue-membership flags (getters).
    // ===================================================================

    /// Port of `CIndividualProcessNode::isProcessingQueued`.
    pub fn is_processing_queued(&self) -> bool {
        self.processing_queued
    }

    /// Port of `CIndividualProcessNode::isExtendedQueueProcessing`.
    pub fn is_extended_queue_processing(&self) -> bool {
        self.extended_queue_processing
    }

    /// Port of `CIndividualProcessNode::isImmediatelyProcessingQueued`.
    pub fn is_immediately_processing_queued(&self) -> bool {
        self.immediately_processing_queued
    }

    /// Port of `CIndividualProcessNode::isDeterministicExpandingProcessingQueued`.
    pub fn is_deterministic_expanding_processing_queued(&self) -> bool {
        self.det_exp_processing_queued
    }

    /// Port of `CIndividualProcessNode::isRegularDepthProcessingQueued`.
    pub fn is_regular_depth_processing_queued(&self) -> bool {
        self.depth_processing_queued
    }

    /// Port of `CIndividualProcessNode::isBlockedReactivationProcessingQueued`.
    pub fn is_blocked_reactivation_processing_queued(&self) -> bool {
        self.blocked_react_processing_queued
    }

    // ===================================================================
    // Queue-membership flags (setters).
    // ===================================================================

    /// Port of `CIndividualProcessNode::setProcessingQueued`.
    pub fn set_processing_queued(&mut self, processing_queued: bool) -> &mut Self {
        self.processing_queued = processing_queued;
        self
    }

    /// Port of `CIndividualProcessNode::setExtendedQueueProcessing`.
    pub fn set_extended_queue_processing(&mut self, extended_queue_processing: bool) -> &mut Self {
        self.extended_queue_processing = extended_queue_processing;
        self
    }

    /// Port of `CIndividualProcessNode::setImmediatelyProcessingQueued`.
    pub fn set_immediately_processing_queued(&mut self, imm_pro_que: bool) -> &mut Self {
        self.immediately_processing_queued = imm_pro_que;
        self
    }

    /// Port of `CIndividualProcessNode::setDeterministicExpandingProcessingQueued`.
    pub fn set_deterministic_expanding_processing_queued(&mut self, imm_pro_que: bool) -> &mut Self {
        self.det_exp_processing_queued = imm_pro_que;
        self
    }

    /// Port of `CIndividualProcessNode::setRegularDepthProcessingQueued`.
    pub fn set_regular_depth_processing_queued(&mut self, depth_pro: bool) -> &mut Self {
        self.depth_processing_queued = depth_pro;
        self
    }

    /// Port of `CIndividualProcessNode::setBlockedReactivationProcessingQueued`.
    pub fn set_blocked_reactivation_processing_queued(&mut self, depth_pro: bool) -> &mut Self {
        self.blocked_react_processing_queued = depth_pro;
        self
    }

    /// Port of `CIndividualProcessNode::setBackendSynchronRetestProcessingQueued`.
    pub fn set_backend_synchron_retest_processing_queued(
        &mut self,
        backend_sync_retest: bool,
    ) -> &mut Self {
        self.backend_synchron_retest_processing_queued = backend_sync_retest;
        self
    }

    /// Port of `CIndividualProcessNode::isBackendSynchronRetestProcessingQueued`.
    pub fn is_backend_synchron_retest_processing_queued(&self) -> bool {
        self.backend_synchron_retest_processing_queued
    }

    /// Port of `CIndividualProcessNode::setBackendIndirectCompatibilityExpansionQueued`.
    pub fn set_backend_indirect_compatibility_expansion_queued(
        &mut self,
        queued: bool,
    ) -> &mut Self {
        self.backend_indirect_compatibility_expansion_queued = queued;
        self
    }

    /// Port of `CIndividualProcessNode::isBackendIndirectCompatibilityExpansionQueued`.
    pub fn is_backend_indirect_compatibility_expansion_queued(&self) -> bool {
        self.backend_indirect_compatibility_expansion_queued
    }

    /// Port of `CIndividualProcessNode::setBackendDirectInfluenceExpansionQueued`.
    pub fn set_backend_direct_influence_expansion_queued(&mut self, queued: bool) -> &mut Self {
        self.backend_direct_influence_expansion_queued = queued;
        self
    }

    /// Port of `CIndividualProcessNode::isBackendDirectInfluenceExpansionQueued`.
    pub fn is_backend_direct_influence_expansion_queued(&self) -> bool {
        self.backend_direct_influence_expansion_queued
    }

    /// Port of `CIndividualProcessNode::setIncrementalCompatibilityCheckingQueued`.
    pub fn set_incremental_compatibility_checking_queued(
        &mut self,
        inc_comp_checking: bool,
    ) -> &mut Self {
        self.incremental_compatibility_checking_queued = inc_comp_checking;
        self
    }

    /// Port of `CIndividualProcessNode::isIncrementalCompatibilityCheckingQueued`.
    pub fn is_incremental_compatibility_checking_queued(&self) -> bool {
        self.incremental_compatibility_checking_queued
    }

    /// Port of `CIndividualProcessNode::setIncrementalExpansionQueued`.
    pub fn set_incremental_expansion_queued(&mut self, inc_exp_queued: bool) -> &mut Self {
        self.incremental_expansion_queued = inc_exp_queued;
        self
    }

    /// Port of `CIndividualProcessNode::isIncrementalExpansionQueued`.
    pub fn is_incremental_expansion_queued(&self) -> bool {
        self.incremental_expansion_queued
    }

    /// Port of `CIndividualProcessNode::setBackendReuseExpansionQueued`.
    pub fn set_backend_reuse_expansion_queued(&mut self, queued: bool) -> &mut Self {
        self.backend_reuse_expansion_queued = queued;
        self
    }

    /// Port of `CIndividualProcessNode::isBackendReuseExpansionQueued`.
    pub fn is_backend_reuse_expansion_queued(&self) -> bool {
        self.backend_reuse_expansion_queued
    }

    /// Port of `CIndividualProcessNode::setBackendNeighbourExpansionQueued`.
    pub fn set_backend_neighbour_expansion_queued(&mut self, queued: bool) -> &mut Self {
        self.backend_neighbour_expansion_queued = queued;
        self
    }

    /// Port of `CIndividualProcessNode::isBackendNeighbourExpansionQueued`.
    pub fn is_backend_neighbour_expansion_queued(&self) -> bool {
        self.backend_neighbour_expansion_queued
    }

    /// Port of `CIndividualProcessNode::clearProcessingQueued`.
    pub fn clear_processing_queued(&mut self) -> &mut Self {
        self.blocked_react_processing_queued = false;
        self.processing_queued = false;
        self.immediately_processing_queued = false;
        self.det_exp_processing_queued = false;
        self.depth_processing_queued = false;
        self.delayed_nominal_processing_queued = false;
        self.backend_synchron_retest_processing_queued = false;
        self.backend_direct_influence_expansion_queued = false;
        self.backend_indirect_compatibility_expansion_queued = false;
        self.incremental_compatibility_checking_queued = false;
        self.incremental_expansion_queued = false;
        self
    }

    // ===================================================================
    // Delayed-nominal processing + assertion-init signature.
    // ===================================================================

    /// Port of `CIndividualProcessNode::isDelayedNominalProcessingQueued`.
    pub fn is_delayed_nominal_processing_queued(&self) -> bool {
        self.delayed_nominal_processing_queued
    }

    /// Port of `CIndividualProcessNode::hasNominalProcessingDelayingChecked`.
    pub fn has_nominal_processing_delaying_checked(&self) -> bool {
        self.nominal_processing_delaying_checked
    }

    /// Port of `CIndividualProcessNode::setDelayedNominalProcessingQueued`.
    pub fn set_delayed_nominal_processing_queued(
        &mut self,
        delayed_processing_queued: bool,
    ) -> &mut Self {
        self.delayed_nominal_processing_queued = delayed_processing_queued;
        self
    }

    /// Port of `CIndividualProcessNode::setNominalProcessingDelayingChecked`.
    pub fn set_nominal_processing_delaying_checked(
        &mut self,
        nominal_processing_delaying_checked: bool,
    ) -> &mut Self {
        self.nominal_processing_delaying_checked = nominal_processing_delaying_checked;
        self
    }

    /// Port of `CIndividualProcessNode::setAssertionInitialisationSignatureValue`.
    pub fn set_assertion_initialisation_signature_value(&mut self, sig_value: Cint64) -> &mut Self {
        self.assertion_initialisation_signature_value = sig_value;
        self
    }

    /// Port of `CIndividualProcessNode::getAssertionInitialisationSignatureValue`.
    pub fn assertion_initialisation_signature_value(&self) -> Cint64 {
        self.assertion_initialisation_signature_value
    }

    // ===================================================================
    // Last-processing priority.
    // ===================================================================

    /// Port of `CIndividualProcessNode::setLastProcessingPriority`.
    pub fn set_last_processing_priority(
        &mut self,
        priority: IndividualProcessNodePriority,
    ) -> &mut Self {
        self.last_processing_priority = priority;
        self
    }

    /// Port of `CIndividualProcessNode::resetLastProcessingPriority`.
    pub fn reset_last_processing_priority(&mut self) -> &mut Self {
        // mLastProcessingPriority.setPriorityToNull();
        // W2-DEFER[api]: CIndividualProcessNodePriority::set_priority_to_null is a
        // method of the (separate) priority class, not part of PN-5; port it with
        // that class so this call delegates instead of mutating fields inline.
        self
    }

    /// Port of `CIndividualProcessNode::getLastProcessingPriority`.
    pub fn last_processing_priority(&self) -> IndividualProcessNodePriority {
        self.last_processing_priority
    }
}
