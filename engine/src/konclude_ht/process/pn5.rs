//! `process::pn5` — method-batch unit **PN-5** of `CIndividualProcessNode`:
//! invalid-signature blocking + successor backward-dependency linkers +
//! role-backward-propagation / individual-process / concept-process linkers +
//! substitute-node + queue-membership flags + last-processing priority
//! (`Source/Reasoner/Kernel/Process/CIndividualProcessNode.cpp` lines 1673–2009).
//!
//! Faithful, method-by-method port (snake_case of each C++ name, same control
//! flow). The methods here are mostly trivial field getters/setters/flag
//! toggles; context-sensitive ownership differences are documented with
//! `KONCLUDE-PORT-NOTE[...]` comments at the relevant method bodies.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ `mSuccessorIndiNodeBackwardDependencyLinker`
//! is an intrusive `CXLinker<CIndividualProcessNode*>` chain; per `substrate.rs`
//! and `node.rs` it is modelled as an owned `Vec<NodeId>` (one chain cell == one
//! `NodeId`). `add*` prepends (the C++ `linker->append(existing)` returns the new
//! head with the freshly-passed cell at the front); `set*` replaces the whole
//! chain; `get*` borrows it; `clear*` empties it. Iteration order is preserved.

#![allow(dead_code)]

use super::super::model::{Cint64, Id};
use super::concept_process_linker::ConceptProcessLinkerId;
use super::context::ProcessContext;
use super::individual_process_linker::IndividualProcessNodeLinkerId;
use super::node::{IndividualProcessNode, IndividualProcessNodePriority};
use super::role_backward_prop::RoleBackwardPropagationHashId as RoleBackPropHashId;
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
            self.successor_indi_node_backward_dependency_linker
                .insert(0, linker);
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
        !self
            .successor_indi_node_backward_dependency_linker
            .is_empty()
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

    /// Port-facing read of `CIndividualProcessNode::getRoleBackwardPropagationHash(false)`.
    pub fn role_backward_propagation_hash(&self, create: bool) -> RoleBackPropHashId {
        debug_assert!(
            !create,
            "use ProcessContext::node_role_backward_propagation_hash for create=true"
        );
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
    ///
    /// Requires the arena-owning `ProcessContext` to resolve
    /// `mConceptProcessLinker->getNext()`. `ProcessContext::node_take_concept_process_linker`
    /// is the usual call path when the node itself is arena-owned.
    pub fn take_concept_process_linker(
        &mut self,
        process_context: &ProcessContext,
    ) -> ConceptProcessLinkerId {
        let con_proc_linker = self.concept_process_linker;
        if self.concept_process_linker.is_some() {
            self.concept_process_linker = process_context
                .concept_process_linker(con_proc_linker)
                .get_next();
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
    ///
    /// Requires the arena-owning `ProcessContext` to execute
    /// `conProcessLinker->append(mConceptProcessLinker)`. `ProcessContext::
    /// node_add_concept_process_linker` is the usual call path when the node
    /// itself is arena-owned.
    pub fn add_concept_process_linker(
        &mut self,
        con_process_linker: ConceptProcessLinkerId,
        process_context: &mut ProcessContext,
    ) -> &mut Self {
        self.concept_process_linker = process_context
            .append_concept_process_linker_chain(con_process_linker, self.concept_process_linker);
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
    pub fn set_deterministic_expanding_processing_queued(
        &mut self,
        imm_pro_que: bool,
    ) -> &mut Self {
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
        self.last_processing_priority.set_priority_to_null();
        self
    }

    /// Port of `CIndividualProcessNode::getLastProcessingPriority`.
    pub fn last_processing_priority(&self) -> IndividualProcessNodePriority {
        self.last_processing_priority
    }
}

impl ProcessContext {
    /// Arena-backed port of `CIndividualProcessNode::takeConceptProcessLinker`.
    pub fn node_take_concept_process_linker(&mut self, node: NodeId) -> ConceptProcessLinkerId {
        let con_proc_linker = self.node(node).concept_process_linker;
        if con_proc_linker.is_some() {
            let next = self.concept_process_linker(con_proc_linker).get_next();
            self.node_mut(node).concept_process_linker = next;
        }
        con_proc_linker
    }

    /// Port of `CLinkerBase::append` for `CConceptProcessLinker` ids.
    pub fn append_concept_process_linker_chain(
        &mut self,
        linker: ConceptProcessLinkerId,
        appending_list: ConceptProcessLinkerId,
    ) -> ConceptProcessLinkerId {
        if linker.is_none() {
            return appending_list;
        }
        let mut last = linker;
        loop {
            let next = self.concept_process_linker(last).get_next();
            if next.is_none() {
                break;
            }
            last = next;
        }
        self.concept_process_linker_mut(last)
            .set_next(appending_list);
        linker
    }

    /// Arena-backed port of `CIndividualProcessNode::addConceptProcessLinker`.
    pub fn node_add_concept_process_linker(
        &mut self,
        node: NodeId,
        con_process_linker: ConceptProcessLinkerId,
    ) -> &mut Self {
        let old_head = self.node(node).concept_process_linker;
        let new_head = self.append_concept_process_linker_chain(con_process_linker, old_head);
        self.node_mut(node).concept_process_linker = new_head;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::RoleId;
    use super::super::concept_process_linker::ConceptProcessLinker;
    use super::super::role_backward_prop::{
        BackwardPropagationLink, BackwardPropagationLinkId, BackwardPropagationReapplyDescriptor,
    };
    use super::super::stubs::ProcessContextId;
    use super::super::ConDescId;
    use super::*;

    #[test]
    fn pn5_reset_last_processing_priority_delegates_to_priority_null_reset() {
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);
        node.set_last_processing_priority(IndividualProcessNodePriority {
            priority_con: 3.0,
            priority_ind: 5.0,
            strict_order: false,
        });

        node.reset_last_processing_priority();

        assert_eq!(node.last_processing_priority().priority_con, 0.0);
        assert_eq!(node.last_processing_priority().priority_ind, 0.0);
        assert!(node.last_processing_priority().strict_order);
        assert!(node.last_processing_priority().is_null_priority());
    }

    #[test]
    fn pn5_context_concept_process_linker_add_appends_old_head_to_tail_and_take_advances() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::new(ProcessContextId::NONE));
        let first = ctx.alloc_concept_process_linker(ConceptProcessLinker::new());
        let second = ctx.alloc_concept_process_linker(ConceptProcessLinker::new());
        let old_head = ctx.alloc_concept_process_linker(ConceptProcessLinker::new());

        ctx.concept_process_linker_mut(first).set_next(second);
        ctx.node_mut(node).set_concept_process_linker(old_head);

        ctx.node_add_concept_process_linker(node, first);

        assert_eq!(ctx.node(node).concept_process_linker(), first);
        assert_eq!(ctx.concept_process_linker(first).get_next(), second);
        assert_eq!(ctx.concept_process_linker(second).get_next(), old_head);

        assert_eq!(ctx.node_take_concept_process_linker(node), first);
        assert_eq!(ctx.node(node).concept_process_linker(), second);
        assert_eq!(ctx.node_take_concept_process_linker(node), second);
        assert_eq!(ctx.node(node).concept_process_linker(), old_head);
    }

    #[test]
    fn pn5_context_role_backward_propagation_hash_lazy_allocates() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::new(ProcessContextId::NONE));

        assert!(ctx
            .node_role_backward_propagation_hash(node, false)
            .is_none());
        let hash = ctx.node_role_backward_propagation_hash(node, true);

        assert!(hash.is_some());
        assert_eq!(ctx.node(node).role_backward_propagation_hash(false), hash);
        assert!(ctx
            .role_backward_prop_hash(hash)
            .get_role_backward_propagation_data_hash()
            .is_empty());
    }

    #[test]
    fn pn5_role_backward_hash_preserves_konclude_prepend_and_return_values() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::new(ProcessContextId::NONE));
        let source_a = ctx.alloc_node(IndividualProcessNode::new(ProcessContextId::NONE));
        let source_b = ctx.alloc_node(IndividualProcessNode::new(ProcessContextId::NONE));
        let role = RoleId::new(7);
        let concept = ConDescId::new(11);
        let hash = ctx.node_role_backward_propagation_hash(node, true);

        let mut reapply = BackwardPropagationReapplyDescriptor::new();
        reapply.init_backward_propagation_reapply_descriptor(concept);
        let reapply = ctx.alloc_backward_prop_reapply_desc(reapply);
        assert_eq!(
            ctx.role_backward_prop_hash_add_backward_propagation_concept_descriptor(
                hash, role, reapply
            ),
            BackwardPropagationLinkId::NONE
        );

        let mut first = BackwardPropagationLink::new();
        first.init_backward_propagation_link(source_a, role);
        let first = ctx.alloc_backward_prop_link(first);
        assert_eq!(
            ctx.role_backward_prop_hash_add_backward_propagation_link(hash, role, first),
            reapply
        );

        let mut second = BackwardPropagationLink::new();
        second.init_backward_propagation_link(source_b, role);
        let second = ctx.alloc_backward_prop_link(second);
        assert_eq!(
            ctx.role_backward_prop_hash_add_backward_propagation_link(hash, role, second),
            reapply
        );

        let data = ctx
            .role_backward_prop_hash(hash)
            .get_role_backward_propagation_data_hash()
            .get(&role)
            .copied()
            .unwrap();
        assert_eq!(data.link_linker, second);
        assert_eq!(ctx.backward_prop_link(second).get_next(), first);
        assert_eq!(data.reapply_linker, reapply);
        assert_eq!(
            ctx.backward_prop_reapply_desc(reapply)
                .get_reaplly_concept_descriptor(),
            concept
        );
    }

    #[test]
    fn pn5_role_backward_hash_duplicate_source_guard_checks_existing_head() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::new(ProcessContextId::NONE));
        let source = ctx.alloc_node(IndividualProcessNode::new(ProcessContextId::NONE));
        let role = RoleId::new(13);
        let hash = ctx.node_role_backward_propagation_hash(node, true);

        let mut first = BackwardPropagationLink::new();
        first.init_backward_propagation_link(source, role);
        let first = ctx.alloc_backward_prop_link(first);
        assert!(ctx
            .role_backward_prop_hash_add_backward_propagation_link(hash, role, first)
            .is_none());

        let mut duplicate = BackwardPropagationLink::new();
        duplicate.init_backward_propagation_link(source, role);
        let duplicate = ctx.alloc_backward_prop_link(duplicate);
        assert!(ctx
            .role_backward_prop_hash_add_backward_propagation_link(hash, role, duplicate)
            .is_none());

        let data = ctx
            .role_backward_prop_hash(hash)
            .get_role_backward_propagation_data_hash()
            .get(&role)
            .unwrap();
        assert_eq!(data.link_linker, first);
        assert_eq!(
            ctx.backward_prop_link(first).get_next(),
            BackwardPropagationLinkId::NONE
        );
    }
}
