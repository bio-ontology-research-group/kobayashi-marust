//! `process::pn3` — method-batch unit **PN-3** of `CIndividualProcessNode`:
//! lazy label / prop-hash getters + role-successor / edge ops + reapply queues +
//! topology / link install-remove
//! (`Source/Reasoner/Kernel/Process/CIndividualProcessNode.cpp` lines 838-1271).
//!
//! Ported per `manifest/05-process-units.md` §3 PN-3, function-by-function after
//! SD-3 (`node.rs`) and PN-1 (`pn1.rs`).
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ methods reach into the node's per-test
//! satellite objects (`mUseReapplyConLabelSet`, `mUseReapplyRoleSuccHash`,
//! `mUseSuccRoleHash`, `mUseConnSuccSet`, `mUseDisjointSuccRoleHash`,
//! `mUseDistinctHash`, the concept-prop hashes, …) through raw pointers and
//! allocate fresh ones from the task pool. In the port a node only holds the
//! `Id<T>` of each satellite; the objects live in per-test arenas owned by the
//! ambient process context, and the satellites' own methods
//! (`insertRoleSuccessorLink`, `getRoleSuccessorLinkIterator`,
//! `initConceptLabelSet`, …) are themselves DEFERRED to units LS-1 / RS-1 / BM-1.
//! Therefore the BRANCH STRUCTURE is preserved exactly — the C++ `if (mUseX)` /
//! `if (create && !mX)` pointer tests map 1:1 to `self.use_x.is_some()` /
//! `create && self.x.is_none()`, since `Id::NONE` == `nullptr` — but every body
//! step that dereferences a satellite or the allocator is marked
//! `// KONCLUDE-PORT-NOTE[ownership]` and routed through context-threaded
//! companions where the satellite arenas are already threaded through
//! `ProcessContext`. Remaining deferred steps are explicit local gaps; the
//! control flow is faithful.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the overloads that take a sibling
//! `CIndividualProcessNode* desIndi/indiNode/individual` only dereference it to
//! read `getIndividualNodeID()`. Following the PN-1 precedent (which borrows
//! `prev: &mut IndividualProcessNode`), they take the sibling as
//! `&IndividualProcessNode` and forward to the id-keyed overload. The C++ relies
//! on the two nodes being distinct objects, exactly as the borrow does.

#![allow(dead_code)]

use super::super::model::{Cint64, ConceptId, RoleId};
use super::context::ProcessContext;
use super::distinct::{ConnectionSuccessorSetIterator, DisjointSuccessorRoleIterator};
use super::node::IndividualProcessNode;
use super::rs1::{ReapplyQueueIterator, RoleSuccessorIterator, RoleSuccessorLinkIterator};
use super::stubs::{
    ConceptProcessingQueueId, ConceptPropBindingSetHashId, ConceptRepPropSetHashId,
    ConceptVarBindPathSetHashId, ConnSuccSetId, DisjointSuccRoleHashId, DistinctHashId,
    SuccRoleHashId,
};
use super::succ_role_hash::{SuccessorIterator, SuccessorRoleIterator};
use super::{DisjointEdgeId, EdgeId, LabelSetId, NodeId, RoleSuccHashId};

// ===========================================================================
// Placeholder return types (not-yet-ported `Process/` iterator / queue classes).
// KONCLUDE-PORT-NOTE[api]: PN-3 returns several `Process/` iterator and reapply
// queue types that have their own (unported) units. They are stubbed here so the
// PN-3 signatures stay exact and diffable; each default-constructs to the C++
// empty/null iterator the `else` branches return. When the real iterator units
// land these reconcile to them.
// ===========================================================================

/// Port of `CCondensedReapplyQueueIterator` (placeholder; the C++ ctor carries the
/// `conceptNegation` flag — `CCondensedReapplyQueueIterator(nullptr,conceptNegation)`).
#[derive(Default)]
pub struct CondensedReapplyQueueIterator {
    pub concept_negation: bool,
}
/// Placeholder for `CReapplyQueue*` (returned by `getRoleReapplyQueue`).
pub struct ReapplyQueuePtr;
/// Placeholder for `CCondensedReapplyQueue*` (returned by `getConceptReapplyQueue`).
pub struct CondensedReapplyQueuePtr;

// ===========================================================================
// Empty-iterator `hasNext`/`next` surface for the PN-3 placeholder iterators.
//
// KONCLUDE-PORT-NOTE[api]: the C++ `getSuccessorRoleIterator` /
// `getDisjointSuccessorRoleIterator` (and the sibling role/link/successor
// iterators) return an iterator over the node's `mUseSuccRoleHash` /
// `mUseDisjointSuccRoleHash` process-hash. Those backends now exist as
// `ProcessContext` arena objects, so the arena-threaded `ctx.node_*` accessors
// return the real iterators. The `&self` node methods below cannot resolve an
// arena id by themselves; their fallback branches yield the same
// default-constructed empty iterator that C++ returns when the hash pointer is
// null.
//
// The imported real iterator types port that empty-iterator behaviour faithfully
// and are the types seeded by the context-threaded route once the backing hash is
// present.
// ===========================================================================

impl IndividualProcessNode {
    // ===================================================================
    // Lazy label / hash / queue getters (`create`-on-demand).
    // ===================================================================

    /// Port of `CIndividualProcessNode::setReapplyConceptLabelSet`.
    pub fn set_reapply_concept_label_set(&mut self, reapply_con_set: LabelSetId) -> &mut Self {
        self.use_reapply_con_label_set = reapply_con_set;
        self.reapply_con_label_set = reapply_con_set;
        self.prev_reapply_con_label_set = reapply_con_set;
        self
    }

    /// Port of `CIndividualProcessNode::getReapplyConceptLabelSet`.
    // superseded by ctx.node_reapply_concept_label_set (W3b context-threaded lazy-getter):
    // the create branch's arena allocation cannot run from `&mut self`; the un-defer
    // wave calls `ctx.node_reapply_concept_label_set(node)` for `create == true`.
    pub fn get_reapply_concept_label_set(&mut self, create: bool) -> LabelSetId {
        if create && self.reapply_con_label_set.is_none() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_reapply_concept_label_set_in_context`.
        }
        self.use_reapply_con_label_set
    }

    /// Context-threaded port of `CIndividualProcessNode::getReapplyConceptLabelSet`.
    pub fn get_reapply_concept_label_set_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        create: bool,
    ) -> LabelSetId {
        if create {
            process_context.node_reapply_concept_label_set(node)
        } else {
            process_context.node(node).use_reapply_con_label_set
        }
    }

    /// Port of `CIndividualProcessNode::getConnectionSuccessorSet`.
    // superseded by ctx.node_connection_successor_set (W3b context-threaded lazy-getter).
    pub fn get_connection_successor_set(&mut self, create: bool) -> ConnSuccSetId {
        if create && self.conn_succ_set.is_none() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_connection_successor_set_in_context`.
        }
        self.use_conn_succ_set
    }

    /// Context-threaded port of `CIndividualProcessNode::getConnectionSuccessorSet`.
    pub fn get_connection_successor_set_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        create: bool,
    ) -> ConnSuccSetId {
        if create {
            process_context.node_connection_successor_set(node)
        } else {
            process_context.node_connection_successor_set_existing(node)
        }
    }

    /// Port of `CIndividualProcessNode::getReapplyRoleSuccessorHash`.
    pub fn get_reapply_role_successor_hash(&mut self, create: bool) -> RoleSuccHashId {
        if create && self.reapply_role_succ_hash.is_none() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_reapply_role_successor_hash_in_context`.
        }
        self.use_reapply_role_succ_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getReapplyRoleSuccessorHash`.
    pub fn get_reapply_role_successor_hash_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        create: bool,
    ) -> RoleSuccHashId {
        if create {
            process_context.node_reapply_role_successor_hash(node)
        } else {
            process_context.node_reapply_role_successor_hash_existing(node)
        }
    }

    /// Port of `CIndividualProcessNode::getConceptPropagationBindingSetHash`.
    // superseded by ctx.node_concept_propagation_binding_set_hash (W3b context-threaded lazy-getter).
    pub fn get_concept_propagation_binding_set_hash(
        &mut self,
        create: bool,
    ) -> ConceptPropBindingSetHashId {
        if create && self.concept_prop_binding_set_hash.is_none() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_concept_propagation_binding_set_hash_in_context`.
        }
        self.use_concept_prop_binding_set_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getConceptPropagationBindingSetHash`.
    pub fn get_concept_propagation_binding_set_hash_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        create: bool,
    ) -> ConceptPropBindingSetHashId {
        if create {
            process_context.node_concept_propagation_binding_set_hash(node)
        } else {
            process_context.node(node).use_concept_prop_binding_set_hash
        }
    }

    /// Port of `CIndividualProcessNode::getConceptVariableBindingPathSetHash`.
    // superseded by ctx.node_concept_variable_binding_path_set_hash (W3b context-threaded lazy-getter).
    pub fn get_concept_variable_binding_path_set_hash(
        &mut self,
        create: bool,
    ) -> ConceptVarBindPathSetHashId {
        if create && self.concept_var_bind_path_set_hash.is_none() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_concept_variable_binding_path_set_hash_in_context`.
        }
        self.use_concept_var_bind_path_set_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getConceptVariableBindingPathSetHash`.
    pub fn get_concept_variable_binding_path_set_hash_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        create: bool,
    ) -> ConceptVarBindPathSetHashId {
        if create {
            process_context.node_concept_variable_binding_path_set_hash(node)
        } else {
            process_context
                .node(node)
                .use_concept_var_bind_path_set_hash
        }
    }

    /// Port of `CIndividualProcessNode::getConceptRepresentativePropagationSetHash`.
    pub fn get_concept_representative_propagation_set_hash(
        &mut self,
        create: bool,
    ) -> ConceptRepPropSetHashId {
        if create && self.concept_rep_prop_set_hash.is_none() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_concept_representative_propagation_set_hash_in_context`.
        }
        self.use_concept_rep_prop_set_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getConceptRepresentativePropagationSetHash`.
    pub fn get_concept_representative_propagation_set_hash_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        create: bool,
    ) -> ConceptRepPropSetHashId {
        if create {
            process_context.node_concept_representative_propagation_set_hash(node)
        } else {
            process_context.node(node).use_concept_rep_prop_set_hash
        }
    }

    // ===================================================================
    // Role-successor reads (over the reapply role-successor hash).
    // ===================================================================

    /// Port of `CIndividualProcessNode::getRoleSuccessorLinkIterator`.
    pub fn get_role_successor_link_iterator(&self, _role: RoleId) -> RoleSuccessorLinkIterator {
        if self.use_reapply_role_succ_hash.is_some() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `ProcessContext::node_role_successor_link_iterator`.
            RoleSuccessorLinkIterator::empty()
        } else {
            RoleSuccessorLinkIterator::empty()
        }
    }

    /// Port of `CIndividualProcessNode::getRoleSuccessorCount`.
    pub fn get_role_successor_count(&self, _role: RoleId) -> Cint64 {
        if self.use_reapply_role_succ_hash.is_some() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `ProcessContext::node_role_successor_count`.
            0
        } else {
            0
        }
    }

    /// Port of `CIndividualProcessNode::getRoleSuccessorHistoryLinkIterator`.
    pub fn get_role_successor_history_link_iterator(
        &self,
        _role: RoleId,
        _last_link: EdgeId,
    ) -> RoleSuccessorLinkIterator {
        if self.use_reapply_role_succ_hash.is_some() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `ProcessContext::node_role_successor_history_link_iterator`.
            RoleSuccessorLinkIterator::empty()
        } else {
            RoleSuccessorLinkIterator::empty()
        }
    }

    /// Port of `CIndividualProcessNode::hasRoleSuccessorToIndividual(CRole*, cint64, bool)`.
    pub fn has_role_successor_to_individual_id(
        &self,
        _role: RoleId,
        _destination_indi_id: Cint64,
        _locateable: bool,
    ) -> bool {
        if self.use_reapply_role_succ_hash.is_some() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `ProcessContext::node_has_role_successor_to_individual_id`.
            return false;
        }
        false
    }

    /// Port of `CIndividualProcessNode::hasRoleSuccessorToIndividual(CRole*, CIndividualProcessNode*, bool)`.
    pub fn has_role_successor_to_individual(
        &self,
        role: RoleId,
        des_indi: &IndividualProcessNode,
        locateable: bool,
    ) -> bool {
        self.has_role_successor_to_individual_id(role, des_indi.individual_node_id(), locateable)
    }

    /// Port of `CIndividualProcessNode::getRoleSuccessorToIndividualLink(CRole*, cint64, bool)`.
    pub fn get_role_successor_to_individual_link_id(
        &self,
        _role: RoleId,
        _destination_indi_id: Cint64,
        _locateable: bool,
    ) -> EdgeId {
        if self.use_reapply_role_succ_hash.is_some() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `ProcessContext::node_get_role_successor_to_individual_link_id`.
            return EdgeId::NONE;
        }
        EdgeId::NONE
    }

    /// Port of `CIndividualProcessNode::getRoleSuccessorToIndividualLink(CRole*, CIndividualProcessNode*, bool)`.
    pub fn get_role_successor_to_individual_link(
        &self,
        role: RoleId,
        des_indi: &IndividualProcessNode,
        locateable: bool,
    ) -> EdgeId {
        self.get_role_successor_to_individual_link_id(
            role,
            des_indi.individual_node_id(),
            locateable,
        )
    }

    // ===================================================================
    // Negation-disjoint reads / topology (over the disjoint-successor-role hash).
    // ===================================================================

    /// Port of `CIndividualProcessNode::hasNegationDisjointToIndividual(CRole*, cint64)`.
    pub fn has_negation_disjoint_to_individual_id(
        &self,
        _role: RoleId,
        _destination_indi_id: Cint64,
    ) -> bool {
        if self.use_disjoint_succ_role_hash.is_some() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `has_negation_disjoint_to_individual_id_in_context`.
            return false;
        }
        false
    }

    /// Context-threaded port of `CIndividualProcessNode::hasNegationDisjointToIndividual(CRole*, cint64)`.
    pub fn has_negation_disjoint_to_individual_id_in_context(
        process_context: &ProcessContext,
        node: NodeId,
        role: RoleId,
        destination_indi_id: Cint64,
    ) -> bool {
        process_context.node_has_negation_disjoint_to_individual_id(node, role, destination_indi_id)
    }

    /// Context-threaded port of `CIndividualProcessNode::hasNegationDisjointToIndividual(CRole*, CIndividualProcessNode*)`.
    pub fn has_negation_disjoint_to_individual_in_context(
        process_context: &ProcessContext,
        node: NodeId,
        des_indi: NodeId,
        role: RoleId,
    ) -> bool {
        let destination_indi_id = process_context.node(des_indi).individual_node_id();
        Self::has_negation_disjoint_to_individual_id_in_context(
            process_context,
            node,
            role,
            destination_indi_id,
        )
    }

    /// Port of `CIndividualProcessNode::hasNegationDisjointToIndividual(CRole*, CIndividualProcessNode*)`.
    pub fn has_negation_disjoint_to_individual(
        &self,
        role: RoleId,
        des_indi: &IndividualProcessNode,
    ) -> bool {
        self.has_negation_disjoint_to_individual_id(role, des_indi.individual_node_id())
    }

    /// Port of `CIndividualProcessNode::hasDisjointRoleConnections`.
    pub fn has_disjoint_role_connections(&self) -> bool {
        self.disjoint_role_connections
    }

    /// Port of `CIndividualProcessNode::setDisjointRoleConnections`.
    pub fn set_disjoint_role_connections(&mut self, disjoint_role_connections: bool) -> &mut Self {
        self.disjoint_role_connections = disjoint_role_connections;
        self
    }

    /// Port of `CIndividualProcessNode::getDisjointSuccessorRoleHash`.
    // superseded by ctx.node_disjoint_successor_role_hash (W3b context-threaded lazy-getter).
    pub fn get_disjoint_successor_role_hash(&mut self, create: bool) -> DisjointSuccRoleHashId {
        if create && self.disjoint_succ_role_hash.is_none() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_disjoint_successor_role_hash_in_context`.
        }
        self.use_disjoint_succ_role_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getDisjointSuccessorRoleHash`.
    pub fn get_disjoint_successor_role_hash_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        create: bool,
    ) -> DisjointSuccRoleHashId {
        if create {
            process_context.node_disjoint_successor_role_hash(node)
        } else {
            process_context.node(node).use_disjoint_succ_role_hash
        }
    }

    /// Port of `CIndividualProcessNode::installDisjointLink`.
    pub fn install_disjoint_link(&mut self, _link: DisjointEdgeId) -> &mut Self {
        if self.disjoint_succ_role_hash.is_none() {
            self.get_disjoint_successor_role_hash(true);
        }
        // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
        // `install_disjoint_link_in_context`.
        self
    }

    /// Context-threaded port of `CIndividualProcessNode::installDisjointLink`.
    pub fn install_disjoint_link_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        link: DisjointEdgeId,
    ) {
        process_context.node_install_disjoint_link(node, link);
    }

    /// Port of `CIndividualProcessNode::removeDisjointLinks`.
    pub fn remove_disjoint_links(&mut self, _succ_indi_id: Cint64) -> &mut Self {
        if self.use_disjoint_succ_role_hash.is_some() {
            if self.disjoint_succ_role_hash.is_none() {
                self.get_disjoint_successor_role_hash(true);
            }
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `remove_disjoint_links_in_context`.
        }
        self
    }

    /// Context-threaded port of `CIndividualProcessNode::removeDisjointLinks`.
    pub fn remove_disjoint_links_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        succ_indi_id: Cint64,
    ) {
        process_context.node_remove_disjoint_links(node, succ_indi_id);
    }

    /// Port of `CIndividualProcessNode::getDisjointSuccessorRoleIterator(cint64)`.
    // superseded by ctx.node_disjoint_successor_role_iterator (u15 context-threaded;
    // seeds the real distinct::DisjointSuccessorRoleIterator).
    pub fn get_disjoint_successor_role_iterator_id(
        &self,
        _succ_indi_id: Cint64,
    ) -> DisjointSuccessorRoleIterator {
        if self.use_disjoint_succ_role_hash.is_some() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_disjoint_successor_role_iterator_id_in_context`.
            DisjointSuccessorRoleIterator::new()
        } else {
            DisjointSuccessorRoleIterator::new()
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getDisjointSuccessorRoleIterator(cint64)`.
    pub fn get_disjoint_successor_role_iterator_id_in_context(
        process_context: &ProcessContext,
        node: NodeId,
        succ_indi_id: Cint64,
    ) -> DisjointSuccessorRoleIterator {
        process_context.node_disjoint_successor_role_iterator(node, succ_indi_id)
    }

    /// Context-threaded port of `CIndividualProcessNode::getDisjointSuccessorRoleIterator(CIndividualProcessNode*)`.
    pub fn get_disjoint_successor_role_iterator_in_context(
        process_context: &ProcessContext,
        node: NodeId,
        indi_node: NodeId,
    ) -> DisjointSuccessorRoleIterator {
        let succ_indi_id = process_context.node(indi_node).individual_node_id();
        Self::get_disjoint_successor_role_iterator_id_in_context(
            process_context,
            node,
            succ_indi_id,
        )
    }

    /// Port of `CIndividualProcessNode::getDisjointSuccessorRoleIterator(CIndividualProcessNode*)`.
    pub fn get_disjoint_successor_role_iterator(
        &self,
        indi_node: &IndividualProcessNode,
    ) -> DisjointSuccessorRoleIterator {
        self.get_disjoint_successor_role_iterator_id(indi_node.individual_node_id())
    }

    /// Port of `CIndividualProcessNode::getRoleIterator`.
    pub fn get_role_iterator(&self) -> RoleSuccessorIterator {
        if self.use_reapply_role_succ_hash.is_none() {
            RoleSuccessorIterator::empty()
        } else {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `ProcessContext::node_role_iterator`.
            RoleSuccessorIterator::empty()
        }
    }

    // ===================================================================
    // Successor-role hash + connection topology.
    // ===================================================================

    /// Port of `CIndividualProcessNode::getSuccessorRoleHash`.
    pub fn get_successor_role_hash(&mut self, create: bool) -> SuccRoleHashId {
        if create && self.succ_role_hash.is_none() {
            // KONCLUDE-PORT-NOTE[ownership]: the faithful arena-backed route is
            // `get_successor_role_hash_in_context`; this `&mut self` compatibility
            // method cannot allocate the context-owned successor-role hash.
        }
        self.use_succ_role_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getSuccessorRoleHash`.
    pub fn get_successor_role_hash_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        create: bool,
    ) -> SuccRoleHashId {
        if create {
            process_context.node_successor_role_hash(node)
        } else {
            process_context.node(node).use_succ_role_hash
        }
    }

    /// Port of `CIndividualProcessNode::getSuccessorRoleIterator(CIndividualProcessNode*)`.
    pub fn get_successor_role_iterator(
        &self,
        indi_node: &IndividualProcessNode,
    ) -> SuccessorRoleIterator {
        self.get_successor_role_iterator_id(indi_node.individual_node_id())
    }

    /// Port of `CIndividualProcessNode::getSuccessorRoleIterator(cint64)`.
    // superseded by ctx.node_successor_role_iterator (u15 context-threaded; seeds the
    // real succ_role_hash::SuccessorRoleIterator). This `&self` body returns the
    // empty placeholder because it cannot resolve the hash id against the arena.
    pub fn get_successor_role_iterator_id(&self, _indi_id: Cint64) -> SuccessorRoleIterator {
        if self.use_succ_role_hash.is_none() {
            SuccessorRoleIterator::empty()
        } else {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `ProcessContext::node_successor_role_iterator`.
            SuccessorRoleIterator::empty()
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getSuccessorRoleIterator(cint64)`.
    pub fn get_successor_role_iterator_id_in_context(
        process_context: &ProcessContext,
        node: NodeId,
        indi_id: Cint64,
    ) -> SuccessorRoleIterator {
        process_context.node_successor_role_iterator(node, indi_id)
    }

    /// Context-threaded port of `CIndividualProcessNode::getSuccessorRoleIterator(CIndividualProcessNode*)`.
    pub fn get_successor_role_iterator_in_context(
        process_context: &ProcessContext,
        node: NodeId,
        indi_node: NodeId,
    ) -> SuccessorRoleIterator {
        let indi_id = process_context.node(indi_node).individual_node_id();
        Self::get_successor_role_iterator_id_in_context(process_context, node, indi_id)
    }

    /// Port of `CIndividualProcessNode::hasSuccessorIndividualNode(CIndividualProcessNode*)`.
    pub fn has_successor_individual_node(&self, indi_node: &IndividualProcessNode) -> bool {
        self.has_successor_individual_node_id(indi_node.individual_node_id())
    }

    /// Port of `CIndividualProcessNode::hasSuccessorIndividualNode(cint64)`.
    pub fn has_successor_individual_node_id(&self, _indi_id: Cint64) -> bool {
        if self.use_succ_role_hash.is_none() {
            false
        } else {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `has_successor_individual_node_id_in_context`.
            false
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::hasSuccessorIndividualNode(cint64)`.
    pub fn has_successor_individual_node_id_in_context(
        process_context: &ProcessContext,
        node: NodeId,
        indi_id: Cint64,
    ) -> bool {
        process_context.node_has_successor_individual_node(node, indi_id)
    }

    /// Context-threaded port of `CIndividualProcessNode::hasSuccessorIndividualNode(CIndividualProcessNode*)`.
    pub fn has_successor_individual_node_in_context(
        process_context: &ProcessContext,
        node: NodeId,
        indi_node: NodeId,
    ) -> bool {
        let indi_id = process_context.node(indi_node).individual_node_id();
        Self::has_successor_individual_node_id_in_context(process_context, node, indi_id)
    }

    // ===================================================================
    // Concept-processing queue + reapply queues / iterators.
    // ===================================================================

    /// Port of `CIndividualProcessNode::getConceptProcessingQueue`.
    pub fn get_concept_processing_queue(&mut self, create: bool) -> ConceptProcessingQueueId {
        if create && self.concept_processing_queue.is_none() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_concept_processing_queue_in_context`.
        }
        self.use_concept_processing_queue
    }

    /// Context-threaded port of `CIndividualProcessNode::getConceptProcessingQueue`.
    pub fn get_concept_processing_queue_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        create: bool,
    ) -> ConceptProcessingQueueId {
        process_context.node_concept_processing_queue(node, create)
    }

    /// Port of `CIndividualProcessNode::getRoleReapplyQueue`.
    pub fn get_role_reapply_queue(
        &mut self,
        _role: RoleId,
        create: bool,
    ) -> Option<ReapplyQueuePtr> {
        let reapply_queue: Option<ReapplyQueuePtr> = None;
        if create && self.reapply_role_succ_hash.is_none() {
            self.get_reapply_role_successor_hash(true);
        }
        if self.use_reapply_role_succ_hash.is_some() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `ProcessContext::node_add_role_reapply_concept_descriptor` /
            // `node_role_reapply_iterator`.
        }
        reapply_queue
    }

    /// Port of `CIndividualProcessNode::getRoleReapplyIterator`.
    pub fn get_role_reapply_iterator(
        &mut self,
        _role: RoleId,
        clear_dynamic_reapply_queue: bool,
    ) -> ReapplyQueueIterator {
        if clear_dynamic_reapply_queue && self.reapply_role_succ_hash.is_none() {
            self.get_reapply_role_successor_hash(true);
        }
        if self.use_reapply_role_succ_hash.is_some() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_role_reapply_iterator_in_context`.
            ReapplyQueueIterator::empty()
        } else {
            // CReapplyQueueIterator(nullptr,nullptr)
            ReapplyQueueIterator::empty()
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getRoleReapplyIterator`.
    pub fn get_role_reapply_iterator_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        role: RoleId,
        clear_dynamic_reapply_queue: bool,
    ) -> ReapplyQueueIterator {
        if clear_dynamic_reapply_queue
            && process_context.node(node).reapply_role_succ_hash.is_none()
        {
            process_context.node_reapply_role_successor_hash(node);
        }
        process_context.node_role_reapply_iterator(node, role, clear_dynamic_reapply_queue)
    }

    /// Port of `CIndividualProcessNode::getConceptReapplyQueue`.
    pub fn get_concept_reapply_queue(
        &mut self,
        _concept: ConceptId,
        _concept_negation: bool,
        create: bool,
    ) -> Option<CondensedReapplyQueuePtr> {
        let reapply_queue: Option<CondensedReapplyQueuePtr> = None;
        if create && self.reapply_con_label_set.is_none() {
            self.get_reapply_concept_label_set(true);
        }
        if self.use_reapply_con_label_set.is_some() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `ProcessContext::node_add_concept_reapply_concept_descriptor` /
            // `node_concept_reapply_iterator`.
        }
        reapply_queue
    }

    /// Port of `CIndividualProcessNode::getConceptReapplyIterator`.
    pub fn get_concept_reapply_iterator(
        &mut self,
        _concept: ConceptId,
        concept_negation: bool,
        clear_dynamic_reapply_queue: bool,
    ) -> CondensedReapplyQueueIterator {
        if clear_dynamic_reapply_queue && self.reapply_con_label_set.is_none() {
            self.get_reapply_concept_label_set(true);
        }
        if self.use_reapply_con_label_set.is_some() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_concept_reapply_iterator_in_context`.
            CondensedReapplyQueueIterator { concept_negation }
        } else {
            // CCondensedReapplyQueueIterator(nullptr,conceptNegation)
            CondensedReapplyQueueIterator { concept_negation }
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getConceptReapplyIterator`.
    pub fn get_concept_reapply_iterator_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        concept: ConceptId,
        concept_negation: bool,
        clear_dynamic_reapply_queue: bool,
    ) -> super::reapply_sat::CondensedReapplyQueueIterator {
        if clear_dynamic_reapply_queue && process_context.node(node).reapply_con_label_set.is_none()
        {
            process_context.node_reapply_concept_label_set(node);
        }
        process_context.node_concept_reapply_iterator(
            node,
            concept,
            concept_negation,
            clear_dynamic_reapply_queue,
        )
    }

    /// Port of `CIndividualProcessNode::getDistinctHash`.
    // superseded by ctx.node_distinct_hash (W3b context-threaded lazy-getter).
    pub fn get_distinct_hash(&mut self, create: bool) -> DistinctHashId {
        if create && self.distinct_hash.is_none() {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `get_distinct_hash_in_context`.
        }
        self.use_distinct_hash
    }

    /// Context-threaded port of `CIndividualProcessNode::getDistinctHash`.
    pub fn get_distinct_hash_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        create: bool,
    ) -> DistinctHashId {
        if create {
            process_context.node_distinct_hash(node)
        } else {
            process_context.node_distinct_hash_existing(node)
        }
    }

    // ===================================================================
    // Blocked-individuals linker chain.
    // KONCLUDE-PORT-NOTE[ownership]: the C++ `CXLinker<CIndividualProcessNode*>*`
    // intrusive chain is modelled as the owned `Vec<NodeId>` field
    // `blocked_individuals_linker` (per `substrate.rs`).
    // ===================================================================

    /// Port of `CIndividualProcessNode::addBlockedIndividualsLinker`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `linker->append(mBlockedIndividualsLinker)`
    /// makes `linker` the new head and chains the existing list onto its tail.
    /// With `Vec`s that is `[linker..., old...]`.
    pub fn add_blocked_individuals_linker(&mut self, linker: Vec<NodeId>) -> &mut Self {
        if !linker.is_empty() {
            let mut new_linker = linker;
            new_linker.extend(self.blocked_individuals_linker.iter().copied());
            self.blocked_individuals_linker = new_linker;
        }
        self
    }

    /// Port of `CIndividualProcessNode::setBlockedIndividualsLinker`.
    pub fn set_blocked_individuals_linker(&mut self, linker: Vec<NodeId>) -> &mut Self {
        self.blocked_individuals_linker = linker;
        self
    }

    /// Port of `CIndividualProcessNode::getBlockedIndividualsLinker`.
    pub fn get_blocked_individuals_linker(&self) -> &[NodeId] {
        &self.blocked_individuals_linker
    }

    /// Port of `CIndividualProcessNode::hasBlockedIndividualsLinker`.
    pub fn has_blocked_individuals_linker(&self) -> bool {
        !self.blocked_individuals_linker.is_empty()
    }

    /// Port of `CIndividualProcessNode::clearBlockedIndividualsLinker`.
    pub fn clear_blocked_individuals_linker(&mut self) -> &mut Self {
        self.blocked_individuals_linker.clear();
        self
    }

    // ===================================================================
    // Ancestor link + topology install/remove.
    // ===================================================================

    /// Port of `CIndividualProcessNode::getAncestorLink`.
    pub fn get_ancestor_link(&self) -> EdgeId {
        self.ancestor_link
    }

    /// Port of `CIndividualProcessNode::setAncestorLink`.
    pub fn set_ancestor_link(&mut self, link: EdgeId) -> &mut Self {
        self.ancestor_link = link;
        self
    }

    /// Port of `CIndividualProcessNode::isIndividualAncestor`.
    pub fn is_individual_ancestor(&self, _individual: &IndividualProcessNode) -> bool {
        if self.ancestor_link.is_some() {
            // KONCLUDE-PORT-NOTE[api]: exact edge-arena lookup is
            // `is_individual_ancestor_in_context`. This compatibility accessor
            // cannot dereference `mAncestorLink` without the process context.
            return false;
        }
        false
    }

    /// Context-threaded port of `CIndividualProcessNode::isIndividualAncestor`.
    pub fn is_individual_ancestor_in_context(
        process_context: &ProcessContext,
        node: NodeId,
        individual: NodeId,
    ) -> bool {
        if node.is_none() || individual.is_none() {
            return false;
        }
        let ancestor_link = process_context.node(node).ancestor_link;
        if ancestor_link.is_none() {
            return false;
        }
        let source = process_context.edge(ancestor_link).get_source_individual();
        if source.is_none() {
            return false;
        }
        process_context.node(source).individual_node_id()
            == process_context.node(individual).individual_node_id()
    }

    /// Port of `CIndividualProcessNode::hasIndividualAncestor`.
    pub fn has_individual_ancestor(&self) -> bool {
        self.ancestor_link.is_some()
    }

    // NOTE: `isBlockableIndividual`, `isNominalIndividualNode`,
    // `getNominalIndividual`, `setNominalIndividual` (`.cpp` 1193-1209) are already
    // ported in `node.rs` (`is_blockable_individual` / `is_nominal_individual_node`
    // / `nominal_individual` / `set_nominal_individual`); not re-ported here.

    /// Port of `CIndividualProcessNode::getLastAddedRoleLink`.
    pub fn get_last_added_role_link(&self) -> EdgeId {
        self.last_added_link
    }

    /// Port of `CIndividualProcessNode::installIndividualLink`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `reapplyQueueIt` is the `CReapplyQueueIterator*`
    /// the C++ threads into `insertRoleSuccessorLink`; ported as a by-value
    /// placeholder until RS-1's insert lands.
    pub fn install_individual_link(
        &mut self,
        link: EdgeId,
        _reapply_queue_it: ReapplyQueueIterator,
    ) -> Cint64 {
        if self.reapply_role_succ_hash.is_none() {
            self.get_reapply_role_successor_hash(true);
        }
        if self.succ_role_hash.is_none() {
            self.get_successor_role_hash(true);
        }
        // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
        // `install_individual_link_in_context`; this compatibility method cannot
        // dereference context-owned role/successor hashes.
        let link_count: Cint64 = 0;
        self.last_added_link = link;
        link_count
    }

    /// Context-threaded port of `CIndividualProcessNode::installIndividualLink`.
    pub fn install_individual_link_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        link: EdgeId,
        reapply_queue_it: &mut ReapplyQueueIterator,
    ) -> Cint64 {
        process_context.node_install_individual_link(node, link, reapply_queue_it)
    }

    /// Port of `CIndividualProcessNode::removeIndividualLink`.
    pub fn remove_individual_link(&mut self, _link: EdgeId) -> &mut Self {
        if self.reapply_role_succ_hash.is_none() {
            self.get_reapply_role_successor_hash(true);
        }
        // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
        // `remove_individual_link_in_context`.
        self
    }

    /// Context-threaded port of `CIndividualProcessNode::removeIndividualLink`.
    pub fn remove_individual_link_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        link: EdgeId,
    ) {
        process_context.node_remove_individual_link(node, link);
    }

    /// Port of `CIndividualProcessNode::removeIndividualConnection`.
    pub fn remove_individual_connection(&mut self, _indi: &IndividualProcessNode) -> &mut Self {
        if self.succ_role_hash.is_none() {
            self.get_successor_role_hash(true);
        }
        if self.use_conn_succ_set.is_some() {
            if self.conn_succ_set.is_none() {
                self.get_connection_successor_set(true);
            }
        }
        // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
        // `remove_individual_connection_in_context`.
        self
    }

    /// Context-threaded port of `CIndividualProcessNode::removeIndividualConnection`.
    pub fn remove_individual_connection_in_context(
        process_context: &mut ProcessContext,
        node: NodeId,
        indi: NodeId,
    ) {
        process_context.node_remove_individual_connection(node, indi);
    }

    /// Port of `CIndividualProcessNode::getSuccessorIterator`.
    // superseded by ctx.node_successor_iterator (u15 context-threaded; seeds the real
    // succ_role_hash::SuccessorIterator).
    pub fn get_successor_iterator(&self) -> SuccessorIterator {
        if self.use_succ_role_hash.is_none() {
            return SuccessorIterator::empty();
        }
        // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
        // `ProcessContext::node_successor_iterator`.
        SuccessorIterator::empty()
    }

    /// Port of `CIndividualProcessNode::getConnectionSuccessorIterator`.
    pub fn get_connection_successor_iterator(&self) -> ConnectionSuccessorSetIterator {
        if self.use_conn_succ_set.is_none() {
            ConnectionSuccessorSetIterator::from_single(Cint64::MIN)
        } else {
            // KONCLUDE-PORT-NOTE[ownership]: faithful arena-backed route is
            // `ProcessContext::node_connection_successor_iterator`.
            ConnectionSuccessorSetIterator::from_single(Cint64::MIN)
        }
    }

    /// Context-threaded port of `CIndividualProcessNode::getConnectionSuccessorIterator`.
    pub fn get_connection_successor_iterator_in_context(
        process_context: &ProcessContext,
        node: NodeId,
    ) -> ConnectionSuccessorSetIterator {
        process_context.node_connection_successor_iterator(node)
    }
}

#[cfg(test)]
mod tests {
    use super::super::edge::{DisjointEdge, IndividualLinkEdge};
    use super::super::TrackPointId;
    use super::*;

    #[test]
    fn connection_successor_iterator_without_hash_is_empty() {
        let node = IndividualProcessNode::default();

        let mut it = node.get_connection_successor_iterator();

        assert!(!it.has_next());
        assert_eq!(it.next_successor_connection_id(true), 0);
    }

    #[test]
    fn connection_successor_iterator_with_hash_uses_context_threaded_fallback() {
        let mut node = IndividualProcessNode::default();
        node.use_conn_succ_set = ConnSuccSetId::new(7);

        let mut it = node.get_connection_successor_iterator();

        assert!(!it.has_next());
        assert_eq!(it.next_successor_connection_id(true), 0);
    }

    #[test]
    fn pn3_connection_successor_iterator_in_context_empty_is_empty() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::default());

        let mut it =
            IndividualProcessNode::get_connection_successor_iterator_in_context(&ctx, node);

        assert!(!it.has_next());
        assert_eq!(it.next_successor_connection_id(true), 0);
    }

    #[test]
    fn pn3_connection_successor_iterator_in_context_returns_single_ancestor_id() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::default());
        let conn_set =
            IndividualProcessNode::get_connection_successor_set_in_context(&mut ctx, node, true);
        ctx.conn_succ_set_mut(conn_set)
            .insert_connection_successor(17);

        let mut it =
            IndividualProcessNode::get_connection_successor_iterator_in_context(&ctx, node);

        assert!(it.has_next());
        assert_eq!(it.next_successor_connection_id(true), 17);
        assert!(!it.has_next());
    }

    #[test]
    fn pn3_connection_successor_iterator_in_context_returns_set_ids() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::default());
        let conn_set =
            IndividualProcessNode::get_connection_successor_set_in_context(&mut ctx, node, true);
        ctx.conn_succ_set_mut(conn_set)
            .insert_connection_successor(17)
            .insert_connection_successor(23);

        let mut it =
            IndividualProcessNode::get_connection_successor_iterator_in_context(&ctx, node);
        let mut ids = Vec::new();
        while it.has_next() {
            ids.push(it.next_successor_connection_id(true));
        }
        ids.sort_unstable();

        assert_eq!(ids, vec![17, 23]);
    }

    #[test]
    fn pn3_successor_role_hash_in_context_allocates_once() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::default());

        assert!(
            IndividualProcessNode::get_successor_role_hash_in_context(&mut ctx, node, false)
                .is_none()
        );
        let hash = IndividualProcessNode::get_successor_role_hash_in_context(&mut ctx, node, true);
        assert!(hash.is_some());
        assert_eq!(ctx.node(node).succ_role_hash, hash);
        assert_eq!(ctx.node(node).use_succ_role_hash, hash);
        assert_eq!(
            IndividualProcessNode::get_successor_role_hash_in_context(&mut ctx, node, true),
            hash
        );
    }

    #[test]
    fn pn3_disjoint_successor_role_hash_in_context_allocates_once() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::default());

        assert!(
            IndividualProcessNode::get_disjoint_successor_role_hash_in_context(
                &mut ctx, node, false
            )
            .is_none()
        );
        let hash = IndividualProcessNode::get_disjoint_successor_role_hash_in_context(
            &mut ctx, node, true,
        );
        assert!(hash.is_some());
        assert_eq!(ctx.node(node).disjoint_succ_role_hash, hash);
        assert_eq!(ctx.node(node).use_disjoint_succ_role_hash, hash);
        assert_eq!(
            IndividualProcessNode::get_disjoint_successor_role_hash_in_context(
                &mut ctx, node, true,
            ),
            hash
        );
    }

    #[test]
    fn pn3_individual_ancestor_in_context_checks_edge_source_individual_id() {
        let mut ctx = ProcessContext::new();
        let source = ctx.alloc_node(IndividualProcessNode::default());
        let same_source_id = ctx.alloc_node(IndividualProcessNode::default());
        let other = ctx.alloc_node(IndividualProcessNode::default());
        let child = ctx.alloc_node(IndividualProcessNode::default());
        let role = RoleId::new(29);
        ctx.node_mut(source).set_individual_node_id(17);
        ctx.node_mut(same_source_id).set_individual_node_id(17);
        ctx.node_mut(other).set_individual_node_id(19);
        ctx.node_mut(child).set_individual_node_id(23);

        let mut edge = IndividualLinkEdge::new();
        edge.init_individual_link_edge(child, source, child, role, TrackPointId::NONE);
        let edge = ctx.alloc_edge(edge);
        ctx.node_mut(child).set_ancestor_link(edge);

        assert!(IndividualProcessNode::is_individual_ancestor_in_context(
            &ctx, child, source
        ));
        assert!(IndividualProcessNode::is_individual_ancestor_in_context(
            &ctx,
            child,
            same_source_id
        ));
        assert!(!IndividualProcessNode::is_individual_ancestor_in_context(
            &ctx, child, other
        ));
    }

    #[test]
    fn pn3_context_threaded_lazy_getters_allocate_once() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::default());

        assert!(
            IndividualProcessNode::get_reapply_concept_label_set_in_context(&mut ctx, node, false)
                .is_none()
        );
        let label_set =
            IndividualProcessNode::get_reapply_concept_label_set_in_context(&mut ctx, node, true);
        assert!(label_set.is_some());
        assert_eq!(ctx.node(node).reapply_con_label_set, label_set);
        assert_eq!(ctx.node(node).use_reapply_con_label_set, label_set);
        assert_eq!(
            IndividualProcessNode::get_reapply_concept_label_set_in_context(&mut ctx, node, true),
            label_set
        );

        assert!(
            IndividualProcessNode::get_connection_successor_set_in_context(&mut ctx, node, false)
                .is_none()
        );
        let conn_set =
            IndividualProcessNode::get_connection_successor_set_in_context(&mut ctx, node, true);
        assert!(conn_set.is_some());
        assert_eq!(ctx.node(node).conn_succ_set, conn_set);
        assert_eq!(ctx.node(node).use_conn_succ_set, conn_set);
        assert_eq!(
            IndividualProcessNode::get_connection_successor_set_in_context(&mut ctx, node, true),
            conn_set
        );

        assert!(
            IndividualProcessNode::get_reapply_role_successor_hash_in_context(
                &mut ctx, node, false
            )
            .is_none()
        );
        let role_hash =
            IndividualProcessNode::get_reapply_role_successor_hash_in_context(&mut ctx, node, true);
        assert!(role_hash.is_some());
        assert_eq!(ctx.node(node).reapply_role_succ_hash, role_hash);
        assert_eq!(ctx.node(node).use_reapply_role_succ_hash, role_hash);
        assert_eq!(
            IndividualProcessNode::get_reapply_role_successor_hash_in_context(&mut ctx, node, true),
            role_hash
        );

        assert!(
            IndividualProcessNode::get_concept_propagation_binding_set_hash_in_context(
                &mut ctx, node, false
            )
            .is_none()
        );
        let prop_hash = IndividualProcessNode::get_concept_propagation_binding_set_hash_in_context(
            &mut ctx, node, true,
        );
        assert!(prop_hash.is_some());
        assert_eq!(ctx.node(node).concept_prop_binding_set_hash, prop_hash);
        assert_eq!(ctx.node(node).use_concept_prop_binding_set_hash, prop_hash);

        assert!(
            IndividualProcessNode::get_concept_variable_binding_path_set_hash_in_context(
                &mut ctx, node, false
            )
            .is_none()
        );
        let var_hash = IndividualProcessNode::get_concept_variable_binding_path_set_hash_in_context(
            &mut ctx, node, true,
        );
        assert!(var_hash.is_some());
        assert_eq!(ctx.node(node).concept_var_bind_path_set_hash, var_hash);
        assert_eq!(ctx.node(node).use_concept_var_bind_path_set_hash, var_hash);

        assert!(
            IndividualProcessNode::get_concept_representative_propagation_set_hash_in_context(
                &mut ctx, node, false
            )
            .is_none()
        );
        let rep_hash =
            IndividualProcessNode::get_concept_representative_propagation_set_hash_in_context(
                &mut ctx, node, true,
            );
        assert!(rep_hash.is_some());
        assert_eq!(ctx.node(node).concept_rep_prop_set_hash, rep_hash);
        assert_eq!(ctx.node(node).use_concept_rep_prop_set_hash, rep_hash);

        assert!(
            IndividualProcessNode::get_concept_processing_queue_in_context(&mut ctx, node, false)
                .is_none()
        );
        let queue =
            IndividualProcessNode::get_concept_processing_queue_in_context(&mut ctx, node, true);
        assert!(queue.is_some());
        assert_eq!(ctx.node(node).concept_processing_queue, queue);
        assert_eq!(ctx.node(node).use_concept_processing_queue, queue);

        assert!(
            IndividualProcessNode::get_distinct_hash_in_context(&mut ctx, node, false).is_none()
        );
        let distinct_hash =
            IndividualProcessNode::get_distinct_hash_in_context(&mut ctx, node, true);
        assert!(distinct_hash.is_some());
        assert_eq!(ctx.node(node).distinct_hash, distinct_hash);
        assert_eq!(ctx.node(node).use_distinct_hash, distinct_hash);
        assert_eq!(
            IndividualProcessNode::get_distinct_hash_in_context(&mut ctx, node, true),
            distinct_hash
        );
    }

    #[test]
    fn pn3_reapply_iterators_create_storage_on_clear() {
        let mut ctx = ProcessContext::new();
        let node = ctx.alloc_node(IndividualProcessNode::default());
        let role = RoleId::new(43);
        let concept = ConceptId::new(47);

        assert!(ctx.node(node).reapply_role_succ_hash.is_none());
        let role_it =
            IndividualProcessNode::get_role_reapply_iterator_in_context(&mut ctx, node, role, true);
        assert!(!role_it.has_next());
        assert!(ctx.node(node).reapply_role_succ_hash.is_some());
        assert_eq!(
            ctx.node(node).reapply_role_succ_hash,
            ctx.node(node).use_reapply_role_succ_hash
        );

        assert!(ctx.node(node).reapply_con_label_set.is_none());
        let concept_it = IndividualProcessNode::get_concept_reapply_iterator_in_context(
            &mut ctx, node, concept, false, true,
        );
        assert!(!concept_it.has_next());
        assert!(ctx.node(node).reapply_con_label_set.is_some());
        assert_eq!(
            ctx.node(node).reapply_con_label_set,
            ctx.node(node).use_reapply_con_label_set
        );
    }

    #[test]
    fn pn3_successor_role_iterator_and_has_in_context_read_hash() {
        let mut ctx = ProcessContext::new();
        let role = RoleId::new(23);
        let source = ctx.alloc_node(IndividualProcessNode::default());
        let dest = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(source).set_individual_node_id(101);
        ctx.node_mut(dest).set_individual_node_id(202);
        let mut edge = IndividualLinkEdge::new();
        edge.init_individual_link_edge(source, source, dest, role, TrackPointId::NONE);
        let edge = ctx.alloc_edge(edge);
        let mut reapply_it = ReapplyQueueIterator::default();

        assert_eq!(
            ctx.node_install_individual_link(source, edge, &mut reapply_it),
            1
        );
        assert!(
            IndividualProcessNode::has_successor_individual_node_id_in_context(&ctx, source, 202)
        );
        assert!(
            IndividualProcessNode::has_successor_individual_node_in_context(&ctx, source, dest)
        );
        assert!(
            !IndividualProcessNode::has_successor_individual_node_id_in_context(&ctx, source, 303)
        );

        let mut it =
            IndividualProcessNode::get_successor_role_iterator_id_in_context(&ctx, source, 202);
        assert_eq!(it.next(true), edge);
        assert_eq!(it.next(true), EdgeId::NONE);

        let mut it =
            IndividualProcessNode::get_successor_role_iterator_in_context(&ctx, source, dest);
        assert_eq!(it.next(true), edge);
        assert_eq!(it.next(true), EdgeId::NONE);
    }

    #[test]
    fn pn3_install_and_remove_individual_link_in_context_follow_topology() {
        let mut ctx = ProcessContext::new();
        let role = RoleId::new(29);
        let source = ctx.alloc_node(IndividualProcessNode::default());
        let dest = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(source).set_individual_node_id(111);
        ctx.node_mut(dest).set_individual_node_id(222);
        let mut edge = IndividualLinkEdge::new();
        edge.init_individual_link_edge(source, source, dest, role, TrackPointId::NONE);
        let edge = ctx.alloc_edge(edge);
        let mut reapply_it = ReapplyQueueIterator::default();

        assert_eq!(
            IndividualProcessNode::install_individual_link_in_context(
                &mut ctx,
                source,
                edge,
                &mut reapply_it,
            ),
            1
        );
        assert_eq!(ctx.node(source).last_added_link, edge);
        assert_eq!(ctx.node_role_successor_count(source, role), 1);
        assert!(
            IndividualProcessNode::has_successor_individual_node_in_context(&ctx, source, dest)
        );

        IndividualProcessNode::remove_individual_link_in_context(&mut ctx, source, edge);
        assert_eq!(ctx.node_role_successor_count(source, role), 0);
        assert!(
            IndividualProcessNode::has_successor_individual_node_in_context(&ctx, source, dest),
            "Konclude removeIndividualLink does not remove the successor-role hash entry"
        );

        IndividualProcessNode::remove_individual_connection_in_context(&mut ctx, source, dest);
        assert!(
            !IndividualProcessNode::has_successor_individual_node_in_context(&ctx, source, dest)
        );
    }

    #[test]
    fn pn3_disjoint_link_wrappers_install_read_iterate_and_remove() {
        let mut ctx = ProcessContext::new();
        let role = RoleId::new(31);
        let source = ctx.alloc_node(IndividualProcessNode::default());
        let dest = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(source).set_individual_node_id(301);
        ctx.node_mut(dest).set_individual_node_id(402);

        assert!(
            !IndividualProcessNode::has_negation_disjoint_to_individual_id_in_context(
                &ctx, source, role, 402
            )
        );

        let mut disjoint_edge = DisjointEdge::new();
        disjoint_edge.init_negation_disjoint_edge(source, dest, role, TrackPointId::NONE);
        let disjoint_edge = ctx.alloc_disjoint_edge(disjoint_edge);
        IndividualProcessNode::install_disjoint_link_in_context(&mut ctx, source, disjoint_edge);

        assert!(
            IndividualProcessNode::has_negation_disjoint_to_individual_id_in_context(
                &ctx, source, role, 402
            )
        );
        assert!(
            IndividualProcessNode::has_negation_disjoint_to_individual_in_context(
                &ctx, source, dest, role
            )
        );
        let mut it = IndividualProcessNode::get_disjoint_successor_role_iterator_id_in_context(
            &ctx, source, 402,
        );
        assert_eq!(it.get_successor_individual_id(), 402);
        assert_eq!(it.next(true), disjoint_edge);
        assert_eq!(it.next(true), DisjointEdgeId::NONE);

        let mut it = IndividualProcessNode::get_disjoint_successor_role_iterator_in_context(
            &ctx, source, dest,
        );
        assert_eq!(it.next(true), disjoint_edge);
        assert_eq!(it.next(true), DisjointEdgeId::NONE);

        IndividualProcessNode::remove_disjoint_links_in_context(&mut ctx, source, 402);
        assert!(
            !IndividualProcessNode::has_negation_disjoint_to_individual_in_context(
                &ctx, source, dest, role
            )
        );
        assert!(
            !IndividualProcessNode::get_disjoint_successor_role_iterator_id_in_context(
                &ctx, source, 402
            )
            .has_next()
        );
    }
}
