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
//! `// W2-DEFER[api]` with a minimal stub (return the C++ null/empty/0 result, or
//! a no-op) until the satellite arenas are threaded through a process context and
//! their methods land. The deferred steps are the only behavioural gap; the
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
use super::node::IndividualProcessNode;
use super::{DisjointEdgeId, EdgeId, LabelSetId, NodeId, RoleSuccHashId};
use super::stubs::{
    ConceptProcessingQueueId, ConceptPropBindingSetHashId, ConceptRepPropSetHashId,
    ConceptVarBindPathSetHashId, ConnSuccSetId, DisjointSuccRoleHashId, DistinctHashId,
    SuccRoleHashId,
};

// ===========================================================================
// Placeholder return types (not-yet-ported `Process/` iterator / queue classes).
// KONCLUDE-PORT-NOTE[api]: PN-3 returns several `Process/` iterator and reapply
// queue types that have their own (unported) units. They are stubbed here so the
// PN-3 signatures stay exact and diffable; each default-constructs to the C++
// empty/null iterator the `else` branches return. When the real iterator units
// land these reconcile to them.
// ===========================================================================

/// Port of `CRoleSuccessorLinkIterator` (placeholder).
#[derive(Default)]
pub struct RoleSuccessorLinkIterator;
/// Port of `CRoleSuccessorIterator` (placeholder).
#[derive(Default)]
pub struct RoleSuccessorIterator;
/// Port of `CSuccessorRoleIterator` (placeholder).
#[derive(Default)]
pub struct SuccessorRoleIterator;
/// Port of `CDisjointSuccessorRoleIterator` (placeholder).
#[derive(Default)]
pub struct DisjointSuccessorRoleIterator;
/// Port of `CSuccessorIterator` (placeholder).
#[derive(Default)]
pub struct SuccessorIterator;
/// Port of `CConnectionSuccessorSetIterator` (placeholder).
#[derive(Default)]
pub struct ConnectionSuccessorSetIterator;
/// Port of `CReapplyQueueIterator` (placeholder; C++ else branch is
/// `CReapplyQueueIterator(nullptr,nullptr)`).
#[derive(Default)]
pub struct ReapplyQueueIterator;
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
// `mUseDisjointSuccRoleHash` process-hash. Those hash backends are W2-DEFER
// (their arenas are not threaded through the process context yet), so the
// `else` branch of each getter yields the *empty* iterator — exactly the
// default-constructed C++ iterator with `mIterator1 == mIterator2 == false`,
// whose `hasNext()` is `false` and whose `next()` is `nullptr`/`0`.
//
// These `has_next`/`next` bodies port that empty-iterator behaviour faithfully
// so the phase-5 link-relocation loops in `completion/u15.rs` (and any other
// caller) COMPILE and run zero iterations until the real hash backend lands.
// They are the `(no has_next/next)` gap the `RECONCILE-NEED` flags called out.
// ===========================================================================

impl SuccessorRoleIterator {
    /// Port of `CSuccessorRoleIterator::hasNext` (empty-iterator surface).
    pub fn has_next(&self) -> bool { false }
    /// Port of `CSuccessorRoleIterator::next` → `CIndividualLinkEdge*` (empty → NONE).
    pub fn next(&mut self, _move_next: bool) -> EdgeId { EdgeId::NONE }
}

impl DisjointSuccessorRoleIterator {
    /// Port of `CDisjointSuccessorRoleIterator::hasNext` (empty-iterator surface).
    pub fn has_next(&self) -> bool { false }
    /// Port of `CDisjointSuccessorRoleIterator::next` → `CNegationDisjointEdge*`
    /// (empty → NONE).
    pub fn next(&mut self, _move_next: bool) -> DisjointEdgeId { DisjointEdgeId::NONE }
}

impl RoleSuccessorIterator {
    /// Port of `CRoleSuccessorIterator::hasNext` (empty-iterator surface).
    pub fn has_next(&self) -> bool { false }
    /// Port of `CRoleSuccessorIterator::next` → `CRole*` (empty → NONE).
    pub fn next(&mut self, _move_next: bool) -> RoleId { RoleId::NONE }
}

impl RoleSuccessorLinkIterator {
    /// Port of `CRoleSuccessorLinkIterator::hasNext` (empty-iterator surface).
    pub fn has_next(&self) -> bool { false }
    /// Port of `CRoleSuccessorLinkIterator::next` → `CIndividualLinkEdge*`
    /// (empty → NONE).
    pub fn next(&mut self, _move_next: bool) -> EdgeId { EdgeId::NONE }
}

impl SuccessorIterator {
    /// Port of `CSuccessorIterator::hasNext` (empty-iterator surface).
    pub fn has_next(&self) -> bool { false }
    /// Port of `CSuccessorIterator::nextLink` → `CIndividualLinkEdge*` (empty → NONE).
    pub fn next_link(&mut self, _move_next: bool) -> EdgeId { EdgeId::NONE }
    /// Port of `CSuccessorIterator::nextIndividualID` → `cint64` (empty → 0).
    pub fn next_individual_id(&mut self, _move_next: bool) -> Cint64 { 0 }
}

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
            // W2-DEFER[api]: allocate CReapplyConceptLabelSet from mMemAllocMan +
            // mReapplyConLabelSet.initConceptLabelSet(mPrevReapplyConLabelSet);
            // mUseReapplyConLabelSet = mReapplyConLabelSet; (needs the label-set arena)
        }
        self.use_reapply_con_label_set
    }

    /// Port of `CIndividualProcessNode::getConnectionSuccessorSet`.
    // superseded by ctx.node_connection_successor_set (W3b context-threaded lazy-getter).
    pub fn get_connection_successor_set(&mut self, create: bool) -> ConnSuccSetId {
        if create && self.conn_succ_set.is_none() {
            // W2-DEFER[api]: allocate CConnectionSuccessorSet +
            // initConnectionSuccessorSet(mPrevConnSuccSet); mUseConnSuccSet = mConnSuccSet;
        }
        self.use_conn_succ_set
    }

    /// Port of `CIndividualProcessNode::getReapplyRoleSuccessorHash`.
    pub fn get_reapply_role_successor_hash(&mut self, create: bool) -> RoleSuccHashId {
        if create && self.reapply_role_succ_hash.is_none() {
            // W2-DEFER[api]: allocate CReapplyRoleSuccessorHash +
            // initRoleSuccessorHash(mPrevReapplyRoleSuccHash); mUseReapplyRoleSuccHash = mReapplyRoleSuccHash;
        }
        self.use_reapply_role_succ_hash
    }

    /// Port of `CIndividualProcessNode::getConceptPropagationBindingSetHash`.
    // superseded by ctx.node_concept_propagation_binding_set_hash (W3b context-threaded lazy-getter).
    pub fn get_concept_propagation_binding_set_hash(
        &mut self,
        create: bool,
    ) -> ConceptPropBindingSetHashId {
        if create && self.concept_prop_binding_set_hash.is_none() {
            // W2-DEFER[api]: allocate CConceptPropagationBindingSetHash +
            // initConceptPropagationBindingSetHash(mPrevConceptPropBindingSetHash);
            // mUseConceptPropBindingSetHash = mConceptPropBindingSetHash;
        }
        self.use_concept_prop_binding_set_hash
    }

    /// Port of `CIndividualProcessNode::getConceptVariableBindingPathSetHash`.
    // superseded by ctx.node_concept_variable_binding_path_set_hash (W3b context-threaded lazy-getter).
    pub fn get_concept_variable_binding_path_set_hash(
        &mut self,
        create: bool,
    ) -> ConceptVarBindPathSetHashId {
        if create && self.concept_var_bind_path_set_hash.is_none() {
            // W2-DEFER[api]: allocate CConceptVariableBindingPathSetHash +
            // initConceptVariableBindingPathSetHash(mPrevConceptVarBindPathSetHash);
            // mUseConceptVarBindPathSetHash = mConceptVarBindPathSetHash;
        }
        self.use_concept_var_bind_path_set_hash
    }

    /// Port of `CIndividualProcessNode::getConceptRepresentativePropagationSetHash`.
    pub fn get_concept_representative_propagation_set_hash(
        &mut self,
        create: bool,
    ) -> ConceptRepPropSetHashId {
        if create && self.concept_rep_prop_set_hash.is_none() {
            // W2-DEFER[api]: allocate CConceptRepresentativePropagationSetHash +
            // initConceptRepresentativePropagationSetHash(mPrevConceptRepPropSetHash);
            // mUseConceptRepPropSetHash = mConceptRepPropSetHash;
        }
        self.use_concept_rep_prop_set_hash
    }

    // ===================================================================
    // Role-successor reads (over the reapply role-successor hash).
    // ===================================================================

    /// Port of `CIndividualProcessNode::getRoleSuccessorLinkIterator`.
    pub fn get_role_successor_link_iterator(&self, _role: RoleId) -> RoleSuccessorLinkIterator {
        if self.use_reapply_role_succ_hash.is_some() {
            // W2-DEFER[api]: return mUseReapplyRoleSuccHash.getRoleSuccessorLinkIterator(role)
            RoleSuccessorLinkIterator
        } else {
            RoleSuccessorLinkIterator
        }
    }

    /// Port of `CIndividualProcessNode::getRoleSuccessorCount`.
    pub fn get_role_successor_count(&self, _role: RoleId) -> Cint64 {
        if self.use_reapply_role_succ_hash.is_some() {
            // W2-DEFER[api]: return mUseReapplyRoleSuccHash.getRoleSuccessorCount(role)
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
            // W2-DEFER[api]: return mUseReapplyRoleSuccHash.getRoleSuccessorHistoryLinkIterator(role,lastLink)
            RoleSuccessorLinkIterator
        } else {
            RoleSuccessorLinkIterator
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
            // W2-DEFER[api]: return mUseReapplyRoleSuccHash.hasRoleSuccessorToIndividual(
            //     role, getIndividualNodeID(), destinationIndiID,
            //     _locateable && self.reapply_role_succ_hash.is_some())
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
            // W2-DEFER[api]: return mUseReapplyRoleSuccHash.getRoleSuccessorToIndividualLink(
            //     role, getIndividualNodeID(), destinationIndiID,
            //     _locateable && self.reapply_role_succ_hash.is_some())
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
        self.get_role_successor_to_individual_link_id(role, des_indi.individual_node_id(), locateable)
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
            // W2-DEFER[api]: return mUseDisjointSuccRoleHash.hasDisjointSuccessorRoleLink(destinationIndiID,role)
            return false;
        }
        false
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
            // W2-DEFER[api]: allocate CDisjointSuccessorRoleHash +
            // initDisjointSuccessorRoleHash(mPrevDisjointSuccRoleHash);
            // mUseDisjointSuccRoleHash = mDisjointSuccRoleHash;
        }
        self.use_disjoint_succ_role_hash
    }

    /// Port of `CIndividualProcessNode::installDisjointLink`.
    pub fn install_disjoint_link(&mut self, _link: DisjointEdgeId) -> &mut Self {
        if self.disjoint_succ_role_hash.is_none() {
            self.get_disjoint_successor_role_hash(true);
        }
        // W2-DEFER[api]: mUseDisjointSuccRoleHash.insertDisjointSuccessorRoleLink(
        //     link.getOppositeIndividualID(mIndiID), link)
        self
    }

    /// Port of `CIndividualProcessNode::removeDisjointLinks`.
    pub fn remove_disjoint_links(&mut self, _succ_indi_id: Cint64) -> &mut Self {
        if self.use_disjoint_succ_role_hash.is_some() {
            if self.disjoint_succ_role_hash.is_none() {
                self.get_disjoint_successor_role_hash(true);
            }
            // W2-DEFER[api]: mUseDisjointSuccRoleHash.removeDisjointSuccessorRoleLinks(succIndiID)
        }
        self
    }

    /// Port of `CIndividualProcessNode::getDisjointSuccessorRoleIterator(cint64)`.
    // superseded by ctx.node_disjoint_successor_role_iterator (u15 context-threaded;
    // seeds the real distinct::DisjointSuccessorRoleIterator).
    pub fn get_disjoint_successor_role_iterator_id(
        &self,
        _succ_indi_id: Cint64,
    ) -> DisjointSuccessorRoleIterator {
        if self.use_disjoint_succ_role_hash.is_some() {
            // W2-DEFER[api]: return mUseDisjointSuccRoleHash.getDisjointRoleIterator(succIndiId)
            DisjointSuccessorRoleIterator
        } else {
            DisjointSuccessorRoleIterator
        }
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
            RoleSuccessorIterator
        } else {
            // W2-DEFER[api]: return mUseReapplyRoleSuccHash.getRoleIterator()
            RoleSuccessorIterator
        }
    }

    // ===================================================================
    // Successor-role hash + connection topology.
    // ===================================================================

    /// Port of `CIndividualProcessNode::getSuccessorRoleHash`.
    pub fn get_successor_role_hash(&mut self, create: bool) -> SuccRoleHashId {
        if create && self.succ_role_hash.is_none() {
            // W2-DEFER[api]: allocate CSuccessorRoleHash + initSuccessorRoleHash(mPrevSuccRoleHash);
            // mUseSuccRoleHash = mSuccRoleHash;
        }
        self.use_succ_role_hash
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
            SuccessorRoleIterator
        } else {
            // W2-DEFER[api]: return mUseSuccRoleHash.getSuccessorRoleIterator(indiID)
            SuccessorRoleIterator
        }
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
            // W2-DEFER[api]: return mUseSuccRoleHash.hasSuccessorIndividualNode(indiID)
            false
        }
    }

    // ===================================================================
    // Concept-processing queue + reapply queues / iterators.
    // ===================================================================

    /// Port of `CIndividualProcessNode::getConceptProcessingQueue`.
    pub fn get_concept_processing_queue(&mut self, create: bool) -> ConceptProcessingQueueId {
        if create && self.concept_processing_queue.is_none() {
            // W2-DEFER[api]: allocate CConceptProcessingQueue +
            // initProcessingQueue(mPrevConceptProcessingQueue);
            // mUseConceptProcessingQueue = mConceptProcessingQueue;
        }
        self.use_concept_processing_queue
    }

    /// Port of `CIndividualProcessNode::getRoleReapplyQueue`.
    pub fn get_role_reapply_queue(&mut self, _role: RoleId, create: bool) -> Option<ReapplyQueuePtr> {
        let reapply_queue: Option<ReapplyQueuePtr> = None;
        if create && self.reapply_role_succ_hash.is_none() {
            self.get_reapply_role_successor_hash(true);
        }
        if self.use_reapply_role_succ_hash.is_some() {
            // W2-DEFER[api]: reapplyQueue = mUseReapplyRoleSuccHash.getRoleReapplyQueue(role,create)
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
            // W2-DEFER[api]: return mUseReapplyRoleSuccHash.getRoleReapplyIterator(role,clearDynamicReapllyQueue)
            ReapplyQueueIterator
        } else {
            // CReapplyQueueIterator(nullptr,nullptr)
            ReapplyQueueIterator
        }
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
            // W2-DEFER[api]: reapplyQueue = mUseReapplyConLabelSet.getConceptReapplyQueue(concept,conceptNegation,create)
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
            // W2-DEFER[api]: return mUseReapplyConLabelSet.getConceptReapplyIterator(concept,conceptNegation,clearDynamicReapllyQueue)
            CondensedReapplyQueueIterator { concept_negation }
        } else {
            // CCondensedReapplyQueueIterator(nullptr,conceptNegation)
            CondensedReapplyQueueIterator { concept_negation }
        }
    }

    /// Port of `CIndividualProcessNode::getDistinctHash`.
    // superseded by ctx.node_distinct_hash (W3b context-threaded lazy-getter).
    pub fn get_distinct_hash(&mut self, create: bool) -> DistinctHashId {
        if create && self.distinct_hash.is_none() {
            // W2-DEFER[api]: allocate CDistinctHash + initDistinctHash(mPrevDistinctHash);
            // mUseDistinctHash = mDistinctHash;
        }
        self.use_distinct_hash
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
            // W2-DEFER[api]: return edges[mAncestorLink].isSourceIndividualID(individual)
            return false;
        }
        false
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
        // W2-DEFER[api]: linkCount = mUseReapplyRoleSuccHash.insertRoleSuccessorLink(
        //     link.getLinkRole(), link, reapplyQueueIt)
        let link_count: Cint64 = 0;
        // W2-DEFER[api]: oppIndiID = link.getOppositeIndividualID(mIndiID)
        // W2-DEFER[api]: mUseSuccRoleHash.insertSuccessorRoleLink(oppIndiID, link)
        self.last_added_link = link;
        link_count
    }

    /// Port of `CIndividualProcessNode::removeIndividualLink`.
    pub fn remove_individual_link(&mut self, _link: EdgeId) -> &mut Self {
        if self.reapply_role_succ_hash.is_none() {
            self.get_reapply_role_successor_hash(true);
        }
        // W2-DEFER[api]: mUseReapplyRoleSuccHash.removeRoleSuccessorLink(link.getLinkRole(), link)
        self
    }

    /// Port of `CIndividualProcessNode::removeIndividualConnection`.
    pub fn remove_individual_connection(&mut self, _indi: &IndividualProcessNode) -> &mut Self {
        if self.succ_role_hash.is_none() {
            self.get_successor_role_hash(true);
        }
        // W2-DEFER[api]: mSuccRoleHash.removeSuccessor(indi.getIndividualNodeID())
        if self.use_conn_succ_set.is_some() {
            if self.conn_succ_set.is_none() {
                self.get_connection_successor_set(true);
            }
            // W2-DEFER[api]: mConnSuccSet.removeConnection(indi.getIndividualNodeID())
        }
        self
    }

    /// Port of `CIndividualProcessNode::getSuccessorIterator`.
    // superseded by ctx.node_successor_iterator (u15 context-threaded; seeds the real
    // succ_role_hash::SuccessorIterator).
    pub fn get_successor_iterator(&self) -> SuccessorIterator {
        if self.use_succ_role_hash.is_none() {
            return SuccessorIterator;
        }
        // W2-DEFER[api]: return mUseSuccRoleHash.getSuccessorIterator()
        SuccessorIterator
    }

    /// Port of `CIndividualProcessNode::getConnectionSuccessorIterator`.
    pub fn get_connection_successor_iterator(&self) -> ConnectionSuccessorSetIterator {
        if self.use_conn_succ_set.is_some() {
            // W2-DEFER[api]: return mUseConnSuccSet.getConnectionSuccessorIterator()
            ConnectionSuccessorSetIterator
        } else {
            ConnectionSuccessorSetIterator
        }
    }
}
