//! `process/db4.rs` — method-batch unit **DB-4**: the `CProcessingDataBox`
//! blocking/reactivation lazy-allocated hashes, the node-linker take/add work
//! queues, and the last-processing / construction-state accessors.
//!
//! Port of `Source/Reasoner/Kernel/Process/CProcessingDataBox.cpp` lines
//! 1295–1675. Struct + the null-ctor live in `databox.rs`; the lifecycle handoff
//! lives in `db1.rs`. Methods already ported in `databox.rs` are NOT re-ported
//! here (noted in the module summary below).
//!
//! Methods of this `.cpp` range that are ALREADY in `databox.rs` (skipped):
//! `hasNominalNonDeterministicProcessingNodesSorted`,
//! `setNominalNonDeterministicProcessingNodesSorted`,
//! `setMultipleConstructionIndividualNodes`,
//! `hasMultipleConstructionIndividualNodes`, `getConstructedIndividualNode`,
//! `setConstructedIndividualNode`, `hasConstructedIndividualNodeInitialized`,
//! `setConstructedIndividualNodeInitialized`,
//! `isReapplicationLastConceptDesciptorOnLastIndividualNodeRequired`,
//! `setReapplicationLastConceptDesciptorOnLastIndividualNodeRequired`,
//! `setMaximumDeterministicBranchTag`, `getMaximumDeterministicBranchTag`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: per the global substrate decision, each
//! intrusive `CXLinker<CIndividualProcessNode*>` / `CIndividualProcessNodeLinker`
//! chain head is owned here as a `Vec<NodeId>` whose **front (index 0) is the
//! chain head**. `getNext()`-style head advance ⇒ `remove(0)`; the C++
//! `linker->append(mHead)` (which splices the *new* chain in front of the
//! existing head and returns the new head) ⇒ prepend; "take the whole linker" ⇒
//! `std::mem::take`. The intrusive `clearNext()` bookkeeping has no `Vec` analog.
//!
//! KONCLUDE-PORT-NOTE[memory-pool]: the `getX(create)` lazy getters allocate
//! their hash/queue/set/tree from the per-test `CProcessContext` pool and run its
//! `initX(prev)` reseed; that allocator + the target container classes are not
//! ported yet, so each allocation site is left as a `// W2-DEFER[api]` stub and
//! the getter returns the current `mUseX` id (`Id::NONE` until wired).

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::databox::ProcessingDataBox;
use super::stubs::{
    BlockingIndividualNodeLinkedCandidateHash, BranchingTree,
    IndividualReactivationProcessingQueue, NodeSwitchHistory, ReusingReviewData,
    SignatureBlockingReviewSet,
};
// W3.5b/W2.7 reconcile: real ported blocking-candidate hashes (un-wired from `stubs`).
use super::blocking_hash::BlockingIndividualNodeCandidateHash;
use super::reapply_sat::SignatureBlockingCandidateHash;
use super::{ConProcDescId, NodeId};

impl ProcessingDataBox {
    /// Port of `CProcessingDataBox::setSignatureBlockingCandidateHash`. `.cpp` 1295.
    pub fn set_signature_blocking_candidate_hash(
        &mut self,
        signature_hash: Id<SignatureBlockingCandidateHash>,
    ) -> &mut Self {
        self.signature_blocking_candidate_hash = signature_hash; // 1296
        self.use_signature_blocking_candidate_hash = signature_hash; // 1297
        self
    }

    /// Port of `CProcessingDataBox::getSignatureBlockingCandidateHash`. `.cpp` 1302.
    pub fn signature_blocking_candidate_hash(
        &mut self,
        create: bool,
    ) -> Id<SignatureBlockingCandidateHash> {
        if self.signature_blocking_candidate_hash.is_none() && create {
            // W2-DEFER[api]: allocate CSignatureBlockingCandidateHash from the
            // process-context pool + initSignatureBlockingCandidateHash(prev).
            //   self.signature_blocking_candidate_hash = <alloc>;
            //   self.signature_blocking_candidate_hash
            //       .init_signature_blocking_candidate_hash(self.prev_signature_blocking_candidate_hash);
            //   self.use_signature_blocking_candidate_hash = self.signature_blocking_candidate_hash;
        }
        self.use_signature_blocking_candidate_hash
    }

    /// Port of `CProcessingDataBox::getSignatureNominalDelayingCandidateHash`. `.cpp` 1313.
    pub fn signature_nominal_delaying_candidate_hash(
        &mut self,
        create: bool,
    ) -> Id<SignatureBlockingCandidateHash> {
        if self.signature_nominal_delaying_candidate_hash.is_none() && create {
            // W2-DEFER[api]: allocate CSignatureBlockingCandidateHash from the
            // process-context pool + initSignatureBlockingCandidateHash(prev).
            //   self.signature_nominal_delaying_candidate_hash = <alloc>;
            //   self.use_signature_nominal_delaying_candidate_hash =
            //       self.signature_nominal_delaying_candidate_hash;
        }
        self.use_signature_nominal_delaying_candidate_hash
    }

    /// Port of `CProcessingDataBox::getBlockingIndividualNodeCandidateHash`. `.cpp` 1324.
    pub fn blocking_individual_node_candidate_hash(
        &mut self,
        create: bool,
    ) -> Id<BlockingIndividualNodeCandidateHash> {
        if self.blocking_indi_node_candidate_hash.is_none() && create {
            // W2-DEFER[api]: allocate CBlockingIndividualNodeCandidateHash + init(prev).
            //   self.blocking_indi_node_candidate_hash = <alloc>;
            //   self.use_blocking_indi_node_candidate_hash = self.blocking_indi_node_candidate_hash;
        }
        self.use_blocking_indi_node_candidate_hash
    }

    /// Port of `CProcessingDataBox::getBlockingIndividualNodeLinkedCandidateHash`. `.cpp` 1333.
    pub fn blocking_individual_node_linked_candidate_hash(
        &mut self,
        create: bool,
    ) -> Id<BlockingIndividualNodeLinkedCandidateHash> {
        if self.blocking_indi_node_linked_candidate_hash.is_none() && create {
            // W2-DEFER[api]: allocate CBlockingIndividualNodeLinkedCandidateHash + init(prev).
            //   self.blocking_indi_node_linked_candidate_hash = <alloc>;
            //   self.use_blocking_indi_node_linked_candidate_hash =
            //       self.blocking_indi_node_linked_candidate_hash;
        }
        self.use_blocking_indi_node_linked_candidate_hash
    }

    /// Port of `CProcessingDataBox::getSignatureBlockingReviewSet`. `.cpp` 1342.
    pub fn signature_blocking_review_set(
        &mut self,
        create: bool,
    ) -> Id<SignatureBlockingReviewSet> {
        if self.signature_blocking_review_set.is_none() && create {
            // W2-DEFER[api]: allocate CSignatureBlockingReviewSet + initSignatureBlockingReviewSet(prev).
            //   self.signature_blocking_review_set = <alloc>;
            //   self.use_signature_blocking_review_set = self.signature_blocking_review_set;
        }
        self.use_signature_blocking_review_set
    }

    /// Port of `CProcessingDataBox::getEarlyIndividualReactivationProcessingQueue`. `.cpp` 1351.
    pub fn early_individual_reactivation_processing_queue(
        &mut self,
        create: bool,
    ) -> Id<IndividualReactivationProcessingQueue> {
        if self.early_indi_react_pro_queue.is_none() && create {
            // W2-DEFER[api]: allocate CIndividualReactivationProcessingQueue + initProcessingQueue(prev).
            //   self.early_indi_react_pro_queue = <alloc>;
            //   self.use_early_indi_react_pro_queue = self.early_indi_react_pro_queue;
        }
        self.use_early_indi_react_pro_queue
    }

    /// Port of `CProcessingDataBox::clearEarlyIndividualReactivationProcessingQueue`. `.cpp` 1360.
    pub fn clear_early_individual_reactivation_processing_queue(&mut self) -> &mut Self {
        self.early_indi_react_pro_queue = Id::NONE; // 1361
        self.use_early_indi_react_pro_queue = Id::NONE; // 1362
        self.prev_early_indi_react_pro_queue = Id::NONE; // 1363
        self
    }

    /// Port of `CProcessingDataBox::getLateIndividualReactivationProcessingQueue`. `.cpp` 1371.
    pub fn late_individual_reactivation_processing_queue(
        &mut self,
        create: bool,
    ) -> Id<IndividualReactivationProcessingQueue> {
        if self.late_indi_react_pro_queue.is_none() && create {
            // W2-DEFER[api]: allocate CIndividualReactivationProcessingQueue + initProcessingQueue(prev).
            //   self.late_indi_react_pro_queue = <alloc>;
            //   self.use_late_indi_react_pro_queue = self.late_indi_react_pro_queue;
        }
        self.use_late_indi_react_pro_queue
    }

    /// Port of `CProcessingDataBox::clearLateIndividualReactivationProcessingQueue`. `.cpp` 1380.
    pub fn clear_late_individual_reactivation_processing_queue(&mut self) -> &mut Self {
        self.late_indi_react_pro_queue = Id::NONE; // 1381
        self.use_late_indi_react_pro_queue = Id::NONE; // 1382
        self.prev_late_indi_react_pro_queue = Id::NONE; // 1383
        self
    }

    /// Port of `CProcessingDataBox::clearSignatureBlockingReviewSet`. `.cpp` 1388.
    pub fn clear_signature_blocking_review_set(&mut self) -> &mut Self {
        self.use_signature_blocking_review_set = Id::NONE; // 1389
        self.signature_blocking_review_set = Id::NONE; // 1390
        self.prev_signature_blocking_review_set = Id::NONE; // 1391
        self
    }

    /// Port of `CProcessingDataBox::clearReusingReviewData`. `.cpp` 1395.
    pub fn clear_reusing_review_data(&mut self) -> &mut Self {
        self.reusing_review_set = Id::NONE; // 1396
        self.use_reusing_review_set = Id::NONE; // 1397
        self.prev_reusing_review_set = Id::NONE; // 1398
        self
    }

    /// Port of `CProcessingDataBox::getReusingReviewData`. `.cpp` 1402.
    pub fn reusing_review_data(&mut self, create: bool) -> Id<ReusingReviewData> {
        if self.reusing_review_set.is_none() && create {
            // W2-DEFER[api]: allocate CReusingReviewData + initReviewData(prev).
            //   self.reusing_review_set = <alloc>;
            //   self.use_reusing_review_set = self.reusing_review_set;
        }
        self.use_reusing_review_set
    }

    /// Port of `CProcessingDataBox::getNodeSwitchHistory`. `.cpp` 1411.
    pub fn node_switch_history(&mut self, create: bool) -> Id<NodeSwitchHistory> {
        if self.node_switch_history.is_none() && create {
            // W2-DEFER[api]: allocate CNodeSwitchHistory + initSwitchHistory(prev).
            //   self.node_switch_history = <alloc>;
            //   self.use_node_switch_history = self.node_switch_history;
        }
        self.use_node_switch_history
    }

    /// Port of `CProcessingDataBox::getBranchingTree`. `.cpp` 1420.
    pub fn branching_tree(&mut self, create: bool) -> Id<BranchingTree> {
        if self.branching_tree.is_none() && create {
            // W2-DEFER[api]: allocate CBranchingTree + initBranchingTree(prev).
            //   self.branching_tree = <alloc>;
            //   self.use_branching_tree = self.branching_tree;
        }
        self.use_branching_tree
    }

    /// Port of `CProcessingDataBox::hasCacheTestingIndividualNodes`. `.cpp` 1429.
    pub fn has_cache_testing_individual_nodes(&self) -> bool {
        !self.individual_node_cache_testing_linker.is_empty()
    }

    /// Port of `CProcessingDataBox::takeNextCacheTestingIndividualNode`. `.cpp` 1433.
    pub fn take_next_cache_testing_individual_node(&mut self) -> NodeId {
        // KONCLUDE-PORT-NOTE[ownership]: head advance == pop the chain front.
        let head = self
            .individual_node_cache_testing_linker
            .first()
            .copied()
            .unwrap_or(NodeId::NONE);
        if !self.individual_node_cache_testing_linker.is_empty() {
            self.individual_node_cache_testing_linker.remove(0);
        }
        head
    }

    /// Port of `CProcessingDataBox::takeIndividualNodeCacheTestingLinker`. `.cpp` 1442.
    pub fn take_individual_node_cache_testing_linker(&mut self) -> Vec<NodeId> {
        std::mem::take(&mut self.individual_node_cache_testing_linker)
    }

    /// Port of `CProcessingDataBox::addIndividualNodeCacheTestingLinker`. `.cpp` 1448.
    pub fn add_individual_node_cache_testing_linker(&mut self, linker: Vec<NodeId>) -> &mut Self {
        if !linker.is_empty() {
            // KONCLUDE-PORT-NOTE[ownership]: `linker->append(mHead)` splices the
            // new chain in front of the existing head ⇒ prepend.
            let mut linker = linker;
            linker.append(&mut self.individual_node_cache_testing_linker);
            self.individual_node_cache_testing_linker = linker;
        }
        self
    }

    /// Port of `CProcessingDataBox::getSortedNominalNonDeterministicProcessingNodeLinker`. `.cpp` 1460.
    pub fn sorted_nominal_non_deterministic_processing_node_linker(&self) -> &[NodeId] {
        &self.sorted_nominal_non_det_processing_node_linker
    }

    /// Port of `CProcessingDataBox::hasSortedNominalNonDeterministicProcessingNodes`. `.cpp` 1465.
    pub fn has_sorted_nominal_non_deterministic_processing_nodes(&self) -> bool {
        !self.sorted_nominal_non_det_processing_node_linker.is_empty()
    }

    /// Port of `CProcessingDataBox::takeSortedNominalNonDeterministicProcessingNode`. `.cpp` 1469.
    pub fn take_sorted_nominal_non_deterministic_processing_node(&mut self) -> NodeId {
        let head = self
            .sorted_nominal_non_det_processing_node_linker
            .first()
            .copied()
            .unwrap_or(NodeId::NONE);
        if !self.sorted_nominal_non_det_processing_node_linker.is_empty() {
            self.nominal_non_det_processing_count -= 1; // 1472
            self.sorted_nominal_non_det_processing_node_linker.remove(0); // 1473
        }
        head
    }

    /// Port of `CProcessingDataBox::takeSortedNominalNonDeterministicProcessingNodeLinker`. `.cpp` 1479.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: mirrors the C++ — only the list head is
    /// cleared; `mNominalNonDetProcessingCount` is left untouched here.
    pub fn take_sorted_nominal_non_deterministic_processing_node_linker(&mut self) -> Vec<NodeId> {
        std::mem::take(&mut self.sorted_nominal_non_det_processing_node_linker)
    }

    /// Port of `CProcessingDataBox::addSortedNominalNonDeterministicProcessingNodeLinker`. `.cpp` 1485.
    pub fn add_sorted_nominal_non_deterministic_processing_node_linker(
        &mut self,
        linker: Vec<NodeId>,
    ) -> &mut Self {
        if !linker.is_empty() {
            self.nominal_non_det_processing_count += linker.len() as Cint64; // 1487
            // 1488: linker->append(mHead) ⇒ prepend (see ownership note).
            let mut linker = linker;
            linker.append(&mut self.sorted_nominal_non_det_processing_node_linker);
            self.sorted_nominal_non_det_processing_node_linker = linker;
        }
        self
    }

    /// Port of `CProcessingDataBox::setSortedNominalNonDeterministicProcessingNodeLinker`. `.cpp` 1493.
    pub fn set_sorted_nominal_non_deterministic_processing_node_linker(
        &mut self,
        linker: Vec<NodeId>,
    ) -> &mut Self {
        self.nominal_non_det_processing_count = linker.len() as Cint64; // 1494
        self.sorted_nominal_non_det_processing_node_linker = linker; // 1495
        self
    }

    /// Port of `CProcessingDataBox::clearSortedNominalNonDeterministicProcessingNodeLinker`. `.cpp` 1499.
    pub fn clear_sorted_nominal_non_deterministic_processing_node_linker(&mut self) -> &mut Self {
        self.sorted_nominal_non_det_processing_node_linker.clear(); // 1500
        self.nominal_non_det_processing_count = 0; // 1501
        self
    }

    /// Port of `CProcessingDataBox::takeNextIndividualNodeBlockedResolveLinker`. `.cpp` 1520.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ returns the head `CXLinker*`; the port
    /// stores nodes directly, so the head's node id is returned.
    pub fn take_next_individual_node_blocked_resolve_linker(&mut self) -> NodeId {
        let head = self
            .individual_node_resolve_linker
            .first()
            .copied()
            .unwrap_or(NodeId::NONE);
        if !self.individual_node_resolve_linker.is_empty() {
            self.individual_node_resolve_linker.remove(0); // 1523
        }
        head
    }

    /// Port of `CProcessingDataBox::hasBlockedResolveIndividualNodes`. `.cpp` 1528.
    pub fn has_blocked_resolve_individual_nodes(&self) -> bool {
        !self.individual_node_resolve_linker.is_empty()
    }

    /// Port of `CProcessingDataBox::clearBlockedResolveIndividualNodes`. `.cpp` 1532.
    pub fn clear_blocked_resolve_individual_nodes(&mut self) -> &mut Self {
        self.individual_node_resolve_linker.clear(); // 1533
        self
    }

    /// Port of `CProcessingDataBox::addIndividualNodeBlockedResolveLinker`. `.cpp` 1537.
    pub fn add_individual_node_blocked_resolve_linker(&mut self, linker: Vec<NodeId>) -> &mut Self {
        if !linker.is_empty() {
            // 1539: linker->append(mHead) ⇒ prepend (see ownership note).
            let mut linker = linker;
            linker.append(&mut self.individual_node_resolve_linker);
            self.individual_node_resolve_linker = linker;
        }
        self
    }

    /// Port of `CProcessingDataBox::getBlockableIndividualNodeUpdatedLinker`. `.cpp` 1551.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `get*` mutates — it advances the
    /// chain head and returns the old head — so the port takes `&mut self` and
    /// pops the front, exactly as the source does.
    pub fn blockable_individual_node_updated_linker(&mut self) -> NodeId {
        let head = self
            .blockable_individual_node_updated_linker
            .first()
            .copied()
            .unwrap_or(NodeId::NONE);
        if !self.blockable_individual_node_updated_linker.is_empty() {
            self.blockable_individual_node_updated_linker.remove(0); // 1554
        }
        head
    }

    /// Port of `CProcessingDataBox::hasBlockableIndividualNodeUpdatedLinker`. `.cpp` 1559.
    pub fn has_blockable_individual_node_updated_linker(&self) -> bool {
        !self.blockable_individual_node_updated_linker.is_empty()
    }

    /// Port of `CProcessingDataBox::clearBlockableIndividualNodeUpdatedLinker`. `.cpp` 1563.
    pub fn clear_blockable_individual_node_updated_linker(&mut self) -> &mut Self {
        self.blockable_individual_node_updated_linker.clear(); // 1564
        self
    }

    /// Port of `CProcessingDataBox::addBlockableIndividualNodeUpdatedLinker`. `.cpp` 1568.
    pub fn add_blockable_individual_node_updated_linker(&mut self, linker: Vec<NodeId>) -> &mut Self {
        if !linker.is_empty() {
            // 1570: linker->append(mHead) ⇒ prepend (see ownership note).
            let mut linker = linker;
            linker.append(&mut self.blockable_individual_node_updated_linker);
            self.blockable_individual_node_updated_linker = linker;
        }
        self
    }

    /// Port of `CProcessingDataBox::getProcessContext`. `.cpp` 1610.
    pub fn process_context(&self) -> Cint64 {
        self.process_context
    }

    /// Port of `CProcessingDataBox::setLastProcessingIndividualNodeAndConceptDescriptor`. `.cpp` 1614.
    pub fn set_last_processing_individual_node_and_concept_descriptor(
        &mut self,
        indi_node: NodeId,
        con_des: ConProcDescId,
    ) -> &mut Self {
        self.last_processing_indi_node = indi_node; // 1615
        self.last_processing_con_des = con_des; // 1616
        self
    }

    /// Port of `CProcessingDataBox::getLastProcessingIndividualNodeAndConceptDescriptor`. `.cpp` 1620.
    ///
    /// KONCLUDE-PORT-NOTE[pointer-alias]: the C++ returns a `bool` and fills two
    /// out-reference params; the port returns `Some((indiNode, conDes))` on the
    /// true branch and `None` otherwise.
    pub fn last_processing_individual_node_and_concept_descriptor(
        &self,
    ) -> Option<(NodeId, ConProcDescId)> {
        if self.last_processing_indi_node.is_some() && self.last_processing_con_des.is_some() {
            return Some((self.last_processing_indi_node, self.last_processing_con_des));
        }
        None
    }

    /// Port of `CProcessingDataBox::hasLastProcessingIndividualNodeAndConceptDescriptor`. `.cpp` 1629.
    pub fn has_last_processing_individual_node_and_concept_descriptor(&self) -> bool {
        self.last_processing_con_des.is_some() && self.last_processing_indi_node.is_some()
    }

    /// Port of `CProcessingDataBox::getIndividualProcessNodeLinker`. `.cpp` 1642.
    pub fn individual_process_node_linker(&self) -> &[NodeId] {
        &self.indi_process_node_linker
    }

    /// Port of `CProcessingDataBox::takeIndividualProcessNodeLinker`. `.cpp` 1646.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: advances the head and returns the old head
    /// node (the C++ `clearNext()` on the detached linker has no `Vec` analog).
    pub fn take_individual_process_node_linker(&mut self) -> NodeId {
        let head = self
            .indi_process_node_linker
            .first()
            .copied()
            .unwrap_or(NodeId::NONE);
        if !self.indi_process_node_linker.is_empty() {
            self.indi_process_node_linker.remove(0); // 1649
        }
        head
    }

    /// Port of `CProcessingDataBox::setIndividualProcessNodeLinker`. `.cpp` 1655.
    pub fn set_individual_process_node_linker(
        &mut self,
        indi_process_node_linker: Vec<NodeId>,
    ) -> &mut Self {
        self.indi_process_node_linker = indi_process_node_linker; // 1656
        self
    }

    /// Port of `CProcessingDataBox::addIndividualProcessNodeLinker`. `.cpp` 1661.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: no null guard in the source; the single
    /// linker is prepended (`indiProcessNodeLinker->append(mHead)`).
    pub fn add_individual_process_node_linker(
        &mut self,
        indi_process_node_linker: NodeId,
    ) -> &mut Self {
        self.indi_process_node_linker.insert(0, indi_process_node_linker); // 1662
        self
    }
}
