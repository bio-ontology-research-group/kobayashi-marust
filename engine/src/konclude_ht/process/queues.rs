//! `process::queues` — the concept / individual **processing-queue subsystem**:
//! the triple-buffered queues that drive the completion engine's inner loop.
//!
//! Ports the workhorse `CIndividual*ProcessingQueue` family + the per-node
//! `CConceptProcessingQueue` from
//! `Source/Reasoner/Kernel/Process/`:
//!   * `CIndividualUnsortedProcessingQueue` (LIFO node linker)
//!   * `CIndividualLinkerRotationProcessingQueue` (two-stage process/rotation)
//!   * `CIndividualDepthProcessingQueue` (depth-priority ordered)
//!   * `CConceptProcessingQueue` (per-node concept-descriptor priority vector)
//!   * the value helpers `CIndividualDepthPriority` and
//!     `CConceptProcessingPriorityQueueData`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: Konclude's queues are bump-allocated from the
//! per-test `CProcessContext` pool and addressed by `CXxx*`; across a
//! non-deterministic branch the child databox shares the parent's queue object
//! through `mPrevX` (a pointer into that shared pool). The port keeps that shared
//! pool faithful: the queue objects live in `Arena<T>` fields on `ProcessContext`
//! (the single per-test pool every branch databox references), addressed by the
//! `Id<T>` triples already declared on the databox. db3's `getXxx` allocates into
//! that arena.
//!
//! KONCLUDE-PORT-NOTE[memory-pool]: the intrusive `CXLinker<CIndividualProcessNode*>`
//! node chains map to owned `Vec<NodeId>` held BY VALUE inside each queue (no
//! separate linker arena — the queued entries are bare node ids). The COW
//! `initProcessingQueue(prev)` (share the parent's linker head) is realised as a
//! deep `clone()` of the parent's `Vec`/`BTreeMap`; behaviour is identical (same
//! queued contents, same take order), only the sharing optimisation is dropped.
//! The `CConceptProcessingQueue` descriptors DO live in an arena
//! (`con_proc_descs`, already ported), so its chain-walking ops thread
//! `&mut ProcessContext`.

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::mem;

use super::super::model::substrate::{Arena, Cint64, Id};
use super::context::ProcessContext;
use super::descriptor::ConceptProcessPriority;
use super::node::IndividualProcessNode;
use super::{ConProcDescId, NodeId};

// ===========================================================================
// CIndividualDepthPriority — the (depth, id) order key.
// ===========================================================================

/// Port of `CIndividualDepthPriority`.
///
/// KONCLUDE-PORT-NOTE[overload]: the C++ `operator<` / `operator<=` / `operator==`
/// order by `mIndiDepth` then `mIndiID`. Field declaration order (`indi_depth`
/// then `indi_id`) makes the derived `Ord` match `operator<` exactly, so the type
/// can key a `BTreeMap` directly.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct IndividualDepthPriority {
    /// `mIndiDepth`.
    pub indi_depth: Cint64,
    /// `mIndiID`.
    pub indi_id: Cint64,
}

impl IndividualDepthPriority {
    /// Port of `CIndividualDepthPriority::CIndividualDepthPriority(cint64,cint64)`.
    pub fn new(indi_depth: Cint64, indi_id: Cint64) -> Self {
        IndividualDepthPriority { indi_depth, indi_id }
    }
    /// Port of `CIndividualDepthPriority::getIndividualDepth`.
    pub fn get_individual_depth(&self) -> Cint64 {
        self.indi_depth
    }
    /// Port of `CIndividualDepthPriority::getIndividualID`.
    pub fn get_individual_id(&self) -> Cint64 {
        self.indi_id
    }
    /// Port of `CIndividualDepthPriority::setPriority`.
    pub fn set_priority(&mut self, indi_depth: Cint64, indi_id: Cint64) -> &mut Self {
        self.indi_depth = indi_depth;
        self.indi_id = indi_id;
        self
    }
}

// ===========================================================================
// CIndividualUnsortedProcessingQueue — LIFO node linker.
// ===========================================================================

/// Port of `CIndividualUnsortedProcessingQueue`.
///
/// KONCLUDE-PORT-NOTE[memory-pool]: `mProcessingIndiNodeLinker` (a head-front
/// `CXLinker` chain, prepend-on-insert / take-head) becomes `linker: Vec<NodeId>`
/// with the HEAD at the BACK (`push`/`pop`): both are LIFO (take == newest), so
/// the take order is byte-identical and `insert`/`take` stay O(1).
#[derive(Clone, Debug, Default)]
pub struct IndividualUnsortedProcessingQueue {
    /// `mIndiProDesCount`.
    pub indi_pro_des_count: Cint64,
    /// `mProcessingIndiNodeLinker` (head == back).
    pub linker: Vec<NodeId>,
}

impl IndividualUnsortedProcessingQueue {
    /// Port of `CIndividualUnsortedProcessingQueue::CIndividualUnsortedProcessingQueue`.
    pub fn new() -> Self {
        IndividualUnsortedProcessingQueue { indi_pro_des_count: 0, linker: Vec::new() }
    }

    /// Port of `CIndividualUnsortedProcessingQueue::initProcessingQueue`.
    pub fn init_processing_queue(&mut self, prev: Option<&IndividualUnsortedProcessingQueue>) -> &mut Self {
        if let Some(p) = prev {
            self.indi_pro_des_count = p.indi_pro_des_count;
            self.linker = p.linker.clone();
        } else {
            self.linker.clear();
            self.indi_pro_des_count = 0;
        }
        self
    }

    /// Port of `CIndividualUnsortedProcessingQueue::takeNextProcessIndividualNode`.
    pub fn take_next_process_individual_node(&mut self) -> NodeId {
        if let Some(n) = self.linker.pop() {
            self.indi_pro_des_count -= 1;
            n
        } else {
            NodeId::NONE
        }
    }

    /// Port of `CIndividualUnsortedProcessingQueue::getNextProcessIndividualNode`.
    pub fn get_next_process_individual_node(&self) -> NodeId {
        self.linker.last().copied().unwrap_or(NodeId::NONE)
    }

    /// Port of `CIndividualUnsortedProcessingQueue::insertIndiviudalProcessNode`.
    pub fn insert_indiviudal_process_node(&mut self, indi: NodeId) -> &mut Self {
        self.linker.push(indi);
        self.indi_pro_des_count += 1;
        self
    }

    /// Port of `CIndividualUnsortedProcessingQueue::isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.linker.is_empty()
    }
}

// ===========================================================================
// CIndividualLinkerRotationProcessingQueue — two-stage process/rotation.
// ===========================================================================

/// Port of `CIndividualLinkerRotationProcessingQueue`.
///
/// KONCLUDE-PORT-NOTE[memory-pool]: the two head-front `CXLinker` chains
/// (`mProcessingIndiNodeLinker` / `mRotationIndiNodeLinker`) become two
/// `Vec<NodeId>` with head == back. Insert prepends to rotation; takeNext drains
/// processing (refilling it from rotation when empty), both head-first.
#[derive(Clone, Debug, Default)]
pub struct IndividualLinkerRotationProcessingQueue {
    /// `mIndiProDesCount`.
    pub indi_pro_des_count: Cint64,
    /// `mProcessingIndiNodeLinker` (head == back).
    pub processing_linker: Vec<NodeId>,
    /// `mRotationIndiNodeLinker` (head == back).
    pub rotation_linker: Vec<NodeId>,
}

impl IndividualLinkerRotationProcessingQueue {
    /// Port of the ctor.
    pub fn new() -> Self {
        IndividualLinkerRotationProcessingQueue {
            indi_pro_des_count: 0,
            processing_linker: Vec::new(),
            rotation_linker: Vec::new(),
        }
    }

    /// Port of `initProcessingQueue`.
    pub fn init_processing_queue(
        &mut self,
        prev: Option<&IndividualLinkerRotationProcessingQueue>,
    ) -> &mut Self {
        if let Some(p) = prev {
            self.indi_pro_des_count = p.indi_pro_des_count;
            self.processing_linker = p.processing_linker.clone();
            self.rotation_linker = p.rotation_linker.clone();
        } else {
            self.rotation_linker.clear();
            self.processing_linker.clear();
            self.indi_pro_des_count = 0;
        }
        self
    }

    /// Port of `takeNextProcessIndividualNode` (with the lazy rotation refill).
    pub fn take_next_process_individual_node(&mut self) -> NodeId {
        if self.processing_linker.is_empty() {
            self.processing_linker = mem::take(&mut self.rotation_linker);
        }
        if let Some(n) = self.processing_linker.pop() {
            self.indi_pro_des_count -= 1;
            n
        } else {
            NodeId::NONE
        }
    }

    /// Port of `getNextProcessIndividualNode`.
    pub fn get_next_process_individual_node(&self) -> NodeId {
        self.processing_linker.last().copied().unwrap_or(NodeId::NONE)
    }

    /// Port of `insertIndiviudalProcessNode` (prepend to rotation).
    pub fn insert_indiviudal_process_node(&mut self, indi: NodeId) -> &mut Self {
        self.rotation_linker.push(indi);
        self.indi_pro_des_count += 1;
        self
    }

    /// Port of `isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.processing_linker.is_empty() && self.rotation_linker.is_empty()
    }
}

// ===========================================================================
// CIndividualDepthProcessingQueue — depth-priority ordered.
// ===========================================================================

/// Port of `CIndividualDepthProcessingQueue`.
///
/// KONCLUDE-PORT-NOTE[memory-pool]: the `mAdditionalPriorityIndiDesMap` COW
/// optimisation (a shared parent map plus a lazily-localised overlay, copied at a
/// size threshold) is collapsed: `init_processing_queue` deep-`clone()`s the
/// parent's `mPriorityIndiDesMap` directly into `priority_map`. Behaviour is
/// identical (the same node is dequeued at each step); only the copy-vs-share
/// optimisation is dropped. The `mRemainingDepthIndiLinkerMap` deferred-depth
/// bucketing IS ported faithfully.
#[derive(Clone, Debug, Default)]
pub struct IndividualDepthProcessingQueue {
    /// `mPriorityIndiDesMap` (depth-priority ordered).
    pub priority_map: BTreeMap<IndividualDepthPriority, NodeId>,
    /// `mNextRemainingDepth`.
    pub next_remaining_depth: Cint64,
    /// `mRemainingDepthIndiLinkerMap` (depth -> queued nodes, head == back).
    pub remaining_depth_map: BTreeMap<Cint64, Vec<NodeId>>,
}

impl IndividualDepthProcessingQueue {
    /// Port of the ctor (`mNextRemainingDepth = 1`).
    pub fn new() -> Self {
        IndividualDepthProcessingQueue {
            priority_map: BTreeMap::new(),
            next_remaining_depth: 1,
            remaining_depth_map: BTreeMap::new(),
        }
    }

    /// Port of `initProcessingQueue` (additional-map COW collapsed, see note).
    pub fn init_processing_queue(&mut self, prev: Option<&IndividualDepthProcessingQueue>) -> &mut Self {
        if let Some(p) = prev {
            self.priority_map = p.priority_map.clone();
            self.remaining_depth_map = p.remaining_depth_map.clone();
            self.next_remaining_depth = p.next_remaining_depth;
        } else {
            self.priority_map.clear();
            self.remaining_depth_map.clear();
            self.next_remaining_depth = 1;
        }
        self
    }

    /// Port of `CIndividualDepthProcessingQueue::takeNextProcessIndividual`.
    ///
    /// Needs each node's `getIndividualNominalLevelOrAncestorDepth` /
    /// `getIndividualNodeID` to rebuild the priority key from a remaining-depth
    /// bucket; those are resolved through the node arena, so this is threaded with
    /// `&Arena<IndividualProcessNode>` (the disjoint-borrow wrapper lives on
    /// `ProcessContext::indi_depth_queue_take_next`).
    pub fn take_next_process_individual(&mut self, nodes: &Arena<IndividualProcessNode>) -> NodeId {
        let mut next_node: NodeId = NodeId::NONE;

        if self.priority_map.is_empty() {
            if let Some((&depth, _)) = self.remaining_depth_map.iter().next() {
                self.next_remaining_depth = depth + 1;
                let bucket = self.remaining_depth_map.remove(&depth).unwrap_or_default();
                for indi in bucket {
                    let node = nodes.get(indi);
                    let priority = IndividualDepthPriority::new(
                        node.individual_nominal_level_or_ancestor_depth(),
                        node.individual_node_id(),
                    );
                    // tryInsert: keep the first value for a key.
                    self.priority_map.entry(priority).or_insert(indi);
                }
            }
        }

        if let Some((&priority, &node)) = self.priority_map.iter().next() {
            next_node = node;
            self.priority_map.remove(&priority);
        }
        next_node
    }

    /// Port of `CIndividualDepthProcessingQueue::insertProcessIndiviudal`.
    pub fn insert_process_indiviudal(
        &mut self,
        nodes: &Arena<IndividualProcessNode>,
        individual: NodeId,
    ) -> &mut Self {
        let node = nodes.get(individual);
        let depth = node.individual_nominal_level_or_ancestor_depth();
        let priority = IndividualDepthPriority::new(depth, node.individual_node_id());
        if depth >= self.next_remaining_depth {
            self.remaining_depth_map.entry(depth).or_default().push(individual);
        } else {
            self.priority_map.insert(priority, individual);
        }
        self
    }

    /// Port of `CIndividualDepthProcessingQueue::isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.priority_map.is_empty() && self.remaining_depth_map.is_empty()
    }
}

// ===========================================================================
// CConceptProcessingPriorityQueueData + CConceptProcessingQueue.
// ===========================================================================

/// Port of `CConceptProcessingPriorityQueueData` — one priority slot of the
/// concept queue: three intrusive `CConceptProcessDescriptor` chain heads.
#[derive(Copy, Clone, Debug)]
pub struct ConceptProcessingPriorityQueueData {
    /// `mDefaultPriorityDescriptorLinker`.
    pub default_linker: ConProcDescId,
    /// `mSortedPriorityDescriptorLinker`.
    pub sorted_linker: ConProcDescId,
    /// `mPrevSortedPriorityDescriptorLinker`.
    pub prev_sorted_linker: ConProcDescId,
}

impl Default for ConceptProcessingPriorityQueueData {
    fn default() -> Self {
        ConceptProcessingPriorityQueueData::new()
    }
}

impl ConceptProcessingPriorityQueueData {
    pub fn new() -> Self {
        ConceptProcessingPriorityQueueData {
            default_linker: ConProcDescId::NONE,
            sorted_linker: ConProcDescId::NONE,
            prev_sorted_linker: ConProcDescId::NONE,
        }
    }
}

/// `CConceptProcessingQueue::mMaxIndex`.
pub const CONCEPT_QUEUE_MAX_INDEX: usize = 15;

/// Port of `CConceptProcessingQueue` — the per-node concept-descriptor queue that
/// drives the inner rule-application loop.
///
/// The priority vector is held BY VALUE (an array of 15 slots); the descriptor
/// chains live in `con_proc_descs` (already an arena), so the insert/take ops
/// thread `&mut ProcessContext`.
#[derive(Clone, Debug)]
pub struct ConceptProcessingQueue {
    /// `mMaxPriorityIndex`.
    pub max_priority_index: Cint64,
    /// `mPriorityVec[mMaxIndex]`.
    pub priority_vec: [ConceptProcessingPriorityQueueData; CONCEPT_QUEUE_MAX_INDEX],
    /// `mDesCount`.
    pub des_count: Cint64,
}

impl Default for ConceptProcessingQueue {
    fn default() -> Self {
        ConceptProcessingQueue::new()
    }
}

impl ConceptProcessingQueue {
    /// Port of `CConceptProcessingQueue::CConceptProcessingQueue`.
    pub fn new() -> Self {
        ConceptProcessingQueue {
            max_priority_index: -1,
            priority_vec: [ConceptProcessingPriorityQueueData::new(); CONCEPT_QUEUE_MAX_INDEX],
            des_count: 0,
        }
    }

    /// Port of `CConceptProcessingQueue::initProcessingQueue`.
    pub fn init_processing_queue(&mut self, prev: Option<&ConceptProcessingQueue>) -> &mut Self {
        if let Some(p) = prev {
            self.max_priority_index = p.max_priority_index;
            self.des_count = p.des_count;
            for i in 0..CONCEPT_QUEUE_MAX_INDEX {
                self.priority_vec[i] = p.priority_vec[i];
                // mPrevSortedPriorityDescriptorLinker = prev->mSortedPriorityDescriptorLinker
                self.priority_vec[i].prev_sorted_linker = p.priority_vec[i].sorted_linker;
            }
        } else {
            self.max_priority_index = -1;
            self.des_count = 0;
            for i in 0..CONCEPT_QUEUE_MAX_INDEX {
                self.priority_vec[i] = ConceptProcessingPriorityQueueData::new();
            }
        }
        self
    }

    /// Port of `CConceptProcessingQueue::resetProcessingQueueModification`.
    pub fn reset_processing_queue_modification(&mut self) -> &mut Self {
        for i in 0..CONCEPT_QUEUE_MAX_INDEX {
            self.priority_vec[i].prev_sorted_linker = ConProcDescId::NONE;
        }
        self
    }

    /// Port of `CConceptProcessingQueue::getDescriptorCount`.
    pub fn get_descriptor_count(&self) -> Cint64 {
        self.des_count
    }
    /// Port of `CConceptProcessingQueue::hasProcessDescriptor`.
    pub fn has_process_descriptor(&self) -> bool {
        self.des_count > 0
    }
    /// Port of `CConceptProcessingQueue::isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.des_count <= 0
    }

    /// Port of `CConceptProcessingQueue::reinsertConceptProcessDescriptor`.
    pub fn reinsert_concept_process_descriptor(
        queue: ConceptProcessingQueueId,
        con_pro_des: ConProcDescId,
        ctx: &mut ProcessContext,
    ) {
        let priority = ctx.con_proc_desc(con_pro_des).get_process_priority().get_priority();
        let priority_index = priority as i64;
        {
            let q = ctx.concept_proc_queue_mut(queue);
            q.des_count += 1;
            if priority_index > q.max_priority_index {
                q.max_priority_index = priority_index;
            }
        }
        let idx = priority_index as usize;
        if priority == priority_index as f64 {
            ctx.concept_proc_queue_mut(queue).priority_vec[idx].default_linker = con_pro_des;
        } else {
            let prev_sorted = ctx.concept_proc_queue(queue).priority_vec[idx].prev_sorted_linker;
            let next = ctx.con_proc_desc(con_pro_des).get_next();
            ctx.concept_proc_queue_mut(queue).priority_vec[idx].sorted_linker = con_pro_des;
            if prev_sorted.is_some() && prev_sorted == next {
                ctx.concept_proc_queue_mut(queue).priority_vec[idx].prev_sorted_linker = con_pro_des;
            }
        }
    }

    /// Port of `CConceptProcessingQueue::insertConceptProcessDescriptor`.
    ///
    /// KONCLUDE-PORT-NOTE[memory-pool]: the sorted-chain COW localise branch
    /// (`mPrevSortedPriorityDescriptorLinker` -> `initCopy` a fresh local
    /// descriptor) is preserved; `new CConceptProcessDescriptor` becomes
    /// `ctx.alloc_con_proc_desc(...)`.
    pub fn insert_concept_process_descriptor(
        queue: ConceptProcessingQueueId,
        con_pro_des: ConProcDescId,
        ctx: &mut ProcessContext,
    ) {
        let priority = ctx.con_proc_desc(con_pro_des).get_process_priority().get_priority();
        let priority_index = priority as i64;
        {
            let q = ctx.concept_proc_queue_mut(queue);
            q.des_count += 1;
            if priority_index > q.max_priority_index {
                q.max_priority_index = priority_index;
            }
        }
        let idx = priority_index as usize;
        if priority == priority_index as f64 {
            // append to the default chain (prepend, head-front).
            let head = ctx.concept_proc_queue(queue).priority_vec[idx].default_linker;
            ctx.con_proc_desc_mut(con_pro_des).set_next(head);
            ctx.concept_proc_queue_mut(queue).priority_vec[idx].default_linker = con_pro_des;
        } else {
            let sorted_head = ctx.concept_proc_queue(queue).priority_vec[idx].sorted_linker;
            if sorted_head.is_none()
                || Self::descriptor_le(ctx, con_pro_des, sorted_head)
            {
                // insert to begin
                ctx.con_proc_desc_mut(con_pro_des).set_next(sorted_head);
                ctx.concept_proc_queue_mut(queue).priority_vec[idx].sorted_linker = con_pro_des;
            } else {
                let mut sorted_des_linker = sorted_head;
                let mut last_sorted: ConProcDescId = ConProcDescId::NONE;
                while sorted_des_linker.is_some()
                    && !Self::descriptor_le(ctx, con_pro_des, sorted_des_linker)
                {
                    let prev_sorted =
                        ctx.concept_proc_queue(queue).priority_vec[idx].prev_sorted_linker;
                    if sorted_des_linker == prev_sorted {
                        // make descriptor local (COW): copy `sorted_des_linker`.
                        let copy_src = sorted_des_linker;
                        // initCopy: a field-wise copy of `copy_src` (ConceptProcessDescriptor: Copy).
                        let src_val = *ctx.con_proc_desc(copy_src);
                        let new_local = ctx.alloc_con_proc_desc(src_val);

                        let prev_next = ctx.con_proc_desc(prev_sorted).get_next();
                        ctx.concept_proc_queue_mut(queue).priority_vec[idx].prev_sorted_linker =
                            prev_next;
                        sorted_des_linker = ctx.con_proc_desc(sorted_des_linker).get_next();

                        if last_sorted.is_some() {
                            ctx.con_proc_desc_mut(last_sorted).set_next(new_local);
                        } else {
                            ctx.concept_proc_queue_mut(queue).priority_vec[idx].sorted_linker =
                                new_local;
                        }
                        last_sorted = new_local;
                    } else {
                        last_sorted = sorted_des_linker;
                        sorted_des_linker = ctx.con_proc_desc(sorted_des_linker).get_next();
                    }
                }
                if last_sorted.is_some() {
                    ctx.con_proc_desc_mut(con_pro_des).set_next(sorted_des_linker);
                    ctx.con_proc_desc_mut(last_sorted).set_next(con_pro_des);
                }
            }
        }
    }

    /// Port of `CConceptProcessingQueue::takeNextConceptDescriptorProcess`.
    pub fn take_next_concept_descriptor_process(
        queue: ConceptProcessingQueueId,
        ctx: &mut ProcessContext,
    ) -> ConProcDescId {
        let mut con_pro_des: ConProcDescId = ConProcDescId::NONE;
        loop {
            let (des_count, max_index) = {
                let q = ctx.concept_proc_queue(queue);
                (q.des_count, q.max_priority_index)
            };
            if !(des_count > 0 && con_pro_des.is_none() && max_index >= 0) {
                break;
            }
            let idx = max_index as usize;
            let default_head = ctx.concept_proc_queue(queue).priority_vec[idx].default_linker;
            con_pro_des = default_head;
            if con_pro_des.is_some() {
                let next = ctx.con_proc_desc(con_pro_des).get_next();
                ctx.concept_proc_queue_mut(queue).priority_vec[idx].default_linker = next;
            } else {
                let sorted_head = ctx.concept_proc_queue(queue).priority_vec[idx].sorted_linker;
                con_pro_des = sorted_head;
                if con_pro_des.is_some() {
                    let prev_sorted =
                        ctx.concept_proc_queue(queue).priority_vec[idx].prev_sorted_linker;
                    if con_pro_des == prev_sorted {
                        let prev_next = ctx.con_proc_desc(prev_sorted).get_next();
                        ctx.concept_proc_queue_mut(queue).priority_vec[idx].prev_sorted_linker =
                            prev_next;
                    }
                    let next = ctx.con_proc_desc(con_pro_des).get_next();
                    ctx.concept_proc_queue_mut(queue).priority_vec[idx].sorted_linker = next;
                } else {
                    ctx.concept_proc_queue_mut(queue).max_priority_index -= 1;
                }
            }
        }
        if con_pro_des.is_some() {
            ctx.concept_proc_queue_mut(queue).des_count -= 1;
        }
        con_pro_des
    }

    /// Port of `CConceptProcessingQueue::getNextConceptProcessPriority`.
    /// Returns `Some(priority)` when a descriptor is available (the C++ `true`
    /// + out-param), `None` for the empty queue (the C++ `false`).
    pub fn get_next_concept_process_priority(
        queue: ConceptProcessingQueueId,
        ctx: &mut ProcessContext,
    ) -> Option<ConceptProcessPriority> {
        if ctx.concept_proc_queue(queue).des_count <= 0 {
            return None;
        }
        let mut con_pro_des: ConProcDescId = ConProcDescId::NONE;
        loop {
            let max_index = ctx.concept_proc_queue(queue).max_priority_index;
            if !(con_pro_des.is_none() && max_index >= 0) {
                break;
            }
            let idx = max_index as usize;
            con_pro_des = ctx.concept_proc_queue(queue).priority_vec[idx].default_linker;
            if con_pro_des.is_none() {
                con_pro_des = ctx.concept_proc_queue(queue).priority_vec[idx].sorted_linker;
                if con_pro_des.is_none() {
                    ctx.concept_proc_queue_mut(queue).max_priority_index -= 1;
                }
            }
        }
        if con_pro_des.is_none() {
            return None;
        }
        Some(ctx.con_proc_desc(con_pro_des).get_process_priority())
    }

    /// `*conProDes <= *sortedDesLinker` — `CConceptProcessDescriptor::operator<=`
    /// (`return descriptor.priority <= priority`, i.e. the *argument's* priority is
    /// `<=` the receiver's). Here receiver == `lhs`, argument == `rhs`.
    fn descriptor_le(ctx: &ProcessContext, lhs: ConProcDescId, rhs: ConProcDescId) -> bool {
        let lhs_pri = ctx.con_proc_desc(lhs).get_process_priority().get_priority();
        let rhs_pri = ctx.con_proc_desc(rhs).get_process_priority().get_priority();
        // operator<= : return descriptor(rhs).priority <= this(lhs).priority
        rhs_pri <= lhs_pri
    }
}

/// `CConceptProcessingQueue*` arena id.
pub type ConceptProcessingQueueId = Id<ConceptProcessingQueue>;
/// `CIndividualUnsortedProcessingQueue*` arena id.
pub type IndividualUnsortedProcessingQueueId = Id<IndividualUnsortedProcessingQueue>;
/// `CIndividualLinkerRotationProcessingQueue*` arena id.
pub type IndividualLinkerRotationProcessingQueueId = Id<IndividualLinkerRotationProcessingQueue>;
/// `CIndividualDepthProcessingQueue*` arena id.
pub type IndividualDepthProcessingQueueId = Id<IndividualDepthProcessingQueue>;
