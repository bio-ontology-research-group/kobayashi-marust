//! `process::queues` — the concept / individual **processing-queue subsystem**:
//! the triple-buffered queues that drive the completion engine's inner loop.
//!
//! Ports the workhorse `CIndividual*ProcessingQueue` family + the per-node
//! `CConceptProcessingQueue` from
//! `Source/Reasoner/Kernel/Process/`:
//!   * `CIndividualUnsortedProcessingQueue` (LIFO node linker)
//!   * `CIndividualLinkerRotationProcessingQueue` (two-stage process/rotation)
//!   * `CIndividualDepthProcessingQueue` (depth-priority ordered)
//!   * `CIndividualCustomPriorityProcessingQueue` (custom `double` priority map)
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

use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};
use std::mem;

use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::{Arena, Cint64, Id};
use super::super::model::ConceptId;
use super::context::ProcessContext;
use super::descriptor::{ConceptDescriptor, ConceptProcessDescriptor, ConceptProcessPriority};
use super::node::{IndividualProcessNode, IndividualProcessNodePriority};
use super::{ConDescId, ConProcDescId, NodeId};

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
        IndividualDepthPriority {
            indi_depth,
            indi_id,
        }
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
        IndividualUnsortedProcessingQueue {
            indi_pro_des_count: 0,
            linker: Vec::new(),
        }
    }

    /// Port of `CIndividualUnsortedProcessingQueue::initProcessingQueue`.
    pub fn init_processing_queue(
        &mut self,
        prev: Option<&IndividualUnsortedProcessingQueue>,
    ) -> &mut Self {
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
        self.processing_linker
            .last()
            .copied()
            .unwrap_or(NodeId::NONE)
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
    pub fn init_processing_queue(
        &mut self,
        prev: Option<&IndividualDepthProcessingQueue>,
    ) -> &mut Self {
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
            self.remaining_depth_map
                .entry(depth)
                .or_default()
                .push(individual);
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
// CIndividualProcessNodeDescriptor / CIndividualProcessingQueue.
// ===========================================================================

/// Port of `CIndividualProcessNodeDescriptor`.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct IndividualProcessNodeDescriptor {
    /// `ind`.
    pub individual: NodeId,
    /// `priority`.
    pub priority: IndividualProcessNodePriority,
}

impl Default for IndividualProcessNodeDescriptor {
    fn default() -> Self {
        IndividualProcessNodeDescriptor {
            individual: NodeId::NONE,
            priority: IndividualProcessNodePriority::default(),
        }
    }
}

impl IndividualProcessNodeDescriptor {
    /// Port of `CIndividualProcessNodeDescriptor::CIndividualProcessNodeDescriptor`.
    pub fn new(individual: NodeId, process_priority: IndividualProcessNodePriority) -> Self {
        IndividualProcessNodeDescriptor {
            individual,
            priority: process_priority,
        }
    }

    /// Port of `CIndividualProcessNodeDescriptor::init`.
    pub fn init(
        &mut self,
        individual: NodeId,
        process_priority: IndividualProcessNodePriority,
    ) -> &mut Self {
        self.individual = individual;
        self.priority = process_priority;
        self
    }

    /// Port of `CIndividualProcessNodeDescriptor::getIndividual`.
    pub fn get_individual(&self) -> NodeId {
        self.individual
    }

    /// Port of `CIndividualProcessNodeDescriptor::getProcessPriority`.
    pub fn get_process_priority(&self) -> IndividualProcessNodePriority {
        self.priority
    }

    /// Port of `operator<=`.
    pub fn le_descriptor(&self, descriptor: &Self) -> bool {
        descriptor.priority.le_priority(&self.priority)
    }
}

/// Ordered key for `CIndividualProcessingQueue`'s `insertMulti` priority map.
#[derive(Copy, Clone, Debug)]
pub struct IndividualProcessPriorityKey {
    pub priority: IndividualProcessNodePriority,
    pub insert_order: u64,
}

impl PartialEq for IndividualProcessPriorityKey {
    fn eq(&self, other: &Self) -> bool {
        !self.priority.lt_priority(&other.priority)
            && !other.priority.lt_priority(&self.priority)
            && self.insert_order == other.insert_order
    }
}

impl Eq for IndividualProcessPriorityKey {}

impl PartialOrd for IndividualProcessPriorityKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for IndividualProcessPriorityKey {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.priority.lt_priority(&other.priority) {
            Ordering::Less
        } else if other.priority.lt_priority(&self.priority) {
            Ordering::Greater
        } else {
            self.insert_order.cmp(&other.insert_order)
        }
    }
}

/// Port of `CIndividualProcessingQueue`.
#[derive(Clone, Debug)]
pub struct IndividualProcessingQueue {
    /// `mPriorityIndiDesMap`.
    pub priority_indi_des_map:
        BTreeMap<IndividualProcessPriorityKey, IndividualProcessNodeDescriptorId>,
    /// `mIndiDesPriorityHash`.
    pub indi_des_priority_hash: HashMap<Cint64, IndividualProcessNodePriority>,
    /// `mIndiProDesCount`.
    pub indi_pro_des_count: Cint64,
    /// `mHasMaxIndiPriority`.
    pub has_max_indi_priority: bool,
    /// `mMaxIndiPriority`.
    pub max_indi_priority: IndividualProcessNodePriority,
    /// `mLastCheckIndi`.
    pub last_check_indi: NodeId,
    /// `mLastCheckIndiPriority`.
    pub last_check_indi_priority: IndividualProcessNodePriority,
    next_insert_order: u64,
}

impl Default for IndividualProcessingQueue {
    fn default() -> Self {
        Self::new()
    }
}

impl IndividualProcessingQueue {
    /// Port of `CIndividualProcessingQueue::CIndividualProcessingQueue`.
    pub fn new() -> Self {
        IndividualProcessingQueue {
            priority_indi_des_map: BTreeMap::new(),
            indi_des_priority_hash: HashMap::new(),
            indi_pro_des_count: 0,
            has_max_indi_priority: false,
            max_indi_priority: IndividualProcessNodePriority::default(),
            last_check_indi: NodeId::NONE,
            last_check_indi_priority: IndividualProcessNodePriority::default(),
            next_insert_order: 0,
        }
    }

    /// Port of `CIndividualProcessingQueue::initProcessingQueue`.
    pub fn init_processing_queue(&mut self, prev: Option<&IndividualProcessingQueue>) -> &mut Self {
        if let Some(p) = prev {
            self.priority_indi_des_map = p.priority_indi_des_map.clone();
            self.indi_des_priority_hash = p.indi_des_priority_hash.clone();
            self.indi_pro_des_count = p.indi_pro_des_count;
            self.next_insert_order = p.next_insert_order;
        } else {
            self.priority_indi_des_map.clear();
            self.indi_des_priority_hash.clear();
            self.indi_pro_des_count = 0;
            self.next_insert_order = 0;
        }
        self.has_max_indi_priority = false;
        self.max_indi_priority = IndividualProcessNodePriority::default();
        self.last_check_indi = NodeId::NONE;
        self.last_check_indi_priority = IndividualProcessNodePriority::default();
        self
    }

    /// Port of `CIndividualProcessingQueue::insertIndiviudalProcessDescriptor`.
    pub fn insert_indiviudal_process_descriptor(
        &mut self,
        descs: &Arena<IndividualProcessNodeDescriptor>,
        nodes: &Arena<IndividualProcessNode>,
        indi_pro_des: IndividualProcessNodeDescriptorId,
    ) -> &mut Self {
        let descriptor = descs.get(indi_pro_des);
        let individual = descriptor.get_individual();
        let indi_priority = descriptor.get_process_priority();
        if individual == self.last_check_indi {
            if indi_priority.ge_priority(&self.last_check_indi_priority) {
                self.last_check_indi_priority = indi_priority;
            }
        }
        let indi_id = nodes.get(individual).individual_node_id();
        if self.has_max_indi_priority && indi_priority.ge_priority(&self.max_indi_priority) {
            self.max_indi_priority = indi_priority;
        }
        self.indi_des_priority_hash.insert(indi_id, indi_priority);
        let key = IndividualProcessPriorityKey {
            priority: indi_priority,
            insert_order: self.next_insert_order,
        };
        self.next_insert_order += 1;
        self.priority_indi_des_map.insert(key, indi_pro_des);
        self.indi_pro_des_count += 1;
        self
    }

    /// Port of `CIndividualProcessingQueue::isIndividualQueued`.
    pub fn is_individual_queued(
        &mut self,
        nodes: &Arena<IndividualProcessNode>,
        individual: NodeId,
    ) -> bool {
        let indi_id = nodes.get(individual).individual_node_id();
        self.last_check_indi_priority = self
            .indi_des_priority_hash
            .get(&indi_id)
            .copied()
            .unwrap_or_default();
        !self.last_check_indi_priority.is_null_priority()
    }

    /// Port of `CIndividualProcessingQueue::needsIndiviudalInsertion`.
    pub fn needs_indiviudal_insertion(
        &mut self,
        nodes: &Arena<IndividualProcessNode>,
        individual: NodeId,
        priority: IndividualProcessNodePriority,
    ) -> bool {
        if self.last_check_indi == individual {
            self.last_check_indi_priority.is_null_priority()
                || !priority.ge_priority(&self.last_check_indi_priority)
        } else {
            let indi_id = nodes.get(individual).individual_node_id();
            self.last_check_indi = individual;
            self.last_check_indi_priority = self
                .indi_des_priority_hash
                .get(&indi_id)
                .copied()
                .unwrap_or_default();
            self.last_check_indi_priority.is_null_priority()
                || !priority.ge_priority(&self.last_check_indi_priority)
        }
    }

    /// Port of `CIndividualProcessingQueue::hasHigherPriorityIndividual`.
    pub fn has_higher_priority_individual(
        &mut self,
        descs: &Arena<IndividualProcessNodeDescriptor>,
        priority: IndividualProcessNodePriority,
    ) -> bool {
        if !self.has_max_indi_priority {
            let next_indi_des = self.get_next_process_individual_descriptor();
            if next_indi_des.is_some() {
                self.max_indi_priority = descs.get(next_indi_des).get_process_priority();
                self.has_max_indi_priority = true;
            }
        }
        self.has_max_indi_priority && self.max_indi_priority.lt_priority(&priority)
    }

    /// Port of `CIndividualProcessingQueue::takeNextProcessIndividualDescriptor`.
    pub fn take_next_process_individual_descriptor(
        &mut self,
        descs: &Arena<IndividualProcessNodeDescriptor>,
        nodes: &Arena<IndividualProcessNode>,
    ) -> IndividualProcessNodeDescriptorId {
        let mut indi_pro_des = IndividualProcessNodeDescriptorId::NONE;
        if self.indi_pro_des_count > 0 {
            self.indi_pro_des_count -= 1;
            if let Some(priority) = self.priority_indi_des_map.keys().next().copied() {
                if let Some(desc) = self.priority_indi_des_map.remove(&priority) {
                    indi_pro_des = desc;
                    let indi = descs.get(desc).get_individual();
                    let indi_id = nodes.get(indi).individual_node_id();
                    self.indi_des_priority_hash
                        .insert(indi_id, IndividualProcessNodePriority::default());
                    self.last_check_indi = NodeId::NONE;
                }
            }
        }
        self.has_max_indi_priority = false;
        indi_pro_des
    }

    /// Port of `CIndividualProcessingQueue::getNextProcessIndividualDescriptor`.
    pub fn get_next_process_individual_descriptor(&self) -> IndividualProcessNodeDescriptorId {
        self.priority_indi_des_map
            .iter()
            .next()
            .map(|(_, desc)| *desc)
            .unwrap_or(IndividualProcessNodeDescriptorId::NONE)
    }

    /// Port of `CIndividualProcessingQueue::isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.indi_pro_des_count <= 0
    }

    /// Port of `CIndividualProcessingQueue::hasIndividualProcessDescriptor`.
    pub fn has_individual_process_descriptor(&self) -> bool {
        self.indi_pro_des_count > 0
    }
}

// ===========================================================================
// CIndividualReactivationProcessingQueue — completion-cache reactivation queue.
// ===========================================================================

/// One value of `CIndividualReactivationProcessingQueue::CIndividualForceReactivationData`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct IndividualForceReactivationData {
    /// `mForceReactivation`.
    pub force_reactivation: bool,
    /// `mIndiNode`.
    pub indi_node: NodeId,
}

impl IndividualForceReactivationData {
    /// Port of `CIndividualForceReactivationData::CIndividualForceReactivationData`.
    pub fn new(indi_node: NodeId, force_reactivation: bool) -> Self {
        IndividualForceReactivationData {
            force_reactivation,
            indi_node,
        }
    }
}

impl Default for IndividualForceReactivationData {
    fn default() -> Self {
        IndividualForceReactivationData {
            force_reactivation: false,
            indi_node: NodeId::NONE,
        }
    }
}

/// Port of `CIndividualReactivationProcessingQueue`.
#[derive(Clone, Debug, Default)]
pub struct IndividualReactivationProcessingQueue {
    /// `mPriorityIndiReactivationMap`.
    pub priority_indi_reactivation_map:
        BTreeMap<IndividualDepthPriority, IndividualForceReactivationData>,
}

impl IndividualReactivationProcessingQueue {
    /// Port of `CIndividualReactivationProcessingQueue::CIndividualReactivationProcessingQueue`.
    pub fn new() -> Self {
        IndividualReactivationProcessingQueue {
            priority_indi_reactivation_map: BTreeMap::new(),
        }
    }

    /// Port of `CIndividualReactivationProcessingQueue::initProcessingQueue`.
    pub fn init_processing_queue(
        &mut self,
        prev: Option<&IndividualReactivationProcessingQueue>,
    ) -> &mut Self {
        if let Some(p) = prev {
            self.priority_indi_reactivation_map = p.priority_indi_reactivation_map.clone();
        } else {
            self.priority_indi_reactivation_map.clear();
        }
        self
    }

    /// Port of `CIndividualReactivationProcessingQueue::takeNextReactivationIndividual`.
    pub fn take_next_reactivation_individual(&mut self) -> Option<(NodeId, bool)> {
        let priority = self.priority_indi_reactivation_map.keys().next().copied()?;
        let data = self.priority_indi_reactivation_map.remove(&priority)?;
        Some((data.indi_node, data.force_reactivation))
    }

    /// Port of `CIndividualReactivationProcessingQueue::getNextReactivationIndividual`.
    pub fn get_next_reactivation_individual(&self) -> Option<(NodeId, bool)> {
        self.priority_indi_reactivation_map
            .iter()
            .next()
            .map(|(_, data)| (data.indi_node, data.force_reactivation))
    }

    /// Port of `CIndividualReactivationProcessingQueue::insertReactivationIndiviudal`.
    pub fn insert_reactivation_indiviudal(
        &mut self,
        nodes: &Arena<IndividualProcessNode>,
        individual: NodeId,
        force_reactivation: bool,
    ) -> bool {
        let node = nodes.get(individual);
        let priority = IndividualDepthPriority::new(
            node.individual_nominal_level_or_ancestor_depth(),
            node.individual_node_id(),
        );
        let data = self
            .priority_indi_reactivation_map
            .entry(priority)
            .or_default();
        let new_entry = data.indi_node.is_none() || !data.force_reactivation && force_reactivation;
        data.force_reactivation = force_reactivation;
        data.indi_node = individual;
        new_entry
    }

    /// Port of `CIndividualReactivationProcessingQueue::hasQueuedIndividual`.
    pub fn has_queued_individual(
        &self,
        nodes: &Arena<IndividualProcessNode>,
        individual: NodeId,
    ) -> bool {
        if self.priority_indi_reactivation_map.is_empty() {
            return false;
        }
        let node = nodes.get(individual);
        let priority = IndividualDepthPriority::new(
            node.individual_nominal_level_or_ancestor_depth(),
            node.individual_node_id(),
        );
        self.priority_indi_reactivation_map.contains_key(&priority)
    }

    /// Port of `CIndividualReactivationProcessingQueue::isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.priority_indi_reactivation_map.is_empty()
    }

    /// Port of `CIndividualReactivationProcessingQueue::getQueuedIndividualCount`.
    pub fn get_queued_individual_count(&self) -> Cint64 {
        self.priority_indi_reactivation_map.len() as Cint64
    }

    /// Port of `CIndividualReactivationProcessingQueue::hasQueuedIndividuals`.
    pub fn has_queued_individuals(&self) -> bool {
        !self.priority_indi_reactivation_map.is_empty()
    }
}

// ===========================================================================
// CIndividualDepthConceptProcessDescriptorProcessingQueue.
// ===========================================================================

/// One value of `CIndividualDepthConceptProcessDescriptorProcessingQueueData`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct IndividualDepthConceptProcessDescriptorProcessingQueueData {
    /// `mConProDes`.
    pub con_pro_des: ConProcDescId,
    /// `mIndiNode`.
    pub indi_node: NodeId,
}

impl IndividualDepthConceptProcessDescriptorProcessingQueueData {
    /// Port of the value ctor.
    pub fn new(con_pro_des: ConProcDescId, indi_node: NodeId) -> Self {
        IndividualDepthConceptProcessDescriptorProcessingQueueData {
            con_pro_des,
            indi_node,
        }
    }
}

impl Default for IndividualDepthConceptProcessDescriptorProcessingQueueData {
    fn default() -> Self {
        IndividualDepthConceptProcessDescriptorProcessingQueueData {
            con_pro_des: ConProcDescId::NONE,
            indi_node: NodeId::NONE,
        }
    }
}

/// Port of `CIndividualDepthConceptProcessDescriptorProcessingQueue`.
///
/// `CPROCESSMAP<CIndividualDepthPriority,...>` is represented as an ordered map
/// to buckets. `insert` replaces the bucket for unrestricted descriptors; Konclude
/// uses `insertMulti` only when a processing restriction is present, which appends
/// another value at the same depth/id key.
#[derive(Clone, Debug, Default)]
pub struct IndividualDepthConceptProcessDescriptorProcessingQueue {
    /// `mPriorityIndiDesMap`.
    pub priority_indi_des_map: BTreeMap<
        IndividualDepthPriority,
        Vec<IndividualDepthConceptProcessDescriptorProcessingQueueData>,
    >,
    /// Cached `mPriorityIndiDesMap.count()`.
    pub queued_individual_count: Cint64,
}

impl IndividualDepthConceptProcessDescriptorProcessingQueue {
    /// Port of the ctor.
    pub fn new() -> Self {
        IndividualDepthConceptProcessDescriptorProcessingQueue {
            priority_indi_des_map: BTreeMap::new(),
            queued_individual_count: 0,
        }
    }

    /// Port of `initProcessingQueue`.
    pub fn init_processing_queue(
        &mut self,
        prev: Option<&IndividualDepthConceptProcessDescriptorProcessingQueue>,
    ) -> &mut Self {
        if let Some(p) = prev {
            self.priority_indi_des_map = p.priority_indi_des_map.clone();
            self.queued_individual_count = p.queued_individual_count;
        } else {
            self.priority_indi_des_map.clear();
            self.queued_individual_count = 0;
        }
        self
    }

    /// Port of `takeNextProcessIndiviudalConceptProcessDescriptor`.
    pub fn take_next_process_indiviudal_concept_process_descriptor(
        &mut self,
    ) -> Option<(NodeId, ConProcDescId)> {
        let priority = self.priority_indi_des_map.keys().next().copied()?;
        let (entry, remove_bucket) = {
            let bucket = self.priority_indi_des_map.get_mut(&priority).unwrap();
            let entry = bucket.remove(0);
            (entry, bucket.is_empty())
        };
        if remove_bucket {
            self.priority_indi_des_map.remove(&priority);
        }
        self.queued_individual_count -= 1;
        Some((entry.indi_node, entry.con_pro_des))
    }

    /// Port of `getNextProcessIndiviudalConceptProcessDescriptor`.
    pub fn get_next_process_indiviudal_concept_process_descriptor(
        &self,
    ) -> Option<(NodeId, ConProcDescId)> {
        self.priority_indi_des_map
            .iter()
            .next()
            .and_then(|(_, bucket)| bucket.first().copied())
            .map(|entry| (entry.indi_node, entry.con_pro_des))
    }

    /// Port of `insertProcessIndiviudalConceptProcessDescriptor`.
    pub fn insert_process_indiviudal_concept_process_descriptor(
        &mut self,
        nodes: &Arena<IndividualProcessNode>,
        con_proc_descs: &Arena<ConceptProcessDescriptor>,
        individual: NodeId,
        con_pro_des: ConProcDescId,
    ) -> &mut Self {
        let node = nodes.get(individual);
        let priority = IndividualDepthPriority::new(
            node.individual_nominal_level_or_ancestor_depth(),
            node.individual_node_id(),
        );
        let entry = IndividualDepthConceptProcessDescriptorProcessingQueueData::new(
            con_pro_des,
            individual,
        );
        if con_proc_descs
            .get(con_pro_des)
            .get_processing_restriction_specification()
            .is_some()
        {
            self.priority_indi_des_map
                .entry(priority)
                .or_default()
                .push(entry);
            self.queued_individual_count += 1;
        } else {
            let old_len = self
                .priority_indi_des_map
                .insert(priority, vec![entry])
                .map(|bucket| bucket.len() as Cint64)
                .unwrap_or(0);
            self.queued_individual_count += 1 - old_len;
        }
        self
    }

    /// Port of `removeQueuedProcessIndiviudal`.
    pub fn remove_queued_process_indiviudal(
        &mut self,
        nodes: &Arena<IndividualProcessNode>,
        individual: NodeId,
    ) -> ConProcDescId {
        let node = nodes.get(individual);
        let priority = IndividualDepthPriority::new(
            node.individual_nominal_level_or_ancestor_depth(),
            node.individual_node_id(),
        );
        let Some(bucket) = self.priority_indi_des_map.get_mut(&priority) else {
            return ConProcDescId::NONE;
        };
        let entry = bucket.remove(0);
        let remove_bucket = bucket.is_empty();
        if remove_bucket {
            self.priority_indi_des_map.remove(&priority);
        }
        self.queued_individual_count -= 1;
        entry.con_pro_des
    }

    /// Port of `isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.queued_individual_count <= 0
    }

    /// Port of `getQueuedIndividualCount`.
    pub fn get_queued_individual_count(&self) -> Cint64 {
        self.queued_individual_count
    }

    /// Port of `hasQueuedIndividuals`.
    pub fn has_queued_individuals(&self) -> bool {
        self.queued_individual_count > 0
    }

    /// Port of `isIndividualQueued`.
    pub fn is_individual_queued(
        &self,
        nodes: &Arena<IndividualProcessNode>,
        individual: NodeId,
    ) -> bool {
        let node = nodes.get(individual);
        let priority = IndividualDepthPriority::new(
            node.individual_nominal_level_or_ancestor_depth(),
            node.individual_node_id(),
        );
        self.priority_indi_des_map.contains_key(&priority)
    }
}

// ===========================================================================
// CIndividualConceptBatchProcessingData / Queue.
// ===========================================================================

/// Port of `CIndividualConceptBatchProcessingData`.
#[derive(Clone, Debug)]
pub struct IndividualConceptBatchProcessingData {
    /// `mIndividualQueue`.
    pub individual_queue: IndividualDepthConceptProcessDescriptorProcessingQueue,
    /// `mConcept`.
    pub concept: ConceptId,
}

impl Default for IndividualConceptBatchProcessingData {
    fn default() -> Self {
        Self::new()
    }
}

impl IndividualConceptBatchProcessingData {
    /// Port of the ctor.
    pub fn new() -> Self {
        IndividualConceptBatchProcessingData {
            individual_queue: IndividualDepthConceptProcessDescriptorProcessingQueue::new(),
            concept: ConceptId::NONE,
        }
    }

    /// Port of `initConceptBatchProcessingData`.
    pub fn init_concept_batch_processing_data(
        &mut self,
        prev: Option<&IndividualConceptBatchProcessingData>,
    ) -> &mut Self {
        if let Some(p) = prev {
            self.individual_queue
                .init_processing_queue(Some(&p.individual_queue));
            self.concept = p.concept;
        } else {
            self.individual_queue.init_processing_queue(None);
            self.concept = ConceptId::NONE;
        }
        self
    }

    /// Port of `getIndividualQueue`.
    pub fn get_individual_queue(
        &mut self,
    ) -> &mut IndividualDepthConceptProcessDescriptorProcessingQueue {
        &mut self.individual_queue
    }

    /// Port of `getConcept`.
    pub fn get_concept(&self) -> ConceptId {
        self.concept
    }

    /// Port of `hasConcept`.
    pub fn has_concept(&self) -> bool {
        self.concept.is_some()
    }

    /// Port of `setConcept`.
    pub fn set_concept(&mut self, concept: ConceptId) -> &mut Self {
        self.concept = concept;
        self
    }
}

/// The nested queue-map value in `CIndividualConceptBatchProcessingQueue`.
#[derive(Clone, Debug, Default)]
pub struct IndividualConceptBatchProcessingQueueData {
    /// `mUseProcData`.
    pub use_proc_data: Option<IndividualConceptBatchProcessingData>,
    /// `mLocProcData`.
    pub loc_proc_data: bool,
}

impl IndividualConceptBatchProcessingQueueData {
    fn localized(&mut self) -> &mut IndividualConceptBatchProcessingData {
        if !self.loc_proc_data {
            let prev = self.use_proc_data.clone();
            let mut data = IndividualConceptBatchProcessingData::new();
            data.init_concept_batch_processing_data(prev.as_ref());
            self.use_proc_data = Some(data);
            self.loc_proc_data = true;
        }
        self.use_proc_data.as_mut().unwrap()
    }
}

/// The queued state for one `(conceptTag, individualID)` binding-count entry.
#[derive(Copy, Clone, Debug)]
pub struct IndividualConceptQueuedData {
    /// `mPrevTag`.
    pub prev_tag: Cint64,
    /// `mQueued`.
    pub queued: bool,
}

impl Default for IndividualConceptQueuedData {
    fn default() -> Self {
        IndividualConceptQueuedData {
            prev_tag: 0,
            queued: false,
        }
    }
}

/// Port of `CIndividualConceptBatchProcessingQueue`.
#[derive(Clone, Debug, Default)]
pub struct IndividualConceptBatchProcessingQueue {
    /// `mCurrentProcessingTag`.
    pub current_processing_tag: Cint64,
    /// `mUseCurrentProcessingQueue`.
    pub use_current_processing_queue: Option<IndividualConceptBatchProcessingData>,
    /// `mLocCurrentProcessingQueue`.
    pub loc_current_processing_queue: bool,
    /// `mConceptIndiQueueMap`.
    pub concept_indi_queue_map: BTreeMap<Cint64, IndividualConceptBatchProcessingQueueData>,
    /// `mBindCountIndiQueueMap`.
    pub bind_count_indi_queue_map: BTreeMap<Cint64, IndividualConceptBatchProcessingQueueData>,
    /// `mBindindBasedQueuedCount` (spelling preserved from upstream).
    pub bindind_based_queued_count: Cint64,
    /// `mBindCountIndiQueuedHash`.
    pub bind_count_indi_queued_hash: HashMap<(Cint64, Cint64), IndividualConceptQueuedData>,
}

impl IndividualConceptBatchProcessingQueue {
    /// Port of the ctor.
    pub fn new() -> Self {
        IndividualConceptBatchProcessingQueue {
            current_processing_tag: -1,
            use_current_processing_queue: None,
            loc_current_processing_queue: false,
            concept_indi_queue_map: BTreeMap::new(),
            bind_count_indi_queue_map: BTreeMap::new(),
            bindind_based_queued_count: 0,
            bind_count_indi_queued_hash: HashMap::new(),
        }
    }

    /// Port of `initProcessingQueue`.
    pub fn init_processing_queue(
        &mut self,
        prev: Option<&IndividualConceptBatchProcessingQueue>,
    ) -> &mut Self {
        if let Some(p) = prev {
            self.concept_indi_queue_map = p.concept_indi_queue_map.clone();
            self.bind_count_indi_queue_map = p.bind_count_indi_queue_map.clone();
            self.use_current_processing_queue = p.use_current_processing_queue.clone();
            self.current_processing_tag = p.current_processing_tag;
            self.loc_current_processing_queue = false;
            self.bindind_based_queued_count = p.bindind_based_queued_count;
            self.bind_count_indi_queued_hash = p.bind_count_indi_queued_hash.clone();
        } else {
            self.concept_indi_queue_map.clear();
            self.bind_count_indi_queue_map.clear();
            self.use_current_processing_queue = None;
            self.loc_current_processing_queue = false;
            self.current_processing_tag = -1;
            self.bindind_based_queued_count = 0;
            self.bind_count_indi_queued_hash.clear();
        }
        self
    }

    /// Port of `isEmpty`.
    pub fn is_empty(&self) -> bool {
        if self.bindind_based_queued_count > 0 {
            return false;
        }
        if let Some(data) = &self.use_current_processing_queue {
            if !data.individual_queue.is_empty() {
                return false;
            }
        }
        for data in self.concept_indi_queue_map.values() {
            if let Some(proc_data) = &data.use_proc_data {
                if !proc_data.individual_queue.is_empty() {
                    return false;
                }
            }
        }
        true
    }

    fn localize_current(&mut self) {
        if !self.loc_current_processing_queue {
            let prev = self.use_current_processing_queue.clone();
            let mut data = IndividualConceptBatchProcessingData::new();
            data.init_concept_batch_processing_data(prev.as_ref());
            self.use_current_processing_queue = Some(data);
            self.loc_current_processing_queue = true;
        }
    }

    /// Port of `takeNextConceptProcessIndividual`.
    pub fn take_next_concept_process_individual(
        &mut self,
        nodes: &Arena<IndividualProcessNode>,
        con_proc_descs: &Arena<ConceptProcessDescriptor>,
        con_descs: &Arena<ConceptDescriptor>,
        onto: &OntologyArenas,
    ) -> Option<(ConceptId, NodeId, ConProcDescId)> {
        if self.use_current_processing_queue.is_none() {
            if self.bindind_based_queued_count > 0 {
                let keys: Vec<Cint64> = self.bind_count_indi_queue_map.keys().copied().collect();
                for key in keys {
                    let non_empty = self
                        .bind_count_indi_queue_map
                        .get(&key)
                        .and_then(|data| data.use_proc_data.as_ref())
                        .is_some_and(|data| !data.individual_queue.is_empty());
                    if non_empty {
                        let data = self.bind_count_indi_queue_map.get_mut(&key).unwrap();
                        let proc_data = data.localized();
                        if let Some((indi_node, con_pro_des)) = proc_data
                            .individual_queue
                            .take_next_process_indiviudal_concept_process_descriptor()
                        {
                            let indi_id = nodes.get(indi_node).individual_node_id();
                            let con_tag = concept_tag_for_process_descriptor(
                                con_proc_descs,
                                con_descs,
                                onto,
                                con_pro_des,
                            );
                            self.bind_count_indi_queued_hash
                                .entry((con_tag, indi_id))
                                .or_default()
                                .queued = false;
                            self.bindind_based_queued_count -= 1;
                            return Some((ConceptId::NONE, indi_node, con_pro_des));
                        }
                    }
                }
                self.bindind_based_queued_count = 0;
            }

            if !self.concept_indi_queue_map.is_empty() {
                while self
                    .use_current_processing_queue
                    .as_ref()
                    .is_none_or(|data| data.individual_queue.is_empty())
                {
                    let Some((&key, _)) = self.concept_indi_queue_map.iter().next() else {
                        break;
                    };
                    let data = self.concept_indi_queue_map.remove(&key).unwrap();
                    self.current_processing_tag = key;
                    self.use_current_processing_queue = data.use_proc_data;
                    self.loc_current_processing_queue = data.loc_proc_data;
                }
            }
        }

        if self.use_current_processing_queue.is_some() {
            let queued_indi_count = self
                .use_current_processing_queue
                .as_ref()
                .unwrap()
                .individual_queue
                .get_queued_individual_count();
            if queued_indi_count > 1 {
                self.localize_current();
                let proc_data = self.use_current_processing_queue.as_mut().unwrap();
                return proc_data
                    .individual_queue
                    .take_next_process_indiviudal_concept_process_descriptor()
                    .map(|(indi_node, con_pro_des)| (proc_data.concept, indi_node, con_pro_des));
            } else if queued_indi_count == 1 {
                let (concept, next) = {
                    let proc_data = self.use_current_processing_queue.as_ref().unwrap();
                    (
                        proc_data.concept,
                        proc_data
                            .individual_queue
                            .get_next_process_indiviudal_concept_process_descriptor(),
                    )
                };
                self.use_current_processing_queue = None;
                self.loc_current_processing_queue = false;
                self.current_processing_tag = -1;
                return next.map(|(indi_node, con_pro_des)| (concept, indi_node, con_pro_des));
            } else {
                self.use_current_processing_queue = None;
                self.loc_current_processing_queue = false;
                self.current_processing_tag = -1;
            }
        }
        Some((ConceptId::NONE, NodeId::NONE, ConProcDescId::NONE))
    }

    /// Port of `insertIndiviudalForConcept`.
    pub fn insert_indiviudal_for_concept(
        &mut self,
        nodes: &Arena<IndividualProcessNode>,
        con_proc_descs: &Arena<ConceptProcessDescriptor>,
        onto: &OntologyArenas,
        concept: ConceptId,
        individual: NodeId,
        con_pro_des: ConProcDescId,
    ) -> &mut Self {
        let con_tag = onto.concept(concept).get_concept_tag();
        let proc_data = self
            .get_batch_processing_data_for_tag(concept, con_tag, true)
            .unwrap();
        proc_data
            .individual_queue
            .insert_process_indiviudal_concept_process_descriptor(
                nodes,
                con_proc_descs,
                individual,
                con_pro_des,
            );
        self
    }

    /// Port of `insertIndiviudalForBindingCount`.
    pub fn insert_indiviudal_for_binding_count(
        &mut self,
        nodes: &Arena<IndividualProcessNode>,
        con_proc_descs: &Arena<ConceptProcessDescriptor>,
        con_descs: &Arena<ConceptDescriptor>,
        onto: &OntologyArenas,
        _concept: ConceptId,
        bind_count: Cint64,
        individual: NodeId,
        con_pro_des: ConProcDescId,
    ) -> &mut Self {
        let con_tag =
            concept_tag_for_process_descriptor(con_proc_descs, con_descs, onto, con_pro_des);
        let indi_id = nodes.get(individual).individual_node_id();
        let queued_data = self
            .bind_count_indi_queued_hash
            .entry((con_tag, indi_id))
            .or_default();
        if !queued_data.queued || bind_count > queued_data.prev_tag {
            let was_queued = queued_data.queued;
            let prev_tag = queued_data.prev_tag;
            if was_queued {
                loop {
                    let prev_con_pro_des = {
                        let prev_proc_data =
                            self.get_batch_processing_data_for_binding_count(prev_tag, true);
                        prev_proc_data
                            .unwrap()
                            .individual_queue
                            .remove_queued_process_indiviudal(nodes, individual)
                    };
                    if prev_con_pro_des.is_none() {
                        break;
                    }
                    if con_proc_descs
                        .get(prev_con_pro_des)
                        .get_processing_restriction_specification()
                        .is_some()
                    {
                        let proc_data =
                            self.get_batch_processing_data_for_binding_count(bind_count, true);
                        proc_data
                            .unwrap()
                            .individual_queue
                            .insert_process_indiviudal_concept_process_descriptor(
                                nodes,
                                con_proc_descs,
                                individual,
                                prev_con_pro_des,
                            );
                    }
                }
            } else {
                self.bindind_based_queued_count += 1;
            }
            let proc_data = self
                .get_batch_processing_data_for_binding_count(bind_count, true)
                .unwrap();
            proc_data
                .individual_queue
                .insert_process_indiviudal_concept_process_descriptor(
                    nodes,
                    con_proc_descs,
                    individual,
                    con_pro_des,
                );
            let queued_data = self
                .bind_count_indi_queued_hash
                .entry((con_tag, indi_id))
                .or_default();
            queued_data.prev_tag = bind_count;
            queued_data.queued = true;
        }
        self
    }

    /// Port of `getBatchProcessingData(CConcept*, bool)`.
    pub fn get_batch_processing_data_for_tag(
        &mut self,
        concept: ConceptId,
        con_tag: Cint64,
        create_and_localize: bool,
    ) -> Option<&mut IndividualConceptBatchProcessingData> {
        if create_and_localize {
            let data = self.concept_indi_queue_map.entry(con_tag).or_default();
            let proc_data = data.localized();
            proc_data.set_concept(concept);
            Some(proc_data)
        } else {
            self.concept_indi_queue_map
                .get_mut(&con_tag)
                .and_then(|data| data.use_proc_data.as_mut())
        }
    }

    /// Port of `getBatchProcessingData(CConcept*, cint64, bool)`.
    pub fn get_batch_processing_data_for_binding_count(
        &mut self,
        bind_count: Cint64,
        create_and_localize: bool,
    ) -> Option<&mut IndividualConceptBatchProcessingData> {
        let processing_tag = -bind_count;
        if create_and_localize {
            if self.current_processing_tag == processing_tag {
                self.localize_current();
                self.use_current_processing_queue.as_mut()
            } else {
                Some(
                    self.bind_count_indi_queue_map
                        .entry(processing_tag)
                        .or_default()
                        .localized(),
                )
            }
        } else if self.current_processing_tag == processing_tag {
            self.use_current_processing_queue.as_mut()
        } else {
            self.bind_count_indi_queue_map
                .get_mut(&processing_tag)
                .and_then(|data| data.use_proc_data.as_mut())
        }
    }
}

fn concept_tag_for_process_descriptor(
    con_proc_descs: &Arena<ConceptProcessDescriptor>,
    con_descs: &Arena<ConceptDescriptor>,
    onto: &OntologyArenas,
    con_pro_des: ConProcDescId,
) -> Cint64 {
    let con_des: ConDescId = con_proc_descs.get(con_pro_des).get_concept_descriptor();
    con_descs.get(con_des).get_concept_tag(onto)
}

// ===========================================================================
// CIndividualCustomPriorityProcessingQueue — ordered custom-priority map.
// ===========================================================================

/// Ordered `double` key used by `CIndividualCustomPriorityProcessingQueue`.
///
/// Konclude's `CPROCESSMAP<double,...>` orders by numeric `double`. The current
/// producer (`getNextIncrementalExpansionPriority`) generates finite values, so
/// NaN is not expected; if one appears, keep map ordering stable via the bit
/// pattern instead of panicking.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct CustomPriorityKey(pub f64);

impl Eq for CustomPriorityKey {}

impl PartialOrd for CustomPriorityKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CustomPriorityKey {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .partial_cmp(&other.0)
            .unwrap_or_else(|| self.0.to_bits().cmp(&other.0.to_bits()))
    }
}

/// Port of `CIndividualCustomPriorityProcessingQueue`.
///
/// `CPROCESSMAP<double,CIndividualProcessNode*>::insertMulti` becomes an ordered
/// map from priority to a bucket of node ids. `begin()` maps to the smallest key
/// and the first node in that bucket.
#[derive(Clone, Debug, Default)]
pub struct IndividualCustomPriorityProcessingQueue {
    /// `mPriorityIndiMap`.
    pub priority_indi_map: BTreeMap<CustomPriorityKey, Vec<NodeId>>,
    /// Cached equivalent of `mPriorityIndiMap.count()`.
    pub queued_individual_count: Cint64,
}

impl IndividualCustomPriorityProcessingQueue {
    /// Port of the ctor.
    pub fn new() -> Self {
        IndividualCustomPriorityProcessingQueue {
            priority_indi_map: BTreeMap::new(),
            queued_individual_count: 0,
        }
    }

    /// Port of `initProcessingQueue`.
    pub fn init_processing_queue(
        &mut self,
        prev: Option<&IndividualCustomPriorityProcessingQueue>,
    ) -> &mut Self {
        if let Some(p) = prev {
            self.priority_indi_map = p.priority_indi_map.clone();
            self.queued_individual_count = p.queued_individual_count;
        } else {
            self.priority_indi_map.clear();
            self.queued_individual_count = 0;
        }
        self
    }

    /// Port of `takeNextProcessIndividual`.
    pub fn take_next_process_individual(&mut self) -> NodeId {
        let Some(priority) = self.priority_indi_map.keys().next().copied() else {
            return NodeId::NONE;
        };
        let (next_node, remove_bucket) = {
            let bucket = self.priority_indi_map.get_mut(&priority).unwrap();
            let next_node = bucket.first().copied().unwrap_or(NodeId::NONE);
            if next_node.is_some() {
                bucket.remove(0);
            }
            (next_node, bucket.is_empty())
        };
        if remove_bucket {
            self.priority_indi_map.remove(&priority);
        }
        if next_node.is_some() {
            self.queued_individual_count -= 1;
        }
        next_node
    }

    /// Port of `getNextProcessIndividual`.
    pub fn get_next_process_individual(&self) -> NodeId {
        self.priority_indi_map
            .iter()
            .next()
            .and_then(|(_, bucket)| bucket.first().copied())
            .unwrap_or(NodeId::NONE)
    }

    /// Port of `insertIndiviudal`.
    pub fn insert_indiviudal(&mut self, priority: f64, individual: NodeId) -> &mut Self {
        self.priority_indi_map
            .entry(CustomPriorityKey(priority))
            .or_default()
            .push(individual);
        self.queued_individual_count += 1;
        self
    }

    /// Port of `isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.queued_individual_count <= 0
    }

    /// Port of `getQueuedIndividualCount`.
    pub fn get_queued_individual_count(&self) -> Cint64 {
        self.queued_individual_count
    }

    /// Port of `hasQueuedIndividuals`.
    pub fn has_queued_individuals(&self) -> bool {
        self.queued_individual_count > 0
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
        let priority = ctx
            .con_proc_desc(con_pro_des)
            .get_process_priority()
            .get_priority();
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
                ctx.concept_proc_queue_mut(queue).priority_vec[idx].prev_sorted_linker =
                    con_pro_des;
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
        let priority = ctx
            .con_proc_desc(con_pro_des)
            .get_process_priority()
            .get_priority();
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
            if sorted_head.is_none() || Self::descriptor_le(ctx, con_pro_des, sorted_head) {
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
                    ctx.con_proc_desc_mut(con_pro_des)
                        .set_next(sorted_des_linker);
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
/// `CIndividualProcessNodeDescriptor*` arena id.
pub type IndividualProcessNodeDescriptorId = Id<IndividualProcessNodeDescriptor>;
/// `CIndividualProcessingQueue*` arena id.
pub type IndividualProcessingQueueId = Id<IndividualProcessingQueue>;
/// `CIndividualCustomPriorityProcessingQueue*` arena id.
pub type IndividualCustomPriorityProcessingQueueId = Id<IndividualCustomPriorityProcessingQueue>;
/// `CIndividualReactivationProcessingQueue*` arena id.
pub type IndividualReactivationProcessingQueueId = Id<IndividualReactivationProcessingQueue>;
/// `CIndividualDepthConceptProcessDescriptorProcessingQueue*` arena id.
pub type IndividualDepthConceptProcessDescriptorProcessingQueueId =
    Id<IndividualDepthConceptProcessDescriptorProcessingQueue>;
/// `CIndividualConceptBatchProcessingQueue*` arena id.
pub type IndividualConceptBatchProcessingQueueId = Id<IndividualConceptBatchProcessingQueue>;
