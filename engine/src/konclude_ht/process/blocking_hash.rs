//! `process::blocking_hash` — port unit **W3.5b**: the remaining blocking-family
//! satellites the signature / dynamic-blocking un-defers (`completion/u18`,
//! `u19`, `u20`, `u31`, `u35`) reach into.
//!
//! Sources (`Source/Reasoner/Kernel/Process/`):
//!   * `CBlockingIndividualNodeCandidateData.{h,cpp}`     → [`BlockingIndividualNodeCandidateData`]
//!   * `CBlockingIndividualNodeCandidateIterator.{h,cpp}` → [`BlockingIndividualNodeCandidateIterator`]
//!   * `CBlockingIndividualNodeCandidateHash.{h,cpp}`     → [`BlockingIndividualNodeCandidateHash`]
//!   * `CBlockingIndividualNodeLinker.{h,cpp}`            → [`BlockingIndividualNodeLinker`]
//!   * `CBlockingIndividualNodeLinkedCandidateData.{h,cpp}` → [`BlockingIndividualNodeLinkedCandidateData`]
//!   * `CBlockingIndividualNodeLinkedCandidateHash.{h,cpp}` → [`BlockingIndividualNodeLinkedCandidateHash`]
//!   * `CSignatureBlockingIndividualNodeConceptExpansionData.{h,cpp}`
//!                                                        → [`SignatureBlockingIndividualNodeConceptExpansionData`]
//!
//! The concrete `CBlockingAlternativeSignatureBlockingCandidateData` and the
//! `CSignatureBlockingCandidateHash` family were already ported in
//! `process::reapply_sat` (W2.7) — they are NOT duplicated here.
//!
//! KONCLUDE-PORT-NOTE[ownership]: every `CXxx*` becomes the matching `Id<T>`;
//! the `CPROCESSHASH<QPair<CConcept*,bool>,…>` candidate hash becomes an owned
//! `HashMap<(ConceptId,bool),…>` (`Id<T>` is `Hash`/`Eq` regardless of `T`); the
//! ordered `CPROCESSMAP<cint64,CIndividualProcessNode*>` candidate map (the
//! iterator calls `upperBound`) becomes an owned `BTreeMap<Cint64,NodeId>`. The
//! hashes/datas are themselves arena elements on `ProcessContext`, so the
//! allocate-a-child methods are associated fns over `(ctx, this, …)` (the
//! `binding_hash` precedent); the same-arena `init…(prev)` borrow is resolved with
//! `mem::replace` (lift parent out, init, restore).

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::ConceptId;
use super::context::ProcessContext;
use super::satellites::ConceptLabelSetModificationTag;
use super::{ConDescId, NodeId, TrackPointId};

// ===========================================================================
// id aliases
// ===========================================================================

/// `CBlockingIndividualNodeCandidateHash*` → `BlockingIndividualNodeCandidateHashId`.
pub type BlockingIndividualNodeCandidateHashId = Id<BlockingIndividualNodeCandidateHash>;
/// `CBlockingIndividualNodeCandidateData*` → `BlockingIndividualNodeCandidateDataId`.
pub type BlockingIndividualNodeCandidateDataId = Id<BlockingIndividualNodeCandidateData>;
/// `CBlockingIndividualNodeLinker*` → `BlockingIndividualNodeLinkerId`.
pub type BlockingIndividualNodeLinkerId = Id<BlockingIndividualNodeLinker>;
/// `CBlockingIndividualNodeLinkedCandidateData*` →
/// `BlockingIndividualNodeLinkedCandidateDataId`.
pub type BlockingIndividualNodeLinkedCandidateDataId =
    Id<BlockingIndividualNodeLinkedCandidateData>;
/// `CBlockingIndividualNodeLinkedCandidateHash*` →
/// `BlockingIndividualNodeLinkedCandidateHashId`.
pub type BlockingIndividualNodeLinkedCandidateHashId =
    Id<BlockingIndividualNodeLinkedCandidateHash>;
/// `CSignatureBlockingIndividualNodeConceptExpansionData*` →
/// `SignatureBlockingIndividualNodeConceptExpansionDataId`.
/// KONCLUDE-PORT-NOTE[ownership]: reconciles the W2 `process::stubs`
/// `SignatureBlockingIndividualNodeConceptExpansionData => SigBlockConExpDataId`
/// marker (`node.rs`'s `sig_block_con_exp_data` / `prev_sig_block_con_exp_data`
/// fields point here once the stub re-aliases below).
pub type SignatureBlockingIndividualNodeConceptExpansionDataId =
    Id<SignatureBlockingIndividualNodeConceptExpansionData>;
/// `CSignatureBlockingReviewSet*` → `SignatureBlockingReviewSetId`.
pub type SignatureBlockingReviewSetId = Id<SignatureBlockingReviewSet>;
/// `CReusingReviewData*` → `ReusingReviewDataId`.
pub type ReusingReviewDataId = Id<ReusingReviewData>;
/// `CReusingIndividualNodeConceptExpansionData*` →
/// `ReusingIndividualNodeConceptExpansionDataId`.
pub type ReusingIndividualNodeConceptExpansionDataId =
    Id<ReusingIndividualNodeConceptExpansionData>;

// ===========================================================================
// CBlockingIndividualNodeLinker / LinkedCandidateData / LinkedCandidateHash
// ===========================================================================

/// Port of `CBlockingIndividualNodeLinker`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct BlockingIndividualNodeLinker {
    /// `CLinkerBase::mData`.
    pub candidate_individual_node: NodeId,
    /// `CLinkerBase::mNext`.
    pub next: BlockingIndividualNodeLinkerId,
    /// `CBlockingIndividualNodeLinker::mLastFailedSubsetConDes`.
    pub last_failed_subset_con_des: ConDescId,
}

impl Default for BlockingIndividualNodeLinker {
    fn default() -> Self {
        Self {
            candidate_individual_node: NodeId::NONE,
            next: BlockingIndividualNodeLinkerId::NONE,
            last_failed_subset_con_des: ConDescId::NONE,
        }
    }
}

impl BlockingIndividualNodeLinker {
    /// Port of `CBlockingIndividualNodeLinker()`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initBlockingIndividualNodeLinker(CBlockingIndividualNodeLinker*)`.
    pub fn init_blocking_individual_node_linker_from(
        &mut self,
        prev: Option<&BlockingIndividualNodeLinker>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.candidate_individual_node = prev.candidate_individual_node;
            self.last_failed_subset_con_des = prev.last_failed_subset_con_des;
            self.next = BlockingIndividualNodeLinkerId::NONE;
        } else {
            self.candidate_individual_node = NodeId::NONE;
            self.last_failed_subset_con_des = ConDescId::NONE;
            self.next = BlockingIndividualNodeLinkerId::NONE;
        }
        self
    }

    /// Port of `initBlockingIndividualNodeLinker(CIndividualProcessNode*)`.
    pub fn init_blocking_individual_node_linker(&mut self, indi_node: NodeId) -> &mut Self {
        self.last_failed_subset_con_des = ConDescId::NONE;
        self.candidate_individual_node = indi_node;
        self.next = BlockingIndividualNodeLinkerId::NONE;
        self
    }

    /// Port of `getLastFailedSubsetConceptDescriptor`.
    pub fn get_last_failed_subset_concept_descriptor(&self) -> ConDescId {
        self.last_failed_subset_con_des
    }

    /// Port of `setLastFailedSubsetConceptDescriptor`.
    pub fn set_last_failed_subset_concept_descriptor(&mut self, con_des: ConDescId) -> &mut Self {
        self.last_failed_subset_con_des = con_des;
        self
    }

    /// Port of `getCandidateIndividualNode`.
    pub fn get_candidate_individual_node(&self) -> NodeId {
        self.candidate_individual_node
    }

    /// Port of `setCandidateIndividualNode`.
    pub fn set_candidate_individual_node(&mut self, indi_node: NodeId) -> &mut Self {
        self.candidate_individual_node = indi_node;
        self
    }

    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> BlockingIndividualNodeLinkerId {
        self.next
    }

    /// Port-facing equivalent of `linker->append(next)`.
    pub fn append(&mut self, next: BlockingIndividualNodeLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}

/// Port of `CBlockingIndividualNodeLinkedCandidateData`.
#[derive(Clone, Debug)]
pub struct BlockingIndividualNodeLinkedCandidateData {
    /// `CBlockingIndividualNodeLinker* mCandLinker`.
    pub cand_linker: BlockingIndividualNodeLinkerId,
    /// `cint64 mCandidateCount`.
    pub candidate_count: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: ambient `CProcessContext* mContext` /
    // `CMemoryAllocationManager* mMemMan` (opaque).
    pub context: Cint64,
    pub mem_man: Cint64,
}

impl Default for BlockingIndividualNodeLinkedCandidateData {
    fn default() -> Self {
        Self {
            cand_linker: BlockingIndividualNodeLinkerId::NONE,
            candidate_count: 0,
            context: INVALID,
            mem_man: INVALID,
        }
    }
}

impl BlockingIndividualNodeLinkedCandidateData {
    /// Port of `CBlockingIndividualNodeLinkedCandidateData(CProcessContext*)`.
    pub fn new(context: Cint64) -> Self {
        Self {
            context,
            ..Self::default()
        }
    }

    /// Port of `initBlockingCandidateData`.
    pub fn init_blocking_candidate_data(
        &mut self,
        prev: Option<&BlockingIndividualNodeLinkedCandidateData>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.candidate_count = prev.candidate_count;
            self.cand_linker = prev.cand_linker;
        } else {
            self.candidate_count = 0;
            self.cand_linker = BlockingIndividualNodeLinkerId::NONE;
        }
        self
    }

    /// Port of `getBlockingCandidatesIndividualNodeLinker`.
    pub fn get_blocking_candidates_individual_node_linker(&self) -> BlockingIndividualNodeLinkerId {
        self.cand_linker
    }

    /// Port of `getCandidateCount`.
    pub fn get_candidate_count(&self) -> Cint64 {
        self.candidate_count
    }

    /// Port of `setCandidateCount`.
    pub fn set_candidate_count(&mut self, cand_count: Cint64) -> &mut Self {
        self.candidate_count = cand_count;
        self
    }
}

/// Per-key value for `CBlockingIndividualNodeLinkedCandidateHash`.
#[derive(Copy, Clone, Debug)]
pub struct BlockingLinkedCandidateHashData {
    /// `mCandidateIndiData`.
    pub candidate_indi_data: BlockingIndividualNodeLinkedCandidateDataId,
    /// `mPrevCandidateIndiData`.
    pub prev_candidate_indi_data: BlockingIndividualNodeLinkedCandidateDataId,
}

impl Default for BlockingLinkedCandidateHashData {
    fn default() -> Self {
        Self {
            candidate_indi_data: BlockingIndividualNodeLinkedCandidateDataId::NONE,
            prev_candidate_indi_data: BlockingIndividualNodeLinkedCandidateDataId::NONE,
        }
    }
}

/// Port of `CBlockingIndividualNodeLinkedCandidateHash`.
#[derive(Clone, Debug)]
pub struct BlockingIndividualNodeLinkedCandidateHash {
    pub context: Cint64,
    pub mem_man: Cint64,
    /// `CPROCESSHASH<QPair<CConcept*,bool>,CBlockingLinkedCandidateHashData>`.
    pub block_candidate_hash: HashMap<(ConceptId, bool), BlockingLinkedCandidateHashData>,
}

impl Default for BlockingIndividualNodeLinkedCandidateHash {
    fn default() -> Self {
        Self {
            context: INVALID,
            mem_man: INVALID,
            block_candidate_hash: HashMap::new(),
        }
    }
}

impl BlockingIndividualNodeLinkedCandidateHash {
    /// Port of `CBlockingIndividualNodeLinkedCandidateHash(CProcessContext*)`.
    pub fn new(context: Cint64) -> Self {
        Self {
            context,
            ..Self::default()
        }
    }

    /// Port of `initBlockingIndividualNodeCandidateHash`.
    pub fn init_blocking_individual_node_candidate_hash(
        &mut self,
        prev: Option<&BlockingIndividualNodeLinkedCandidateHash>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.block_candidate_hash = prev
                .block_candidate_hash
                .iter()
                .map(|(k, v)| {
                    (
                        *k,
                        BlockingLinkedCandidateHashData {
                            candidate_indi_data: Id::NONE,
                            prev_candidate_indi_data: v.prev_candidate_indi_data,
                        },
                    )
                })
                .collect();
        } else {
            self.block_candidate_hash.clear();
        }
        self
    }

    /// Port of `getBlockingIndividualCandidateData(CConcept*, bool, bool create)`.
    pub fn get_blocking_individual_candidate_data(
        ctx: &mut ProcessContext,
        this: BlockingIndividualNodeLinkedCandidateHashId,
        initialization_concept: ConceptId,
        concept_negation: bool,
        create: bool,
    ) -> BlockingIndividualNodeLinkedCandidateDataId {
        let key = (initialization_concept, concept_negation);
        if create {
            let (candidate, prev) = {
                let hash = ctx.blocking_indi_node_linked_cand_hash_mut(this);
                let data = hash.block_candidate_hash.entry(key).or_default();
                (data.candidate_indi_data, data.prev_candidate_indi_data)
            };
            if candidate.is_none() {
                let new_data = ctx.alloc_blocking_indi_node_linked_cand_data(
                    BlockingIndividualNodeLinkedCandidateData::new(INVALID),
                );
                if prev.is_some() {
                    let taken = std::mem::replace(
                        ctx.blocking_indi_node_linked_cand_data_mut(prev),
                        BlockingIndividualNodeLinkedCandidateData::new(INVALID),
                    );
                    ctx.blocking_indi_node_linked_cand_data_mut(new_data)
                        .init_blocking_candidate_data(Some(&taken));
                    *ctx.blocking_indi_node_linked_cand_data_mut(prev) = taken;
                } else {
                    ctx.blocking_indi_node_linked_cand_data_mut(new_data)
                        .init_blocking_candidate_data(None);
                }
                let data = ctx
                    .blocking_indi_node_linked_cand_hash_mut(this)
                    .block_candidate_hash
                    .get_mut(&key)
                    .unwrap();
                data.candidate_indi_data = new_data;
                data.prev_candidate_indi_data = new_data;
                new_data
            } else {
                prev
            }
        } else {
            ctx.blocking_indi_node_linked_cand_hash(this)
                .block_candidate_hash
                .get(&key)
                .map(|d| d.prev_candidate_indi_data)
                .unwrap_or(BlockingIndividualNodeLinkedCandidateDataId::NONE)
        }
    }

    /// Port of `getBlockingIndividualCandidateData(CConceptDescriptor*, bool create)`.
    pub fn get_blocking_individual_candidate_data_for_concept_descriptor(
        ctx: &mut ProcessContext,
        this: BlockingIndividualNodeLinkedCandidateHashId,
        initialization_con_des: ConDescId,
        create: bool,
    ) -> BlockingIndividualNodeLinkedCandidateDataId {
        let concept = ctx.con_desc(initialization_con_des).get_concept();
        let negation = ctx.con_desc(initialization_con_des).is_negated();
        Self::get_blocking_individual_candidate_data(ctx, this, concept, negation, create)
    }
}

// ===========================================================================
// CSignatureBlockingReviewData / Iterator / Set
// ===========================================================================

/// Port of `CSignatureBlockingReviewData`.
#[derive(Clone, Debug, Default)]
pub struct SignatureBlockingReviewData {
    /// `mIndividualSet`.
    pub individual_set: BTreeSet<Cint64>,
    /// `mDepthIndividualMap`.
    pub depth_individual_map: BTreeMap<Cint64, Vec<Cint64>>,
}

impl SignatureBlockingReviewData {
    /// Port of `CSignatureBlockingReviewData::CSignatureBlockingReviewData`.
    pub fn new() -> Self {
        SignatureBlockingReviewData::default()
    }

    /// Port of `initSignatureBlockingReviewData`.
    pub fn init_signature_blocking_review_data(
        &mut self,
        prev: Option<&SignatureBlockingReviewData>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.individual_set = prev.individual_set.clone();
            self.depth_individual_map = prev.depth_individual_map.clone();
        } else {
            self.individual_set.clear();
            self.depth_individual_map.clear();
        }
        self
    }

    /// Port of `insert`.
    pub fn insert(&mut self, depth: Cint64, indi_id: Cint64) -> &mut Self {
        if !self.individual_set.contains(&indi_id) {
            self.individual_set.insert(indi_id);
            self.depth_individual_map
                .entry(depth)
                .or_default()
                .push(indi_id);
        }
        self
    }

    /// Port of `contains`.
    pub fn contains(&self, indi_id: Cint64) -> bool {
        self.individual_set.contains(&indi_id)
    }

    /// Port of `remove`.
    pub fn remove(&mut self, indi_id: Cint64) -> &mut Self {
        self.individual_set.remove(&indi_id);
        self
    }

    /// Port of `isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.individual_set.is_empty()
    }

    /// Port of `getIterator`.
    pub fn get_iterator(&mut self) -> SignatureBlockingReviewDataIterator<'_> {
        SignatureBlockingReviewDataIterator::new(self)
    }

    fn front_valid_id(&mut self) -> Option<Cint64> {
        loop {
            let depth = *self.depth_individual_map.keys().next()?;
            let mut remove_depth = false;
            let mut current = None;
            if let Some(ids) = self.depth_individual_map.get_mut(&depth) {
                while let Some(first) = ids.first().copied() {
                    if self.individual_set.contains(&first) {
                        current = Some(first);
                        break;
                    }
                    ids.remove(0);
                }
                remove_depth = ids.is_empty();
            }
            if remove_depth {
                self.depth_individual_map.remove(&depth);
            } else {
                return current;
            }
        }
    }

    fn pop_front_current(&mut self) {
        let Some(depth) = self.depth_individual_map.keys().next().copied() else {
            return;
        };
        let mut remove_depth = false;
        if let Some(ids) = self.depth_individual_map.get_mut(&depth) {
            if !ids.is_empty() {
                ids.remove(0);
            }
            remove_depth = ids.is_empty();
        }
        if remove_depth {
            self.depth_individual_map.remove(&depth);
        }
    }
}

/// Port of `CSignatureBlockingReviewDataIterator`.
pub struct SignatureBlockingReviewDataIterator<'a> {
    data: &'a mut SignatureBlockingReviewData,
    current: Option<Cint64>,
}

impl<'a> SignatureBlockingReviewDataIterator<'a> {
    /// Port of `CSignatureBlockingReviewDataIterator`.
    pub fn new(data: &'a mut SignatureBlockingReviewData) -> Self {
        let current = data.front_valid_id();
        SignatureBlockingReviewDataIterator { data, current }
    }

    /// Port of `hasNext`.
    pub fn has_next(&self) -> bool {
        self.current.is_some()
    }

    /// Port of `next`.
    pub fn next(&mut self, move_next: bool) -> Cint64 {
        let indi_id = self.current.unwrap_or(-1);
        if move_next {
            self.current = self.data.front_valid_id();
        }
        indi_id
    }

    /// Port of `removeAndMoveNext`.
    pub fn remove_and_move_next(&mut self) -> bool {
        let Some(indi_id) = self.current else {
            return false;
        };
        self.data.individual_set.remove(&indi_id);
        self.data.pop_front_current();
        self.current = self.data.front_valid_id();
        true
    }
}

/// Port of `CSignatureBlockingReviewSet`.
#[derive(Clone, Debug, Default)]
pub struct SignatureBlockingReviewSet {
    /// `mSubsetReviews`.
    pub subset_reviews: SignatureBlockingReviewData,
    /// `mNonSubsetReviews`.
    pub non_subset_reviews: SignatureBlockingReviewData,
}

impl SignatureBlockingReviewSet {
    /// Port of `CSignatureBlockingReviewSet::CSignatureBlockingReviewSet`.
    pub fn new() -> Self {
        SignatureBlockingReviewSet::default()
    }

    /// Port of `initSignatureBlockingReviewSet`.
    pub fn init_signature_blocking_review_set(
        &mut self,
        prev: Option<&SignatureBlockingReviewSet>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.subset_reviews
                .init_signature_blocking_review_data(Some(&prev.subset_reviews));
            self.non_subset_reviews
                .init_signature_blocking_review_data(Some(&prev.non_subset_reviews));
        } else {
            self.subset_reviews
                .init_signature_blocking_review_data(None);
            self.non_subset_reviews
                .init_signature_blocking_review_data(None);
        }
        self
    }

    /// Port of `getSubsetReviewData`.
    pub fn get_subset_review_data(&mut self) -> &mut SignatureBlockingReviewData {
        &mut self.subset_reviews
    }

    /// Port of `getReviewData`.
    pub fn get_review_data(&mut self, subset: bool) -> &mut SignatureBlockingReviewData {
        if subset {
            &mut self.subset_reviews
        } else {
            &mut self.non_subset_reviews
        }
    }

    /// Port of `getNonSubsetReviewData`.
    pub fn get_non_subset_review_data(&mut self) -> &mut SignatureBlockingReviewData {
        &mut self.non_subset_reviews
    }

    /// Port of `isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.subset_reviews.is_empty() && self.non_subset_reviews.is_empty()
    }

    /// Driver helper for the upstream `getNonSubsetReviewData`/fallback
    /// `getSubsetReviewData` iterator sequence. Returns `(individual_id,
    /// is_non_subset_data)`.
    pub fn take_next_review_individual(&mut self) -> Option<(Cint64, bool)> {
        if !self.non_subset_reviews.is_empty() {
            let mut it = self.non_subset_reviews.get_iterator();
            if it.has_next() {
                let indi_id = it.next(false);
                it.remove_and_move_next();
                return Some((indi_id, true));
            }
        }
        if !self.subset_reviews.is_empty() {
            let mut it = self.subset_reviews.get_iterator();
            if it.has_next() {
                let indi_id = it.next(false);
                it.remove_and_move_next();
                return Some((indi_id, false));
            }
        }
        None
    }
}

// ===========================================================================
// CReusingReviewData
// ===========================================================================

/// Port of `CReusingReviewData`.
#[derive(Clone, Debug, Default)]
pub struct ReusingReviewData {
    /// `mIndividualSet`.
    pub individual_set: BTreeSet<Cint64>,
    /// `mDepthIndividualMap`.
    pub depth_individual_map: BTreeMap<Cint64, Vec<Cint64>>,
}

impl ReusingReviewData {
    /// Port of `CReusingReviewData::CReusingReviewData`.
    pub fn new() -> Self {
        ReusingReviewData::default()
    }

    /// Port of `initReviewData`.
    pub fn init_review_data(&mut self, prev: Option<&ReusingReviewData>) -> &mut Self {
        if let Some(prev) = prev {
            self.individual_set = prev.individual_set.clone();
            self.depth_individual_map = prev.depth_individual_map.clone();
        } else {
            self.individual_set.clear();
            self.depth_individual_map.clear();
        }
        self
    }

    /// Port of `insert`.
    pub fn insert(&mut self, depth: Cint64, indi_id: Cint64) -> &mut Self {
        if !self.individual_set.contains(&indi_id) {
            self.individual_set.insert(indi_id);
            self.depth_individual_map
                .entry(depth)
                .or_default()
                .push(indi_id);
        }
        self
    }

    /// Port of `contains`.
    pub fn contains(&self, indi_id: Cint64) -> bool {
        self.individual_set.contains(&indi_id)
    }

    /// Port of `remove`.
    pub fn remove(&mut self, indi_id: Cint64) -> &mut Self {
        self.individual_set.remove(&indi_id);
        self
    }

    /// Port of `isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.individual_set.is_empty()
    }

    /// Port of `hasNextIndividualID`.
    ///
    /// KONCLUDE-PORT-NOTE[fidelity]: upstream returns `mIndividualSet.isEmpty()`
    /// (not `!isEmpty()`), so the driver loop only enters when the set is empty.
    pub fn has_next_individual_id(&self) -> bool {
        self.individual_set.is_empty()
    }

    /// Port of `takeNextIndividualID`.
    pub fn take_next_individual_id(&mut self) -> Cint64 {
        let mut indi_id = 0;
        loop {
            let Some(depth) = self.depth_individual_map.keys().next().copied() else {
                break;
            };
            let mut remove_depth = false;
            if let Some(ids) = self.depth_individual_map.get_mut(&depth) {
                if let Some(id) = ids.first().copied() {
                    indi_id = id;
                    ids.remove(0);
                    if self.individual_set.contains(&indi_id) {
                        self.individual_set.remove(&indi_id);
                        remove_depth = ids.is_empty();
                        if remove_depth {
                            self.depth_individual_map.remove(&depth);
                        }
                        break;
                    }
                }
                remove_depth = ids.is_empty();
            }
            if remove_depth {
                self.depth_individual_map.remove(&depth);
            }
        }
        indi_id
    }
}

// ===========================================================================
// CBlockingIndividualNodeCandidateData
// ===========================================================================

/// Port of `CBlockingIndividualNodeCandidateData`
/// (`: public CConceptLabelSetModificationTag, public CNodeSwitchTag`).
///
/// KONCLUDE-PORT-NOTE[ownership]: the two polymorphic tag bases become inline
/// composition (the `node_switch_tag` word + the `modification_tag`; the full
/// `CProcessTagger`-driven protocol is `W3.5b-DEFER[api]`, only the marking word
/// is modelled — the same simplification `reapply_sat::IndividualNodeBlockingTestData`
/// takes). The ordered `CPROCESSMAP<cint64,CIndividualProcessNode*> mCandidateIndiMap`
/// becomes a `BTreeMap<Cint64,NodeId>` keyed by `-candidateIndividualID` (so
/// `upperBound` is faithful).
///
/// KONCLUDE-PORT-NOTE[api]: no `#[derive(Clone)]` (the `modification_tag` base is not
/// `Clone`); the struct is never whole-cloned — `init_blocking_candidate_data` clones
/// only the `BTreeMap`, and `get_blocking_individual_candidate_data` uses `mem::replace`.
#[derive(Clone)]
pub struct BlockingIndividualNodeCandidateData {
    // --- base CNodeSwitchTag (: CProcessTag) ---
    pub node_switch_tag: Cint64,
    // --- base CConceptLabelSetModificationTag ---
    pub modification_tag: ConceptLabelSetModificationTag,

    // --- own fields ---
    /// `CPROCESSMAP<cint64,CIndividualProcessNode*> mCandidateIndiMap` (keyed by `-id`).
    pub candidate_indi_map: BTreeMap<Cint64, NodeId>,
    /// `cint64 mMaxValidIndividualID`.
    pub max_valid_individual_id: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CProcessContext* mContext` /
    // `CMemoryAllocationManager* mMemMan` (opaque).
    pub context: Cint64,
    pub mem_man: Cint64,
}

impl Default for BlockingIndividualNodeCandidateData {
    fn default() -> Self {
        BlockingIndividualNodeCandidateData {
            node_switch_tag: 0,
            modification_tag: ConceptLabelSetModificationTag::default(),
            candidate_indi_map: BTreeMap::new(),
            max_valid_individual_id: 0,
            context: INVALID,
            mem_man: INVALID,
        }
    }
}

impl BlockingIndividualNodeCandidateData {
    /// Port of `CBlockingIndividualNodeCandidateData(CProcessContext*)`.
    pub fn new(context: Cint64) -> Self {
        BlockingIndividualNodeCandidateData {
            context,
            ..Self::default()
        }
    }

    /// Port of `CNodeSwitchTag::getNodeSwitchTag`.
    pub fn get_node_switch_tag(&self) -> Cint64 {
        self.node_switch_tag
    }
    /// Port of `CNodeSwitchTag::setNodeSwitchTag(cint64)`.
    pub fn set_node_switch_tag(&mut self, node_switch_tag: Cint64) -> &mut Self {
        self.node_switch_tag = node_switch_tag;
        self
    }
    /// Port of `CNodeSwitchTag::initNodeSwitchTag(cint64)`.
    pub fn init_node_switch_tag(&mut self, node_switch_tag: Cint64) -> &mut Self {
        self.node_switch_tag = node_switch_tag;
        self
    }
    /// Port of `CNodeSwitchTag::isNodeSwitchTagUpdated(cint64)`.
    pub fn is_node_switch_tag_updated(&self, node_switch_tag: Cint64) -> bool {
        node_switch_tag > self.node_switch_tag
    }
    /// Port of `CNodeSwitchTag::isNodeSwitchTagUpToDate(cint64)`.
    pub fn is_node_switch_tag_up_to_date(&self, node_switch_tag: Cint64) -> bool {
        self.node_switch_tag >= node_switch_tag
    }
    /// Port of `CNodeSwitchTag::updateNodeSwitchTag(cint64)`.
    pub fn update_node_switch_tag(&mut self, node_switch_tag: Cint64) -> bool {
        let updated = self.node_switch_tag != node_switch_tag;
        self.node_switch_tag = node_switch_tag;
        updated
    }

    /// Port of `CConceptLabelSetModificationTag::getConceptLabelSetModificationTag`.
    pub fn get_concept_label_set_modification_tag(&self) -> Cint64 {
        self.modification_tag
            .get_concept_label_set_modification_tag()
    }
    /// Port of `CConceptLabelSetModificationTag::updateConceptLabelSetModificationTag(cint64)`.
    pub fn update_concept_label_set_modification_tag(
        &mut self,
        concept_label_set_modification_tag: Cint64,
    ) -> bool {
        self.modification_tag
            .update_concept_label_set_modification_tag(concept_label_set_modification_tag)
    }

    /// Port of `initBlockingCandidateData`.
    pub fn init_blocking_candidate_data(
        &mut self,
        prev: Option<&BlockingIndividualNodeCandidateData>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.candidate_indi_map = prev.candidate_indi_map.clone();
            self.max_valid_individual_id = prev.max_valid_individual_id;
        } else {
            self.max_valid_individual_id = 0;
            self.candidate_indi_map.clear();
        }
        self
    }

    /// Port of `insertBlockingCandidateIndividualNode(CIndividualProcessNode*)`.
    /// KONCLUDE-PORT-NOTE[pointer-alias]: `candidateIndi->getIndividualNodeID()`
    /// resolves against the node arena (hence `&ProcessContext`).
    pub fn insert_blocking_candidate_individual_node(
        &mut self,
        candidate_indi: NodeId,
        ctx: &ProcessContext,
    ) -> &mut Self {
        let candidate_individual_id = ctx.node(candidate_indi).individual_node_id();
        self.candidate_indi_map
            .insert(-candidate_individual_id, candidate_indi);
        self
    }

    /// Port of `getBlockingCandidatesIndividualNodeIterator(cint64)`.
    pub fn get_blocking_candidates_individual_node_iterator(
        &self,
        candidate_individual_id: Cint64,
    ) -> BlockingIndividualNodeCandidateIterator {
        BlockingIndividualNodeCandidateIterator::new(
            &self.candidate_indi_map,
            candidate_individual_id,
        )
    }

    /// Port of `getBlockingCandidatesIndividualNodeIterator(CIndividualProcessNode*)`.
    pub fn get_blocking_candidates_individual_node_iterator_for_node(
        &self,
        candidate_indi: NodeId,
        ctx: &ProcessContext,
    ) -> BlockingIndividualNodeCandidateIterator {
        self.get_blocking_candidates_individual_node_iterator(
            ctx.node(candidate_indi).individual_node_id(),
        )
    }

    /// Context-threaded port of `getBlockingCandidatesIndividualNodeIterator(CIndividualProcessNode*)`.
    pub fn get_blocking_candidates_individual_node_iterator_for_node_in_context(
        ctx: &ProcessContext,
        this: BlockingIndividualNodeCandidateDataId,
        candidate_indi: NodeId,
    ) -> BlockingIndividualNodeCandidateIterator {
        BlockingIndividualNodeCandidateIterator::new_in_context(
            ctx,
            this,
            ctx.node(candidate_indi).individual_node_id(),
        )
    }

    /// Port of `getMaxValidIndividualID`.
    pub fn get_max_valid_individual_id(&self) -> Cint64 {
        self.max_valid_individual_id
    }
    /// Port of `setMaxValidIndividualID`.
    pub fn set_max_valid_individual_id(&mut self, indi_id: Cint64) -> &mut Self {
        self.max_valid_individual_id = indi_id;
        self
    }
}

// ===========================================================================
// CBlockingIndividualNodeCandidateIterator
// ===========================================================================

/// Port of `CBlockingIndividualNodeCandidateIterator` — walks the candidate map
/// of one `CBlockingIndividualNodeCandidateData` from `upperBound(-id)` onward.
///
/// KONCLUDE-PORT-NOTE[ownership]: the C++ holds a raw pointer into the data's
/// `CPROCESSMAP` plus `begin/end/last` const_iterators. The port snapshots the
/// FULL ordered `(key,node)` set (cheap; the candidate map is small) and keeps the
/// three cursors as `usize` indices, so `next` / `hasNext` / `hasIndividualCandidate`
/// stay faithful for read-only callers. When the iterator is constructed through
/// the context-threaded route it also stores the owning candidate-data id, allowing
/// `removeLastIndividualCandidate` to erase from the real arena-owned map.
pub struct BlockingIndividualNodeCandidateIterator {
    /// the full ordered `(key, node)` snapshot (`key == -individualNodeID`).
    entries: Vec<(Cint64, NodeId)>,
    /// `mItBegin` (= `upperBound(-candidateIndividualID)` position).
    it_begin: usize,
    /// `mItEnd` (= `end()` == `entries.len()`).
    it_end: usize,
    /// `mItLast` (the position last yielded by `next`).
    it_last: usize,
    /// whether the underlying map was non-empty at construction (`mCandidateMap`).
    map_present: bool,
    /// Arena owner for context-threaded `removeLastIndividualCandidate`.
    owner_data: BlockingIndividualNodeCandidateDataId,
}

impl BlockingIndividualNodeCandidateIterator {
    /// Empty iterator equivalent to a null/empty candidate map.
    pub fn empty() -> Self {
        BlockingIndividualNodeCandidateIterator {
            entries: Vec::new(),
            it_begin: 0,
            it_end: 0,
            it_last: 0,
            map_present: false,
            owner_data: Id::NONE,
        }
    }

    /// Port of the `CBlockingIndividualNodeCandidateIterator(map, candidateIndividualID)`
    /// ctor (`mItBegin = upperBound(-candidateIndividualID); mItEnd = end(); mItLast = mItBegin`).
    pub fn new(candidate_map: &BTreeMap<Cint64, NodeId>, candidate_individual_id: Cint64) -> Self {
        let entries: Vec<(Cint64, NodeId)> = candidate_map.iter().map(|(k, v)| (*k, *v)).collect();
        // upperBound(-candidateIndividualID): first index whose key > -candidateIndividualID.
        let target = -candidate_individual_id;
        let it_begin = entries.partition_point(|(k, _)| *k <= target);
        let it_end = entries.len();
        BlockingIndividualNodeCandidateIterator {
            entries,
            it_begin,
            it_end,
            it_last: it_begin,
            map_present: true,
            owner_data: Id::NONE,
        }
    }

    /// Context-threaded constructor for an arena-owned candidate-data map.
    pub fn new_in_context(
        ctx: &ProcessContext,
        owner_data: BlockingIndividualNodeCandidateDataId,
        candidate_individual_id: Cint64,
    ) -> Self {
        let mut iterator = Self::new(
            &ctx.blocking_indi_node_cand_data(owner_data)
                .candidate_indi_map,
            candidate_individual_id,
        );
        iterator.owner_data = owner_data;
        iterator
    }

    /// Port of `hasNext` (`mCandidateMap && mItBegin != mItEnd`).
    pub fn has_next(&self) -> bool {
        self.map_present && self.it_begin != self.it_end
    }

    /// Port of `hasIndividualCandidates` (`mCandidateMap && !mCandidateMap->isEmpty()`).
    pub fn has_individual_candidates(&self) -> bool {
        self.map_present && !self.entries.is_empty()
    }

    /// Port of `hasIndividualCandidate(cint64)` (`mCandidateMap->contains(-indiID)`).
    pub fn has_individual_candidate(&self, indi_id: Cint64) -> bool {
        self.map_present && self.entries.iter().any(|(k, _)| *k == -indi_id)
    }

    /// Port of `hasIndividualCandidate(CIndividualProcessNode*)`.
    pub fn has_individual_candidate_for_node(&self, indi: NodeId, ctx: &ProcessContext) -> bool {
        self.has_individual_candidate(ctx.node(indi).individual_node_id())
    }

    /// Port of `next(bool moveNext)` (`return nextIndividualCandidate(moveNext)->getIndividualNodeID()`).
    pub fn next(&mut self, move_next: bool, ctx: &ProcessContext) -> Cint64 {
        if let Some(indi) = self.next_individual_candidate(move_next) {
            return ctx.node(indi).individual_node_id();
        }
        0
    }

    /// Port of `nextIndividualCandidate(bool moveNext)`.
    pub fn next_individual_candidate(&mut self, move_next: bool) -> Option<NodeId> {
        if self.map_present && self.it_begin != self.it_end {
            let indi = self.entries[self.it_begin].1;
            self.it_last = self.it_begin;
            if move_next {
                self.it_begin += 1;
            }
            Some(indi)
        } else {
            None
        }
    }

    /// Snapshot-only compatibility fallback for `removeLastIndividualCandidate`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: call `remove_last_individual_candidate_in_context`
    /// when the iterator was built from an arena-owned candidate-data id and the
    /// C++ backing-map erase side effect is required.
    pub fn remove_last_individual_candidate(&mut self) -> bool {
        if self.it_last != self.it_end {
            // erase the last-yielded entry; the next cursor resumes at that slot
            // (Vec::remove shifts the tail left, matching `mItBegin = erase(mItLast)`).
            self.entries.remove(self.it_last);
            self.it_end = self.entries.len();
            self.it_begin = self.it_last;
            self.it_last = self.it_begin;
            true
        } else {
            false
        }
    }

    /// Context-threaded port of `removeLastIndividualCandidate`.
    pub fn remove_last_individual_candidate_in_context(
        &mut self,
        ctx: &mut ProcessContext,
    ) -> bool {
        if self.it_last != self.it_end {
            let removed_key = self.entries[self.it_last].0;
            self.entries.remove(self.it_last);
            self.it_end = self.entries.len();
            self.it_begin = self.it_last;
            self.it_last = self.it_begin;
            if self.owner_data.is_some() {
                ctx.blocking_indi_node_cand_data_mut(self.owner_data)
                    .candidate_indi_map
                    .remove(&removed_key);
            }
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::node::IndividualProcessNode;
    use super::*;

    #[test]
    fn blocking_candidate_iterator_context_remove_erases_backing_map() {
        let mut ctx = ProcessContext::new();
        let data = ctx
            .alloc_blocking_indi_node_cand_data(BlockingIndividualNodeCandidateData::new(INVALID));
        let first = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(first).set_individual_node_id(3);
        let second = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(second).set_individual_node_id(7);
        let third = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(third).set_individual_node_id(11);

        ctx.blocking_indi_node_cand_data_insert_blocking_candidate_individual_node(data, first);
        ctx.blocking_indi_node_cand_data_insert_blocking_candidate_individual_node(data, second);
        ctx.blocking_indi_node_cand_data_insert_blocking_candidate_individual_node(data, third);

        let mut iterator = BlockingIndividualNodeCandidateIterator::new_in_context(&ctx, data, 12);
        assert_eq!(iterator.next_individual_candidate(true), Some(third));
        assert!(iterator.remove_last_individual_candidate_in_context(&mut ctx));
        assert!(!ctx
            .blocking_indi_node_cand_data(data)
            .candidate_indi_map
            .contains_key(&-11));
        assert_eq!(iterator.next_individual_candidate(true), Some(second));
        assert!(iterator.remove_last_individual_candidate_in_context(&mut ctx));
        assert!(!ctx
            .blocking_indi_node_cand_data(data)
            .candidate_indi_map
            .contains_key(&-7));
        assert_eq!(iterator.next_individual_candidate(true), Some(first));
        assert!(ctx
            .blocking_indi_node_cand_data(data)
            .candidate_indi_map
            .contains_key(&-3));
    }

    #[test]
    fn blocking_candidate_iterator_snapshot_remove_is_local_fallback() {
        let mut ctx = ProcessContext::new();
        let data = ctx
            .alloc_blocking_indi_node_cand_data(BlockingIndividualNodeCandidateData::new(INVALID));
        let candidate = ctx.alloc_node(IndividualProcessNode::default());
        ctx.node_mut(candidate).set_individual_node_id(5);
        ctx.blocking_indi_node_cand_data_insert_blocking_candidate_individual_node(data, candidate);

        let mut iterator = ctx
            .blocking_indi_node_cand_data(data)
            .get_blocking_candidates_individual_node_iterator(6);
        assert_eq!(iterator.next_individual_candidate(true), Some(candidate));
        assert!(iterator.remove_last_individual_candidate());
        assert!(
            ctx.blocking_indi_node_cand_data(data)
                .candidate_indi_map
                .contains_key(&-5),
            "snapshot-only compatibility fallback must not mutate the arena map"
        );
    }
}

// ===========================================================================
// CBlockingIndividualNodeCandidateHash
// ===========================================================================

/// Port of `CBlockingIndividualNodeCandidateHash::CBlockingCandidateHashData` — the
/// per-`(concept,negation)` value: the localised candidate-data id + the parent's.
///
/// KONCLUDE-PORT-NOTE[ownership]: the C++ copy ctor resets `mCandidateIndiData`
/// to `nullptr` and keeps `mPrevCandidateIndiData` — the COW-localise marker. The
/// arena collapse models that in [`BlockingIndividualNodeCandidateHash::init_…`].
#[derive(Debug, Clone, Copy)]
pub struct BlockingCandidateHashData {
    /// `CBlockingIndividualNodeCandidateData* mCandidateIndiData`.
    pub candidate_indi_data: BlockingIndividualNodeCandidateDataId,
    /// `CBlockingIndividualNodeCandidateData* mPrevCandidateIndiData`.
    pub prev_candidate_indi_data: BlockingIndividualNodeCandidateDataId,
}

impl Default for BlockingCandidateHashData {
    fn default() -> Self {
        Self::new()
    }
}

impl BlockingCandidateHashData {
    /// Port of the inline `CBlockingCandidateHashData()` ctor (`mCandidateIndiData =
    /// mPrevCandidateIndiData = nullptr`).
    pub fn new() -> Self {
        BlockingCandidateHashData {
            candidate_indi_data: Id::NONE,
            prev_candidate_indi_data: Id::NONE,
        }
    }
}

/// Port of `CBlockingIndividualNodeCandidateHash` — `(concept,negation)` →
/// per-key blocking-candidate-data index.
///
/// KONCLUDE-PORT-NOTE[ownership]: the C++ triple-buffer (`mBlock`/`mUse`/`mPrev`
/// `CPROCESSHASH*`) collapses to one owned `HashMap`; the databox holds the three
/// `Id`s (block/use/prev) into the arena and the lazy `*mBlock = *mPrev` COW is the
/// eager [`init_blocking_individual_node_candidate_hash`] clone (the same collapse
/// `reapply_sat::SignatureBlockingCandidateHash` takes).
#[derive(Clone)]
pub struct BlockingIndividualNodeCandidateHash {
    // KONCLUDE-PORT-NOTE[memory-pool]: ambient `CProcessContext* mContext` /
    // `CMemoryAllocationManager* mMemMan` (opaque).
    pub context: Cint64,
    pub mem_man: Cint64,
    /// `CPROCESSHASH<QPair<CConcept*,bool>,CBlockingCandidateHashData> mBlockCandidateHash`.
    pub block_candidate_hash: HashMap<(ConceptId, bool), BlockingCandidateHashData>,
}

impl Default for BlockingIndividualNodeCandidateHash {
    fn default() -> Self {
        BlockingIndividualNodeCandidateHash {
            context: INVALID,
            mem_man: INVALID,
            block_candidate_hash: HashMap::new(),
        }
    }
}

impl BlockingIndividualNodeCandidateHash {
    /// Port of `CBlockingIndividualNodeCandidateHash(CProcessContext*)`.
    pub fn new(context: Cint64) -> Self {
        BlockingIndividualNodeCandidateHash {
            context,
            mem_man: INVALID,
            block_candidate_hash: HashMap::new(),
        }
    }

    /// Port of `initBlockingIndividualNodeCandidateHash`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ defers the `*mBlock = *mPrev` clone to
    /// the first `getBlockingIndividualCandidateData(create)`; the arena collapse
    /// does it eagerly here (behaviour identical, the lazy-share perf is left for
    /// later). The COW copy ctor resets each entry's live `mCandidateIndiData` to
    /// `nullptr` and keeps `mPrevCandidateIndiData`.
    pub fn init_blocking_individual_node_candidate_hash(
        &mut self,
        prev: Option<&BlockingIndividualNodeCandidateHash>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.block_candidate_hash = prev
                .block_candidate_hash
                .iter()
                .map(|(k, v)| {
                    (
                        *k,
                        BlockingCandidateHashData {
                            candidate_indi_data: Id::NONE,
                            prev_candidate_indi_data: v.prev_candidate_indi_data,
                        },
                    )
                })
                .collect();
        } else {
            self.block_candidate_hash.clear();
        }
        self
    }

    /// Port of `getBlockingIndividualCandidateData(CConcept*, bool, bool create)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: this allocates a child
    /// `CBlockingIndividualNodeCandidateData` from the pool on the create-localise
    /// path, so it is an associated fn over `(ctx, this, …)` (the `binding_hash`
    /// precedent). The same-arena `initBlockingCandidateData(prev)` borrow is
    /// resolved with `mem::replace`. The `concept` argument is reduced to its
    /// `(ConceptId, negation)` key. Returns `mPrevCandidateIndiData` (the C++
    /// returns it in both branches).
    pub fn get_blocking_individual_candidate_data(
        ctx: &mut ProcessContext,
        this: BlockingIndividualNodeCandidateHashId,
        initialization_concept: ConceptId,
        concept_negation: bool,
        create: bool,
    ) -> BlockingIndividualNodeCandidateDataId {
        let key = (initialization_concept, concept_negation);
        if create {
            let (candidate, prev) = {
                let hash = ctx.blocking_indi_node_cand_hash_mut(this);
                let data = hash.block_candidate_hash.entry(key).or_default();
                (data.candidate_indi_data, data.prev_candidate_indi_data)
            };
            if candidate.is_none() {
                let new_data = ctx.alloc_blocking_indi_node_cand_data(
                    BlockingIndividualNodeCandidateData::new(INVALID),
                );
                if prev.is_some() {
                    let taken = std::mem::replace(
                        ctx.blocking_indi_node_cand_data_mut(prev),
                        BlockingIndividualNodeCandidateData::new(INVALID),
                    );
                    ctx.blocking_indi_node_cand_data_mut(new_data)
                        .init_blocking_candidate_data(Some(&taken));
                    *ctx.blocking_indi_node_cand_data_mut(prev) = taken;
                } else {
                    ctx.blocking_indi_node_cand_data_mut(new_data)
                        .init_blocking_candidate_data(None);
                }
                let data = ctx
                    .blocking_indi_node_cand_hash_mut(this)
                    .block_candidate_hash
                    .get_mut(&key)
                    .unwrap();
                data.candidate_indi_data = new_data;
                data.prev_candidate_indi_data = new_data;
                new_data
            } else {
                prev
            }
        } else {
            ctx.blocking_indi_node_cand_hash(this)
                .block_candidate_hash
                .get(&key)
                .map(|d| d.prev_candidate_indi_data)
                .unwrap_or(BlockingIndividualNodeCandidateDataId::NONE)
        }
    }

    /// Port of `getBlockingIndividualCandidateData(CConceptDescriptor*, bool create)`
    /// (`return getBlockingIndividualCandidateData(conDes->getConcept(), conDes->getNegation(), create)`).
    pub fn get_blocking_individual_candidate_data_for_concept_descriptor(
        ctx: &mut ProcessContext,
        this: BlockingIndividualNodeCandidateHashId,
        initialization_con_des: ConDescId,
        create: bool,
    ) -> BlockingIndividualNodeCandidateDataId {
        let concept = ctx.con_desc(initialization_con_des).get_concept();
        let negation = ctx.con_desc(initialization_con_des).is_negated();
        Self::get_blocking_individual_candidate_data(ctx, this, concept, negation, create)
    }
}

// ===========================================================================
// CSignatureBlockingIndividualNodeConceptExpansionData (SigBlockConExpData)
// ===========================================================================

/// Port of `CSignatureBlockingIndividualNodeConceptExpansionData` — the per-node
/// signature-blocking concept-expansion bookkeeping (the blocker, the cached
/// concept-set signature/counts, and the review/subset markers the dynamic
/// signature-blocking test reads).
#[derive(Clone, Debug)]
pub struct SignatureBlockingIndividualNodeConceptExpansionData {
    /// `CConceptDescriptor* mSubsetTestedConDes`.
    pub subset_tested_con_des: ConDescId,
    /// `CIndividualProcessNode* blockerIndiNode`.
    pub blocker_indi_node: NodeId,
    /// `cint64 mBlockingConceptSignature`.
    pub blocking_concept_signature: Cint64,
    /// `cint64 mBlockingConceptCount`.
    pub blocking_concept_count: Cint64,
    /// `cint64 mExpandedContainedConceptCount`.
    pub expanded_contained_concept_count: Cint64,
    /// `cint64 mLastUpdatedConExpCount`.
    pub last_updated_con_exp_count: Cint64,
    /// `cint64 mLastUpdatedConCount`.
    pub last_updated_con_count: Cint64,
    /// `bool mReviewMarked`.
    pub review_marked: bool,
    /// `bool mReviewSubsetMarked`.
    pub review_subset_marked: bool,
    /// `bool mIdenticConceptSetRequired`.
    pub identic_concept_set_required: bool,
    /// `bool mStillConceptSetSubset`.
    pub still_concept_set_subset: bool,
}

impl Default for SignatureBlockingIndividualNodeConceptExpansionData {
    /// The default ctor body is empty in C++ (every field is set by
    /// `initBlockingExpansionData`); this mirrors the `prevData == nullptr` branch.
    fn default() -> Self {
        SignatureBlockingIndividualNodeConceptExpansionData {
            subset_tested_con_des: ConDescId::NONE,
            blocker_indi_node: NodeId::NONE,
            blocking_concept_signature: 0,
            blocking_concept_count: 0,
            expanded_contained_concept_count: 0,
            last_updated_con_exp_count: 0,
            last_updated_con_count: 0,
            review_marked: false,
            review_subset_marked: false,
            identic_concept_set_required: false,
            still_concept_set_subset: true,
        }
    }
}

impl SignatureBlockingIndividualNodeConceptExpansionData {
    /// Port of `CSignatureBlockingIndividualNodeConceptExpansionData()` (empty ctor).
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initBlockingExpansionData`.
    pub fn init_blocking_expansion_data(
        &mut self,
        prev: Option<&SignatureBlockingIndividualNodeConceptExpansionData>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.subset_tested_con_des = prev.subset_tested_con_des;
            self.blocking_concept_signature = prev.blocking_concept_signature;
            self.blocking_concept_count = prev.blocking_concept_count;
            self.expanded_contained_concept_count = prev.expanded_contained_concept_count;
            self.last_updated_con_exp_count = prev.last_updated_con_exp_count;
            self.blocker_indi_node = prev.blocker_indi_node;
            self.last_updated_con_count = prev.last_updated_con_count;
            self.review_marked = prev.review_marked;
            self.review_subset_marked = prev.review_subset_marked;
            self.identic_concept_set_required = prev.identic_concept_set_required;
            self.still_concept_set_subset = prev.still_concept_set_subset;
        } else {
            self.subset_tested_con_des = ConDescId::NONE;
            self.blocker_indi_node = NodeId::NONE;
            self.blocking_concept_signature = 0;
            self.blocking_concept_count = 0;
            self.expanded_contained_concept_count = 0;
            self.last_updated_con_exp_count = 0;
            self.last_updated_con_count = 0;
            self.review_marked = false;
            self.review_subset_marked = false;
            self.identic_concept_set_required = false;
            self.still_concept_set_subset = true;
        }
        self
    }

    /// Port of `getLastSubsetTestedConceptDescriptor`.
    pub fn get_last_subset_tested_concept_descriptor(&self) -> ConDescId {
        self.subset_tested_con_des
    }
    /// Port of `getBlockingConceptSignature` (the C++ getter is mis-named
    /// `setBlockingConceptSignature()` — a no-arg returning `mBlockingConceptSignature`).
    pub fn get_blocking_concept_signature(&self) -> Cint64 {
        self.blocking_concept_signature
    }
    /// Port of `getBlockingConceptCount`.
    pub fn get_blocking_concept_count(&self) -> Cint64 {
        self.blocking_concept_count
    }
    /// Port of `getContinuousExpandedContainedConceptCount`.
    pub fn get_continuous_expanded_contained_concept_count(&self) -> Cint64 {
        self.expanded_contained_concept_count
    }
    /// Port of `getLastUpdatedConceptExpansionCount`.
    pub fn get_last_updated_concept_expansion_count(&self) -> Cint64 {
        self.last_updated_con_exp_count
    }
    /// Port of `getLastUpdatedConceptCount`.
    pub fn get_last_updated_concept_count(&self) -> Cint64 {
        self.last_updated_con_count
    }
    /// Port of `getBlockerIndividualNode`.
    pub fn get_blocker_individual_node(&self) -> NodeId {
        self.blocker_indi_node
    }
    /// Port of `isBlockingReviewMarked`.
    pub fn is_blocking_review_marked(&self) -> bool {
        self.review_marked
    }
    /// Port of `isBlockingSubsetReviewMarked`.
    pub fn is_blocking_subset_review_marked(&self) -> bool {
        self.review_subset_marked
    }
    /// Port of `isIdenticConceptSetRequired`.
    pub fn is_identic_concept_set_required(&self) -> bool {
        self.identic_concept_set_required
    }
    /// Port of `isConceptSetStillSubset`.
    pub fn is_concept_set_still_subset(&self) -> bool {
        self.still_concept_set_subset
    }

    /// Port of `setLastSubsetTestedConceptDescriptor`.
    pub fn set_last_subset_tested_concept_descriptor(&mut self, con_des: ConDescId) -> &mut Self {
        self.subset_tested_con_des = con_des;
        self
    }
    /// Port of `setBlockingConceptSignature(cint64)`.
    pub fn set_blocking_concept_signature(&mut self, signature: Cint64) -> &mut Self {
        self.blocking_concept_signature = signature;
        self
    }
    /// Port of `setBlockingConceptCount`.
    pub fn set_blocking_concept_count(&mut self, con_count: Cint64) -> &mut Self {
        self.blocking_concept_count = con_count;
        self
    }
    /// Port of `setContinuousExpandedContainedConceptCount`.
    pub fn set_continuous_expanded_contained_concept_count(
        &mut self,
        con_count: Cint64,
    ) -> &mut Self {
        self.expanded_contained_concept_count = con_count;
        self
    }
    /// Port of `setLastUpdatedConceptExpansionCount`.
    pub fn set_last_updated_concept_expansion_count(&mut self, con_count: Cint64) -> &mut Self {
        self.last_updated_con_exp_count = con_count;
        self
    }
    /// Port of `setLastUpdatedConceptCount`.
    pub fn set_last_updated_concept_count(&mut self, con_count: Cint64) -> &mut Self {
        self.last_updated_con_count = con_count;
        self
    }
    /// Port of `setBlockerIndividualNode`.
    pub fn set_blocker_individual_node(&mut self, node: NodeId) -> &mut Self {
        self.blocker_indi_node = node;
        self
    }
    /// Port of `setBlockingReviewMarked`.
    pub fn set_blocking_review_marked(&mut self, marked: bool) -> &mut Self {
        self.review_marked = marked;
        self
    }
    /// Port of `setBlockingSubsetReviewMarked`.
    pub fn set_blocking_subset_review_marked(&mut self, marked: bool) -> &mut Self {
        self.review_subset_marked = marked;
        self
    }
    /// Port of `setIdenticConceptSetRequired`.
    pub fn set_identic_concept_set_required(
        &mut self,
        identic_concept_set_required: bool,
    ) -> &mut Self {
        self.identic_concept_set_required = identic_concept_set_required;
        self
    }
    /// Port of `setConceptSetStillSubset`.
    pub fn set_concept_set_still_subset(&mut self, still_subset: bool) -> &mut Self {
        self.still_concept_set_subset = still_subset;
        self
    }
}

/// Port of `CReusingIndividualNodeConceptExpansionData`.
///
/// KONCLUDE-PORT-NOTE[inheritance]: the C++ class derives from
/// `CSignatureBlockingIndividualNodeConceptExpansionData`; the Rust port folds
/// the base object into `blocking_expansion_data` and forwards the base methods
/// needed by existing call sites.
#[derive(Clone, Debug)]
pub struct ReusingIndividualNodeConceptExpansionData {
    pub blocking_expansion_data: SignatureBlockingIndividualNodeConceptExpansionData,
    pub reusing_tried_count: Cint64,
    pub reusing_failed_count: Cint64,
    pub reused_individuals: BTreeSet<Cint64>,
    pub reused_concept_set_signatures: BTreeSet<Cint64>,
    pub reuse_concepts_dependency_track_point: TrackPointId,
    pub last_non_det_expansion_linker: Vec<ConDescId>,
}

impl Default for ReusingIndividualNodeConceptExpansionData {
    fn default() -> Self {
        Self {
            blocking_expansion_data: SignatureBlockingIndividualNodeConceptExpansionData::default(),
            reusing_tried_count: 0,
            reusing_failed_count: 0,
            reused_individuals: BTreeSet::new(),
            reused_concept_set_signatures: BTreeSet::new(),
            reuse_concepts_dependency_track_point: TrackPointId::NONE,
            last_non_det_expansion_linker: Vec::new(),
        }
    }
}

impl ReusingIndividualNodeConceptExpansionData {
    /// Port of `CReusingIndividualNodeConceptExpansionData()`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initReusingExpansionData`.
    pub fn init_reusing_expansion_data(
        &mut self,
        prev: Option<&ReusingIndividualNodeConceptExpansionData>,
    ) -> &mut Self {
        if let Some(prev) = prev {
            self.blocking_expansion_data
                .init_blocking_expansion_data(Some(&prev.blocking_expansion_data));
            self.reusing_tried_count = prev.reusing_tried_count;
            self.reusing_failed_count = prev.reusing_failed_count;
            self.reuse_concepts_dependency_track_point = prev.reuse_concepts_dependency_track_point;
            self.last_non_det_expansion_linker = prev.last_non_det_expansion_linker.clone();
        } else {
            self.blocking_expansion_data
                .init_blocking_expansion_data(None);
            self.reusing_tried_count = 0;
            self.reusing_failed_count = 0;
            self.reuse_concepts_dependency_track_point = TrackPointId::NONE;
            self.last_non_det_expansion_linker.clear();
        }
        self
    }

    /// Port of `getReusingTriedCount`.
    pub fn get_reusing_tried_count(&self) -> Cint64 {
        self.reusing_tried_count
    }

    /// Port of `getReusingFailedCount`.
    pub fn get_reusing_failed_count(&self) -> Cint64 {
        self.reusing_failed_count
    }

    /// Port of `setReusingTriedCount`.
    pub fn set_reusing_tried_count(&mut self, tried_count: Cint64) -> &mut Self {
        self.reusing_tried_count = tried_count;
        self
    }

    /// Port of `setReusingFailedCount`.
    pub fn set_reusing_failed_count(&mut self, failed_count: Cint64) -> &mut Self {
        self.reusing_failed_count = failed_count;
        self
    }

    /// Port of `incReusingTriedCount`.
    pub fn inc_reusing_tried_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.reusing_tried_count += inc_count;
        self
    }

    /// Port of `incReusingFailedCount`.
    pub fn inc_reusing_failed_count(&mut self, inc_count: Cint64) -> &mut Self {
        self.reusing_failed_count += inc_count;
        self
    }

    /// Port of `addReusingFailedSignatureAndIndividual`.
    pub fn add_reusing_failed_signature_and_individual(
        &mut self,
        con_set_signature: Cint64,
        individual_id: Cint64,
    ) -> &mut Self {
        self.reused_individuals.insert(individual_id);
        self.reused_concept_set_signatures.insert(con_set_signature);
        self
    }

    /// Port of `getReuseConceptsDependencyTrackPoint`.
    pub fn get_reuse_concepts_dependency_track_point(&self) -> TrackPointId {
        self.reuse_concepts_dependency_track_point
    }

    /// Port of `setReuseConceptsDependencyTrackPoint`.
    pub fn set_reuse_concepts_dependency_track_point(
        &mut self,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
        self.reuse_concepts_dependency_track_point = dep_track_point;
        self
    }

    /// Port of `getLastNonDeterministicExpansionLinker`.
    pub fn get_last_non_deterministic_expansion_linker(&self) -> &[ConDescId] {
        &self.last_non_det_expansion_linker
    }

    /// Port of `setLastNonDeterministicExpansionLinker`.
    pub fn set_last_non_deterministic_expansion_linker(
        &mut self,
        exp_linker: Vec<ConDescId>,
    ) -> &mut Self {
        self.last_non_det_expansion_linker = exp_linker;
        self
    }

    /// Base-class forwarder for `getBlockerIndividualNode`.
    pub fn get_blocker_individual_node(&self) -> NodeId {
        self.blocking_expansion_data.get_blocker_individual_node()
    }

    /// Base-class forwarder for `setBlockerIndividualNode`.
    pub fn set_blocker_individual_node(&mut self, node: NodeId) -> &mut Self {
        self.blocking_expansion_data
            .set_blocker_individual_node(node);
        self
    }

    /// Base-class forwarder for `isConceptSetStillSubset`.
    pub fn is_concept_set_still_subset(&self) -> bool {
        self.blocking_expansion_data.is_concept_set_still_subset()
    }

    /// Base-class forwarder for `setConceptSetStillSubset`.
    pub fn set_concept_set_still_subset(&mut self, still_subset: bool) -> &mut Self {
        self.blocking_expansion_data
            .set_concept_set_still_subset(still_subset);
        self
    }
}
