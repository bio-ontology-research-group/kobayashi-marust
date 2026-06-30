//! `process::blocking_hash` — port unit **W3.5b**: the remaining blocking-family
//! satellites the signature / dynamic-blocking un-defers (`completion/u18`,
//! `u19`, `u20`, `u31`, `u35`) reach into.
//!
//! Sources (`Source/Reasoner/Kernel/Process/`):
//!   * `CBlockingIndividualNodeCandidateData.{h,cpp}`     → [`BlockingIndividualNodeCandidateData`]
//!   * `CBlockingIndividualNodeCandidateIterator.{h,cpp}` → [`BlockingIndividualNodeCandidateIterator`]
//!   * `CBlockingIndividualNodeCandidateHash.{h,cpp}`     → [`BlockingIndividualNodeCandidateHash`]
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

use std::collections::{BTreeMap, HashMap};

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::ConceptId;
use super::context::ProcessContext;
use super::satellites::ConceptLabelSetModificationTag;
use super::{ConDescId, NodeId};

// ===========================================================================
// id aliases
// ===========================================================================

/// `CBlockingIndividualNodeCandidateHash*` → `BlockingIndividualNodeCandidateHashId`.
pub type BlockingIndividualNodeCandidateHashId = Id<BlockingIndividualNodeCandidateHash>;
/// `CBlockingIndividualNodeCandidateData*` → `BlockingIndividualNodeCandidateDataId`.
pub type BlockingIndividualNodeCandidateDataId = Id<BlockingIndividualNodeCandidateData>;
/// `CSignatureBlockingIndividualNodeConceptExpansionData*` →
/// `SignatureBlockingIndividualNodeConceptExpansionDataId`.
/// KONCLUDE-PORT-NOTE[ownership]: reconciles the W2 `process::stubs`
/// `SignatureBlockingIndividualNodeConceptExpansionData => SigBlockConExpDataId`
/// marker (`node.rs`'s `sig_block_con_exp_data` / `prev_sig_block_con_exp_data`
/// fields point here once the stub re-aliases below).
pub type SignatureBlockingIndividualNodeConceptExpansionDataId =
    Id<SignatureBlockingIndividualNodeConceptExpansionData>;

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
        BlockingIndividualNodeCandidateIterator::new(&self.candidate_indi_map, candidate_individual_id)
    }

    /// Port of `getBlockingCandidatesIndividualNodeIterator(CIndividualProcessNode*)`.
    pub fn get_blocking_candidates_individual_node_iterator_for_node(
        &self,
        candidate_indi: NodeId,
        ctx: &ProcessContext,
    ) -> BlockingIndividualNodeCandidateIterator {
        self.get_blocking_candidates_individual_node_iterator(ctx.node(candidate_indi).individual_node_id())
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
/// / `removeLast` are faithful over the snapshot. `removeLastIndividualCandidate`
/// drops from the snapshot and reports the removed key; propagating the erase to
/// the owning arena map is `W3.5b-DEFER[api]` (the C++ `mCandidateMap->erase(it)`
/// mutates the shared map; the arena map is reached via `&mut ctx`, which the
/// snapshot iterator does not hold — the un-defer wave threads it).
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
}

impl BlockingIndividualNodeCandidateIterator {
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
        }
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

    /// Port of `removeLastIndividualCandidate` (over the snapshot; arena-map erase
    /// propagation is `W3.5b-DEFER[api]`). Returns `true` if a candidate was removed.
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
                let new_data =
                    ctx.alloc_blocking_indi_node_cand_data(BlockingIndividualNodeCandidateData::new(INVALID));
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
#[derive(Clone)]
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
    pub fn set_continuous_expanded_contained_concept_count(&mut self, con_count: Cint64) -> &mut Self {
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
    pub fn set_identic_concept_set_required(&mut self, identic_concept_set_required: bool) -> &mut Self {
        self.identic_concept_set_required = identic_concept_set_required;
        self
    }
    /// Port of `setConceptSetStillSubset`.
    pub fn set_concept_set_still_subset(&mut self, still_subset: bool) -> &mut Self {
        self.still_concept_set_subset = still_subset;
        self
    }
}
