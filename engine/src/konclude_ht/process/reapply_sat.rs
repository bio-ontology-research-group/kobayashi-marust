//! `process::reapply_sat` (port unit W2.7 — the "fill wave" satellite subsystem)
//! — the reapply-label-set iterator, the signature blocking-candidate
//! hash/data/iterator/linker, the per-node blocking-test data, the blocking
//! alternative data, and the per-node incremental-expansion data.
//!
//! These are the `Process/` satellite helper classes that the deferred completion
//! bodies (`completion/u18.rs` signature-blocking, `completion/u26.rs`
//! incremental-expansion; the `u16/u18/u26` blocking + reapply families) reach
//! into. W2 stubbed them as zero-size markers (`process::stubs`); this unit ports
//! them for real so those bodies can later un-defer.
//!
//! Sources (`Source/Reasoner/Kernel/Process/`):
//!   * `CReapplyConceptLabelSetIterator.{h,cpp}`
//!   * `CSignatureBlockingCandidateData.{h,cpp}` / `CSignatureBlockingCandidateHash.{h,cpp}`
//!     / `CSignatureBlockingCandidateIterator.{h,cpp}` / `CSignatureIterator.{h,cpp}`
//!   * `CIndividualNodeBlockingTestData.{h,cpp}` (`: CIndividualNodeBlockData,
//!     CNodeSwitchTag, CConceptLabelSetModificationTag`)
//!   * `CBlockingAlternativeData.{h,cpp}` + `CBlockingAlternativeSignatureBlockingCandidateData.{h,cpp}`
//!   * `CIndividualNodeIncrementalExpansionData.{h,cpp}`
//!
//! KONCLUDE-PORT-NOTE[ownership]: every raw `CXxx*` becomes the matching `Id<T>`
//! (the global substrate decision); the intrusive `CXLinker<cint64>*` candidate
//! chains and `CPROCESSLIST<…>*` working lists become owned `Vec`s (head-front,
//! per `PORT.md` §6). The `CPROCESSMAP::const_iterator` cursors the label-set
//! iterator holds become `Vec`-snapshot + `usize` position cursors.
//! KONCLUDE-PORT-NOTE[pointer-alias]: where a C++ method dereferences a pooled
//! object (`indi->getIndividualNodeID()`, `conDes->getNext()`,
//! `conDes->getDependencyTrackPoint()`), the port threads `&ProcessContext` and
//! resolves the id against the arena (`ctx.node(id)…` / `ctx.con_desc(id)…`).

#![allow(dead_code)]

use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::IndividualId;
use super::context::ProcessContext;
use super::satellites::{
    ConceptLabelSetModificationTag, ConceptSetSignature, CondensedReapplyQueue,
    CoreConceptDescriptorId,
};
use super::{ConDescId, EdgeId, NodeId, TrackPointId};

// ===========================================================================
// W2.7 arena id aliases (the `CXxx*` → `Id<T>` replacements for this unit).
// ===========================================================================

/// `CSignatureBlockingCandidateHash*` → `SigBlockCandHashId`.
pub type SigBlockCandHashId = Id<SignatureBlockingCandidateHash>;
/// `CIndividualNodeBlockingTestData*` → `BlockingTestDataId`.
/// KONCLUDE-PORT-NOTE[ownership]: reconciles the W2 `process::stubs`
/// `IndividualNodeBlockData => IndiBlockDataId` marker — `node.rs`'s
/// `indi_block: IndiBlockDataId` field's runtime object is a
/// `CIndividualNodeBlockingTestData` (the derived class); this is its real arena id.
pub type BlockingTestDataId = Id<IndividualNodeBlockingTestData>;
/// `CBlockingAlternativeSignatureBlockingCandidateData*` → `BlockingAltDataId`
/// (the only concrete `CBlockingAlternativeData` subclass).
pub type BlockingAltDataId = Id<BlockingAlternativeSignatureBlockingCandidateData>;
/// `CIndividualNodeIncrementalExpansionData*` → `IncrementalExpansionDataId`.
/// KONCLUDE-PORT-NOTE[ownership]: reconciles the W2 `process::stubs`
/// `IndividualNodeIncrementalExpansionData => IncExpDataId` marker (`node.rs`'s
/// `use_inc_exp_data` / `loc_inc_exp_data` fields point here).
pub type IncrementalExpansionDataId = Id<IndividualNodeIncrementalExpansionData>;
/// `CCondensedReapplyConceptDescriptor*` → `CondensedReapplyConceptDescriptorId`.
pub type CondensedReapplyConceptDescriptorId = Id<CondensedReapplyConceptDescriptor>;
/// `CReapplyConceptDescriptor*` → `ReapplyConceptDescriptorId`.
pub type ReapplyConceptDescriptorId = Id<ReapplyConceptDescriptor>;

// ===========================================================================
// CReapplyConceptLabelSetIterator
// ===========================================================================

/// One entry of a label-set reapply-map stream, the port of dereferencing a
/// `CPROCESSMAP<cint64,CConceptDescriptorDependencyReapplyData>::const_iterator`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the C++ iterator holds live `const_iterator`s
/// into the label set's two `mConceptDesDepMap` / `mAdditionalConceptDesDepMap`
/// maps and reads `.key()` / `.value().mConceptDescriptor` /
/// `.value().mPosNegReapplyQueue`. To avoid a self-referential borrow of the
/// arena-held label set, `getConceptLabelSetIterator` (LS-1, deferred) snapshots
/// each map into a key-sorted `Vec<LabelSetMapEntry>`; the merge-by-key logic in
/// `moveNext`/`getDataTag`/… is reproduced byte-exactly over the two cursors.
#[derive(Clone)]
pub struct LabelSetMapEntry {
    /// the map key (`it.key()`).
    pub key: Cint64,
    /// `it.value().mConceptDescriptor` (`nullptr` == `Id::NONE`).
    pub concept_descriptor: ConDescId,
    // KONCLUDE-PORT-NOTE[api]: `it.value().mPosNegReapplyQueue` is a
    // `CCondensedReapplyQueue` held by value in the map value; the iterator's
    // `getPosNegReapplyQueue` returns `&` it. The condensed-reapply-queue class is
    // a not-yet-ported placeholder (`satellites::CondensedReapplyQueue`); kept by
    // value here so the reference path stays exact when it lands.
    pub pos_neg_reapply_queue: CondensedReapplyQueue,
}

/// Port of `CReapplyConceptLabelSetIterator`.
///
/// Iterates a node's concept label set: first the unmerged `mConceptDesLinkerIt`
/// descriptor chain (the recently-added, not-yet-folded-into-map descriptors),
/// then the merge of the two sorted reapply-map streams.
pub struct ReapplyConceptLabelSetIterator {
    // mConDesDepBeginIt / mConDesDepEndIt → Vec snapshot + position cursor.
    con_des_dep: Vec<LabelSetMapEntry>,
    con_des_dep_pos: usize,
    // mAdditionalConDesDepBeginIt / mAdditionalConDesDepEndIt.
    additional_con_des_dep: Vec<LabelSetMapEntry>,
    additional_con_des_dep_pos: usize,
    // KONCLUDE-PORT-NOTE[ownership]: `CConceptDescriptor* mConceptDesLinkerIt` → `ConDescId`.
    concept_des_linker_it: ConDescId,
    concept_count: Cint64,
    skip_empty_concept_descriptors: bool,
}

impl ReapplyConceptLabelSetIterator {
    /// Port of the `CReapplyConceptLabelSetIterator(...)` ctor (incl. the
    /// construction-time skip-empty advance of both map cursors).
    pub fn new(
        concept_count: Cint64,
        concept_des_linker: ConDescId,
        con_des_dep: Vec<LabelSetMapEntry>,
        additional_con_des_dep: Vec<LabelSetMapEntry>,
        skip_empty_concept_descriptors: bool,
    ) -> Self {
        let mut it = ReapplyConceptLabelSetIterator {
            concept_count,
            concept_des_linker_it: concept_des_linker,
            con_des_dep,
            con_des_dep_pos: 0,
            additional_con_des_dep,
            additional_con_des_dep_pos: 0,
            skip_empty_concept_descriptors,
        };
        if it.skip_empty_concept_descriptors {
            while it.con_des_dep_pos != it.con_des_dep.len()
                && it.con_des_dep[it.con_des_dep_pos]
                    .concept_descriptor
                    .is_none()
            {
                it.con_des_dep_pos += 1;
            }
            while it.additional_con_des_dep_pos != it.additional_con_des_dep.len()
                && it.additional_con_des_dep[it.additional_con_des_dep_pos]
                    .concept_descriptor
                    .is_none()
            {
                it.additional_con_des_dep_pos += 1;
            }
        }
        it
    }

    /// Port of `getRemainingConceptCount`.
    pub fn get_remaining_concept_count(&self) -> Cint64 {
        self.concept_count
    }

    /// Port of `operator++` (`return *moveNext();`).
    pub fn next_pp(&mut self, ctx: &ProcessContext) -> &mut Self {
        self.move_next(ctx)
    }

    /// Port of `operator*` (`return getConceptDescriptor();`).
    pub fn deref(&self) -> ConDescId {
        self.get_concept_descriptor()
    }

    /// Port of `moveNext`. KONCLUDE-PORT-NOTE[pointer-alias]: the linker advance
    /// `mConceptDesLinkerIt = mConceptDesLinkerIt->getNext()` resolves through the
    /// descriptor arena, hence the `&ProcessContext`.
    pub fn move_next(&mut self, ctx: &ProcessContext) -> &mut Self {
        if self.concept_des_linker_it.is_some() {
            self.concept_des_linker_it = ctx
                .con_desc(self.concept_des_linker_it)
                .get_next_concept_descriptor();
            self.concept_count -= 1;
        } else if self.con_des_dep_pos != self.con_des_dep.len()
            || self.additional_con_des_dep_pos != self.additional_con_des_dep.len()
        {
            if self.con_des_dep_pos != self.con_des_dep.len()
                && self.additional_con_des_dep_pos != self.additional_con_des_dep.len()
            {
                let add_key = self.additional_con_des_dep[self.additional_con_des_dep_pos].key;
                let main_key = self.con_des_dep[self.con_des_dep_pos].key;
                if add_key == main_key {
                    self.additional_con_des_dep_pos += 1;
                    self.con_des_dep_pos += 1;
                } else if add_key < main_key {
                    self.additional_con_des_dep_pos += 1;
                } else {
                    self.con_des_dep_pos += 1;
                }
            } else if self.con_des_dep_pos == self.con_des_dep.len() {
                self.additional_con_des_dep_pos += 1;
            } else {
                self.con_des_dep_pos += 1;
            }
            if self.skip_empty_concept_descriptors {
                while self.con_des_dep_pos != self.con_des_dep.len()
                    && self.con_des_dep[self.con_des_dep_pos]
                        .concept_descriptor
                        .is_none()
                {
                    self.con_des_dep_pos += 1;
                }
                while self.additional_con_des_dep_pos != self.additional_con_des_dep.len()
                    && self.additional_con_des_dep[self.additional_con_des_dep_pos]
                        .concept_descriptor
                        .is_none()
                {
                    self.additional_con_des_dep_pos += 1;
                }
            }
            self.concept_count -= 1;
        }
        self
    }

    /// Port of `getDataTag`. KONCLUDE-PORT-NOTE[pointer-alias]: the linker branch
    /// `mConceptDesLinkerIt->getConceptTag()` resolves the descriptor against the
    /// process-context descriptor arena, then reads the wrapped concept's tag from
    /// the static terminology (`CConceptDescriptor::getConceptTag`, now ported in
    /// `descriptor.rs`); the merged-map branches read the map key directly.
    pub fn get_data_tag(&self, ctx: &ProcessContext, onto: &OntologyArenas) -> Cint64 {
        if self.concept_des_linker_it.is_some() {
            ctx.con_desc(self.concept_des_linker_it)
                .get_concept_tag(onto)
        } else if self.con_des_dep_pos != self.con_des_dep.len()
            && self.additional_con_des_dep_pos != self.additional_con_des_dep.len()
        {
            let add_key = self.additional_con_des_dep[self.additional_con_des_dep_pos].key;
            let main_key = self.con_des_dep[self.con_des_dep_pos].key;
            if add_key < main_key {
                add_key
            } else {
                main_key
            }
        } else if self.con_des_dep_pos == self.con_des_dep.len() {
            self.additional_con_des_dep[self.additional_con_des_dep_pos].key
        } else {
            self.con_des_dep[self.con_des_dep_pos].key
        }
    }

    /// Port of `getConceptDescriptor`.
    pub fn get_concept_descriptor(&self) -> ConDescId {
        if self.concept_des_linker_it.is_some() {
            self.concept_des_linker_it
        } else if self.con_des_dep_pos != self.con_des_dep.len()
            && self.additional_con_des_dep_pos != self.additional_con_des_dep.len()
        {
            let add = &self.additional_con_des_dep[self.additional_con_des_dep_pos];
            let main = &self.con_des_dep[self.con_des_dep_pos];
            if add.key < main.key {
                add.concept_descriptor
            } else {
                main.concept_descriptor
            }
        } else if self.con_des_dep_pos == self.con_des_dep.len() {
            self.additional_con_des_dep[self.additional_con_des_dep_pos].concept_descriptor
        } else {
            self.con_des_dep[self.con_des_dep_pos].concept_descriptor
        }
    }

    /// Port of `getDependencyTrackPoint`.
    /// KONCLUDE-PORT-NOTE[pointer-alias]: both branches deref a `CConceptDescriptor`
    /// (`->getDependencyTrackPoint()`) → resolve via the descriptor arena.
    pub fn get_dependency_track_point(&self, ctx: &ProcessContext) -> TrackPointId {
        if self.concept_des_linker_it.is_some() {
            ctx.con_desc(self.concept_des_linker_it)
                .get_dependency_track_point()
        } else {
            let con_des = self.get_concept_descriptor();
            if con_des.is_some() {
                ctx.con_desc(con_des).get_dependency_track_point()
            } else {
                TrackPointId::NONE
            }
        }
    }

    /// Port of `getPosNegReapplyQueue`. Returns `None` for the linker branch
    /// (C++ `nullptr`), else a borrow of the active map entry's queue.
    pub fn get_pos_neg_reapply_queue(&self) -> Option<&CondensedReapplyQueue> {
        if self.concept_des_linker_it.is_some() {
            None
        } else if self.con_des_dep_pos != self.con_des_dep.len()
            && self.additional_con_des_dep_pos != self.additional_con_des_dep.len()
        {
            let add = &self.additional_con_des_dep[self.additional_con_des_dep_pos];
            let main = &self.con_des_dep[self.con_des_dep_pos];
            if add.key < main.key {
                Some(&add.pos_neg_reapply_queue)
            } else {
                Some(&main.pos_neg_reapply_queue)
            }
        } else if self.con_des_dep_pos == self.con_des_dep.len() {
            Some(
                &self.additional_con_des_dep[self.additional_con_des_dep_pos].pos_neg_reapply_queue,
            )
        } else {
            Some(&self.con_des_dep[self.con_des_dep_pos].pos_neg_reapply_queue)
        }
    }

    /// Port of `next(bool moveToNext)`.
    pub fn next(&mut self, move_to_next: bool, ctx: &ProcessContext) -> ConDescId {
        let con_des = self.get_concept_descriptor();
        if move_to_next {
            self.move_next(ctx);
        }
        con_des
    }

    /// Port of `hasValue`.
    pub fn has_value(&self) -> bool {
        self.concept_des_linker_it.is_some()
            || self.con_des_dep_pos != self.con_des_dep.len()
            || self.additional_con_des_dep_pos != self.additional_con_des_dep.len()
    }

    /// Port of `hasNext` (identical body to `hasValue` in the C++).
    pub fn has_next(&self) -> bool {
        self.concept_des_linker_it.is_some()
            || self.con_des_dep_pos != self.con_des_dep.len()
            || self.additional_con_des_dep_pos != self.additional_con_des_dep.len()
    }

    // KONCLUDE-PORT-NOTE[unclear]: the C++ `operator!=` / `operator==` compare the
    // additional-map BEGIN cursor against the other iterator's additional-map END
    // cursor (`mAdditionalConDesDepBeginIt != iterator.mAdditionalConDesDepEndIt`)
    // — almost certainly a copy/paste slip in the original, but ported verbatim so
    // the two trees diff method-by-method. The `end` cursor of a snapshot stream is
    // its length, so the additional-map comparison is against `other`'s length.
    /// Port of `operator!=`.
    pub fn ne(&self, other: &ReapplyConceptLabelSetIterator) -> bool {
        self.concept_des_linker_it != other.concept_des_linker_it
            || self.con_des_dep_pos != other.con_des_dep_pos
            || self.additional_con_des_dep_pos != other.additional_con_des_dep.len()
    }

    /// Port of `operator==`.
    pub fn eq(&self, other: &ReapplyConceptLabelSetIterator) -> bool {
        self.concept_des_linker_it == other.concept_des_linker_it
            && self.con_des_dep_pos == other.con_des_dep_pos
            && self.additional_con_des_dep_pos != other.additional_con_des_dep.len()
    }
}

// ===========================================================================
// CSignatureBlockingCandidateData  (+ the hash, the two iterators)
// ===========================================================================

/// Port of `CSignatureBlockingCandidateData` — the per-signature value of the
/// blocking-candidate hash: the chain of candidate individual-node ids + a count.
#[derive(Clone)]
pub struct SignatureBlockingCandidateData {
    // KONCLUDE-PORT-NOTE[ownership]: `CXLinker<cint64>* mCandidateIndiLinker` → an
    // owned head-front `Vec<cint64>` of candidate individual-node ids (PORT.md §6).
    pub candidate_indi_linker: Vec<Cint64>,
    /// `cint64 mCandidateCount`.
    pub candidate_count: Cint64,
}

impl Default for SignatureBlockingCandidateData {
    /// Port of the inline default ctor (`mCandidateIndiLinker = nullptr; mCandidateCount = 0`).
    fn default() -> Self {
        SignatureBlockingCandidateData {
            candidate_indi_linker: Vec::new(),
            candidate_count: 0,
        }
    }
}

impl SignatureBlockingCandidateData {
    /// Port of `getCandidateIndividualLinker`.
    pub fn get_candidate_individual_linker(&self) -> &[Cint64] {
        &self.candidate_indi_linker
    }
    /// Port of `getCandidateIndividualCount`.
    pub fn get_candidate_individual_count(&self) -> Cint64 {
        self.candidate_count
    }
}

/// Port of `CSignatureBlockingCandidateIterator` — walks the candidate-id chain
/// of one signature.
pub struct SignatureBlockingCandidateIterator {
    msignature: Cint64,
    // KONCLUDE-PORT-NOTE[ownership]: `CXLinker<cint64>* mCandidateIndiLinkerIt` (a
    // raw cursor into the hash value's chain) → an owned snapshot + position.
    candidate_indi_linker: Vec<Cint64>,
    candidate_indi_linker_pos: usize,
}

impl SignatureBlockingCandidateIterator {
    /// Port of the `CSignatureBlockingCandidateIterator(signature, candidateIndiLinker)` ctor.
    pub fn new(signature: Cint64, candidate_indi_linker: Vec<Cint64>) -> Self {
        SignatureBlockingCandidateIterator {
            msignature: signature,
            candidate_indi_linker,
            candidate_indi_linker_pos: 0,
        }
    }

    /// Port of `hasNext` (`mCandidateIndiLinkerIt != nullptr`).
    pub fn has_next(&self) -> bool {
        self.candidate_indi_linker_pos != self.candidate_indi_linker.len()
    }

    /// Port of `next(bool moveNext)`.
    pub fn next(&mut self, move_next: bool) -> Cint64 {
        let mut indi_id: Cint64 = -1;
        if self.candidate_indi_linker_pos != self.candidate_indi_linker.len() {
            indi_id = self.candidate_indi_linker[self.candidate_indi_linker_pos];
            if move_next {
                self.candidate_indi_linker_pos += 1;
            }
        }
        indi_id
    }

    /// The signature this iterator was opened for (`mSignature`).
    pub fn signature(&self) -> Cint64 {
        self.msignature
    }
}

/// Port of `CSignatureIterator` — walks every (signature → candidate chain) entry
/// of a `CSignatureBlockingCandidateHash`.
pub struct SignatureIterator {
    // KONCLUDE-PORT-NOTE[ownership]: `CPROCESSHASH<…>* mSigHash` + begin/end
    // const_iterators → a snapshot of `(signature, candidate chain)` pairs + pos.
    // `CPROCESSHASH` is unordered, so iteration order is unspecified in the C++ too.
    entries: Vec<(Cint64, Vec<Cint64>)>,
    pos: usize,
}

impl SignatureIterator {
    /// Port of the `CSignatureIterator(sigHash)` ctor (`mItBegin = constBegin()`, …).
    pub fn new(entries: Vec<(Cint64, Vec<Cint64>)>) -> Self {
        SignatureIterator { entries, pos: 0 }
    }

    /// Port of `hasNext`.
    pub fn has_next(&self) -> bool {
        self.pos != self.entries.len()
    }

    /// Port of `moveNext`.
    pub fn move_next(&mut self) -> bool {
        if self.pos != self.entries.len() {
            self.pos += 1;
            return true;
        }
        false
    }

    /// Port of `next(bool moveNext)`.
    pub fn next(&mut self, move_next: bool) -> Cint64 {
        let mut signature: Cint64 = -1;
        if self.pos != self.entries.len() {
            signature = self.entries[self.pos].0;
            if move_next {
                self.pos += 1;
            }
        }
        signature
    }

    /// Port of `getSignature`.
    pub fn get_signature(&self) -> Cint64 {
        if self.pos != self.entries.len() {
            self.entries[self.pos].0
        } else {
            -1
        }
    }

    /// Port of `getCandidateLinker`.
    pub fn get_candidate_linker(&self) -> &[Cint64] {
        if self.pos != self.entries.len() {
            &self.entries[self.pos].1
        } else {
            &[]
        }
    }
}

/// Port of `CSignatureBlockingCandidateHash` — signature → candidate-node-id
/// chain index used to find blocking candidates by concept-set signature.
#[derive(Clone)]
pub struct SignatureBlockingCandidateHash {
    // KONCLUDE-PORT-NOTE[ownership]: ambient `CProcessContext* mContext` (opaque).
    pub context: Cint64,
    // KONCLUDE-PORT-NOTE[memory-pool]: `CMemoryAllocationManager* mMemMan` (opaque).
    pub mem_man: Cint64,
    /// `CPROCESSHASH<cint64,CSignatureBlockingCandidateData> mSigBlockCandidateHash`.
    pub sig_block_candidate_hash: std::collections::HashMap<Cint64, SignatureBlockingCandidateData>,
}

impl Default for SignatureBlockingCandidateHash {
    fn default() -> Self {
        SignatureBlockingCandidateHash {
            context: INVALID,
            mem_man: INVALID,
            sig_block_candidate_hash: std::collections::HashMap::new(),
        }
    }
}

impl SignatureBlockingCandidateHash {
    /// Port of the `CSignatureBlockingCandidateHash(CProcessContext*)` ctor
    /// (`mMemMan = mContext->getUsedMemoryAllocationManager()`).
    pub fn new(context: Cint64) -> Self {
        SignatureBlockingCandidateHash {
            context,
            // W2.7-DEFER[api]: mContext->getUsedMemoryAllocationManager(); opaque pool handle.
            mem_man: INVALID,
            sig_block_candidate_hash: std::collections::HashMap::new(),
        }
    }

    /// Port of `initSignatureBlockingCandidateHash`.
    /// KONCLUDE-PORT-NOTE[ownership]: `mSigBlockCandidateHash = prev->mSigBlockCandidateHash`
    /// is an implicitly-shared (COW) assignment in C++; the port clones (behaviour
    /// identical, the `[memory-pool]` share optimisation is left for later).
    pub fn init_signature_blocking_candidate_hash(
        &mut self,
        prev_sig_block_cand_hash: Option<&SignatureBlockingCandidateHash>,
    ) -> &mut Self {
        if let Some(prev) = prev_sig_block_cand_hash {
            self.sig_block_candidate_hash = prev.sig_block_candidate_hash.clone();
        } else {
            self.sig_block_candidate_hash.clear();
        }
        self
    }

    /// Port of `insertSignatureBlockingCandidate(cint64, CIndividualProcessNode*)`.
    /// KONCLUDE-PORT-NOTE[pointer-alias]: `individualCandidate->getIndividualNodeID()`
    /// resolves against the node arena (hence `&ProcessContext`); the prepend
    /// `candLinker->initLinker(id, head); head = candLinker` is the head-front
    /// splice `insert(0, id)` (PORT.md §6).
    pub fn insert_signature_blocking_candidate(
        &mut self,
        signature: Cint64,
        individual_candidate: NodeId,
        ctx: &ProcessContext,
    ) -> &mut Self {
        let indi_cand_id = ctx.node(individual_candidate).individual_node_id();
        let data = self.sig_block_candidate_hash.entry(signature).or_default();
        data.candidate_indi_linker.insert(0, indi_cand_id);
        data.candidate_count += 1;
        self
    }

    /// Port of `insertSignatureBlockingCandidate(CConceptSetSignature*, …)`.
    pub fn insert_signature_blocking_candidate_for_concept_set_signature(
        &mut self,
        signature: &ConceptSetSignature,
        individual_candidate: NodeId,
        ctx: &ProcessContext,
    ) -> &mut Self {
        self.insert_signature_blocking_candidate(
            signature.signature_value,
            individual_candidate,
            ctx,
        )
    }

    /// Port of `insertSignatureBlockingCandidates(cint64, CXLinker<cint64>*)`.
    /// KONCLUDE-PORT-NOTE[ownership]: `candidateLinker->append(data.mCandidateIndiLinker);
    /// data.mCandidateIndiLinker = candidateLinker;` splices the existing chain to
    /// the TAIL of the incoming chain, then makes the incoming chain the head —
    /// head-front: `[candidate_linker…, existing…]`.
    pub fn insert_signature_blocking_candidates(
        &mut self,
        signature: Cint64,
        candidate_linker: Vec<Cint64>,
    ) -> &mut Self {
        let data = self.sig_block_candidate_hash.entry(signature).or_default();
        data.candidate_count += candidate_linker.len() as Cint64;
        let mut new_chain = candidate_linker;
        if !data.candidate_indi_linker.is_empty() {
            new_chain.append(&mut data.candidate_indi_linker);
        }
        data.candidate_indi_linker = new_chain;
        self
    }

    /// Port of `getBlockingCandidatesIterator(cint64)`.
    pub fn get_blocking_candidates_iterator(
        &self,
        signature: Cint64,
    ) -> SignatureBlockingCandidateIterator {
        if let Some(data) = self.sig_block_candidate_hash.get(&signature) {
            SignatureBlockingCandidateIterator::new(signature, data.candidate_indi_linker.clone())
        } else {
            SignatureBlockingCandidateIterator::new(signature, Vec::new())
        }
    }

    /// Port of `getBlockingCandidatesIterator(CConceptSetSignature*)`.
    pub fn get_blocking_candidates_iterator_for_concept_set_signature(
        &self,
        signature: &ConceptSetSignature,
    ) -> SignatureBlockingCandidateIterator {
        self.get_blocking_candidates_iterator(signature.signature_value)
    }

    /// Port of `getBlockingCandidatesCount(cint64)`.
    pub fn get_blocking_candidates_count(&self, signature: Cint64) -> Cint64 {
        if let Some(data) = self.sig_block_candidate_hash.get(&signature) {
            return data.candidate_count;
        }
        0
    }

    /// Port of `getBlockingCandidatesCount(CConceptSetSignature*)`.
    pub fn get_blocking_candidates_count_for_concept_set_signature(
        &self,
        signature: &ConceptSetSignature,
    ) -> Cint64 {
        self.get_blocking_candidates_count(signature.signature_value)
    }

    /// Port of `getSignatureIterator`.
    pub fn get_signature_iterator(&self) -> SignatureIterator {
        let entries = self
            .sig_block_candidate_hash
            .iter()
            .map(|(k, v)| (*k, v.candidate_indi_linker.clone()))
            .collect();
        SignatureIterator::new(entries)
    }
}

// ===========================================================================
// CIndividualNodeBlockingTestData
// ===========================================================================

/// Port of `CIndividualNodeBlockingTestData`
/// (`: public CIndividualNodeBlockData, public CNodeSwitchTag,
/// public CConceptLabelSetModificationTag`).
///
/// KONCLUDE-PORT-NOTE[ownership]: the three polymorphic bases become composition.
/// `CIndividualNodeBlockData` carries no state (empty class) and is omitted;
/// `CNodeSwitchTag : CProcessTag` and `CConceptLabelSetModificationTag` each carry
/// a process-tag word, kept as inline fields. `CCoreConceptDescriptor*` is a
/// `CConceptDescriptor` subtype → `ConDescId` (matching `satellites.rs`'s
/// `core_con_des_linker`).
#[derive(Clone)]
pub struct IndividualNodeBlockingTestData {
    // --- base CNodeSwitchTag (: CProcessTag) ---
    // KONCLUDE-PORT-NOTE[api]: the full `CNodeSwitchTag` (init/update/up-to-date
    // tag protocol over a `CProcessTagger`) is a separate not-yet-ported unit; only
    // the marking word is modelled here. W2.7-DEFER[api] for its method protocol.
    pub node_switch_tag: Cint64,
    // --- base CConceptLabelSetModificationTag ---
    pub modification_tag: ConceptLabelSetModificationTag,

    // --- own fields ---
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode* mBlockingIndiNode` → `NodeId`.
    pub blocking_indi_node: NodeId,              // mBlockingIndiNode
    pub last_core_block_cand_con_des: ConDescId, // mLastCoreBlockCandConDes
    pub last_added_core_con_des: CoreConceptDescriptorId, // mLastAddedCoreConDes
    pub last_core_block_cand_node_diff: Cint64,  // mLastCoreBlockCandNodeDiff
}

impl Default for IndividualNodeBlockingTestData {
    /// Port of the `CIndividualNodeBlockingTestData()` ctor
    /// (`mBlockingIndiNode = nullptr`; the rest are init'd in `initBlockData`).
    fn default() -> Self {
        IndividualNodeBlockingTestData {
            node_switch_tag: 0,
            modification_tag: ConceptLabelSetModificationTag::default(),
            blocking_indi_node: NodeId::NONE,
            last_core_block_cand_con_des: ConDescId::NONE,
            last_added_core_con_des: CoreConceptDescriptorId::NONE,
            last_core_block_cand_node_diff: 0,
        }
    }
}

impl IndividualNodeBlockingTestData {
    /// Port of the `CIndividualNodeBlockingTestData()` ctor.
    pub fn new() -> Self {
        Self::default()
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

    /// Port of `initBlockData`.
    pub fn init_block_data(
        &mut self,
        prev_block_data: Option<&IndividualNodeBlockingTestData>,
    ) -> &mut Self {
        if let Some(prev) = prev_block_data {
            self.blocking_indi_node = prev.blocking_indi_node;
            self.last_added_core_con_des = prev.last_added_core_con_des;
            self.last_core_block_cand_con_des = prev.last_core_block_cand_con_des;
            self.last_core_block_cand_node_diff = prev.last_core_block_cand_node_diff;
        } else {
            self.blocking_indi_node = NodeId::NONE;
            self.last_added_core_con_des = CoreConceptDescriptorId::NONE;
            self.last_core_block_cand_con_des = ConDescId::NONE;
            self.last_core_block_cand_node_diff = 0;
        }
        self
    }

    /// Port of `getBlockingIndividualNode`.
    pub fn get_blocking_individual_node(&self) -> NodeId {
        self.blocking_indi_node
    }
    /// Port of `clearBlockingIndividualNode`.
    pub fn clear_blocking_individual_node(&mut self) -> &mut Self {
        self.blocking_indi_node = NodeId::NONE;
        self
    }
    /// Port of `setBlockingIndividualNode`.
    pub fn set_blocking_individual_node(&mut self, blocking_individual_node: NodeId) -> &mut Self {
        self.blocking_indi_node = blocking_individual_node;
        self
    }

    /// Port of `getLastCoreBlockingCandidateConceptDescriptor`.
    pub fn get_last_core_blocking_candidate_concept_descriptor(&self) -> ConDescId {
        self.last_core_block_cand_con_des
    }
    /// Port of `setLastCoreBlockingCandidateConceptDescriptor`.
    pub fn set_last_core_blocking_candidate_concept_descriptor(
        &mut self,
        last_core_block_cand_con_des: ConDescId,
    ) -> &mut Self {
        self.last_core_block_cand_con_des = last_core_block_cand_con_des;
        self
    }

    /// Port of `getLastCoreBlockingCandidateConceptNodeDifference`.
    pub fn get_last_core_blocking_candidate_concept_node_difference(&self) -> Cint64 {
        self.last_core_block_cand_node_diff
    }
    /// Port of `setLastCoreBlockingCandidateConceptNodeDifference`.
    pub fn set_last_core_blocking_candidate_concept_node_difference(
        &mut self,
        diff_count: Cint64,
    ) -> &mut Self {
        self.last_core_block_cand_node_diff = diff_count;
        self
    }

    /// Port of `getLastAddedCoreConceptDescriptor`.
    pub fn get_last_added_core_concept_descriptor(&self) -> CoreConceptDescriptorId {
        self.last_added_core_con_des
    }
    /// Port of `setLastAddedCoreConceptDescriptor`.
    pub fn set_last_added_core_concept_descriptor(
        &mut self,
        last_core_con_des: CoreConceptDescriptorId,
    ) -> &mut Self {
        self.last_added_core_con_des = last_core_con_des;
        self
    }
}

// ===========================================================================
// CBlockingAlternativeData  (+ the signature-blocking-candidate subclass)
// ===========================================================================

/// Port of `CBlockingAlternativeData::BLOCKINGALTERNATIVEDATA`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum BlockingAlternativeDataType {
    /// `BADSIGNATUREBLOCKINGCANDIDATE`.
    SignatureBlockingCandidate,
}

/// Port of `CBlockingAlternativeData` (the abstract base with the pure-virtual
/// `getBlockingAlternativeDataType()`).
///
/// KONCLUDE-PORT-NOTE[overload]: the C++ virtual hierarchy becomes a Rust trait;
/// the single concrete subclass below implements it.
pub trait BlockingAlternativeData {
    /// Port of `getBlockingAlternativeDataType` (pure virtual).
    fn get_blocking_alternative_data_type(&self) -> BlockingAlternativeDataType;
}

/// Port of `CBlockingAlternativeSignatureBlockingCandidateData`
/// (`: public CBlockingAlternativeData`).
#[derive(Clone)]
pub struct BlockingAlternativeSignatureBlockingCandidateData {
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode* mBlockIndiCandi` → `NodeId`.
    pub block_indi_candi: NodeId,           // mBlockIndiCandi
    pub violated_res_count: Cint64,         // mViolatedResCount
    pub violated_non_det_res_count: Cint64, // mViolatedNonDetResCount
    pub diff_concept_count: Cint64,         // mDiffConceptCount
}

impl Default for BlockingAlternativeSignatureBlockingCandidateData {
    /// Port of the `CBlockingAlternativeSignatureBlockingCandidateData()` ctor
    /// (empty body; the fields are set by `initSignatureBlockingCandidateData`).
    fn default() -> Self {
        BlockingAlternativeSignatureBlockingCandidateData {
            block_indi_candi: NodeId::NONE,
            violated_res_count: 0,
            violated_non_det_res_count: 0,
            diff_concept_count: 0,
        }
    }
}

impl BlockingAlternativeSignatureBlockingCandidateData {
    /// Port of the ctor.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initSignatureBlockingCandidateData`.
    pub fn init_signature_blocking_candidate_data(
        &mut self,
        block_indi_cand: NodeId,
        violated_res_count: Cint64,
        violated_non_det_res_count: Cint64,
        diff_concept_count: Cint64,
    ) -> &mut Self {
        self.block_indi_candi = block_indi_cand;
        self.violated_res_count = violated_res_count;
        self.violated_non_det_res_count = violated_non_det_res_count;
        self.diff_concept_count = diff_concept_count;
        self
    }

    /// Port of `getSignatureBlockingCandidateNode`.
    pub fn get_signature_blocking_candidate_node(&self) -> NodeId {
        self.block_indi_candi
    }
    /// Port of `setSignatureBlockingCandidateNode`.
    pub fn set_signature_blocking_candidate_node(&mut self, block_indi_can: NodeId) -> &mut Self {
        self.block_indi_candi = block_indi_can;
        self
    }

    /// Port of `getConceptDifferenceCount`.
    pub fn get_concept_difference_count(&self) -> Cint64 {
        self.diff_concept_count
    }
    /// Port of `getViolatedRestrictionCount`.
    pub fn get_violated_restriction_count(&self) -> Cint64 {
        self.violated_res_count
    }
    /// Port of `getViolatedNonDeterministicRestrictionCount`.
    pub fn get_violated_non_deterministic_restriction_count(&self) -> Cint64 {
        self.violated_non_det_res_count
    }

    /// Port of `setConceptDifferenceCount`.
    pub fn set_concept_difference_count(&mut self, count: Cint64) -> &mut Self {
        self.diff_concept_count = count;
        self
    }
    /// Port of `setViolatedRestrictionCount`.
    pub fn set_violated_restriction_count(&mut self, count: Cint64) -> &mut Self {
        self.violated_res_count = count;
        self
    }
    /// Port of `setViolatedNonDeterministicRestrictionCount`.
    pub fn set_violated_non_deterministic_restriction_count(&mut self, count: Cint64) -> &mut Self {
        self.violated_non_det_res_count = count;
        self
    }
}

impl BlockingAlternativeData for BlockingAlternativeSignatureBlockingCandidateData {
    /// Port of `getBlockingAlternativeDataType` (`return BADSIGNATUREBLOCKINGCANDIDATE;`).
    fn get_blocking_alternative_data_type(&self) -> BlockingAlternativeDataType {
        BlockingAlternativeDataType::SignatureBlockingCandidate
    }
}

// ===========================================================================
// CIndividualNodeIncrementalExpansionData
// ===========================================================================

/// Port of `CIndividualNodeIncrementalExpansionData` — the per-node satellite that
/// records, for incremental (re-)classification, what changed on a node vs the
/// previous completion graph and which individuals still need expansion.
///
/// KONCLUDE-PORT-NOTE[ownership]: the two `CPROCESSLIST<…>*` use/loc pairs become
/// `Option<Vec<…>>` use/loc pairs. In C++ the `mUseX` pointer is shared (aliases
/// the parent's list or, after localisation, `mLocX`); `getXList(true)` copies the
/// shared list into a freshly-allocated `mLocX` and repoints `mUseX = mLocX`
/// (copy-on-write). The port keeps `loc` as the locally-owned copy and treats it
/// as authoritative once present; reads fall back to the shared `use` snapshot
/// before localisation (see `use_inc_list` / `use_neigh_list` helpers). The share
/// is a clone (`[memory-pool]`: the zero-copy pointer share is left for later).
#[derive(Clone)]
pub struct IndividualNodeIncrementalExpansionData {
    // KONCLUDE-PORT-NOTE[ownership]: ambient `CProcessContext* mProcessContext` (opaque).
    pub process_context: Cint64, // mProcessContext

    pub expansion_priority: f64, // mExpansionPriority

    // mUseIncrementalExpansionList / mLocIncrementalExpansionList (CIndividual*).
    use_incremental_expansion_list: Option<Vec<IndividualId>>,
    loc_incremental_expansion_list: Option<Vec<IndividualId>>,
    pub incremetnal_expansion_list_initialized: bool, // mIncremetnalExpansionListInitialized (sic, C++ typo)

    // mUseNeighbourPropagatedDirectlyChangedList / mLoc… (CIndividualProcessNode*).
    use_neighbour_propagated_directly_changed_list: Option<Vec<NodeId>>,
    loc_neighbour_propagated_directly_changed_list: Option<Vec<NodeId>>,

    pub directly_changed: bool, // mDirectlyChanged
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode*` → `NodeId`.
    pub directly_changed_neighbour_conn_node: NodeId, // mDirectlyChangedNeighbourConnNode

    pub prev_comp_graph_corr_indi_node: NodeId, // mPrevCompGraphCorrIndiNode
    pub prev_comp_graph_corr_indi_node_loaded: bool, // mPrevCompGraphCorrIndiNodeLoaded

    pub completion_graph_compatible: bool, // mCompletionGraphCompatible
    pub last_compatible_checked_con_des: ConDescId, // mLastCompatibleCheckedConDes
    // KONCLUDE-PORT-NOTE[ownership]: `CLinkEdge* mLastCompatibleCheckedLink` → `EdgeId`.
    pub last_compatible_checked_link: EdgeId, // mLastCompatibleCheckedLink
}

impl Default for IndividualNodeIncrementalExpansionData {
    fn default() -> Self {
        IndividualNodeIncrementalExpansionData {
            process_context: INVALID,
            expansion_priority: 0.0,
            use_incremental_expansion_list: None,
            loc_incremental_expansion_list: None,
            incremetnal_expansion_list_initialized: false,
            use_neighbour_propagated_directly_changed_list: None,
            loc_neighbour_propagated_directly_changed_list: None,
            directly_changed: false,
            directly_changed_neighbour_conn_node: NodeId::NONE,
            prev_comp_graph_corr_indi_node: NodeId::NONE,
            prev_comp_graph_corr_indi_node_loaded: false,
            completion_graph_compatible: false,
            last_compatible_checked_con_des: ConDescId::NONE,
            last_compatible_checked_link: EdgeId::NONE,
        }
    }
}

impl IndividualNodeIncrementalExpansionData {
    /// Port of the `CIndividualNodeIncrementalExpansionData(CProcessContext*)` ctor.
    pub fn new(process_context: Cint64) -> Self {
        IndividualNodeIncrementalExpansionData {
            process_context,
            ..Default::default()
        }
    }

    /// Port of `initIncrementalExpansionData`.
    /// KONCLUDE-PORT-NOTE[ownership]: the `mUseX = prev->mUseX; mLocX = nullptr`
    /// pointer-share becomes a clone of the parent's authoritative list snapshot.
    pub fn init_incremental_expansion_data(
        &mut self,
        prev_data: Option<&IndividualNodeIncrementalExpansionData>,
    ) -> &mut Self {
        if let Some(prev) = prev_data {
            self.directly_changed = prev.directly_changed;
            self.directly_changed_neighbour_conn_node = prev.directly_changed_neighbour_conn_node;
            self.completion_graph_compatible = prev.completion_graph_compatible;
            self.last_compatible_checked_con_des = prev.last_compatible_checked_con_des;
            self.last_compatible_checked_link = prev.last_compatible_checked_link;
            self.prev_comp_graph_corr_indi_node = prev.prev_comp_graph_corr_indi_node;
            self.prev_comp_graph_corr_indi_node_loaded = prev.prev_comp_graph_corr_indi_node_loaded;
            // mUseNeighbour… = prev->mUseNeighbour… (shared); mLocNeighbour… = nullptr.
            self.use_neighbour_propagated_directly_changed_list =
                prev.authoritative_neigh_list().cloned();
            self.loc_neighbour_propagated_directly_changed_list = None;
            self.use_incremental_expansion_list = prev.authoritative_inc_list().cloned();
            self.loc_incremental_expansion_list = None;
            self.incremetnal_expansion_list_initialized =
                prev.incremetnal_expansion_list_initialized;
            self.expansion_priority = prev.expansion_priority;
        } else {
            self.directly_changed = false;
            self.directly_changed_neighbour_conn_node = NodeId::NONE;
            self.completion_graph_compatible = false;
            self.prev_comp_graph_corr_indi_node_loaded = false;
            self.last_compatible_checked_con_des = ConDescId::NONE;
            self.last_compatible_checked_link = EdgeId::NONE;
            self.prev_comp_graph_corr_indi_node = NodeId::NONE;
            self.loc_neighbour_propagated_directly_changed_list = None;
            self.use_neighbour_propagated_directly_changed_list = None;
            self.loc_incremental_expansion_list = None;
            self.use_incremental_expansion_list = None;
            self.incremetnal_expansion_list_initialized = false;
            self.expansion_priority = 0.0;
        }
        self
    }

    /// The authoritative neighbour-propagated list for reads (`mUseNeighbour…`):
    /// the localised copy if present, else the shared snapshot.
    fn authoritative_neigh_list(&self) -> Option<&Vec<NodeId>> {
        self.loc_neighbour_propagated_directly_changed_list
            .as_ref()
            .or(self.use_neighbour_propagated_directly_changed_list.as_ref())
    }

    /// The authoritative incremental-expansion list for reads (`mUseIncrementalExpansionList`).
    fn authoritative_inc_list(&self) -> Option<&Vec<IndividualId>> {
        self.loc_incremental_expansion_list
            .as_ref()
            .or(self.use_incremental_expansion_list.as_ref())
    }

    /// Port of `getDirectlyChangedNeighbourConnectionNode`.
    pub fn get_directly_changed_neighbour_connection_node(&self) -> NodeId {
        self.directly_changed_neighbour_conn_node
    }
    /// Port of `setDirectlyChangedNeighbourConnectionNode`.
    pub fn set_directly_changed_neighbour_connection_node(&mut self, node: NodeId) -> &mut Self {
        self.directly_changed_neighbour_conn_node = node;
        self
    }
    /// Port of `hasDirectlyChangedNeighbourConnection`.
    pub fn has_directly_changed_neighbour_connection(&self) -> bool {
        self.directly_changed_neighbour_conn_node.is_some()
    }
    /// Port of `isCompatibilityChanged`.
    pub fn is_compatibility_changed(&self) -> bool {
        self.directly_changed && self.has_directly_changed_neighbour_connection()
    }
    /// Port of `isDirectlyChanged`.
    pub fn is_directly_changed(&self) -> bool {
        self.directly_changed
    }
    /// Port of `setDirectlyChanged`.
    pub fn set_directly_changed(&mut self, directly_changed: bool) -> &mut Self {
        self.directly_changed = directly_changed;
        self
    }

    /// Port of `isPreviousCompletionGraphCompatible`.
    pub fn is_previous_completion_graph_compatible(&self) -> bool {
        self.completion_graph_compatible
    }
    /// Port of `setPreviousCompletionGraphCompatible`.
    pub fn set_previous_completion_graph_compatible(&mut self, compatible: bool) -> &mut Self {
        self.completion_graph_compatible = compatible;
        self
    }

    /// Port of `getLastCompatibleCheckedConceptDescriptor`.
    pub fn get_last_compatible_checked_concept_descriptor(&self) -> ConDescId {
        self.last_compatible_checked_con_des
    }
    /// Port of `getLastCompatibleCheckedLink`.
    pub fn get_last_compatible_checked_link(&self) -> EdgeId {
        self.last_compatible_checked_link
    }
    /// Port of `setLastCompatibleCheckedConceptDescriptor`.
    pub fn set_last_compatible_checked_concept_descriptor(
        &mut self,
        con_des: ConDescId,
    ) -> &mut Self {
        self.last_compatible_checked_con_des = con_des;
        self
    }
    /// Port of `setLastCompatibleCheckedLink`.
    pub fn set_last_compatible_checked_link(&mut self, link: EdgeId) -> &mut Self {
        self.last_compatible_checked_link = link;
        self
    }

    /// Port of `getPreviousCompletionGraphCorrespondenceIndividualNode`.
    pub fn get_previous_completion_graph_correspondence_individual_node(&self) -> NodeId {
        self.prev_comp_graph_corr_indi_node
    }
    /// Port of `setPreviousCompletionGraphCorrespondenceIndividualNode`.
    pub fn set_previous_completion_graph_correspondence_individual_node(
        &mut self,
        node: NodeId,
    ) -> &mut Self {
        self.prev_comp_graph_corr_indi_node = node;
        self
    }
    /// Port of `isPreviousCompletionGraphCorrespondenceIndividualNodeLoaded`.
    pub fn is_previous_completion_graph_correspondence_individual_node_loaded(&self) -> bool {
        self.prev_comp_graph_corr_indi_node_loaded
    }
    /// Port of `setPreviousCompletionGraphCorrespondenceIndividualNodeLoaded`.
    pub fn set_previous_completion_graph_correspondence_individual_node_loaded(
        &mut self,
        loaded: bool,
    ) -> &mut Self {
        self.prev_comp_graph_corr_indi_node_loaded = loaded;
        self
    }

    /// Port of `getNeighbourPropagatedDirectlyChangedList(bool create)`.
    /// KONCLUDE-PORT-NOTE[memory-pool]: `*mLocX = *mUseX` (copy the shared list into
    /// the fresh local) becomes a clone; `mUseX = mLocX` (repoint) is modelled by
    /// `loc` becoming authoritative (see `authoritative_neigh_list`).
    pub fn get_neighbour_propagated_directly_changed_list(
        &mut self,
        create: bool,
    ) -> Option<&mut Vec<NodeId>> {
        if self
            .loc_neighbour_propagated_directly_changed_list
            .is_none()
            && create
        {
            let mut loc = Vec::new();
            if let Some(u) = &self.use_neighbour_propagated_directly_changed_list {
                loc = u.clone();
            }
            self.loc_neighbour_propagated_directly_changed_list = Some(loc);
        }
        if self
            .loc_neighbour_propagated_directly_changed_list
            .is_some()
        {
            self.loc_neighbour_propagated_directly_changed_list.as_mut()
        } else {
            self.use_neighbour_propagated_directly_changed_list.as_mut()
        }
    }

    /// Port of `addNeighbourPropagatedDirectlyChanged`.
    pub fn add_neighbour_propagated_directly_changed(&mut self, indi_node: NodeId) -> &mut Self {
        self.get_neighbour_propagated_directly_changed_list(true)
            .unwrap()
            .push(indi_node);
        self
    }

    /// Port of `clearNeighbourPropagatedDirectlyChangedList`.
    pub fn clear_neighbour_propagated_directly_changed_list(&mut self) -> &mut Self {
        if self
            .authoritative_neigh_list()
            .map_or(false, |l| !l.is_empty())
        {
            self.get_neighbour_propagated_directly_changed_list(true)
                .unwrap()
                .clear();
        }
        self
    }

    /// Port of `hasNeighbourPropagatedDirectlyChanged`.
    pub fn has_neighbour_propagated_directly_changed(&self) -> bool {
        self.authoritative_neigh_list()
            .map_or(false, |l| !l.is_empty())
    }

    /// Snapshot equivalent of iterating `getNeighbourPropagatedDirectlyChangedList(false)`.
    pub fn neighbour_propagated_directly_changed_snapshot(&self) -> Vec<NodeId> {
        self.authoritative_neigh_list().cloned().unwrap_or_default()
    }

    /// Port of `getIncrementalExpansionList(bool create)`.
    pub fn get_incremental_expansion_list(
        &mut self,
        create: bool,
    ) -> Option<&mut Vec<IndividualId>> {
        if self.loc_incremental_expansion_list.is_none() && create {
            let mut loc = Vec::new();
            if let Some(u) = &self.use_incremental_expansion_list {
                loc = u.clone();
            }
            self.loc_incremental_expansion_list = Some(loc);
        }
        if self.loc_incremental_expansion_list.is_some() {
            self.loc_incremental_expansion_list.as_mut()
        } else {
            self.use_incremental_expansion_list.as_mut()
        }
    }

    /// Port of `isIncremetnalExpansionListInitialized` (C++ spelling kept).
    pub fn is_incremetnal_expansion_list_initialized(&self) -> bool {
        self.incremetnal_expansion_list_initialized
    }
    /// Port of `setIncremetnalExpansionListInitialized`.
    pub fn set_incremetnal_expansion_list_initialized(&mut self, initialized: bool) -> &mut Self {
        self.incremetnal_expansion_list_initialized = initialized;
        self
    }

    /// Port of `requiresFurtherIncrementalExpansion`.
    pub fn requires_further_incremental_expansion(&self) -> bool {
        self.authoritative_inc_list()
            .map_or(false, |l| !l.is_empty())
    }

    /// Port of `getExpansionPriority`.
    pub fn get_expansion_priority(&self) -> f64 {
        self.expansion_priority
    }
    /// Port of `setExpansionPriority`.
    pub fn set_expansion_priority(&mut self, priority: f64) -> &mut Self {
        self.expansion_priority = priority;
        self
    }
    /// Port of `setExpansionID` (`mExpansionPriority = (cint64)id;`).
    pub fn set_expansion_id(&mut self, id: Cint64) -> &mut Self {
        self.expansion_priority = id as f64;
        self
    }
    /// Port of `getNextIncrementalExpansionPriority` (`mExpansionPriority + 1.0`).
    pub fn get_next_incremental_expansion_priority(&self) -> f64 {
        self.expansion_priority + 1.0
    }

    /// Port of `takeNextIncrementalExpansionIndividual` (`takeFirst` — head-front
    /// `remove(0)`, PORT.md §6).
    pub fn take_next_incremental_expansion_individual(&mut self) -> IndividualId {
        if let Some(list) = self
            .loc_incremental_expansion_list
            .as_mut()
            .filter(|l| !l.is_empty())
        {
            return list.remove(0);
        }
        if let Some(list) = self
            .use_incremental_expansion_list
            .as_mut()
            .filter(|l| !l.is_empty())
        {
            return list.remove(0);
        }
        IndividualId::NONE
    }

    /// Port of `getNextIncrementalExpansionIndividual` (`first`).
    pub fn get_next_incremental_expansion_individual(&self) -> IndividualId {
        if let Some(list) = self.authoritative_inc_list() {
            if !list.is_empty() {
                return list[0];
            }
        }
        IndividualId::NONE
    }
}

// ===========================================================================
// CReapplyConceptDescriptor
// (`CReapplyConceptDescriptor.{h,cpp}`)
// ===========================================================================

/// Port of `CReapplyConceptDescriptor`
/// (`: public CLinkerBase<CConceptDescriptor*, CReapplyConceptDescriptor>`).
///
/// KONCLUDE-PORT-NOTE[ownership]: the intrusive linker becomes `next:
/// ReapplyConceptDescriptorId`; `CProcessingRestrictionSpecification*` remains an
/// opaque process-local handle until the restriction object family is fully wired.
#[derive(Clone)]
pub struct ReapplyConceptDescriptor {
    /// `CLinkerBase::mData` (`CConceptDescriptor*`).
    pub data: ConDescId,
    /// `CLinkerBase::mNext`.
    pub next: ReapplyConceptDescriptorId,
    /// `CReapplyConceptDescriptor::mTrackPoint`.
    pub track_point: TrackPointId,
    /// `CReapplyConceptDescriptor::mStatic`.
    pub static_descriptor: bool,
    /// `CReapplyConceptDescriptor::mProcessingRestriction` (opaque).
    pub processing_restriction: Cint64,
}

impl Default for ReapplyConceptDescriptor {
    fn default() -> Self {
        ReapplyConceptDescriptor {
            data: Id::NONE,
            next: Id::NONE,
            track_point: Id::NONE,
            static_descriptor: false,
            processing_restriction: INVALID,
        }
    }
}

impl ReapplyConceptDescriptor {
    /// Port of `CReapplyConceptDescriptor(CConceptDescriptor*, CDependencyTrackPoint*, bool)`.
    pub fn new(
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        is_static_des: bool,
    ) -> Self {
        ReapplyConceptDescriptor {
            data: concept_descriptor,
            next: Id::NONE,
            track_point: dep_track_point,
            static_descriptor: is_static_des,
            processing_restriction: INVALID,
        }
    }

    /// Port of `initReapllyDescriptor(conceptDescriptor, depTrackPoint, isStaticDes)`.
    pub fn init_reapply_descriptor(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        is_static_des: bool,
    ) -> &mut Self {
        self.data = concept_descriptor;
        self.track_point = dep_track_point;
        self.static_descriptor = is_static_des;
        self.processing_restriction = INVALID;
        self
    }

    /// Port of `initReapllyDescriptor(conceptDescriptor, depTrackPoint, procRest)`.
    pub fn init_reapply_descriptor_restricted(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        proc_rest: Cint64,
    ) -> &mut Self {
        self.data = concept_descriptor;
        self.track_point = dep_track_point;
        self.static_descriptor = false;
        self.processing_restriction = proc_rest;
        self
    }

    /// Port of `getNext`.
    pub fn get_next(&self) -> ReapplyConceptDescriptorId {
        self.next
    }

    /// Port of `getConceptDescriptor`.
    pub fn get_concept_descriptor(&self) -> ConDescId {
        self.data
    }

    /// Port of `getDependencyTrackPoint`.
    pub fn get_dependency_track_point(&self) -> TrackPointId {
        self.track_point
    }

    /// Port of `isStaticDescriptor`.
    pub fn is_static_descriptor(&self) -> bool {
        self.static_descriptor
    }

    /// Port of `getReapplyProcessingRestriction`.
    pub fn get_reapply_processing_restriction(&self) -> Cint64 {
        self.processing_restriction
    }

    /// Port of `hasConceptDescriptor`.
    pub fn has_concept_descriptor(&self, concept_descriptor: ConDescId) -> bool {
        self.data == concept_descriptor
    }

    /// Port of `CLinkerBase::append`.
    pub fn append(
        ctx: &mut ProcessContext,
        this: ReapplyConceptDescriptorId,
        appending_list: ReapplyConceptDescriptorId,
    ) -> ReapplyConceptDescriptorId {
        if this.is_none() {
            return appending_list;
        }
        let mut last = this;
        while ctx.reapply_con_desc(last).next.is_some() {
            last = ctx.reapply_con_desc(last).next;
        }
        ctx.reapply_con_desc_mut(last).next = appending_list;
        this
    }
}

// ===========================================================================
// CCondensedReapplyConceptDescriptor  (+ CCondensedReapplyQueueIterator)
// (`CCondensedReapplyConceptDescriptor.{h,cpp}` +
//  `CCondensedReapplyQueueIterator.{h,cpp}`)
// ===========================================================================

/// Port of `CCondensedReapplyConceptDescriptor`
/// (`: public CReapplyConceptDescriptor : public CLinkerBase<CConceptDescriptor*, …>`).
///
/// The intrusive reapply-queue descriptor the condensed iterator walks. The
/// `CLinkerBase` `data`/`next` become a `ConDescId` payload + a head-front linker
/// id (PORT.md §6); the `CReapplyConceptDescriptor` `mTrackPoint`/`mStatic`/
/// `mProcessingRestriction` and the condensed `mPositive`/`mExtended` are inlined.
///
/// KONCLUDE-PORT-NOTE[ownership]: `CProcessingRestrictionSpecification* mProcessingRestriction`
/// stays opaque `Cint64` (`INVALID` == `nullptr`) — the iterator never reads it.
#[derive(Clone)]
pub struct CondensedReapplyConceptDescriptor {
    /// `CLinkerBase::mData` (`CConceptDescriptor*`).
    pub data: ConDescId,
    /// `CLinkerBase::mNext` (next `CCondensedReapplyConceptDescriptor*`).
    pub next: CondensedReapplyConceptDescriptorId,
    /// `CReapplyConceptDescriptor::mTrackPoint`.
    pub track_point: TrackPointId,
    /// `CReapplyConceptDescriptor::mStatic`.
    pub static_descriptor: bool,
    /// `CReapplyConceptDescriptor::mProcessingRestriction` (opaque).
    pub processing_restriction: Cint64,
    /// `CCondensedReapplyConceptDescriptor::mPositive`.
    pub positive: bool,
    /// `CCondensedReapplyConceptDescriptor::mExtended`.
    pub extended: bool,
}

impl Default for CondensedReapplyConceptDescriptor {
    fn default() -> Self {
        // Port of `CCondensedReapplyConceptDescriptor::CCondensedReapplyConceptDescriptor()`
        // (`mExtended = false; mPositive = true;`) over the `CLinkerBase` null defaults.
        CondensedReapplyConceptDescriptor {
            data: Id::NONE,
            next: Id::NONE,
            track_point: Id::NONE,
            static_descriptor: false,
            processing_restriction: INVALID,
            positive: true,
            extended: false,
        }
    }
}

impl CondensedReapplyConceptDescriptor {
    /// Port of `CCondensedReapplyConceptDescriptor(CConceptDescriptor*, CDependencyTrackPoint*, bool isPositiveDes)`.
    pub fn new(
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        is_positive_des: bool,
    ) -> Self {
        CondensedReapplyConceptDescriptor {
            data: concept_descriptor,
            next: Id::NONE,
            track_point: dep_track_point,
            static_descriptor: false,
            processing_restriction: INVALID,
            positive: is_positive_des,
            extended: false,
        }
    }

    /// Port of `getNext`.
    pub fn get_next(&self) -> CondensedReapplyConceptDescriptorId {
        self.next
    }

    /// Port of `CReapplyConceptDescriptor::getConceptDescriptor` (`getData`).
    pub fn get_concept_descriptor(&self) -> ConDescId {
        self.data
    }

    /// Port of `CReapplyConceptDescriptor::getDependencyTrackPoint`.
    pub fn get_dependency_track_point(&self) -> TrackPointId {
        self.track_point
    }

    /// Port of `CReapplyConceptDescriptor::isStaticDescriptor`.
    pub fn is_static_descriptor(&self) -> bool {
        self.static_descriptor
    }

    /// Port of `CReapplyConceptDescriptor::getReapplyProcessingRestriction`.
    pub fn get_reapply_processing_restriction(&self) -> Cint64 {
        self.processing_restriction
    }

    /// Port of `isPositiveDescriptor` (`return mPositive`).
    pub fn is_positive_descriptor(&self) -> bool {
        self.positive
    }

    /// Port of `isExtended` (`return mExtended`).
    pub fn is_extended(&self) -> bool {
        self.extended
    }

    /// Port of `initReapllyDescriptor(conceptDescriptor, depTrackPoint, isPositiveDes)`.
    pub fn init_reapply_descriptor(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        is_positive_des: bool,
    ) -> &mut Self {
        self.data = concept_descriptor;
        self.track_point = dep_track_point;
        self.static_descriptor = false;
        self.positive = is_positive_des;
        self
    }

    /// Port of `initReapllyDescriptor(conceptDescriptor, depTrackPoint, isPositiveDes, procRest)`.
    pub fn init_reapply_descriptor_restricted(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        is_positive_des: bool,
        proc_rest: Cint64,
    ) -> &mut Self {
        self.data = concept_descriptor;
        self.track_point = dep_track_point;
        self.static_descriptor = false;
        self.processing_restriction = proc_rest;
        self.positive = is_positive_des;
        self
    }
}

/// Port of `CCondensedReapplyQueueIterator`.
///
/// Walks a `CCondensedReapplyConceptDescriptor*` linker chain, yielding only the
/// descriptors whose polarity is *not* filtered out by `mPosDes`/`mNegDes`.
///
/// KONCLUDE-PORT-NOTE[ownership]: the C++ holds a raw
/// `CCondensedReapplyConceptDescriptor*` head; here it is a
/// `CondensedReapplyConceptDescriptorId` into `ProcessContext::cond_reapply_con_descs`,
/// and every `getNext()` / `isPositiveDescriptor()` deref threads `&ProcessContext`.
/// This is a distinct, real port from the W2 by-value placeholders in `process::pn3`
/// / `process::ls1` (which the completion units still reference); the un-defer wave
/// reconciles those call sites onto this type.
#[derive(Clone, Copy)]
pub struct CondensedReapplyQueueIterator {
    /// `CCondensedReapplyConceptDescriptor* mDynamicPosNegReapplyDesLinker`.
    dynamic_pos_neg_reapply_des_linker: CondensedReapplyConceptDescriptorId,
    /// `bool mPosDes`.
    pos_des: bool,
    /// `bool mNegDes`.
    neg_des: bool,
}

impl Default for CondensedReapplyQueueIterator {
    /// Port of `CCondensedReapplyQueueIterator::CCondensedReapplyQueueIterator()`.
    fn default() -> Self {
        CondensedReapplyQueueIterator {
            dynamic_pos_neg_reapply_des_linker: Id::NONE,
            pos_des: true,
            neg_des: true,
        }
    }
}

impl CondensedReapplyQueueIterator {
    /// Port of `CCondensedReapplyQueueIterator()` (the empty iterator).
    pub fn new() -> Self {
        Self::default()
    }

    // KONCLUDE-PORT-NOTE[ownership]: the C++ ctors run the polarity-skip while-loop
    // in their initializer body; in the port the loop is factored into
    // `skip_filtered` (threading `&ProcessContext`) and called from each ctor — the
    // observable advance is identical.
    fn skip_filtered(&mut self, ctx: &ProcessContext) {
        while self.dynamic_pos_neg_reapply_des_linker.is_some() {
            let positive = ctx
                .cond_reapply_con_desc(self.dynamic_pos_neg_reapply_des_linker)
                .is_positive_descriptor();
            if (positive && !self.pos_des) || (!positive && !self.neg_des) {
                self.dynamic_pos_neg_reapply_des_linker = ctx
                    .cond_reapply_con_desc(self.dynamic_pos_neg_reapply_des_linker)
                    .get_next();
            } else {
                break;
            }
        }
    }

    /// Port of `CCondensedReapplyQueueIterator(dynamicReapplyDesLinker, positiveDescriptors, negativeDescriptors)`.
    pub fn new_pos_neg(
        ctx: &ProcessContext,
        dynamic_reapply_des_linker: CondensedReapplyConceptDescriptorId,
        positive_descriptors: bool,
        negative_descriptors: bool,
    ) -> Self {
        let mut it = CondensedReapplyQueueIterator {
            dynamic_pos_neg_reapply_des_linker: dynamic_reapply_des_linker,
            pos_des: positive_descriptors,
            neg_des: negative_descriptors,
        };
        it.skip_filtered(ctx);
        it
    }

    /// Port of `CCondensedReapplyQueueIterator(dynamicReapplyDesLinker, onlyPositiveDescriptors)`.
    pub fn new_only_positive(
        ctx: &ProcessContext,
        dynamic_reapply_des_linker: CondensedReapplyConceptDescriptorId,
        only_positive_descriptors: bool,
    ) -> Self {
        let mut it = CondensedReapplyQueueIterator {
            dynamic_pos_neg_reapply_des_linker: dynamic_reapply_des_linker,
            pos_des: only_positive_descriptors,
            neg_des: !only_positive_descriptors,
        };
        it.skip_filtered(ctx);
        it
    }

    /// Port of `next(bool moveNext)`.
    pub fn next(
        &mut self,
        ctx: &ProcessContext,
        move_next: bool,
    ) -> CondensedReapplyConceptDescriptorId {
        let mut next_des = CondensedReapplyConceptDescriptorId::NONE;
        if self.dynamic_pos_neg_reapply_des_linker.is_some() {
            next_des = self.dynamic_pos_neg_reapply_des_linker;
            if move_next {
                self.dynamic_pos_neg_reapply_des_linker = ctx
                    .cond_reapply_con_desc(self.dynamic_pos_neg_reapply_des_linker)
                    .get_next();
                self.skip_filtered(ctx);
            }
        }
        next_des
    }

    /// Port of `hasNext`.
    pub fn has_next(&self) -> bool {
        self.dynamic_pos_neg_reapply_des_linker.is_some()
    }
}

// ===========================================================================
// W2.7-ARENA-ADDITIONS
// ===========================================================================
//
// `process::context::ProcessContext` needs these new per-test arena pools added
// (each via the existing `arena_accessors!` macro — same `get / get_mut / alloc`
// trio convention as the W3.5 arenas):
//
//   sig_block_cand_hashes : Arena<SignatureBlockingCandidateHash>
//       → trio  sig_block_cand_hash / sig_block_cand_hash_mut / alloc_sig_block_cand_hash
//       (indexed by `SigBlockCandHashId`; the databox's per-test signature
//        blocking-candidate hash — reconciles the `stubs::SignatureBlockingCandidateHash`
//        marker held inline on `CProcessingDataBox`).
//
//   blocking_test_datas : Arena<IndividualNodeBlockingTestData>
//       → trio  blocking_test_data / blocking_test_data_mut / alloc_blocking_test_data
//       (indexed by `BlockingTestDataId`; RECONCILES the W2 stub
//        `IndividualNodeBlockData => IndiBlockDataId` — `node.rs`'s
//        `indi_block` / `prev_indi_block` fields should be retyped from
//        `IndiBlockDataId` to `BlockingTestDataId` when this lands).
//
//   blocking_alt_datas : Arena<BlockingAlternativeSignatureBlockingCandidateData>
//       → trio  blocking_alt_data / blocking_alt_data_mut / alloc_blocking_alt_data
//       (indexed by `BlockingAltDataId`; the only concrete `CBlockingAlternativeData`
//        subclass — if more land, promote to an enum-tagged arena).
//
//   inc_exp_datas : Arena<IndividualNodeIncrementalExpansionData>
//       → trio  inc_exp_data / inc_exp_data_mut / alloc_inc_exp_data
//       (indexed by `IncrementalExpansionDataId`; RECONCILES the W2 stub
//        `IndividualNodeIncrementalExpansionData => IncExpDataId` — `node.rs`'s
//        `use_inc_exp_data` / `loc_inc_exp_data` fields point here).
//
// The iterators (`ReapplyConceptLabelSetIterator`, `SignatureBlockingCandidateIterator`,
// `SignatureIterator`) are NOT arena-allocated: like their C++ originals they are
// constructed by value and returned from getters (`getConceptLabelSetIterator` in
// LS-1, `getBlockingCandidatesIterator` / `getSignatureIterator` above), so they
// need no `ProcessContext` field — only `&ProcessContext` threaded into the
// methods that deref the descriptor/node arenas.
//
// W2.7-DEFER[api] (cross-subtree wiring left for when the owners un-defer):
//   * `CReapplyConceptLabelSet::getConceptLabelSetIterator` (LS-1) builds a
//     `ReapplyConceptLabelSetIterator` from its two COW maps — it must snapshot
//     each map into a key-SORTED `Vec<LabelSetMapEntry>` (the merge logic assumes
//     ordered keys; the W2 satellites store them in an unordered `HashMap`, so the
//     builder sorts on the way out).
//   * `CConceptDescriptor::getConceptTag` (descriptor W2 batch) — DONE (W3b.1):
//     `get_data_tag(ctx, onto)`'s linker branch now calls
//     `ctx.con_desc(it).get_concept_tag(onto)`.
//   * `CNodeSwitchTag` tag protocol (init/update/up-to-date over `CProcessTagger`)
//     on `IndividualNodeBlockingTestData` — only the marking word is modelled.
//   * `SignatureBlockingCandidateHash::mem_man` — the pooled
//     `getUsedMemoryAllocationManager()` handle stays opaque (the arenas are the pool).
