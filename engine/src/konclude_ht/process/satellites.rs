//! `process::satellites` (port unit SD-4) — the three per-node satellite core
//! classes of the completion graph:
//!
//! * `CReapplyConceptLabelSet` — a node's concept label set + reapply map;
//! * `CReapplyRoleSuccessorHash` — a node's role→successor-edge index;
//! * `CBranchingMergingProcessingRestrictionSpecification` — the ≤n merge /
//!   branching restriction record.
//!
//! (`Source/Reasoner/Kernel/Process/CReapplyConceptLabelSet.{h,cpp}`,
//! `CReapplyRoleSuccessorHash.{h,cpp}` + `CReapplyRoleSuccessorData.h`,
//! `CBranchingMergingProcessingRestrictionSpecification.{h,cpp}`.)
//!
//! CRITICAL — the **copy-on-write size thresholds are behaviour-load-bearing**
//! and must survive into the byte-exact method port (deferred to units LS-1 /
//! RS-1 / BM-1). They are NOT simplified away here: the paired/triple fields the
//! threshold logic reads and writes are all kept explicit:
//!   * label set: `concept_des_dep_map` + `additional_concept_des_dep_map`
//!     (init COW thresholds **`size <= 50`** / **`size*10 < additional.size`**);
//!   * role-succ per-role value: `link_set` + `prev_link_set` + `link_linker` +
//!     `located_link_set` (localate thresholds **`size <= 100`** / **`*10`** and
//!     the **`link_count >= 5`** locate-on-read trigger);
//!   * merge spec: `distinct_merged_nodes_set` + `last_distinct_merged_nodes_set`.

#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::node_resolution::ProcessTagger;
use super::reapply_sat::ReapplyConceptDescriptorId;
use super::stubs::CandidateLinkerId;
use super::{ClashDescId, ConDescId, DependencyId, EdgeId, RestrictionSpecId, TrackPointId};

/// `CCoreConceptDescriptor*` → `CoreConceptDescriptorId`.
pub type CoreConceptDescriptorId = Id<CoreConceptDescriptor>;

/// Port of `CCoreConceptDescriptor`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CoreConceptDescriptor {
    /// `CLinkerBase::mData`.
    pub concept_descriptor: ConDescId,
    /// `CLinkerBase::mNext`.
    pub next: CoreConceptDescriptorId,
}

impl Default for CoreConceptDescriptor {
    fn default() -> Self {
        Self {
            concept_descriptor: ConDescId::NONE,
            next: CoreConceptDescriptorId::NONE,
        }
    }
}

impl CoreConceptDescriptor {
    /// Port of `CCoreConceptDescriptor()`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initCoreConceptDescriptor`.
    pub fn init_core_concept_descriptor(&mut self, con_des: ConDescId) -> &mut Self {
        self.concept_descriptor = con_des;
        self.next = CoreConceptDescriptorId::NONE;
        self
    }

    /// Port of `getConceptDesciptor` (Konclude spelling).
    pub fn get_concept_desciptor(&self) -> ConDescId {
        self.concept_descriptor
    }

    /// Port of `CLinkerBase::getNext`.
    pub fn get_next(&self) -> CoreConceptDescriptorId {
        self.next
    }

    /// Port-facing equivalent of `coreConDes->append(next)`.
    pub fn append(&mut self, next: CoreConceptDescriptorId) -> &mut Self {
        self.next = next;
        self
    }
}

// ===========================================================================
// Shared not-yet-ported placeholder types (resolved in LS-1 / RS-1 / BM-1 + SD-1)
// ===========================================================================
// KONCLUDE-PORT-NOTE[api]: descriptor/queue/flag value-classes and the candidate
// linker that these three classes embed are separate `Process/` units not yet
// ported. They are stubbed here so the field types stay exact; the real structs
// land in their own units and these placeholders reconcile then.

// u15 reconcile: `CCondensedReapplyQueue` is now the real ported struct in
// `process::condensed_reapply` (dynamic reapply-queue head + descriptor linker).
// Re-exported here so every `use super::satellites::{… CondensedReapplyQueue}`
// call site (this file's `ConceptDescriptorDependencyReapplyData`,
// `reapply_sat::LabelSetMapEntry`, `ls1`) keeps resolving onto the real type.
pub use super::condensed_reapply::CondensedReapplyQueue;

/// Port of `CReapplyQueue`.
///
/// KONCLUDE-PORT-NOTE[ownership]: `CReapplyConceptDescriptor*` heads become ids
/// into `ProcessContext::reapply_con_descs`. Konclude's optional queue-count
/// macro is disabled in the source header, so only the descriptor heads are kept.
#[derive(Copy, Clone)]
pub struct ReapplyQueue {
    /// `CReapplyConceptDescriptor* mStaticReapplyDesLinker`.
    pub static_reapply_des_linker: ReapplyConceptDescriptorId,
    /// `CReapplyConceptDescriptor* mDynamicReapplyDesLinker`.
    pub dynamic_reapply_des_linker: ReapplyConceptDescriptorId,
}

impl Default for ReapplyQueue {
    fn default() -> Self {
        ReapplyQueue {
            static_reapply_des_linker: ReapplyConceptDescriptorId::NONE,
            dynamic_reapply_des_linker: ReapplyConceptDescriptorId::NONE,
        }
    }
}

impl ReapplyQueue {
    /// Port of `CReapplyQueue::CReapplyQueue`.
    pub fn new() -> Self {
        Self::default()
    }
}

/// Port of `CConceptSetSignature` (held by value).
#[derive(Copy, Clone)]
pub struct ConceptSetSignature {
    pub value1: Cint64,
    pub value2: Cint64,
    pub value3: Cint64,
    pub signature_value: Cint64,
}

impl Default for ConceptSetSignature {
    fn default() -> Self {
        let mut sig = ConceptSetSignature {
            value1: 0,
            value2: 1,
            value3: 0,
            signature_value: 0,
        };
        sig.reset();
        sig
    }
}

impl ConceptSetSignature {
    /// Port of `CConceptSetSignature::reset`.
    pub fn reset(&mut self) -> &mut Self {
        self.signature_value = 0;
        self.value1 = 0;
        self.value2 = 1;
        self.value3 = 0;
        self
    }

    /// Port of `CConceptSetSignature::getSignatureValue`.
    pub fn get_signature_value(&self) -> Cint64 {
        self.signature_value
    }

    /// Port of `CConceptSetSignature::addConceptSignature(CConcept*, bool)`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: Konclude folds the raw `CConcept*` pointer
    /// into `mValue3`; the arena port uses the stable `ConceptId` raw value.
    pub fn add_concept_signature(
        &mut self,
        concept: ConceptId,
        concept_tag: Cint64,
        negation: bool,
    ) -> &mut Self {
        let con_sig = if negation {
            Cint64::MAX.wrapping_sub(concept_tag)
        } else {
            concept_tag
        };
        self.value1 = self.value1.wrapping_add(con_sig);
        self.value2 = self.value2.wrapping_mul(con_sig);
        self.value3 = self.value3.wrapping_add(concept.raw);
        self.signature_value = self.value1 ^ self.value2 ^ self.value3;
        self
    }

    /// Port of `CConceptSetSignature::isSignatureEquivalent`.
    pub fn is_signature_equivalent(&self, other: &ConceptSetSignature) -> bool {
        self.signature_value == other.signature_value
    }
}

/// Port of `CConceptSetStructure` (placeholder, held by value).
#[derive(Default, Clone)]
pub struct ConceptSetStructure;

impl ConceptSetStructure {
    /// Port of `hasBindingPropagationConcepts`.
    pub fn has_binding_propagation_concepts(&self) -> bool {
        false
    }

    /// Port of `hasDynamicCreatedConcepts`.
    pub fn has_dynamic_created_concepts(&self) -> bool {
        false
    }
}

/// Port of `CConceptSetFlags` (placeholder, held by value).
#[derive(Default, Clone)]
pub struct ConceptSetFlags;

/// Port of `CConceptLabelSetModificationTag` (placeholder base, `: CProcessTag`).
/// Embedded by composition; carries the process-tag marking word.
#[derive(Default, Clone)]
pub struct ConceptLabelSetModificationTag {
    // CProcessTag::mProcessTag
    pub process_tag: Cint64,
}

impl ConceptLabelSetModificationTag {
    /// Port of `getConceptLabelSetModificationTag`.
    pub fn get_concept_label_set_modification_tag(&self) -> Cint64 {
        self.process_tag
    }

    /// Port of `setConceptLabelSetModificationTag(cint64)`.
    pub fn set_concept_label_set_modification_tag(
        &mut self,
        concept_label_set_modification_tag: Cint64,
    ) -> &mut Self {
        self.process_tag = concept_label_set_modification_tag;
        self
    }

    /// Port of `initConceptLabelSetModificationTag(cint64)`.
    pub fn init_concept_label_set_modification_tag(
        &mut self,
        concept_label_set_modification_tag: Cint64,
    ) -> &mut Self {
        self.process_tag = concept_label_set_modification_tag;
        self
    }

    /// Port of `isConceptLabelSetModificationTagUpdated(cint64)`.
    pub fn is_concept_label_set_modification_tag_updated(
        &self,
        concept_label_set_modification_tag: Cint64,
    ) -> bool {
        concept_label_set_modification_tag > self.process_tag
    }

    /// Port of `isConceptLabelSetModificationTagUpToDate(cint64)`.
    pub fn is_concept_label_set_modification_tag_up_to_date(
        &self,
        concept_label_set_modification_tag: Cint64,
    ) -> bool {
        self.process_tag >= concept_label_set_modification_tag
    }

    /// Port of `updateConceptLabelSetModificationTag(cint64)`.
    pub fn update_concept_label_set_modification_tag(
        &mut self,
        concept_label_set_modification_tag: Cint64,
    ) -> bool {
        let updated = self.process_tag != concept_label_set_modification_tag;
        self.process_tag = concept_label_set_modification_tag;
        updated
    }

    /// Port of `setConceptLabelSetModificationTag(CProcessTagger*)`.
    pub fn set_concept_label_set_modification_tag_tagger(
        &mut self,
        process_tagger: &ProcessTagger,
    ) -> &mut Self {
        self.set_concept_label_set_modification_tag(
            process_tagger.get_current_concept_label_set_modification_tag(),
        )
    }

    /// Port of `initConceptLabelSetModificationTag(CProcessTagger*)`.
    pub fn init_concept_label_set_modification_tag_tagger(
        &mut self,
        process_tagger: &ProcessTagger,
    ) -> &mut Self {
        self.init_concept_label_set_modification_tag(
            process_tagger.get_current_concept_label_set_modification_tag(),
        )
    }

    /// Port of `isConceptLabelSetModificationTagUpdated(CProcessTagger*)`.
    pub fn is_concept_label_set_modification_tag_updated_tagger(
        &self,
        process_tagger: &ProcessTagger,
    ) -> bool {
        self.is_concept_label_set_modification_tag_updated(
            process_tagger.get_current_concept_label_set_modification_tag(),
        )
    }

    /// Port of `isConceptLabelSetModificationTagUpToDate(CProcessTagger*)`.
    pub fn is_concept_label_set_modification_tag_up_to_date_tagger(
        &self,
        process_tagger: &ProcessTagger,
    ) -> bool {
        self.is_concept_label_set_modification_tag_up_to_date(
            process_tagger.get_current_concept_label_set_modification_tag(),
        )
    }

    /// Port of `updateConceptLabelSetModificationTag(CProcessTagger*)`.
    pub fn update_concept_label_set_modification_tag_tagger(
        &mut self,
        process_tagger: &ProcessTagger,
    ) -> bool {
        self.update_concept_label_set_modification_tag(
            process_tagger.get_current_concept_label_set_modification_tag(),
        )
    }
}

/// Port of `CConceptDescriptorDependencyReapplyData`
/// (`CConceptDescriptorDependencyReapplyData.h`) — the per-concept value in the
/// label set's reapply maps.
#[derive(Clone)]
pub struct ConceptDescriptorDependencyReapplyData {
    // KONCLUDE-PORT-NOTE[ownership]: `CConceptDescriptor* mConceptDescriptor` → `ConDescId`.
    pub concept_descriptor: ConDescId,
    // `CCondensedReapplyQueue mPosNegReapplyQueue` (held by value).
    pub pos_neg_reapply_queue: CondensedReapplyQueue,
}

impl Default for ConceptDescriptorDependencyReapplyData {
    fn default() -> Self {
        ConceptDescriptorDependencyReapplyData {
            concept_descriptor: Id::NONE,
            pos_neg_reapply_queue: CondensedReapplyQueue::new(),
        }
    }
}

// KONCLUDE-PORT-NOTE[api]: `CBranchingMergingIndividualNodeCandidateLinker` (the
// intrusive candidate-node linker chain) is the marker `CandidateLinkerId`
// imported from `process::stubs` above.

// ===========================================================================
// CReapplyConceptLabelSet  (port unit LS-1 holds the method bodies)
// ===========================================================================

/// Port of `CReapplyConceptLabelSet` (`: public CConceptLabelSetModificationTag`,
/// virtual dtor → polymorphic base of the saturation twin).
///
/// KONCLUDE-PORT-NOTE[ownership]: pointer members become `Id`s, the
/// `CConceptDescriptor*` linker heads become `ConDescId`s, and the two
/// `CPROCESSMAP<cint64,…>` maps become `HashMap`s. The COW between them is the
/// load-bearing part — see the field notes below + unit LS-1.
#[derive(Clone)]
pub struct ReapplyConceptLabelSet {
    // --- base CConceptLabelSetModificationTag (composition) ------------------
    pub modification_tag: ConceptLabelSetModificationTag,

    // --- the COW map pair (behaviour-load-bearing) --------------------------
    /// `CPROCESSMAP<cint64,CConceptDescriptorDependencyReapplyData> mConceptDesDepMap`.
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ map is an implicitly-shared
    /// (copy-on-write) `CPROCESSMAP`; `initConceptLabelSet` value-assigns it from
    /// the parent label set (cheap share in C++) only while it stays small. The
    /// size threshold that decides share-vs-rebuild (**`size <= 50`**, or
    /// **`size*10 < additional.size`**) is reproduced in LS-1.
    pub concept_des_dep_map: HashMap<Cint64, ConceptDescriptorDependencyReapplyData>,
    /// `CPROCESSMAP<cint64,…>* mAdditionalConceptDesDepMap` — the COW partner.
    /// KONCLUDE-PORT-NOTE[ownership][unclear]: in C++ this raw pointer is null, or
    /// owns a freshly-allocated overflow map, or **aliases another label set's**
    /// `mConceptDesDepMap` / `mAdditionalConceptDesDepMap` (see `initConceptLabelSet`
    /// lines 72/84). The three states are modelled by `AdditionalDesDepMapRef`;
    /// the exact alias target + the byte-exact share logic land in LS-1.
    pub additional_concept_des_dep_map: AdditionalDesDepMapRef,

    // --- descriptor linker heads --------------------------------------------
    pub core_con_des_linker: CoreConceptDescriptorId, // CCoreConceptDescriptor* mCoreConDesLinker
    pub concept_des_linker: ConDescId,                // CConceptDescriptor* mConceptDesLinker
    pub prev_concept_des_linker: ConDescId,           // CConceptDescriptor* mPrevConceptDesLinker

    // --- value-typed signature / structure / flags (inline) -----------------
    pub concept_signature: ConceptSetSignature, // mConceptSignature
    pub concept_structure: ConceptSetStructure, // mConceptStructure
    pub concept_flags: ConceptSetFlags,         // mConceptFlags
    pub concept_count: Cint64,                  // mConceptCount

    // KONCLUDE-PORT-NOTE[ownership]: ambient `CProcessContext*` handle (opaque).
    pub process_context: Cint64, // mProcessContext
}

/// The three states of `mAdditionalConceptDesDepMap` (null / owned-overflow /
/// shared-from-another-label-set). Kept first-class so LS-1 can port the COW
/// share-vs-copy decision byte-exactly.
#[derive(Clone)]
pub enum AdditionalDesDepMapRef {
    /// `nullptr`.
    Null,
    /// A self-allocated overflow map (`allocateAndConstructAndParameterize`).
    Owned(HashMap<Cint64, ConceptDescriptorDependencyReapplyData>),
    // KONCLUDE-PORT-NOTE[ownership][unclear]: C++ aliases the `mConceptDesDepMap`
    // (or `mAdditionalConceptDesDepMap`) of another `ReapplyConceptLabelSet` by
    // raw pointer. No stable arena id exists for an inner map yet; LS-1 resolves
    // the alias target representation.
    Shared(LabelSetMapAlias),
}

/// Placeholder alias handle for a shared additional-map pointer (LS-1).
#[derive(Copy, Clone)]
pub struct LabelSetMapAlias {
    pub label_set: super::LabelSetId,
    pub which: AdditionalMapSlot,
}

#[derive(Copy, Clone)]
pub enum AdditionalMapSlot {
    Main,
    Additional,
}

impl Default for ReapplyConceptLabelSet {
    /// Port of the `CReapplyConceptLabelSet(CProcessContext*)` ctor's initial state.
    fn default() -> Self {
        ReapplyConceptLabelSet {
            modification_tag: ConceptLabelSetModificationTag::default(),
            concept_des_dep_map: HashMap::new(),
            additional_concept_des_dep_map: AdditionalDesDepMapRef::Null,
            core_con_des_linker: CoreConceptDescriptorId::NONE,
            concept_des_linker: Id::NONE,
            prev_concept_des_linker: Id::NONE,
            concept_signature: ConceptSetSignature::default(),
            concept_structure: ConceptSetStructure::default(),
            concept_flags: ConceptSetFlags::default(),
            concept_count: 0,
            process_context: INVALID,
        }
    }
}

impl ReapplyConceptLabelSet {
    /// Port of the `CReapplyConceptLabelSet(CProcessContext*)` ctor.
    pub fn new(process_context: Cint64) -> Self {
        ReapplyConceptLabelSet {
            process_context,
            ..Default::default()
        }
    }

    /// Port of inherited `getConceptLabelSetModificationTag`.
    pub fn get_concept_label_set_modification_tag(&self) -> Cint64 {
        self.modification_tag
            .get_concept_label_set_modification_tag()
    }

    /// Port of inherited `updateConceptLabelSetModificationTag(CProcessTagger*)`.
    pub fn update_concept_label_set_modification_tag(
        &mut self,
        process_tagger: &ProcessTagger,
    ) -> bool {
        self.modification_tag
            .update_concept_label_set_modification_tag_tagger(process_tagger)
    }

    /// Port of inherited `isConceptLabelSetModificationTagUpToDate(cint64)`.
    pub fn is_concept_label_set_modification_tag_up_to_date(
        &self,
        concept_label_set_modification_tag: Cint64,
    ) -> bool {
        self.modification_tag
            .is_concept_label_set_modification_tag_up_to_date(concept_label_set_modification_tag)
    }

    /// Port of `getConceptCount`.
    pub fn get_concept_count(&self) -> Cint64 {
        self.concept_count
    }
    /// Port of `getConceptSignatureValue` (`mConceptSignature.getSignatureValue()`).
    pub fn get_concept_signature_value(&self) -> Cint64 {
        self.concept_signature.signature_value
    }
    /// Port of `getCoreConceptDescriptorLinker`.
    pub fn get_core_concept_descriptor_linker(&self) -> CoreConceptDescriptorId {
        self.core_con_des_linker
    }

    // DEFER (LS-1): initConceptLabelSet (the COW share/rebuild heart, thresholds
    // 50 / *10), all insert*/get*/has*/contains* descriptor ops + reapply-queue
    // accessors, addCoreConceptDescriptor, the label-set iterator. See
    // `manifest/05-process-units.md` unit LS-1.
}

// ===========================================================================
// CReapplyRoleSuccessorHash  (port unit RS-1 holds the method bodies)
// ===========================================================================

/// Port of `CReapplyRoleSuccessorData` (`CReapplyRoleSuccessorData.h`) — the
/// per-role value of the successor hash. Carries the **3-way successor
/// representation** (intrusive link chain ⟷ localised link set ⟷ shared previous
/// link set) whose copy-on-write thresholds (`<= 100`, `*10`, `>= 5`) are
/// behaviour-load-bearing; all three slots + the `located` flag are kept explicit.
pub struct ReapplyRoleSuccessorData {
    /// `CPROCESSHASH<cint64,CIndividualLinkEdge*>* mLinkSet` — the localised set
    /// (coupled-id → edge). `None` == `nullptr`.
    /// KONCLUDE-PORT-NOTE[ownership]: owned-or-shared in C++ (raw pointer); the
    /// `located_link_set` flag distinguishes; RS-1 reproduces share-vs-copy.
    pub link_set: Option<HashMap<Cint64, EdgeId>>,
    /// `CPROCESSHASH<cint64,CIndividualLinkEdge*>* mPrevLinkSet` — the shared
    /// previous set kept un-copied until an entry is touched (the COW partner).
    pub prev_link_set: Option<HashMap<Cint64, EdgeId>>,
    // KONCLUDE-PORT-NOTE[ownership]: `CIndividualLinkEdge* mLinkLinker` — head of
    // the intrusive successor-edge chain (the always-present representation) → `EdgeId`.
    pub link_linker: EdgeId,
    /// `bool mLocatedLinkSet` — whether `link_set` is locally owned (not shared).
    pub located_link_set: bool,
    /// `cint64 mLinkCount`.
    pub link_count: Cint64,
    /// `CReapplyQueue mReapplyQueue` (held by value).
    pub reapply_queue: ReapplyQueue,
}

impl Default for ReapplyRoleSuccessorData {
    /// Port of the `CReapplyRoleSuccessorData()` ctor.
    fn default() -> Self {
        ReapplyRoleSuccessorData {
            link_set: None,
            prev_link_set: None,
            link_linker: Id::NONE,
            located_link_set: false,
            link_count: 0,
            reapply_queue: ReapplyQueue::new(),
        }
    }
}

/// Port of `CReapplyRoleSuccessorHash` (no base class).
#[derive(Clone)]
pub struct ReapplyRoleSuccessorHash {
    // KONCLUDE-PORT-NOTE[ownership]: ambient `CProcessContext*` handle (opaque).
    pub context: Cint64, // mContext
    /// `CPROCESSHASH<CRole*,CReapplyRoleSuccessorData> mRoleSuccessorDataHash`.
    /// KONCLUDE-PORT-NOTE[ownership]: `CRole*` key → `RoleId`. The whole hash is
    /// value-copied from the parent in `initRoleSuccessorHash` (implicit COW in
    /// C++); per-role 3-way COW lives in `ReapplyRoleSuccessorData`.
    pub role_successor_data_hash: HashMap<RoleId, ReapplyRoleSuccessorData>,
    /// `cint64 mLinkCount`.
    pub link_count: Cint64,
}

impl Default for ReapplyRoleSuccessorHash {
    fn default() -> Self {
        ReapplyRoleSuccessorHash {
            context: INVALID,
            role_successor_data_hash: HashMap::new(),
            link_count: 0,
        }
    }
}

impl ReapplyRoleSuccessorHash {
    /// Port of the `CReapplyRoleSuccessorHash(CProcessContext*)` ctor.
    pub fn new(context: Cint64) -> Self {
        ReapplyRoleSuccessorHash {
            context,
            ..Default::default()
        }
    }

    /// Port of `getRoleSuccessorCount` for the whole hash bookkeeping counter.
    /// (The per-role count getter is `ReapplyRoleSuccessorData::link_count`.)
    pub fn link_count(&self) -> Cint64 {
        self.link_count
    }

    /// Port of `getCoupledIndividualID(cint64, cint64)`.
    /// GOTCHA (RS-1): the coupled id is the integer **sum** of the two endpoint
    /// individual ids, NOT a pair — reproduced verbatim.
    pub fn get_coupled_individual_id(&self, indi1_id: Cint64, indi2_id: Cint64) -> Cint64 {
        indi1_id + indi2_id
    }

    // DEFER (RS-1): initRoleSuccessorHash, insertRoleSuccessorLink,
    // ensureRoleSuccessorDataLocalated (thresholds 100 / *10),
    // eliminateRoleSuccessorPreviousShareData, removeRoleSuccessorLink,
    // getRoleSuccessorToIndividualLink (the `link_count >= 5` locate trigger),
    // the link/role iterators, reapply-queue accessors. See unit RS-1.
}

// ===========================================================================
// CBranchingMergingProcessingRestrictionSpecification (unit BM-1 holds methods)
// ===========================================================================

/// Port of `CBranchingMergingProcessingRestrictionSpecification`
/// (`: public CProcessingRestrictionSpecification, public CDependencyTracker`).
///
/// KONCLUDE-PORT-NOTE[ownership]: the two multiple-inheritance bases become
/// composition (`priority_offset` + `next_restriction` from
/// `CProcessingRestrictionSpecification : CLinkerBase<double,…>`,
/// `dependency_track_point` from `CDependencyTracker`); the six
/// `CBranchingMergingIndividualNodeCandidateLinker*` chains become candidate-linker
/// head ids, and the `CXLinker<CIndividualLinkEdge*>*` chain a `Vec<EdgeId>`.
#[derive(Clone)]
pub struct BranchingMergingProcessingRestrictionSpecification {
    // --- base CProcessingRestrictionSpecification (: CLinkerBase<double,…>) ---
    /// `CLinkerBase<double,…>` data element (`getPriorityOffset`).
    pub priority_offset: f64,
    /// `CLinkerBase<double,…>::next` → next restriction spec in the chain.
    pub next_restriction: RestrictionSpecId,
    // --- base CDependencyTracker --------------------------------------------
    /// `CDependencyTrackPoint* mDependencyTrackPoint`.
    pub dependency_track_point: TrackPointId,

    // --- own fields ----------------------------------------------------------
    pub remaining_nominal_creation_count: Cint64, // mRemainingNominalCreationCount
    pub indi_link: EdgeId,                        // CIndividualLinkEdge* mIndiLink
    pub remaining_linker_merging_candidate_indi_node_count: Cint64, // mRemainingLinkerMergingCandidateIndiNodeCount
    pub remaining_valid_merging_candidate_indi_node_count: Cint64, // mRemainingValidMergingCandidateIndiNodeCount
    pub distinct_set_fixed: bool,                                  // mDistinctSetFixed
    pub has_merging_init_candidates: bool,                         // mHasMergingInitCandidates

    // --- the distinct-merged-nodes COW pair (behaviour-load-bearing) --------
    /// `CPROCESSSET<cint64>* mDistinctMergedNodesSet`. `None` == `nullptr`.
    pub distinct_merged_nodes_set: Option<HashSet<Cint64>>,
    /// `CPROCESSSET<cint64>* mLastDistinctMergedNodesSet` — the COW partner
    /// (`createLocalizedDistinctMergedNodeSet` localises on write).
    pub last_distinct_merged_nodes_set: Option<HashSet<Cint64>>,

    // --- six candidate-linker chain heads -----------------------------------
    pub nominal_merging_nodes_linker: CandidateLinkerId, // mNominalMergingNodesLinker
    pub merging_nodes_linker: CandidateLinkerId,         // mMergingNodesLinker
    pub merging_init_nodes_linker: CandidateLinkerId,    // mMergingInitNodesLinker
    pub only_pos_qualify_nodes_linker: CandidateLinkerId, // mOnlyPosQualifyNodesLinker
    pub only_neg_qualify_nodes_linker: CandidateLinkerId, // mOnlyNegQualifyNodesLinker
    pub both_qualify_nodes_linker: CandidateLinkerId,    // mBothQualifyNodesLinker

    // KONCLUDE-PORT-NOTE[ownership]: `CNonDeterministicDependencyNode*` →
    // `DependencyId` (the dependency-node arena, the §4 tagged enum).
    pub merging_dependency_node: DependencyId, // mMergingDependencyNode
    pub init_merging_nodes_clashes: ClashDescId, // CClashedDependencyDescriptor* mInitMergingNodesClashes
    pub multiple_init_merging_nodes_clashes: ClashDescId, // mMultipleInitMergingNodesClashes

    // KONCLUDE-PORT-NOTE[ownership]: ambient `CProcessContext*` handle (opaque).
    pub process_context: Cint64, // mProcessContext

    pub added_blockable_pred_merging_node_candidate: bool, // mAddedBlockablePredMergingNodeCandidate
    pub added_blockable_pred_dep_track_point: TrackPointId, // mAddedBlockablePredDepTrackPoint

    pub distinct_set_node_relocated: bool, // mDistinctSetNodeRelocated

    pub succ_choice_triggering_installed: bool, // mSuccChoiceTriggeringInstalled
    pub succ_choice_triggering_installed_count: Cint64, // mSuccChoiceTriggeringInstalledCount
    // KONCLUDE-PORT-NOTE[ownership]: `CXLinker<CIndividualLinkEdge*>*` → `Vec<EdgeId>`.
    pub last_checked_succ_choice_trigger_linker: Vec<EdgeId>, // mLastCheckedSuccChoiceTriggerLinker

    // KONCLUDE-PORT-NOTE[api]: the full `CProcessingRestrictionSpecification*`
    // hierarchy is still collapsed to this arena record. This field carries the
    // `CLinkProcessingRestrictionSpecification::mRestLink` payload for the live
    // restricted-reapply path.
    pub link_restriction: EdgeId,

    // --- at-most resume (the port's realisation of Konclude's incremental ---
    // --- reapplication; see `apply_atmost_rule` in completion/u08) --------
    /// `true` iff this record was initialised as a BRANCHING-MERGING rest (the
    /// C++ subclass discriminant: `applyATMOSTRule` may only resume from a
    /// `CBranchingMergingProcessingRestrictionSpecification`, never from the
    /// link-restriction payload the restricted-reapply path attaches).
    pub is_branching_merging: bool,
    /// KONCLUDE-PORT-NOTE[api]: Konclude resumes the successor scan from
    /// `mIndiLink` (its role-successor linker is newest-first, so iteration
    /// stops at the previously-newest link). The port's successor list is in
    /// edge-ARENA order, so the resume point is the edge-arena length at the
    /// end of the last scan: links with `index() >= scan_edge_watermark` are
    /// unseen. Consistency with epoch rollback: every truncating branch-epoch
    /// pop also journal-restores THIS record (`restriction_spec_mut` routes
    /// through `get_mut_journaled`), so the watermark and the edge arena roll
    /// back together — a watermark above the live edge-arena length is
    /// impossible; callers still clamp defensively and re-scan from 0 if it
    /// ever exceeds the arena length.
    pub scan_edge_watermark: Cint64,
}

impl Default for BranchingMergingProcessingRestrictionSpecification {
    fn default() -> Self {
        BranchingMergingProcessingRestrictionSpecification {
            priority_offset: 0.0,
            next_restriction: Id::NONE,
            dependency_track_point: Id::NONE,
            remaining_nominal_creation_count: 0,
            indi_link: Id::NONE,
            remaining_linker_merging_candidate_indi_node_count: 0,
            remaining_valid_merging_candidate_indi_node_count: 0,
            distinct_set_fixed: false,
            has_merging_init_candidates: false,
            distinct_merged_nodes_set: None,
            last_distinct_merged_nodes_set: None,
            nominal_merging_nodes_linker: Id::NONE,
            merging_nodes_linker: Id::NONE,
            merging_init_nodes_linker: Id::NONE,
            only_pos_qualify_nodes_linker: Id::NONE,
            only_neg_qualify_nodes_linker: Id::NONE,
            both_qualify_nodes_linker: Id::NONE,
            merging_dependency_node: Id::NONE,
            init_merging_nodes_clashes: Id::NONE,
            multiple_init_merging_nodes_clashes: Id::NONE,
            process_context: INVALID,
            added_blockable_pred_merging_node_candidate: false,
            added_blockable_pred_dep_track_point: Id::NONE,
            distinct_set_node_relocated: false,
            succ_choice_triggering_installed: false,
            succ_choice_triggering_installed_count: 0,
            last_checked_succ_choice_trigger_linker: Vec::new(),
            link_restriction: Id::NONE,
            is_branching_merging: false,
            scan_edge_watermark: 0,
        }
    }
}

impl BranchingMergingProcessingRestrictionSpecification {
    /// Port of the `CBranchingMergingProcessingRestrictionSpecification(CProcessContext*)` ctor.
    pub fn new(process_context: Cint64) -> Self {
        BranchingMergingProcessingRestrictionSpecification {
            process_context,
            ..Default::default()
        }
    }

    /// Port of `CProcessingRestrictionSpecification::initProcessingRestriction`.
    pub fn init_processing_restriction(&mut self, prev_rest: Option<&Self>) -> &mut Self {
        self.priority_offset = prev_rest.map_or(0.0, |prev| prev.priority_offset);
        self
    }
    /// Port of `getNextProcessingRestrictionSpecification`.
    pub fn get_next_processing_restriction_specification(&self) -> RestrictionSpecId {
        self.next_restriction
    }
    /// Port of `getPriorityOffset` (from the `CProcessingRestrictionSpecification` base).
    pub fn get_priority_offset(&self) -> f64 {
        self.priority_offset
    }
    /// Port of `setPriorityOffset`.
    pub fn set_priority_offset(&mut self, priority_offset: f64) -> &mut Self {
        self.priority_offset = priority_offset;
        self
    }
    /// Port of `CLinkProcessingRestrictionSpecification::initLinkRestriction`.
    pub fn init_link_restriction(&mut self, rest_link: EdgeId) -> &mut Self {
        self.link_restriction = rest_link;
        self
    }
    /// Port of `CLinkProcessingRestrictionSpecification::getLinkRestriction`.
    pub fn get_link_restriction(&self) -> EdgeId {
        self.link_restriction
    }
    /// Port of `getDependencyTrackPoint` (from the `CDependencyTracker` base).
    pub fn get_dependency_track_point(&self) -> TrackPointId {
        self.dependency_track_point
    }
    /// Port of `setDependencyTrackPoint`.
    pub fn set_dependency_track_point(
        &mut self,
        dependency_track_point: TrackPointId,
    ) -> &mut Self {
        self.dependency_track_point = dependency_track_point;
        self
    }
    /// Port of `isDistinctSetFixed`.
    pub fn is_distinct_set_fixed(&self) -> bool {
        self.distinct_set_fixed
    }
    /// Port of `setDistinctSetFixed`.
    pub fn set_distinct_set_fixed(&mut self, fixed: bool) -> &mut Self {
        self.distinct_set_fixed = fixed;
        self
    }
    /// Port of `getRemainingNominalCreationCount`.
    pub fn get_remaining_nominal_creation_count(&self) -> Cint64 {
        self.remaining_nominal_creation_count
    }
    /// Port of `setRemainingNominalCreationCount`.
    pub fn set_remaining_nominal_creation_count(&mut self, nom_count: Cint64) -> &mut Self {
        self.remaining_nominal_creation_count = nom_count;
        self
    }

    // DEFER (BM-1): initBranchingMergingProcessingRestriction, the candidate-linker
    // get/take/add/clear chains (6 lists), addDistinctMergedNode /
    // removeDistinctMergedNode + createLocalizedDistinctMergedNodeSet (the
    // distinct-set COW), the remaining-candidate counters, the merging-dependency /
    // clash-descriptor accessors, succ-choice-trigger handling. See unit BM-1.
}
