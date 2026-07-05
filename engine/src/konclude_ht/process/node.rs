//! `process::node` — SD-3: the completion-graph node
//! (`Source/Reasoner/Kernel/Process/CIndividualProcessNode.{h,cpp}`).
//!
//! Struct-definition unit only (wave W2). Every declared member variable of
//! `CIndividualProcessNode` is reproduced 1:1 for method-by-method diffability;
//! the `init*`/getter/setter logic is DEFERRED to method-batch units PN-1..PN-6
//! (see `manifest/05-process-units.md` §3; `// W2 method-batch: PN-n` markers
//! below mark where each lands).
//!
//! KONCLUDE-PORT-NOTE[ownership]: `CIndividualProcessNode` multiply-inherits four
//! bases (`CIndividualProcessNodeReference`, `CLocalizationTag`, `CBlockedTestTag`,
//! `CDependencyTracker`). Rust has no inheritance, so each base is FOLDED IN as
//! composition fields (grouped first, below). `CIndividualProcessNodeReference`
//! (→ `CProcessReference`) carries no data; `CLocalizationTag` and
//! `CBlockedTestTag` each separately inherit `CProcessTag`, so each contributes
//! its own `mProcessTag` (kept as two distinct fields, exact C++ layout);
//! `CDependencyTracker` supplies `dep_track_point`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: raw `CXxx*` back-pointers become typed arena
//! ids (`Id::NONE` == `nullptr`); intrusive `CXLinker`/`CXSortedNegLinker` chains
//! become `Vec`s (per `substrate.rs`). The triple-buffer (`mX`/`mUseX`/`mPrevX`),
//! double-buffer (`mX`/`mPrevX`) and loc/use (`mLocX`/`mUseX`) slots are the
//! branch save/restore core: they are kept as the EXPLICIT separate fields the
//! C++ declares (NOT collapsed), since `init*` shuffles them between `prev`/`use`
//! generations on branch entry.

#![allow(dead_code)]

use super::super::model::individual::{
    ConceptAssertion, DataAssertion, ReverseRoleAssertion, RoleAssertion,
};
use super::super::model::{Cint64, ConceptId, Id, IndividualId, NegLink};
use super::{ConDescId, EdgeId, LabelSetId, NodeId, RoleSuccHashId, TrackPointId};

// KONCLUDE-PORT-NOTE[api]: the not-yet-ported `Process/` helper/data classes that
// `CIndividualProcessNode` fields point at (the `CIndividualNode*Data`/hash/queue/
// linker classes + assertion linker chain heads) live as shared marker stubs in
// `process::stubs`; the node fields stay strongly typed via their `Id<T>` aliases.
use super::concept_process_linker::ConceptProcessLinkerId;
use super::individual_process_linker::IndividualProcessNodeLinkerId;
use super::reapply_sat::ReapplyConceptDescriptorId as ReapplyConDescId;
use super::role_backward_prop::RoleBackwardPropagationHashId as RoleBackPropHashId;
use super::stubs::{
    ATMOSTReactivationDataId, AdditionalDataAssertionsLinkerId, AdditionalRoleAssertionsLinkerId,
    AnalizedConExpDataId, BackendSyncDataId, BlockingFollowSetId, ConceptAssertionLinkerId,
    ConceptProcessingQueueId, ConceptPropBindingSetHashId, ConceptRepPropSetHashId,
    ConceptVarBindPathSetHashId, ConnSuccSetId, DataAssertionLinkerId, DatatypesValueSpaceDataId,
    DisjointSuccRoleHashId, DistinctHashId, IncExpDataId, IndiBlockDataId, IndiSatBlockDataId,
    IndividualMergingHashId, IndividualNodeModelDataId, MemAllocId, NominalConnectionSetId,
    ProcessAssertedDataLiteralLinkerId, ProcessContextId, ReactivationDataId, ReusingConExpDataId,
    ReverseRoleAssertionLinkerId, RoleAssertionLinkerId, SatCacheRetDataId, SatCacheStoringDataId,
    SigBlockConExpDataId, SuccRoleHashId, UnsatCacheRetId, VarPropBlockDataId,
};

/// Port of `CIndividualProcessNode::CIndividualType`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum IndividualType {
    /// `BLOCKABLEINDIVIDUALTYPE`.
    Blockable,
    /// `NOMINALINDIVIDUALTYPE`.
    Nominal,
}

impl Default for IndividualType {
    fn default() -> Self {
        IndividualType::Blockable
    }
}

/// Port of `CIndividualProcessNodePriority` (value type; held inline by the node).
/// KONCLUDE-PORT-NOTE[api]: a small by-value class — ported as a plain struct.
/// Full method set deferred; only the data + null/default are needed here.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct IndividualProcessNodePriority {
    pub priority_con: f64,  // mPriorityCon
    pub priority_ind: f64,  // mPriorityInd
    pub strict_order: bool, // mStrictOrder
}

impl Default for IndividualProcessNodePriority {
    /// Mirrors `CIndividualProcessNodePriority(0., 0., true)`.
    fn default() -> Self {
        IndividualProcessNodePriority {
            priority_con: 0.0,
            priority_ind: 0.0,
            strict_order: true,
        }
    }
}

impl IndividualProcessNodePriority {
    /// Port of `CIndividualProcessNodePriority::isNullPriority`.
    pub fn is_null_priority(&self) -> bool {
        self.priority_con == 0.0 && self.priority_ind == 0.0
    }

    /// Port of `CIndividualProcessNodePriority::getConceptPriority`.
    pub fn get_concept_priority(&self) -> f64 {
        self.priority_con
    }

    /// Port of `CIndividualProcessNodePriority::getIndividualPriority`.
    pub fn get_individual_priority(&self) -> f64 {
        self.priority_ind
    }

    /// Port of `CIndividualProcessNodePriority::setPriority`.
    pub fn set_priority(&mut self, con_priority: f64, indi_priority: f64) -> &mut Self {
        self.priority_con = con_priority;
        self.priority_ind = indi_priority;
        self
    }

    /// Port of `CIndividualProcessNodePriority::setPriorityToNull`.
    pub fn set_priority_to_null(&mut self) -> &mut Self {
        self.priority_con = 0.0;
        self.priority_ind = 0.0;
        self.strict_order = true;
        self
    }

    /// Port of `operator<=`.
    pub fn le_priority(&self, indi_priority: &Self) -> bool {
        let strict_order = self.strict_order || indi_priority.strict_order;
        if strict_order {
            if self.priority_ind < indi_priority.priority_ind {
                true
            } else if self.priority_ind > indi_priority.priority_ind {
                false
            } else {
                self.priority_con <= indi_priority.priority_con
            }
        } else {
            let same_concept_priority = self.priority_con == indi_priority.priority_con;
            (same_concept_priority && self.priority_ind <= indi_priority.priority_ind)
                || (!same_concept_priority && self.priority_con >= indi_priority.priority_con)
        }
    }

    /// Port of `operator>=`.
    pub fn ge_priority(&self, indi_priority: &Self) -> bool {
        let strict_order = self.strict_order || indi_priority.strict_order;
        if strict_order {
            if self.priority_ind > indi_priority.priority_ind {
                true
            } else if self.priority_ind < indi_priority.priority_ind {
                false
            } else {
                self.priority_con >= indi_priority.priority_con
            }
        } else {
            let same_concept_priority = self.priority_con == indi_priority.priority_con;
            (same_concept_priority && self.priority_ind >= indi_priority.priority_ind)
                || (!same_concept_priority && self.priority_con <= indi_priority.priority_con)
        }
    }

    /// Port of `operator<`.
    pub fn lt_priority(&self, indi_priority: &Self) -> bool {
        let strict_order = self.strict_order || indi_priority.strict_order;
        if strict_order {
            self.priority_ind < indi_priority.priority_ind
        } else {
            let same_concept_priority = self.priority_con == indi_priority.priority_con;
            (same_concept_priority && self.priority_ind < indi_priority.priority_ind)
                || (!same_concept_priority && self.priority_con > indi_priority.priority_con)
        }
    }

    /// Port of `operator>`.
    pub fn gt_priority(&self, indi_priority: &Self) -> bool {
        let strict_order = self.strict_order || indi_priority.strict_order;
        if strict_order {
            self.priority_ind > indi_priority.priority_ind
        } else {
            let same_concept_priority = self.priority_con == indi_priority.priority_con;
            (same_concept_priority && self.priority_ind > indi_priority.priority_ind)
                || (!same_concept_priority && self.priority_con < indi_priority.priority_con)
        }
    }
}

/// Port of `CIndividualProcessNode`.
///
/// A node in the per-satisfiability-test completion graph: the most-referenced
/// type in the process model. Fields are grouped per `manifest/05-process-units.md`
/// §SD-3 (A triples / B doubles / C loc-use / D identity / … / K singletons) and
/// otherwise follow the C++ declaration order for diffability.
pub struct IndividualProcessNode {
    // === folded bases (KONCLUDE-PORT-NOTE[ownership]) =====================
    // `CIndividualProcessNodeReference` (→ `CProcessReference`): no data.
    /// `CLocalizationTag::CProcessTag::mProcessTag`.
    pub localization_tag: Cint64,
    /// `CLocalizationTag::mRelocalized`.
    pub relocalized: bool,
    /// `CBlockedTestTag::CProcessTag::mProcessTag`.
    pub blocked_test_tag: Cint64,
    /// `CDependencyTracker::mDependencyTrackPoint`.
    pub dep_track_point: TrackPointId,

    // === public member ====================================================
    /// `mDebugBlockerLastConceptDes`.
    pub debug_blocker_last_concept_des: ConDescId,

    // === D. identity / topology ===========================================
    pub indi_id: Cint64,           // mIndiID
    pub indi_type: IndividualType, // mIndiType
    pub nom_indi: IndividualId,    // mNomIndi (CIndividual*)
    /// `mProcessingRestrictionFlags` — bitset over the `PRF_*` masks below.
    pub processing_restriction_flags: Cint64,
    pub indi_anc_depth: Cint64,            // indiAncDepth
    pub nominal_level: Cint64,             // mNominalLevel
    pub ancestor_link: EdgeId,             // mAncestorLink (CIndividualLinkEdge*)
    pub merge_into_id: Cint64,             // mMergeIntoID
    pub process_context: ProcessContextId, // mProcessContext
    pub mem_alloc_man: MemAllocId,         // mMemAllocMan
    pub prev_individual: NodeId,           // mPrevIndividual

    // === A. triple-buffers (mX / mUseX / mPrevX) ==========================
    // 1. concept-processing queue
    pub concept_processing_queue: ConceptProcessingQueueId, // mConceptProcessingQueue
    pub use_concept_processing_queue: ConceptProcessingQueueId, // mUseConceptProcessingQueue
    pub prev_concept_processing_queue: ConceptProcessingQueueId, // mPrevConceptProcessingQueue
    // 2. reapply concept-label set
    pub reapply_con_label_set: LabelSetId, // mReapplyConLabelSet
    pub use_reapply_con_label_set: LabelSetId, // mUseReapplyConLabelSet
    pub prev_reapply_con_label_set: LabelSetId, // mPrevReapplyConLabelSet
    // 3. reapply role-successor hash
    pub reapply_role_succ_hash: RoleSuccHashId, // mReapplyRoleSuccHash
    pub use_reapply_role_succ_hash: RoleSuccHashId, // mUseReapplyRoleSuccHash
    pub prev_reapply_role_succ_hash: RoleSuccHashId, // mPrevReapplyRoleSuccHash
    // 4. successor-role hash
    pub succ_role_hash: SuccRoleHashId,      // mSuccRoleHash
    pub use_succ_role_hash: SuccRoleHashId,  // mUseSuccRoleHash
    pub prev_succ_role_hash: SuccRoleHashId, // mPrevSuccRoleHash

    pub last_added_link: EdgeId, // mLastAddedLink (CIndividualLinkEdge*)
    pub blocker_indi_node: NodeId, // mBlockerIndiNode
    pub following_indi_node: NodeId, // mFollowingIndiNode

    // 5. connection-successor set
    pub conn_succ_set: ConnSuccSetId,      // mConnSuccSet
    pub use_conn_succ_set: ConnSuccSetId,  // mUseConnSuccSet
    pub prev_conn_succ_set: ConnSuccSetId, // mPrevConnSuccSet
    // 6. distinct hash
    pub distinct_hash: DistinctHashId,      // mDistinctHash
    pub use_distinct_hash: DistinctHashId,  // mUseDistinctHash
    pub prev_distinct_hash: DistinctHashId, // mPrevDistinctHash

    pub disjoint_role_connections: bool, // mDisjointRoleConnections
    // 7. disjoint-successor-role hash
    pub disjoint_succ_role_hash: DisjointSuccRoleHashId, // mDisjointSuccRoleHash
    pub use_disjoint_succ_role_hash: DisjointSuccRoleHashId, // mUseDisjointSuccRoleHash
    pub prev_disjoint_succ_role_hash: DisjointSuccRoleHashId, // mPrevDisjointSuccRoleHash

    // === B. double-buffers (mX / mPrevX) (interleaved, C++ order) =========
    // 1. saturation-blocking data
    pub indi_sat_block_data: IndiSatBlockDataId, // mIndiSatBlockData
    pub prev_indi_sat_block_data: IndiSatBlockDataId, // mPrevIndiSatBlockData
    // 2. block data
    pub indi_block: IndiBlockDataId,      // mIndiBlock
    pub prev_indi_block: IndiBlockDataId, // mPrevIndiBlock
    // 3. variable-bindings propagation block data
    pub indi_var_prop_block_data: VarPropBlockDataId, // mIndiVarPropBlockData
    pub prev_indi_var_prop_block_data: VarPropBlockDataId, // mPrevIndiVarPropBlockData
    // 4. unsat-cache retrieval data
    pub indi_unsat_cache_ret: UnsatCacheRetId, // mIndiUnsatCacheRet
    pub prev_indi_unsat_cache_ret: UnsatCacheRetId, // mPrevIndiUnsatCacheRet

    // === A. triple (8) sig-block analyzed-expansion data ==================
    pub sig_block_ind_expl_data: AnalizedConExpDataId, // mSigBlockIndExplData
    pub use_sig_block_ind_expl_data: AnalizedConExpDataId, // mUseSigBlockIndExplData
    pub prev_sig_block_ind_expl_data: AnalizedConExpDataId, // mPrevSigBlockIndExplData

    // === B. double (5) sig-block concept-expansion data ===================
    pub sig_block_con_exp_data: SigBlockConExpDataId, // mSigBlockConExpData
    pub prev_sig_block_con_exp_data: SigBlockConExpDataId, // mPrevSigBlockConExpData
    // === B. double (6) reusing-expansion data =============================
    pub reusing_con_exp_data: ReusingConExpDataId, // mReusingConExpData
    pub prev_reusing_con_exp_data: ReusingConExpDataId, // mPrevReusingConExpData

    // === A. triple (9) sig-block follow set ===============================
    pub sig_block_follow_set: BlockingFollowSetId, // mSigBlockFollowSet
    pub use_sig_block_follow_set: BlockingFollowSetId, // mUseSigBlockFollowSet
    pub prev_sig_block_follow_set: BlockingFollowSetId, // mPrevSigBlockFollowSet

    // === A. triples (10/11/12) concept prop/var-bind-path/rep-prop hashes ==
    pub concept_prop_binding_set_hash: ConceptPropBindingSetHashId, // mConceptPropBindingSetHash
    pub use_concept_prop_binding_set_hash: ConceptPropBindingSetHashId, // mUseConceptPropBindingSetHash
    pub prev_concept_prop_binding_set_hash: ConceptPropBindingSetHashId, // mPrevConceptPropBindingSetHash

    pub concept_var_bind_path_set_hash: ConceptVarBindPathSetHashId, // mConceptVarBindPathSetHash
    pub use_concept_var_bind_path_set_hash: ConceptVarBindPathSetHashId, // mUseConceptVarBindPathSetHash
    pub prev_concept_var_bind_path_set_hash: ConceptVarBindPathSetHashId, // mPrevConceptVarBindPathSetHash

    pub concept_rep_prop_set_hash: ConceptRepPropSetHashId, // mConceptRepPropSetHash
    pub use_concept_rep_prop_set_hash: ConceptRepPropSetHashId, // mUseConceptRepPropSetHash
    pub prev_concept_rep_prop_set_hash: ConceptRepPropSetHashId, // mPrevConceptRepPropSetHash

    // === E. blocking / sig-blocking =======================================
    pub invalid_signature_blocking: bool, // mInvalidSignatureBlocking

    // === F. assertion-init linkers / iterators ============================
    pub init_concept_descriptor: ConDescId, // mInitConceptDescriptor (CConceptDescriptor*)
    /// `mInitializingConceptLinkerIt` (`CXSortedNegLinker<CConcept*>*`).
    pub initializing_concept_linker: Vec<NegLink<ConceptId>>,
    /// `mProcessInitializingConceptLinkerIt`.
    pub process_initializing_concept_linker: Vec<NegLink<ConceptId>>,
    pub assertion_concept_linker: ConceptAssertionLinkerId, // mAssertionConceptLinkerIt
    /// Rust-owned bridge for `mAssertionConceptLinkerIt` while the pointer
    /// linker class remains an opaque id.
    pub assertion_concept_assertions: Vec<ConceptAssertion>,
    pub assertion_data_linker: DataAssertionLinkerId, // mAssertionDataLinkerIt
    /// Rust-owned bridge for `mAssertionDataLinkerIt`.
    pub assertion_data_assertions: Vec<DataAssertion>,
    pub last_processed_assertion_data_linker: DataAssertionLinkerId, // mLastProcessedAssertionDataLinker
    pub assertion_role_linker: RoleAssertionLinkerId,                // mAssertionRoleLinkerIt
    /// Rust-owned bridge for `mAssertionRoleLinkerIt`.
    pub assertion_role_assertions: Vec<RoleAssertion>,
    pub reverse_assertion_role_linker: ReverseRoleAssertionLinkerId, // mReverseAssertionRoleLinkerIt
    /// Rust-owned bridge for `mReverseAssertionRoleLinkerIt`.
    pub reverse_assertion_role_assertions: Vec<ReverseRoleAssertion>,
    pub additional_role_assertions_linker: AdditionalRoleAssertionsLinkerId, // mAdditionalRoleAssertionsLinker
    pub additional_data_assertions_linker: AdditionalDataAssertionsLinkerId, // mAdditionalDataAssertionsLinker
    pub last_processed_additional_data_assertions_linker: AdditionalDataAssertionsLinkerId, // mLastProcessedAdditionalDataAssertionsLinker

    // === G. assertion-init bool flags + creation id =======================
    pub role_assertions_initialized: bool, // mRoleAssertionsInitialized
    pub reverse_role_assertions_initialized: bool, // mReverseRoleAssertionsInitialized
    pub role_assertion_creation_id: Cint64, // mRoleAssertionCreationID

    pub asserted_data_literal_linker: ProcessAssertedDataLiteralLinkerId, // mAssertedDataLiteralLinker
    pub last_asserted_data_literal_linker: ProcessAssertedDataLiteralLinkerId, // mLastAssertedDataLiteralLinker

    pub base_concepts_initialized: bool, // mBaseConceptsInitialized
    pub universally_connection_individual_initialized: bool, // mUniversallyConnectionIndividualInitialized
    pub nominal_indi_triples_assertions: bool,               // mNominalIndiTriplesAssertions
    pub loaded_nominal_indi_triples_assertions: bool,        // mLoadedNominalIndiTriplesAssertions
    pub loaded_nominal_indi_representative_backend_data: bool, // mLoadedNominalIndiRepresentativeBackendData

    // === E. blocker-candidate counts ======================================
    pub last_concept_count_cached_blocker_candidate: Cint64, // mLastConceptCountCachedBlockerCandidate
    pub last_concept_count_search_blocker_candidate: Cint64, // mLastConceptCountSearchBlockerCandidate
    pub last_search_blocker_candidate_count: Cint64,         // mLastSearchBlockerCandidateCount
    pub last_search_blocker_candidate_signature: Cint64,     // mLastSearchBlockerCandidateSignature
    pub blocking_caching_saved_candidate_count: Cint64,      // mBlockingCachingSavedCandidateCount

    /// `mBlockedIndividualsLinker` (`CXLinker<CIndividualProcessNode*>*` → `Vec`).
    pub blocked_individuals_linker: Vec<NodeId>,

    // === I. propagation / backward-dep ====================================
    /// `mSuccessorIndiNodeBackwardDependencyLinker` (`CXLinker<...>*` → `Vec`).
    pub successor_indi_node_backward_dependency_linker: Vec<NodeId>,
    pub backward_dependency_to_ancestor_individual_node: bool, // mBackwardDependencyToAncestorIndividualNode

    // === H. caching / model ===============================================
    pub indi_model: IndividualNodeModelDataId, // indiModel
    // === B. doubles (7/8/9) sat-cache retrieval/storing + backend sync =====
    pub sat_cache_ret_data: SatCacheRetDataId, // mSatCacheRetData
    pub prev_sat_cache_ret_data: SatCacheRetDataId, // mPrevSatCacheRetData
    pub sat_cache_storing_data: SatCacheStoringDataId, // mSatCacheStoringData
    pub prev_sat_cache_storing_data: SatCacheStoringDataId, // mPrevSatCacheStoringData
    pub backend_sync_data: BackendSyncDataId,  // mBackendSyncData
    pub prev_backend_sync_data: BackendSyncDataId, // mPrevBackendSyncData

    pub processing_blocked_indi: NodeId, // mProcessingBlockedIndi
    /// `mProcessingBlockedIndividualsLinker` (`CXLinker<...>*` → `Vec`).
    pub processing_blocked_individuals_linker: Vec<NodeId>,

    pub sat_cached_absorbed_disjunctions_reapply_con_des: ReapplyConDescId, // mSatCachedAbsorbedDisjunctionsReapplyConDes
    pub sat_cached_absorbed_successor_reapply_con_des: ReapplyConDescId, // mSatCachedAbsorbedSuccessorReapplyConDes

    pub role_back_prop_hash: RoleBackPropHashId, // mRoleBackPropHash
    pub indi_process_linker: IndividualProcessNodeLinkerId, // mIndiProcessLinker
    pub concept_process_linker: ConceptProcessLinkerId, // mConceptProcessLinker
    pub required_back_prop: bool,                // mRequiredBackProp
    pub substitute_indi_node: NodeId,            // mSubstituteIndiNode

    // === J. queue-membership bools + priority =============================
    pub extended_queue_processing: bool, // mExtendedQueueProcessing
    pub immediately_processing_queued: bool, // mImmediatelyProcessingQueued
    pub det_exp_processing_queued: bool, // mDetExpProcessingQueued
    pub depth_processing_queued: bool,   // mDepthProcessingQueued
    pub blocked_react_processing_queued: bool, // mBlockedReactProcessingQueued
    pub backend_synchron_retest_processing_queued: bool, // mBackendSynchronRetestProcessingQueued
    pub backend_indirect_compatibility_expansion_queued: bool, // mBackendIndirectCompatibilityExpansionQueued
    pub backend_direct_influence_expansion_queued: bool, // mBackendDirectInfluenceExpansionQueued
    pub incremental_compatibility_checking_queued: bool, // mIncrementalCompatibilityCheckingQueued
    pub incremental_expansion_queued: bool,              // mIncrementalExpansionQueued
    pub processing_queued: bool,                         // mProcessingQueued
    pub backend_reuse_expansion_queued: bool,            // mBackendReuseExpansionQueued
    pub backend_neighbour_expansion_queued: bool,        // mBackendNeighbourExpansionQueued
    pub last_processing_priority: IndividualProcessNodePriority, // mLastProcessingPriority

    pub delayed_nominal_processing_queued: bool, // mDelayedNominalProcessingQueued
    pub nominal_processing_delaying_checked: bool, // mNominalProcessingDelayingChecked
    pub assertion_initialisation_signature_value: Cint64, // mAssertionInitialisationSignatureValue

    // === K. reactivation / nominal-conn / datatype / incremental + merge ===
    pub caching_loss_node_reactivation_installed: bool, // mCachingLossNodeReactivationInstalled
    // === C. loc/use pairs (mUseX / mLocX) =================================
    // 1. reactivation
    pub use_reactivation_data: ReactivationDataId, // mUseReactivationData
    pub loc_reactivation_data: ReactivationDataId, // mLocReactivationData
    // 2. ATMOST-reactivation
    pub use_succ_indi_atmost_reactivation_data: ATMOSTReactivationDataId, // mUseSuccIndiATMOSTReactivationData
    pub loc_succ_indi_atmost_reactivation_data: ATMOSTReactivationDataId, // mLocSuccIndiATMOSTReactivationData
    // 3. nominal-connection set
    pub use_nominal_connection_set: NominalConnectionSetId, // mUseNominalConnectionSet
    pub loc_nominal_connection_set: NominalConnectionSetId, // mLocNominalConnectionSet
    // 4. datatypes value-space data
    pub use_datatypes_value_space_data: DatatypesValueSpaceDataId, // mUseDatatypesValueSpaceData
    pub loc_datatypes_value_space_data: DatatypesValueSpaceDataId, // mLocDatatypesValueSpaceData
    // 5. incremental-expansion data
    pub use_inc_exp_data: IncExpDataId, // mUseIncExpData
    pub loc_inc_exp_data: IncExpDataId, // mLocIncExpData
    pub inc_exp_id: Cint64,             // mIncExpID
    // 6. merging hash
    pub use_individual_merging_hash: IndividualMergingHashId, // mUseIndividualMergingHash
    pub loc_individual_merging_hash: IndividualMergingHashId, // mLocIndividualMergingHash

    pub merged_dep_track_point: TrackPointId, // mMergedDepTrackPoint (CDependencyTrackPoint*)
    pub last_merged_into_individual_node: NodeId, // mLastMergedIntoIndividualNode
}

impl IndividualProcessNode {
    // ---- processing-restriction flags (PRF*) -----------------------------
    // Port of the `const static cint64 PRF...` masks (`.h` 553–627). Bitset over
    // `processing_restriction_flags`.
    pub const PRF_DIRECTBLOCKED: Cint64 = 0x1;
    pub const PRF_PROCESSINGBLOCKED: Cint64 = 0x2;
    pub const PRF_INDIRECTBLOCKED: Cint64 = 0x4;
    pub const PRF_PURGEDBLOCKED: Cint64 = 0x8;
    pub const PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED: Cint64 = 0x10;
    pub const PRF_INVALIDBLOCKINGORCACHING: Cint64 = 0x20;

    pub const PRF_BLOCKINGRETESTDUEANCESTORMODIFIED: Cint64 = 0x100;
    pub const PRF_BLOCKINGRETESTDUEDIRECTMODIFIED: Cint64 = 0x200;
    pub const PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED: Cint64 = 0x400;
    pub const PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS: Cint64 = 0x800;

    pub const PRF_PROCESSINGCOMPLETED: Cint64 = 0x1000;
    pub const PRF_ANCESTORALLPROCESSED: Cint64 = 0x2000;

    pub const PRF_CONSNODEPREPARATIONINDINODE: Cint64 = 0x10000;
    pub const PRF_CONCRETEDATAINDINODE: Cint64 = 0x20000;

    pub const PRF_SATISFIABLECACHED: Cint64 = 0x100000;
    pub const PRF_ANCESTORSATISFIABLECACHED: Cint64 = 0x200000;
    pub const PRF_RETESTSATISFIABLECACHEDDUEDIRECTMODIFIED: Cint64 = 0x400000;
    pub const PRF_ANCESTORSATISFIABLECACHEDABOLISHED: Cint64 = 0x800000;

    pub const PRF_SIGNATUREBLOCKINGCACHED: Cint64 = 0x1000000;
    pub const PRF_ANCESTORSIGNATUREBLOCKINGCACHED: Cint64 = 0x2000000;
    pub const PRF_RETESTSIGNATUREBLOCKINGCACHEDDUEDIRECTMODIFIED: Cint64 = 0x4000000;
    pub const PRF_ANCESTORSIGNATUREBLOCKINGCACHEDABOLISHED: Cint64 = 0x8000000;

    pub const PRF_SATURATIONBLOCKINGCACHED: Cint64 = 0x10000000;
    pub const PRF_ANCESTORSATURATIONBLOCKINGCACHED: Cint64 = 0x20000000;
    pub const PRF_RETESTSATURATIONBLOCKINGCACHEDDUEDIRECTMODIFIED: Cint64 = 0x40000000;
    pub const PRF_ANCESTORSATURATIONBLOCKINGCACHEDABOLISHED: Cint64 = 0x80000000;

    pub const PRF_SATURATIONSUCCESSORCREATIONBLOCKINGCACHED: Cint64 = 0x100000000;
    pub const PRF_SATURATIONBLOCKINGCACHEDINVALIDATED: Cint64 = 0x200000000;
    pub const PRF_SATURATIONBLOCKINGCACHEDRETESTDUETOMODIFICATION: Cint64 = 0x400000000;

    pub const PRF_COMPLETIONGRAPHCACHED: Cint64 = 0x1000000000;
    pub const PRF_COMPLETIONGRAPHCACHINGINVALID: Cint64 = 0x2000000000;
    pub const PRF_COMPLETIONGRAPHCACHINGINVALIDATED: Cint64 = 0x4000000000;
    pub const PRF_RETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED: Cint64 = 0x8000000000;

    pub const PRF_COMPLETIONGRAPHCACHEDNODELOCATED: Cint64 = 0x10000000000;
    pub const PRF_COMPLETIONGRAPHCACHEDNODEEXTENDED: Cint64 = 0x20000000000;

    pub const PRF_SUCCESSORNOMINALCONNECTION: Cint64 = 0x40000000000;
    pub const PRF_SUCCESSORNEWNOMINALCONNECTION: Cint64 = 0x80000000000;

    pub const PRF_REUSINGINDIVIDUAL: Cint64 = 0x100000000000;
    pub const PRF_ANCESTORREUSINGINDIVIDUALBLOCKED: Cint64 = 0x200000000000;
    pub const PRF_ANCESTORREUSINGINDIVIDUALBLOCKEDABOLISHED: Cint64 = 0x400000000000;

    pub const PRF_CACHEDCOMPUTEDTYPESADDED: Cint64 = 0x1000000000000;

    pub const PRF_SYNCHRONIZEDBACKEND: Cint64 = 0x10000000000000;
    pub const PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED: Cint64 = 0x20000000000000;
    pub const PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED: Cint64 = 0x40000000000000;
    pub const PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED: Cint64 = 0x80000000000000;

    pub const PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED: Cint64 = 0x100000000000000;

    pub const PRF_SYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION: Cint64 = 0x200000000000000;
    pub const PRF_SYNCHRONIZEDBACKENNEIGHBOURDFULLEXPANSION: Cint64 = 0x400000000000000;
    pub const PRF_SYNCHRONIZEDBACKENPROCESSINGDELAYING: Cint64 = 0x800000000000000;

    pub const PRF_BACKENDEXPANSIONREUSINGINDIVIDUAL: Cint64 = 0x1000000000000000;
    pub const PRF_BACKENDEXPANSIONREUSEDISCARDED: Cint64 = 0x2000000000000000;

    pub const PRF_INCREMENTALEXPANDING: Cint64 = 0x4000000000000000;
    // KONCLUDE-PORT-NOTE[int-width]: C++ `cint64` is signed; `0x8000...` (bit 63)
    // overflows `i64` as a literal, so it is built from the unsigned pattern.
    pub const PRF_INCREMENTALEXPANSIONRETESTDUEDIRECTMODIFIED: Cint64 =
        0x8000000000000000u64 as Cint64;

    pub const PRF_BLOCKINGRELATEDFLAGCOMPINATION: Cint64 = Self::PRF_DIRECTBLOCKED
        | Self::PRF_INDIRECTBLOCKED
        | Self::PRF_PROCESSINGBLOCKED
        | Self::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED
        | Self::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED
        | Self::PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED
        | Self::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED
        | Self::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS;

    pub const PRF_INVALIDATEBLOCKERFLAGSCOMPINATION: Cint64 = Self::PRF_DIRECTBLOCKED
        | Self::PRF_INDIRECTBLOCKED
        | Self::PRF_PROCESSINGBLOCKED
        | Self::PRF_PURGEDBLOCKED
        | Self::PRF_SATISFIABLECACHED
        | Self::PRF_ANCESTORSATISFIABLECACHED
        | Self::PRF_SIGNATUREBLOCKINGCACHED
        | Self::PRF_ANCESTORSIGNATUREBLOCKINGCACHED
        | Self::PRF_REUSINGINDIVIDUAL
        | Self::PRF_ANCESTORREUSINGINDIVIDUALBLOCKED
        | Self::PRF_ANCESTORSATURATIONBLOCKINGCACHED
        | Self::PRF_CONCRETEDATAINDINODE;

    /// Port of `CIndividualProcessNode::CIndividualProcessNode(CProcessContext*)`.
    /// Mirrors the constructor's all-null/zero/false initialisation. The C++ ctor
    /// also derives `mMemAllocMan` from the context and seeds the localization tag
    /// from `processContext->getUsedProcessTagger()`; both depend on the ambient
    /// context and are DEFERRED to PN-1 (the tagger is not yet ported).
    pub fn new(process_context: ProcessContextId) -> Self {
        IndividualProcessNode {
            process_context,
            ..Default::default()
        }
    }

    // W2 method-batch: PN-1 — init/clone (ctor body, initIndividualProcessNode,
    //                          initIndividualProcessNodeCopy).
    // W2 method-batch: PN-2 — assertion/init-concept linkers + init-state flags + identity.
    // W2 method-batch: PN-3 — label/prop-hash getters + role-successor/edge ops +
    //                          reapply queues + topology/link install-remove.
    // W2 method-batch: PN-4 — model/cache/blocking-data accessors + depth/merge-into +
    //                          processing-blocked linkers + restriction flags + counts.
    // W2 method-batch: PN-5 — invalid-sig blocking + backward-dep linkers + backprop/
    //                          process-node linkers + queue membership + priority.
    // W2 method-batch: PN-6 — reactivation / nominal-conn / datatype / incremental + merge.
}

impl Default for IndividualProcessNode {
    /// All-null/zero/false, matching the C++ constructor's field initialisation
    /// (`mIndiType = BLOCKABLEINDIVIDUALTYPE`, every pointer `nullptr`/`Id::NONE`,
    /// every linker empty, every count 0, every flag false).
    fn default() -> Self {
        IndividualProcessNode {
            localization_tag: 0,
            relocalized: false,
            blocked_test_tag: 0,
            dep_track_point: Id::NONE,
            debug_blocker_last_concept_des: Id::NONE,

            indi_id: 0,
            indi_type: IndividualType::Blockable,
            nom_indi: Id::NONE,
            processing_restriction_flags: 0,
            indi_anc_depth: 0,
            nominal_level: 0,
            ancestor_link: Id::NONE,
            merge_into_id: 0,
            process_context: Id::NONE,
            mem_alloc_man: Id::NONE,
            prev_individual: Id::NONE,

            concept_processing_queue: Id::NONE,
            use_concept_processing_queue: Id::NONE,
            prev_concept_processing_queue: Id::NONE,
            reapply_con_label_set: Id::NONE,
            use_reapply_con_label_set: Id::NONE,
            prev_reapply_con_label_set: Id::NONE,
            reapply_role_succ_hash: Id::NONE,
            use_reapply_role_succ_hash: Id::NONE,
            prev_reapply_role_succ_hash: Id::NONE,
            succ_role_hash: Id::NONE,
            use_succ_role_hash: Id::NONE,
            prev_succ_role_hash: Id::NONE,

            last_added_link: Id::NONE,
            blocker_indi_node: Id::NONE,
            following_indi_node: Id::NONE,

            conn_succ_set: Id::NONE,
            use_conn_succ_set: Id::NONE,
            prev_conn_succ_set: Id::NONE,
            distinct_hash: Id::NONE,
            use_distinct_hash: Id::NONE,
            prev_distinct_hash: Id::NONE,

            disjoint_role_connections: false,
            disjoint_succ_role_hash: Id::NONE,
            use_disjoint_succ_role_hash: Id::NONE,
            prev_disjoint_succ_role_hash: Id::NONE,

            indi_sat_block_data: Id::NONE,
            prev_indi_sat_block_data: Id::NONE,
            indi_block: Id::NONE,
            prev_indi_block: Id::NONE,
            indi_var_prop_block_data: Id::NONE,
            prev_indi_var_prop_block_data: Id::NONE,
            indi_unsat_cache_ret: Id::NONE,
            prev_indi_unsat_cache_ret: Id::NONE,

            sig_block_ind_expl_data: Id::NONE,
            use_sig_block_ind_expl_data: Id::NONE,
            prev_sig_block_ind_expl_data: Id::NONE,

            sig_block_con_exp_data: Id::NONE,
            prev_sig_block_con_exp_data: Id::NONE,
            reusing_con_exp_data: Id::NONE,
            prev_reusing_con_exp_data: Id::NONE,

            sig_block_follow_set: Id::NONE,
            use_sig_block_follow_set: Id::NONE,
            prev_sig_block_follow_set: Id::NONE,

            concept_prop_binding_set_hash: Id::NONE,
            use_concept_prop_binding_set_hash: Id::NONE,
            prev_concept_prop_binding_set_hash: Id::NONE,
            concept_var_bind_path_set_hash: Id::NONE,
            use_concept_var_bind_path_set_hash: Id::NONE,
            prev_concept_var_bind_path_set_hash: Id::NONE,
            concept_rep_prop_set_hash: Id::NONE,
            use_concept_rep_prop_set_hash: Id::NONE,
            prev_concept_rep_prop_set_hash: Id::NONE,

            invalid_signature_blocking: false,

            init_concept_descriptor: Id::NONE,
            initializing_concept_linker: Vec::new(),
            process_initializing_concept_linker: Vec::new(),
            assertion_concept_linker: Id::NONE,
            assertion_concept_assertions: Vec::new(),
            assertion_data_linker: Id::NONE,
            assertion_data_assertions: Vec::new(),
            last_processed_assertion_data_linker: Id::NONE,
            assertion_role_linker: Id::NONE,
            assertion_role_assertions: Vec::new(),
            reverse_assertion_role_linker: Id::NONE,
            reverse_assertion_role_assertions: Vec::new(),
            additional_role_assertions_linker: Id::NONE,
            additional_data_assertions_linker: Id::NONE,
            last_processed_additional_data_assertions_linker: Id::NONE,

            role_assertions_initialized: false,
            reverse_role_assertions_initialized: false,
            role_assertion_creation_id: 0,

            asserted_data_literal_linker: Id::NONE,
            last_asserted_data_literal_linker: Id::NONE,

            base_concepts_initialized: false,
            universally_connection_individual_initialized: false,
            nominal_indi_triples_assertions: false,
            loaded_nominal_indi_triples_assertions: false,
            loaded_nominal_indi_representative_backend_data: false,

            last_concept_count_cached_blocker_candidate: 0,
            last_concept_count_search_blocker_candidate: 0,
            last_search_blocker_candidate_count: 0,
            last_search_blocker_candidate_signature: 0,
            blocking_caching_saved_candidate_count: 0,

            blocked_individuals_linker: Vec::new(),

            successor_indi_node_backward_dependency_linker: Vec::new(),
            backward_dependency_to_ancestor_individual_node: false,

            indi_model: Id::NONE,
            sat_cache_ret_data: Id::NONE,
            prev_sat_cache_ret_data: Id::NONE,
            sat_cache_storing_data: Id::NONE,
            prev_sat_cache_storing_data: Id::NONE,
            backend_sync_data: Id::NONE,
            prev_backend_sync_data: Id::NONE,

            processing_blocked_indi: Id::NONE,
            processing_blocked_individuals_linker: Vec::new(),

            sat_cached_absorbed_disjunctions_reapply_con_des: Id::NONE,
            sat_cached_absorbed_successor_reapply_con_des: Id::NONE,

            role_back_prop_hash: Id::NONE,
            indi_process_linker: Id::NONE,
            concept_process_linker: Id::NONE,
            required_back_prop: false,
            substitute_indi_node: Id::NONE,

            extended_queue_processing: false,
            immediately_processing_queued: false,
            det_exp_processing_queued: false,
            depth_processing_queued: false,
            blocked_react_processing_queued: false,
            backend_synchron_retest_processing_queued: false,
            backend_indirect_compatibility_expansion_queued: false,
            backend_direct_influence_expansion_queued: false,
            incremental_compatibility_checking_queued: false,
            incremental_expansion_queued: false,
            processing_queued: false,
            backend_reuse_expansion_queued: false,
            backend_neighbour_expansion_queued: false,
            last_processing_priority: IndividualProcessNodePriority::default(),

            delayed_nominal_processing_queued: false,
            nominal_processing_delaying_checked: false,
            assertion_initialisation_signature_value: 0,

            caching_loss_node_reactivation_installed: false,
            use_reactivation_data: Id::NONE,
            loc_reactivation_data: Id::NONE,
            use_succ_indi_atmost_reactivation_data: Id::NONE,
            loc_succ_indi_atmost_reactivation_data: Id::NONE,
            use_nominal_connection_set: Id::NONE,
            loc_nominal_connection_set: Id::NONE,
            use_datatypes_value_space_data: Id::NONE,
            loc_datatypes_value_space_data: Id::NONE,
            use_inc_exp_data: Id::NONE,
            loc_inc_exp_data: Id::NONE,
            inc_exp_id: 0,
            use_individual_merging_hash: Id::NONE,
            loc_individual_merging_hash: Id::NONE,

            merged_dep_track_point: Id::NONE,
            last_merged_into_individual_node: Id::NONE,
        }
    }
}

impl IndividualProcessNode {
    // ---- SIMPLE accessors (trivial getters/setters; complex logic deferred) --

    /// Port of `getIndividualNodeID`.
    pub fn individual_node_id(&self) -> Cint64 {
        self.indi_id
    }
    /// Port of `setIndividualNodeID`.
    // KONCLUDE-PORT-NOTE[unclear→resolved]: C++ guards the merge-into id so it
    // follows the node id when they were equal: `if (mMergeIntoID == mIndiID)
    // mMergeIntoID = indiID;` then `mIndiID = indiID;`. Must read old indi_id
    // before overwriting it.
    pub fn set_individual_node_id(&mut self, indi_id: Cint64) -> &mut Self {
        if self.merge_into_id == self.indi_id {
            self.merge_into_id = indi_id;
        }
        self.indi_id = indi_id;
        self
    }

    /// Port of `getIndividualType`.
    pub fn individual_type(&self) -> IndividualType {
        self.indi_type
    }
    /// Port of `setIndividualType`.
    pub fn set_individual_type(&mut self, indi_type: IndividualType) -> &mut Self {
        self.indi_type = indi_type;
        self
    }

    /// Port of `isBlockableIndividual`.
    pub fn is_blockable_individual(&self) -> bool {
        self.indi_type == IndividualType::Blockable
    }
    /// Port of `isNominalIndividualNode`.
    pub fn is_nominal_individual_node(&self) -> bool {
        self.indi_type == IndividualType::Nominal
    }

    /// Port of `getNominalIndividual`.
    pub fn nominal_individual(&self) -> IndividualId {
        self.nom_indi
    }
    /// Port of `setNominalIndividual`.
    pub fn set_nominal_individual(&mut self, indi: IndividualId) -> &mut Self {
        self.nom_indi = indi;
        self
    }

    /// Port of `getIndividualAncestorDepth`.
    pub fn individual_ancestor_depth(&self) -> Cint64 {
        self.indi_anc_depth
    }
    /// Port of `setIndividualAncestorDepth`.
    pub fn set_individual_ancestor_depth(&mut self, depth: Cint64) -> &mut Self {
        self.indi_anc_depth = depth;
        self
    }

    /// Port of `getIndividualNominalLevel`.
    pub fn individual_nominal_level(&self) -> Cint64 {
        self.nominal_level
    }
    /// Port of `setIndividualNominalLevel`.
    pub fn set_individual_nominal_level(&mut self, level: Cint64) -> &mut Self {
        self.nominal_level = level;
        self
    }

    /// Port of `getMergedIntoIndividualNodeID`.
    pub fn merged_into_individual_node_id(&self) -> Cint64 {
        self.merge_into_id
    }
    /// Port of `hasMergedIntoIndividualNodeID`.
    // KONCLUDE-PORT-NOTE[unclear→resolved]: C++ (CIndividualProcessNode.cpp
    // ~1483) returns `mMergeIntoID != mIndiID`, NOT `!= 0`.
    pub fn has_merged_into_individual_node_id(&self) -> bool {
        self.merge_into_id != self.indi_id
    }
    /// Port of `setMergedIntoIndividualNodeID`.
    pub fn set_merged_into_individual_node_id(&mut self, indi_node_id: Cint64) -> &mut Self {
        self.merge_into_id = indi_node_id;
        self
    }

    /// Port of `getProcessingRestrictionFlags`.
    pub fn processing_restriction_flags(&self) -> Cint64 {
        self.processing_restriction_flags
    }
    /// Port of `hasProcessingRestrictionFlags` (all `test_flags` set).
    pub fn has_processing_restriction_flags(&self, test_flags: Cint64) -> bool {
        (self.processing_restriction_flags & test_flags) == test_flags
    }
    /// Port of `hasPartialProcessingRestrictionFlags` (any `test_flags` set).
    pub fn has_partial_processing_restriction_flags(&self, test_flags: Cint64) -> bool {
        (self.processing_restriction_flags & test_flags) != 0
    }

    /// Port of `isRelocalized` (`CLocalizationTag`).
    pub fn is_relocalized(&self) -> bool {
        self.relocalized
    }

    /// Port of `getDependencyTrackPoint` (`CDependencyTracker`).
    pub fn dependency_track_point(&self) -> TrackPointId {
        self.dep_track_point
    }
    /// Port of `setDependencyTrackPoint` (`CDependencyTracker`).
    pub fn set_dependency_track_point(&mut self, dep_track_point: TrackPointId) -> &mut Self {
        self.dep_track_point = dep_track_point;
        self
    }
}
