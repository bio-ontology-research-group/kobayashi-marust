//! `process/databox.rs` — SD-2: the per-satisfiability-test ambient state box.
//!
//! Port of Konclude `Source/Reasoner/Kernel/Process/CProcessingDataBox.{h,cpp}`
//! (the `.h` field block 565–875, 208 declared members). This unit ports the
//! **struct definition + `new`/`Default` + the simple getters/setters only**.
//! The 265 stateful methods (lazy-alloc `getX(create)`, the triple-buffer
//! save/restore handoff in `initProcessingDataBox`, the take/add work-queue
//! linker ops, the id-counter increments) are deferred to the method-batch units
//! DB-1..DB-6 — see `manifest/05-process-units.md`. Each such site is left with a
//! `// W2 method-batch: DB-n` marker.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::super::model::ConceptId;
use super::{BranchInstrId, ClashDescId, ConDescId, ConProcDescId, NodeId, SatNodeId};

// KONCLUDE-PORT-NOTE[ownership]: Konclude holds each container/queue/hash/payload
// below by a pool-allocated `CXxx*`; per the global substrate decision they become
// `Id<T>` into a per-test arena (`Id::NONE` == `nullptr`). The bodies are their own
// later port units; here they are the shared zero-size marker stubs from
// `process::stubs` (`ConceptSaturationDescriptor` is shared with `sat_node`).
use super::stubs::{
    BackendNeighbourExpansionControllingData, BackendNeighbourExpansionQueue,
    BlockingIndividualNodeLinkedCandidateHash, BranchingTree,
    ConceptNominalSchemaGroundingHash, ConceptSaturationDescriptor, ConceptSaturationProcess,
    ConceptVector, CriticalIndividualNodeConceptTestSet, CriticalIndividualNodeProcessingQueue,
    IndividualConceptBatchProcessingQueue, IndividualCustomPriorityProcessingQueue,
    IndividualDelayedBackendInitializationProcessingQueue, IndividualDepthProcessingQueue,
    IndividualLinkerRotationProcessingQueue, IndividualProcessingQueue,
    IndividualReactivationProcessingQueue,
    IndividualRepresentativeBackendCacheConceptSetLabelProcessingHash,
    IndividualRepresentativeBackendCacheLoadedAssociationHash,
    IndividualSaturationProcessNodeVector, IndividualSaturationSuccessorLinkData,
    IndividualUnsortedProcessingQueue, IndividualVector, MarkerIndividualNodeHash,
    NodeSwitchHistory, NominalCachingLossReactivationHash, ReferredIndividualTrackingVector,
    RepresentativeJoiningHash, RepresentativeVariableBindingPathHash,
    RepresentativeVariableBindingPathJoiningKeyHash, RepresentativeVariableBindingPathSetHash,
    ReusingReviewData, RoleSaturationProcess, SaturationInfluencedNominalSet,
    SaturationNominalDependentNodeHash, SaturationSuccessorExtensionIndividualNodeProcessingQueue,
    SignatureBlockingReviewSet, VariableBindingPathMergingHash,
};
// `CIndividualProcessNodeVector` is a real ported type (node-resolution keystone),
// held BY VALUE on the databox rather than as an `Id<stub>`.
use super::node_resolution::IndividualProcessNodeVector;
// W3.5b/W2.7 reconcile: the blocking-candidate hashes are real ported structs; the
// databox holds `Id<…>` into their arenas (un-wired from the `stubs` markers).
use super::blocking_hash::BlockingIndividualNodeCandidateHash;
use super::reapply_sat::SignatureBlockingCandidateHash;

/// Port of `CProcessingDataBox`.
///
/// The completion engine's per-test mutable state: every processing queue, the
/// blocking/saturation/backend bookkeeping, and the id counters. Field order
/// mirrors the C++ `.h` (565–875) for method-by-method diffability.
///
/// KONCLUDE-PORT-NOTE[ownership]: the 36 `mX`/`mUseX`/`mPrevX` triple-buffer
/// slots and the 14 `mLocX`/`mUseX` loc/use pairs are kept as the explicit
/// current/working/previous (resp. local/use) `Id` fields the C++ has. The save
/// /restore semantics (which alias holds the live object, which is the parent's,
/// which is the snapshot to rewind to on backtrack) are realised by the
/// `initProcessingDataBox(parent)` handoff in DB-1, NOT by this struct shape:
/// here they are three plain ids that may legally hold the same value.
pub struct ProcessingDataBox {
    // --- ontology / context singletons (.h 565–571) ---
    /// KONCLUDE-PORT-NOTE[ownership]: `CProcessContext*` back-pointer to the
    /// ambient owner of every arena; the process context is the `&mut` state
    /// threaded through the methods, not an arena element, so it is kept as an
    /// opaque `Cint64` handle rather than an `Id`.
    pub process_context: Cint64,
    pub ontology_top_concept: ConceptId,
    pub ontology_top_data_range_concept: ConceptId,
    /// KONCLUDE-PORT-NOTE[api]: `CConcreteOntology*` lives in a not-yet-ported
    /// upstream layer; kept as an opaque `Cint64` handle for now.
    pub ontology: Cint64,
    pub clashed_descriptor_linker: ClashDescId,

    // --- loc/use pair 1: individual vector (.h 573–574) ---
    pub local_indi_vector: Id<IndividualVector>,
    pub use_indi_vector: Id<IndividualVector>,

    // --- loc/use pair 2: individual processing queue (.h 576–577) ---
    pub use_indi_process_queue: Id<IndividualProcessingQueue>,
    pub loc_indi_process_queue: Id<IndividualProcessingQueue>,

    /// individual-process-node vector (.h 578). `mIndiProcessVector`: the per-test
    /// map from individual node id → current node. Held BY VALUE (real ported type).
    pub indi_process_vector: IndividualProcessNodeVector,

    // --- triple-buffered processing queues (.h 580–697) ---
    pub indi_imm_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub use_indi_imm_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub prev_indi_imm_process_queue: Id<IndividualUnsortedProcessingQueue>,

    pub delay_nom_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub use_delay_nom_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub prev_delay_nom_process_queue: Id<IndividualUnsortedProcessingQueue>,

    pub role_assertion_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub use_role_assertion_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub prev_role_assertion_process_queue: Id<IndividualUnsortedProcessingQueue>,

    pub backend_sync_retest_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub use_backend_sync_retest_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub prev_backend_sync_retest_process_queue: Id<IndividualUnsortedProcessingQueue>,

    pub backend_indirect_compatibility_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub use_backend_indirect_compatibility_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub prev_backend_indirect_compatibility_expansion_queue: Id<IndividualUnsortedProcessingQueue>,

    pub backend_individual_reuse_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub use_backend_individual_reuse_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub prev_backend_individual_reuse_expansion_queue: Id<IndividualUnsortedProcessingQueue>,

    /// (.h 608) sits inside the queue block in C++.
    pub backend_individual_late_reuse_expansion_activated: bool,
    pub backend_late_individual_reuse_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub use_backend_late_individual_reuse_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub prev_backend_late_individual_reuse_expansion_queue: Id<IndividualUnsortedProcessingQueue>,

    pub backend_individual_neighbour_expansion_queue: Id<IndividualLinkerRotationProcessingQueue>,
    pub use_backend_individual_neighbour_expansion_queue: Id<IndividualLinkerRotationProcessingQueue>,
    pub prev_backend_individual_neighbour_expansion_queue: Id<IndividualLinkerRotationProcessingQueue>,

    pub backend_direct_influence_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub use_backend_direct_influence_expansion_queue: Id<IndividualUnsortedProcessingQueue>,
    pub prev_backend_direct_influence_expansion_queue: Id<IndividualUnsortedProcessingQueue>,

    pub indi_depth_det_exp_pre_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub use_indi_depth_det_exp_pre_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub prev_indi_depth_det_exp_pre_processing_queue: Id<IndividualDepthProcessingQueue>,

    pub indi_depth_first_det_exp_pre_processing_queue: Id<IndividualUnsortedProcessingQueue>,
    pub use_indi_depth_first_det_exp_pre_processing_queue: Id<IndividualUnsortedProcessingQueue>,
    pub prev_indi_depth_first_det_exp_pre_processing_queue: Id<IndividualUnsortedProcessingQueue>,

    pub var_bind_concept_batch_process_queue: Id<IndividualConceptBatchProcessingQueue>,
    pub use_var_bind_concept_batch_process_queue: Id<IndividualConceptBatchProcessingQueue>,
    pub prev_var_bind_concept_batch_process_queue: Id<IndividualConceptBatchProcessingQueue>,

    pub indi_depth_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub use_indi_depth_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub prev_indi_depth_processing_queue: Id<IndividualDepthProcessingQueue>,

    pub nominal_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub use_nominal_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub prev_nominal_processing_queue: Id<IndividualDepthProcessingQueue>,

    pub nominal_deterministic_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub use_nominal_deterministic_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub prev_nominal_deterministic_processing_queue: Id<IndividualDepthProcessingQueue>,

    pub indi_depth_first_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub use_indi_depth_first_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub prev_indi_depth_first_process_queue: Id<IndividualUnsortedProcessingQueue>,

    pub caching_loss_reactivation_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub use_caching_loss_reactivation_process_queue: Id<IndividualUnsortedProcessingQueue>,
    pub prev_caching_loss_reactivation_process_queue: Id<IndividualUnsortedProcessingQueue>,

    pub indi_signature_blocking_update_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub use_indi_signature_blocking_update_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub prev_indi_signature_blocking_update_processing_queue: Id<IndividualDepthProcessingQueue>,

    pub indi_blocked_reactivation_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub use_indi_blocked_reactivation_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub prev_indi_blocked_reactivation_processing_queue: Id<IndividualDepthProcessingQueue>,

    pub value_space_triggering_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub use_value_space_triggering_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub prev_value_space_triggering_processing_queue: Id<IndividualDepthProcessingQueue>,

    pub distinct_value_space_satisfiability_checking_queue: Id<IndividualDepthProcessingQueue>,
    pub use_distinct_value_space_satisfiability_checking_queue: Id<IndividualDepthProcessingQueue>,
    pub prev_distinct_value_space_satisfiability_checking_queue: Id<IndividualDepthProcessingQueue>,

    pub incremental_exansion_initializing_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub use_incremental_exansion_initializing_processing_queue: Id<IndividualDepthProcessingQueue>,
    pub prev_incremental_exansion_initializing_processing_queue: Id<IndividualDepthProcessingQueue>,

    pub incremental_exansion_processing_queue: Id<IndividualCustomPriorityProcessingQueue>,
    pub use_incremental_exansion_processing_queue: Id<IndividualCustomPriorityProcessingQueue>,
    pub prev_incremental_exansion_processing_queue: Id<IndividualCustomPriorityProcessingQueue>,

    pub incremental_compatibility_checking_queue: Id<IndividualDepthProcessingQueue>,
    pub use_incremental_compatibility_checking_queue: Id<IndividualDepthProcessingQueue>,
    pub prev_incremental_compatibility_checking_queue: Id<IndividualDepthProcessingQueue>,

    // --- triple-buffered hashes / review-sets / history / tree (.h 701–743) ---
    pub signature_blocking_candidate_hash: Id<SignatureBlockingCandidateHash>,
    pub use_signature_blocking_candidate_hash: Id<SignatureBlockingCandidateHash>,
    pub prev_signature_blocking_candidate_hash: Id<SignatureBlockingCandidateHash>,

    pub signature_blocking_review_set: Id<SignatureBlockingReviewSet>,
    pub use_signature_blocking_review_set: Id<SignatureBlockingReviewSet>,
    pub prev_signature_blocking_review_set: Id<SignatureBlockingReviewSet>,

    pub signature_nominal_delaying_candidate_hash: Id<SignatureBlockingCandidateHash>,
    pub use_signature_nominal_delaying_candidate_hash: Id<SignatureBlockingCandidateHash>,
    pub prev_signature_nominal_delaying_candidate_hash: Id<SignatureBlockingCandidateHash>,

    pub early_indi_react_pro_queue: Id<IndividualReactivationProcessingQueue>,
    pub use_early_indi_react_pro_queue: Id<IndividualReactivationProcessingQueue>,
    pub prev_early_indi_react_pro_queue: Id<IndividualReactivationProcessingQueue>,

    pub late_indi_react_pro_queue: Id<IndividualReactivationProcessingQueue>,
    pub use_late_indi_react_pro_queue: Id<IndividualReactivationProcessingQueue>,
    pub prev_late_indi_react_pro_queue: Id<IndividualReactivationProcessingQueue>,

    pub reusing_review_set: Id<ReusingReviewData>,
    pub use_reusing_review_set: Id<ReusingReviewData>,
    pub prev_reusing_review_set: Id<ReusingReviewData>,

    /// (.h 727) sits inside the hash block in C++.
    pub branching_instruction: BranchInstrId,

    pub blocking_indi_node_candidate_hash: Id<BlockingIndividualNodeCandidateHash>,
    pub use_blocking_indi_node_candidate_hash: Id<BlockingIndividualNodeCandidateHash>,
    pub prev_blocking_indi_node_candidate_hash: Id<BlockingIndividualNodeCandidateHash>,

    pub blocking_indi_node_linked_candidate_hash: Id<BlockingIndividualNodeLinkedCandidateHash>,
    pub use_blocking_indi_node_linked_candidate_hash: Id<BlockingIndividualNodeLinkedCandidateHash>,
    pub prev_blocking_indi_node_linked_candidate_hash: Id<BlockingIndividualNodeLinkedCandidateHash>,

    pub node_switch_history: Id<NodeSwitchHistory>,
    pub use_node_switch_history: Id<NodeSwitchHistory>,
    pub prev_node_switch_history: Id<NodeSwitchHistory>,

    pub branching_tree: Id<BranchingTree>,
    pub use_branching_tree: Id<BranchingTree>,
    pub prev_branching_tree: Id<BranchingTree>,

    // --- loc/use pair 3: extended concept vector (.h 745–746) ---
    pub loc_extended_concept_vector: Id<ConceptVector>,
    pub use_extended_concept_vector: Id<ConceptVector>,

    // --- loc/use pair 4: grounding hash (.h 748–749) ---
    pub loc_grounding_hash: Id<ConceptNominalSchemaGroundingHash>,
    pub use_grounding_hash: Id<ConceptNominalSchemaGroundingHash>,

    // --- construction / last-processing bookkeeping (.h 751–758) ---
    pub multiple_construction_indi_nodes: bool,
    pub constructed_indi_node: NodeId,
    pub constructed_indi_node_initialized: bool,
    pub maximum_deterministic_branch_tag: Cint64,
    pub last_processing_indi_node: NodeId,
    pub last_processing_con_des: ConProcDescId,
    pub last_con_des_indi_reapplication: bool,

    // --- node-linker work queues (.h 761–797) ---
    // KONCLUDE-PORT-NOTE[ownership]: intrusive `CXLinker`/`C*Linker` chain heads
    // become owned `Vec`s of the element id (the work-queue convention). `take*`
    // == `std::mem::take`, `add*` == `push`.
    pub sorted_nominal_non_det_processing_node_linker: Vec<NodeId>,
    pub sorted_nominal_non_det_processing_nodes_sorted: bool,
    pub nominal_non_det_processing_count: Cint64,
    pub individual_node_cache_testing_linker: Vec<NodeId>,
    pub indi_process_node_linker: Vec<NodeId>,

    // --- saturation linkers / vectors / sets (.h 770–797) ---
    pub disjunct_common_concept_extract_processing_linker: Vec<SatNodeId>,
    pub indi_saturation_process_node_linker: Vec<SatNodeId>,
    pub indi_saturation_completion_node_linker: Vec<SatNodeId>,
    pub indi_saturation_completed_node_linker: Vec<SatNodeId>,
    pub indi_saturation_analysing_node_linker: Vec<SatNodeId>,
    pub indi_saturation_process_vector: Id<IndividualSaturationProcessNodeVector>,
    /// KONCLUDE-PORT-NOTE[ownership]: status-update linker; per-element status
    /// payload is deferred to DB-5, here just the sat-node chain.
    pub rem_sat_update_linker: Vec<SatNodeId>,
    pub rem_sat_indi_node_linker: Vec<SatNodeId>,
    pub rem_sat_indi_succ_link_data_linker: Vec<Id<IndividualSaturationSuccessorLinkData>>,
    pub rem_con_sat_process_linker: Vec<Id<ConceptSaturationProcess>>,
    pub rem_role_sat_process_linker: Vec<Id<RoleSaturationProcess>>,
    pub rem_con_sat_des: Vec<Id<ConceptSaturationDescriptor>>,
    pub rem_con_des: Vec<ConDescId>,
    pub sat_critical_indi_node_proc_queue: Id<CriticalIndividualNodeProcessingQueue>,
    pub sat_critical_indi_node_con_test_set: Id<CriticalIndividualNodeConceptTestSet>,
    pub sat_nominal_dependent_node_hash: Id<SaturationNominalDependentNodeHash>,
    pub sat_influenced_nominal_set: Id<SaturationInfluencedNominalSet>,
    pub insufficient_node_occured: bool,
    pub delayed_nominal_processing_occured: bool,
    pub problematic_eq_candidate_node_occured: bool,
    pub sat_succ_ext_ind_node_proc_queue: Id<SaturationSuccessorExtensionIndividualNodeProcessingQueue>,
    pub nominal_delayed_indi_saturation_process_node_linker: Vec<SatNodeId>,
    pub saturation_atmost_merging_process_linker: Vec<SatNodeId>,
    pub separated_saturation_con_ass_resolve_node: SatNodeId,
    pub individual_node_resolve_linker: Vec<NodeId>,
    pub blockable_individual_node_updated_linker: Vec<NodeId>,

    // --- id counters (.h 799–803) ---
    pub next_sat_res_succ_ext_individual_node_id: Cint64,
    pub next_individual_node_id: Cint64,
    pub next_propagation_id: Cint64,
    pub next_variable_id: Cint64,
    pub next_rep_variable_id: Cint64,

    // --- loc/use pairs 5–11: rep-binding / nominal / marker hashes (.h 805–826) ---
    pub use_var_binding_path_merging_hash: Id<VariableBindingPathMergingHash>,
    pub loc_var_binding_path_merging_hash: Id<VariableBindingPathMergingHash>,

    pub use_rep_var_bind_path_set_hash: Id<RepresentativeVariableBindingPathSetHash>,
    pub loc_rep_var_bind_path_set_hash: Id<RepresentativeVariableBindingPathSetHash>,

    pub use_rep_var_bind_path_joining_key_hash: Id<RepresentativeVariableBindingPathJoiningKeyHash>,
    pub loc_rep_var_bind_path_joining_key_hash: Id<RepresentativeVariableBindingPathJoiningKeyHash>,

    pub use_rep_joining_hash: Id<RepresentativeJoiningHash>,
    pub loc_rep_joining_hash: Id<RepresentativeJoiningHash>,

    pub use_rep_var_bind_path_hash: Id<RepresentativeVariableBindingPathHash>,
    pub loc_rep_var_bind_path_hash: Id<RepresentativeVariableBindingPathHash>,

    pub use_nom_caching_loss_react_hash: Id<NominalCachingLossReactivationHash>,
    pub loc_nom_caching_loss_react_hash: Id<NominalCachingLossReactivationHash>,

    pub use_marker_indi_node_hash: Id<MarkerIndividualNodeHash>,
    pub loc_marker_indi_node_hash: Id<MarkerIndividualNodeHash>,

    // --- incremental expansion (.h 829–834) ---
    pub incremental_expansion_initialized: bool,
    pub next_incremental_indi_exp_id: Cint64,
    pub incremental_exp_id: Cint64,
    pub incremental_expansion_compatible_merged: bool,
    pub incremental_expansion_caching_merged: bool,
    pub max_inc_prev_comp_graph_node_id: Cint64,

    /// (.h 837)
    pub next_role_assertion_creation_id: Cint64,

    // --- referred-individual tracking (.h 840–841) ---
    pub referred_indi_track_vec: Id<ReferredIndividualTrackingVector>,
    pub indi_dep_tracking_required: bool,

    // --- possible-instance merging (.h 843–849) ---
    /// `CXLinker<CXLinker<cint64>*>*` → list of linker-lists.
    pub current_merged_possible_instance_individual_linkers_linker: Vec<Vec<Cint64>>,
    /// `CXLinker<cint64>*`
    pub last_merged_possible_instance_individual_linker: Vec<Cint64>,
    pub remaining_possible_instance_individual_merging_limit: Cint64,
    pub possible_instance_individual_current_merging_count: Cint64,
    pub possible_instance_individual_merged_count: Cint64,
    pub possible_instance_individual_merging_size: Cint64,
    pub possible_instance_individual_merging_stopped: bool,

    // --- backend cache misc (.h 852–875) ---
    pub last_backend_cache_integrated_indi_node_linker: Vec<NodeId>,
    pub backend_cache_integrated_individual_node_count: Cint64,
    pub backend_cache_integrated_same_individual_node_count: Cint64,

    // loc/use pair 12
    pub use_backend_loaded_association_hash: Id<IndividualRepresentativeBackendCacheLoadedAssociationHash>,
    pub loc_backend_loaded_association_hash: Id<IndividualRepresentativeBackendCacheLoadedAssociationHash>,

    // loc/use pair 13
    pub use_backend_concept_set_label_processing_hash:
        Id<IndividualRepresentativeBackendCacheConceptSetLabelProcessingHash>,
    pub loc_backend_concept_set_label_processing_hash:
        Id<IndividualRepresentativeBackendCacheConceptSetLabelProcessingHash>,

    // triple-buffered queue (.h 861–863)
    pub delayed_backend_init_proc_queue: Id<IndividualDelayedBackendInitializationProcessingQueue>,
    pub use_delayed_backend_init_proc_queue: Id<IndividualDelayedBackendInitializationProcessingQueue>,
    pub prev_delayed_backend_init_proc_queue: Id<IndividualDelayedBackendInitializationProcessingQueue>,

    // loc/use pair 14
    pub use_backend_neighbour_expansion_controlling_data: Id<BackendNeighbourExpansionControllingData>,
    pub loc_backend_neighbour_expansion_controlling_data: Id<BackendNeighbourExpansionControllingData>,

    // triple-buffered queue (.h 869–871; note the C++ Use/Prev names drop "Queue")
    pub backend_neighbour_expansion_queue: Id<BackendNeighbourExpansionQueue>,
    pub use_backend_neighbour_expansion: Id<BackendNeighbourExpansionQueue>,
    pub prev_backend_neighbour_expansion: Id<BackendNeighbourExpansionQueue>,

    pub backend_cache_update_individuals_initialized: bool,
    pub representative_neighbour_expansion_individual_node_linker: Vec<NodeId>,
}

impl ProcessingDataBox {
    /// Port of `CProcessingDataBox::CProcessingDataBox`.
    ///
    /// KONCLUDE-PORT-NOTE[uninit]: the C++ ctor leaves most pointers `nullptr`
    /// and seeds a few id counters; the real seed values are installed by
    /// `initProcessingDataBox` (DB-1). Here every slot starts empty
    /// (`Id::NONE` / `false` / `0` / empty `Vec`); DB-1 sets the live values.
    pub fn new() -> Self {
        ProcessingDataBox {
            process_context: Id::<()>::NONE.raw,
            ontology_top_concept: ConceptId::NONE,
            ontology_top_data_range_concept: ConceptId::NONE,
            ontology: Id::<()>::NONE.raw,
            clashed_descriptor_linker: ClashDescId::NONE,

            local_indi_vector: Id::NONE,
            use_indi_vector: Id::NONE,
            use_indi_process_queue: Id::NONE,
            loc_indi_process_queue: Id::NONE,
            indi_process_vector: IndividualProcessNodeVector::new(),

            indi_imm_process_queue: Id::NONE,
            use_indi_imm_process_queue: Id::NONE,
            prev_indi_imm_process_queue: Id::NONE,
            delay_nom_process_queue: Id::NONE,
            use_delay_nom_process_queue: Id::NONE,
            prev_delay_nom_process_queue: Id::NONE,
            role_assertion_process_queue: Id::NONE,
            use_role_assertion_process_queue: Id::NONE,
            prev_role_assertion_process_queue: Id::NONE,
            backend_sync_retest_process_queue: Id::NONE,
            use_backend_sync_retest_process_queue: Id::NONE,
            prev_backend_sync_retest_process_queue: Id::NONE,
            backend_indirect_compatibility_expansion_queue: Id::NONE,
            use_backend_indirect_compatibility_expansion_queue: Id::NONE,
            prev_backend_indirect_compatibility_expansion_queue: Id::NONE,
            backend_individual_reuse_expansion_queue: Id::NONE,
            use_backend_individual_reuse_expansion_queue: Id::NONE,
            prev_backend_individual_reuse_expansion_queue: Id::NONE,
            backend_individual_late_reuse_expansion_activated: false,
            backend_late_individual_reuse_expansion_queue: Id::NONE,
            use_backend_late_individual_reuse_expansion_queue: Id::NONE,
            prev_backend_late_individual_reuse_expansion_queue: Id::NONE,
            backend_individual_neighbour_expansion_queue: Id::NONE,
            use_backend_individual_neighbour_expansion_queue: Id::NONE,
            prev_backend_individual_neighbour_expansion_queue: Id::NONE,
            backend_direct_influence_expansion_queue: Id::NONE,
            use_backend_direct_influence_expansion_queue: Id::NONE,
            prev_backend_direct_influence_expansion_queue: Id::NONE,
            indi_depth_det_exp_pre_processing_queue: Id::NONE,
            use_indi_depth_det_exp_pre_processing_queue: Id::NONE,
            prev_indi_depth_det_exp_pre_processing_queue: Id::NONE,
            indi_depth_first_det_exp_pre_processing_queue: Id::NONE,
            use_indi_depth_first_det_exp_pre_processing_queue: Id::NONE,
            prev_indi_depth_first_det_exp_pre_processing_queue: Id::NONE,
            var_bind_concept_batch_process_queue: Id::NONE,
            use_var_bind_concept_batch_process_queue: Id::NONE,
            prev_var_bind_concept_batch_process_queue: Id::NONE,
            indi_depth_processing_queue: Id::NONE,
            use_indi_depth_processing_queue: Id::NONE,
            prev_indi_depth_processing_queue: Id::NONE,
            nominal_processing_queue: Id::NONE,
            use_nominal_processing_queue: Id::NONE,
            prev_nominal_processing_queue: Id::NONE,
            nominal_deterministic_processing_queue: Id::NONE,
            use_nominal_deterministic_processing_queue: Id::NONE,
            prev_nominal_deterministic_processing_queue: Id::NONE,
            indi_depth_first_process_queue: Id::NONE,
            use_indi_depth_first_process_queue: Id::NONE,
            prev_indi_depth_first_process_queue: Id::NONE,
            caching_loss_reactivation_process_queue: Id::NONE,
            use_caching_loss_reactivation_process_queue: Id::NONE,
            prev_caching_loss_reactivation_process_queue: Id::NONE,
            indi_signature_blocking_update_processing_queue: Id::NONE,
            use_indi_signature_blocking_update_processing_queue: Id::NONE,
            prev_indi_signature_blocking_update_processing_queue: Id::NONE,
            indi_blocked_reactivation_processing_queue: Id::NONE,
            use_indi_blocked_reactivation_processing_queue: Id::NONE,
            prev_indi_blocked_reactivation_processing_queue: Id::NONE,
            value_space_triggering_processing_queue: Id::NONE,
            use_value_space_triggering_processing_queue: Id::NONE,
            prev_value_space_triggering_processing_queue: Id::NONE,
            distinct_value_space_satisfiability_checking_queue: Id::NONE,
            use_distinct_value_space_satisfiability_checking_queue: Id::NONE,
            prev_distinct_value_space_satisfiability_checking_queue: Id::NONE,
            incremental_exansion_initializing_processing_queue: Id::NONE,
            use_incremental_exansion_initializing_processing_queue: Id::NONE,
            prev_incremental_exansion_initializing_processing_queue: Id::NONE,
            incremental_exansion_processing_queue: Id::NONE,
            use_incremental_exansion_processing_queue: Id::NONE,
            prev_incremental_exansion_processing_queue: Id::NONE,
            incremental_compatibility_checking_queue: Id::NONE,
            use_incremental_compatibility_checking_queue: Id::NONE,
            prev_incremental_compatibility_checking_queue: Id::NONE,

            signature_blocking_candidate_hash: Id::NONE,
            use_signature_blocking_candidate_hash: Id::NONE,
            prev_signature_blocking_candidate_hash: Id::NONE,
            signature_blocking_review_set: Id::NONE,
            use_signature_blocking_review_set: Id::NONE,
            prev_signature_blocking_review_set: Id::NONE,
            signature_nominal_delaying_candidate_hash: Id::NONE,
            use_signature_nominal_delaying_candidate_hash: Id::NONE,
            prev_signature_nominal_delaying_candidate_hash: Id::NONE,
            early_indi_react_pro_queue: Id::NONE,
            use_early_indi_react_pro_queue: Id::NONE,
            prev_early_indi_react_pro_queue: Id::NONE,
            late_indi_react_pro_queue: Id::NONE,
            use_late_indi_react_pro_queue: Id::NONE,
            prev_late_indi_react_pro_queue: Id::NONE,
            reusing_review_set: Id::NONE,
            use_reusing_review_set: Id::NONE,
            prev_reusing_review_set: Id::NONE,
            branching_instruction: BranchInstrId::NONE,
            blocking_indi_node_candidate_hash: Id::NONE,
            use_blocking_indi_node_candidate_hash: Id::NONE,
            prev_blocking_indi_node_candidate_hash: Id::NONE,
            blocking_indi_node_linked_candidate_hash: Id::NONE,
            use_blocking_indi_node_linked_candidate_hash: Id::NONE,
            prev_blocking_indi_node_linked_candidate_hash: Id::NONE,
            node_switch_history: Id::NONE,
            use_node_switch_history: Id::NONE,
            prev_node_switch_history: Id::NONE,
            branching_tree: Id::NONE,
            use_branching_tree: Id::NONE,
            prev_branching_tree: Id::NONE,

            loc_extended_concept_vector: Id::NONE,
            use_extended_concept_vector: Id::NONE,
            loc_grounding_hash: Id::NONE,
            use_grounding_hash: Id::NONE,

            multiple_construction_indi_nodes: false,
            constructed_indi_node: NodeId::NONE,
            constructed_indi_node_initialized: false,
            maximum_deterministic_branch_tag: 0,
            last_processing_indi_node: NodeId::NONE,
            last_processing_con_des: ConProcDescId::NONE,
            last_con_des_indi_reapplication: false,

            sorted_nominal_non_det_processing_node_linker: Vec::new(),
            sorted_nominal_non_det_processing_nodes_sorted: false,
            nominal_non_det_processing_count: 0,
            individual_node_cache_testing_linker: Vec::new(),
            indi_process_node_linker: Vec::new(),

            disjunct_common_concept_extract_processing_linker: Vec::new(),
            indi_saturation_process_node_linker: Vec::new(),
            indi_saturation_completion_node_linker: Vec::new(),
            indi_saturation_completed_node_linker: Vec::new(),
            indi_saturation_analysing_node_linker: Vec::new(),
            indi_saturation_process_vector: Id::NONE,
            rem_sat_update_linker: Vec::new(),
            rem_sat_indi_node_linker: Vec::new(),
            rem_sat_indi_succ_link_data_linker: Vec::new(),
            rem_con_sat_process_linker: Vec::new(),
            rem_role_sat_process_linker: Vec::new(),
            rem_con_sat_des: Vec::new(),
            rem_con_des: Vec::new(),
            sat_critical_indi_node_proc_queue: Id::NONE,
            sat_critical_indi_node_con_test_set: Id::NONE,
            sat_nominal_dependent_node_hash: Id::NONE,
            sat_influenced_nominal_set: Id::NONE,
            insufficient_node_occured: false,
            delayed_nominal_processing_occured: false,
            problematic_eq_candidate_node_occured: false,
            sat_succ_ext_ind_node_proc_queue: Id::NONE,
            nominal_delayed_indi_saturation_process_node_linker: Vec::new(),
            saturation_atmost_merging_process_linker: Vec::new(),
            separated_saturation_con_ass_resolve_node: SatNodeId::NONE,
            individual_node_resolve_linker: Vec::new(),
            blockable_individual_node_updated_linker: Vec::new(),

            next_sat_res_succ_ext_individual_node_id: 0,
            next_individual_node_id: 0,
            next_propagation_id: 0,
            next_variable_id: 0,
            next_rep_variable_id: 0,

            use_var_binding_path_merging_hash: Id::NONE,
            loc_var_binding_path_merging_hash: Id::NONE,
            use_rep_var_bind_path_set_hash: Id::NONE,
            loc_rep_var_bind_path_set_hash: Id::NONE,
            use_rep_var_bind_path_joining_key_hash: Id::NONE,
            loc_rep_var_bind_path_joining_key_hash: Id::NONE,
            use_rep_joining_hash: Id::NONE,
            loc_rep_joining_hash: Id::NONE,
            use_rep_var_bind_path_hash: Id::NONE,
            loc_rep_var_bind_path_hash: Id::NONE,
            use_nom_caching_loss_react_hash: Id::NONE,
            loc_nom_caching_loss_react_hash: Id::NONE,
            use_marker_indi_node_hash: Id::NONE,
            loc_marker_indi_node_hash: Id::NONE,

            incremental_expansion_initialized: false,
            next_incremental_indi_exp_id: 0,
            incremental_exp_id: 0,
            incremental_expansion_compatible_merged: false,
            incremental_expansion_caching_merged: false,
            max_inc_prev_comp_graph_node_id: 0,

            next_role_assertion_creation_id: 0,

            referred_indi_track_vec: Id::NONE,
            indi_dep_tracking_required: false,

            current_merged_possible_instance_individual_linkers_linker: Vec::new(),
            last_merged_possible_instance_individual_linker: Vec::new(),
            remaining_possible_instance_individual_merging_limit: 0,
            possible_instance_individual_current_merging_count: 0,
            possible_instance_individual_merged_count: 0,
            possible_instance_individual_merging_size: 0,
            possible_instance_individual_merging_stopped: false,

            last_backend_cache_integrated_indi_node_linker: Vec::new(),
            backend_cache_integrated_individual_node_count: 0,
            backend_cache_integrated_same_individual_node_count: 0,
            use_backend_loaded_association_hash: Id::NONE,
            loc_backend_loaded_association_hash: Id::NONE,
            use_backend_concept_set_label_processing_hash: Id::NONE,
            loc_backend_concept_set_label_processing_hash: Id::NONE,
            delayed_backend_init_proc_queue: Id::NONE,
            use_delayed_backend_init_proc_queue: Id::NONE,
            prev_delayed_backend_init_proc_queue: Id::NONE,
            use_backend_neighbour_expansion_controlling_data: Id::NONE,
            loc_backend_neighbour_expansion_controlling_data: Id::NONE,
            backend_neighbour_expansion_queue: Id::NONE,
            use_backend_neighbour_expansion: Id::NONE,
            prev_backend_neighbour_expansion: Id::NONE,
            backend_cache_update_individuals_initialized: false,
            representative_neighbour_expansion_individual_node_linker: Vec::new(),
        }
    }

    // ----------------------------------------------------------------------
    // Simple getters / setters (trivial field access). Every method with
    // lazy-alloc (`getX(create)`), id-increment, take/add work-queue, or the
    // triple-buffer save/restore handoff is deferred.
    //
    // W2 method-batch: DB-1 (lifecycle / save-restore: ctor + initProcessingDataBox)
    // W2 method-batch: DB-2 (localised getters + id counters + indi-queue/vector accessors)
    // W2 method-batch: DB-3 (triple-buffered queue get/clear pairs)
    // W2 method-batch: DB-4 (blocking/reactivation hashes + node-linker take/add + construction state)
    // W2 method-batch: DB-5 (saturation subsystem linkers / sets / occurred flags)
    // W2 method-batch: DB-6 (incremental / possible-instance merging / backend-cache / branching instruction)
    // ----------------------------------------------------------------------

    /// Port of `getOntologyTopConcept`.
    pub fn ontology_top_concept(&self) -> ConceptId { self.ontology_top_concept }
    /// Port of `getOntologyTopDataRangeConcept`.
    pub fn ontology_top_data_range_concept(&self) -> ConceptId { self.ontology_top_data_range_concept }

    /// Port of `hasClashedDescriptorLinker`.
    pub fn has_clashed_descriptor_linker(&self) -> bool { self.clashed_descriptor_linker.is_some() }
    /// Port of `getClashedDescriptorLinker`.
    pub fn clashed_descriptor_linker(&self) -> ClashDescId { self.clashed_descriptor_linker }
    /// Port of `setClashedDescriptorLinker`.
    pub fn set_clashed_descriptor_linker(&mut self, v: ClashDescId) -> &mut Self {
        self.clashed_descriptor_linker = v;
        self
    }

    /// Port of `isBackendIndividualLateReuseExpansionActivated`.
    pub fn is_backend_individual_late_reuse_expansion_activated(&self) -> bool {
        self.backend_individual_late_reuse_expansion_activated
    }
    /// Port of `setBackendIndividualLateReuseExpansionActivated`.
    pub fn set_backend_individual_late_reuse_expansion_activated(&mut self, v: bool) -> &mut Self {
        self.backend_individual_late_reuse_expansion_activated = v;
        self
    }

    /// Port of `hasMultipleConstructionIndividualNodes`.
    pub fn has_multiple_construction_individual_nodes(&self) -> bool {
        self.multiple_construction_indi_nodes
    }
    /// Port of `setMultipleConstructionIndividualNodes`.
    pub fn set_multiple_construction_individual_nodes(&mut self, v: bool) -> &mut Self {
        self.multiple_construction_indi_nodes = v;
        self
    }

    /// Port of `getConstructedIndividualNode`.
    pub fn constructed_individual_node(&self) -> NodeId { self.constructed_indi_node }
    /// Port of `setConstructedIndividualNode`.
    pub fn set_constructed_individual_node(&mut self, v: NodeId) -> &mut Self {
        self.constructed_indi_node = v;
        self
    }
    /// Port of `hasConstructedIndividualNodeInitialized`.
    pub fn has_constructed_individual_node_initialized(&self) -> bool {
        self.constructed_indi_node_initialized
    }
    /// Port of `setConstructedIndividualNodeInitialized`.
    pub fn set_constructed_individual_node_initialized(&mut self, v: bool) -> &mut Self {
        self.constructed_indi_node_initialized = v;
        self
    }

    /// Port of `getMaximumDeterministicBranchTag`.
    pub fn maximum_deterministic_branch_tag(&self) -> Cint64 { self.maximum_deterministic_branch_tag }
    /// Port of `setMaximumDeterministicBranchTag`.
    pub fn set_maximum_deterministic_branch_tag(&mut self, v: Cint64) -> &mut Self {
        self.maximum_deterministic_branch_tag = v;
        self
    }

    /// Port of `isReapplicationLastConceptDesciptorOnLastIndividualNodeRequired`.
    pub fn is_reapplication_last_concept_descriptor_on_last_individual_node_required(&self) -> bool {
        self.last_con_des_indi_reapplication
    }
    /// Port of `setReapplicationLastConceptDesciptorOnLastIndividualNodeRequired`.
    pub fn set_reapplication_last_concept_descriptor_on_last_individual_node_required(
        &mut self,
        v: bool,
    ) -> &mut Self {
        self.last_con_des_indi_reapplication = v;
        self
    }

    /// Port of `hasNominalNonDeterministicProcessingNodesSorted`.
    pub fn has_nominal_non_deterministic_processing_nodes_sorted(&self) -> bool {
        self.sorted_nominal_non_det_processing_nodes_sorted
    }
    /// Port of `setNominalNonDeterministicProcessingNodesSorted`.
    pub fn set_nominal_non_deterministic_processing_nodes_sorted(&mut self, v: bool) -> &mut Self {
        self.sorted_nominal_non_det_processing_nodes_sorted = v;
        self
    }

    /// Port of `isInsufficientNodeOccured`.
    pub fn is_insufficient_node_occured(&self) -> bool { self.insufficient_node_occured }
    /// Port of `setInsufficientNodeOccured`.
    pub fn set_insufficient_node_occured(&mut self, v: bool) -> &mut Self {
        self.insufficient_node_occured = v;
        self
    }

    /// Port of `isDelayedNominalProcessingOccured`.
    pub fn is_delayed_nominal_processing_occured(&self) -> bool { self.delayed_nominal_processing_occured }
    /// Port of `setDelayedNominalProcessingOccured`.
    pub fn set_delayed_nominal_processing_occured(&mut self, v: bool) -> &mut Self {
        self.delayed_nominal_processing_occured = v;
        self
    }

    /// Port of `isProblematicEQCandidateOccured`.
    pub fn is_problematic_eq_candidate_occured(&self) -> bool { self.problematic_eq_candidate_node_occured }
    /// Port of `setProblematicEQCandidateOccured`.
    pub fn set_problematic_eq_candidate_occured(&mut self, v: bool) -> &mut Self {
        self.problematic_eq_candidate_node_occured = v;
        self
    }

    /// Port of `getSeparatedSaturationConceptAssertionResolveNode`.
    pub fn separated_saturation_concept_assertion_resolve_node(&self) -> SatNodeId {
        self.separated_saturation_con_ass_resolve_node
    }
    /// Port of `setSeparatedSaturationConceptAssertionResolveNode`.
    pub fn set_separated_saturation_concept_assertion_resolve_node(&mut self, v: SatNodeId) -> &mut Self {
        self.separated_saturation_con_ass_resolve_node = v;
        self
    }

    /// Port of `isIncrementalExpansionInitialised`.
    pub fn is_incremental_expansion_initialised(&self) -> bool { self.incremental_expansion_initialized }
    /// Port of `setIncrementalExpansionInitialised`.
    pub fn set_incremental_expansion_initialised(&mut self, v: bool) -> &mut Self {
        self.incremental_expansion_initialized = v;
        self
    }

    /// Port of `getIncrementalExpansionID`.
    pub fn incremental_expansion_id(&self) -> Cint64 { self.incremental_exp_id }
    /// Port of `setIncrementalExpansionID`.
    pub fn set_incremental_expansion_id(&mut self, v: Cint64) -> &mut Self {
        self.incremental_exp_id = v;
        self
    }

    /// Port of `getMaxIncrementalPreviousCompletionGraphNodeID`.
    pub fn max_incremental_previous_completion_graph_node_id(&self) -> Cint64 {
        self.max_inc_prev_comp_graph_node_id
    }
    /// Port of `setMaxIncrementalPreviousCompletionGraphNodeID`.
    pub fn set_max_incremental_previous_completion_graph_node_id(&mut self, v: Cint64) -> &mut Self {
        self.max_inc_prev_comp_graph_node_id = v;
        self
    }

    /// Port of `isIncrementalExpansionCompatibleMerged`.
    pub fn is_incremental_expansion_compatible_merged(&self) -> bool {
        self.incremental_expansion_compatible_merged
    }
    /// Port of `setIncrementalExpansionCompatibleMerged`.
    pub fn set_incremental_expansion_compatible_merged(&mut self, v: bool) -> &mut Self {
        self.incremental_expansion_compatible_merged = v;
        self
    }

    /// Port of `isIncrementalExpansionCachingMerged`.
    pub fn is_incremental_expansion_caching_merged(&self) -> bool { self.incremental_expansion_caching_merged }
    /// Port of `setIncrementalExpansionCachingMerged`.
    pub fn set_incremental_expansion_caching_merged(&mut self, v: bool) -> &mut Self {
        self.incremental_expansion_caching_merged = v;
        self
    }

    /// Port of `isIndividualDependenceTrackingRequired`.
    pub fn is_individual_dependence_tracking_required(&self) -> bool { self.indi_dep_tracking_required }
    /// Port of `setIndividualDependenceTrackingRequired`.
    pub fn set_individual_dependence_tracking_required(&mut self, v: bool) -> &mut Self {
        self.indi_dep_tracking_required = v;
        self
    }

    /// Port of `hasBranchingInstruction`.
    pub fn has_branching_instruction(&self) -> bool { self.branching_instruction.is_some() }
    /// Port of `getBranchingInstruction`.
    pub fn branching_instruction(&self) -> BranchInstrId { self.branching_instruction }
    /// Port of `setBranchingInstruction`.
    pub fn set_branching_instruction(&mut self, v: BranchInstrId) -> &mut Self {
        self.branching_instruction = v;
        self
    }
    /// Port of `clearBranchingInstruction`.
    pub fn clear_branching_instruction(&mut self) -> &mut Self {
        self.branching_instruction = BranchInstrId::NONE;
        self
    }

    /// Port of `getRemainingPossibleInstanceIndividualMergingLimit`.
    pub fn remaining_possible_instance_individual_merging_limit(&self) -> Cint64 {
        self.remaining_possible_instance_individual_merging_limit
    }
    /// Port of `setRemainingPossibleInstanceIndividualMergingLimit`.
    pub fn set_remaining_possible_instance_individual_merging_limit(&mut self, v: Cint64) -> &mut Self {
        self.remaining_possible_instance_individual_merging_limit = v;
        self
    }

    /// Port of `getPossibleInstanceIndividualMergedCount`.
    pub fn possible_instance_individual_merged_count(&self) -> Cint64 {
        self.possible_instance_individual_merged_count
    }
    /// Port of `setPossibleInstanceIndividualMergedCount`.
    pub fn set_possible_instance_individual_merged_count(&mut self, v: Cint64) -> &mut Self {
        self.possible_instance_individual_merged_count = v;
        self
    }
    /// Port of `getPossibleInstanceIndividualCurrentMergingCount`.
    pub fn possible_instance_individual_current_merging_count(&self) -> Cint64 {
        self.possible_instance_individual_current_merging_count
    }
    /// Port of `setPossibleInstanceIndividualCurrentMergingCount`.
    pub fn set_possible_instance_individual_current_merging_count(&mut self, v: Cint64) -> &mut Self {
        self.possible_instance_individual_current_merging_count = v;
        self
    }
    /// Port of `getPossibleInstanceIndividualMergingSize`.
    pub fn possible_instance_individual_merging_size(&self) -> Cint64 {
        self.possible_instance_individual_merging_size
    }
    /// Port of `setPossibleInstanceIndividualMergingSize`.
    pub fn set_possible_instance_individual_merging_size(&mut self, v: Cint64) -> &mut Self {
        self.possible_instance_individual_merging_size = v;
        self
    }
    /// Port of `isPossibleInstanceIndividualMergingStopped`.
    pub fn is_possible_instance_individual_merging_stopped(&self) -> bool {
        self.possible_instance_individual_merging_stopped
    }
    /// Port of `setPossibleInstanceIndividualMergingStopped`.
    pub fn set_possible_instance_individual_merging_stopped(&mut self, v: bool) -> &mut Self {
        self.possible_instance_individual_merging_stopped = v;
        self
    }

    /// Port of `getBackendCacheIntegratedIndividualNodeCount`.
    pub fn backend_cache_integrated_individual_node_count(&self) -> Cint64 {
        self.backend_cache_integrated_individual_node_count
    }
    /// Port of `getBackendCacheIntegratedSameIndividualNodeCount`.
    pub fn backend_cache_integrated_same_individual_node_count(&self) -> Cint64 {
        self.backend_cache_integrated_same_individual_node_count
    }

    /// Port of `hasBackendCacheUpdateIndividualsInitialized`.
    pub fn has_backend_cache_update_individuals_initialized(&self) -> bool {
        self.backend_cache_update_individuals_initialized
    }
    /// Port of `setBackendCacheUpdateIndividualsInitialized`.
    pub fn set_backend_cache_update_individuals_initialized(&mut self, v: bool) -> &mut Self {
        self.backend_cache_update_individuals_initialized = v;
        self
    }
}

impl Default for ProcessingDataBox {
    fn default() -> Self { Self::new() }
}
