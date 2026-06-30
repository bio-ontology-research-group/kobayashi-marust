//! `process::pn1` — method-batch unit **PN-1** of `CIndividualProcessNode`:
//! init / clone (`Source/Reasoner/Kernel/Process/CIndividualProcessNode.cpp`
//! lines 35–482).
//!
//! Ported FIRST of the PN units because it fixes the buffer-handoff conventions
//! every other PN unit assumes: the constructor's all-null seeding, and the two
//! `init*` methods that build a fresh node from its predecessor by shuffling the
//! triple-buffer (`mX`/`mUseX`/`mPrevX`), double-buffer (`mX`/`mPrevX`) and
//! loc/use (`mLocX`/`mUseX`) slots between `prev`/`use` generations on branch
//! entry. See `manifest/05-process-units.md` §3 PN-1.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ `init*` methods take a single
//! `CIndividualProcessNode* prevIndividual` and both (a) read all of its fields
//! and (b) store the pointer into `mPrevIndividual` and call
//! `prevIndividual->setRelocalized()`. The port splits this single argument into
//! `prev_id: NodeId` (the arena id stored in `prev_individual`) and
//! `prev: &mut IndividualProcessNode` (the borrowed object read/relocalized).
//! Behaviour is identical; only the representation of the pointer differs. The
//! caller is responsible for obtaining the two disjoint `&mut` (e.g. a future
//! `Arena::get2_mut`/`split_at_mut` helper), exactly as the C++ relies on the two
//! nodes being distinct objects.
//!
//! KONCLUDE-PORT-NOTE[ownership]: a handful of node fields the C++ copies by raw
//! linker-chain pointer (`mInitializingConceptLinkerIt`,
//! `mProcessInitializingConceptLinkerIt`, `mBlockedIndividualsLinker`,
//! `mSuccessorIndiNodeBackwardDependencyLinker`,
//! `mProcessingBlockedIndividualsLinker`) are modelled in `node.rs` as owned
//! `Vec`s (per `substrate.rs`). A C++ pointer copy shared the chain; the port
//! `.clone()`s the `Vec`. Iteration order is preserved, so behaviour matches.

#![allow(dead_code)]

use super::super::model::{Cint64, Id};
use super::node::IndividualProcessNode;
use super::stubs::ProcessContextId;
use super::NodeId;

impl IndividualProcessNode {
    // ===================================================================
    // Tag-base accessors (folded `CLocalizationTag` / `CBlockedTestTag` /
    // `CProcessTag` methods that PN-1's init/ctor logic relies on).
    // ===================================================================

    /// Port of `CLocalizationTag::setLocalizationTag(cint64)` (→ `CProcessTag::setProcessTag`).
    pub fn set_localization_tag(&mut self, localization_tag: Cint64) -> &mut Self {
        // CProcessTag::setProcessTag(localizationTag) on the localization base.
        self.localization_tag = localization_tag;
        self
    }

    /// Port of `CLocalizationTag::getLocalizationTag()` (→ `CProcessTag::getProcessTag`).
    pub fn localization_tag(&self) -> Cint64 {
        self.localization_tag
    }

    /// Port of `CLocalizationTag::isLocalizationTagUpToDate(cint64)`
    /// (→ `CProcessTag::isProcessTagUpToDate`, `.cpp` 55–57: `mProcessTag >= processTag`).
    /// The node-resolution keystone reads this against the current localization tag
    /// from `CProcessTagger::getCurrentLocalizationTag()`.
    pub fn is_localization_tag_up_to_date(&self, localization_tag: Cint64) -> bool {
        self.localization_tag >= localization_tag
    }

    /// Port of `CLocalizationTag::setRelocalized(bool)`.
    pub fn set_relocalized(&mut self, relocalized: bool) -> &mut Self {
        if self.relocalized != relocalized {
            self.relocalized = relocalized;
        }
        self
    }

    /// Port of `CBlockedTestTag::getBlockedTestTag()` (→ `CProcessTag::getProcessTag`).
    pub fn blocked_test_tag(&self) -> Cint64 {
        self.blocked_test_tag
    }

    /// Port of `CBlockedTestTag::setBlockedTestTag(cint64)` (→ `CProcessTag::setProcessTag`).
    pub fn set_blocked_test_tag(&mut self, blocking_add_tag: Cint64) -> &mut Self {
        self.blocked_test_tag = blocking_add_tag;
        self
    }

    // ===================================================================
    // Constructor / init / clone (PN-1).
    // ===================================================================

    /// Port of `CIndividualProcessNode::CIndividualProcessNode(CProcessContext*)`.
    ///
    /// The C++ constructor assigns every member to its null/zero/false default and
    /// then performs two context-dependent steps. The all-null part is supplied by
    /// `IndividualProcessNode::default()` (faithful to the field-by-field nulling
    /// at `.cpp` 38–211); this constructor adds only the two contextual steps.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: this is the real constructor port and
    /// supersedes the placeholder `IndividualProcessNode::new` declared at
    /// struct-def time in `node.rs` (whose doc explicitly deferred the tagger /
    /// mem-alloc seeding to PN-1).
    pub fn construct(process_context: ProcessContextId) -> Self {
        let mut node = IndividualProcessNode { process_context, ..Default::default() };
        // mMemAllocMan = CContext::getMemoryAllocationManager(mProcessContext);
        // W2-DEFER[api]: CContext::get_memory_allocation_manager(process_context)
        node.mem_alloc_man = Id::NONE;
        // setLocalizationTag(mProcessContext->getUsedProcessTagger());
        // W2-DEFER[api]: process_context.get_used_process_tagger().get_current_localization_tag()
        node.set_localization_tag(0);
        node
    }

    /// Port of `CIndividualProcessNode::initIndividualProcessNode`.
    ///
    /// Re-initialises `self` (a freshly allocated node) as the successor of
    /// `prev` in the completion graph: nulls the per-test-local slots, then copies
    /// / hands off every buffered + status field from the predecessor.
    pub fn init_individual_process_node(
        &mut self,
        prev_id: NodeId,
        prev: &mut IndividualProcessNode,
    ) -> &mut Self {
        self.role_back_prop_hash = Id::NONE;
        self.indi_process_linker = Id::NONE;
        self.concept_process_linker = Id::NONE;
        self.required_back_prop = false;
        self.indi_block = Id::NONE;
        self.indi_var_prop_block_data = Id::NONE;
        self.substitute_indi_node = Id::NONE;
        self.loc_reactivation_data = Id::NONE;
        self.loc_nominal_connection_set = Id::NONE;
        self.loc_succ_indi_atmost_reactivation_data = Id::NONE;
        self.loc_datatypes_value_space_data = Id::NONE;
        self.loc_inc_exp_data = Id::NONE;
        self.loc_individual_merging_hash = Id::NONE;
        self.backend_sync_data = Id::NONE;
        let prev_blocked_test_tag = prev.blocked_test_tag();
        self.set_blocked_test_tag(prev_blocked_test_tag);
        self.prev_individual = prev_id;
        self.debug_blocker_last_concept_des = prev.debug_blocker_last_concept_des;
        self.prev_concept_processing_queue = prev.use_concept_processing_queue;
        self.use_concept_processing_queue = self.prev_concept_processing_queue;
        self.prev_reapply_con_label_set = prev.use_reapply_con_label_set;
        self.use_reapply_con_label_set = self.prev_reapply_con_label_set;
        self.prev_reapply_role_succ_hash = prev.use_reapply_role_succ_hash;
        self.use_reapply_role_succ_hash = self.prev_reapply_role_succ_hash;
        self.last_added_link = prev.last_added_link;
        self.prev_concept_prop_binding_set_hash = prev.use_concept_prop_binding_set_hash;
        self.use_concept_prop_binding_set_hash = self.prev_concept_prop_binding_set_hash;
        self.prev_concept_var_bind_path_set_hash = prev.use_concept_var_bind_path_set_hash;
        self.use_concept_var_bind_path_set_hash = self.prev_concept_var_bind_path_set_hash;
        self.prev_concept_rep_prop_set_hash = prev.use_concept_rep_prop_set_hash;
        self.use_concept_rep_prop_set_hash = self.prev_concept_rep_prop_set_hash;
        self.prev_succ_role_hash = prev.use_succ_role_hash;
        self.use_succ_role_hash = self.prev_succ_role_hash;
        self.prev_disjoint_succ_role_hash = prev.use_disjoint_succ_role_hash;
        self.use_disjoint_succ_role_hash = self.prev_disjoint_succ_role_hash;
        self.disjoint_role_connections = prev.disjoint_role_connections;
        self.prev_conn_succ_set = prev.use_conn_succ_set;
        self.use_conn_succ_set = self.prev_conn_succ_set;
        self.prev_distinct_hash = prev.use_distinct_hash;
        self.use_distinct_hash = self.prev_distinct_hash;
        // [ownership]: linker-chain pointer copy → owned-Vec clone (see module note).
        self.initializing_concept_linker = prev.initializing_concept_linker.clone();
        self.process_initializing_concept_linker = prev.process_initializing_concept_linker.clone();
        self.assertion_role_linker = prev.assertion_role_linker;
        self.assertion_concept_linker = prev.assertion_concept_linker;
        self.assertion_data_linker = prev.assertion_data_linker;
        self.asserted_data_literal_linker = prev.asserted_data_literal_linker;
        self.last_processed_assertion_data_linker = prev.last_processed_assertion_data_linker;
        self.last_asserted_data_literal_linker = prev.last_asserted_data_literal_linker;
        self.reverse_assertion_role_linker = prev.reverse_assertion_role_linker;
        self.additional_role_assertions_linker = prev.additional_role_assertions_linker;
        self.additional_data_assertions_linker = prev.additional_data_assertions_linker;
        self.last_processed_additional_data_assertions_linker =
            prev.last_processed_additional_data_assertions_linker;
        self.base_concepts_initialized = prev.base_concepts_initialized;
        self.universally_connection_individual_initialized =
            prev.universally_connection_individual_initialized;
        self.role_assertions_initialized = prev.role_assertions_initialized;
        self.reverse_role_assertions_initialized = prev.reverse_role_assertions_initialized;
        self.loaded_nominal_indi_triples_assertions = prev.loaded_nominal_indi_triples_assertions;
        self.loaded_nominal_indi_representative_backend_data =
            prev.loaded_nominal_indi_representative_backend_data;
        self.nominal_indi_triples_assertions = prev.nominal_indi_triples_assertions;
        // [ownership]: linker-chain pointer copy → owned-Vec clone (see module note).
        self.blocked_individuals_linker = prev.blocked_individuals_linker.clone();
        self.successor_indi_node_backward_dependency_linker =
            prev.successor_indi_node_backward_dependency_linker.clone();
        self.backward_dependency_to_ancestor_individual_node =
            prev.backward_dependency_to_ancestor_individual_node;
        self.ancestor_link = prev.ancestor_link;
        self.indi_model = prev.indi_model;
        self.prev_indi_block = prev.prev_indi_block;
        self.prev_indi_var_prop_block_data = prev.prev_indi_var_prop_block_data;
        self.prev_indi_sat_block_data = prev.prev_indi_sat_block_data;
        self.prev_indi_unsat_cache_ret = prev.prev_indi_unsat_cache_ret;
        self.prev_sig_block_con_exp_data = prev.prev_sig_block_con_exp_data;
        self.prev_reusing_con_exp_data = prev.prev_reusing_con_exp_data;
        self.prev_sat_cache_ret_data = prev.prev_sat_cache_ret_data;
        self.prev_backend_sync_data = prev.prev_backend_sync_data;
        self.prev_sig_block_ind_expl_data = prev.use_sig_block_ind_expl_data;
        self.use_sig_block_ind_expl_data = self.prev_sig_block_ind_expl_data;
        self.prev_sig_block_follow_set = prev.use_sig_block_follow_set;
        self.use_sig_block_follow_set = self.prev_sig_block_follow_set;
        self.prev_sat_cache_storing_data = prev.prev_sat_cache_storing_data;
        self.indi_anc_depth = prev.indi_anc_depth;
        self.nominal_level = prev.nominal_level;
        self.merge_into_id = prev.merge_into_id;
        self.merged_dep_track_point = prev.merged_dep_track_point;
        self.indi_id = prev.indi_id;
        self.indi_type = prev.indi_type;
        self.processing_blocked_indi = prev.processing_blocked_indi;
        self.processing_blocked_individuals_linker =
            prev.processing_blocked_individuals_linker.clone();
        self.init_concept_descriptor = prev.init_concept_descriptor;
        self.processing_restriction_flags = prev.processing_restriction_flags;
        self.nom_indi = prev.nom_indi;
        self.invalid_signature_blocking = prev.invalid_signature_blocking;
        self.processing_queued = prev.processing_queued;
        self.extended_queue_processing = prev.extended_queue_processing;
        self.immediately_processing_queued = prev.immediately_processing_queued;
        self.det_exp_processing_queued = prev.det_exp_processing_queued;
        self.depth_processing_queued = prev.depth_processing_queued;
        self.blocked_react_processing_queued = prev.blocked_react_processing_queued;
        self.backend_synchron_retest_processing_queued =
            prev.backend_synchron_retest_processing_queued;
        self.backend_direct_influence_expansion_queued =
            prev.backend_direct_influence_expansion_queued;
        self.backend_indirect_compatibility_expansion_queued =
            prev.backend_indirect_compatibility_expansion_queued;
        self.backend_reuse_expansion_queued = prev.backend_reuse_expansion_queued;
        self.backend_neighbour_expansion_queued = prev.backend_neighbour_expansion_queued;
        self.incremental_compatibility_checking_queued =
            prev.incremental_compatibility_checking_queued;
        self.incremental_expansion_queued = prev.incremental_expansion_queued;
        self.delayed_nominal_processing_queued = prev.delayed_nominal_processing_queued;
        self.nominal_processing_delaying_checked = prev.nominal_processing_delaying_checked;
        self.assertion_initialisation_signature_value =
            prev.assertion_initialisation_signature_value;
        self.last_processing_priority = prev.last_processing_priority;
        self.dep_track_point = prev.dep_track_point;
        self.sat_cached_absorbed_disjunctions_reapply_con_des =
            prev.sat_cached_absorbed_disjunctions_reapply_con_des;
        self.sat_cached_absorbed_successor_reapply_con_des =
            prev.sat_cached_absorbed_successor_reapply_con_des;
        self.last_concept_count_cached_blocker_candidate =
            prev.last_concept_count_cached_blocker_candidate;
        self.last_concept_count_search_blocker_candidate =
            prev.last_concept_count_search_blocker_candidate;
        self.blocking_caching_saved_candidate_count = prev.blocking_caching_saved_candidate_count;
        self.last_search_blocker_candidate_count = prev.last_search_blocker_candidate_count;
        self.last_search_blocker_candidate_signature = prev.last_search_blocker_candidate_signature;
        self.caching_loss_node_reactivation_installed =
            prev.caching_loss_node_reactivation_installed;
        prev.set_relocalized(true);
        self.use_reactivation_data = prev.use_reactivation_data;
        self.use_nominal_connection_set = prev.use_nominal_connection_set;
        self.use_succ_indi_atmost_reactivation_data = prev.use_succ_indi_atmost_reactivation_data;
        self.use_datatypes_value_space_data = prev.use_datatypes_value_space_data;
        self.use_inc_exp_data = prev.use_inc_exp_data;
        self.inc_exp_id = prev.inc_exp_id;
        self.role_assertion_creation_id = prev.role_assertion_creation_id;
        self.use_individual_merging_hash = prev.use_individual_merging_hash;
        self.blocker_indi_node = prev.blocker_indi_node;
        self.following_indi_node = prev.following_indi_node;
        self.last_merged_into_individual_node = prev.last_merged_into_individual_node;
        self
    }

    /// Port of `CIndividualProcessNode::initIndividualProcessNodeCopy`.
    ///
    /// A selective variant of `init_individual_process_node`: only the field
    /// groups gated by `adobt_concept_labels` / `adobt_role_successors` /
    /// `adobt_status` are handed off (the C++ spelling `adobt*` is preserved).
    pub fn init_individual_process_node_copy(
        &mut self,
        prev_id: NodeId,
        prev: &mut IndividualProcessNode,
        adobt_concept_labels: bool,
        adobt_role_successors: bool,
        adobt_status: bool,
    ) -> &mut Self {
        self.role_back_prop_hash = Id::NONE;
        self.indi_process_linker = Id::NONE;
        self.concept_process_linker = Id::NONE;
        self.required_back_prop = false;
        self.substitute_indi_node = Id::NONE;
        self.indi_block = Id::NONE;
        self.indi_var_prop_block_data = Id::NONE;
        self.loc_reactivation_data = Id::NONE;
        self.loc_nominal_connection_set = Id::NONE;
        self.loc_datatypes_value_space_data = Id::NONE;
        self.loc_inc_exp_data = Id::NONE;
        self.loc_individual_merging_hash = Id::NONE;
        prev.set_relocalized(true);
        if adobt_status {
            let prev_blocked_test_tag = prev.blocked_test_tag();
            self.set_blocked_test_tag(prev_blocked_test_tag);
        }
        self.backend_sync_data = Id::NONE;
        self.prev_individual = prev_id;
        self.prev_concept_processing_queue = prev.use_concept_processing_queue;
        self.use_concept_processing_queue = self.prev_concept_processing_queue;
        self.dep_track_point = prev.dep_track_point;
        self.debug_blocker_last_concept_des = prev.debug_blocker_last_concept_des;
        self.caching_loss_node_reactivation_installed =
            prev.caching_loss_node_reactivation_installed;
        self.last_merged_into_individual_node = prev.last_merged_into_individual_node;

        if adobt_concept_labels {
            self.prev_reapply_con_label_set = prev.use_reapply_con_label_set;
            self.use_reapply_con_label_set = self.prev_reapply_con_label_set;
        }
        if adobt_role_successors {
            self.prev_reapply_role_succ_hash = prev.use_reapply_role_succ_hash;
            self.use_reapply_role_succ_hash = self.prev_reapply_role_succ_hash;
            self.last_added_link = prev.last_added_link;
            self.prev_concept_prop_binding_set_hash = prev.use_concept_prop_binding_set_hash;
            self.use_concept_prop_binding_set_hash = self.prev_concept_prop_binding_set_hash;
            self.prev_concept_var_bind_path_set_hash = prev.use_concept_var_bind_path_set_hash;
            self.use_concept_var_bind_path_set_hash = self.prev_concept_var_bind_path_set_hash;
            self.prev_concept_rep_prop_set_hash = prev.use_concept_rep_prop_set_hash;
            self.use_concept_rep_prop_set_hash = self.prev_concept_rep_prop_set_hash;
            self.prev_succ_role_hash = prev.use_succ_role_hash;
            self.use_succ_role_hash = self.prev_succ_role_hash;
            self.prev_disjoint_succ_role_hash = prev.use_disjoint_succ_role_hash;
            self.use_disjoint_succ_role_hash = self.prev_disjoint_succ_role_hash;
            self.disjoint_role_connections = prev.disjoint_role_connections;
            self.prev_conn_succ_set = prev.use_conn_succ_set;
            self.use_conn_succ_set = self.prev_conn_succ_set;
            self.prev_distinct_hash = prev.use_distinct_hash;
            self.use_distinct_hash = self.prev_distinct_hash;
            self.use_reactivation_data = prev.use_reactivation_data;
            self.use_nominal_connection_set = prev.use_nominal_connection_set;
            self.use_succ_indi_atmost_reactivation_data =
                prev.use_succ_indi_atmost_reactivation_data;
            self.nominal_processing_delaying_checked = prev.nominal_processing_delaying_checked;
            self.use_datatypes_value_space_data = prev.use_datatypes_value_space_data;
            self.use_individual_merging_hash = prev.use_individual_merging_hash;
        }
        if adobt_status {
            self.role_assertion_creation_id = prev.role_assertion_creation_id;
            self.inc_exp_id = prev.inc_exp_id;
            self.use_inc_exp_data = prev.use_inc_exp_data;
            self.following_indi_node = prev.following_indi_node;
            self.blocker_indi_node = prev.blocker_indi_node;
            // [ownership]: linker-chain pointer copy → owned-Vec clone (see module note).
            self.initializing_concept_linker = prev.initializing_concept_linker.clone();
            self.process_initializing_concept_linker =
                prev.process_initializing_concept_linker.clone();
            self.assertion_role_linker = prev.assertion_role_linker;
            self.assertion_concept_linker = prev.assertion_concept_linker;
            self.assertion_data_linker = prev.assertion_data_linker;
            self.asserted_data_literal_linker = prev.asserted_data_literal_linker;
            self.last_processed_assertion_data_linker = prev.last_processed_assertion_data_linker;
            self.last_asserted_data_literal_linker = prev.last_asserted_data_literal_linker;
            self.reverse_assertion_role_linker = prev.reverse_assertion_role_linker;
            self.additional_role_assertions_linker = prev.additional_role_assertions_linker;
            self.additional_data_assertions_linker = prev.additional_data_assertions_linker;
            self.last_processed_additional_data_assertions_linker =
                prev.last_processed_additional_data_assertions_linker;
            self.base_concepts_initialized = prev.base_concepts_initialized;
            self.universally_connection_individual_initialized =
                prev.universally_connection_individual_initialized;
            self.role_assertions_initialized = prev.role_assertions_initialized;
            self.reverse_role_assertions_initialized = prev.reverse_role_assertions_initialized;
            self.nominal_indi_triples_assertions = prev.nominal_indi_triples_assertions;
            self.loaded_nominal_indi_triples_assertions =
                prev.loaded_nominal_indi_triples_assertions;
            self.loaded_nominal_indi_representative_backend_data =
                prev.loaded_nominal_indi_representative_backend_data;
            self.blocked_individuals_linker = prev.blocked_individuals_linker.clone();
            self.successor_indi_node_backward_dependency_linker =
                prev.successor_indi_node_backward_dependency_linker.clone();
            self.backward_dependency_to_ancestor_individual_node =
                prev.backward_dependency_to_ancestor_individual_node;
            self.ancestor_link = prev.ancestor_link;
            self.indi_model = prev.indi_model;
            self.prev_indi_block = prev.prev_indi_block;
            self.prev_indi_var_prop_block_data = prev.prev_indi_var_prop_block_data;
            self.prev_indi_sat_block_data = prev.prev_indi_sat_block_data;
            self.prev_indi_unsat_cache_ret = prev.prev_indi_unsat_cache_ret;
            self.prev_sig_block_con_exp_data = prev.prev_sig_block_con_exp_data;
            self.prev_reusing_con_exp_data = prev.prev_reusing_con_exp_data;
            self.prev_sat_cache_ret_data = prev.prev_sat_cache_ret_data;
            self.prev_backend_sync_data = prev.prev_backend_sync_data;
            self.prev_sig_block_ind_expl_data = prev.use_sig_block_ind_expl_data;
            self.use_sig_block_ind_expl_data = self.prev_sig_block_ind_expl_data;
            self.prev_sig_block_follow_set = prev.use_sig_block_follow_set;
            self.use_sig_block_follow_set = self.prev_sig_block_follow_set;
            self.prev_sat_cache_storing_data = prev.prev_sat_cache_storing_data;
            self.processing_blocked_indi = prev.processing_blocked_indi;
            self.processing_blocked_individuals_linker =
                prev.processing_blocked_individuals_linker.clone();
            self.init_concept_descriptor = prev.init_concept_descriptor;
            self.processing_restriction_flags = prev.processing_restriction_flags;
            self.indi_id = prev.indi_id;
            self.merge_into_id = prev.merge_into_id;
            self.merged_dep_track_point = prev.merged_dep_track_point;
            self.nom_indi = prev.nom_indi;
            self.sat_cached_absorbed_disjunctions_reapply_con_des =
                prev.sat_cached_absorbed_disjunctions_reapply_con_des;
            self.sat_cached_absorbed_successor_reapply_con_des =
                prev.sat_cached_absorbed_successor_reapply_con_des;
            self.last_concept_count_cached_blocker_candidate =
                prev.last_concept_count_cached_blocker_candidate;
            self.last_concept_count_search_blocker_candidate =
                prev.last_concept_count_search_blocker_candidate;
            self.blocking_caching_saved_candidate_count =
                prev.blocking_caching_saved_candidate_count;
            self.last_search_blocker_candidate_count = prev.last_search_blocker_candidate_count;
            self.last_search_blocker_candidate_signature =
                prev.last_search_blocker_candidate_signature;
            self.invalid_signature_blocking = prev.invalid_signature_blocking;
            self.processing_queued = prev.processing_queued;
            self.extended_queue_processing = prev.extended_queue_processing;
            self.last_processing_priority = prev.last_processing_priority;
            self.immediately_processing_queued = prev.immediately_processing_queued;
            self.det_exp_processing_queued = prev.det_exp_processing_queued;
            self.depth_processing_queued = prev.depth_processing_queued;
            self.blocked_react_processing_queued = prev.blocked_react_processing_queued;
            self.backend_synchron_retest_processing_queued =
                prev.backend_synchron_retest_processing_queued;
            self.backend_indirect_compatibility_expansion_queued =
                prev.backend_indirect_compatibility_expansion_queued;
            self.backend_direct_influence_expansion_queued =
                prev.backend_direct_influence_expansion_queued;
            self.backend_reuse_expansion_queued = prev.backend_reuse_expansion_queued;
            self.backend_neighbour_expansion_queued = prev.backend_neighbour_expansion_queued;
            self.incremental_compatibility_checking_queued =
                prev.incremental_compatibility_checking_queued;
            self.incremental_expansion_queued = prev.incremental_expansion_queued;
            self.delayed_nominal_processing_queued = prev.delayed_nominal_processing_queued;
            self.assertion_initialisation_signature_value =
                prev.assertion_initialisation_signature_value;
        }
        self.indi_anc_depth = prev.indi_anc_depth;
        self.nominal_level = prev.nominal_level;
        self.indi_type = prev.indi_type;
        self
    }
}
