//! `task::config` — the reasoner feature-flag bag.
//!
//! Ports the MEMBER FIELDS of Konclude
//! `Source/Reasoner/Kernel/Task/CCalculationConfigurationExtension.h`
//! (`: public CLocalConfigurationFixedExtension`). ~130 lazily-read config flags
//! (`mConf*Activated`) each paired with a `mConf*Checked` "already-resolved" bit,
//! plus ~20 `cint64` numeric limits (and their `*Checked` bits). Every
//! `is*Activated()` reads-once-then-caches from the config tree.
//!
//! This is the struct-definition wave; the ~130 `is*Activated()` / `get*()`
//! read-once-cache accessor bodies are the `// W6-TASK method-batch` unit.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the `mConf*Checked` lazy-resolve bits are kept
//! as plain `bool` companions of each flag (faithful read-once-then-cache); the
//! config tree (`CLocalConfigurationFixedExtension` / `CConfigDataReader`) the
//! accessors read from is an opaque provider (`config_provider`, [api]) until the
//! `Config/` subtree is ported. The base `CLocalConfigurationFixedExtension`
//! carries the config back-pointers; folded in as the opaque `base` handle.

#![allow(dead_code)]

use super::super::model::substrate::Cint64;

/// Port of `Reasoner::Kernel::Task::CCalculationConfigurationExtension`.
///
/// Field names are snake_case of the C++ `m*` members, in declaration order.
/// `*_activated` / `*_checked` is the read-once-cache pair; numeric `cint64`
/// limits map to `Cint64`.
#[derive(Debug, Default, Clone)]
pub struct CalculationConfigurationExtension {
    /// `CLocalConfigurationFixedExtension` base + config tree provider. [api]
    /// opaque handle (`CConfigurationBase* fixedCollectingConfiguration` + the
    /// previous-extension chain + `configID`).
    pub base: Cint64,

    // --- mConf*Activated / numeric limits (.h 215-368) ---
    pub conf_dependency_tracking_activated: bool,
    pub conf_backjumping_activated: bool,
    pub conf_unsat_caching_activated: bool,
    pub conf_sat_caching_activated: bool,
    pub conf_unsat_cache_single_level_writing_activated: bool,
    pub conf_unsat_cache_tested_concept_writing_activated: bool,
    pub conf_sat_cache_single_level_writing_activated: bool,
    pub conf_proxy_individuals_activated: bool,
    pub conf_minimize_merging_branches_activated: bool,
    pub conf_pseudo_model_rule_essential_checking_activated: bool,
    pub conf_class_pseudo_model_subsumption_merging_activated: bool,
    pub conf_specialized_automate_rule_activated: bool,
    pub conf_sub_set_blocking_activated: bool,
    pub conf_optimized_blocking_activated: bool,
    pub conf_equal_set_blocking_activated: bool,
    pub conf_pairwise_equal_set_blocking_activated: bool,
    pub conf_ancestor_blocking_search_activated: bool,
    pub conf_anywhere_blocking_search_activated: bool,
    pub conf_anywhere_blocking_candidate_hash_search_activated: bool,
    pub conf_semantic_branching_activated: bool,
    pub conf_atomic_semantic_branching_activated: bool,
    pub conf_branch_triggering_activated: bool,
    pub conf_strict_indi_node_processing_activated: bool,
    pub conf_id_indi_priorization_activated: bool,
    pub conf_propagate_node_processed_activated: bool,
    pub conf_direct_rule_preprocessing_activated: bool,
    pub conf_lazy_new_nominal_creation_activated: bool,
    pub conf_consistence_restricted_non_stict_processing_activated: bool,
    pub conf_unique_name_assumption_activated: bool,

    pub conf_satisfiable_expansion_cache_retrieval_activated: bool,
    pub conf_satisfiable_expansion_cache_concept_expansion_activated: bool,
    pub conf_satisfiable_expansion_cache_satisfiable_blocking_activated: bool,
    pub conf_satisfiable_expansion_cache_writing_activated: bool,

    pub conf_signature_mirroring_blocking_activated: bool,
    pub conf_signature_saving_activated: bool,
    pub conf_skip_and_concepts_activated: bool,

    pub conf_completion_graph_caching_activated: bool,
    pub conf_avoid_repeated_individual_processing_activated: bool,
    pub conf_delayed_completion_graph_caching_reactivation_activated: bool,
    pub conf_force_nodes_recreation_for_repeated_individual_processing_activated: bool,

    pub conf_unsat_caching_use_full_node_dependency_activated: bool,
    pub conf_unsat_caching_use_node_signature_set_activated: bool,

    pub conf_pairwise_merging_activated: bool,

    pub conf_saturation_piling_activated: bool,

    pub conf_comp_graph_reuse_cache_retrieval_activated: bool,
    pub conf_comp_graph_deterministic_reuse_activated: bool,
    pub conf_comp_graph_non_deterministic_reuse_activated: bool,

    pub conf_anywhere_blocking_core_concept_candidate_hash_search_activated: bool,
    pub conf_representative_propagation_activated: bool,

    pub conf_debugging_write_data_activated: bool,
    pub conf_debugging_write_data_completion_tasks_activated: bool,
    pub conf_debugging_write_data_saturation_tasks_activated: bool,
    pub conf_debugging_write_data_only_on_satisfiability_activated: bool,
    pub conf_debugging_write_data_for_consistency_tests_activated: bool,
    pub conf_debugging_write_data_for_classification_tests_activated: bool,
    pub conf_debugging_write_data_for_answering_propagation_tests_activated: bool,
    pub conf_debugging_write_data_for_incremental_expansion_tests_activated: bool,
    pub conf_debugging_write_data_for_representative_cache_recomputation_tests_activated: bool,
    pub conf_debugging_write_data_for_all_tests_activated: bool,

    pub conf_successor_concept_saturation_expansion_activated: bool,
    pub conf_saturation_caching_activated: bool,
    pub conf_saturation_critical_concept_testing_activated: bool,
    pub conf_saturation_direct_critical_to_insufficient_activated: bool,

    pub conf_saturation_successor_extension_activated: bool,
    pub conf_saturation_caching_with_nominals_by_reactivation_activated: bool,
    pub conf_nominal_saturation_activated: bool,
    pub conf_saturation_expansion_satisfiability_cache_writing_activated: bool,
    pub conf_saturation_unsatisfiability_cache_writing_activated: bool,
    pub conf_individuals_backend_cache_loading_activated: bool,

    pub equivalent_alternatives_saturation_merging_activated: bool,
    pub datatype_reasoning_activated: bool,
    pub computed_types_caching_activated: bool,
    pub construction_individual_node_merging_activated: bool,

    pub saturation_referred_node_many_concept_count: Cint64,
    pub saturation_many_concept_referred_node_count_process_limit: Cint64,
    pub saturation_referred_node_concept_count_process_limit: Cint64,
    pub saturation_referred_node_unprocessed_count_process_limit: Cint64,
    pub saturation_referred_node_checking_depth: Cint64,

    pub conf_force_many_concept_saturation_activated: bool,

    pub allow_backend_neighbour_expansion_blocking_activated: bool,
    pub allow_backend_successor_expansion_blocking_activated: bool,

    pub max_rec_pro_concept_count: Cint64,
    pub occurrence_statistics_collection_activated: bool,
    pub generating_test_queries_activated: bool,
    pub blocking_tests_ignoring_completion_graph_cached_non_blocked_nodes_activated: bool,
    pub backend_critical_neighbour_representative_expansion_delaying_checked: bool,
    pub backend_critical_neighbour_representative_expansion_delaying_activated: bool,

    pub backend_critical_neighbour_expansion_limitation_activated: bool,
    pub backend_critical_neighbour_expansion_reusing_activated: bool,
    pub backend_expansion_limit_reached_reuse_activation_activated: bool,
    pub backend_expansion_limit_reached_reuse_activation_checked: bool,

    pub backend_critical_neighbour_expansion_limit: Cint64,
    pub backend_critical_neighbour_expansion_priority_reduction_count: Cint64,
    pub backend_critical_neighbour_direct_expansion_limit: Cint64,
    pub backend_critical_neighbour_expansion_individuals_batch_size: Cint64,
    pub backend_critical_neighbour_expansion_roles_batch_size: Cint64,

    pub backend_delayed_same_initialization_copying_activated: bool,
    pub backend_delayed_same_initialization_copying_checked: bool,
    pub backend_only_deterministic_representative_individual_data_consideration_activated: bool,
    pub backend_only_deterministic_representative_individual_data_consideration_checked: bool,

    pub backend_critical_neighbour_expansion_limitation_checked: bool,
    pub backend_critical_neighbour_expansion_reusing_checked: bool,
    pub backend_critical_neighbour_expansion_late_dynamic_reusing_checked: bool,
    pub backend_critical_neighbour_expansion_late_dynamic_reusing_activated: bool,

    pub default_individual_precomputation_count: Cint64,
    pub default_individual_precomputation_count_checked: bool,
    pub backend_critical_neighbour_expansion_limit_checked: bool,
    pub backend_critical_neighbour_expansion_priority_reduction_count_checked: bool,
    pub backend_critical_neighbour_direct_expansion_limit_checked: bool,
    pub backend_critical_neighbour_expansion_individuals_batch_size_checked: bool,
    pub backend_critical_neighbour_expansion_roles_batch_size_checked: bool,

    pub backend_critical_neighbour_direct_expansion_over_critical_reduction_size_checked: bool,
    pub backend_critical_neighbour_direct_expansion_over_critical_reduction_size: Cint64,

    pub backend_expansion_reuse_activation_neighbour_individual_count_checked: bool,
    pub backend_expansion_reuse_activation_neighbour_individual_count: Cint64,
    pub backend_expansion_reuse_activation_same_individual_count_checked: bool,
    pub backend_expansion_reuse_activation_same_individual_count: Cint64,

    pub backend_expand_deterministically_merged_handled_neighbours_activated: bool,
    pub backend_expand_deterministically_merged_handled_neighbours_checked: bool,
    pub backend_cardinality_neighbour_expansion_representative_counting_activated: bool,
    pub backend_cardinality_neighbour_expansion_representative_counting_checked: bool,

    // --- mConf*Checked resolve-once bits (.h 371-474) ---
    pub conf_dependency_tracking_checked: bool,
    pub conf_backjumping_checked: bool,
    pub conf_unsat_caching_checked: bool,
    pub conf_sat_caching_checked: bool,
    pub conf_unsat_cache_single_level_writing_checked: bool,
    pub conf_unsat_cache_tested_concept_writing_checked: bool,
    pub conf_sat_cache_single_level_writing_checked: bool,
    pub conf_proxy_individuals_checked: bool,
    pub conf_minimize_merging_branches_checked: bool,
    pub conf_pseudo_model_rule_essential_checking_checked: bool,
    pub conf_class_pseudo_model_subsumption_merging_checked: bool,
    pub conf_specialized_automate_rule_checked: bool,
    pub conf_sub_set_blocking_checked: bool,
    pub conf_optimized_blocking_checked: bool,
    pub conf_equal_set_blocking_checked: bool,
    pub conf_pairwise_equal_set_blocking_checked: bool,
    pub conf_ancestor_blocking_search_checked: bool,
    pub conf_anywhere_blocking_search_checked: bool,
    pub conf_anywhere_blocking_candidate_hash_search_checked: bool,
    pub conf_semantic_branching_checked: bool,
    pub conf_atomic_semantic_branching_checked: bool,
    pub conf_branch_triggering_checked: bool,
    pub conf_strict_indi_node_processing_checked: bool,
    pub conf_id_indi_priorization_checked: bool,
    pub conf_propagate_node_processed_checked: bool,
    pub conf_direct_rule_preprocessing_checked: bool,
    pub conf_lazy_new_nominal_creation_checked: bool,
    pub conf_consistence_restricted_non_stict_processing_checked: bool,
    pub conf_unique_name_assumption_checked: bool,

    pub conf_satisfiable_expansion_cache_retrieval_checked: bool,
    pub conf_satisfiable_expansion_cache_concept_expansion_checked: bool,
    pub conf_satisfiable_expansion_cache_satisfiable_blocking_checked: bool,
    pub conf_satisfiable_expansion_cache_writing_checked: bool,

    pub conf_signature_mirroring_blocking_checked: bool,
    pub conf_signature_saving_checked: bool,
    pub conf_skip_and_concepts_checked: bool,

    pub conf_completion_graph_caching_checked: bool,
    pub conf_avoid_repeated_individual_processing_checked: bool,
    pub conf_delayed_completion_graph_caching_reactivation_checked: bool,
    pub conf_force_nodes_recreation_for_repeated_individual_processing_checked: bool,
    pub conf_individuals_backend_cache_loading_checked: bool,

    pub conf_unsat_caching_use_full_node_dependency_checked: bool,
    pub conf_unsat_caching_use_node_signature_set_checked: bool,

    pub conf_pairwise_merging_checked: bool,

    pub conf_saturation_piling_checked: bool,

    pub conf_comp_graph_reuse_cache_retrieval_checked: bool,
    pub conf_comp_graph_deterministic_reuse_checked: bool,
    pub conf_comp_graph_non_deterministic_reuse_checked: bool,

    pub conf_anywhere_blocking_core_concept_candidate_hash_search_checked: bool,
    pub conf_representative_propagation_checked: bool,
    pub conf_debugging_write_data_checked: bool,
    pub conf_debugging_write_data_saturation_tasks_checked: bool,
    pub conf_debugging_write_data_completion_tasks_checked: bool,
    pub conf_debugging_write_data_only_on_satisfiability_checked: bool,
    pub conf_debugging_write_data_for_consistency_tests_checked: bool,
    pub conf_debugging_write_data_for_classification_tests_checked: bool,
    pub conf_debugging_write_data_for_answering_propagation_tests_checked: bool,
    pub conf_debugging_write_data_for_incremental_expansion_tests_checked: bool,
    pub conf_debugging_write_data_for_representative_cache_recomputation_tests_checked: bool,
    pub conf_debugging_write_data_for_all_tests_checked: bool,

    pub conf_successor_concept_saturation_expansion_checked: bool,
    pub conf_saturation_caching_checked: bool,
    pub conf_saturation_critical_concept_testing_checked: bool,
    pub conf_saturation_direct_critical_to_insufficient_checked: bool,
    pub conf_saturation_successor_extension_checked: bool,
    pub conf_saturation_caching_with_nominals_by_reactivation_checked: bool,
    pub conf_nominal_saturation_checked: bool,
    pub conf_saturation_expansion_satisfiability_cache_writing_checked: bool,
    pub conf_saturation_unsatisfiability_cache_writing_checked: bool,

    pub equivalent_alternatives_saturation_merging_checked: bool,
    pub datatype_reasoning_checked: bool,

    pub computed_types_caching_checked: bool,
    pub construction_individual_node_merging_checked: bool,

    pub saturation_referred_node_many_concept_count_checked: bool,
    pub saturation_many_concept_referred_node_count_process_limit_checked: bool,
    pub saturation_referred_node_concept_count_process_limit_checked: bool,
    pub saturation_referred_node_unprocessed_count_process_limit_checked: bool,
    pub saturation_referred_node_checking_depth_checked: bool,

    pub conf_force_many_concept_saturation_checked: bool,

    pub new_mergings_backend_only_inferring_neighbour_expansion_checked: bool,
    pub new_mergings_backend_only_inferring_neighbour_expansion_activated: bool,

    pub allow_backend_neighbour_expansion_blocking_checked: bool,
    pub allow_backend_successor_expansion_blocking_checked: bool,

    pub max_rec_pro_concept_count_checked: bool,
    pub occurrence_statistics_collection_checked: bool,
    pub generating_test_queries_checked: bool,

    pub blocking_tests_ignoring_completion_graph_cached_non_blocked_nodes_checked: bool,
}

impl CalculationConfigurationExtension {
    /// Port of `CCalculationConfigurationExtension::CCalculationConfigurationExtension`.
    pub fn new() -> Self {
        CalculationConfigurationExtension::default()
    }
    /// W6-DEFER[api]: Port of `CConfigDataReader::readConfigBoolean`. The config
    /// tree (`CLocalConfigurationFixedExtension` / `CConfigDataReader`) is the
    /// opaque `base` provider until the `Config/` subtree is ported; the
    /// read-once-cache control flow of every getter is real, but the actual
    /// lookup resolves to the Konclude-shipped default here.
    fn read_config_boolean(&self, _config_path: &str, default_value: bool) -> bool {
        default_value
    }

    /// W6-DEFER[api]: Port of `CConfigDataReader::readConfigInteger` (see
    /// `read_config_boolean`).
    fn read_config_integer(&self, _config_path: &str, default_value: Cint64) -> Cint64 {
        default_value
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_dependency_tracking_activated(&mut self) -> bool {
        if !self.conf_dependency_tracking_checked {
            let mut tmp_config = self
                .read_config_boolean("Konclude.Calculation.Optimization.DependencyTracking", true);
            tmp_config |= self.is_backjumping_activated()
                | self.is_single_level_unsatisfiable_cache_writing_activated();
            self.conf_dependency_tracking_activated = tmp_config;
            self.conf_dependency_tracking_checked = true;
        }
        self.conf_dependency_tracking_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_backjumping_activated(&mut self) -> bool {
        if !self.conf_backjumping_checked {
            self.conf_backjumping_activated =
                self.read_config_boolean("Konclude.Calculation.Optimization.Backjumping", true);
            self.conf_backjumping_checked = true;
        }
        self.conf_backjumping_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_satisfiable_cache_retrieval_activated(&mut self) -> bool {
        if !self.conf_sat_caching_checked {
            self.conf_sat_caching_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.SatisfiableCacheRetrieval",
                true,
            );
            self.conf_sat_caching_checked = true;
        }
        self.conf_sat_caching_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_unsatisfiable_cache_retrieval_activated(&mut self) -> bool {
        if !self.conf_unsat_caching_checked {
            self.conf_unsat_caching_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.UnsatisfiableCacheRetrieval",
                true,
            );
            self.conf_unsat_caching_checked = true;
        }
        self.conf_unsat_caching_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_proxy_individuals_activated(&mut self) -> bool {
        if !self.conf_proxy_individuals_checked {
            self.conf_proxy_individuals_activated = self
                .read_config_boolean("Konclude.Calculation.Optimization.ProxyIndividuals", true);
            self.conf_proxy_individuals_checked = true;
        }
        self.conf_proxy_individuals_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_minimize_merging_branches_activated(&mut self) -> bool {
        if !self.conf_minimize_merging_branches_checked {
            self.conf_minimize_merging_branches_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.MinimizedMergingBranches",
                true,
            );
            self.conf_minimize_merging_branches_checked = true;
        }
        self.conf_minimize_merging_branches_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_single_level_unsatisfiable_cache_writing_activated(&mut self) -> bool {
        if !self.conf_unsat_cache_single_level_writing_checked {
            self.conf_unsat_cache_single_level_writing_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.UnsatisfiableCacheSingleLevelWriting",
                true,
            );
            self.conf_unsat_cache_single_level_writing_checked = true;
        }
        self.conf_unsat_cache_single_level_writing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_tested_concept_unsatisfiable_cache_writing_activated(&mut self) -> bool {
        if !self.conf_unsat_cache_tested_concept_writing_checked {
            self.conf_unsat_cache_tested_concept_writing_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.UnsatisfiableCacheTestingConceptWriting",
                true,
            );
            self.conf_unsat_cache_tested_concept_writing_checked = true;
        }
        self.conf_unsat_cache_tested_concept_writing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_single_level_satisfiable_cache_writing_activated(&mut self) -> bool {
        if !self.conf_sat_cache_single_level_writing_checked {
            self.conf_sat_cache_single_level_writing_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.SatisfiableCacheSingleLevelWriting",
                true,
            );
            self.conf_sat_cache_single_level_writing_checked = true;
        }
        self.conf_sat_cache_single_level_writing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_pseudo_model_rule_essential_checking_activated(&mut self) -> bool {
        if !self.conf_pseudo_model_rule_essential_checking_checked {
            self.conf_pseudo_model_rule_essential_checking_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.PseudoModelEssentialRuleChecking",
                true,
            );
            self.conf_pseudo_model_rule_essential_checking_checked = true;
        }
        self.conf_pseudo_model_rule_essential_checking_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_classification_pseudo_model_subsumption_merging_activated(&mut self) -> bool {
        if !self.conf_class_pseudo_model_subsumption_merging_checked {
            self.conf_class_pseudo_model_subsumption_merging_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.PseudoModelSubsumptionMerging",
                true,
            );
            self.conf_class_pseudo_model_subsumption_merging_checked = true;
        }
        self.conf_class_pseudo_model_subsumption_merging_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_specialized_automate_rule_activated(&mut self) -> bool {
        if !self.conf_specialized_automate_rule_checked {
            self.conf_specialized_automate_rule_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.SpezializedAutomateRule",
                true,
            );
            self.conf_specialized_automate_rule_checked = true;
        }
        self.conf_specialized_automate_rule_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_sub_set_blocking_activated(&mut self) -> bool {
        if !self.conf_sub_set_blocking_checked {
            self.conf_sub_set_blocking_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.SubSetBlockingTest",
                false,
            );
            self.conf_sub_set_blocking_checked = true;
        }
        self.conf_sub_set_blocking_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_optimized_blocking_activated(&mut self) -> bool {
        if !self.conf_optimized_blocking_checked {
            self.conf_optimized_blocking_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.OptimizedBlockingTest",
                true,
            );
            if !self.is_sub_set_blocking_activated()
                && !self.is_equal_set_blocking_activated()
                && !self.is_pairwise_equal_set_blocking_activated()
            {
                self.conf_optimized_blocking_activated = true;
            }
            self.conf_optimized_blocking_checked = true;
        }
        self.conf_optimized_blocking_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_equal_set_blocking_activated(&mut self) -> bool {
        if !self.conf_equal_set_blocking_checked {
            self.conf_equal_set_blocking_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.EqualSetBlockingTest",
                false,
            );
            self.conf_equal_set_blocking_checked = true;
        }
        self.conf_equal_set_blocking_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_pairwise_equal_set_blocking_activated(&mut self) -> bool {
        if !self.conf_pairwise_equal_set_blocking_checked {
            self.conf_pairwise_equal_set_blocking_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.PairwiseEqualSetBlockingTest",
                false,
            );
            self.conf_pairwise_equal_set_blocking_checked = true;
        }
        self.conf_pairwise_equal_set_blocking_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_ancestor_blocking_search_activated(&mut self) -> bool {
        if !self.conf_ancestor_blocking_search_checked {
            self.conf_ancestor_blocking_search_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.AncestorBlockingSearch",
                false,
            );
            if !self.is_anywhere_blocking_search_activated()
                && !self.is_anywhere_blocking_candidate_hash_search_activated()
                && !self.is_anywhere_blocking_core_concept_candidate_hash_search_activated()
            {
                self.conf_ancestor_blocking_search_activated = true;
            }
            self.conf_ancestor_blocking_search_checked = true;
        }
        self.conf_ancestor_blocking_search_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_anywhere_blocking_search_activated(&mut self) -> bool {
        if !self.conf_anywhere_blocking_search_checked {
            self.conf_anywhere_blocking_search_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.AnywhereBlockingSearch",
                false,
            );
            self.conf_anywhere_blocking_search_checked = true;
        }
        self.conf_anywhere_blocking_search_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_anywhere_blocking_candidate_hash_search_activated(&mut self) -> bool {
        if !self.conf_anywhere_blocking_candidate_hash_search_checked {
            self.conf_anywhere_blocking_candidate_hash_search_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.AnywhereCandidateHashBlockingSearch",
                true,
            );
            self.conf_anywhere_blocking_candidate_hash_search_checked = true;
        }
        self.conf_anywhere_blocking_candidate_hash_search_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_semantic_branching_activated(&mut self) -> bool {
        if !self.conf_semantic_branching_checked {
            self.conf_semantic_branching_activated = self
                .read_config_boolean("Konclude.Calculation.Optimization.SemanticBranching", false);
            self.conf_semantic_branching_checked = true;
        }
        self.conf_semantic_branching_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_atomic_semantic_branching_activated(&mut self) -> bool {
        if !self.conf_atomic_semantic_branching_checked {
            self.conf_atomic_semantic_branching_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.AtomicSemanticBranching",
                true,
            );
            self.conf_atomic_semantic_branching_checked = true;
        }
        self.conf_atomic_semantic_branching_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_branch_triggering_activated(&mut self) -> bool {
        if !self.conf_branch_triggering_checked {
            self.conf_branch_triggering_activated = self
                .read_config_boolean("Konclude.Calculation.Optimization.BranchTriggering", true);
            self.conf_branch_triggering_checked = true;
        }
        self.conf_branch_triggering_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_strict_indi_node_processing_activated(&mut self) -> bool {
        if !self.conf_strict_indi_node_processing_checked {
            self.conf_strict_indi_node_processing_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.StrictIndividualNodeProcessingOrder",
                true,
            );
            self.conf_strict_indi_node_processing_checked = true;
        }
        self.conf_strict_indi_node_processing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_id_indi_priorization_activated(&mut self) -> bool {
        if !self.conf_id_indi_priorization_checked {
            self.conf_id_indi_priorization_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.IndividualNodeIDPriorization",
                true,
            );
            self.conf_id_indi_priorization_checked = true;
        }
        self.conf_id_indi_priorization_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_propagate_node_processed_activated(&mut self) -> bool {
        if !self.conf_propagate_node_processed_checked {
            self.conf_propagate_node_processed_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.ProcessedIndividualNodePropagation",
                false,
            );
            if !self.is_strict_indi_node_processing_activated() {
                self.conf_propagate_node_processed_activated = true;
            }
            self.conf_propagate_node_processed_checked = true;
        }
        self.conf_propagate_node_processed_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_direct_rule_preprocessing_activated(&mut self) -> bool {
        if !self.conf_direct_rule_preprocessing_checked {
            self.conf_direct_rule_preprocessing_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.DirectRulePreprocessing",
                true,
            );
            self.conf_direct_rule_preprocessing_checked = true;
        }
        self.conf_direct_rule_preprocessing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_lazy_new_nominal_creation_activated(&mut self) -> bool {
        if !self.conf_lazy_new_nominal_creation_checked {
            self.conf_lazy_new_nominal_creation_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.LazyNewMergingNominalCreation",
                true,
            );
            self.conf_lazy_new_nominal_creation_checked = true;
        }
        self.conf_lazy_new_nominal_creation_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_consistence_restricted_non_stict_processing_activated(&mut self) -> bool {
        if !self.conf_consistence_restricted_non_stict_processing_checked {
            self.conf_consistence_restricted_non_stict_processing_activated = self
                .read_config_boolean(
                    "Konclude.Calculation.Optimization.ConsistenceRestrictedNonStrictProcessing",
                    true,
                );
            self.conf_consistence_restricted_non_stict_processing_checked = true;
        }
        self.conf_consistence_restricted_non_stict_processing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_unique_name_assumption_activated(&mut self) -> bool {
        if !self.conf_unique_name_assumption_checked {
            self.conf_unique_name_assumption_activated =
                self.read_config_boolean("Konclude.Calculation.UniqueNameAssumption", false);
            self.conf_unique_name_assumption_checked = true;
        }
        self.conf_unique_name_assumption_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_satisfiable_expansion_cache_retrieval_activated(&mut self) -> bool {
        if !self.conf_satisfiable_expansion_cache_retrieval_checked {
            self.conf_satisfiable_expansion_cache_retrieval_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.SatisfiableExpansionCacheRetrieval",
                true,
            );
            self.conf_satisfiable_expansion_cache_retrieval_checked = true;
        }
        self.conf_satisfiable_expansion_cache_retrieval_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_satisfiable_expansion_cache_concept_expansion_activated(&mut self) -> bool {
        if !self.conf_satisfiable_expansion_cache_concept_expansion_checked {
            self.conf_satisfiable_expansion_cache_concept_expansion_activated = self
                .read_config_boolean(
                    "Konclude.Calculation.Optimization.SatisfiableExpansionCacheConceptExpansion",
                    true,
                );
            self.conf_satisfiable_expansion_cache_concept_expansion_checked = true;
        }
        self.conf_satisfiable_expansion_cache_concept_expansion_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_satisfiable_expansion_cache_satisfiable_blocking_activated(&mut self) -> bool {
        if !self.conf_satisfiable_expansion_cache_satisfiable_blocking_checked {
            self.conf_satisfiable_expansion_cache_satisfiable_blocking_activated = self
                .read_config_boolean(
                "Konclude.Calculation.Optimization.SatisfiableExpansionCacheSatisfiableBlocking",
                true,
            );
            self.conf_satisfiable_expansion_cache_satisfiable_blocking_checked = true;
        }
        self.conf_satisfiable_expansion_cache_satisfiable_blocking_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_satisfiable_expansion_cache_writing_activated(&mut self) -> bool {
        if !self.conf_satisfiable_expansion_cache_writing_checked {
            self.conf_satisfiable_expansion_cache_writing_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.SatisfiableExpansionCacheWriting",
                true,
            );
            self.conf_satisfiable_expansion_cache_writing_checked = true;
        }
        self.conf_satisfiable_expansion_cache_writing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_signature_mirroring_blocking_activated(&mut self) -> bool {
        if !self.conf_signature_mirroring_blocking_checked {
            self.conf_signature_mirroring_blocking_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.SignatureMirroringBlocking",
                true,
            );
            self.conf_signature_mirroring_blocking_checked = true;
        }
        self.conf_signature_mirroring_blocking_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_signature_saving_activated(&mut self) -> bool {
        if !self.conf_signature_saving_checked {
            self.conf_signature_saving_activated =
                self.read_config_boolean("Konclude.Calculation.Optimization.SignatureSaving", true);
            self.conf_signature_saving_checked = true;
        }
        self.conf_signature_saving_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_skip_and_concepts_activated(&mut self) -> bool {
        if !self.conf_skip_and_concepts_checked {
            self.conf_skip_and_concepts_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.ANDConceptSkipping",
                false,
            );
            self.conf_skip_and_concepts_checked = true;
        }
        self.conf_skip_and_concepts_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_completion_graph_caching_activated(&mut self) -> bool {
        if !self.conf_completion_graph_caching_checked {
            self.conf_completion_graph_caching_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.CompletionGraphCaching",
                true,
            );
            self.conf_completion_graph_caching_checked = true;
        }
        self.conf_completion_graph_caching_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_delayed_completion_graph_caching_reactivation_activated(&mut self) -> bool {
        if !self.conf_delayed_completion_graph_caching_reactivation_checked {
            self.conf_delayed_completion_graph_caching_reactivation_activated = self
                .read_config_boolean(
                    "Konclude.Calculation.Optimization.DelayedCompletionGraphCachingReactivation",
                    false,
                );
            self.conf_delayed_completion_graph_caching_reactivation_checked = true;
        }
        self.conf_delayed_completion_graph_caching_reactivation_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_force_nodes_recreation_for_repeated_individual_processing_activated(
        &mut self,
    ) -> bool {
        if !self.conf_force_nodes_recreation_for_repeated_individual_processing_checked {
            self.conf_force_nodes_recreation_for_repeated_individual_processing_activated = self.read_config_boolean("Konclude.Calculation.Optimization.ForceNodesRecreationForRepeatedIndividualProcessing", true);
            self.conf_force_nodes_recreation_for_repeated_individual_processing_checked = true;
        }
        self.conf_force_nodes_recreation_for_repeated_individual_processing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_avoid_repeated_individual_processing_activated(&mut self) -> bool {
        if !self.conf_avoid_repeated_individual_processing_checked {
            self.conf_avoid_repeated_individual_processing_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.AvoidRepeatedIndividualProcessing",
                true,
            );
            self.conf_avoid_repeated_individual_processing_checked = true;
        }
        self.conf_avoid_repeated_individual_processing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_individuals_backend_cache_loading_activated(&mut self) -> bool {
        if !self.conf_individuals_backend_cache_loading_checked {
            self.conf_individuals_backend_cache_loading_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.IndividualsBackendCacheLoading",
                true,
            );
            self.conf_individuals_backend_cache_loading_checked = true;
        }
        self.conf_individuals_backend_cache_loading_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_unsatisfiable_caching_full_dependency_activated(&mut self) -> bool {
        if !self.conf_unsat_caching_use_full_node_dependency_checked {
            self.conf_unsat_caching_use_full_node_dependency_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.UnsatisfiableCachingFullDependency",
                false,
            );
            self.conf_unsat_caching_use_full_node_dependency_checked = true;
        }
        self.conf_unsat_caching_use_full_node_dependency_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_unsatisfiable_caching_full_signature_activated(&mut self) -> bool {
        if !self.conf_unsat_caching_use_node_signature_set_checked {
            self.conf_unsat_caching_use_node_signature_set_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.UnsatisfiableCachingFullSignature",
                false,
            );
            self.conf_unsat_caching_use_node_signature_set_checked = true;
        }
        self.conf_unsat_caching_use_node_signature_set_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_pairwise_merging_activated(&mut self) -> bool {
        if !self.conf_pairwise_merging_checked {
            self.conf_pairwise_merging_activated = self
                .read_config_boolean("Konclude.Calculation.Optimization.PairwiseMerging", false);
            self.conf_pairwise_merging_checked = true;
        }
        self.conf_pairwise_merging_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_saturation_piling_activated(&mut self) -> bool {
        if !self.conf_saturation_piling_checked {
            self.conf_saturation_piling_activated = self
                .read_config_boolean("Konclude.Calculation.Optimization.SaturationPiling", false);
            self.conf_saturation_piling_checked = true;
        }
        self.conf_saturation_piling_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_completion_graph_reuse_caching_retrieval_activated(&mut self) -> bool {
        if !self.conf_comp_graph_reuse_cache_retrieval_checked {
            self.conf_comp_graph_reuse_cache_retrieval_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.CompletionGraphReuseCachingRetrieval",
                true,
            );
            self.conf_comp_graph_reuse_cache_retrieval_checked = true;
        }
        self.conf_comp_graph_reuse_cache_retrieval_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_completion_graph_deterministic_reuse_activated(&mut self) -> bool {
        if !self.conf_comp_graph_deterministic_reuse_checked {
            self.conf_comp_graph_deterministic_reuse_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.CompletionGraphDeterministicReuse",
                true,
            );
            self.conf_comp_graph_deterministic_reuse_checked = true;
        }
        self.conf_comp_graph_deterministic_reuse_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_completion_graph_non_deterministic_reuse_activated(&mut self) -> bool {
        if !self.conf_comp_graph_non_deterministic_reuse_checked {
            self.conf_comp_graph_non_deterministic_reuse_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.CompletionGraphNonDeterministicReuse",
                true,
            );
            self.conf_comp_graph_non_deterministic_reuse_checked = true;
        }
        self.conf_comp_graph_non_deterministic_reuse_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_anywhere_blocking_core_concept_candidate_hash_search_activated(&mut self) -> bool {
        if !self.conf_anywhere_blocking_core_concept_candidate_hash_search_checked {
            self.conf_anywhere_blocking_core_concept_candidate_hash_search_activated = self
                .read_config_boolean(
                "Konclude.Calculation.Optimization.AnywhereCoreConceptCandidateHashBlockingSearch",
                true,
            );
            self.conf_anywhere_blocking_core_concept_candidate_hash_search_checked = true;
        }
        self.conf_anywhere_blocking_core_concept_candidate_hash_search_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_representative_propagation_activated(&mut self) -> bool {
        if !self.conf_representative_propagation_checked {
            self.conf_representative_propagation_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.RepresentativePropagation",
                true,
            );
            self.conf_representative_propagation_checked = true;
        }
        self.conf_representative_propagation_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_debugging_write_data_activated(&mut self) -> bool {
        if !self.conf_debugging_write_data_checked {
            self.conf_debugging_write_data_activated =
                self.read_config_boolean("Konclude.Debugging.WriteDebuggingData", false);
            self.conf_debugging_write_data_checked = true;
        }
        self.conf_debugging_write_data_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_debugging_write_data_saturation_tasks_activated(&mut self) -> bool {
        if !self.conf_debugging_write_data_saturation_tasks_checked {
            self.conf_debugging_write_data_saturation_tasks_activated = self.read_config_boolean(
                "Konclude.Debugging.WriteDebuggingDataSaturationTasks",
                false,
            );
            self.conf_debugging_write_data_saturation_tasks_checked = true;
        }
        self.conf_debugging_write_data_saturation_tasks_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_debugging_write_data_completion_tasks_activated(&mut self) -> bool {
        if !self.conf_debugging_write_data_completion_tasks_checked {
            self.conf_debugging_write_data_completion_tasks_activated = self.read_config_boolean(
                "Konclude.Debugging.WriteDebuggingDataCompletionTasks",
                false,
            );
            self.conf_debugging_write_data_completion_tasks_checked = true;
        }
        self.conf_debugging_write_data_completion_tasks_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_debugging_write_data_completion_tasks_only_on_satisfiability_activated(
        &mut self,
    ) -> bool {
        if !self.conf_debugging_write_data_only_on_satisfiability_checked {
            self.conf_debugging_write_data_only_on_satisfiability_activated = self
                .read_config_boolean(
                    "Konclude.Debugging.WriteDebuggingDataCompletionTasksOnlyOnSatisfiability",
                    false,
                );
            self.conf_debugging_write_data_only_on_satisfiability_checked = true;
        }
        self.conf_debugging_write_data_only_on_satisfiability_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_debugging_write_data_completion_tasks_for_consistency_tests_activated(
        &mut self,
    ) -> bool {
        if !self.conf_debugging_write_data_for_consistency_tests_checked {
            self.conf_debugging_write_data_for_consistency_tests_activated = self
                .read_config_boolean(
                    "Konclude.Debugging.WriteDebuggingDataCompletionTasksForConsistencyTests",
                    false,
                );
            self.conf_debugging_write_data_for_consistency_tests_checked = true;
        }
        self.conf_debugging_write_data_for_consistency_tests_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_debugging_write_data_completion_tasks_for_classification_tests_activated(
        &mut self,
    ) -> bool {
        if !self.conf_debugging_write_data_for_classification_tests_checked {
            self.conf_debugging_write_data_for_classification_tests_activated = self
                .read_config_boolean(
                    "Konclude.Debugging.WriteDebuggingDataCompletionTasksForClassificationTests",
                    false,
                );
            self.conf_debugging_write_data_for_classification_tests_checked = true;
        }
        self.conf_debugging_write_data_for_classification_tests_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_debugging_write_data_completion_tasks_for_answering_propagation_tests_activated(
        &mut self,
    ) -> bool {
        if !self.conf_debugging_write_data_for_answering_propagation_tests_checked {
            self.conf_debugging_write_data_for_answering_propagation_tests_activated = self
                .read_config_boolean(
                "Konclude.Debugging.WriteDebuggingDataCompletionTasksForAnsweringPropagationTests",
                false,
            );
            self.conf_debugging_write_data_for_answering_propagation_tests_checked = true;
        }
        self.conf_debugging_write_data_for_answering_propagation_tests_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_debugging_write_data_completion_tasks_for_incremental_expansion_tests_activated(
        &mut self,
    ) -> bool {
        if !self.conf_debugging_write_data_for_incremental_expansion_tests_checked {
            self.conf_debugging_write_data_for_incremental_expansion_tests_activated = self
                .read_config_boolean(
                "Konclude.Debugging.WriteDebuggingDataCompletionTasksForIncrementalExpansionTests",
                false,
            );
            self.conf_debugging_write_data_for_incremental_expansion_tests_checked = true;
        }
        self.conf_debugging_write_data_for_incremental_expansion_tests_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_debugging_write_data_completion_tasks_for_representative_cache_recomputation_tests_activated(
        &mut self,
    ) -> bool {
        if !self.conf_debugging_write_data_for_representative_cache_recomputation_tests_checked {
            self.conf_debugging_write_data_for_representative_cache_recomputation_tests_activated = self.read_config_boolean("Konclude.Debugging.WriteDebuggingDataCompletionTasksForRepresentativeCacheRecomputationTests", false);
            self.conf_debugging_write_data_for_representative_cache_recomputation_tests_checked =
                true;
        }
        self.conf_debugging_write_data_for_representative_cache_recomputation_tests_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_debugging_write_data_completion_tasks_for_all_tests_activated(&mut self) -> bool {
        if !self.conf_debugging_write_data_for_all_tests_checked {
            self.conf_debugging_write_data_for_all_tests_activated =
                self.read_config_boolean("Konclude.Debugging.WriteDebuggingDataForAllTests", false);
            self.conf_debugging_write_data_for_all_tests_checked = true;
        }
        self.conf_debugging_write_data_for_all_tests_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_successor_concept_saturation_expansion_activated(&mut self) -> bool {
        if !self.conf_successor_concept_saturation_expansion_checked {
            self.conf_successor_concept_saturation_expansion_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.SuccessorConceptSaturationExpansion",
                true,
            );
            self.conf_successor_concept_saturation_expansion_checked = true;
        }
        self.conf_successor_concept_saturation_expansion_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_saturation_caching_activated(&mut self) -> bool {
        if !self.conf_saturation_caching_checked {
            self.conf_saturation_caching_activated = self
                .read_config_boolean("Konclude.Calculation.Optimization.SaturationCaching", true);
            self.conf_saturation_caching_checked = true;
        }
        self.conf_saturation_caching_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_saturation_critical_concept_testing_activated(&mut self) -> bool {
        if !self.conf_saturation_critical_concept_testing_checked {
            self.conf_saturation_critical_concept_testing_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.SaturationCriticalConceptTesting",
                true,
            );
            self.conf_saturation_critical_concept_testing_checked = true;
        }
        self.conf_saturation_critical_concept_testing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_saturation_direct_critical_to_insufficient_activated(&mut self) -> bool {
        if !self.conf_saturation_direct_critical_to_insufficient_checked {
            self.conf_saturation_direct_critical_to_insufficient_activated = self
                .read_config_boolean(
                    "Konclude.Calculation.Optimization.SaturationDirectCriticalToInsufficient",
                    false,
                );
            self.conf_saturation_direct_critical_to_insufficient_checked = true;
        }
        self.conf_saturation_direct_critical_to_insufficient_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_saturation_successor_extension_activated(&mut self) -> bool {
        if !self.conf_saturation_successor_extension_checked {
            self.conf_saturation_successor_extension_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.SaturationSuccessorExtension",
                false,
            );
            self.conf_saturation_successor_extension_checked = true;
        }
        self.conf_saturation_successor_extension_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_saturation_caching_with_nominals_by_reactivation_activated(&mut self) -> bool {
        if !self.conf_saturation_caching_with_nominals_by_reactivation_checked {
            self.conf_saturation_caching_with_nominals_by_reactivation_activated = self
                .read_config_boolean(
                    "Konclude.Calculation.Optimization.NominalSaturationCachingByNodeReactivation",
                    false,
                );
            self.conf_saturation_caching_with_nominals_by_reactivation_checked = true;
        }
        self.conf_saturation_caching_with_nominals_by_reactivation_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_nominal_saturation_activated(&mut self) -> bool {
        if !self.conf_nominal_saturation_checked {
            self.conf_nominal_saturation_activated = self
                .read_config_boolean("Konclude.Calculation.Optimization.NominalSaturation", true);
            self.conf_nominal_saturation_checked = true;
        }
        self.conf_nominal_saturation_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_equivalent_alternatives_saturation_merging_activated(&mut self) -> bool {
        if !self.equivalent_alternatives_saturation_merging_checked {
            self.equivalent_alternatives_saturation_merging_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.EquivalentAlternativesSaturationMerging",
                true,
            );
            self.equivalent_alternatives_saturation_merging_checked = true;
        }
        self.equivalent_alternatives_saturation_merging_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_saturation_expansion_satisfiability_cache_writing_activated(&mut self) -> bool {
        if !self.conf_saturation_expansion_satisfiability_cache_writing_checked {
            self.conf_saturation_expansion_satisfiability_cache_writing_activated = self
                .read_config_boolean(
                "Konclude.Calculation.Optimization.SaturationExpansionSatisfiabilityCacheWriting",
                true,
            );
            self.conf_saturation_expansion_satisfiability_cache_writing_checked = true;
        }
        self.conf_saturation_expansion_satisfiability_cache_writing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_saturation_unsatisfiability_cache_writing_activated(&mut self) -> bool {
        if !self.conf_saturation_unsatisfiability_cache_writing_checked {
            self.conf_saturation_unsatisfiability_cache_writing_activated = self
                .read_config_boolean(
                "Konclude.Calculation.Optimization.SaturationExpansionSatisfiabilityCacheWriting",
                true,
            );
            self.conf_saturation_unsatisfiability_cache_writing_checked = true;
        }
        self.conf_saturation_unsatisfiability_cache_writing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_datatype_reasoning_activated(&mut self) -> bool {
        if !self.datatype_reasoning_checked {
            self.datatype_reasoning_activated =
                self.read_config_boolean("Konclude.Calculation.ComputedTypesCaching", true);
            self.datatype_reasoning_checked = true;
        }
        self.datatype_reasoning_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_computed_types_caching_activated(&mut self) -> bool {
        if !self.computed_types_caching_checked {
            self.computed_types_caching_activated = self
                .read_config_boolean("Konclude.Calculation.Optimization.DatatypeReasoning", true);
            self.computed_types_caching_checked = true;
        }
        self.computed_types_caching_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_construction_individual_node_merging_activated(&mut self) -> bool {
        if !self.construction_individual_node_merging_checked {
            self.construction_individual_node_merging_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.ConstructionIndividualNodeMerging",
                true,
            );
            self.construction_individual_node_merging_checked = true;
        }
        self.construction_individual_node_merging_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_force_many_concept_saturation_activated(&mut self) -> bool {
        if !self.conf_force_many_concept_saturation_checked {
            self.conf_force_many_concept_saturation_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.ForceManyConceptNodeSaturation",
                true,
            );
            self.conf_force_many_concept_saturation_checked = true;
        }
        self.conf_force_many_concept_saturation_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_allow_backend_neighbour_expansion_blocking_activated(&mut self) -> bool {
        if !self.allow_backend_neighbour_expansion_blocking_checked {
            self.allow_backend_neighbour_expansion_blocking_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.AllowBackendNeighbourExpansionBlocking",
                true,
            );
            self.allow_backend_neighbour_expansion_blocking_checked = true;
        }
        self.allow_backend_neighbour_expansion_blocking_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_new_mergings_backend_only_inferring_neighbour_expansion_activated(&mut self) -> bool {
        if !self.new_mergings_backend_only_inferring_neighbour_expansion_checked {
            self.new_mergings_backend_only_inferring_neighbour_expansion_activated = self.read_config_boolean("Konclude.Calculation.Optimization.NewMergingsBackendOnlyInferringNeighbourExpansion", true);
            self.new_mergings_backend_only_inferring_neighbour_expansion_checked = true;
        }
        self.new_mergings_backend_only_inferring_neighbour_expansion_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_allow_backend_successor_expansion_blocking_activated(&mut self) -> bool {
        if !self.allow_backend_successor_expansion_blocking_checked {
            self.allow_backend_successor_expansion_blocking_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.AllowBackendSuccessorExpansionBlocking",
                true,
            );
            self.allow_backend_successor_expansion_blocking_checked = true;
        }
        self.allow_backend_successor_expansion_blocking_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_occurrence_statistics_collection_activated(&mut self) -> bool {
        if !self.occurrence_statistics_collection_checked {
            self.occurrence_statistics_collection_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.OccurrenceStatisticsCollecting",
                true,
            );
            self.occurrence_statistics_collection_checked = true;
        }
        self.occurrence_statistics_collection_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_generating_test_queries_activated(&mut self) -> bool {
        if !self.generating_test_queries_checked {
            self.generating_test_queries_activated = self.read_config_boolean(
                "Konclude.Test.ConjunctiveQueryGeneration.CompletionGraphRandomWalks",
                true,
            );
            self.generating_test_queries_checked = true;
        }
        self.generating_test_queries_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_blocking_tests_ignoring_completion_graph_cached_non_blocked_nodes_activated(
        &mut self,
    ) -> bool {
        if !self.blocking_tests_ignoring_completion_graph_cached_non_blocked_nodes_checked {
            self.blocking_tests_ignoring_completion_graph_cached_non_blocked_nodes_activated = self.read_config_boolean("Konclude.Calculation.Optimization.BlockingTestsIgnoringCompletionGraphCachedNonBlockedNodes", true);
            self.blocking_tests_ignoring_completion_graph_cached_non_blocked_nodes_checked = true;
        }
        self.blocking_tests_ignoring_completion_graph_cached_non_blocked_nodes_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_backend_critical_neighbour_representative_expansion_delaying_activated(
        &mut self,
    ) -> bool {
        if !self.backend_critical_neighbour_representative_expansion_delaying_checked {
            self.backend_critical_neighbour_representative_expansion_delaying_activated = self.read_config_boolean("Konclude.Calculation.Optimization.BackendCriticalNeighbourRepresentativeExpansionDelaying", true);
            self.backend_critical_neighbour_representative_expansion_delaying_checked = true;
        }
        self.backend_critical_neighbour_representative_expansion_delaying_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_backend_critical_neighbour_expansion_limitation_activated(&mut self) -> bool {
        if !self.backend_critical_neighbour_expansion_limitation_checked {
            self.backend_critical_neighbour_expansion_limitation_activated = self
                .read_config_boolean(
                    "Konclude.Calculation.Optimization.BackendCriticalNeighbourExpansionLimitation",
                    true,
                );
            self.backend_critical_neighbour_expansion_limitation_checked = true;
        }
        self.backend_critical_neighbour_expansion_limitation_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_backend_critical_neighbour_expansion_reusing_activated(&mut self) -> bool {
        if !self.backend_critical_neighbour_expansion_reusing_checked {
            self.backend_critical_neighbour_expansion_reusing_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.BackendCriticalNeighbourExpansionReusing",
                false,
            );
            self.backend_critical_neighbour_expansion_reusing_checked = true;
        }
        self.backend_critical_neighbour_expansion_reusing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_backend_critical_neighbour_expansion_late_dynamic_reusing_activated(
        &mut self,
    ) -> bool {
        if !self.backend_critical_neighbour_expansion_late_dynamic_reusing_checked {
            self.backend_critical_neighbour_expansion_late_dynamic_reusing_activated = self.read_config_boolean("Konclude.Calculation.Optimization.BackendCriticalNeighbourExpansionLateDynamicReusing", false);
            self.backend_critical_neighbour_expansion_late_dynamic_reusing_checked = true;
        }
        self.backend_critical_neighbour_expansion_late_dynamic_reusing_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_backend_expansion_limit_reached_reuse_activation_activated(&mut self) -> bool {
        if !self.backend_expansion_limit_reached_reuse_activation_checked {
            self.backend_expansion_limit_reached_reuse_activation_activated = self
                .read_config_boolean(
                    "Konclude.Calculation.Optimization.BackendExpansionLimitReachedReuseActivation",
                    true,
                );
            self.backend_expansion_limit_reached_reuse_activation_checked = true;
        }
        self.backend_expansion_limit_reached_reuse_activation_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_backend_delayed_same_initialization_copying_activated(&mut self) -> bool {
        if !self.backend_delayed_same_initialization_copying_checked {
            self.backend_delayed_same_initialization_copying_activated = self.read_config_boolean(
                "Konclude.Calculation.Optimization.BackendDelayedSameLabelInitializationCopying",
                true,
            );
            self.backend_delayed_same_initialization_copying_checked = true;
        }
        self.backend_delayed_same_initialization_copying_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_backend_only_deterministic_representative_individual_data_consideration_activated(
        &mut self,
    ) -> bool {
        if !self.backend_only_deterministic_representative_individual_data_consideration_checked {
            self.backend_only_deterministic_representative_individual_data_consideration_activated = self.read_config_boolean("Konclude.Calculation.Optimization.BackendOnlyDeterministicRepresentativeIndividualDataConsideration", true);
            self.backend_only_deterministic_representative_individual_data_consideration_checked =
                true;
        }
        self.backend_only_deterministic_representative_individual_data_consideration_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_backend_expand_deterministically_merged_handled_neighbours_activated(
        &mut self,
    ) -> bool {
        if !self.backend_expand_deterministically_merged_handled_neighbours_checked {
            self.backend_expand_deterministically_merged_handled_neighbours_activated = self.read_config_boolean("Konclude.Calculation.Optimization.BackendExpandDeterministicallyMergedHandledNeighbours", true);
            self.backend_expand_deterministically_merged_handled_neighbours_checked = true;
        }
        self.backend_expand_deterministically_merged_handled_neighbours_activated
    }

    /// Port of the matching `is*Activated()` read-once-cache predicate.
    pub fn is_backend_cardinality_neighbour_expansion_representative_counting_activated(
        &mut self,
    ) -> bool {
        if !self.backend_cardinality_neighbour_expansion_representative_counting_checked {
            self.backend_cardinality_neighbour_expansion_representative_counting_activated = self.read_config_boolean("Konclude.Calculation.Optimization.BackendCriticalCardinalityCheckingNeighbourExpansionRepresentativeCounting", false);
            self.backend_cardinality_neighbour_expansion_representative_counting_checked = true;
        }
        self.backend_cardinality_neighbour_expansion_representative_counting_activated
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_maximum_recursive_processing_concept_count(&mut self) -> Cint64 {
        if !self.max_rec_pro_concept_count_checked {
            self.max_rec_pro_concept_count = self.read_config_integer(
                "Konclude.Calculation.MaximumRecursiveProcessingConceptCount",
                true as Cint64,
            );
            self.max_rec_pro_concept_count_checked = true;
        }
        self.max_rec_pro_concept_count
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_saturation_referred_node_many_concept_count(&mut self) -> Cint64 {
        if !self.saturation_referred_node_many_concept_count_checked {
            self.saturation_referred_node_many_concept_count = self.read_config_integer(
                "Konclude.Calculation.Optimization.SaturationReferredNodeManyConceptCount",
                true as Cint64,
            );
            self.saturation_referred_node_many_concept_count_checked = true;
        }
        self.saturation_referred_node_many_concept_count
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_saturation_many_concept_referred_node_count_process_limit(&mut self) -> Cint64 {
        if !self.saturation_many_concept_referred_node_count_process_limit_checked {
            self.saturation_many_concept_referred_node_count_process_limit = self.read_config_integer("Konclude.Calculation.Optimization.SaturationManyConceptReferredNodeCountProcessLimit", true as Cint64);
            self.saturation_many_concept_referred_node_count_process_limit_checked = true;
        }
        self.saturation_many_concept_referred_node_count_process_limit
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_saturation_referred_node_concept_count_process_limit(&mut self) -> Cint64 {
        if !self.saturation_referred_node_concept_count_process_limit_checked {
            self.saturation_referred_node_concept_count_process_limit = self.read_config_integer(
                "Konclude.Calculation.Optimization.SaturationReferredNodeConceptCountProcessLimit",
                true as Cint64,
            );
            self.saturation_referred_node_concept_count_process_limit_checked = true;
        }
        self.saturation_referred_node_concept_count_process_limit
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_saturation_referred_node_unprocessed_count_process_limit(&mut self) -> Cint64 {
        if !self.saturation_referred_node_unprocessed_count_process_limit_checked {
            self.saturation_referred_node_unprocessed_count_process_limit = self.read_config_integer("Konclude.Calculation.Optimization.SaturationReferredNodeUnprocessedCountProcessLimit", true as Cint64);
            self.saturation_referred_node_unprocessed_count_process_limit_checked = true;
        }
        self.saturation_referred_node_unprocessed_count_process_limit
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_saturation_referred_node_checking_depth(&mut self) -> Cint64 {
        if !self.saturation_referred_node_checking_depth_checked {
            self.saturation_referred_node_checking_depth = self.read_config_integer(
                "Konclude.Calculation.Optimization.SaturationReferredNodeCheckingDepth",
                true as Cint64,
            );
            self.saturation_referred_node_checking_depth_checked = true;
        }
        self.saturation_referred_node_checking_depth
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_backend_critical_neighbour_expansion_limit(&mut self) -> Cint64 {
        if !self.backend_critical_neighbour_expansion_limit_checked {
            self.backend_critical_neighbour_expansion_limit = self.read_config_integer(
                "Konclude.Calculation.Optimization.BackendCriticalNeighbourExpansionLimit",
                15000,
            );
            self.backend_critical_neighbour_expansion_limit_checked = true;
        }
        self.backend_critical_neighbour_expansion_limit
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_default_individual_precomputation_count(&mut self) -> Cint64 {
        if !self.default_individual_precomputation_count_checked {
            self.default_individual_precomputation_count = self.read_config_integer(
                "Konclude.Calculation.Precomputation.TotalPrecomputor.IndividualsPrecompuationSize",
                1500,
            );
            self.default_individual_precomputation_count_checked = true;
        }
        self.default_individual_precomputation_count
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_backend_critical_neighbour_expansion_priority_reduction_count(&mut self) -> Cint64 {
        if !self.backend_critical_neighbour_expansion_priority_reduction_count_checked {
            self.backend_critical_neighbour_expansion_priority_reduction_count = self.read_config_integer("Konclude.Calculation.Optimization.BackendCriticalNeighbourExpansionPriorityReductionCount", 12000);
            self.backend_critical_neighbour_expansion_priority_reduction_count_checked = true;
        }
        self.backend_critical_neighbour_expansion_priority_reduction_count
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_backend_critical_neighbour_direct_expansion_limit(&mut self) -> Cint64 {
        if !self.backend_critical_neighbour_direct_expansion_limit_checked {
            self.backend_critical_neighbour_direct_expansion_limit = self.read_config_integer(
                "Konclude.Calculation.Optimization.BackendCriticalNeighbourDirectExpansionLimit",
                10,
            );
            self.backend_critical_neighbour_direct_expansion_limit_checked = true;
        }
        self.backend_critical_neighbour_direct_expansion_limit
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_backend_critical_neighbour_direct_expansion_over_critical_reduction_size(
        &mut self,
    ) -> Cint64 {
        if !self.backend_critical_neighbour_direct_expansion_over_critical_reduction_size_checked {
            self.backend_critical_neighbour_direct_expansion_over_critical_reduction_size = self.read_config_integer("Konclude.Calculation.Optimization.BackendCriticalNeighbourDirectExpansionOverCriticalReductionSize", 200);
            self.backend_critical_neighbour_direct_expansion_over_critical_reduction_size_checked =
                true;
        }
        self.backend_critical_neighbour_direct_expansion_over_critical_reduction_size
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_backend_critical_neighbour_expansion_individuals_batch_size(&mut self) -> Cint64 {
        if !self.backend_critical_neighbour_expansion_individuals_batch_size_checked {
            self.backend_critical_neighbour_expansion_individuals_batch_size = self.read_config_integer("Konclude.Calculation.Optimization.BackendCriticalNeighbourExpansionIndividualsBatchSize", 3);
            self.backend_critical_neighbour_expansion_individuals_batch_size_checked = true;
        }
        self.backend_critical_neighbour_expansion_individuals_batch_size
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_backend_critical_neighbour_expansion_roles_batch_size(&mut self) -> Cint64 {
        if !self.backend_critical_neighbour_expansion_roles_batch_size_checked {
            self.backend_critical_neighbour_expansion_roles_batch_size = self.read_config_integer(
                "Konclude.Calculation.Optimization.BackendCriticalNeighbourExpansionRolesBatchSize",
                5,
            );
            self.backend_critical_neighbour_expansion_roles_batch_size_checked = true;
        }
        self.backend_critical_neighbour_expansion_roles_batch_size
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_backend_expansion_reuse_activation_neighbour_individual_count(&mut self) -> Cint64 {
        if !self.backend_expansion_reuse_activation_neighbour_individual_count_checked {
            self.backend_expansion_reuse_activation_neighbour_individual_count = self.read_config_integer("Konclude.Calculation.Optimization.BackendExpansionReuseActivationNeighbourIndividualCount", 1);
            self.backend_expansion_reuse_activation_neighbour_individual_count_checked = true;
        }
        self.backend_expansion_reuse_activation_neighbour_individual_count
    }

    /// Port of the matching `get*()` numeric-limit read-once-cache accessor.
    pub fn get_backend_expansion_reuse_activation_same_individual_count(&mut self) -> Cint64 {
        if !self.backend_expansion_reuse_activation_same_individual_count_checked {
            self.backend_expansion_reuse_activation_same_individual_count = self.read_config_integer("Konclude.Calculation.Optimization.BackendExpansionReuseActivationSameIndividualCount", 1);
            self.backend_expansion_reuse_activation_same_individual_count_checked = true;
        }
        self.backend_expansion_reuse_activation_same_individual_count
    }
}
