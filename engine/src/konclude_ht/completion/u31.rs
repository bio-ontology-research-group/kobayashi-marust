//! `completion::u31` — Generic helpers / accessors / label tests, batch
//! (port unit #31 of 36).
//!
//! Faithful port of the 9 methods the manifest (`01-completion-methods.md`,
//! "Unit 31") groups under configuration reading + ABox/branching analysis +
//! individual-reusing maintenance of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) are noted on each item:
//!
//!   * `readCalculationConfig`                    [494–845]   (the per-test config snapshot)
//!   * `analyzeABoxCompressionPossibilities`      [4097–4159] (debug: signature histogram)
//!   * `analyzeBranchingMemoryWasting`            [4163–4190] (debug: memory-pool accounting)
//!   * `testProblematicConceptSet`                [4408–4456] (debug: caching-error probe)
//!   * `analyseBranchingStatistics`               [4462–4499] (disjunction branching stats)
//!   * `debugTestCriticalConceptSet`              [4628–4667] (debug: critical-set match)
//!   * `searchSignatureReusingIndividualNode`     [4977–5018] (signature-blocking reuse search)
//!   * `removeIndividualReusing`                  [5021–5025]
//!   * `updateIndividualReusing`                  [5028–5178]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus, where the C++ takes one, the threaded per-thread context
//! `calc_alg_context: &mut CalculationAlgorithmContextBase` (the C++
//! `CCalculationAlgorithmContextBase*`). `readCalculationConfig` has NO context
//! parameter in C++ — it is a pure `mConf*`/`mOpt*` self-field snapshot driven by
//! the `CSatisfiableCalculationTask*`, ported faithfully as such. C++
//! `CIndividualProcessNode*&` in/out pointer-references become `&mut NodeId`; a
//! plain `CIndividualProcessNode*` value becomes `NodeId`.
//!
//! Deferral landscape. This unit is the config/debug/analysis tail of the engine;
//! almost every nontrivial body bottoms out in a subsystem that is not yet ported:
//!
//!   * the **configuration extension** `CCalculationConfigurationExtension`
//!     (`completion::stubs`, a zero-size marker with no getters) — the
//!     config-PRESENT branch of `readCalculationConfig` (`.cpp` 497–603) reads
//!     ~150 `config->isXxxActivated()` flags that do not exist yet, so that branch
//!     is `W6-DEFER[api]`; the config-ABSENT default branch (`.cpp` 604–697) is a
//!     pure self-field seeding and is **ported in full** here;
//!   * the **rule jump tables** (`mPosJumpFuncVec`/`mNegJumpFuncVec`, `.cpp`
//!     702–730) wire `apply*Rule` member-function pointers that are still opaque
//!     `Cint64` (`u05+` batches) — `W3-DEFER[pointer-alias]`;
//!   * the **task adapters / memory pools** on `CSatisfiableCalculationTask`
//!     (a W6 stub) — the `mOpt*` per-task option computation (`.cpp` 740–844) and
//!     `analyzeBranchingMemoryWasting` are `W6-DEFER[api]`;
//!   * the **debug model-string generators** (`generateExtendedDebugIndiModelStringList`,
//!     unit 32) + Qt file I/O + `cout` — the `analyze*`/`testProblematic*`/`debug*`
//!     bodies are debug-only and `W3-DEFER[api]`;
//!   * the **branch-tree / dependency-node / disjunction-statistics** spine and the
//!     **signature-blocking candidate hash** + **`CReusingIndividualNodeConceptExpansionData`**
//!     reuse subsystem with its sibling helpers (`getUpToDateIndividual`,
//!     `isIndividualNodeValidBlocker`, `removeReusingBlockerFollowing`,
//!     `reactivateIndirectReuseSuccessors`, `addReusingBlockerFollowing`,
//!     `anlyzeIndiviudalNodesConceptExpansion`, `updateSignatureBlockingConceptExpansion`,
//!     `addConceptToIndividual`, the `create*Dependency` factory) — all unported,
//!     so `analyseBranchingStatistics` / `searchSignatureReusingIndividualNode` /
//!     `removeIndividualReusing` / `updateIndividualReusing` keep their C++ control
//!     flow as `// PORT-PENDING` structural transcriptions; logic is documented,
//!     never silently dropped.
//!
//! Fully ported here (substrate-resolvable): the entire default-config seeding of
//! `readCalculationConfig`, and `debugTestCriticalConceptSet` (the digit/`^`-stripped
//! string-set match against `mCriticalConceptSetStringSet`) minus its one debug
//! string-generator call.

#![allow(dead_code)]
#![allow(unused_variables)]

use std::collections::HashSet;

use super::super::model::substrate::Id;
use super::super::process::NodeId;
use super::context::CalculationAlgorithmContextBase;
use super::stubs::{CalculationConfigurationExtension, SatisfiableCalculationTask};

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `readCalculationConfig`. cpp 494–845.
    ///
    /// Snapshots the per-test calculation configuration into the `mConf*` flags and
    /// derives the per-test `mOpt*` options. Faithful structure:
    ///   1. if the config object changed since `mLastConfig`, re-read all `mConf*`
    ///      (from the config if present, else from hard-coded defaults), re-point
    ///      `mLastConfig`, and re-wire the rule jump tables;
    ///   2. unconditionally re-derive the `mOpt*` options from the task adapters.
    pub fn read_calculation_config(&mut self, sat_calc_task: Id<SatisfiableCalculationTask>) {
        // W6-DEFER[api]: CCalculationConfigurationExtension* config =
        //     satCalcTask->getCalculationConfiguration();
        // `CSatisfiableCalculationTask` + `CCalculationConfigurationExtension` are
        // zero-size W6 stubs with no getters, so the live config cannot be read.
        // The config is treated as absent (`nullptr`), exercising the default
        // branch below; the config-PRESENT branch is transcribed as a deferral.
        let config: Id<CalculationConfigurationExtension> = Id::NONE;
        if config != self.last_config {
            if config != Id::NONE {
                // W6-DEFER[api]: config-PRESENT branch (cpp 497–603). Every line is
                //   mConfXxx = config->isXxxActivated();  /  config->getXxx();
                // re-read from the `CCalculationConfigurationExtension` getters,
                // which are not ported. The settings mirror the defaults below.
            } else {
                // Default (config == nullptr) branch, cpp 604–697 — pure self seeding.
                self.conf_completion_graph_caching = true;
                self.conf_delay_completion_graph_caching_reactivation = false;
                self.conf_specialized_automate_rules = true;
                self.conf_sub_set_blocking = false;
                self.conf_optimized_sub_set_blocking = true;
                self.conf_equal_set_blocking = false;
                self.conf_pairwise_equal_set_blocking = false;
                self.conf_ancestor_blocking_search = false;
                self.conf_anywhere_blocking_search = false;
                self.conf_anywhere_blocking_candidate_hash_search = false;
                self.conf_anywhere_blocking_linked_candidate_hash_search = true;
                self.conf_semantic_branching = false;
                self.conf_atomic_semantic_branching = true;
                self.conf_branch_triggering = true;
                self.conf_strict_indi_node_processing = true;
                self.conf_id_indi_priorization = true;
                self.conf_propagate_node_processed = false;
                self.conf_direct_rule_preprocessing = true;
                self.conf_lazy_new_nominal_generation = true;
                self.conf_cons_restricted_non_strict_indi_node_processing = true;
                self.conf_unique_name_assumption = false;
                self.conf_build_dependencies = true;
                self.conf_dependency_backtracking = true;
                self.conf_dependency_backjumping = true;
                self.conf_write_unsat_caching = true;
                self.conf_tested_concept_write_unsat_caching = true;
                self.conf_test_occur_unsat_cached = true;
                self.conf_test_precheck_unsat_cached = true;
                self.conf_minimize_merging = true;
                self.conf_sat_exp_cache_retrieval = true;
                self.conf_sat_exp_cache_concept_expansion = true;
                self.conf_sat_exp_cache_satisfiable_blocking = true;
                self.conf_sat_exp_cache_writing = true;
                self.conf_signature_saving = false;
                self.conf_signature_mirroring_blocking = false;
                self.conf_unsat_caching_use_full_node_dependency = false;
                self.conf_unsat_caching_use_node_signature_set = false;
                self.conf_comp_graph_reuse_cache_retrieval = false;
                self.conf_comp_graph_deterministic_reuse = true;
                self.conf_comp_graph_non_deterministic_reuse = true;
                self.conf_representative_propagation_rules = true;
                self.conf_debugging_write_data = false;
                self.conf_generate_queries = false;
                self.conf_debugging_write_data_complation_tasks = false;
                self.conf_debugging_write_data_only_on_satisfiability = false;
                self.conf_debugging_write_data_for_consistency_tests = false;
                self.conf_debugging_write_data_for_classification_tests = false;
                self.conf_debugging_write_data_for_answering_propagation_tests = false;
                self.conf_debugging_write_data_for_incremental_expansion_tests = false;
                self.conf_debugging_write_data_for_rep_cache_indi_computation_tests = false;
                self.conf_debugging_write_data_for_all_tests = false;
                self.conf_expand_created_successors_from_saturation = true;
                self.conf_caching_blocking_from_saturation = true;
                self.conf_saturation_caching_with_nominals = true;
                self.conf_saturation_concept_unsatisfiability_saturated_cache_writing = true;
                self.conf_saturation_satisfiabilitiy_expansion_cache_writing = false;
                self.conf_datatype_reasoning = true;
                self.conf_individuals_backend_cache_loading = true;
                self.conf_add_cached_computed_consequences = true;
                self.conf_merge_constructed_individual_node = false;
                self.conf_allow_backend_neighbour_expansion_blocking = true;
                self.conf_new_mergings_only_inferring_expansion = true;
                self.conf_allow_backend_successor_expansion_blocking = true;
                self.current_rec_proc_depth_limit = 300;
                self.conf_occurrence_statistics_collecting = true;
                self.conf_ignore_blocking_completion_graph_cached_non_blocking_nodes = true;

                self.conf_limit_backend_neighbour_expansion = false;
                self.conf_max_backend_neighbour_total_expansion_count = 15000;
                self.conf_default_individual_precomputation_count = 1500;
                self.conf_critical_backend_neighbour_total_expansion_count = 12000;
                self.conf_min_backend_neighbour_direct_expansion_count = 10;
                self.conf_all_problematic_backend_neighbour_direct_expansion = true;
                self.conf_atmost_all_direct_backend_neighbour_expansion = true;
                self.conf_backend_expansion_reuse = true;
                self.conf_backend_expansion_limit_reached_reuse_activation = true;
                self.conf_queued_backend_neighbour_expansion_indis_batch_size = 5;
                self.conf_queued_backend_neighbour_expansion_roles_batch_count = 3;
                self.conf_min_direct_neighbour_expansion_over_critical_reduction_size = 100;

                self.conf_neighbour_label_representative_expansion_delaying = true;
                self.conf_only_deterministic_representative_backend_individual_data_consideration =
                    true;

                self.conf_delayed_backend_initializiation = true;

                self.conf_backend_expansion_neighbour_individual_count_reuse_activation = 1;
                self.conf_backend_expansion_same_individual_count_reuse_activation = 1;

                self.conf_expand_deterministic_merged_handled_neighbours = true;
                self.conf_cardinality_neighbour_expansion_representative_counting = false;
            }
            self.last_config = config; // cpp 698: mLastConfig = config

            // cpp 700.
            self.conf_collect_caching_updated_blockable_indi_nodes =
                self.conf_completion_graph_caching;

            // W3-DEFER[pointer-alias]: rule jump-table wiring (cpp 702–730).
            //   mPosJumpFuncVec[CCAQAND] = &applyANDRule / &applyAutomatANDRule;
            //   the CCVARBIND* slots fan out to the REPRESENTATIVE* or the VARBIND*
            //   rules depending on mConfRepresentativePropagationRules.
            // The `apply*Rule` member-function pointers are not yet ported
            // (`u05+` batches); `pos/neg_tableau_rule_jump_func_vec` stay INVALID.
        }

        // W3-DEFER[api]: mConceptPriorityStrategy->readCalculationConfig(satCalcTask)
        // (cpp 737) — the priority strategy is a zero-size stub.

        // W6-DEFER[api]: per-task option derivation (cpp 740–840). Computes
        //   consPrepProcessing, mOptIncremental*Expansion, mOptAnalogousPropagationPathBlocking,
        //   mOptMergeConstructedIndividualNode, mOptCollectOccurrenceStatistics,
        //   mOptDelayedBackendInitializiation, mOptBackendExpansionReuse,
        //   mOptNeighbourLabelRepresentativeExpansionDelaying, the mOpt*BackendNeighbour*
        //   limits (scaled by the representative-backend precomputation factor),
        //   mOptConsistenceNodeMarking, mOptDetExpPreporcessing
        // from the task's consistence/incremental/representative-backend/possible-instance
        // adapters + processing data box — all `CSatisfiableCalculationTask` (W6 stub).

        // cpp 841: config-independent literal, ported in full.
        self.opt_non_strict_indi_node_processing = true;
    }

    /// Port of `analyzeABoxCompressionPossibilities`. cpp 4097–4159.
    ///
    /// Debug instrumentation: histograms the nominal individual nodes by the
    /// signature of their (non-nominal) concept label, then prints the counts /
    /// label sizes / determinism to `cout`.
    pub fn analyze_abox_compression_possibilities(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: debug-only. Iterates dataBox->getIndividualProcessNodeVector(),
        // and for each nominal node walks its CReapplyConceptLabelSet building a
        // CConceptSetSignature (not ported) keyed by the dependency-track-point
        // branching tag, then `cout`s the per-signature histogram. Needs the label-set
        // descriptor traversal, the individual/nominal-concept accessors, and the
        // CConceptSetSignature accumulator — none ported. No completion-graph effect.
    }

    /// Port of `analyzeBranchingMemoryWasting`. cpp 4163–4190.
    ///
    /// Debug instrumentation: walks the task's (and ancestors') memory-pool chain
    /// summing allocated / used / wasted bytes, then prints to `cout`.
    pub fn analyze_branching_memory_wasting(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W6-DEFER[api]: debug-only. Walks satTask->getMemoryPools() up the
        // getParentTask() chain accounting CMemoryPool block sizes/pointers. The
        // CSatisfiableCalculationTask + the bump CMemoryPool are not ported (the
        // arena model replaces the per-task pools); no completion-graph effect.
    }

    /// Port of `testProblematicConceptSet`. cpp 4408–4456.
    ///
    /// Debug probe: scans the up-to-date, localized non-nominal nodes for a
    /// hard-coded "FruitCourse/SweetFruitCourse" caching-error signature and, on a
    /// match, dumps the extended debug individual model to `caching-error.txt`.
    pub fn test_problematic_concept_set(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: debug-only. Iterates the individual node vector via
        // getUpToDateIndividual / getLocalizedIndividual (siblings, not ported),
        // checks each node's label for the hard-coded food-ontology IRIs, and on a
        // hit writes generateExtendedDebugIndiModelStringList(...) (unit 32) to a Qt
        // QFile. Needs the up-to-date/localized node siblings, the label traversal,
        // CIRIName lookups, the debug-string generator, and Qt file I/O — none ported.
    }

    /// Port of `analyseBranchingStatistics`. cpp 4462–4499.
    ///
    /// Walks the branch tree from the current node to the root, and for each
    /// non-deterministic OR-dependency increments the per-disjunction and
    /// per-disjunct expanded/satisfiable-occurrence statistics. Returns `true`.
    pub fn analyse_branching_statistics(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING / W3-DEFER[api]: gated by mConfBranchingStatisticsAnalysing
        // (default false). The loop:
        //   branchTreeNode = ctx->getBranchTreeNode();
        //   while (mConfBranchingStatisticsAnalysing && branchTreeNode) {
        //       nonDetDepTrackPoint = branchTreeNode->getDependencyTrackPoint();
        //       if (depNode && depNode->type == DNTORDEPENDENCY) {
        //           orDepNode->getConceptDescriptor()->getConcept()->getConceptData()
        //               ->getBranchingStatistics()->{incExpandedCount,incSatisfiableOccurrenceCount}();
        //           ((CORDisjunctDependencyTrackPoint*)nonDetDepTrackPoint)
        //               ->getDisjunctBranchingStatistics()->{inc...}();
        //       }
        //       branchTreeNode = (node != root) ? node->getParentNode() : nullptr;
        //   }
        // Needs the branch-tree-node accessors, the DependencyNode enum's OR variant,
        // CConceptProcessData + CDisjunction/DisjunctBranchingStatistics (none ported).
        // The conf flag is false by default, so the loop is inert; structure preserved.
        true
    }

    /// Port of `debugTestCriticalConceptSet`. cpp 4628–4667.
    ///
    /// Debug probe: if the concept-set string list has exactly 67 entries, strips
    /// `^` and digits from each, and if the resulting set is a superset of the
    /// configured `mCriticalConceptSetStringSet`, dumps the extended debug model.
    ///
    /// Ported in full bar the one debug string-generator call.
    pub fn debug_test_critical_concept_set(
        &mut self,
        con_set_list: &[String],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if con_set_list.len() == 67 {
            let mut contain_all = true;
            let mut test_concept_set_string_set: HashSet<String> = HashSet::new();
            // cpp 4632: the `containAll &&` guard is invariant-true during this
            // build loop (containAll is only cleared afterwards), so a plain
            // iteration is behaviourally identical.
            for con_string in con_set_list {
                let mut test_string = con_string.clone();
                test_string = test_string.replace("^", "");
                test_string = test_string.replace("0", "");
                test_string = test_string.replace("1", "");
                test_string = test_string.replace("2", "");
                test_string = test_string.replace("3", "");
                test_string = test_string.replace("4", "");
                test_string = test_string.replace("5", "");
                test_string = test_string.replace("6", "");
                test_string = test_string.replace("7", "");
                test_string = test_string.replace("8", "");
                test_string = test_string.replace("9", "");
                let test_string = test_string.trim().to_string();
                test_concept_set_string_set.insert(test_string);
            }

            if test_concept_set_string_set.len() >= self.critical_concept_set_string_set.len() {
                for test_string in &self.critical_concept_set_string_set {
                    if !test_concept_set_string_set.contains(test_string) {
                        contain_all = false;
                    }
                }
            } else {
                contain_all = false;
            }

            if contain_all && !self.found_critical_concept_set {
                self.found_critical_concept_set = true;
                // W3-DEFER[api]: mEndTaskDebugIndiModelString =
                //     generateExtendedDebugIndiModelStringList(calcAlgContext); (unit 32)
                self.found_critical_concept_set = false;
                let _debug = true; // cpp 4664: `bool debug = true;` debug breakpoint marker
            }
        }
    }

    /// Port of `searchSignatureReusingIndividualNode`. cpp 4977–5018.
    ///
    /// Looks up the signature-blocking candidate hash for an individual node and
    /// returns the first up-to-date, valid, concept-set-compatible candidate that
    /// can be reused as its blocker, or `Id::NONE`.
    pub fn search_signature_reusing_individual_node(
        &mut self,
        individual_node: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING / W3-DEFER[api]: structure (cpp 4978–5017):
        //   sigBlockCandHash = dataBox->getSignatureBlockingCandidateHash(false);
        //   conSet = individualNode->getReapplyConceptLabelSet(false);
        //   if (sigBlockCandHash && conSet) {
        //       conCount = conSet->getConceptCount();
        //       if (!node->isInvalidSignatureBlocking()
        //               && node->getLastConceptCountSearchBlockingCandidate() != conCount) {
        //           node->setLastConceptCountSearchBlockingCandidate(conCount);
        //           conSig = conSet->getConceptSignatureValue();
        //           newCandCount = sigBlockCandHash->getBlockingCandidatesCount(conSig);
        //           lastCandCount = node->getLastSearchBlockerCandidateCount();
        //           if (node->getLastSearchBlockerCandidateSignature() != conSig) lastCandCount = 0;
        //           node->setLastSearchBlockerCandidateSignature(conSig);
        //           if (newCandCount != lastCandCount) {
        //               candDiffCount = newCandCount - lastCandCount;
        //               iterate sigBlockCandHash->getBlockingCandidatesIterator(conSig)
        //                 while hasNext && candDiffCount-- > 0 && !node->isInvalidSignatureBlocking():
        //                   candIndiID = it.next(true);
        //                   if (candIndiID != node->getIndividualNodeID()) {
        //                       candNode = getUpToDateIndividual(candIndiID, ctx);
        //                       if (isIndividualNodeValidBlocker(candNode, ctx)
        //                               && hasCompatibleConceptSetReuse(node, conSet, candNode, ctx)) {
        //                           node->setLastSearchBlockerCandidateCount(newCandCount - candDiffCount);
        //                           return candNode;
        //                       }
        //                   }
        //               node->setLastSearchBlockerCandidateCount(newCandCount);
        //           }
        //       }
        //   }
        //   return nullptr;
        // Needs the CSignatureBlockingCandidateHash + its iterator (Process layer,
        // not ported), the node signature-blocking accessors, and the siblings
        // getUpToDateIndividual / isIndividualNodeValidBlocker / hasCompatibleConceptSetReuse.
        Id::NONE
    }

    /// Port of `removeIndividualReusing`. cpp 5021–5025.
    ///
    /// Tears down a node's individual-reusing: clears the reusing flag, removes the
    /// blocker-following link, and reactivates the indirect reuse successors.
    pub fn remove_individual_reusing(
        &mut self,
        individual_node: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING / W3-DEFER[api]: structure (cpp 5022–5024):
        //   individualNode->clearProcessingRestrictionFlags(PRFREUSINGINDIVIDUAL);
        //   removeReusingBlockerFollowing(individualNode, calcAlgContext);
        //   reactivateIndirectReuseSuccessors(individualNode, true, calcAlgContext);
        // Needs the node PRFREUSINGINDIVIDUAL flag clear (process layer) and the two
        // siblings removeReusingBlockerFollowing / reactivateIndirectReuseSuccessors
        // (units 32+), none ported.
    }

    /// Port of `updateIndividualReusing`. cpp 5028–5178.
    ///
    /// Maintains a reusing node against its blocker: re-validates / re-searches the
    /// reuse target, propagates the blocker's non-deterministic concept expansion,
    /// re-checks the subset condition, and (on incompatibility) queues a blocking
    /// review.
    pub fn update_individual_reusing(
        &mut self,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING / W3-DEFER[api]: 151-line body (cpp 5029–5177), gated by the
        // node's PRFREUSINGINDIVIDUAL flag. Faithful outline:
        //   reusingData = processIndi->getReusingIndividualNodeConceptExpansionData(false);
        //   reuseIndi = getUpToDateIndividual(reusingData->getBlockerIndividualNode(), ctx);
        //   if (isIndividualNodeValidBlocker(reuseIndi, ctx)) {  // now invalid/blocked
        //       removeReusingBlockerFollowing(processIndi, ctx);
        //       reuseIndi = searchSignatureReusingIndividualNode(processIndi, ctx);
        //       if (reuseIndi) { copy-on-write locReusingData = initBlockingExpansionData(reusingData);
        //                        reset its blocking concept count/signature/subset-cursor;
        //                        addReusingBlockerFollowing(processIndi, ctx); }
        //       else { reactivateIndirectReuseSuccessors(processIndi, true, ctx);
        //              clear PRFREUSINGINDIVIDUAL; if (reusingData->isBlockingReviewMarked())
        //                  reusingReviewData->remove(processIndi->getIndividualNodeID()); }
        //   }
        //   if (reuseIndi) {
        //       anlyzeIndiviudalNodesConceptExpansion(reuseIndi, ctx);
        //       blockerAnalizedConExpData = reuseIndi->getAnalizedConceptExpansionData(false);
        //       reusingIndiCompatible &= !blockerAnalizedConExpData->isInvalidBlocker();
        //       // (a) propagate fresh non-deterministic expansions as a REUSECONCEPTS
        //       //     dependency branch, adding the missing concepts non-deterministically
        //       //     via addConceptToIndividual(...);
        //       // (b) re-validate the subset condition over the newly added sorted
        //       //     concept descriptors (updateSignatureBlockingConceptExpansion + scan),
        //       //     clearing reusingIndiCompatible if no longer a subset;
        //       // (c) if incompatible, mark the node for blocking review
        //       //     (reusingReviewData->insert(ancestorDepth, nodeID)).
        //   }
        // Needs CReusingIndividualNodeConceptExpansionData, CIndividualNodeAnalizedConceptExpansionData,
        // CReusingReviewData, the dependency factory (createREUSECONCEPTSDependency,
        // createNonDeterministicDependencyTrackPointBranch), and the siblings
        // getUpToDateIndividual / isIndividualNodeValidBlocker / removeReusingBlockerFollowing /
        // searchSignatureReusingIndividualNode / addReusingBlockerFollowing /
        // reactivateIndirectReuseSuccessors / anlyzeIndiviudalNodesConceptExpansion /
        // updateSignatureBlockingConceptExpansion / addConceptToIndividual — none ported.
    }
}
