//! `completion::u13` — Merge-handling family, batch 2 (port unit #13 of 36).
//!
//! Faithful port of 3 merge methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (manifest `01-completion-methods.md`, "Unit 13", cpp 15097–15816):
//!   - `mergeMergingIndividualNodes`  [15097-15526] (the at-most / NN merge driver)
//!   - `createMergeBranchingTask`     [15611-15673] (the non-deterministic merge branch task)
//!   - `qualifyMergingIndividualNodes`[15677-15816] (the qualified-cardinality choose split)
//!
//! KONCLUDE-PORT-NOTE[ownership]: a merge method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase` (the C++ `CCalculationAlgorithmContextBase*`).
//! The C++ `CIndividualProcessNode*&` / `CConceptProcessDescriptor*&` out/in-out
//! pointer-references become `&mut NodeId` / `&mut ConProcDescId`; the raw
//! `CBranchingMergingProcessingRestrictionSpecification*` becomes its arena id
//! `RestrictionSpecId`. All other arena pointers become typed ids / opaque `Cint64`.
//!
//! KONCLUDE-PORT-NOTE[api]: following the convention established by the immediately
//! preceding same-wave unit (`u06`), every external dereference / call that bottoms
//! out in a NOT-YET-PORTED facility is reproduced as a `// W3-DEFER[...]:` stub
//! returning the minimal value (`Id::NONE`/`INVALID`/`false`/`0`/empty), preserving
//! the EXACT branch + loop structure and order of operations; no logic is dropped.
//! The real `self` state that IS ported is mutated faithfully — the at-most rule
//! counter (`mAppliedATMOSTRuleCount` → `self.applied_atmost_rule_count`) and the
//! ported config flags (`mConfLazyNewNominalGeneration` →
//! `self.conf_lazy_new_nominal_generation`, `mConfMinimizeMerging` →
//! `self.conf_minimize_merging`). The deferred facilities here are:
//!   * the per-test arenas (node / concept / descriptor / restriction-spec /
//!     dependency) — `W3-DEFER[api]`, to be wired onto `ctx.used_process_context()`
//!     in the arena-reconcile pass;
//!   * ~14 sibling merge/nominal/clash/dependency-factory algorithm methods that
//!     land in units 12 / 14 / 15 / 16 (`getUpToDateIndividual`,
//!     `createIndividualMergeCausingDescriptors`, `createClashedConceptDescriptor`,
//!     `getCorrectedNominalIndividualNode`, `isIndividualNodesMergeable`,
//!     `getMergedIndividualNodes`, `getIntoEmptyMergedIndividualNode`,
//!     `getLocalizedIndividual`, `getSuccessorIndividual`,
//!     `initializeMergingIndividualNodes`, `addIndividualToProcessingQueue`,
//!     `createNominalsSuccessorIndividuals`, `setIndividualNodeConceptLabelSetModified`,
//!     `createMERGEDependency`, `createNonDeterministicDependencyTrackPointBranch`,
//!     `createQUALIFYDependency`, `createClashedIndividualLinkDescriptor`,
//!     `containsIndividualNodeConcepts`, `addConceptsToIndividual`,
//!     `testIndividualNodeUnsatisfiableCached`,
//!     `addIndividualNodeForCacheUnsatisfiableRetrieval`) — `W3-DEFER[api]`;
//!   * the Task / Strategy / cache-retrieval subsystems (`createDependendBranchingTaskList`,
//!     `createCalculationAlgorithmContext`, `CSatisfiableCalculationTask`,
//!     `CProcessContext`/`CProcessTagger` allocation, the
//!     `CObjectParameterizingAllocator` of a new restriction spec/candidate linker,
//!     `getUsedTaskProcessorContext` / `communicateTaskCreation`,
//!     `getUsedTaskPriorityStrategy`, `getUsedUnsatisfiableCacheRetrievalStrategy`) —
//!     `W6-DEFER[api]` (Cache / Task / Strategy are out of W3 scope).
//!
//! KONCLUDE-PORT-NOTE[exceptions]: Konclude uses C++ exceptions as non-local
//! control flow here (`throw CCalculationClashProcessingException(...)` for an
//! at-most clash, `throw CCalculationStopProcessingException(true)` to suspend the
//! task after spawning merge branches). The exception machinery is not ported; each
//! throw site is marked `// W3-DEFER[exceptions]:` and followed by an early
//! `return false;` so control does NOT fall through, matching the C++ (the bool is
//! a placeholder — the C++ throw never produces a return value).
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ `CPROCESSSET<cint64>* distinctMergedSet`
//! (the restriction spec's distinct-merged-node id set) is modelled here as a local
//! `Vec<Cint64>` snapshot anchor (`distinct_merged_set`); the real COW set lives on
//! the restriction spec (`get_distinct_merged_nodes_set`). Set iteration is over the
//! snapshot by index so the iterator/`firstMergeableIt`/`secondMergeableIt` cursors
//! become `Option<usize>` indices — observationally identical (the C++ set order is
//! itself unspecified).

#![allow(
    unused_variables,
    unused_mut,
    unused_assignments,
    dead_code,
    clippy::collapsible_if,
    clippy::collapsible_else_if,
    clippy::too_many_arguments,
    clippy::needless_range_loop
)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::super::process::stubs::CandidateLinkerId;
use super::super::process::{
    ClashDescId, ConDescId, ConProcDescId, DependencyId, EdgeId, NodeId, RestrictionSpecId,
    RoleSuccHashId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;
use super::stubs::SatisfiableCalculationTask;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::mergeMergingIndividualNodes`.
    ///
    /// The at-most / NN-rule merge driver (cpp 15097–15526). Given the candidate
    /// successor nodes collected on `branching_merging_proc_rest`, it: (1) raises an
    /// at-most clash when the cardinality is already exhausted; (2) sets up the
    /// distinct-merged set (fixed-nominal or generic initialization, with the
    /// lazy-new-nominal generation arm); (3) relocates distinct entries onto their
    /// corrected nominal nodes; then (4) iterates the remaining merging candidates,
    /// finding the first/second distinct nodes the candidate is mergeable with and
    /// either adds it as a new distinct node, performs the single deterministic
    /// merge, or spawns the non-deterministic merge/distinct branch tasks (and
    /// suspends via `CCalculationStopProcessingException`).
    pub fn merge_merging_individual_nodes(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        link_count: Cint64,
        cardinality: Cint64,
        branching_merging_proc_rest: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[api]: conProDes->getConceptDescriptor()
        let con_des: ConDescId = Id::NONE;
        // W3-DEFER[api]: conDes->getConcept()
        let concept: ConceptId = Id::NONE;
        // W3-DEFER[api]: concept->getRole()
        let role: RoleId = Id::NONE;
        // W3-DEFER[api]: concept->getOperandList()  (conceptOpLinkerIt)
        // (anchor only; the operand list is consumed inside the sibling helpers)
        // W3-DEFER[api]: branchingMergingProcRest->getDistinctMergedNodesSet(false)
        // [ownership]: snapshot of the restriction-spec distinct-merged-node id set.
        let mut distinct_merged_set: Vec<Cint64> = Vec::new();
        let mut has_distinct_merged_set = false; // distinctMergedSet != nullptr
        let mut loc_distinct_merged_set_present = false; // locDistinctMergedSet != nullptr

        let mut deterministic_merging_attempt: Cint64 = 0;
        let mut deterministic_merging_step: Cint64 = 0;

        let mut distinct_count: Cint64 = 0;
        if has_distinct_merged_set {
            // W3-DEFER[api]: distinctMergedSet->count()
            distinct_count = distinct_merged_set.len() as Cint64;
        }
        // W3-DEFER[api]: branchingMergingProcRest->getRemainingLinkerMergingCandidateIndividualNodeCount()
        let remaining_linker_merging_candidate_count: Cint64 = 0;
        let link_and_candidate_count: Cint64 =
            remaining_linker_merging_candidate_count + distinct_count;
        if link_count != link_and_candidate_count {
            // update
            // W3-DEFER[api]: branchingMergingProcRest->setRemainingValidMergingCandidateIndividualNodeCount(linkCount-distinctCount)
            let _new_remaining_valid = link_count - distinct_count;
        }

        // W3-DEFER[api]: branchingMergingProcRest->getDependencyTrackPoint()
        let mut base_dep_track_point: TrackPointId = Id::NONE;

        let mut next_dep_track_point: TrackPointId = Id::NONE;

        let mut tmp_cardinality: Cint64 = cardinality;

        // W3-DEFER[api]: branchingMergingProcRest->getRemainingLinkerMergingCandidateIndividualNodeCount() > 0
        if cardinality <= 0 && remaining_linker_merging_candidate_count > 0 {
            // clash
            // W3-DEFER[api]: branchingMergingProcRest->takeNextMergingCandidateNodeLinker()
            let mut merge_cand_linker: CandidateLinkerId = Id::NONE;
            while merge_cand_linker != Id::NONE {
                // W3-DEFER[api]: mergeCandLinker->getMergingIndividualNodeCandidate()
                let merge_cand_indi_node: NodeId = Id::NONE;
                // W3-DEFER[api]: branchingMergingProcRest->hasValidRemainingMergingCandidates()
                //              || processIndi->hasRoleSuccessorToIndividual(role,mergeCandIndiNode,true)
                let valid_or_has_succ = false;
                if valid_or_has_succ {
                    let mut clash_descriptors: ClashDescId = Id::NONE;
                    // W3-DEFER[api]: getUpToDateIndividual(mergeCandIndiNode,calcAlgContext)  [unit 14]
                    let merging_indi_node: NodeId = Id::NONE;
                    // W3-DEFER[api]: createIndividualMergeCausingDescriptors(clashDescriptors,mergingIndiNode,mergeCandLinker->getMergingIndividualLink(),conceptOpLinkerIt,calcAlgContext)  [unit 14]
                    clash_descriptors = Id::NONE;
                    // W3-DEFER[api]: createClashedConceptDescriptor(clashDescriptors,processIndi,nullptr,baseDepTrackPoint,calcAlgContext)  [clash family]
                    clash_descriptors = Id::NONE;
                    // W3-DEFER[exceptions]: throw CCalculationClashProcessingException(clashDescriptors)
                    return false;
                } else {
                    // invalid link
                    // W3-DEFER[api]: branchingMergingProcRest->incRemainingValidMergingCandidateIndividualNodeCount()
                }
                // W3-DEFER[api]: branchingMergingProcRest->takeNextMergingCandidateNodeLinker()
                merge_cand_linker = Id::NONE;
            }
        }

        // W3-DEFER[api]: processIndi->isNominalIndividualNode()
        //              && branchingMergingProcRest->hasAddedBlockablePredecessorMergingNodeCandidate()
        let fixed_nominal_merging = false;
        let mut requires_nn_operating = false;
        if fixed_nominal_merging {
            // W3-DEFER[api]: branchingMergingProcRest->getRemainingNominalCreationCount()
            let remaining_nominal_creation_count: Cint64 = 0;
            let fix_dis_count = distinct_count + remaining_nominal_creation_count;
            if fix_dis_count > 0 {
                tmp_cardinality = distinct_count;
                // W3-DEFER[api]: branchingMergingProcRest->hasRemainingMergingCandidates()
                let has_remaining_merging_candidates = false;
                if has_remaining_merging_candidates {
                    requires_nn_operating = true;
                }
            } else if link_and_candidate_count > 0 {
                requires_nn_operating = true;
            }
        }

        let mut init_clash_descriptors: ClashDescId = Id::NONE;

        if link_and_candidate_count > tmp_cardinality || requires_nn_operating {
            // needs merging
            if fixed_nominal_merging {
                // W3-DEFER[api]: branchingMergingProcRest->isDistinctSetFixed()
                let is_distinct_set_fixed = false;
                let requires_nn_initialization = fixed_nominal_merging && !is_distinct_set_fixed;
                if requires_nn_initialization {
                    // W3-DEFER[macro]: STATINC(INDINODEMERGENEWNOMINALINITCOUNT,calcAlgContext)

                    if !loc_distinct_merged_set_present {
                        // W3-DEFER[api]: branchingMergingProcRest->getDistinctMergedNodesSet(true)->clear()
                        loc_distinct_merged_set_present = true;
                        has_distinct_merged_set = true;
                        distinct_merged_set.clear();
                        distinct_count = 0;
                    }

                    if self.conf_lazy_new_nominal_generation {
                        // W3-DEFER[api]: branchingMergingProcRest->setRemainingNominalCreationCount(tmpCardinality)
                        tmp_cardinality = 0;
                    } else {
                        // W3-DEFER[api]: createNominalsSuccessorIndividuals(processIndi,role->getIndirectSuperRoleList(),role,conceptOpLinkerIt,false,branchingMergingProcRest->getAddedBlockablePredecessorDependencyTrackPoint(),tmpCardinality,calcAlgContext)  [unit 16]
                        distinct_count = tmp_cardinality;

                        let mut dis_indi_idx: Cint64 = 0;

                        let mut new_last_link: EdgeId = Id::NONE;
                        // W3-DEFER[api]: processIndi->getRoleSuccessorHistoryLinkIterator(role,branchingMergingProcRest->getLastIndividualLink())
                        // iterate while roleSuccIt.hasNext():
                        //   link = roleSuccIt.next();
                        //   if (!newLastLink) newLastLink = link;
                        //   nominalSuccIndi = getSuccessorIndividual(processIndi,link,calcAlgContext);
                        //   distinctMergedSet->insert(nominalSuccIndi->getIndividualNodeID());
                        //   ++disIndiIdx;
                        // W3-DEFER[api]: branchingMergingProcRest->setLastIndividualLink(newLastLink)
                        let _ = (dis_indi_idx, new_last_link);
                    }
                    // W3-DEFER[api]: branchingMergingProcRest->setDistinctSetFixed(true)
                }
            } else {
                while distinct_count <= 0 {
                    if !loc_distinct_merged_set_present {
                        // W3-DEFER[api]: branchingMergingProcRest->getDistinctMergedNodesSet(true)
                        loc_distinct_merged_set_present = true;
                        has_distinct_merged_set = true;
                    }
                    // W3-DEFER[api]: branchingMergingProcRest->getMultipleMergingNodesInitializationClashesDescriptors()
                    init_clash_descriptors = Id::NONE;
                    // W3-DEFER[api]: branchingMergingProcRest->takeNextMergingCandidateNodeLinker()
                    let mut merge_cand_linker: CandidateLinkerId = Id::NONE;
                    while merge_cand_linker != Id::NONE {
                        // W3-DEFER[api]: mergeCandLinker->getMergingIndividualNodeCandidate()
                        let mut merge_cand_indi_node: NodeId = Id::NONE;

                        // W3-DEFER[api]: branchingMergingProcRest->hasValidRemainingMergingCandidates()
                        let has_valid_remaining = false;
                        if !has_valid_remaining {
                            // W3-DEFER[api]: getCorrectedNominalIndividualNode(mergeCandIndiNode->getIndividualNodeID(),calcAlgContext)  [unit 16]
                            merge_cand_indi_node = Id::NONE;
                        }

                        // W3-DEFER[api]: getUpToDateIndividual(mergeCandIndiNode,calcAlgContext)  [unit 14]
                        let merging_indi_node: NodeId = Id::NONE;
                        // W3-DEFER[api]: createIndividualMergeCausingDescriptors(initClashDescriptors,mergingIndiNode,mergeCandLinker->getMergingIndividualLink(),conceptOpLinkerIt,calcAlgContext)
                        init_clash_descriptors = Id::NONE;

                        // W3-DEFER[api]: distinctMergedSet->insert(mergeCandIndiNode->getIndividualNodeID())
                        distinct_count += 1;
                        if distinct_count > tmp_cardinality {
                            // clash, not able to merge
                            if init_clash_descriptors == Id::NONE {
                                // W3-DEFER[api]: branchingMergingProcRest->getMergingNodesInitializationClashesDescriptors()
                                init_clash_descriptors = Id::NONE;
                            }
                            // W3-DEFER[api]: createClashedConceptDescriptor(initClashDescriptors,processIndi,nullptr,baseDepTrackPoint,calcAlgContext)
                            init_clash_descriptors = Id::NONE;
                            // W3-DEFER[exceptions]: throw CCalculationClashProcessingException(initClashDescriptors)
                            return false;
                        }
                        // W3-DEFER[api]: branchingMergingProcRest->takeNextMergingInitializationCandidateNodeLinker()
                        merge_cand_linker = Id::NONE;
                    }
                }
            }

            // W3-DEFER[api]: branchingMergingProcRest->hasValidRemainingMergingCandidates()
            let has_valid_remaining_merging_candidates = false;
            if !has_valid_remaining_merging_candidates {
                // update distinct hash
                if !has_distinct_merged_set {
                    // W3-DEFER[api]: branchingMergingProcRest->getDistinctMergedNodesSet(true)
                    loc_distinct_merged_set_present = true;
                    has_distinct_merged_set = true;
                }
                let mut relocated = false;

                // for distinctIndiID in distinctMergedSet (snapshot copy — the C++ mutates locDistinctMergedSet inside)
                let dis_snapshot: Vec<Cint64> = distinct_merged_set.clone();
                for dis_index in 0..dis_snapshot.len() {
                    let distinct_indi_id = dis_snapshot[dis_index];

                    // W3-DEFER[api]: processIndi->getRoleSuccessorToIndividualLink(role,distinctIndiID,true)
                    let dis_indi_link: EdgeId = Id::NONE;
                    if dis_indi_link == Id::NONE {
                        // W3-DEFER[api]: getCorrectedNominalIndividualNode(distinctIndiID,calcAlgContext)  [unit 16]
                        let merged_into_node: NodeId = Id::NONE;
                        if !loc_distinct_merged_set_present {
                            // W3-DEFER[api]: branchingMergingProcRest->getDistinctMergedNodesSet(true)
                            loc_distinct_merged_set_present = true;
                            has_distinct_merged_set = true;
                        }
                        // W3-DEFER[api]: locDistinctMergedSet->remove(distinctIndiID)
                        relocated = true;
                        // W3-DEFER[api]: merged_into_node->getIndividualNodeID()
                        let merged_into_node_id: Cint64 = 0;
                        // W3-DEFER[api]: locDistinctMergedSet->contains(mergedIntoNode->getIndividualNodeID())
                        let contains_merged_into = false;
                        if contains_merged_into {
                            distinct_count -= 1;
                            if fixed_nominal_merging {
                                tmp_cardinality = distinct_count;
                            }
                        }
                        // W3-DEFER[api]: locDistinctMergedSet->insert(mergedIntoNode->getIndividualNodeID())
                    } else if loc_distinct_merged_set_present {
                        // W3-DEFER[api]: locDistinctMergedSet->insert(distinctIndiID)
                    }
                }

                if relocated {
                    // W3-DEFER[api]: branchingMergingProcRest->setDistinctSetNodeRelocated(true)
                }
            }

            // W3-DEFER[api]: branchingMergingProcRest->hasRemainingMergingCandidates()
            loop {
                let has_remaining_merging_candidates = false;
                if !has_remaining_merging_candidates {
                    break;
                }

                deterministic_merging_attempt += 1;
                let mut create_new_nodes_as_nominals = false;

                if self.conf_lazy_new_nominal_generation {
                    // W3-DEFER[api]: branchingMergingProcRest->getRemainingNominalCreationCount()
                    let remaining_new_nominal_creation_count: Cint64 = 0;
                    if remaining_new_nominal_creation_count > 0 {
                        // generate new nominal (NB the original creation block is commented-out in C++;
                        // only the tmpCardinality bump + flag remain live)
                        tmp_cardinality += 1;
                        create_new_nodes_as_nominals = true;
                    }
                }

                // W3-DEFER[api]: branchingMergingProcRest->takeNextMergingCandidateNodeLinker()
                let merge_cand_linker: CandidateLinkerId = Id::NONE;
                // W3-DEFER[api]: mergeCandLinker->getMergingIndividualNodeCandidate()
                let merge_cand_indi_node: NodeId = Id::NONE;
                let merge_cand_indi_node_id: Cint64 = 0; // mergeCandIndiNode->getIndividualNodeID()

                // KONCLUCE_TASK_ALGORITHM_MODEL_STRING_INSTRUCTION(...) — debug only, omitted.

                // W3-DEFER[api]: ((branchingMergingProcRest->hasValidRemainingMergingCandidates()
                //   && branchingMergingProcRest->getRemainingValidMergingCandidateIndividualNodeCount() > 0)
                //   || processIndi->hasRoleSuccessorToIndividual(role,mergeCandIndiNode,true))
                //   && !distinctMergedSet->contains(mergeCandIndiNode->getIndividualNodeID())
                let candidate_admissible = false;
                if candidate_admissible {
                    deterministic_merging_step += 1;

                    // W3-DEFER[api]: getUpToDateIndividual(mergeCandIndiNode,calcAlgContext)  [unit 14]
                    let merging_indi_node: NodeId = Id::NONE;

                    // TODO(Konclude): collect clashes and update distinct node set
                    let mut clash_descriptors: ClashDescId = init_clash_descriptors;
                    init_clash_descriptors = Id::NONE;
                    // W3-DEFER[api]: createIndividualMergeCausingDescriptors(clashDescriptors,mergingIndiNode,mergeCandLinker->getMergingIndividualLink(),conceptOpLinkerIt,calcAlgContext)
                    clash_descriptors = Id::NONE;

                    // search the distinct set for the first/second mergeable distinct node
                    let it_distinct_merged_set: Vec<Cint64> = distinct_merged_set.clone();
                    let dis_it_end = it_distinct_merged_set.len();
                    let mut first_mergeable_it: Option<usize> = None;
                    let mut second_mergeable_it: Option<usize> = None;

                    let mut first_cont_index: Cint64 = 0;
                    let mut second_cont_index: Cint64 = 0;

                    let mut cont_index: Cint64 = 0;
                    let mut dis_it = 0usize;
                    while dis_it != dis_it_end {
                        cont_index += 1;
                        let distinct_indi_id = it_distinct_merged_set[dis_it];

                        // W3-DEFER[api]: processIndi->getRoleSuccessorToIndividualLink(role,distinctIndiID,true)
                        let dis_indi_link: EdgeId = Id::NONE;
                        // KONCLUDE_ASSERT_X(disIndiLink, ...)
                        if dis_indi_link != Id::NONE {
                            // W3-DEFER[api]: getSuccessorIndividual(processIndi,disIndiLink,calcAlgContext)  [unit 14]
                            let dis_indi_node: NodeId = Id::NONE;

                            // W3-DEFER[api]: createIndividualMergeCausingDescriptors(clashDescriptors,disIndiNode,disIndiLink,conceptOpLinkerIt,calcAlgContext)
                            clash_descriptors = Id::NONE;

                            // W3-DEFER[api]: isIndividualNodesMergeable(disIndiNode,mergingIndiNode,clashDescriptors,calcAlgContext)  [unit 14]
                            let mergeable = false;
                            if mergeable {
                                if first_mergeable_it.is_none() {
                                    first_mergeable_it = Some(dis_it);
                                    first_cont_index = cont_index;
                                } else {
                                    second_mergeable_it = Some(dis_it);
                                    second_cont_index = cont_index;
                                    break;
                                }
                            }
                            dis_it += 1;
                        }
                    }

                    // W3-DEFER[api]: createMERGEDependency(processIndi,nullptr,baseDepTrackPoint,calcAlgContext)  [unit 12]
                    let merge_dependency_node: DependencyId = Id::NONE;
                    if merge_dependency_node != Id::NONE {
                        // W3-DEFER[api]: mergeDependencyNode->addBranchClashes(clashDescriptors)
                    }

                    if first_mergeable_it.is_none() {
                        if distinct_count < tmp_cardinality {
                            self.applied_atmost_rule_count += 1;

                            // add individual to distinct set
                            if !loc_distinct_merged_set_present {
                                // W3-DEFER[api]: branchingMergingProcRest->getDistinctMergedNodesSet(true)
                                loc_distinct_merged_set_present = true;
                                has_distinct_merged_set = true;
                            }
                            // W3-DEFER[api]: createNonDeterministicDependencyTrackPointBranch(mergeDependencyNode,true,calcAlgContext)  [unit 28/29]
                            let merge_non_det_dep_track_point: TrackPointId = Id::NONE;
                            // W3-DEFER[api]: mergingIndiNode->isNominalIndividualNode()
                            let merging_is_nominal = false;
                            if (!self.conf_minimize_merging && !create_new_nodes_as_nominals)
                                || merging_is_nominal
                            {
                                // W3-DEFER[api]: distinctMergedSet->insert(mergingIndiNode->getIndividualNodeID())

                                if create_new_nodes_as_nominals {
                                    // W3-DEFER[api]: branchingMergingProcRest->decRemainingNominalCreationCount()
                                }

                                // W3-DEFER[api]: branchingMergingProcRest->initMergingDependencyNode(mergeDependencyNode)
                                // W3-DEFER[api]: branchingMergingProcRest->initDependencyTracker(mergeNonDetDepTrackPoint)
                                base_dep_track_point = merge_non_det_dep_track_point;
                            } else {
                                // W3-DEFER[api]: getLocalizedIndividual(mergingIndiNode,false,calcAlgContext)  [unit 14/local]
                                let loc_merging_indi_node: NodeId = Id::NONE;

                                if create_new_nodes_as_nominals {
                                    // W3-DEFER[api]: branchingMergingProcRest->decRemainingNominalCreationCount()
                                }

                                // W3-DEFER[api]: getIntoEmptyMergedIndividualNode(locMergingIndiNode,createNewNodesAsNominals,processIndi,mergeNonDetDepTrackPoint,calcAlgContext)  [unit 14]
                                let merged_into_empty_indi_node: NodeId = Id::NONE;
                                // W3-DEFER[api]: distinctMergedSet->insert(mergedIntoEmptyIndiNode->getIndividualNodeID())

                                // W3-DEFER[api]: processIndi->getRoleSuccessorHistoryLinkIterator(role,branchingMergingProcRest->getLastIndividualLink()) — if hasNext():
                                //   link = roleSuccIt.next(); branchingMergingProcRest->setLastIndividualLink(link);
                                // W3-DEFER[api]: addIndividualToProcessingQueue(mergedIntoEmptyIndiNode,calcAlgContext)  [unit 3/driver]
                            }

                            distinct_count += 1;
                        } else {
                            // clash, not able to merge
                            // W3-DEFER[api]: createClashedConceptDescriptor(clashDescriptors,processIndi,nullptr,baseDepTrackPoint,calcAlgContext)
                            clash_descriptors = Id::NONE;
                            // W3-DEFER[exceptions]: throw CCalculationClashProcessingException(clashDescriptors)
                            return false;
                        }
                    } else if second_mergeable_it.is_none() && distinct_count >= tmp_cardinality {
                        self.applied_atmost_rule_count += 1;
                        // only one possibility to merge
                        // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi,calcAlgContext)
                        // W3-DEFER[api]: getLocalizedIndividual(*firstMergeableIt,calcAlgContext)  [unit 14]
                        let loc_dis_indi_node: NodeId = Id::NONE;
                        // W3-DEFER[api]: getLocalizedIndividual(mergingIndiNode,false,calcAlgContext)
                        let loc_merging_indi_node: NodeId = Id::NONE;

                        // W3-DEFER[api]: createNonDeterministicDependencyTrackPointBranch(mergeDependencyNode,true,calcAlgContext)
                        let merge_non_det_dep_track_point: TrackPointId = Id::NONE;

                        // W3-DEFER[api]: branchingMergingProcRest->isDistinctSetNodeRelocated()
                        let is_distinct_set_node_relocated = false;
                        if is_distinct_set_node_relocated {
                            // W3-DEFER[api]: branchingMergingProcRest->setDistinctSetNodeRelocated(false)
                            // W3-DEFER[api]: branchingMergingProcRest->initMergingDependencyNode(mergeDependencyNode)
                            // W3-DEFER[api]: branchingMergingProcRest->initDependencyTracker(mergeNonDetDepTrackPoint)
                        }

                        // W3-DEFER[api]: getMergedIndividualNodes(locDisIndiNode,locMergingIndiNode,mergeNonDetDepTrackPoint,calcAlgContext)  [unit 14]
                        let loc_merged_indi_node: NodeId = Id::NONE;
                        // W3-DEFER[api]: locMergedIndiNode->getIndividualNodeID() != locDisIndiNode->getIndividualNodeID()
                        let merged_id_changed = false;
                        if merged_id_changed {
                            if !loc_distinct_merged_set_present {
                                // W3-DEFER[api]: branchingMergingProcRest->getDistinctMergedNodesSet(true)
                                loc_distinct_merged_set_present = true;
                                has_distinct_merged_set = true;
                            }
                            // W3-DEFER[api]: distinctMergedSet->remove(locDisIndiNode->getIndividualNodeID())
                            // W3-DEFER[api]: distinctMergedSet->insert(locMergedIndiNode->getIndividualNodeID())
                            // W3-DEFER[api]: branchingMergingProcRest->setDistinctSetNodeRelocated(true)
                        }

                        // W6-DEFER[api]: calcAlgContext->getUsedUnsatisfiableCacheRetrievalStrategy()
                        //   ->testUnsatisfiableCacheForMergedIndividualNodes(conProDes,processIndi,locMergedIndiNode)
                        let test_unsat_cache_merged = false;
                        if test_unsat_cache_merged {
                            // W3-DEFER[api]: testIndividualNodeUnsatisfiableCached(locMergedIndiNode,calcAlgContext)
                        }

                        // W3-DEFER[api]: processIndi->getReapplyRoleSuccessorHash(false)
                        let role_succ_hash: RoleSuccHashId = Id::NONE;
                        // W3-DEFER[api]: roleSuccHash->getRoleSuccessorHistoryLinkIterator(role,branchingMergingProcRest->getLastIndividualLink(),&linkCount) — if hasNext():
                        let role_succ_it_has_next = false;
                        if role_succ_it_has_next {
                            // W3-DEFER[api]: initializeMergingIndividualNodes(processIndi,conProDes,&roleSuccIt,nullptr,conceptOpLinkerIt,branchingMergingProcRest,calcAlgContext)  [unit 14]
                            self.initialize_merging_individual_nodes_anchor();
                            // W3-DEFER[api]: qualifyMergingIndividualNodes(processIndi,conProDes,branchingMergingProcRest,calcAlgContext)  [sibling, this unit]
                            self.qualify_merging_individual_nodes(
                                process_indi,
                                con_pro_des,
                                branching_merging_proc_rest,
                                calc_alg_context,
                            );
                        }
                    } else {
                        self.applied_atmost_rule_count += 1;
                        // W6-DEFER[api]: CSatisfiableCalculationTask* newTaskList = nullptr;
                        let mut new_task_list: Id<SatisfiableCalculationTask> = Id::NONE;

                        // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi,calcAlgContext)
                        if let Some(first_idx) = first_mergeable_it {
                            // W3-DEFER[api]: getUpToDateIndividual(*firstMergeableIt,calcAlgContext)
                            let first_distinct_indi_node: NodeId = Id::NONE;
                            let new_task = self.create_merge_branching_task(
                                process_indi,
                                con_pro_des,
                                &mut first_distinct_indi_node.clone(),
                                &mut merging_indi_node.clone(),
                                merge_dependency_node,
                                branching_merging_proc_rest,
                                calc_alg_context,
                            );
                            // W6-DEFER[api]: newTaskList = newTask->append(newTaskList)
                            new_task_list = new_task;
                        }
                        if let Some(second_idx) = second_mergeable_it {
                            // W3-DEFER[api]: getUpToDateIndividual(*secondMergeableIt,calcAlgContext)
                            let second_distinct_indi_node: NodeId = Id::NONE;
                            let new_task = self.create_merge_branching_task(
                                process_indi,
                                con_pro_des,
                                &mut second_distinct_indi_node.clone(),
                                &mut merging_indi_node.clone(),
                                merge_dependency_node,
                                branching_merging_proc_rest,
                                calc_alg_context,
                            );
                            // W6-DEFER[api]: newTaskList = newTask->append(newTaskList)
                            new_task_list = new_task;

                            // continue past the second mergeable: spawn a branch per further mergeable distinct node
                            let mut mergeable_it = second_idx + 1;
                            while mergeable_it != dis_it_end {
                                let distinct_indi_id = it_distinct_merged_set[mergeable_it];

                                // W3-DEFER[api]: processIndi->getRoleSuccessorToIndividualLink(role,distinctIndiID,true)
                                let dis_indi_link: EdgeId = Id::NONE;
                                // KONCLUDE_ASSERT_X(disIndiLink, ...)
                                if dis_indi_link != Id::NONE {
                                    // W3-DEFER[api]: getSuccessorIndividual(processIndi,disIndiLink,calcAlgContext)
                                    let distinct_indi_node: NodeId = Id::NONE;

                                    // W3-DEFER[api]: createIndividualMergeCausingDescriptors(nullptr,distinctIndiNode,disIndiLink,conceptOpLinkerIt,calcAlgContext)
                                    let more_clash_descriptors: ClashDescId = Id::NONE;

                                    // W3-DEFER[api]: isIndividualNodesMergeable(distinctIndiNode,mergingIndiNode,moreClashDescriptors,calcAlgContext)
                                    let further_mergeable = false;
                                    if further_mergeable {
                                        let new_task = self.create_merge_branching_task(
                                            process_indi,
                                            con_pro_des,
                                            &mut distinct_indi_node.clone(),
                                            &mut merging_indi_node.clone(),
                                            merge_dependency_node,
                                            branching_merging_proc_rest,
                                            calc_alg_context,
                                        );
                                        // W6-DEFER[api]: newTaskList = newTask->append(newTaskList)
                                        new_task_list = new_task;
                                    }

                                    if merge_dependency_node != Id::NONE {
                                        // W3-DEFER[api]: mergeDependencyNode->addBranchClashes(moreClashDescriptors)
                                    }
                                }
                                mergeable_it += 1;
                            }
                        }

                        if distinct_count < tmp_cardinality {
                            // W3-DEFER[api]: createDistinctBranchingTask(processIndi,conProDes,mergingIndiNode,createNewNodesAsNominals,mergeDependencyNode,branchingMergingProcRest,calcAlgContext)  [unit 12]
                            let new_task: Id<SatisfiableCalculationTask> = Id::NONE;
                            // W6-DEFER[api]: newTaskList = newTask->append(newTaskList)
                            new_task_list = new_task;
                        }

                        // W6-DEFER[api]: calcAlgContext->getUsedTaskProcessorContext()
                        //   ->getTaskProcessorCommunicator()->communicateTaskCreation(newTaskList)
                        let _ = new_task_list;

                        // W3-DEFER[exceptions]: throw CCalculationStopProcessingException(true)
                        return false;
                    }
                } else {
                    // invalid link
                    // W3-DEFER[api]: branchingMergingProcRest->incRemainingValidMergingCandidateIndividualNodeCount()
                }
            }
        }
        false
    }

    /// Internal anchor for the unit-14 sibling `initializeMergingIndividualNodes`,
    /// referenced from `merge_merging_individual_nodes` before unit 14 is ported.
    /// W3-DEFER[api]: replaced by `self.initialize_merging_individual_nodes(...)` on reconcile.
    #[inline]
    fn initialize_merging_individual_nodes_anchor(&mut self) {}

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createMergeBranchingTask`.
    ///
    /// Spawns a fresh dependent satisfiable-calculation task whose process context
    /// localises `processIndiNode` / `distinctIndiNode` / `mergingIndiNode`, merges
    /// the distinct + merging nodes into it, re-queues the at-most concept restricted
    /// to the cloned restriction spec, optionally schedules an unsatisfiable-cache
    /// retrieval, prepares branched processing and sets the task's merging priority
    /// (cpp 15611–15673).
    ///
    /// W6-DEFER[api]: the entire body is the Task / Strategy / cache-retrieval
    /// subsystem (`createDependendBranchingTaskList`, `getProcessContext`,
    /// `createCalculationAlgorithmContext`, the `CObjectParameterizingAllocator` of
    /// the new restriction spec, `getUsedTaskPriorityStrategy`,
    /// `getUsedUnsatisfiableCacheRetrievalStrategy`) which is out of W3 scope; the
    /// faithful control flow is transcribed in comments and the result is the
    /// new-task id (`Id::NONE` until the Task subsystem lands).
    pub fn create_merge_branching_task(
        &mut self,
        process_indi_node: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        distinct_indi_node: &mut NodeId,
        merging_indi_node: &mut NodeId,
        merge_dependency_node: DependencyId,
        branching_merging_proc_rest: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Id<SatisfiableCalculationTask> {
        // W3-DEFER[macro]: STATINC(TASKINDINODEMERGEBRANCHCREATIONCOUNT,calcAlgContext)

        // W3-DEFER[api]: conProDes->getConceptDescriptor()
        let con_des: ConDescId = Id::NONE;
        let new_sat_calc_task = self.create_dependend_branching_task_list(1, calc_alg_context);

        // W6-DEFER[api]: processorContext = calcAlgContext->getUsedTaskProcessorContext();
        //   newProcessContext = newSatCalcTask->getProcessContext(processorContext);
        //   newCalcAlgContext = createCalculationAlgorithmContext(processorContext,newProcessContext,newSatCalcTask);
        //   newProcessingDataBox = newSatCalcTask->getProcessingDataBox();
        //   newTaskMemMan = newCalcAlgContext->getUsedProcessTaskMemoryAllocationManager();

        // W3-DEFER[api]: createNonDeterministicDependencyTrackPointBranch(mergeDependencyNode,false,newCalcAlgContext)
        let merge_non_det_dep_track_point: TrackPointId = Id::NONE;

        // W6-DEFER[api]: newBranchingMergingProcRest = CObjectParameterizingAllocator<...>::allocate(...);
        //   newBranchingMergingProcRest->initBranchingMergingProcessingRestriction(branchingMergingProcRest);
        let new_branching_merging_proc_rest: RestrictionSpecId = Id::NONE;

        // W6-DEFER[api]: newProcessTagger = newCalcAlgContext->getUsedProcessTagger();
        //   newProcessTagger->incBranchingTag(); newProcessTagger->incLocalizationTag();

        // W3-DEFER[api]: getLocalizedIndividual(distinctIndiNode,false,newCalcAlgContext)
        let new_loc_distinct_indi_node: NodeId = Id::NONE;
        // W3-DEFER[api]: getLocalizedIndividual(mergingIndiNode,false,newCalcAlgContext)
        let new_loc_merging_indi_node: NodeId = Id::NONE;

        // W3-DEFER[api]: newBranchingMergingProcRest->isDistinctSetNodeRelocated()
        let is_distinct_set_node_relocated = false;
        if is_distinct_set_node_relocated {
            // W3-DEFER[api]: newBranchingMergingProcRest->setDistinctSetNodeRelocated(false)
            // W3-DEFER[api]: newBranchingMergingProcRest->initMergingDependencyNode(mergeDependencyNode)
            // W3-DEFER[api]: newBranchingMergingProcRest->initDependencyTracker(mergeNonDetDepTrackPoint)
        }

        // W3-DEFER[api]: getMergedIndividualNodes(newLocDistinctIndiNode,newLocMergingIndiNode,mergeNonDetDepTrackPoint,newCalcAlgContext)  [unit 14]
        let loc_merged_indi_node: NodeId = Id::NONE;
        // W3-DEFER[api]: locMergedIndiNode->getIndividualNodeID() != newLocDistinctIndiNode->getIndividualNodeID()
        let merged_id_changed = false;
        if merged_id_changed {
            // W3-DEFER[api]: newBranchingMergingProcRest->getDistinctMergedNodesSet(true)
            //   ->remove(newLocDistinctIndiNode->getIndividualNodeID())
            //   ->insert(locMergedIndiNode->getIndividualNodeID());
            // W3-DEFER[api]: newBranchingMergingProcRest->setDistinctSetNodeRelocated(true)
        }

        // continue merging
        // W3-DEFER[api]: getLocalizedIndividual(processIndiNode,true,newCalcAlgContext)
        let loc_process_indi_node: NodeId = Id::NONE;
        // W3-DEFER[api]: locProcessIndiNode->getConceptProcessingQueue(true)
        let con_pro_queue: Cint64 = INVALID;
        // W3-DEFER[api]: addConceptRestrictedToProcessingQueue(conDes,mergeNonDetDepTrackPoint,conProQueu,locProcessIndiNode,true,newBranchingMergingProcRest,newCalcAlgContext)  [unit 3/10]

        // W6-DEFER[api]: calcAlgContext->getUsedUnsatisfiableCacheRetrievalStrategy()
        //   ->testUnsatisfiableCacheForMergedIndividualNodes(conProDes,locProcessIndiNode,locMergedIndiNode)
        let test_unsat_cache_merged = false;
        if test_unsat_cache_merged {
            // W3-DEFER[api]: addIndividualNodeForCacheUnsatisfiableRetrieval(locMergedIndiNode,newCalcAlgContext)
        }

        // W3-DEFER[api]: prepareBranchedTaskProcessing(locProcessIndiNode,newSatCalcTask,newCalcAlgContext)  [unit 1/driver]

        if let Some(task_priority_strategy) = calc_alg_context.base.used_task_priority_strategy() {
            let used_sat_calc_task = calc_alg_context.base.used_sat_calc_task;
            let new_task_priority = task_priority_strategy.get_priority_for_task_merging(
                &calc_alg_context.base.sat_calc_task_arena,
                new_sat_calc_task,
                used_sat_calc_task,
            );
            calc_alg_context
                .base
                .sat_calc_task_mut(new_sat_calc_task)
                .base
                .set_task_priority(new_task_priority);
        }

        new_sat_calc_task
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::qualifyMergingIndividualNodes`.
    ///
    /// The qualified-cardinality "choose" rule over the both-qualify candidate nodes
    /// (cpp 15677–15816): for each still-valid candidate it either (a) moves it onto
    /// the merging-candidate linker when it already carries one of the qualifying
    /// concepts positively, or (b) creates a QUALIFY dependency and — depending on
    /// the residual cardinality — deterministically adds the negated qualifier, or
    /// spawns the two-way qualify-choose branch tasks (positive/negative) and
    /// suspends via `CCalculationStopProcessingException`.
    pub fn qualify_merging_individual_nodes(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        branching_merging_proc_rest: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;
        // W3-DEFER[api]: calcAlgContext->getUsedProcessContext()
        let process_context: Cint64 = INVALID;
        // W3-DEFER[api]: conProDes->getConceptDescriptor()
        let con_des: ConDescId = Id::NONE;
        // W3-DEFER[api]: conDes->getConcept()
        let concept: ConceptId = Id::NONE;
        // W3-DEFER[api]: concept->getRole()
        let role: RoleId = Id::NONE;
        // W3-DEFER[api]: concept->getParameter() - 1*conDes->isNegated()
        let cardinality: Cint64 = 0;
        // W3-DEFER[api]: conProDes->getDependencyTrackPoint()
        let dep_track_point: TrackPointId = Id::NONE;
        // W3-DEFER[api]: concept->getOperandList()  (conceptOpLinkerIt — qualifying concepts)

        let mut qualifing = false;

        // W3-DEFER[api]: branchingMergingProcRest->getBothQualifyCandidateNodeLinker()
        let mut qualify_pos_neg_cand_linker: CandidateLinkerId = Id::NONE;
        while qualify_pos_neg_cand_linker != Id::NONE {
            // W3-DEFER[api]: qualifyPosNegCandLinker->getMergingIndividualNodeCandidate()
            let qualify_indi_node: NodeId = Id::NONE;

            // check still valid
            // W3-DEFER[api]: processIndi->getRoleSuccessorToIndividualLink(role,qualifyIndiNode,true)
            let link: EdgeId = Id::NONE;
            if link != Id::NONE {
                // W3-DEFER[api]: getUpToDateIndividual(qualifyIndiNode,calcAlgContext)  [unit 14]
                let up_qualify_indi_node: NodeId = Id::NONE;
                let mut negated = false;
                // W3-DEFER[api]: containsIndividualNodeConcepts(upQualifyIndiNode,conceptOpLinkerIt,&negated,calcAlgContext)  [helpers]
                let contains_qualifying_concepts = false;
                if contains_qualifying_concepts {
                    if !negated {
                        if cardinality <= 0 {
                            // clash (NB the C++ block here is intentionally empty)
                        }
                        // W6-DEFER[api]: qualifiedMovedCandLinker = CObjectParameterizingAllocator<...>::allocate(...);
                        //   qualifiedMovedCandLinker->initBranchingMergingIndividualNodeCandidate(qualifyPosNegCandLinker);
                        // W3-DEFER[api]: branchingMergingProcRest->addMergingCandidateNodeLinker(qualifiedMovedCandLinker)
                    }
                } else {
                    // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi,calcAlgContext)
                    // W3-DEFER[api]: createClashedIndividualLinkDescriptor(nullptr,link,link->getDependencyTrackPoint(),calcAlgContext)  [clash family]
                    let clash_des: ClashDescId = Id::NONE;

                    // create dependency
                    // W3-DEFER[api]: createQUALIFYDependency(processIndi,nullptr,branchingMergingProcRest->getDependencyTrackPoint(),calcAlgContext)  [unit 12/dep factory]
                    let qualify_dep_node: DependencyId = Id::NONE;
                    if qualify_dep_node != Id::NONE {
                        // W3-DEFER[api]: qualifyDepNode->addBranchClashes(clashDes)
                    }
                    // W3-DEFER[api]: branchingMergingProcRest->setBothQualifyCandidateNodeLinker(qualifyPosNegCandLinker->getNext())

                    if cardinality <= 0 {
                        self.applied_atmost_rule_count += 1;
                        // W3-DEFER[macro]: STATINC(INDINODEQUALIFYCHOOCECOUNT,calcAlgContext)
                        // W3-DEFER[api]: createNonDeterministicDependencyTrackPointBranch(qualifyDepNode,true,calcAlgContext)
                        let new_dependency_track_point: TrackPointId = Id::NONE;

                        // W3-DEFER[api]: getLocalizedIndividual(upQualifyIndiNode,false,calcAlgContext)
                        let loc_qualify_indi_node: NodeId = Id::NONE;
                        // qualify only negated
                        // W3-DEFER[api]: addConceptsToIndividual(conceptOpLinkerIt,true,locQualifyIndiNode,newDependencyTrackPoint,false,true,nullptr,calcAlgContext)  [helpers]
                        // W3-DEFER[api]: addIndividualToProcessingQueue(locQualifyIndiNode,calcAlgContext)

                        // W6-DEFER[api]: calcAlgContext->getUsedUnsatisfiableCacheRetrievalStrategy()
                        //   ->testUnsatisfiableCacheForQualifiedIndividualNodes(conProDes,processIndi,locQualifyIndiNode)
                        let test_unsat_cache_qualified = false;
                        if test_unsat_cache_qualified {
                            // W3-DEFER[api]: addIndividualNodeForCacheUnsatisfiableRetrieval(locQualifyIndiNode,calcAlgContext)
                        }
                    } else {
                        self.applied_atmost_rule_count += 1;
                        // W3-DEFER[macro]: STATINC(INDINODEQUALIFYCHOOCECOUNT,calcAlgContext)

                        qualifing = true;

                        let new_task_list =
                            self.create_dependend_branching_task_list(2, calc_alg_context);
                        // W6-DEFER[api]: processorContext = calcAlgContext->getUsedTaskProcessorContext();

                        // iterate the two created tasks (pos / neg qualifier branch)
                        let mut new_task_it: Id<SatisfiableCalculationTask> = new_task_list;
                        let mut branch_number: Cint64 = 1;
                        let mut qual_neg = true;
                        let mut branching_merging_proc_rest_it = branching_merging_proc_rest;
                        while new_task_it != Id::NONE {
                            // W3-DEFER[macro]: STATINC(TASKQUALIFYCHOOSEBRANCHCREATIONCOUNT,calcAlgContext)

                            // W6-DEFER[api]: newProcessContext = newSatCalcTask->getProcessContext(processorContext);
                            //   newCalcAlgContext = createCalculationAlgorithmContext(...);
                            //   newProcessingDataBox = newSatCalcTask->getProcessingDataBox();
                            //   newProcessTagger = newCalcAlgContext->getUsedProcessTagger();
                            //   newProcessTagger->incBranchingTag(); newProcessTagger->incLocalizationTag();

                            // W3-DEFER[api]: getLocalizedIndividual(processIndi,false,newCalcAlgContext)
                            let new_loc_indi_node: NodeId = Id::NONE;
                            // W3-DEFER[api]: newLocIndiNode->getConceptProcessingQueue(true)
                            let new_con_proc_queue: Cint64 = INVALID;

                            // W3-DEFER[api]: getLocalizedIndividual(upQualifyIndiNode,false,newCalcAlgContext)
                            let new_loc_qualify_indi_node: NodeId = Id::NONE;

                            // create dependency track point
                            // W3-DEFER[api]: createNonDeterministicDependencyTrackPointBranch(qualifyDepNode,false,newCalcAlgContext)
                            let new_dependency_track_point: TrackPointId = Id::NONE;

                            if !qual_neg {
                                // W6-DEFER[api]: newTaskMemMan = newCalcAlgContext->getUsedProcessTaskMemoryAllocationManager();
                                //   newBranchingMergingProcRest = CObjectParameterizingAllocator<...>::allocate(...);
                                //   newBranchingMergingProcRest->initBranchingMergingProcessingRestriction(branchingMergingProcRest);
                                //   qualifiedMovedCandLinker = CObjectParameterizingAllocator<...>::allocate(...);
                                //   qualifiedMovedCandLinker->initBranchingMergingIndividualNodeCandidate(qualifyPosNegCandLinker);
                                //   newBranchingMergingProcRest->addMergingCandidateNodeLinker(qualifiedMovedCandLinker);
                                let new_branching_merging_proc_rest: RestrictionSpecId = Id::NONE;
                                branching_merging_proc_rest_it = new_branching_merging_proc_rest;
                            }

                            // ATMOST reapplication in new tasks
                            // W3-DEFER[api]: addConceptRestrictedToProcessingQueue(conDes,depTrackPoint,newConProcQueue,newLocIndiNode,true,branchingMergingProcRest,newCalcAlgContext)  [unit 3/10]

                            // qualify
                            // W3-DEFER[api]: addConceptsToIndividual(conceptOpLinkerIt,qualNeg,newLocQualifyIndiNode,newDependencyTrackPoint,false,true,nullptr,newCalcAlgContext)
                            // W3-DEFER[api]: addIndividualToProcessingQueue(newLocQualifyIndiNode,newCalcAlgContext)

                            // W6-DEFER[api]: calcAlgContext->getUsedUnsatisfiableCacheRetrievalStrategy()
                            //   ->testUnsatisfiableCacheForQualifiedIndividualNodes(conProDes,newLocIndiNode,newLocQualifyIndiNode)
                            let test_unsat_cache_qualified = false;
                            if test_unsat_cache_qualified {
                                // W3-DEFER[api]: addIndividualNodeForCacheUnsatisfiableRetrieval(newLocQualifyIndiNode,newCalcAlgContext)
                            }

                            // W3-DEFER[api]: prepareBranchedTaskProcessing(newLocIndiNode,newTaskIt,newCalcAlgContext)

                            if let Some(task_priority_strategy) =
                                calc_alg_context.base.used_task_priority_strategy()
                            {
                                let used_sat_calc_task = calc_alg_context.base.used_sat_calc_task;
                                let new_task_priority = task_priority_strategy
                                    .get_priority_for_task_qualifing(
                                        &calc_alg_context.base.sat_calc_task_arena,
                                        new_task_it,
                                        used_sat_calc_task,
                                        qual_neg,
                                    );
                                calc_alg_context
                                    .base
                                    .sat_calc_task_mut(new_task_it)
                                    .base
                                    .set_task_priority(new_task_priority);
                            }

                            branch_number += 1;
                            qual_neg = !qual_neg;
                            new_task_it =
                                calc_alg_context.base.sat_calc_task(new_task_it).get_next();
                        }

                        // W6-DEFER[api]: processorContext->getTaskProcessorCommunicator()->communicateTaskCreation(newTaskList)
                        // W3-DEFER[exceptions]: throw CCalculationStopProcessingException(true)
                        return qualifing;
                    }
                }
            }

            // W3-DEFER[api]: qualifyPosNegCandLinker = qualifyPosNegCandLinker->getNext()
            qualify_pos_neg_cand_linker = Id::NONE;
        }
        // W3-DEFER[api]: branchingMergingProcRest->setBothQualifyCandidateNodeLinker(nullptr)
        qualifing
    }
}
