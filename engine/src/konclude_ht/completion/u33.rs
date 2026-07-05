//! `completion::u33` — Generic helpers / accessors / label tests family, batch
//! (port unit #33 of 36).
//!
//! Faithful port of the 14 methods that the manifest (`01-completion-methods.md`,
//! "Unit 33") groups under the REPRESENTATIVE variable-binding-path propagation
//! and the PROPAGATION-BINDING propagation subsystem of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) per method are noted on each item.
//!
//! Methods (cpp order):
//!   * `tryCompletionGraphReuse`                          [9257–9381]
//!   * `isRestrictedTopObjectPropertyPropagation`         [9617–9631]
//!   * `areRepresentativesJoinable`                       [10650–10669]
//!   * `createCommonJoiningAll`                           [10672–10715]
//!   * `createCommonJoiningKeyMap`                        [10719–10767]
//!   * `propagateRepresentativeToSuccessor`               [11050–11117]
//!   * `updateRepresentativePropagationSet`               [11260–11375]
//!   * `propagateRepresentative`                          [11379–11387]
//!   * `requiresRepresentativePropagation`                [11390–11444]
//!   * `propagatePropagationBindingsToSuccessor`          [13294–13355]
//!   * `propagateInitialPropagationBindingsToSuccessor`   [13362–13390]
//!   * `propagateFreshPropagationBindingsToSuccessor`     [13395–13463]
//!   * `propagatePropagationBindings`                     [13626–13688]
//!   * `propagateInitialPropagationBindings`              [13773–13801]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` out/in-out
//! pointer-references become `&mut NodeId`; a plain `CIndividualProcessNode*`
//! value parameter becomes `NodeId`; `CConceptDescriptor*` → `ConDescId`;
//! `CConceptProcessDescriptor*&` → `&mut ConProcDescId`; `CConcept*` → `ConceptId`;
//! `CIndividualLinkEdge*` → `EdgeId`; `CDependencyTrackPoint*` → `TrackPointId`;
//! `CDependency*` (additional-dependency back-edge) → `DepLinkId`. The per-test
//! arenas are reached through the context as `calc_alg_context.process_context()`
//! / `_mut()`, the databox as `calc_alg_context.processing_data_box{,_mut}()`.
//!
//! KONCLUDE-PORT-NOTE[api]: this unit is the most deeply REPRESENTATIVE/
//! PROPAGATION-BINDING-dependent of the W3 helper batches. Its bodies are driven
//! start-to-finish by satellite data types that are NOT yet ported (the W2/W6
//! representative + propagation-binding subsystem), namely:
//!   * `CRepresentativeVariableBindingPathSetData` + its `MigrateData`,
//!     `CRepresentativeVariableBindingPathMap` / `…MapData`,
//!     `CRepresentativeContainingMap`, `CRepresentativePropagationSet`,
//!     `CRepresentativePropagationDescriptor`,
//!     `CConceptRepresentativePropagationSetHash`,
//!     `CRepresentativeJoiningCommonKeyMap` / `…CommonKeyData`,
//!     `CRepresentativeJoiningAllDataExtension`,
//!     `CRepresentativeVariableBindingPathSetJoiningKeyMap` / `…KeyDataMap`,
//!     `CVariableBindingPath` — the `process::stubs` markers
//!     `RepresentativeVariableBindingPathSetHash` / `…JoiningKeyHash` / `…Hash`
//!     name only the per-databox HASHES; the per-set/per-descriptor/per-map data
//!     classes have no arena yet;
//!   * `CPropagationBindingSet`, `CPropagationBindingDescriptor`,
//!     `CPropagationBindingMap` / `…MapData`, `CPropagationBinding`,
//!     `CConceptPropagationBindingSetHash` (process::stubs
//!     `ConceptPropagationBindingSetHash` is a zero-size marker),
//!     `CPropagationBindingReapplyConceptDescriptor`, `CCondensedReapplyQueue` /
//!     `…Iterator`;
//!   * the node-level satellite ACCESSORS these walk
//!     (`getReapplyConceptLabelSet`, `getConceptRepresentativePropagationSetHash`,
//!     `getConceptPropagationBindingSetHash`, `getConceptProcessingQueue`,
//!     `getProcessInitializingConceptLinker`) are not yet on `process::node`;
//!   * the Cache subtree (`CReuseCompletionGraphCacheHandler` /
//!     `CReuseCompletionGraphCacheEntry`, `self.reuse_comp_graph_cache_handler`,
//!     a zero-size `Id` stub) and the Task-creation / dependency-track-point
//!     branching machinery (`createDependendBranchingTaskList`,
//!     `createCalculationAlgorithmContext`,
//!     `createNonDeterministicDependencyTrackPointBranch`, the
//!     `CCalculationStopProcessingException` control-flow throw — all later units
//!     / W6).
//!
//! Where a method NESTS a sibling already ported in another unit
//! (`hasCommonVariableBindings` u11, `reapplyConceptUpdatedRepresentative` u10,
//! `addConceptToIndividualReturnConceptDescriptor` /
//! `addConceptPreprocessedToProcessingQueue` / `addIndividualToProcessingQueue` /
//! `applyReapplyQueueConcepts` / `setIndividualNodeConceptLabelSetModified` /
//! `getLocalizedIndividual` core units, the `create*Dependency` factory wrappers
//! u29), the call is named in the PORT-PENDING outline so a later wave wires it
//! without re-reading the source. Following the porting convention each method is
//! kept `// PORT-PENDING` with the faithful signature + a structural transcription
//! of the C++ and returns the C++ default of its branch (`false` / `true` / no-op
//! void). Logic is documented, never silently dropped; the `unused_variables`
//! allow keeps the faithful parameter names as anchors.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, VariableId};
use super::super::process::binding_hash::ConceptPropagationBindingSetHash;
use super::super::process::propagation_binding::{
    PropagationBindingDescriptor, PropagationBindingDescriptorId, PropagationBindingMapData,
    PropagationBindingSetId,
};
use super::super::process::representative::{
    RepresentativeJoiningAllDataExtension, RepresentativeJoiningCommonKeyData,
    RepresentativeJoiningCommonKeyMap, RepresentativePropagationDescriptor,
    RepresentativePropagationDescriptorId, RepresentativePropagationSet,
    RepresentativePropagationSetId, RepresentativeVariableBindingPathSetData,
    RepresentativeVariableBindingPathSetDataId, RepresentativeVariableBindingPathSetHash,
    RepresentativeVariableBindingPathSetJoiningKeyMap,
    RepresentativeVariableBindingPathSetMigrateDataId,
};
use super::super::process::varbind::RepresentativeVariableBindingPathMapData;
use super::super::process::varbind::VariableBindingPath;
use super::super::process::{
    ConDescId, ConProcDescId, DepLinkId, EdgeId, LabelSetId, NodeId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;

/// KONCLUDE-PORT-NOTE[ownership]: `CDependency*` additional-dependency chains are
/// represented by the folded dependency-link spine used by the dependency factory.
type DependencyHandle = DepLinkId;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // UN-DEFER WAVE STATUS (node-resolution keystone landed): the representative +
    // propagation-binding ARENAS now exist (`alloc_rep_var_bind_path_set_data` /
    // `alloc_rep_prop_des` / `alloc_rep_prop_set` / `alloc_prop_binding{,_des,_set}`),
    // but every body in this unit remains blocked on shared pieces that are NOT yet
    // present, so all 14 methods stay PORT-PENDING. Concretely:
    //
    //   LIVE SINCE W28/W51: the representative / propagation-binding dependency
    //     wrappers are present under their Rust names
    //     (`create_representative_all_dependency`,
    //     `create_resolve_representative_dependency`,
    //     `create_propagate_bindings_successor_dependency`,
    //     `create_bindpropagateand_dependency`, `create_propagate_binding_dependency`).
    //     The C++ `CDependency*` additional-dependency back-edge is carried as the
    //     folded `DepLinkId` dependency-link spine already accepted by the factory
    //     wrappers.
    //   LIVE SINCE W51-W57: u11 representative-map siblings
    //     `has_common_variable_bindings` and `get_joined_variable_binding_path`,
    //     plus the representative satellite typed accessors
    //     (`getMigrateData` / `getRepresentativeVariableBindingPathMap` / iterator
    //     snapshots / `getVariableBindingPath` / `getRepresentativeContainingMap` /
    //     `RepresentativeVariableBindingPathSetHash::get…`). The remaining blockers
    //     for the older PORT-PENDING bodies are the still-deferred representative
    //     join/cache/task call sites that have no faithful local substrate yet.
    // The propagation-binding SET/MAP types themselves (`process/propagation_binding.rs`)
    // are arena-backed, including the reapply-concept hash and iterator.
    // =======================================================================
    // Completion-graph reuse (cpp 9257–9381).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::tryCompletionGraphReuse`.
    /// cpp 9257–9381.
    ///
    /// If the reuse-completion-graph cache (W6) yields an entry for `processIndi`
    /// matching the configured deterministic/non-deterministic reuse policy, this
    /// builds 1 (deterministic) or 2 (non-deterministic) dependent branching tasks
    /// — the first reusing the cached graph (re-seeding a fresh individual with the
    /// node's process-initializing concepts + the ontology top concept), the second
    /// a localized fallback — communicates them, and aborts the current test by
    /// throwing `CCalculationStopProcessingException(true)`.
    pub fn try_completion_graph_reuse(
        &mut self,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // The substrate-portable head guard:
        //   if (mReuseCompGraphCacheHandler && mConfCompGraphReuseCacheRetrieval) { ... }
        // KONCLUDE-PORT-NOTE[api]: `self.reuse_comp_graph_cache_handler` is a
        // zero-size W6 `Id` stub (always `Id::NONE` today) and the body cannot
        // proceed without the Cache subtree + Task machinery, so the whole method
        // is held PORT-PENDING rather than porting only the guard.
        //
        // PORT-PENDING: faithful transcription of cpp 9257–9381. Outline:
        //
        //   if !(reuse_comp_graph_cache_handler.is_some() && self.conf_comp_graph_reuse_cache_retrieval): return;
        //   STATINC(COMPLETIONGRAPHREUSECACHERETRIEVALCOUNT, ctx);
        //   self.compl_graph_reuse_cache_retrieval.start();                                   // timer
        //   reuseEntry = mReuseCompGraphCacheHandler.getReuseCompletionGraphEntry(            // W6-DEFER[api]
        //       process_indi, &minimalCompletionGraph, &minimalCompletionGraphConnection, ctx);
        //   STATINCM(TIMECOMPLETIONGRAPHREUSERETRIVAL, timer.elapsed(), ctx);
        //   if reuseEntry.is_none(): STATINC(...RETRIEVALFAILEDCOUNT, ctx); return;
        //   STATINC(...RETRIEVALSUCCESSCOUNT, ctx);
        //   initConceptLinkerIt = process_indi.getProcessInitializingConceptLinker();         // node accessor (unported)
        //   processorContext    = ctx.getUsedTaskProcessorContext();                          // scheduler (opaque)
        //   reuseSatCalcTask    = reuseEntry.getJobInstantiation();                            // Task (W6-DEFER)
        //   reuseProcessingDataBox = reuseSatCalcTask.getProcessingDataBox();
        //   reuseBranchingTag   = reuseProcessingDataBox.getProcessContext()
        //                            .getUsedProcessTagger().getCurrentBranchingTag();
        //   deterministicReuse  = reuseBranchingTag == 0 && minimalCompletionGraph && minimalCompletionGraphConnection;
        //   if !( (!deterministicReuse && self.conf_comp_graph_non_deterministic_reuse)
        //         || (deterministicReuse && self.conf_comp_graph_deterministic_reuse) ): return;
        //   taskCreationCount = if deterministicReuse { STATINC(...REUSINGDETCOUNT); 1 } else { STATINC(...REUSINGNONDETCOUNT); 2 };
        //   newTaskList = self.create_dependend_branching_task_list(taskCreationCount, ctx);   // u29 / Task (W6-DEFER)
        //   reuseDepNode = self.create_reuse_completion_graph_dependency(process_indi, NONE, NONE, ctx); // u29
        //   newTaskIt = newTaskList;
        //   for i in 0..taskCreationCount {
        //       newSatCalcTask = newTaskIt;
        //       reusingAlternative = i == 0;
        //       if reusingAlternative {
        //           newDepTrackPoint = if deterministicReuse {
        //               ctx.base_dependency_node().getContinueDependencyTrackPoint()
        //           } else {
        //               self.create_non_deterministic_dependency_track_point_branch(reuseDepNode, false, ctx) // u29
        //           };
        //           newProcessingDataBox = newSatCalcTask.getProcessingDataBox();
        //           newProcessingDataBox.initProcessingDataBox(reuseProcessingDataBox);
        //           newProcessContext   = newSatCalcTask.getProcessContext(processorContext);
        //           newCalcAlgContext   = self.create_calculation_algorithm_context(processorContext, newProcessContext, newSatCalcTask); // u01
        //           newProcessTagger    = newCalcAlgContext.getUsedProcessTagger();
        //           if !deterministicReuse {
        //               newProcessTagger.incBranchingTag();
        //               if !minimalCompletionGraphConnection { newProcessingDataBox.setMaximumDeterministicBranchTag(-1); }
        //           }
        //           newProcessTagger.incLocalizationTag();
        //           indiNodeVec = newProcessingDataBox.getIndividualProcessNodeVector();
        //           nextIndiID  = indiNodeVec.getItemMaxIndex() + 1;
        //           newIndi = newProcessContext.alloc_node(IndividualProcessNode::new(newProcessContext)); // arena alloc
        //           newIndi.setIndividualNodeID(nextIndiID);
        //           newIndi.addProcessingRestrictionFlags(PRFINVALIDBLOCKINGORCACHING);
        //           newProcessingDataBox.setConstructedIndividualNode(newIndi);
        //           indiNodeVec.setData(nextIndiID, newIndi);
        //           self.add_concepts_to_individual(initConceptLinkerIt, false, newIndi, newDepTrackPoint, false, true, NONE, newCalcAlgContext);
        //           topConcept = ctx.processing_data_box().getOntologyTopConcept();
        //           self.add_concept_to_individual(topConcept, false, newIndi, newDepTrackPoint, false, true, newCalcAlgContext);
        //           self.prepare_branched_task_processing(newIndi, newSatCalcTask, newCalcAlgContext);
        //       } else {
        //           newProcessContext = newSatCalcTask.getProcessContext(processorContext);
        //           newCalcAlgContext = self.create_calculation_algorithm_context(processorContext, newProcessContext, newSatCalcTask);
        //           newLocIndiNode    = self.get_localized_individual(process_indi, false, newCalcAlgContext);
        //           self.prepare_branched_task_processing(newLocIndiNode, newSatCalcTask, newCalcAlgContext);
        //       }
        //       newTaskPriority = ctx.getUsedTaskPriorityStrategy().getPriorityForTaskReusing(
        //           newSatCalcTask, ctx.getUsedSatisfiableCalculationTask(), reusingAlternative);
        //       newSatCalcTask.setTaskPriority(newTaskPriority);
        //       newTaskIt = newTaskIt.getNext();
        //   }
        //   processorContext.getTaskProcessorCommunicator().communicateTaskCreation(newTaskList); // W6-DEFER[threading]
        //   throw CCalculationStopProcessingException(true);                                       // W3-DEFER[exceptions] — early return
    }

    // =======================================================================
    // Restricted top-object-property propagation test (cpp 9617–9631).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isRestrictedTopObjectPropertyPropagation`.
    /// cpp 9617–9631.
    ///
    /// Returns true when the answering propagation-steering controller marks
    /// `concept` as a restricted-top propagation and `processIndi`/`destIndi` are
    /// the universal-connection individual or both/destination nominal nodes
    /// (the universal-connection-edge propagation must then be suppressed).
    pub fn is_restricted_top_object_property_propagation(
        &mut self,
        process_indi: &mut NodeId,
        dest_indi: &mut NodeId,
        concept: ConceptId,
        negated: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 9617–9631. Outline:
        //
        //   answererMessageAdapter = ctx.getSatisfiableCalculationTask()
        //       .getSatisfiableAnswererBindingPropagationAdapter();                  // W6-DEFER[api] answering adapter
        //   if let Some(adapter) = answererMessageAdapter {
        //       propagationSteeringController = adapter.getAnswererPropagationSteeringController();
        //       if let Some(controller) = propagationSteeringController {
        //           if controller.isRestrictedTopPropagation(concept) {
        //               univConnIndiId = ctx.processing_data_box().getOntology()
        //                   .getABox().getUniversalConnectionIndividualID();          // ontology (unported ABox)
        //               if ctx.node(*process_indi).individual_node_id() == -univConnIndiId
        //                   || ctx.node(*dest_indi).individual_node_id() == -univConnIndiId
        //                   || (ctx.node(*process_indi).nominal_individual() && ctx.node(*dest_indi).nominal_individual())
        //                   || ctx.node(*dest_indi).nominal_individual() {
        //                   return true;
        //               }
        //           }
        //       }
        //   }
        // KONCLUDE-PORT-NOTE[api]: the answering binding-propagation adapter +
        // steering controller live in the answering subsystem (W6); with no
        // adapter the C++ falls through to the trailing `return false`.
        false
    }

    // =======================================================================
    // Representative joinability + common-joining map construction
    // (cpp 10650–10767).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::areRepresentativesJoinable`.
    /// cpp 10650–10669.
    ///
    /// Quick-fail pre-check before a representative join: when both single-variable
    /// representative binding paths share no common variable bindings, the join
    /// cannot produce anything (increments `mStatRepresentativeJoinQuickFailCount`
    /// and returns false). Otherwise true.
    ///
    pub fn are_representatives_joinable(
        &mut self,
        process_indi: &mut NodeId,
        left_rep_data: RepresentativeVariableBindingPathSetDataId,
        right_rep_data: RepresentativeVariableBindingPathSetDataId,
        var_linker: &[VariableId],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let left_rep_mig_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            calc_alg_context.process_context_mut(),
            left_rep_data,
            false,
        );
        let right_rep_mig_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            calc_alg_context.process_context_mut(),
            right_rep_data,
            false,
        );
        if !var_linker.is_empty() && left_rep_mig_data.is_some() && right_rep_mig_data.is_some() {
            let (left_rep_var_bind_map, right_rep_var_bind_map) = {
                let pc = calc_alg_context.process_context();
                (
                    pc.rep_var_bind_path_set_migrate_data(left_rep_mig_data)
                        .get_representative_variable_binding_path_map()
                        .clone(),
                    pc.rep_var_bind_path_set_migrate_data(right_rep_mig_data)
                        .get_representative_variable_binding_path_map()
                        .clone(),
                )
            };
            let left_var_bind_path = left_rep_var_bind_map
                .map
                .keys()
                .min()
                .map(|key| {
                    left_rep_var_bind_map
                        .value(*key)
                        .get_variable_binding_path()
                })
                .unwrap_or(Id::NONE);
            let right_var_bind_path = right_rep_var_bind_map
                .map
                .keys()
                .min()
                .map(|key| {
                    right_rep_var_bind_map
                        .value(*key)
                        .get_variable_binding_path()
                })
                .unwrap_or(Id::NONE);
            if left_var_bind_path.is_some()
                && right_var_bind_path.is_some()
                && VariableBindingPath::get_variable_binding_count(
                    calc_alg_context.process_context(),
                    left_var_bind_path,
                ) == 1
                && VariableBindingPath::get_variable_binding_count(
                    calc_alg_context.process_context(),
                    right_var_bind_path,
                ) == 1
                && !self.has_common_variable_bindings(
                    process_indi,
                    &left_rep_var_bind_map,
                    &right_rep_var_bind_map,
                    calc_alg_context,
                )
            {
                self.stat_representative_join_quick_fail_count += 1;
                return false;
            }
        }
        true
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createCommonJoiningAll`.
    /// cpp 10672–10715.
    ///
    /// Materialises the FULL cross-product join of a common-joining-key map: for
    /// every common key, for every left/right binding-path pair, joins the two
    /// variable-binding paths (`getJoinedVariableBindingPath`, u11) and records the
    /// merged path in the left/right resolve maps + the new representative's own
    /// resolve map, then registers the freshly created representative set data in
    /// the databox hash and stores it on the all-data extension.
    ///
    pub fn create_common_joining_all(
        &mut self,
        rep_join_common_key_map: &RepresentativeJoiningCommonKeyMap,
        join_all_ext_data: &mut RepresentativeJoiningAllDataExtension,
        left_rep_data: RepresentativeVariableBindingPathSetDataId,
        right_rep_data: RepresentativeVariableBindingPathSetDataId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> RepresentativeVariableBindingPathSetDataId {
        let localization_tag = calc_alg_context
            .process_context()
            .used_process_tagger()
            .get_current_localization_tag();
        let rep_data = calc_alg_context
            .process_context_mut()
            .alloc_rep_var_bind_path_set_data(RepresentativeVariableBindingPathSetData::new(
                INVALID,
                localization_tag,
            ));
        let rep_id = calc_alg_context
            .processing_data_box_mut()
            .next_representative_variable_binding_path_id(true);
        calc_alg_context
            .process_context_mut()
            .rep_var_bind_path_set_data_mut(rep_data)
            .init_representative_variable_binding_path_data(None)
            .set_representative_id(rep_id)
            .set_migratable(false)
            .inc_use_count(1)
            .inc_share_count(1);

        let rep_migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            calc_alg_context.process_context_mut(),
            rep_data,
            true,
        );

        let mut common_keys = rep_join_common_key_map
            .map
            .keys()
            .copied()
            .collect::<Vec<_>>();
        common_keys.sort_unstable();
        for joining_key in common_keys {
            let common_key_data = rep_join_common_key_map
                .value(joining_key)
                .expect("common joining-key data");
            let left_paths = common_key_data
                .get_left_joining_data_map()
                .map
                .values()
                .copied()
                .collect::<Vec<_>>();
            let right_paths = common_key_data
                .get_right_joining_data_map()
                .map
                .values()
                .copied()
                .collect::<Vec<_>>();
            for var_bind_path1 in &left_paths {
                for var_bind_path2 in &right_paths {
                    let merged_var_bind_path = self.get_joined_variable_binding_path(
                        *var_bind_path1,
                        *var_bind_path2,
                        calc_alg_context,
                    );
                    let merged_prop_id = calc_alg_context
                        .process_context()
                        .vbpath(merged_var_bind_path)
                        .get_propagation_id();

                    let mut left_map_data =
                        RepresentativeVariableBindingPathMapData::new_with_resolve(
                            merged_var_bind_path,
                            *var_bind_path1,
                            left_rep_data,
                        );
                    left_map_data.resolve_rep_var_bind_path_set_data_id = calc_alg_context
                        .process_context()
                        .rep_var_bind_path_set_data(left_rep_data)
                        .get_representative_id();
                    join_all_ext_data
                        .get_left_resolve_variable_binding_path_map(true)
                        .expect("left resolve map")
                        .insert(merged_prop_id, left_map_data);

                    let mut right_map_data =
                        RepresentativeVariableBindingPathMapData::new_with_resolve(
                            merged_var_bind_path,
                            *var_bind_path2,
                            right_rep_data,
                        );
                    right_map_data.resolve_rep_var_bind_path_set_data_id = calc_alg_context
                        .process_context()
                        .rep_var_bind_path_set_data(right_rep_data)
                        .get_representative_id();
                    join_all_ext_data
                        .get_right_resolve_variable_binding_path_map(true)
                        .expect("right resolve map")
                        .insert(merged_prop_id, right_map_data);

                    let mut joined_map_data = RepresentativeVariableBindingPathMapData::new(
                        merged_var_bind_path,
                        rep_data,
                    );
                    joined_map_data.resolve_rep_var_bind_path_set_data_id = rep_id;
                    calc_alg_context
                        .process_context_mut()
                        .rep_var_bind_path_set_migrate_data_mut(rep_migrate_data)
                        .get_representative_variable_binding_path_map_mut()
                        .insert(merged_prop_id, joined_map_data);
                }
            }
        }

        // W3-DEFER[macro]: ++mStatRepresentativeJoinCombinesCount.
        calc_alg_context
            .process_context_mut()
            .rep_var_bind_path_set_migrate_data_mut(rep_migrate_data)
            .get_representative_containing_map_mut()
            .insert_contained_representative(rep_id, rep_data, false);
        calc_alg_context
            .process_context_mut()
            .rep_var_bind_path_set_data_mut(rep_data)
            .add_key_signature_value(rep_id);
        let rep_var_bind_path_set_hash =
            calc_alg_context.representative_variable_binding_path_set_hash(true);
        RepresentativeVariableBindingPathSetHash::insert_representative_variable_binding_path_set_data(
            calc_alg_context.process_context_mut(),
            rep_var_bind_path_set_hash,
            rep_data,
        );
        join_all_ext_data.set_representative_variable_binding_path_set_data(rep_data);
        rep_data
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createCommonJoiningKeyMap`.
    /// cpp 10719–10767.
    ///
    /// Builds the intersection (`repJoinCommonKeyMap`) of two joining-key maps,
    /// orienting smaller-onto-larger (recursing with swapped left/right when the
    /// second map is smaller) and switching between a direct-lookup pass and a
    /// merge-walk pass on the `mMapComparisonDirectLookupFactor` heuristic.
    ///
    pub fn create_common_joining_key_map(
        &mut self,
        rep_join_common_key_map: &mut RepresentativeJoiningCommonKeyMap,
        first_joining_key_map: &RepresentativeVariableBindingPathSetJoiningKeyMap,
        first_rep_data: RepresentativeVariableBindingPathSetDataId,
        sec_joining_key_map: &RepresentativeVariableBindingPathSetJoiningKeyMap,
        sec_rep_data: RepresentativeVariableBindingPathSetDataId,
        first_left: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = (first_rep_data, sec_rep_data);

        if sec_joining_key_map.count() < first_joining_key_map.count() {
            self.create_common_joining_key_map(
                rep_join_common_key_map,
                sec_joining_key_map,
                sec_rep_data,
                first_joining_key_map,
                first_rep_data,
                !first_left,
                calc_alg_context,
            );
        }

        if first_joining_key_map.count() * self.map_comparison_direct_lookup_factor
            < sec_joining_key_map.count()
        {
            for (joining_key, first_data) in &first_joining_key_map.map {
                let first_joining_data_map =
                    first_data.get_representative_variable_binding_path_set_joining_key_data_map();
                let sec_joining_data_map =
                    sec_joining_key_map.get_joining_key_data_map_existing(*joining_key);
                if let (Some(first_joining_data_map), Some(sec_joining_data_map)) =
                    (first_joining_data_map, sec_joining_data_map)
                {
                    let (left_joining_data_map, right_joining_data_map) = if first_left {
                        (first_joining_data_map.clone(), sec_joining_data_map.clone())
                    } else {
                        (sec_joining_data_map.clone(), first_joining_data_map.clone())
                    };
                    rep_join_common_key_map.insert(
                        *joining_key,
                        RepresentativeJoiningCommonKeyData::new(
                            left_joining_data_map,
                            right_joining_data_map,
                        ),
                    );
                }
            }
        } else {
            let mut first_keys = first_joining_key_map
                .map
                .keys()
                .copied()
                .collect::<Vec<_>>();
            first_keys.sort_unstable();
            let mut sec_keys = sec_joining_key_map.map.keys().copied().collect::<Vec<_>>();
            sec_keys.sort_unstable();
            let mut first_index = 0;
            let mut sec_index = 0;
            while first_index < first_keys.len() && sec_index < sec_keys.len() {
                let joining_key1 = first_keys[first_index];
                let joining_key2 = sec_keys[sec_index];
                if joining_key1 == joining_key2 {
                    let first_joining_data_map =
                        first_joining_key_map.get_joining_key_data_map_existing(joining_key1);
                    let sec_joining_data_map =
                        sec_joining_key_map.get_joining_key_data_map_existing(joining_key2);
                    if let (Some(first_joining_data_map), Some(sec_joining_data_map)) =
                        (first_joining_data_map, sec_joining_data_map)
                    {
                        let (left_joining_data_map, right_joining_data_map) = if first_left {
                            (first_joining_data_map.clone(), sec_joining_data_map.clone())
                        } else {
                            (sec_joining_data_map.clone(), first_joining_data_map.clone())
                        };
                        rep_join_common_key_map.insert(
                            joining_key1,
                            RepresentativeJoiningCommonKeyData::new(
                                left_joining_data_map,
                                right_joining_data_map,
                            ),
                        );
                    }
                    first_index += 1;
                    sec_index += 1;
                } else if joining_key1 < joining_key2 {
                    first_index += 1;
                } else if joining_key2 < joining_key1 {
                    sec_index += 1;
                }
            }
        }
    }

    // =======================================================================
    // Representative propagation to successor + set maintenance
    // (cpp 11050–11444).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateRepresentativeToSuccessor`.
    /// cpp 11050–11117.
    ///
    /// Propagates the representative variable-binding paths attached to `conDes`'s
    /// concept on `processIndi` across `restLink` onto each operand concept of
    /// `succIndi`: for each operand it adds the binding concept (creating a
    /// REPRESENTATIVEALL dependency the first time), and either seeds or updates the
    /// successor representative-propagation set (`propagateRepresentative` /
    /// `requiresRepresentativePropagation`), re-applying any pending reapply queue;
    /// if anything changed the successor is re-queued.
    ///
    /// W58: dependency wrapper and representative propagation set/descriptors are live;
    /// `concept_op_linker` is threaded as the port's `Vec<NegLink<ConceptId>>` slice,
    /// the direct equivalent of Konclude's `CSortedNegLinker<CConcept*>*`.
    pub fn propagate_representative_to_successor(
        &mut self,
        process_indi: NodeId,
        succ_indi: &mut NodeId,
        concept_op_linker: &[NegLink<ConceptId>],
        negate: bool,
        con_des: ConDescId,
        rest_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let concept = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();

        *succ_indi = self.get_localized_individual(*succ_indi, false, calc_alg_context);

        let mut con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*succ_indi);
        let mut next_dep_track_point: TrackPointId = Id::NONE;
        let mut continue_propagation = false;

        for concept_op_linker_it in concept_op_linker.iter().copied() {
            let op_concept = concept_op_linker_it.target;
            let op_con_neg = concept_op_linker_it.negated ^ negate;
            let op_concept_tag = calc_alg_context
                .ontology_arenas()
                .concept(op_concept)
                .get_concept_tag();

            let con_rep_prop_set_hash = calc_alg_context
                .process_context_mut()
                .node_concept_representative_propagation_set_hash(process_indi);
            let prev_rep_prop_set =
                super::super::process::representative::ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                    calc_alg_context.process_context_mut(),
                    con_rep_prop_set_hash,
                    concept,
                    false,
                );
            let succ_con_rep_prop_set_hash = calc_alg_context
                .process_context_mut()
                .node_concept_representative_propagation_set_hash(*succ_indi);
            let succ_rep_prop_set =
                super::super::process::representative::ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                    calc_alg_context.process_context_mut(),
                    succ_con_rep_prop_set_hash,
                    op_concept,
                    true,
                );
            let proc_rep_prop_des = if prev_rep_prop_set.is_some() {
                calc_alg_context
                    .process_context()
                    .rep_prop_set(prev_rep_prop_set)
                    .get_outgoing_representative_propagation_descriptor_linker()
            } else {
                Id::NONE
            };
            if proc_rep_prop_des.is_none() {
                continue;
            }
            let prop_dep_track_point = calc_alg_context
                .process_context()
                .rep_prop_des(proc_rep_prop_des)
                .get_dependency_track_point();

            let mut binding_con_des: ConDescId = Id::NONE;
            let mut binding_dep_track_point: TrackPointId = Id::NONE;
            let mut reapply_queue_empty = true;
            let has_binding_con_des_and_queue = calc_alg_context
                .process_context()
                .label_set(con_set)
                .get_concept_descriptor_and_reapply_queue_state_by_tag(
                    op_concept_tag,
                    &mut binding_con_des,
                    &mut binding_dep_track_point,
                    &mut reapply_queue_empty,
                );

            if !has_binding_con_des_and_queue {
                self.stat_representative_propagate_succ_count += 1;
                if next_dep_track_point.is_none() {
                    con_set = calc_alg_context
                        .process_context_mut()
                        .node_reapply_concept_label_set(*succ_indi);
                    let link_dep_track_point = calc_alg_context
                        .process_context()
                        .edge(rest_link)
                        .get_dependency_track_point();
                    let mut process_indi_ref = process_indi;
                    let _rep_all_dep_node = self.create_representative_all_dependency(
                        &mut next_dep_track_point,
                        &mut process_indi_ref,
                        con_des,
                        prop_dep_track_point,
                        link_dep_track_point,
                        calc_alg_context,
                    );
                    if next_dep_track_point.is_none() {
                        next_dep_track_point = prop_dep_track_point;
                    }
                }

                binding_con_des = self.add_concept_to_individual_return_concept_descriptor(
                    op_concept,
                    op_con_neg,
                    succ_indi,
                    next_dep_track_point,
                    false,
                    false,
                    calc_alg_context,
                );
                calc_alg_context
                    .process_context_mut()
                    .rep_prop_set_mut(succ_rep_prop_set)
                    .set_concept_descriptor(binding_con_des);
                self.propagate_representative(
                    succ_indi,
                    proc_rep_prop_des,
                    succ_rep_prop_set,
                    next_dep_track_point,
                    calc_alg_context,
                );
                continue_propagation = true;
            } else if self.requires_representative_propagation(
                succ_indi,
                proc_rep_prop_des,
                succ_rep_prop_set,
                calc_alg_context,
            ) {
                self.stat_representative_propagate_succ_count += 1;
                if next_dep_track_point.is_none() {
                    con_set = calc_alg_context
                        .process_context_mut()
                        .node_reapply_concept_label_set(*succ_indi);
                    let link_dep_track_point = calc_alg_context
                        .process_context()
                        .edge(rest_link)
                        .get_dependency_track_point();
                    let mut process_indi_ref = process_indi;
                    let _rep_all_dep_node = self.create_representative_all_dependency(
                        &mut next_dep_track_point,
                        &mut process_indi_ref,
                        con_des,
                        prop_dep_track_point,
                        link_dep_track_point,
                        calc_alg_context,
                    );
                    if next_dep_track_point.is_none() {
                        next_dep_track_point = prop_dep_track_point;
                    }
                }

                self.propagate_representative(
                    succ_indi,
                    proc_rep_prop_des,
                    succ_rep_prop_set,
                    next_dep_track_point,
                    calc_alg_context,
                );
                let succ_out_rep_prop_des = calc_alg_context
                    .process_context()
                    .rep_prop_set(succ_rep_prop_set)
                    .get_outgoing_representative_propagation_descriptor_linker();
                let succ_rep_data = calc_alg_context
                    .process_context()
                    .rep_prop_des(succ_out_rep_prop_des)
                    .get_representative_variable_binding_path_set_data();
                let var_count =
                    RepresentativeVariableBindingPathSetData::get_representated_variable_count(
                        calc_alg_context.process_context(),
                        succ_rep_data,
                    );
                self.reapply_concept_updated_representative_binding_count(
                    *succ_indi,
                    binding_con_des,
                    binding_dep_track_point,
                    var_count,
                    con_set,
                    0,
                    calc_alg_context,
                );
                let _ = reapply_queue_empty;
                continue_propagation = true;
            }
        }

        if continue_propagation {
            self.add_individual_to_processing_queue(*succ_indi, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::updateRepresentativePropagationSet`.
    /// cpp 11260–11375.
    ///
    /// Folds newly arrived incoming representative-propagation descriptors of
    /// `repPropSet` into a single outgoing representative: when there is exactly one
    /// new incoming and no outgoing it shares it directly; otherwise it allocates a
    /// merged `CRepresentativeVariableBindingPathSetData` (migrating/copying from the
    /// previous outgoing when share/use counts allow), unions the per-descriptor
    /// variable-binding-path maps (direct-lookup vs merge-walk on
    /// `mMapComparisonDirectLookupFactor`), records a RESOLVEREPRESENTATIVE
    /// dependency, and installs the new outgoing descriptor.
    ///
    /// W55: both the "single incoming and no outgoing" share branch and the folded
    /// multi-incoming merge branch are live.
    pub fn update_representative_propagation_set(
        &mut self,
        process_indi: &mut NodeId,
        rep_prop_set: RepresentativePropagationSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let last_processed = calc_alg_context
            .process_context()
            .rep_prop_set(rep_prop_set)
            .get_last_processed_incoming_representative_propagation_descriptor_linker();
        let last_inc_rep_prop_des = calc_alg_context
            .process_context()
            .rep_prop_set(rep_prop_set)
            .get_incoming_representative_propagation_descriptor_linker();
        if last_processed == last_inc_rep_prop_des {
            return;
        }

        let last_rep_prop_des = last_processed;
        let last_out_rep_prop_des = calc_alg_context
            .process_context()
            .rep_prop_set(rep_prop_set)
            .get_outgoing_representative_propagation_descriptor_linker();
        calc_alg_context
            .process_context_mut()
            .rep_prop_set_mut(rep_prop_set)
            .set_last_processed_incoming_representative_propagation_descriptor_linker(
                last_inc_rep_prop_des,
            );

        if last_out_rep_prop_des.is_none()
            && last_inc_rep_prop_des.is_some()
            && !calc_alg_context
                .process_context()
                .rep_prop_des(last_inc_rep_prop_des)
                .has_next()
        {
            calc_alg_context
                .process_context_mut()
                .rep_prop_set_mut(rep_prop_set)
                .set_outgoing_representative_propagation_descriptor_linker(last_inc_rep_prop_des);
            let rep_data = calc_alg_context
                .process_context()
                .rep_prop_des(last_inc_rep_prop_des)
                .get_representative_variable_binding_path_set_data();
            let cur_loc_tag = calc_alg_context
                .process_context()
                .used_process_tagger()
                .get_current_localization_tag();
            if calc_alg_context
                .process_context()
                .rep_var_bind_path_set_data(rep_data)
                .is_localization_tag_up_to_date(cur_loc_tag)
            {
                calc_alg_context
                    .process_context_mut()
                    .rep_var_bind_path_set_data_mut(rep_data)
                    .inc_share_count(1);
            }
            return;
        }

        self.stat_representative_propagate_use_representative_count += 1;

        let rep_var_bind_path_set_hash =
            calc_alg_context.representative_variable_binding_path_set_hash(true);

        let last_rep_var_bind_path_set_data = if last_out_rep_prop_des.is_some() {
            calc_alg_context
                .process_context()
                .rep_prop_des(last_out_rep_prop_des)
                .get_representative_variable_binding_path_set_data()
        } else {
            Id::NONE
        };
        let mut migrateable = false;
        if last_rep_var_bind_path_set_data.is_some() {
            let cur_loc_tag = calc_alg_context
                .process_context()
                .used_process_tagger()
                .get_current_localization_tag();
            let last_is_local = calc_alg_context
                .process_context()
                .rep_var_bind_path_set_data(last_rep_var_bind_path_set_data)
                .is_localization_tag_up_to_date(cur_loc_tag);
            if last_is_local {
                {
                    calc_alg_context
                        .process_context_mut()
                        .rep_var_bind_path_set_data_mut(last_rep_var_bind_path_set_data)
                        .dec_share_count(1);
                }
                let last_data = calc_alg_context
                    .process_context()
                    .rep_var_bind_path_set_data(last_rep_var_bind_path_set_data);
                migrateable = last_data.is_migratable()
                    && last_data.get_share_count() <= 0
                    && last_data.get_use_count() <= 20;
            }
        }

        let rep_var_bind_path_set_data =
            RepresentativeVariableBindingPathSetHash::get_representative_variable_binding_path_set_data_for_propagation_set(
                calc_alg_context.process_context_mut(),
                rep_var_bind_path_set_hash,
                rep_prop_set,
                true,
            );
        {
            calc_alg_context
                .process_context_mut()
                .rep_var_bind_path_set_data_mut(rep_var_bind_path_set_data)
                .inc_share_count(1)
                .inc_use_count(1);
        }

        if !calc_alg_context
            .process_context()
            .rep_var_bind_path_set_data(rep_var_bind_path_set_data)
            .has_migrate_data()
        {
            self.stat_representative_propagate_new_representative_count += 1;
            let rep_id = calc_alg_context
                .processing_data_box_mut()
                .next_representative_variable_binding_path_id(true);
            calc_alg_context
                .process_context_mut()
                .rep_var_bind_path_set_data_mut(rep_var_bind_path_set_data)
                .set_representative_id(rep_id);

            let mut update_new_only = false;
            if migrateable && last_rep_var_bind_path_set_data.is_some() {
                update_new_only = true;
                RepresentativeVariableBindingPathSetData::take_migrate_data_from(
                    calc_alg_context.process_context_mut(),
                    rep_var_bind_path_set_data,
                    last_rep_var_bind_path_set_data,
                );
            } else if last_rep_var_bind_path_set_data.is_some() {
                update_new_only = true;
                RepresentativeVariableBindingPathSetData::copy_migrate_data_from(
                    calc_alg_context.process_context_mut(),
                    rep_var_bind_path_set_data,
                    last_rep_var_bind_path_set_data,
                );
            }

            let rep_migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
                calc_alg_context.process_context_mut(),
                rep_var_bind_path_set_data,
                true,
            );
            let until_update_rep_prop_des = if update_new_only {
                last_rep_prop_des
            } else {
                Id::NONE
            };
            let mut new_rep_prop_des_it = last_inc_rep_prop_des;
            while new_rep_prop_des_it != until_update_rep_prop_des && new_rep_prop_des_it.is_some()
            {
                let new_rep_var_bind_path_set_data = calc_alg_context
                    .process_context()
                    .rep_prop_des(new_rep_prop_des_it)
                    .get_representative_variable_binding_path_set_data();
                let new_rep_migrate_data =
                    RepresentativeVariableBindingPathSetData::get_migrate_data(
                        calc_alg_context.process_context_mut(),
                        new_rep_var_bind_path_set_data,
                        true,
                    );
                let (new_rep_id, new_rep_key) = {
                    let new_rep_data = calc_alg_context
                        .process_context()
                        .rep_var_bind_path_set_data(new_rep_var_bind_path_set_data);
                    (
                        new_rep_data.get_representative_id(),
                        new_rep_data.get_representative_key(),
                    )
                };
                calc_alg_context
                    .process_context_mut()
                    .rep_var_bind_path_set_migrate_data_mut(rep_migrate_data)
                    .get_representative_containing_map_mut()
                    .insert_contained_representative(
                        new_rep_id,
                        new_rep_var_bind_path_set_data,
                        true,
                    );
                calc_alg_context
                    .process_context_mut()
                    .rep_var_bind_path_set_data_mut(rep_var_bind_path_set_data)
                    .add_key_signature_value(new_rep_key);

                let new_rep_var_bind_path_map = calc_alg_context
                    .process_context()
                    .rep_var_bind_path_set_migrate_data(new_rep_migrate_data)
                    .get_representative_variable_binding_path_map()
                    .clone();
                let rep_var_bind_path_map_count = calc_alg_context
                    .process_context()
                    .rep_var_bind_path_set_migrate_data(rep_migrate_data)
                    .get_representative_variable_binding_path_map()
                    .count();
                if new_rep_var_bind_path_map.count() * self.map_comparison_direct_lookup_factor
                    <= rep_var_bind_path_map_count
                {
                    for (propagation_id, data) in new_rep_var_bind_path_map.map.iter() {
                        self.insert_representative_fold_map_entry_if_missing(
                            rep_migrate_data,
                            *propagation_id,
                            *data,
                            new_rep_var_bind_path_set_data,
                            new_rep_id,
                            calc_alg_context,
                        );
                    }
                } else {
                    let mut new_keys: Vec<Cint64> =
                        new_rep_var_bind_path_map.map.keys().copied().collect();
                    let mut rep_keys: Vec<Cint64> = calc_alg_context
                        .process_context()
                        .rep_var_bind_path_set_migrate_data(rep_migrate_data)
                        .get_representative_variable_binding_path_map()
                        .map
                        .keys()
                        .copied()
                        .collect();
                    new_keys.sort_unstable();
                    rep_keys.sort_unstable();
                    let mut new_key_pos = 0usize;
                    let mut rep_key_pos = 0usize;
                    while new_key_pos < new_keys.len() {
                        if rep_key_pos >= rep_keys.len()
                            || new_keys[new_key_pos] < rep_keys[rep_key_pos]
                        {
                            let propagation_id = new_keys[new_key_pos];
                            let data = new_rep_var_bind_path_map.value(propagation_id);
                            self.insert_representative_fold_map_entry_if_missing(
                                rep_migrate_data,
                                propagation_id,
                                data,
                                new_rep_var_bind_path_set_data,
                                new_rep_id,
                                calc_alg_context,
                            );
                            new_key_pos += 1;
                        } else if new_keys[new_key_pos] == rep_keys[rep_key_pos] {
                            new_key_pos += 1;
                            rep_key_pos += 1;
                        } else {
                            rep_key_pos += 1;
                        }
                    }
                }

                new_rep_prop_des_it = calc_alg_context
                    .process_context()
                    .rep_prop_des(new_rep_prop_des_it)
                    .get_next();
            }
        } else {
            self.stat_representative_propagate_reused_representative_count += 1;
        }

        let out_prop_rep_des = calc_alg_context
            .process_context_mut()
            .alloc_rep_prop_des(RepresentativePropagationDescriptor::new());
        let mut next_dep_track_point = Id::NONE;
        let rep_migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            calc_alg_context.process_context_mut(),
            rep_var_bind_path_set_data,
            false,
        );
        let rep_var_bind_path_map = calc_alg_context
            .process_context()
            .rep_var_bind_path_set_migrate_data(rep_migrate_data)
            .get_representative_variable_binding_path_map()
            .clone();
        let rep_prop_map = calc_alg_context
            .process_context()
            .rep_prop_set(rep_prop_set)
            .get_representative_propagation_map()
            .clone();
        let con_des = calc_alg_context
            .process_context()
            .rep_prop_set(rep_prop_set)
            .get_concept_descriptor();
        let prev_dep_track_point = calc_alg_context
            .process_context()
            .rep_prop_des(last_inc_rep_prop_des)
            .get_dependency_track_point();
        let additional_dep_track_point = if last_out_rep_prop_des.is_some() {
            calc_alg_context
                .process_context()
                .rep_prop_des(last_out_rep_prop_des)
                .get_dependency_track_point()
        } else {
            Id::NONE
        };
        self.create_resolve_representative_dependency(
            &mut next_dep_track_point,
            process_indi,
            con_des,
            Some(&rep_var_bind_path_map),
            Some(&rep_prop_map),
            prev_dep_track_point,
            additional_dep_track_point,
            calc_alg_context,
        );
        calc_alg_context
            .process_context_mut()
            .rep_prop_des_mut(out_prop_rep_des)
            .init_representative_descriptor(rep_var_bind_path_set_data, next_dep_track_point);
        RepresentativePropagationSet::add_outgoing_representative_propagation_descriptor_linker(
            calc_alg_context.process_context_mut(),
            rep_prop_set,
            out_prop_rep_des,
        );
    }

    fn insert_representative_fold_map_entry_if_missing(
        &mut self,
        rep_migrate_data: RepresentativeVariableBindingPathSetMigrateDataId,
        propagation_id: Cint64,
        data: RepresentativeVariableBindingPathMapData,
        new_rep_var_bind_path_set_data: RepresentativeVariableBindingPathSetDataId,
        new_rep_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if !calc_alg_context
            .process_context()
            .rep_var_bind_path_set_migrate_data(rep_migrate_data)
            .get_representative_variable_binding_path_map()
            .contains(propagation_id)
        {
            let mut folded_data = RepresentativeVariableBindingPathMapData::new(
                data.get_variable_binding_path(),
                new_rep_var_bind_path_set_data,
            );
            folded_data.resolve_rep_var_bind_path_set_data_id = new_rep_id;
            calc_alg_context
                .process_context_mut()
                .rep_var_bind_path_set_migrate_data_mut(rep_migrate_data)
                .get_representative_variable_binding_path_map_mut()
                .insert(propagation_id, folded_data);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateRepresentative`.
    /// cpp 11379–11387.
    ///
    /// Allocates an incoming representative-propagation descriptor cloning
    /// `repPropDes`'s set data (with `nextDepTrackPoint`), links it into
    /// `repPropSet`, and re-folds the set via `updateRepresentativePropagationSet`.
    ///
    /// W51: `repPropDes` / `repPropSet` are now typed arena ids. W52/W55 ported
    /// the representative propagation-set update branches this calls.
    pub fn propagate_representative(
        &mut self,
        process_indi: &mut NodeId,
        rep_prop_des: RepresentativePropagationDescriptorId,
        rep_prop_set: RepresentativePropagationSetId,
        next_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let rep_data = calc_alg_context
            .process_context()
            .rep_prop_des(rep_prop_des)
            .get_representative_variable_binding_path_set_data();
        let propagate_rep_des = calc_alg_context
            .process_context_mut()
            .alloc_rep_prop_des(RepresentativePropagationDescriptor::new());
        calc_alg_context
            .process_context_mut()
            .rep_prop_des_mut(propagate_rep_des)
            .init_representative_descriptor(rep_data, next_dep_track_point);
        RepresentativePropagationSet::add_incoming_representative_propagation(
            calc_alg_context.process_context_mut(),
            rep_prop_set,
            propagate_rep_des,
        );
        self.update_representative_propagation_set(process_indi, rep_prop_set, calc_alg_context);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::requiresRepresentativePropagation`.
    /// cpp 11390–11444.
    ///
    /// Decides whether the representative carried by `repPropDes` adds anything to
    /// `testRepPropSet`: false if the set already contains the representative id or
    /// its containing-map covers it or the available outgoing map already subsumes
    /// every propagation variable-binding-path id (direct-lookup vs merge-walk on
    /// `mMapComparisonDirectLookupFactor`); otherwise true.
    pub fn requires_representative_propagation(
        &mut self,
        process_indi: &mut NodeId,
        rep_prop_des: RepresentativePropagationDescriptorId,
        test_rep_prop_set: RepresentativePropagationSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let prop_rep_data = calc_alg_context
            .process_context()
            .rep_prop_des(rep_prop_des)
            .get_representative_variable_binding_path_set_data();
        let prop_rep_id = calc_alg_context
            .process_context()
            .rep_var_bind_path_set_data(prop_rep_data)
            .get_representative_id();
        if calc_alg_context
            .process_context()
            .rep_prop_set(test_rep_prop_set)
            .contains_representative_propagation_for_id(prop_rep_id)
        {
            return false;
        }

        let last_rep_prop_des = calc_alg_context
            .process_context()
            .rep_prop_set(test_rep_prop_set)
            .get_outgoing_representative_propagation_descriptor_linker();
        if last_rep_prop_des.is_some() {
            let avail_rep_data = calc_alg_context
                .process_context()
                .rep_prop_des(last_rep_prop_des)
                .get_representative_variable_binding_path_set_data();
            let avail_mig_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
                calc_alg_context.process_context_mut(),
                avail_rep_data,
                false,
            );
            if avail_mig_data.is_some() {
                if calc_alg_context
                    .process_context()
                    .rep_var_bind_path_set_migrate_data(avail_mig_data)
                    .get_representative_containing_map()
                    .contains(prop_rep_id)
                {
                    return false;
                }

                let avail_var_bind_path_map = calc_alg_context
                    .process_context()
                    .rep_var_bind_path_set_migrate_data(avail_mig_data)
                    .get_representative_variable_binding_path_map()
                    .clone();
                let prop_mig_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
                    calc_alg_context.process_context_mut(),
                    prop_rep_data,
                    false,
                );
                let prop_var_bind_path_map = calc_alg_context
                    .process_context()
                    .rep_var_bind_path_set_migrate_data(prop_mig_data)
                    .get_representative_variable_binding_path_map()
                    .clone();

                if prop_var_bind_path_map.count() * self.map_comparison_direct_lookup_factor
                    <= avail_var_bind_path_map.count()
                {
                    for prop_var_bind_path_id in prop_var_bind_path_map.map.keys() {
                        if !avail_var_bind_path_map.contains(*prop_var_bind_path_id) {
                            return true;
                        }
                    }
                    return false;
                } else {
                    let mut avail_keys: Vec<Cint64> =
                        avail_var_bind_path_map.map.keys().copied().collect();
                    let mut prop_keys: Vec<Cint64> =
                        prop_var_bind_path_map.map.keys().copied().collect();
                    avail_keys.sort_unstable();
                    prop_keys.sort_unstable();
                    let mut avail_pos = 0usize;
                    let mut prop_pos = 0usize;
                    while prop_pos < prop_keys.len() {
                        let prop_id = prop_keys[prop_pos];
                        if avail_pos >= avail_keys.len() {
                            return true;
                        }
                        let avail_id = avail_keys[avail_pos];
                        if avail_id < prop_id {
                            avail_pos += 1;
                        } else if prop_id < avail_id {
                            return true;
                        } else {
                            avail_pos += 1;
                            prop_pos += 1;
                        }
                    }
                    return false;
                }
            }
        }
        let _ = process_indi;
        true
    }

    // =======================================================================
    // Propagation-binding propagation to successor (cpp 13294–13463).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagatePropagationBindingsToSuccessor`.
    /// cpp 13294–13355.
    ///
    /// The successor twin of `propagatePropagationBindings`: for each operand of
    /// `conDes`'s concept it adds the binding concept on `succIndi` (creating a
    /// BINDPROPAGATEALL dependency the first time) and either seeds the successor
    /// propagation-binding set
    /// (`propagateInitialPropagationBindingsToSuccessor`) or freshly extends it
    /// (`propagateFreshPropagationBindingsToSuccessor`), queueing the new descriptor
    /// + re-applying any pending reapply queue; re-queues `succIndi` if anything
    /// changed.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `concept_op_linker` (`CSortedNegLinker<CConcept*>*`)
    /// is threaded as the owning concept id; propagation-binding sets are arena ids.
    pub fn propagate_propagation_bindings_to_successor(
        &mut self,
        process_indi: NodeId,
        succ_indi: &mut NodeId,
        // W3-RECONCILE[overload]: faithful arg is concept->getOperandList(); sole caller threads the concept id.
        concept_op_linker: ConceptId,
        negate: bool,
        con_des: ConDescId,
        rest_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let dep_track_point = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_dependency_track_point();
        let concept = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();

        *succ_indi = self.get_localized_individual(*succ_indi, false, calc_alg_context);

        let mut con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*succ_indi);
        let mut next_dep_track_point: TrackPointId = Id::NONE;
        let mut continue_propagation = false;
        let concept_op_linker_it = calc_alg_context
            .ontology_arenas()
            .concept(concept_op_linker)
            .get_operand_list()
            .to_vec();
        for concept_op_linker_it in concept_op_linker_it {
            let op_concept = concept_op_linker_it.target;
            let op_con_neg = concept_op_linker_it.negated ^ negate;
            let op_concept_tag = calc_alg_context
                .ontology_arenas()
                .concept(op_concept)
                .get_concept_tag();

            let mut binding_con_des: ConDescId = Id::NONE;
            let mut binding_dep_track_point: TrackPointId = Id::NONE;
            let has_binding_con_des_and_queue = calc_alg_context
                .process_context()
                .label_set(con_set)
                .get_concept_descriptor_and_reapply_queue_by_tag(
                    op_concept_tag,
                    &mut binding_con_des,
                    &mut binding_dep_track_point,
                );

            if !has_binding_con_des_and_queue {
                if next_dep_track_point.is_none() {
                    con_set = calc_alg_context
                        .process_context_mut()
                        .node_reapply_concept_label_set(*succ_indi);
                    let link_dep_track_point = calc_alg_context
                        .process_context()
                        .edge(rest_link)
                        .get_dependency_track_point();
                    let mut process_indi_ref = process_indi;
                    let _bind_dep_node = self.create_bind_propagate_all_dependency(
                        &mut next_dep_track_point,
                        &mut process_indi_ref,
                        con_des,
                        dep_track_point,
                        link_dep_track_point,
                        calc_alg_context,
                    );
                    if next_dep_track_point.is_none() {
                        // W6-DEFER[api]: createBINDPROPAGATEALLDependency is called
                        // at the C++ point, but the dependency-base backend is still
                        // not materialized; carry the premise dependency until it lands.
                        next_dep_track_point = dep_track_point;
                    }
                }

                binding_con_des = self.add_concept_to_individual_return_concept_descriptor(
                    op_concept,
                    op_con_neg,
                    succ_indi,
                    next_dep_track_point,
                    false,
                    false,
                    calc_alg_context,
                );

                let con_prop_binding_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_propagation_binding_set_hash(process_indi);
                let concept_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag();
                let prev_prop_binding_set =
                    ConceptPropagationBindingSetHash::get_propagation_binding_set(
                        calc_alg_context.process_context_mut(),
                        con_prop_binding_set_hash,
                        concept_tag,
                        false,
                    );
                let succ_con_prop_binding_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_propagation_binding_set_hash(*succ_indi);
                let prop_binding_set =
                    ConceptPropagationBindingSetHash::get_propagation_binding_set(
                        calc_alg_context.process_context_mut(),
                        succ_con_prop_binding_set_hash,
                        op_concept_tag,
                        true,
                    );
                calc_alg_context
                    .process_context_mut()
                    .prop_binding_set_mut(prop_binding_set)
                    .set_concept_descriptor(binding_con_des);
                let mut process_indi_ref = process_indi;
                self.propagate_initial_propagation_bindings_to_successor(
                    &mut process_indi_ref,
                    *succ_indi,
                    binding_con_des,
                    prop_binding_set,
                    prev_prop_binding_set,
                    rest_link,
                    calc_alg_context,
                );
                continue_propagation = true;
            } else {
                let con_prop_binding_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_propagation_binding_set_hash(process_indi);
                let concept_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag();
                let prev_prop_binding_set =
                    ConceptPropagationBindingSetHash::get_propagation_binding_set(
                        calc_alg_context.process_context_mut(),
                        con_prop_binding_set_hash,
                        concept_tag,
                        false,
                    );
                let succ_con_prop_binding_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_propagation_binding_set_hash(*succ_indi);
                let prop_binding_set =
                    ConceptPropagationBindingSetHash::get_propagation_binding_set(
                        calc_alg_context.process_context_mut(),
                        succ_con_prop_binding_set_hash,
                        op_concept_tag,
                        true,
                    );
                let mut process_indi_ref = process_indi;
                if self.propagate_fresh_propagation_bindings_to_successor(
                    &mut process_indi_ref,
                    *succ_indi,
                    con_des,
                    prop_binding_set,
                    prev_prop_binding_set,
                    rest_link,
                    calc_alg_context,
                ) {
                    self.set_individual_node_concept_label_set_modified(
                        succ_indi,
                        calc_alg_context,
                    );
                    let con_pro_queue = calc_alg_context
                        .process_context_mut()
                        .node_concept_processing_queue(*succ_indi, true);
                    self.add_concept_preprocessed_to_processing_queue_skip(
                        binding_con_des,
                        binding_dep_track_point,
                        con_pro_queue,
                        *succ_indi,
                        true,
                        calc_alg_context,
                        super::super::model::substrate::INVALID,
                    );
                    // W3-DEFER[api]: if (!reapplyQueue->isEmpty()) construct
                    // CCondensedReapplyQueueIterator from the concrete queue pointer
                    // returned by getConceptDescriptorAndReapplyQueue and call
                    // applyReapplyQueueConcepts(succIndi,...). The current label-set
                    // API exposes descriptor + dependency only, not that queue pointer.
                    continue_propagation = true;
                }
            }
        }
        if continue_propagation {
            self.add_individual_to_processing_queue(*succ_indi, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateInitialPropagationBindingsToSuccessor`.
    /// cpp 13362–13390.
    ///
    /// Initial (whole-set copy) variant: copies every propagation binding of
    /// `prevPropBindingSet` into the fresh `newPropBindingSet`, cloning each
    /// descriptor under a new PROPAGATEBINDINGSSUCCESSOR dependency. Returns whether
    /// anything was propagated (including the propagate-all flag adoption).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `new_prop_binding_set` /
    /// `prev_prop_binding_set` (`CPropagationBindingSet*`) are arena ids. The
    /// `PROPAGATEBINDINGSSUCCESSOR` dependency factory exists as a deferred wrapper,
    /// so the descriptor currently carries the previous dependency track point.
    pub fn propagate_initial_propagation_bindings_to_successor(
        &mut self,
        process_indi: &mut NodeId,
        succ_indi: NodeId,
        con_des: ConDescId,
        new_prop_binding_set: PropagationBindingSetId,
        prev_prop_binding_set: PropagationBindingSetId,
        rest_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut propagations = false;
        let mut new_prop_bind_des_linker: PropagationBindingDescriptorId = Id::NONE;
        if prev_prop_binding_set.is_some() {
            let _ = (*process_indi, succ_indi, con_des);
            let adopted = {
                let prev_snapshot = {
                    let pc = calc_alg_context.process_context();
                    pc.prop_binding_set(prev_prop_binding_set)
                        .propagate_all_flag
                };
                let new_set = calc_alg_context
                    .process_context_mut()
                    .prop_binding_set_mut(new_prop_binding_set);
                let old_flag = new_set.propagate_all_flag;
                new_set.propagate_all_flag |= prev_snapshot;
                new_set.propagate_all_flag != old_flag
            };
            propagations |= adopted;

            let prev_map = {
                let pc = calc_alg_context.process_context();
                pc.prop_binding_set(prev_prop_binding_set).prop_map.clone()
            };
            calc_alg_context
                .process_context_mut()
                .prop_binding_set_mut(new_prop_binding_set)
                .copy_propagation_bindings(Some(&prev_map));

            let mut prop_keys: Vec<Cint64> = {
                let pc = calc_alg_context.process_context();
                pc.prop_binding_set(new_prop_binding_set)
                    .prop_map
                    .map
                    .keys()
                    .copied()
                    .collect()
            };
            prop_keys.sort();

            for prop_id in prop_keys {
                // W3-DEFER[macro]: STATINC(PBINDPROPAGATEDCOUNT, calcAlgContext)
                // W3-DEFER[macro]: STATINC(PBINDPROPAGATEDINITIALCOUNT, calcAlgContext)
                let prev_prop_bind_des = {
                    let data = calc_alg_context
                        .process_context_mut()
                        .prop_binding_set_mut(new_prop_binding_set)
                        .prop_map
                        .entry_mut(prop_id);
                    data.clear_reapply_concept_descriptor();
                    data.get_propagation_binding_descriptor()
                };
                let (prop_binding, prev_dep_track_point) = {
                    let pc = calc_alg_context.process_context();
                    let prev_des = pc.prop_binding_des(prev_prop_bind_des);
                    (
                        prev_des.get_propagation_binding(),
                        prev_des.get_dependency_track_point(),
                    )
                };
                let link_dep_track_point = calc_alg_context
                    .process_context()
                    .edge(rest_link)
                    .get_dependency_track_point();

                let new_prop_bind_des = calc_alg_context
                    .process_context_mut()
                    .alloc_prop_binding_des(PropagationBindingDescriptor::new());
                calc_alg_context
                    .process_context_mut()
                    .prop_binding_des_mut(new_prop_bind_des)
                    .set_data(new_prop_bind_des);
                let mut new_dep_track_point: TrackPointId = Id::NONE;
                let _bind_dep_node = self.create_propagate_bindings_successor_dependency(
                    &mut new_dep_track_point,
                    process_indi,
                    con_des,
                    prev_dep_track_point,
                    link_dep_track_point,
                    calc_alg_context,
                );
                if new_dep_track_point.is_none() {
                    // W3-DEFER[api]: createPROPAGATEBINDINGSSUCCESSORDependency(
                    // newDepTrackPoint, processIndi, conDes,
                    // prevPropBindDes->getDependencyTrackPoint(),
                    // restLink->getDependencyTrackPoint(), calcAlgContext) is wired
                    // but its dependency base object is not materialized yet, so the
                    // previous dependency track point is carried until the factory
                    // backend lands.
                    new_dep_track_point = prev_dep_track_point;
                }
                calc_alg_context
                    .process_context_mut()
                    .prop_binding_des_mut(new_prop_bind_des)
                    .init_propagation_binding_descriptor(prop_binding, new_dep_track_point);
                calc_alg_context
                    .process_context_mut()
                    .prop_binding_set_mut(new_prop_binding_set)
                    .prop_map
                    .entry_mut(prop_id)
                    .set_propagation_binding_descriptor(new_prop_bind_des);
                if new_prop_bind_des_linker.is_none() {
                    new_prop_bind_des_linker = new_prop_bind_des;
                } else {
                    PropagationBindingDescriptor::append(
                        calc_alg_context.process_context_mut(),
                        new_prop_bind_des,
                        new_prop_bind_des_linker,
                    );
                    new_prop_bind_des_linker = new_prop_bind_des;
                }
                propagations = true;
            }
            if new_prop_bind_des_linker.is_some() {
                super::super::process::propagation_binding::PropagationBindingSet::add_propagation_binding_descriptor_linker(
                    calc_alg_context.process_context_mut(),
                    new_prop_binding_set,
                    new_prop_bind_des_linker,
                );
            }
        }
        propagations
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateFreshPropagationBindingsToSuccessor`.
    /// cpp 13395–13463.
    ///
    /// Fresh (incremental) variant: merge-walks `prevPropBindingSet` against the
    /// existing `newPropBindingSet` map, cloning only the bindings that are new (or
    /// not yet descriptor-bound), each under a new PROPAGATEBINDINGSSUCCESSOR
    /// dependency, re-applying any pending reapply-concept descriptors on update.
    /// Returns whether anything was propagated.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `new_prop_binding_set` /
    /// `prev_prop_binding_set` (`CPropagationBindingSet*`) are arena ids. The
    /// `PROPAGATEBINDINGSSUCCESSOR` dependency factory is called at the C++ point;
    /// its dependency-base backend is still deferred.
    pub fn propagate_fresh_propagation_bindings_to_successor(
        &mut self,
        process_indi: &mut NodeId,
        succ_indi: NodeId,
        con_des: ConDescId,
        new_prop_binding_set: PropagationBindingSetId,
        prev_prop_binding_set: PropagationBindingSetId,
        rest_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut propagations = false;
        if prev_prop_binding_set.is_some() {
            let adopted = {
                let prev_snapshot = {
                    let pc = calc_alg_context.process_context();
                    pc.prop_binding_set(prev_prop_binding_set)
                        .propagate_all_flag
                };
                let new_set = calc_alg_context
                    .process_context_mut()
                    .prop_binding_set_mut(new_prop_binding_set);
                let old_flag = new_set.propagate_all_flag;
                new_set.propagate_all_flag |= prev_snapshot;
                new_set.propagate_all_flag != old_flag
            };
            propagations |= adopted;

            let prev_keys: Vec<Cint64> = {
                let pc = calc_alg_context.process_context();
                let mut keys: Vec<Cint64> = pc
                    .prop_binding_set(prev_prop_binding_set)
                    .prop_map
                    .map
                    .keys()
                    .copied()
                    .collect();
                keys.sort();
                keys
            };
            let new_keys: Vec<Cint64> = {
                let pc = calc_alg_context.process_context();
                let mut keys: Vec<Cint64> = pc
                    .prop_binding_set(new_prop_binding_set)
                    .prop_map
                    .map
                    .keys()
                    .copied()
                    .collect();
                keys.sort();
                keys
            };
            let mut new_key_index = 0usize;
            let mut new_prop_bind_des_linker: PropagationBindingDescriptorId = Id::NONE;

            for prev_prop_id in prev_keys {
                let mut do_propagation = false;
                let mut update_existing = false;
                loop {
                    if new_key_index >= new_keys.len() {
                        do_propagation = true;
                        break;
                    }
                    let new_prop_id = new_keys[new_key_index];
                    if new_prop_id < prev_prop_id {
                        new_key_index += 1;
                    } else if new_prop_id == prev_prop_id {
                        let has_descriptor = calc_alg_context
                            .process_context()
                            .prop_binding_set(new_prop_binding_set)
                            .prop_map
                            .value(new_prop_id)
                            .has_propagation_binding_descriptor();
                        if !has_descriptor {
                            do_propagation = true;
                            update_existing = true;
                        } else {
                            new_key_index += 1;
                        }
                        break;
                    } else {
                        do_propagation = true;
                        break;
                    }
                }

                if do_propagation {
                    // W3-DEFER[macro]: STATINC(PBINDPROPAGATEDCOUNT, calcAlgContext)
                    // W3-DEFER[macro]: STATINC(PBINDPROPAGATEDFRESHCOUNT, calcAlgContext)
                    let prev_prop_bind_des = calc_alg_context
                        .process_context()
                        .prop_binding_set(prev_prop_binding_set)
                        .prop_map
                        .value(prev_prop_id)
                        .get_propagation_binding_descriptor();
                    let (prop_binding, prev_dep_track_point) = {
                        let pc = calc_alg_context.process_context();
                        let prev_des = pc.prop_binding_des(prev_prop_bind_des);
                        (
                            prev_des.get_propagation_binding(),
                            prev_des.get_dependency_track_point(),
                        )
                    };
                    let link_dep_track_point = calc_alg_context
                        .process_context()
                        .edge(rest_link)
                        .get_dependency_track_point();

                    let new_prop_bind_des = calc_alg_context
                        .process_context_mut()
                        .alloc_prop_binding_des(PropagationBindingDescriptor::new());
                    calc_alg_context
                        .process_context_mut()
                        .prop_binding_des_mut(new_prop_bind_des)
                        .set_data(new_prop_bind_des);
                    let mut new_dep_track_point: TrackPointId = Id::NONE;
                    let _bind_dep_node = self.create_propagate_bindings_successor_dependency(
                        &mut new_dep_track_point,
                        process_indi,
                        con_des,
                        prev_dep_track_point,
                        link_dep_track_point,
                        calc_alg_context,
                    );
                    if new_dep_track_point.is_none() {
                        // W3-DEFER[api]: createPROPAGATEBINDINGSSUCCESSORDependency(
                        // newDepTrackPoint, processIndi, conDes,
                        // prevPropBindDes->getDependencyTrackPoint(),
                        // restLink->getDependencyTrackPoint(), calcAlgContext) is
                        // invoked here, but the dependency base object is not
                        // materialized yet, so the previous dependency track point is
                        // carried until the factory backend lands.
                        new_dep_track_point = prev_dep_track_point;
                    }
                    calc_alg_context
                        .process_context_mut()
                        .prop_binding_des_mut(new_prop_bind_des)
                        .init_propagation_binding_descriptor(prop_binding, new_dep_track_point);

                    let prop_id = calc_alg_context
                        .process_context()
                        .prop_binding(prop_binding)
                        .get_propagation_id();
                    if update_existing {
                        let reapply_des = {
                            let data = calc_alg_context
                                .process_context_mut()
                                .prop_binding_set_mut(new_prop_binding_set)
                                .prop_map
                                .entry_mut(prop_id);
                            data.set_propagation_binding_descriptor(new_prop_bind_des);
                            data.get_reapply_concept_descriptor()
                        };
                        if reapply_des.is_some() {
                            self.apply_reapply_queue_concepts_propagation_binding(
                                succ_indi,
                                reapply_des,
                                calc_alg_context,
                            );
                        }
                    } else {
                        calc_alg_context
                            .process_context_mut()
                            .prop_binding_set_mut(new_prop_binding_set)
                            .prop_map
                            .map
                            .insert(prop_id, PropagationBindingMapData::new(new_prop_bind_des));
                    }
                    if new_prop_bind_des_linker.is_none() {
                        new_prop_bind_des_linker = new_prop_bind_des;
                    } else {
                        PropagationBindingDescriptor::append(
                            calc_alg_context.process_context_mut(),
                            new_prop_bind_des,
                            new_prop_bind_des_linker,
                        );
                        new_prop_bind_des_linker = new_prop_bind_des;
                    }
                    propagations = true;
                }
            }
            if new_prop_bind_des_linker.is_some() {
                super::super::process::propagation_binding::PropagationBindingSet::add_propagation_binding_descriptor_linker(
                    calc_alg_context.process_context_mut(),
                    new_prop_binding_set,
                    new_prop_bind_des_linker,
                );
            }
        }
        propagations
    }

    // =======================================================================
    // Propagation-binding propagation on the same node (cpp 13626–13801).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagatePropagationBindings`.
    /// cpp 13626–13688.
    ///
    /// The BINDPROPAGATEAND rule body: for each operand `bindingTriggerConcept` of
    /// `conProDes`'s concept it adds the trigger concept on `processIndi` (creating a
    /// BINDPROPAGATEAND dependency the first time) and either seeds the trigger's
    /// propagation-binding set (`propagateInitialPropagationBindings`, carrying the
    /// propagate-all flag) or freshly extends it (`propagateFreshPropagationBindings`,
    /// or sets the propagate-all flag), queueing the new descriptor + re-applying any
    /// pending reapply queue.
    pub fn propagate_propagation_bindings(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        propagate_all_flag: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 13626–13688. Outline:
        //
        //   conDes      = ctx.con_proc_desc(*con_pro_des).concept_descriptor();
        //   concept     = ctx.con_desc(conDes).concept();
        //   conceptNegation = negate;
        //   depTrackPoint   = ctx.con_proc_desc(*con_pro_des).dependency_track_point();
        //   opConLinker     = ctx.concept(concept).operand_list();          // concept operand neg-linker (unported accessor)
        //   STATINC(PBINDRULEANDAPPLICATIONCOUNT, ctx);
        //   conSet = ctx.node(*process_indi).getReapplyConceptLabelSet(false);     // node accessor (unported)
        //   nextDepTrackPoint = NONE;
        //   for opConLinkerIt in opConLinker {
        //       bindingTriggerConcept = opConLinkerIt.getData();
        //       bindingTriggerConceptNegation = opConLinkerIt.isNegated() ^ conceptNegation;
        //       if !conSet.getConceptDescriptorAndReapplyQueue(bindingTriggerConcept, &bindingConDes, &bindingDepTrackPoint, &reapplyQueue) {
        //           if nextDepTrackPoint.is_none() {
        //               conSet = ctx.node_mut(*process_indi).getReapplyConceptLabelSet(true);
        //               self.create_bindpropagateand_dependency(&mut nextDepTrackPoint, process_indi, conDes, depTrackPoint, ctx); // create*Dependency
        //           }
        //           bindingConDes = self.add_concept_to_individual_return_concept_descriptor(bindingTriggerConcept, bindingTriggerConceptNegation, *process_indi, nextDepTrackPoint, false, false, ctx);
        //           conPropBindingSetHash = ctx.node_mut(*process_indi).getConceptPropagationBindingSetHash(true);
        //           prevPropBindingSet    = conPropBindingSetHash.getPropagationBindingSet(concept, false);
        //           propBindingSet        = conPropBindingSetHash.getPropagationBindingSet(bindingTriggerConcept, true);
        //           propBindingSet.setConceptDescriptor(bindingConDes);
        //           if propagate_all_flag { propBindingSet.setPropagateAllFlag(true); }
        //           self.propagate_initial_propagation_bindings(process_indi, bindingConDes, propBindingSet, prevPropBindingSet, NONE, ctx);
        //       } else {
        //           conPropBindingSetHash = ctx.node_mut(*process_indi).getConceptPropagationBindingSetHash(true);
        //           prevPropBindingSet    = conPropBindingSetHash.getPropagationBindingSet(concept, false);
        //           propBindingSet        = conPropBindingSetHash.getPropagationBindingSet(bindingTriggerConcept, true);
        //           if self.propagate_fresh_propagation_bindings(process_indi, conDes, propBindingSet, prevPropBindingSet, NONE, ctx)
        //               || (propagate_all_flag && !propBindingSet.hasPropagateAllFlag()) {
        //               if propagate_all_flag { propBindingSet.setPropagateAllFlag(true); }
        //               self.set_individual_node_concept_label_set_modified(*process_indi, ctx);
        //               conProQueue = ctx.node_mut(*process_indi).getConceptProcessingQueue(true);
        //               self.add_concept_preprocessed_to_processing_queue(bindingConDes, bindingDepTrackPoint, conProQueue, *process_indi, true, ctx);
        //               if !reapplyQueue.isEmpty() {
        //                   conSet = ctx.node_mut(*process_indi).getReapplyConceptLabelSet(true);
        //                   reapplyQueueIt = CondensedReapplyQueueIterator(conSet.getConceptReapplyIterator(bindingConDes));
        //                   self.apply_reapply_queue_concepts(*process_indi, &reapplyQueueIt, ctx);
        //               }
        //           }
        //       }
        //   }
        //
        // KONCLUDE-PORT-NOTE[api]: `propagate_fresh_propagation_bindings` /
        // `propagate_initial_propagation_bindings` (the non-successor twins) are the
        // u34 siblings; the propagation-binding sets/maps + the node satellite
        // accessors are unported.
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateInitialPropagationBindings`.
    /// cpp 13773–13801.
    ///
    /// Same-node initial variant of `propagateInitialPropagationBindingsToSuccessor`:
    /// copies every propagation binding of `prevPropBindingSet` into
    /// `newPropBindingSet`, cloning each descriptor under a new PROPAGATEBINDING
    /// dependency (carrying `otherDependencies`). Returns whether anything was
    /// propagated.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `new_prop_binding_set` /
    /// `prev_prop_binding_set` (`CPropagationBindingSet*`) are arena ids;
    /// `other_dependencies` (`CDependency*`, the additional-dependency back-edge)
    /// remains an opaque handle until the dependency base lands.
    pub fn propagate_initial_propagation_bindings(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        new_prop_binding_set: PropagationBindingSetId,
        prev_prop_binding_set: PropagationBindingSetId,
        other_dependencies: DependencyHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut propagations = false;
        let mut new_prop_bind_des_linker: PropagationBindingDescriptorId = Id::NONE;
        if prev_prop_binding_set.is_some() {
            let _ = (*process_indi, con_des, other_dependencies);
            let adopted = {
                let prev_snapshot = {
                    let pc = calc_alg_context.process_context();
                    pc.prop_binding_set(prev_prop_binding_set)
                        .propagate_all_flag
                };
                let new_set = calc_alg_context
                    .process_context_mut()
                    .prop_binding_set_mut(new_prop_binding_set);
                let old_flag = new_set.propagate_all_flag;
                new_set.propagate_all_flag |= prev_snapshot;
                new_set.propagate_all_flag != old_flag
            };
            propagations |= adopted;

            let prev_map = {
                let pc = calc_alg_context.process_context();
                pc.prop_binding_set(prev_prop_binding_set).prop_map.clone()
            };
            calc_alg_context
                .process_context_mut()
                .prop_binding_set_mut(new_prop_binding_set)
                .copy_propagation_bindings(Some(&prev_map));

            let mut prop_keys: Vec<Cint64> = {
                let pc = calc_alg_context.process_context();
                pc.prop_binding_set(new_prop_binding_set)
                    .prop_map
                    .map
                    .keys()
                    .copied()
                    .collect()
            };
            prop_keys.sort();

            for prop_id in prop_keys {
                // W3-DEFER[macro]: STATINC(PBINDPROPAGATEDCOUNT, calcAlgContext)
                // W3-DEFER[macro]: STATINC(PBINDPROPAGATEDINITIALCOUNT, calcAlgContext)
                let prev_prop_bind_des = {
                    let data = calc_alg_context
                        .process_context_mut()
                        .prop_binding_set_mut(new_prop_binding_set)
                        .prop_map
                        .entry_mut(prop_id);
                    data.clear_reapply_concept_descriptor();
                    data.get_propagation_binding_descriptor()
                };
                let (prop_binding, prev_dep_track_point) = {
                    let pc = calc_alg_context.process_context();
                    let prev_des = pc.prop_binding_des(prev_prop_bind_des);
                    (
                        prev_des.get_propagation_binding(),
                        prev_des.get_dependency_track_point(),
                    )
                };

                let new_prop_bind_des = calc_alg_context
                    .process_context_mut()
                    .alloc_prop_binding_des(PropagationBindingDescriptor::new());
                calc_alg_context
                    .process_context_mut()
                    .prop_binding_des_mut(new_prop_bind_des)
                    .set_data(new_prop_bind_des);
                let mut new_dep_track_point: TrackPointId = Id::NONE;
                let _bind_dep_node = self.create_propagate_binding_dependency(
                    &mut new_dep_track_point,
                    process_indi,
                    con_des,
                    prev_dep_track_point,
                    other_dependencies,
                    calc_alg_context,
                );
                if new_dep_track_point.is_none() {
                    new_dep_track_point = prev_dep_track_point;
                }
                calc_alg_context
                    .process_context_mut()
                    .prop_binding_des_mut(new_prop_bind_des)
                    .init_propagation_binding_descriptor(prop_binding, new_dep_track_point);
                calc_alg_context
                    .process_context_mut()
                    .prop_binding_set_mut(new_prop_binding_set)
                    .prop_map
                    .entry_mut(prop_id)
                    .set_propagation_binding_descriptor(new_prop_bind_des);
                if new_prop_bind_des_linker.is_none() {
                    new_prop_bind_des_linker = new_prop_bind_des;
                } else {
                    PropagationBindingDescriptor::append(
                        calc_alg_context.process_context_mut(),
                        new_prop_bind_des,
                        new_prop_bind_des_linker,
                    );
                    new_prop_bind_des_linker = new_prop_bind_des;
                }
                propagations = true;
            }
            if new_prop_bind_des_linker.is_some() {
                super::super::process::propagation_binding::PropagationBindingSet::add_propagation_binding_descriptor_linker(
                    calc_alg_context.process_context_mut(),
                    new_prop_binding_set,
                    new_prop_bind_des_linker,
                );
            }
        }
        propagations
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::substrate::Id;
    use super::super::super::model::VariableId;
    use super::super::super::process::varbind::{
        VarBindingDescriptorId, VarBindingPathId, VariableBinding, VariableBindingDescriptor,
        VariableBindingPath,
    };
    use super::super::super::process::{NodeId, TrackPointId};
    use super::super::algorithm::CompletionTaskHandleAlgorithm;
    use super::*;

    fn key_map(
        process_context: Cint64,
        entries: &[(Cint64, Cint64, Cint64)],
    ) -> RepresentativeVariableBindingPathSetJoiningKeyMap {
        let mut map = RepresentativeVariableBindingPathSetJoiningKeyMap::new(process_context);
        for (joining_key, propagation_id, path_raw) in entries {
            map.get_joining_key_data_map(*joining_key, true)
                .expect("created joining-key bucket")
                .insert(*propagation_id, VarBindingPathId::new(*path_raw));
        }
        map
    }

    fn var_binding(
        ctx: &mut CalculationAlgorithmContextBase,
        variable: Cint64,
        individual: Cint64,
    ) -> super::super::super::process::varbind::VarBindingId {
        let id = ctx
            .process_context_mut()
            .alloc_var_binding(VariableBinding::new());
        ctx.process_context_mut()
            .var_binding_mut(id)
            .init_variable_binding(
                TrackPointId::NONE,
                NodeId::new(individual),
                VariableId::new(variable),
            );
        id
    }

    fn var_binding_path_from_bindings(
        ctx: &mut CalculationAlgorithmContextBase,
        prop_id: Cint64,
        bindings: &[super::super::super::process::varbind::VarBindingId],
    ) -> VarBindingPathId {
        let mut head = VarBindingDescriptorId::NONE;
        let mut last = VarBindingDescriptorId::NONE;
        for binding in bindings {
            let des = ctx
                .process_context_mut()
                .alloc_var_binding_des(VariableBindingDescriptor::new());
            ctx.process_context_mut()
                .var_binding_des_mut(des)
                .init_variable_binding_descriptor(*binding);
            if last.is_some() {
                ctx.process_context_mut()
                    .var_binding_des_mut(last)
                    .set_next(des);
            } else {
                head = des;
            }
            last = des;
        }
        let path = ctx
            .process_context_mut()
            .alloc_vbpath(VariableBindingPath::new());
        ctx.process_context_mut()
            .vbpath_mut(path)
            .init_variable_binding_path(prop_id, head);
        path
    }

    fn rep_data(
        ctx: &mut CalculationAlgorithmContextBase,
        rep_id: Cint64,
    ) -> RepresentativeVariableBindingPathSetDataId {
        let tag = ctx
            .process_context()
            .used_process_tagger()
            .get_current_localization_tag();
        let data = ctx.process_context_mut().alloc_rep_var_bind_path_set_data(
            RepresentativeVariableBindingPathSetData::new(INVALID, tag),
        );
        ctx.process_context_mut()
            .rep_var_bind_path_set_data_mut(data)
            .set_representative_id(rep_id)
            .add_key_signature_value(rep_id);
        data
    }

    fn add_representative_path(
        ctx: &mut CalculationAlgorithmContextBase,
        rep_data: RepresentativeVariableBindingPathSetDataId,
        prop_id: Cint64,
        path: VarBindingPathId,
    ) {
        let migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            ctx.process_context_mut(),
            rep_data,
            true,
        );
        let rep_id = ctx
            .process_context()
            .rep_var_bind_path_set_data(rep_data)
            .get_representative_id();
        let mut map_data = RepresentativeVariableBindingPathMapData::new(path, rep_data);
        map_data.resolve_rep_var_bind_path_set_data_id = rep_id;
        ctx.process_context_mut()
            .rep_var_bind_path_set_migrate_data_mut(migrate_data)
            .get_representative_variable_binding_path_map_mut()
            .insert(prop_id, map_data);
    }

    #[test]
    fn representative_common_joining_key_map_preserves_left_orientation_after_swap() {
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let first = key_map(0, &[(1, 11, 111), (2, 22, 222), (3, 33, 333)]);
        let second = key_map(0, &[(2, 220, 2220)]);
        let mut common = RepresentativeJoiningCommonKeyMap::new(0);

        algo.create_common_joining_key_map(
            &mut common,
            &first,
            Id::NONE,
            &second,
            Id::NONE,
            true,
            &mut ctx,
        );

        assert_eq!(common.count(), 1);
        let common_data = common.value(2).expect("common joining key");
        assert_eq!(common_data.get_left_count(), 1);
        assert_eq!(common_data.get_right_count(), 1);
        assert_eq!(
            common_data.get_left_joining_data_map().value(22),
            VarBindingPathId::new(222)
        );
        assert_eq!(
            common_data.get_right_joining_data_map().value(220),
            VarBindingPathId::new(2220)
        );
    }

    #[test]
    fn representatives_joinable_quick_fails_single_binding_disjoint_maps() {
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut node = NodeId::NONE;
        let left_rep = rep_data(&mut ctx, 101);
        let right_rep = rep_data(&mut ctx, 202);
        let variable = VariableId::new(1);
        let left_binding = var_binding(&mut ctx, variable.raw, 11);
        let right_binding = var_binding(&mut ctx, variable.raw, 22);
        let left_path = var_binding_path_from_bindings(&mut ctx, 11, &[left_binding]);
        let right_path = var_binding_path_from_bindings(&mut ctx, 22, &[right_binding]);
        add_representative_path(&mut ctx, left_rep, 11, left_path);
        add_representative_path(&mut ctx, right_rep, 22, right_path);

        assert!(!algo.are_representatives_joinable(
            &mut node,
            left_rep,
            right_rep,
            &[variable],
            &mut ctx,
        ));
        assert_eq!(algo.stat_representative_join_quick_fail_count, 1);
    }

    #[test]
    fn representatives_joinable_accepts_single_binding_shared_map_key() {
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut node = NodeId::NONE;
        let left_rep = rep_data(&mut ctx, 303);
        let right_rep = rep_data(&mut ctx, 404);
        let variable = VariableId::new(1);
        let left_binding = var_binding(&mut ctx, variable.raw, 33);
        let right_binding = var_binding(&mut ctx, variable.raw, 44);
        let left_path = var_binding_path_from_bindings(&mut ctx, 33, &[left_binding]);
        let right_path = var_binding_path_from_bindings(&mut ctx, 33, &[right_binding]);
        add_representative_path(&mut ctx, left_rep, 33, left_path);
        add_representative_path(&mut ctx, right_rep, 33, right_path);

        assert!(algo.are_representatives_joinable(
            &mut node,
            left_rep,
            right_rep,
            &[variable],
            &mut ctx,
        ));
        assert_eq!(algo.stat_representative_join_quick_fail_count, 0);
    }

    #[test]
    fn representative_common_joining_all_creates_joined_rep_and_resolve_maps() {
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let left_rep = rep_data(&mut ctx, 10);
        let right_rep = rep_data(&mut ctx, 20);

        let left_path = {
            let left_binding = var_binding(&mut ctx, 1, 101);
            var_binding_path_from_bindings(&mut ctx, 11, &[left_binding])
        };
        let right_path = {
            let right_binding = var_binding(&mut ctx, 2, 202);
            var_binding_path_from_bindings(&mut ctx, 22, &[right_binding])
        };

        let left_map = key_map(0, &[(7, 11, left_path.raw)]);
        let right_map = key_map(0, &[(7, 22, right_path.raw)]);
        let mut common = RepresentativeJoiningCommonKeyMap::new(0);
        algo.create_common_joining_key_map(
            &mut common,
            &left_map,
            left_rep,
            &right_map,
            right_rep,
            true,
            &mut ctx,
        );
        let mut extension = RepresentativeJoiningAllDataExtension::new(0);

        let joined_rep =
            algo.create_common_joining_all(&common, &mut extension, left_rep, right_rep, &mut ctx);

        assert_eq!(
            extension.get_representative_variable_binding_path_set_data(),
            joined_rep
        );
        let joined_rep_id = ctx
            .process_context()
            .rep_var_bind_path_set_data(joined_rep)
            .get_representative_id();
        assert_eq!(
            ctx.process_context()
                .rep_var_bind_path_set_data(joined_rep)
                .get_representative_key(),
            13 + joined_rep_id + 13 * joined_rep_id * 17
        );

        let joined_migrate = RepresentativeVariableBindingPathSetData::get_migrate_data(
            ctx.process_context_mut(),
            joined_rep,
            false,
        );
        let (merged_prop_id, merged_path) = {
            let joined_map = ctx
                .process_context()
                .rep_var_bind_path_set_migrate_data(joined_migrate)
                .get_representative_variable_binding_path_map();
            assert_eq!(joined_map.count(), 1);
            let (prop_id, map_data) = joined_map.map.iter().next().expect("merged path entry");
            (*prop_id, map_data.get_variable_binding_path())
        };
        assert_ne!(merged_path, left_path);
        assert_ne!(merged_path, right_path);

        let left_resolve = extension
            .get_left_resolve_variable_binding_path_map(false)
            .expect("left resolve map")
            .value(merged_prop_id);
        assert_eq!(left_resolve.get_variable_binding_path(), merged_path);
        assert_eq!(left_resolve.get_resolve_variable_binding_path(), left_path);
        assert_eq!(
            left_resolve.get_resolve_representative_variable_binding_path_set_data(),
            left_rep
        );

        let right_resolve = extension
            .get_right_resolve_variable_binding_path_map(false)
            .expect("right resolve map")
            .value(merged_prop_id);
        assert_eq!(right_resolve.get_variable_binding_path(), merged_path);
        assert_eq!(
            right_resolve.get_resolve_variable_binding_path(),
            right_path
        );
        assert_eq!(
            right_resolve.get_resolve_representative_variable_binding_path_set_data(),
            right_rep
        );

        let hash = ctx.processing_data_box().use_rep_var_bind_path_set_hash;
        assert!(hash.is_some());
        assert_eq!(
            RepresentativeVariableBindingPathSetHash::get_representative_variable_binding_path_set_data_for_data(
                ctx.process_context_mut(),
                hash,
                joined_rep,
                false,
            ),
            joined_rep
        );
    }
}
