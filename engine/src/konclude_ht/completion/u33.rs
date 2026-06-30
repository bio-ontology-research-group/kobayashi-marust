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

use super::super::model::substrate::Cint64;
use super::super::model::ConceptId;
use super::super::process::{ConDescId, ConProcDescId, DepLinkId, EdgeId, NodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // UN-DEFER WAVE STATUS (node-resolution keystone landed): the representative +
    // propagation-binding ARENAS now exist (`alloc_rep_var_bind_path_set_data` /
    // `alloc_rep_prop_des` / `alloc_rep_prop_set` / `alloc_prop_binding{,_des,_set}`),
    // but every body in this unit remains blocked on shared pieces that are NOT yet
    // present, so all 14 methods stay PORT-PENDING. Concretely:
    //
    //   RECONCILE-NEED: representative / propagation-binding dependency-factory
    //     wrappers — `create_representativeall_dependency`,
    //     `create_resolverepresentative_dependency`,
    //     `create_propagatebindingssuccessor_dependency`,
    //     `create_bindpropagateand_dependency`, `create_propagatebinding_dependency`.
    //     u29 ships only the atmost/reuse/qualify/implication/expanded/connection
    //     dependency creators; these five are absent. Every propagate*/update* body
    //     allocates a dependency track point through one of them, so none can land.
    //   RECONCILE-NEED: u11 representative-map siblings `has_common_variable_bindings`
    //     and `get_joined_variable_binding_path` are STILL Cint64-typed deferred stubs
    //     (their map `count()`/`contains()`/dual-cursor walk is W3-DEFER), so
    //     `are_representatives_joinable` / `create_common_joining_all` would call into
    //     stubs.
    //   RECONCILE-NEED: the representative satellite TYPED accessors
    //     (`getMigrateData` / `getRepresentativeVariableBindingPathMap` / `constBegin` /
    //     `getVariableBindingPath` / `getRepresentativeContainingMap` /
    //     `RepresentativeVariableBindingPathSetHash::get…`) are not reachable from the
    //     opaque `Cint64` handles these signatures still carry; un-deferring needs the
    //     signatures retyped to the real arena Ids in lock-step with the (deferred)
    //     call sites.
    // The propagation-binding SET/MAP types themselves (`process/propagation_binding.rs`)
    // ARE fully ported; only the dependency creators + u11 map walk gate the bodies.
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
    /// KONCLUDE-PORT-NOTE[api]: `left_rep_data` / `right_rep_data`
    /// (`CRepresentativeVariableBindingPathSetData*`) and `var_linker`
    /// (`CSortedLinker<CVariable*>*`) are unported representative satellite types →
    /// opaque `Cint64`.
    pub fn are_representatives_joinable(
        &mut self,
        process_indi: &mut NodeId,
        left_rep_data: Cint64,
        right_rep_data: Cint64,
        var_linker: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 10650–10669. Outline:
        //
        //   leftRepMigData  = leftRepData.getMigrateData();
        //   rightRepMigData = rightRepData.getMigrateData();
        //   if varLinker && leftRepMigData && rightRepMigData {
        //       leftRepVarBindMap  = leftRepMigData.getRepresentativeVariableBindingPathMap();
        //       rightRepVarBindMap = rightRepMigData.getRepresentativeVariableBindingPathMap();
        //       leftVarBindPath  = leftRepVarBindMap.constBegin().value().getVariableBindingPath();
        //       rightVarBindPath = rightRepVarBindMap.constBegin().value().getVariableBindingPath();
        //       if leftVarBindPath.getVariableBindingCount() == 1 && rightVarBindPath.getVariableBindingCount() == 1 {
        //           if !self.has_common_variable_bindings(process_indi, leftRepVarBindMap, rightRepVarBindMap, ctx) { // u11
        //               self.stat_representative_join_quick_fail_count += 1;
        //               return false;
        //           }
        //       }
        //   }
        //   return true;
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
    /// KONCLUDE-PORT-NOTE[api]: `rep_join_common_key_map`
    /// (`CRepresentativeJoiningCommonKeyMap*`), `join_all_ext_data`
    /// (`CRepresentativeJoiningAllDataExtension*`), `left_rep_data`/`right_rep_data`
    /// (`CRepresentativeVariableBindingPathSetData*`) → opaque `Cint64`.
    pub fn create_common_joining_all(
        &mut self,
        rep_join_common_key_map: Cint64,
        join_all_ext_data: Cint64,
        left_rep_data: Cint64,
        right_rep_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 10672–10715. Outline:
        //
        //   procDataBox    = ctx.used_processing_data_box_mut();
        //   processContext = ctx.used_process_context_mut();
        //   repData = processContext.alloc_<RepresentativeVariableBindingPathSetData>(...); // W6-DEFER[api] arena
        //   repData.initRepresentativeVariableBindingPathData(NONE);
        //   repData.setRepresentativeID(procDataBox.next_representative_variable_binding_path_id(true)); // db2
        //   repData.setMigratable(false); repData.incUseCount(); repData.incShareCount();
        //   repMigData = repData.getMigrateData(true);
        //   varBindPathResolveMap = repMigData.getRepresentativeVariableBindingPathMap();
        //   leftResolveMap  = joinAllExtData.getLeftResolveVariableBindingPathMap(true);
        //   rightResolveMap = joinAllExtData.getRightResolveVariableBindingPathMap(true);
        //   for (joiningKey, commonKeyData) in repJoinCommonKeyMap {
        //       leftKeyDataMap  = commonKeyData.getLeftJoiningDataMap();
        //       rightKeyDataMap = commonKeyData.getRightJoiningDataMap();
        //       for varBindPath1 in leftKeyDataMap.values() {
        //           for varBindPath2 in rightKeyDataMap.values() {
        //               mergedVarBindPath = self.get_joined_variable_binding_path(varBindPath1, varBindPath2, ctx); // u11
        //               leftResolveMap.insert(mergedVarBindPath.getPropagationID(),
        //                   RepVarBindPathMapData(mergedVarBindPath, varBindPath1, leftRepData));
        //               rightResolveMap.insert(mergedVarBindPath.getPropagationID(),
        //                   RepVarBindPathMapData(mergedVarBindPath, varBindPath2, rightRepData));
        //               varBindPathResolveMap.insert(mergedVarBindPath.getPropagationID(),
        //                   RepVarBindPathMapData(mergedVarBindPath, repData));
        //           }
        //       }
        //   }
        //   self.stat_representative_join_combines_count += 1;
        //   repMigData.getRepresentativeContainingMap().insertContainedRepresentative(repData, false);
        //   repData.addKeySignatureValue(repData.getRepresentativeID());
        //   repVarBindPathSetHash = procDataBox.representative_variable_binding_path_set_hash(true); // db2
        //   repVarBindPathSetHash.insertRepresentativeVariableBindingPathSetData(repData);
        //   joinAllExtData.setRepresentativeVariableBindingPathSetData(repData);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createCommonJoiningKeyMap`.
    /// cpp 10719–10767.
    ///
    /// Builds the intersection (`repJoinCommonKeyMap`) of two joining-key maps,
    /// orienting smaller-onto-larger (recursing with swapped left/right when the
    /// second map is smaller) and switching between a direct-lookup pass and a
    /// merge-walk pass on the `mMapComparisonDirectLookupFactor` heuristic.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the joining-key maps + representative set data are
    /// unported representative satellite types → opaque `Cint64`.
    pub fn create_common_joining_key_map(
        &mut self,
        rep_join_common_key_map: Cint64,
        first_joining_key_map: Cint64,
        first_rep_data: Cint64,
        sec_joining_key_map: Cint64,
        sec_rep_data: Cint64,
        first_left: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 10719–10767. Outline:
        //
        //   if secJoiningKeyMap.count() < firstJoiningKeyMap.count() {
        //       self.create_common_joining_key_map(repJoinCommonKeyMap,                 // recursive swap
        //           secJoiningKeyMap, secRepData, firstJoiningKeyMap, firstRepData, !firstLeft, ctx);
        //   }
        //   if firstJoiningKeyMap.count() * self.map_comparison_direct_lookup_factor < secJoiningKeyMap.count() {
        //       // direct-lookup pass: for each (key, firstDataMap) in firstJoiningKeyMap
        //       //   secDataMap = secJoiningKeyMap.value(key).getRepresentativeVariableBindingPathSetJoiningKeyDataMap();
        //       //   if secDataMap { orient (left,right) by firstLeft; repJoinCommonKeyMap.insert(key, CommonKeyData(left,right)); }
        //   } else {
        //       // merge-walk pass over the two sorted key maps in lock-step:
        //       //   key1==key2 && both data maps non-null -> orient + insert; advance both
        //       //   key1<key2 -> ++it1 ;  key2<key1 -> ++it2
        //   }
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
    /// KONCLUDE-PORT-NOTE[api]: `concept_op_linker` (`CSortedNegLinker<CConcept*>*`,
    /// the concept operand neg-linker) → opaque `Cint64`; the representative
    /// propagation sets/descriptors are unported satellite types.
    pub fn propagate_representative_to_successor(
        &mut self,
        process_indi: NodeId,
        succ_indi: &mut NodeId,
        // W3-RECONCILE[overload]: faithful arg is concept->getOperandList(); the
        // sole caller threads the CConcept id (operand list resolved when body lands).
        concept_op_linker: Cint64,
        negate: bool,
        con_des: ConDescId,
        rest_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 11050–11117. Outline:
        //
        //   depTrackPoint = ctx.con_desc(con_des).dependency_track_point();
        //   concept       = ctx.con_desc(con_des).concept();
        //   *succ_indi = self.get_localized_individual(*succ_indi, false, ctx);
        //   conSet = ctx.node(*succ_indi).getReapplyConceptLabelSet(false);     // node accessor (unported)
        //   nextDepTrackPoint = NONE; continuePropagation = false;
        //   for conceptOpLinkerIt in concept_op_linker {
        //       opConcept = conceptOpLinkerIt.getData();
        //       opConNeg  = conceptOpLinkerIt.isNegated() ^ negate;
        //       conRepPropSetHash     = ctx.node_mut(process_indi).getConceptRepresentativePropagationSetHash(true);
        //       prevRepPropSet        = conRepPropSetHash.getRepresentativePropagationSet(concept, false);
        //       succConRepPropSetHash = ctx.node_mut(*succ_indi).getConceptRepresentativePropagationSetHash(true);
        //       succRepPropSet        = succConRepPropSetHash.getRepresentativePropagationSet(opConcept, true);
        //       procRepPropDes = prevRepPropSet?.getOutgoingRepresentativePropagationDescriptorLinker();
        //       if procRepPropDes.is_none() { continue; }
        //       propDepTrackPoint = procRepPropDes.getDependencyTrackPoint();
        //       if !conSet.getConceptDescriptorAndReapplyQueue(opConcept, &bindingConDes, &bindingDepTrackPoint, &reapplyQueue) {
        //           self.stat_representative_propagate_succ_count += 1;
        //           if nextDepTrackPoint.is_none() {
        //               conSet = ctx.node_mut(*succ_indi).getReapplyConceptLabelSet(true);
        //               self.create_representativeall_dependency(&mut nextDepTrackPoint, process_indi, con_des,
        //                   propDepTrackPoint, ctx.edge(rest_link).dependency_track_point(), ctx);   // create*Dependency
        //           }
        //           bindingConDes = self.add_concept_to_individual_return_concept_descriptor(opConcept, opConNeg, *succ_indi, nextDepTrackPoint, false, false, ctx);
        //           succRepPropSet.setConceptDescriptor(bindingConDes);
        //           self.propagate_representative(*succ_indi, procRepPropDes, succRepPropSet, nextDepTrackPoint, ctx);
        //           continuePropagation = true;
        //       } else if self.requires_representative_propagation(*succ_indi, procRepPropDes, succRepPropSet, ctx) {
        //           self.stat_representative_propagate_succ_count += 1;
        //           if nextDepTrackPoint.is_none() {
        //               conSet = ctx.node_mut(*succ_indi).getReapplyConceptLabelSet(true);
        //               self.create_representativeall_dependency(&mut nextDepTrackPoint, process_indi, con_des,
        //                   propDepTrackPoint, ctx.edge(rest_link).dependency_track_point(), ctx);
        //           }
        //           self.propagate_representative(*succ_indi, procRepPropDes, succRepPropSet, nextDepTrackPoint, ctx);
        //           varCount = succRepPropSet.getOutgoingRepresentativePropagationDescriptorLinker()
        //                          .getRepresentativeVariableBindingPathSetData().getRepresentatedVariableCount();
        //           self.reapply_concept_updated_representative(*succ_indi, bindingConDes, bindingDepTrackPoint, varCount, conSet, reapplyQueue, ctx); // u10
        //           continuePropagation = true;
        //       }
        //   }
        //   if continuePropagation { self.add_individual_to_processing_queue(*succ_indi, ctx); }
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
    /// KONCLUDE-PORT-NOTE[api]: `rep_prop_set`
    /// (`CRepresentativePropagationSet*`) + every descriptor/set-data/map walked
    /// are unported representative satellite types → opaque `Cint64`.
    pub fn update_representative_propagation_set(
        &mut self,
        process_indi: &mut NodeId,
        rep_prop_set: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 11260–11375. Outline:
        //
        //   if repPropSet.getLastProcessedIncoming...Linker() == repPropSet.getIncoming...Linker() { return; }
        //   lastRepPropDes    = repPropSet.getLastProcessedIncomingRepresentativePropagationDescriptorLinker();
        //   lastIncRepPropDes = repPropSet.getIncomingRepresentativePropagationDescriptorLinker();
        //   lastOutRepPropDes = repPropSet.getOutgoingRepresentativePropagationDescriptorLinker();
        //   repPropSet.setLastProcessedIncoming...Linker(lastIncRepPropDes);
        //   if !repPropSet.getOutgoing...Linker() && !lastIncRepPropDes.hasNext() {
        //       repPropSet.setOutgoing...Linker(lastIncRepPropDes);
        //       if lastIncRepPropDes.getRepresentativeVariableBindingPathSetData()
        //              .isLocalizationTagUpToDate(ctx.getUsedProcessTagger()) {
        //           lastIncRepPropDes.getRepresentativeVariableBindingPathSetData().incShareCount();
        //       }
        //       return;
        //   }
        //   self.stat_representative_propagate_use_representative_count += 1;
        //   procDataBox = ctx.used_processing_data_box_mut();
        //   repVarBindPathSetHash = procDataBox.representative_variable_binding_path_set_hash(true); // db2
        //   migrateable = false; lastRepVarBindPathSetData = lastOutRepPropDes?.getRepresentativeVariableBindingPathSetData();
        //   if lastRepVarBindPathSetData && lastRepVarBindPathSetData.isLocalizationTagUpToDate(tagger) {
        //       lastRepVarBindPathSetData.decShareCount();
        //       if lastRepVarBindPathSetData.isMigratable() && shareCount<=0 && useCount<=20 { migrateable = true; }
        //   }
        //   repVarBindPathSetData = repVarBindPathSetHash.getRepresentativeVariableBindingPathSetData(repPropSet, true);
        //   repVarBindPathSetData.incShareCount(); repVarBindPathSetData.incUseCount();
        //   if !repVarBindPathSetData.hasMigrateData() {
        //       self.stat_representative_propagate_new_representative_count += 1;
        //       repVarBindPathSetData.setRepresentativeID(procDataBox.next_representative_variable_binding_path_id(true));
        //       updateNewOnly = false;
        //       if migrateable { updateNewOnly = true; repVarBindPathSetData.takeMigrateDataFrom(lastRepVarBindPathSetData); }
        //       else if lastRepVarBindPathSetData { updateNewOnly = true; repVarBindPathSetData.copyMigrateDataFrom(lastRepVarBindPathSetData); }
        //       repMigrateData = repVarBindPathSetData.getMigrateData(true);
        //       repVarBindPathMap = repMigrateData.getRepresentativeVariableBindingPathMap();
        //       untilUpdateRepPropDes = if updateNewOnly { lastRepPropDes } else { NONE };
        //       for newRepPropDesIt = lastIncRepPropDes; newRepPropDesIt != untilUpdateRepPropDes; newRepPropDesIt = newRepPropDesIt.getNext() {
        //           newRepVarBindPathSetData = newRepPropDesIt.getRepresentativeVariableBindingPathSetData();
        //           newRepMigrateData = newRepVarBindPathSetData.getMigrateData(true);
        //           repMigrateData.getRepresentativeContainingMap().insertContainedRepresentative(newRepVarBindPathSetData, true);
        //           repVarBindPathSetData.addKeySignatureValue(newRepVarBindPathSetData.getRepresentativeKey());
        //           newRepVarBindPathMap = newRepMigrateData.getRepresentativeVariableBindingPathMap();
        //           if newRepVarBindPathMap.count() * self.map_comparison_direct_lookup_factor <= repVarBindPathMap.count() {
        //               // direct-lookup union: insert (propID -> data) for each propID not already in repVarBindPathMap
        //           } else {
        //               // merge-walk union of the two sorted maps (insert at availIt cursor when prop key missing)
        //           }
        //       }
        //   } else {
        //       self.stat_representative_propagate_reused_representative_count += 1;
        //   }
        //   outPropRepDes = alloc_<RepresentativePropagationDescriptor>(taskMemMan);            // arena
        //   nextDepTrackPoint = NONE;
        //   repVarBindPathMap = repVarBindPathSetData.getMigrateData(false).getRepresentativeVariableBindingPathMap();
        //   repConMap         = repVarBindPathSetData.getMigrateData(false).getRepresentativeContainingMap();
        //   self.create_resolverepresentative_dependency(&mut nextDepTrackPoint, process_indi, repPropSet.getConceptDescriptor(),
        //       repVarBindPathMap, repPropSet.getRepresentativePropagationMap(),
        //       lastIncRepPropDes.getDependencyTrackPoint(), lastOutRepPropDes.getDependencyTrackPoint(), ctx);  // create*Dependency
        //   outPropRepDes.initRepresentativeDescriptor(repVarBindPathSetData, nextDepTrackPoint);
        //   repPropSet.addOutgoingRepresentativePropagationDescriptorLinker(outPropRepDes);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateRepresentative`.
    /// cpp 11379–11387.
    ///
    /// Allocates an incoming representative-propagation descriptor cloning
    /// `repPropDes`'s set data (with `nextDepTrackPoint`), links it into
    /// `repPropSet`, and re-folds the set via `updateRepresentativePropagationSet`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `rep_prop_des` / `rep_prop_set` are unported
    /// representative satellite types → opaque `Cint64`.
    pub fn propagate_representative(
        &mut self,
        process_indi: &mut NodeId,
        rep_prop_des: Cint64,
        rep_prop_set: Cint64,
        next_dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 11379–11387. Outline:
        //
        //   propagateRepDes = alloc_<RepresentativePropagationDescriptor>(taskMemMan);   // arena
        //   propagateRepDes.initRepresentativeDescriptor(repPropDes.getRepresentativeVariableBindingPathSetData(), next_dep_track_point);
        //   repPropSet.addIncomingRepresentativePropagation(propagateRepDes);
        //   self.update_representative_propagation_set(process_indi, rep_prop_set, ctx);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::requiresRepresentativePropagation`.
    /// cpp 11390–11444.
    ///
    /// Decides whether the representative carried by `repPropDes` adds anything to
    /// `testRepPropSet`: false if the set already contains the representative id or
    /// its containing-map covers it or the available outgoing map already subsumes
    /// every propagation variable-binding-path id (direct-lookup vs merge-walk on
    /// `mMapComparisonDirectLookupFactor`); otherwise true.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `rep_prop_des` / `test_rep_prop_set` are unported
    /// representative satellite types → opaque `Cint64`.
    pub fn requires_representative_propagation(
        &mut self,
        process_indi: &mut NodeId,
        rep_prop_des: Cint64,
        test_rep_prop_set: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 11390–11444. Outline:
        //
        //   propRepID = repPropDes.getRepresentativeVariableBindingPathSetData().getRepresentativeID();
        //   if testRepPropSet.containsRepresentativePropagation(propRepID) { return false; }
        //   lastRepPropDes = testRepPropSet.getOutgoingRepresentativePropagationDescriptorLinker();
        //   if lastRepPropDes {
        //       availMigData = lastRepPropDes.getRepresentativeVariableBindingPathSetData().getMigrateData(false);
        //       if availMigData {
        //           if availMigData.getRepresentativeContainingMap().contains(propRepID) { return false; }
        //           availVarBindPathMap = availMigData.getRepresentativeVariableBindingPathMap();
        //           propMigData = repPropDes.getRepresentativeVariableBindingPathSetData().getMigrateData(false);
        //           propVarBindPathMap = propMigData.getRepresentativeVariableBindingPathMap();
        //           if propVarBindPathMap.count() * self.map_comparison_direct_lookup_factor <= availVarBindPathMap.count() {
        //               // direct-lookup: return true on first prop key not in availVarBindPathMap, else false
        //           } else {
        //               // merge-walk: return true when a prop key has no avail match, else false
        //           }
        //       }
        //   }
        //   return true;
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
    /// → opaque `Cint64`; the propagation-binding sets are unported satellite types.
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
        // PORT-PENDING: faithful transcription of cpp 13294–13355. Outline:
        //
        //   depTrackPoint = ctx.con_desc(con_des).dependency_track_point();
        //   concept       = ctx.con_desc(con_des).concept();
        //   *succ_indi = self.get_localized_individual(*succ_indi, false, ctx);
        //   conSet = ctx.node(*succ_indi).getReapplyConceptLabelSet(false);    // node accessor (unported)
        //   nextDepTrackPoint = NONE; continuePropagation = false;
        //   for conceptOpLinkerIt in concept_op_linker {
        //       opConcept = conceptOpLinkerIt.getData();
        //       opConNeg  = conceptOpLinkerIt.isNegated() ^ negate;
        //       if !conSet.getConceptDescriptorAndReapplyQueue(opConcept, &bindingConDes, &bindingDepTrackPoint, &reapplyQueue) {
        //           if nextDepTrackPoint.is_none() {
        //               conSet = ctx.node_mut(process_indi).getReapplyConceptLabelSet(true);
        //               self.create_bindpropagateall_dependency(&mut nextDepTrackPoint, process_indi, con_des,
        //                   depTrackPoint, ctx.edge(rest_link).dependency_track_point(), ctx);     // create*Dependency
        //           }
        //           bindingConDes = self.add_concept_to_individual_return_concept_descriptor(opConcept, opConNeg, *succ_indi, nextDepTrackPoint, false, false, ctx);
        //           conPropBindingSetHash = ctx.node_mut(process_indi).getConceptPropagationBindingSetHash(true);
        //           prevPropBindingSet    = conPropBindingSetHash.getPropagationBindingSet(concept, false);
        //           succConPropBindingSetHash = ctx.node_mut(*succ_indi).getConceptPropagationBindingSetHash(true);
        //           propBindingSet        = succConPropBindingSetHash.getPropagationBindingSet(opConcept, true);
        //           propBindingSet.setConceptDescriptor(bindingConDes);
        //           self.propagate_initial_propagation_bindings_to_successor(process_indi, *succ_indi, bindingConDes, propBindingSet, prevPropBindingSet, rest_link, ctx);
        //           continuePropagation = true;
        //       } else {
        //           conPropBindingSetHash = ctx.node_mut(process_indi).getConceptPropagationBindingSetHash(true);
        //           prevPropBindingSet    = conPropBindingSetHash.getPropagationBindingSet(concept, false);
        //           succConPropBindingSetHash = ctx.node_mut(*succ_indi).getConceptPropagationBindingSetHash(true);
        //           propBindingSet        = succConPropBindingSetHash.getPropagationBindingSet(opConcept, true);
        //           if self.propagate_fresh_propagation_bindings_to_successor(process_indi, *succ_indi, con_des, propBindingSet, prevPropBindingSet, rest_link, ctx) {
        //               self.set_individual_node_concept_label_set_modified(*succ_indi, ctx);
        //               conProQueue = ctx.node_mut(*succ_indi).getConceptProcessingQueue(true);
        //               self.add_concept_preprocessed_to_processing_queue(bindingConDes, bindingDepTrackPoint, conProQueue, *succ_indi, true, ctx);
        //               if !reapplyQueue.isEmpty() {
        //                   conSet = ctx.node_mut(*succ_indi).getReapplyConceptLabelSet(true);
        //                   reapplyQueueIt = CondensedReapplyQueueIterator(conSet.getConceptReapplyIterator(bindingConDes));
        //                   self.apply_reapply_queue_concepts(*succ_indi, &reapplyQueueIt, ctx);
        //               }
        //               continuePropagation = true;
        //           }
        //       }
        //   }
        //   if continuePropagation { self.add_individual_to_processing_queue(*succ_indi, ctx); }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateInitialPropagationBindingsToSuccessor`.
    /// cpp 13362–13390.
    ///
    /// Initial (whole-set copy) variant: copies every propagation binding of
    /// `prevPropBindingSet` into the fresh `newPropBindingSet`, cloning each
    /// descriptor under a new PROPAGATEBINDINGSSUCCESSOR dependency. Returns whether
    /// anything was propagated (including the propagate-all flag adoption).
    ///
    /// KONCLUDE-PORT-NOTE[api]: `new_prop_binding_set` / `prev_prop_binding_set`
    /// (`CPropagationBindingSet*`) → opaque `Cint64`.
    pub fn propagate_initial_propagation_bindings_to_successor(
        &mut self,
        process_indi: &mut NodeId,
        succ_indi: NodeId,
        con_des: ConDescId,
        new_prop_binding_set: Cint64,
        prev_prop_binding_set: Cint64,
        rest_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 13362–13390. Outline:
        //
        //   propagations = false; newPropBindDesLinker = NONE;
        //   if prevPropBindingSet {
        //       propagations |= newPropBindingSet.adoptPropagateAllFlag(prevPropBindingSet);
        //       newPropBindingSet.copyPropagationBindings(prevPropBindingSet.getPropagationBindingMap());
        //       for (_, propBindMapData) in newPropBindingSet.getPropagationBindingMap() {
        //           STATINC(PBINDPROPAGATEDCOUNT, ctx); STATINC(PBINDPROPAGATEDINITIALCOUNT, ctx);
        //           propBindMapData.clearReapplyConceptDescriptor();
        //           prevPropBindDes = propBindMapData.getPropagationBindingDescriptor();
        //           newPropBindDes  = alloc_<PropagationBindingDescriptor>(taskMemMan);    // arena
        //           newDepTrackPoint = NONE;
        //           self.create_propagatebindingssuccessor_dependency(&mut newDepTrackPoint, process_indi, con_des,
        //               prevPropBindDes.getDependencyTrackPoint(), ctx.edge(rest_link).dependency_track_point(), ctx); // create*Dependency
        //           newPropBindDes.initPropagationBindingDescriptor(prevPropBindDes.getPropagationBinding(), newDepTrackPoint);
        //           propBindMapData.setPropagationBindingDescriptor(newPropBindDes);
        //           newPropBindDesLinker = newPropBindDes.append(newPropBindDesLinker);
        //           propagations = true;
        //       }
        //       if newPropBindDesLinker { newPropBindingSet.addPropagationBindingDescriptorLinker(newPropBindDesLinker); }
        //   }
        //   return propagations;
        false
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
    /// KONCLUDE-PORT-NOTE[api]: `new_prop_binding_set` / `prev_prop_binding_set`
    /// → opaque `Cint64`.
    pub fn propagate_fresh_propagation_bindings_to_successor(
        &mut self,
        process_indi: &mut NodeId,
        succ_indi: NodeId,
        con_des: ConDescId,
        new_prop_binding_set: Cint64,
        prev_prop_binding_set: Cint64,
        rest_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 13395–13463. Outline:
        //
        //   propagations = false;
        //   if prevPropBindingSet {
        //       propagations |= newPropBindingSet.adoptPropagateAllFlag(prevPropBindingSet);
        //       prevPropBindMap = prevPropBindingSet.getPropagationBindingMap();
        //       newPropBindMap  = newPropBindingSet.getPropagationBindingMap();
        //       itNew = newPropBindMap.begin(); (itPrev, itPrevEnd) = prevPropBindMap iter; newPropBindDesLinker = NONE;
        //       while itPrev != itPrevEnd {
        //           prevPropID = itPrev.key(); doPropagation = false; updateExisting = false;
        //           if itNew == newPropBindMap.end() { doPropagation = true; }
        //           else {
        //               newPropID = itNew.key();
        //               if newPropID < prevPropID { ++itNew; }
        //               else if newPropID == prevPropID {
        //                   if !itNew.value().hasPropagationBindingDescriptor() { doPropagation = true; updateExisting = true; }
        //                   else { ++itNew; ++itPrev; }
        //               } else { doPropagation = true; }
        //           }
        //           if doPropagation {
        //               STATINC(PBINDPROPAGATEDCOUNT, ctx); STATINC(PBINDPROPAGATEDFRESHCOUNT, ctx);
        //               prevPropBindDes = itPrev.value().getPropagationBindingDescriptor();
        //               newPropBindDes  = alloc_<PropagationBindingDescriptor>(taskMemMan);
        //               newDepTrackPoint = NONE;
        //               self.create_propagatebindingssuccessor_dependency(&mut newDepTrackPoint, process_indi, con_des,
        //                   prevPropBindDes.getDependencyTrackPoint(), ctx.edge(rest_link).dependency_track_point(), ctx);
        //               propBinding = prevPropBindDes.getPropagationBinding();
        //               newPropBindDes.initPropagationBindingDescriptor(propBinding, newDepTrackPoint);
        //               if updateExisting {
        //                   data = newPropBindMap[propBinding.getPropagationID()];
        //                   data.setPropagationBindingDescriptor(newPropBindDes);
        //                   if let Some(reapplyDes) = data.getReapplyConceptDescriptor() {
        //                       self.apply_reapply_queue_concepts(succ_indi, reapplyDes, ctx);   // u10
        //                   }
        //               } else {
        //                   itNew = newPropBindMap.insert(propBinding.getPropagationID(), PropagationBindingMapData(newPropBindDes));
        //               }
        //               newPropBindDesLinker = newPropBindDes.append(newPropBindDesLinker);
        //               propagations = true;
        //           }
        //       }
        //       if newPropBindDesLinker { newPropBindingSet.addPropagationBindingDescriptorLinker(newPropBindDesLinker); }
        //   }
        //   return propagations;
        false
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
    /// KONCLUDE-PORT-NOTE[api]: `new_prop_binding_set` / `prev_prop_binding_set`
    /// (`CPropagationBindingSet*`) → opaque `Cint64`; `other_dependencies`
    /// (`CDependency*`, the additional-dependency back-edge) → `DepLinkId`.
    pub fn propagate_initial_propagation_bindings(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        new_prop_binding_set: Cint64,
        prev_prop_binding_set: Cint64,
        other_dependencies: DepLinkId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 13773–13801. Outline:
        //
        //   propagations = false; newPropBindDesLinker = NONE;
        //   if prevPropBindingSet {
        //       propagations |= newPropBindingSet.adoptPropagateAllFlag(prevPropBindingSet);
        //       newPropBindingSet.copyPropagationBindings(prevPropBindingSet.getPropagationBindingMap());
        //       for (_, propBindMapData) in newPropBindingSet.getPropagationBindingMap() {
        //           STATINC(PBINDPROPAGATEDCOUNT, ctx); STATINC(PBINDPROPAGATEDINITIALCOUNT, ctx);
        //           propBindMapData.clearReapplyConceptDescriptor();
        //           prevPropBindDes = propBindMapData.getPropagationBindingDescriptor();
        //           newPropBindDes  = alloc_<PropagationBindingDescriptor>(taskMemMan);    // arena
        //           newDepTrackPoint = NONE;
        //           self.create_propagatebinding_dependency(&mut newDepTrackPoint, process_indi, con_des,
        //               prevPropBindDes.getDependencyTrackPoint(), other_dependencies, ctx);   // create*Dependency
        //           newPropBindDes.initPropagationBindingDescriptor(prevPropBindDes.getPropagationBinding(), newDepTrackPoint);
        //           propBindMapData.setPropagationBindingDescriptor(newPropBindDes);
        //           newPropBindDesLinker = newPropBindDes.append(newPropBindDesLinker);
        //           propagations = true;
        //       }
        //       if newPropBindDesLinker { newPropBindingSet.addPropagationBindingDescriptorLinker(newPropBindDesLinker); }
        //   }
        //   return propagations;
        false
    }
}
