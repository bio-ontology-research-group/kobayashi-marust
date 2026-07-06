//! `completion::u32` — W3 completion method-batch **Unit 32**
//! (family: Generic helpers / accessors / label tests).
//!
//! Faithful function-by-function port of the 9 methods of Konclude
//! `CCalculationTableauCompletionTaskHandleAlgorithm`
//! (`Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`)
//! that `manifest/01-completion-methods.md` Unit 32 groups under generic
//! helpers / accessors / label tests. Method order follows the manifest
//! (ascending `.cpp` line). cpp line ranges (1-based) are noted on each item:
//!
//!   * `establishIndividualReusing`                     [5193-5298]
//!   * `reactivateIndirectReuseSuccessors`              [6486-6503]
//!   * `cancellationRootTask`                           [6902-6932]
//!   * `cancellationTask`                               [6935-6949]
//!   * `generateDebugIndiStatusString`                  [8039-8173]
//!   * `generateExtendedDebugConceptSetStringList`      [8301-8362]
//!   * `writeGeneratedExtendedDebugIndiModelStringList` [8368-8393]
//!   * `generateExtendedDebugIndiModelStringList`       [8396-8625]
//!   * `generateDebugIndiModelStringList`               [8629-8718]
//!
//! Bodies use the W3.5 accessor convention (PORT.md): a C++ `indi->getX()` where
//! `indi` is a `CIndividualProcessNode*` becomes
//! `ctx.process_context().node(id).get_x()` (read) /
//! `ctx.process_context_mut().node_mut(id)` (mutate); `getUsedProcessingDataBox()`
//! → `ctx.processing_data_box{,_mut}()`; the static terminology (`CConcept`/`CRole`)
//! via `ctx.ontology_arenas()`; sibling algorithm methods → `self.x(...)`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: pointers become arena ids (`CIndividualProcessNode*`
//! → `NodeId`, `CConceptDescriptor*` → `ConDescId`, `CReapplyConceptLabelSet*` →
//! `LabelSetId`, `CIndividualLinkEdge*` → `EdgeId`, `CDependencyTrackPoint*` →
//! `TrackPointId`); a `CIndividualProcessNode*&` out/in-out reference becomes
//! `&mut NodeId`; the `calcAlgContext` pointer becomes the threaded
//! `&mut CalculationAlgorithmContextBase`.
//!
//! Family character: this unit is the reusing-establishment branch trigger, the
//! root/task cancellation pair, and the four completion-graph debug-dump helpers.
//! Only `generate_debug_indi_status_string` bottoms out cleanly on the ported node
//! flag set; the remainder sit on not-yet-ported subsystems and Qt I/O:
//!   - the **Task** machinery (`CSatisfiableCalculationTask`,
//!     `createDependendBranchingTaskList`, `CTaskProcessorContext`,
//!     `getTaskProcessorCommunicator`, `getSatisfiableCalculationTaskResult`) →
//!     `// W6-DEFER[api]`;
//!   - the **dependency-creation** sibling helpers (`createREUSEINDIVIDUALDependency`,
//!     `createNonDeterministicDependencyTrackPointBranch`, …) → `self.x(...)`
//!     forward references resolved when their dependency-tracking units land;
//!   - the per-node **satellites** (`CReusingIndividualNodeConceptExpansionData`,
//!     `CSignatureBlockingIndividualNodeConceptExpansionData`, the concept-label-set
//!     iterator, the prop-/var-binding hashes, the backend-sync data, the successor
//!     iterators) → `// W6-DEFER[api]` / `// W3-DEFER[api]`;
//!   - the **string formatters** (`CConceptTextFormater`, `CIRIName`) and **Qt**
//!     (`QString`/`QStringList`/`QFile`) → faithful Rust `String`/`Vec<String>`,
//!     with the formatter/file pieces deferred;
//!   - the C++ `throw CCalculationStopProcessingException(true)` → `// [exceptions]`
//!     + early return (no unwinding control flow is introduced).
//! Per the port convention no logic is dropped: every deferred dereference is kept
//! in-comment and the control flow is transcribed structurally.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::process::node::IndividualProcessNode;
use super::super::process::stubs::{ConceptPropBindingSetHashId, ConceptVarBindPathSetHashId};
use super::super::process::{ConDescId, EdgeId, LabelSetId, NodeId};
use super::context::CalculationAlgorithmContextBase;
use super::stubs::SatisfiableCalculationTask;

/// KONCLUDE-PORT-NOTE[api]: `CSatisfiableCalculationTask*` is reached through the
/// not-yet-ported Task subsystem; here it is the `stubs::SatisfiableCalculationTask`
/// marker addressed by `Id<…>` (the same handle the context's `used_sat_calc_task`
/// uses). A not-yet-resolvable task pointer is `Id::NONE`.
type SatTaskId = Id<SatisfiableCalculationTask>;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Reusing establishment — the individual-reusing branch trigger
    // (cpp 5193-5298).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::establishIndividualReusing`.
    /// cpp 5193-5298.
    ///
    /// Splits the current test into a two-way non-deterministic branch over whether
    /// `process_indi` reuses `reuse_indi`'s (analysed) concept expansion. Alternative
    /// 0 installs the reuse: it copies the blocker's label-set signature into the
    /// localized node's `CReusingIndividualNodeConceptExpansionData`, non-det adds the
    /// blocker's analysed non-deterministic concepts the node is still missing, flags
    /// the node `PRFREUSINGINDIVIDUAL`, and registers the reuse-blocker following /
    /// indirect-successor-reuse-blocked propagation. Alternative 1 records the reuse
    /// failure (failed signature + individual). Both prepare a branched task, set its
    /// reusing priority, and the pair is submitted; the method then STOPS the current
    /// task via the calculation-stop exception.
    ///
    /// KONCLUDE-PORT-NOTE[exceptions]: the terminal
    /// `throw CCalculationStopProcessingException(true)` becomes a tagged early
    /// return — the whole body is the branch-creation side effect; nothing follows
    /// the throw in C++.
    pub fn establish_individual_reusing(
        &mut self,
        process_indi: NodeId,
        mut reuse_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // reuseDepNode = createREUSEINDIVIDUALDependency(processIndi, nullptr, nullptr, ctx)
        let reuse_dep_node = self.create_reuse_individual_dependency(
            process_indi,
            Id::NONE,
            Id::NONE,
            calc_alg_context,
        );

        // newTaskList = createDependendBranchingTaskList(2, ctx)
        // W6-DEFER[api]: the branching-task list is created via the Task subsystem.
        let new_task_list: SatTaskId =
            self.create_dependend_branching_task_list(2, calc_alg_context);
        // processorContext = calcAlgContext->getUsedTaskProcessorContext()
        // W6-DEFER[api]: the task-processor context is the scheduler handle.
        let processor_context: Cint64 = INVALID;

        // anlyzeIndiviudalNodesConceptExpansion(reuseIndi, ctx)
        self.anlyze_indiviudal_nodes_concept_expansion(&mut reuse_indi, calc_alg_context);
        // blockerAnalizedConExpData = reuseIndi->getAnalizedConceptExpansionData(false)
        // W6-DEFER[api]: CIndividualNodeAnalizedConceptExpansionData is an unported
        // node satellite; its presence gates the whole branch body.
        let blocker_analized_con_exp_data: Cint64 = INVALID;
        if blocker_analized_con_exp_data != INVALID {
            // nonDetExpLinker = blockerAnalizedConExpData->getAnalysedNonDeterministicConceptExpansionLinker()
            // W6-DEFER[api]: the analysed non-deterministic concept-descriptor chain.
            // Walked below as `non_det_exp_linker` (deferred empty until the satellite lands).
            let non_det_exp_linker: &[ConDescId] = &[];

            // newTaskIt = newTaskList
            let mut new_task_it: SatTaskId = new_task_list;
            for i in 0..2 {
                let reusing_alternative = i == 0;

                let new_sat_calc_task: SatTaskId = new_task_it;
                // newProcessContext = newSatCalcTask->getProcessContext(processorContext)
                // newCalcAlgContext = createCalculationAlgorithmContext(processorContext, newProcessContext, newSatCalcTask)
                // newProcessingDataBox = newSatCalcTask->getProcessingDataBox()
                // W6-DEFER[api]: each branch task owns its OWN per-test context /
                // databox; in the by-value port the per-thread `calc_alg_context` is
                // the single context, so the freshly created branch context is the
                // deferred handle the C++ allocates per task.
                //
                // newProcessTagger = newCalcAlgContext->getUsedProcessTagger()
                // newProcessTagger->incBranchingTag(); newProcessTagger->incLocalizationTag()
                // W6-DEFER[api]: CProcessTagger (branching/localization tag) is unported.

                // newLocIndiNode = getLocalizedIndividual(processIndi, false, newCalcAlgContext)
                let mut new_loc_indi_node =
                    self.get_localized_individual(process_indi, false, calc_alg_context);
                // newConProcQueue = newLocIndiNode->getConceptProcessingQueue(true)
                let _new_con_proc_queue = calc_alg_context
                    .process_context_mut()
                    .node_mut(new_loc_indi_node)
                    .get_concept_processing_queue(true);

                // locReusingData = newLocIndiNode->getReusingIndividualNodeConceptExpansionData(true)
                // W6-DEFER[api]: CReusingIndividualNodeConceptExpansionData is an
                // unported node satellite. The C++ lazily allocates + initBlockingExpansionData
                // from the base reusing data when absent, then resets every counter and,
                // for the reusing alternative, copies the localized node's label-set
                // signature into it. Reproduced structurally; all field writes deferred.
                //
                // if (!locReusingData) {
                //   taskMemMan = newCalcAlgContext->getUsedProcessTaskMemoryAllocationManager();
                //   reusingData = newLocIndiNode->getReusingIndividualNodeConceptExpansionData(false);
                //   locReusingData = allocateAndConstruct<CReusingIndividualNodeConceptExpansionData>(taskMemMan);
                //   locReusingData->initBlockingExpansionData(reusingData);
                //   newLocIndiNode->setReusingIndividualNodeConceptExpansionData(locReusingData);
                // }
                // locReusingData->incReusingTriedCount();
                // locReusingData->setBlockingConceptCount(0);
                // locReusingData->setBlockingConceptSignature(0);
                // locReusingData->setLastSubsetTestedConceptDescriptor(nullptr);
                // locReusingData->setContinuousExpandedContainedConceptCount(0);
                // locReusingData->setBlockerIndividualNode(nullptr);
                // locReusingData->setLastUpdatedConceptCount(0);
                // locReusingData->setLastUpdatedConceptExpansionCount(0);
                // locReusingData->setBlockingReviewMarked(false);

                if reusing_alternative {
                    // newDependencyTrackPoint = createNonDeterministicDependencyTrackPointBranch(reuseDepNode, false, ctx)
                    let new_dependency_track_point = self
                        .create_non_deterministic_dependency_track_point_branch(
                            reuse_dep_node,
                            false,
                            calc_alg_context,
                        );

                    // reuseConceptsDepNode = createREUSECONCEPTSDependency(processIndi, nullptr, newDependencyTrackPoint, ctx)
                    let reuse_concepts_dep_node = self.create_reuse_concepts_dependency(
                        process_indi,
                        Id::NONE,
                        new_dependency_track_point,
                        calc_alg_context,
                    );
                    // reuseConceptsDependencyTrackPoint = createNonDeterministicDependencyTrackPointBranch(reuseConceptsDepNode, true, ctx)
                    let reuse_concepts_dependency_track_point = self
                        .create_non_deterministic_dependency_track_point_branch(
                            reuse_concepts_dep_node,
                            true,
                            calc_alg_context,
                        );

                    // locReusingData->setReuseConceptsDependencyTrackPoint(reuseConceptsDependencyTrackPoint)
                    // W6-DEFER[api]: reusing-data field write (satellite).

                    // indiLabelSet = newLocIndiNode->getReapplyConceptLabelSet(true)
                    // W6-DEFER[api]: getReapplyConceptLabelSet(true) lazily allocates the
                    // node's CReapplyConceptLabelSet (unported satellite getter); the
                    // signature/count/last-descriptor copies below read from it.
                    let indi_label_set: LabelSetId = Id::NONE;

                    // locReusingData->setBlockingConceptCount(indiLabelSet->getConceptCount());
                    // locReusingData->setBlockingConceptSignature(indiLabelSet->getConceptSignatureValue());
                    // locReusingData->setLastSubsetTestedConceptDescriptor(indiLabelSet->getAddingSortedConceptDescriptionLinker());
                    // locReusingData->setContinuousExpandedContainedConceptCount(0);
                    // locReusingData->setBlockerIndividualNode(reuseIndi);
                    // locReusingData->setLastUpdatedConceptCount(0);
                    // locReusingData->setLastUpdatedConceptExpansionCount(0);
                    // W6-DEFER[api]: reusing-data / label-set field copies (satellites).

                    // for each reusingConDes in nonDetExpLinker: if !indiLabelSet contains it,
                    //   non-deterministically add the missing concept to the localized node.
                    for &reusing_con_des in non_det_exp_linker.iter() {
                        // if (!indiLabelSet->containsConceptDescriptor(reusingConDes)) { ... }
                        // W6-DEFER[api]: containsConceptDescriptor is a label-set satellite
                        // test; held false so the add is reached faithfully when it lands.
                        let contains = false;
                        if !contains {
                            // addConceptToIndividual(reusingConDes->getConcept(), reusingConDes->isNegated(),
                            //   newLocIndiNode, reuseConceptsDependencyTrackPoint, false, true, newCalcAlgContext)
                            let concept = calc_alg_context
                                .process_context()
                                .con_desc(reusing_con_des)
                                .get_concept();
                            let negated = calc_alg_context
                                .process_context()
                                .con_desc(reusing_con_des)
                                .is_negated();
                            self.add_concept_to_individual(
                                concept,
                                negated,
                                &mut new_loc_indi_node,
                                reuse_concepts_dependency_track_point,
                                false,
                                true,
                                calc_alg_context,
                            );
                        }
                    }

                    // newLocIndiNode->addProcessingRestrictionFlags(PRFREUSINGINDIVIDUAL)
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(new_loc_indi_node)
                        .add_processing_restriction_flags(
                            IndividualProcessNode::PRF_REUSINGINDIVIDUAL,
                        );

                    // addReusingBlockerFollowing(newLocIndiNode, newCalcAlgContext)
                    self.add_reusing_blocker_following(new_loc_indi_node, calc_alg_context);
                    // propagateIndirectSuccessorReuseBlocked(newLocIndiNode, newCalcAlgContext)
                    self.propagate_indirect_successor_reuse_blocked(
                        new_loc_indi_node,
                        calc_alg_context,
                    );
                } else {
                    // newDependencyTrackPoint = createNonDeterministicDependencyTrackPointBranch(reuseDepNode, false, ctx)
                    let _new_dependency_track_point = self
                        .create_non_deterministic_dependency_track_point_branch(
                            reuse_dep_node,
                            false,
                            calc_alg_context,
                        );
                    // locReusingData->incReusingFailedCount();
                    // locReusingData->addReusingFailedSignatureAndIndividual(
                    //   reuseIndi->getReapplyConceptLabelSet(false)->getConceptSignatureValue(),
                    //   reuseIndi->getIndividualNodeID());
                    // W6-DEFER[api]: reusing-data failure recording (satellite) + label-set
                    // signature read of reuseIndi.
                }

                // prepareBranchedTaskProcessing(newLocIndiNode, newTaskIt, newCalcAlgContext)
                self.prepare_branched_task_processing(
                    new_loc_indi_node,
                    new_task_it,
                    calc_alg_context,
                );

                // newTaskPriority = calcAlgContext->getUsedTaskPriorityStrategy()->getPriorityForTaskReusing(
                //   newSatCalcTask, calcAlgContext->getUsedSatisfiableCalculationTask(), reusingAlternative);
                // newSatCalcTask->setTaskPriority(newTaskPriority);
                // W6-DEFER[api]: task-priority strategy + task priority set are Task/Strategy.

                // newTaskIt = (CSatisfiableCalculationTask*)newTaskIt->getNext()
                // W6-DEFER[api]: branch-task list link advance.
                new_task_it = Id::NONE;
            }

            // processorContext->getTaskProcessorCommunicator()->communicateTaskCreation(newTaskList)
            // W6-DEFER[api]: submit the created branch tasks to the scheduler.

            // [exceptions]: throw CCalculationStopProcessingException(true) — STOP the
            // current task. Ported as an early return after the side effects above.
            let _ = (new_task_list, processor_context);
            return;
        }
    }

    // =======================================================================
    // Indirect reuse-successor reactivation (cpp 6486-6503).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reactivateIndirectReuseSuccessors`.
    /// cpp 6486-6503.
    ///
    /// Walks `indi`'s successor links; for every successor that is strictly deeper
    /// (a real successor, not the ancestor edge) and flagged
    /// `PRFANCESTORREUSINGINDIVIDUALBLOCKED` but not yet
    /// `…BLOCKEDABOLISHED`, localizes the successor and sets the abolished flag —
    /// reactivating reuse-blocked successors after the reuse blocker changed.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `recursive` is taken (matching the C++ signature)
    /// but, as in the original, this body does not recurse on it.
    pub fn reactivate_indirect_reuse_successors(
        &mut self,
        indi: &mut NodeId,
        recursive: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // succIt = indi->getSuccessorIterator()
        // W6-DEFER[api]: CSuccessorIterator walks the node's successor-role hash, an
        // unported satellite. The iteration is transcribed over the deferred-empty
        // successor link set so no successor is silently skipped once it lands.
        let succ_links: &[EdgeId] = &[];
        // ancDepth = indi->getIndividualAncestorDepth()
        let anc_depth = calc_alg_context
            .process_context()
            .node(*indi)
            .individual_ancestor_depth();
        for &succ_link in succ_links.iter() {
            // succIndi = getSuccessorIndividual(indi, succLink, ctx)
            let succ_indi = self.get_successor_individual(indi, succ_link, calc_alg_context);
            // succAncDepth = succIndi->getIndividualAncestorDepth()
            let succ_anc_depth = calc_alg_context
                .process_context()
                .node(succ_indi)
                .individual_ancestor_depth();
            if succ_anc_depth > anc_depth {
                if calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORREUSINGINDIVIDUALBLOCKED,
                    )
                {
                    if !calc_alg_context
                        .process_context()
                        .node(succ_indi)
                        .has_partial_processing_restriction_flags(
                            IndividualProcessNode::PRF_ANCESTORREUSINGINDIVIDUALBLOCKEDABOLISHED,
                        )
                    {
                        // locIndiNode = getLocalizedIndividual(succIndi, false, ctx)
                        let loc_indi_node =
                            self.get_localized_individual(succ_indi, false, calc_alg_context);
                        // locIndiNode->addProcessingRestrictionFlags(PRFANCESTORREUSINGINDIVIDUALBLOCKEDABOLISHED)
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(loc_indi_node)
                            .add_processing_restriction_flags(
                                IndividualProcessNode::PRF_ANCESTORREUSINGINDIVIDUALBLOCKEDABOLISHED,
                            );
                    }
                }
            }
        }
        let _ = recursive;
    }

    // =======================================================================
    // Task cancellation pair (cpp 6902-6949).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::cancellationRootTask`.
    /// cpp 6902-6932.
    ///
    /// The root-task unsatisfiability handler: bumps the root-backjump / root-unsat
    /// statistics, writes the root unsatisfiability caches, and cancels the root
    /// task. (The C++ debug dump of the closed completion graph + the per-branch-level
    /// closed-count summary are `#if`-disabled in the source and ported as comments.)
    pub fn cancellation_root_task(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // In-process stand-in for cancelling the root task: the drive loop (u02)
        // reads this flag as "the clash traced to branching level 0 ⇒ the whole
        // problem is unsatisfiable regardless of open disjunction alternatives".
        self.ddb_root_cancelled = true;
        // rootTask = (CSatisfiableCalculationTask*)calcAlgContext->getSatisfiableCalculationTask()->getRootTask()
        // W6-DEFER[api]: the satisfiable-calculation task + its root task are Task subsystem.
        let root_task: SatTaskId = Id::NONE;
        // STATINC(TASKROOTBACKJUMPINGCOUNT, calcAlgContext)
        // STATINC(ROOTTASKUNSATISFIABLECOUNT, calcAlgContext)
        // W3-DEFER[macro]: STATINC statistic counters route through the unported
        // CProcessingStatisticGathering.

        // rootUnsatisfiabilityWriteCaches(rootTask, calcAlgContext)
        self.root_unsatisfiability_write_caches(root_task, calc_alg_context);

        // Disabled-in-source debug dump (xDebug==false) of the clashed root graph and
        // the per-branch-level closed-count string — kept as a note, no behaviour.

        // return cancellationTask(rootTask, calcAlgContext)
        self.cancellation_task(root_task, calc_alg_context)
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::cancellationTask`.
    /// cpp 6935-6949.
    ///
    /// Installs an unsatisfiable (`false`) result on `task` if it has none yet, and —
    /// when dependency backjumping is on — bumps the backjump statistics (away-backjump
    /// when the task is not the one currently being processed) and notifies the
    /// scheduler of the task status change, returning `true`. Returns `false` if the
    /// result was already present or backjumping is off.
    pub fn cancellation_task(
        &mut self,
        task: SatTaskId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // if (!task->getSatisfiableCalculationTaskResult()->hasResult())
        // W6-DEFER[api]: CSatisfiableCalculationTaskResult is part of the Task subsystem;
        // `has_result` is held false so the install path is reached faithfully.
        let has_result = false;
        if !has_result {
            // task->getSatisfiableCalculationTaskResult()->installResult(false)
            // W6-DEFER[api]: install the unsatisfiable result on the task.
            if self.conf_dependency_backjumping {
                // STATINC(TASKBACKJUMPINGCOUNT, calcAlgContext)
                // W3-DEFER[macro]: backjumping statistic.
                // if (calcAlgContext->getUsedSatisfiableCalculationTask() != task) STATINC(TASKAWAYBACKJUMPINGCOUNT, ...)
                if calc_alg_context.base.used_sat_calc_task != task {
                    // STATINC(TASKAWAYBACKJUMPINGCOUNT, calcAlgContext)
                    // W3-DEFER[macro]: away-backjumping statistic.
                }
                // processorContext = calcAlgContext->getUsedTaskProcessorContext()
                // processorContext->getTaskProcessorCommunicator()->communicateTaskStatusUpdate(task)
                // W6-DEFER[api]: notify the scheduler of the cancelled task's status.
                return true;
            }
        }
        false
    }

    // =======================================================================
    // Debug node-status string (cpp 8039-8173).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::generateDebugIndiStatusString`.
    /// cpp 8039-8173.
    ///
    /// Renders the per-node processing-restriction flag set as a comma-joined status
    /// string (the human label per `PRF*` bit), plus the nominal marker and the
    /// "processing" marker when the node's concept-processing queue is non-empty. This
    /// is the one fully-resolvable method of the unit (it bottoms out on the ported
    /// node flag accessors); only the signature-blocking blocker id, the direct-blocked
    /// blocker concept tag, and the queue-empty test touch deferred satellites.
    pub fn generate_debug_indi_status_string(
        &self,
        indi: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> String {
        let mut status_string_list: Vec<String> = Vec::new();
        let node = calc_alg_context.process_context().node(indi);
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION,
        ) {
            status_string_list.push("invalid-blocker".to_string());
        }
        if node.has_partial_processing_restriction_flags(IndividualProcessNode::PRF_PURGEDBLOCKED) {
            status_string_list.push("pruned".to_string());
        }
        if node
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_PROCESSINGBLOCKED)
        {
            status_string_list.push("processing blocked".to_string());
        }
        if node
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_SATISFIABLECACHED)
        {
            status_string_list.push("satisfiable-cached".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED,
        ) {
            status_string_list.push("ancestor-satisfiable-cached".to_string());
        }
        if node.has_partial_processing_restriction_flags(IndividualProcessNode::PRF_DIRECTBLOCKED) {
            // blockerIndiID = indi->getBlockerIndividualNode()->getIndividualNodeID()
            let blocker_node = node.blocker_individual_node();
            let blocker_indi_id = if blocker_node != Id::NONE {
                calc_alg_context
                    .process_context()
                    .node(blocker_node)
                    .individual_node_id()
            } else {
                -1
            };
            // lastConTag = indi->mDebugBlockerLastConceptDes->getConceptTag()
            let last_con_des = node.debug_blocker_last_concept_des;
            let last_con_tag = if last_con_des != Id::NONE {
                let concept = calc_alg_context
                    .process_context()
                    .con_desc(last_con_des)
                    .get_concept();
                calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag()
            } else {
                0
            };
            status_string_list.push(format!(
                "direct-blocked by {} ({})",
                blocker_indi_id, last_con_tag
            ));
        }
        if node.has_partial_processing_restriction_flags(IndividualProcessNode::PRF_INDIRECTBLOCKED)
        {
            status_string_list.push("indirect-blocked".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS,
        ) {
            status_string_list.push("indirect-blocking-loss".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED,
        ) {
            status_string_list.push("blocking-retest-direct-modification".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED,
        ) {
            status_string_list.push("blocking-retest-blocker-modification".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED,
        ) {
            status_string_list.push("blocking-retest-ancestor-modification".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED,
        ) {
            // locSigBlockingData = indi->getSignatureBlockingIndividualNodeConceptExpansionData(false)
            // blockerIndiID = locSigBlockingData->getBlockerIndividualNode() ? …->getIndividualNodeID() : -1
            // W6-DEFER[api]: CSignatureBlockingIndividualNodeConceptExpansionData's
            // getBlockerIndividualNode is an unported satellite; the blocker id defaults
            // to -1 (the C++ initial value) until it lands.
            let blocker_indi_id: Cint64 = -1;
            status_string_list.push(format!("signature-blocking-cached by {}", blocker_indi_id));
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
        ) {
            status_string_list.push("ancestor-signature-blocking-cached".to_string());
        }
        if node
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_REUSINGINDIVIDUAL)
        {
            status_string_list.push("reusing-individual-blocked".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORREUSINGINDIVIDUALBLOCKED,
        ) {
            status_string_list.push("ancestor-reusing-individual-blocked".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHED,
        ) {
            status_string_list.push("saturation-cached-blocked".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED,
        ) {
            status_string_list.push("ancestor-saturation-cached-blocked".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
        ) {
            status_string_list.push("completion-graph-cached-blocked".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALID,
        ) {
            status_string_list.push("completion-graph-caching-invalid".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHEDNODELOCATED,
        ) {
            status_string_list.push("completion-graph-caching-node-located".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHEDNODEEXTENDED,
        ) {
            status_string_list.push("completion-graph-caching-node-extended".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED,
        ) {
            status_string_list.push("completion-graph-caching-invalidated".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_RETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED,
        ) {
            status_string_list
                .push("completion-graph-caching-retest-due-to-modification".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SUCCESSORNOMINALCONNECTION,
        ) {
            status_string_list.push("successor-nominal-connection".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SUCCESSORNEWNOMINALCONNECTION,
        ) {
            status_string_list.push("successor-new-nominal-connection".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_CONCRETEDATAINDINODE,
        ) {
            status_string_list.push("data-node".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND,
        ) {
            status_string_list.push("backend-synchronization".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED,
        ) {
            status_string_list.push(
                "backend-synchronized-nominal-indirect-connections-expansion-blocked".to_string(),
            );
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED,
        ) {
            status_string_list.push("backend-synchronized-neighbour-expansion-blocked".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION,
        ) {
            status_string_list.push("backend-synchronized-neighbour-partial-expansion".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDFULLEXPANSION,
        ) {
            status_string_list.push("backend-synchronized-neighbour-full-expansion".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED,
        ) {
            status_string_list.push("backend-synchronized-successor-expansion-blocked".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_INCREMENTALEXPANDING,
        ) {
            status_string_list.push("incremental-expansion".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_INCREMENTALEXPANSIONRETESTDUEDIRECTMODIFIED,
        ) {
            status_string_list.push(
                "incremental-expansion-compatibility-checking-due-to-modification".to_string(),
            );
        }
        if node
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_REUSINGINDIVIDUAL)
        {
            status_string_list.push("backend-expansion-reusing-individual".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BACKENDEXPANSIONREUSINGINDIVIDUAL,
        ) {
            status_string_list.push("backend-expansion-reusing-individual".to_string());
        }
        if node.has_partial_processing_restriction_flags(
            IndividualProcessNode::PRF_BACKENDEXPANSIONREUSEDISCARDED,
        ) {
            status_string_list.push("backend-expansion-reuse-discarded".to_string());
        }
        if node.is_nominal_individual_node() {
            status_string_list.push("nominal".to_string());
        }

        // conProQue = indi->getConceptProcessingQueue(false)
        // if (conProQue && !conProQue->isEmpty() && !indi->hasPartialProcessingRestrictionFlags(PRFINVALIDATEBLOCKERFLAGSCOMPINATION))
        //   statusStringList.append("processing")
        // W6-DEFER[api]: the concept-processing queue's `isEmpty` is an unported queue
        // satellite. The queue handle is read non-mutating; the empty test is deferred,
        // so the "processing" marker is held off until the queue accessor lands.
        let con_pro_que = node.concept_processing_queue;
        if con_pro_que != Id::NONE {
            // !conProQue->isEmpty() && !indi->has...(PRFINVALIDATEBLOCKERFLAGSCOMPINATION)
            let con_pro_que_non_empty = false; // W6-DEFER[api]: !isEmpty()
            if con_pro_que_non_empty
                && !node.has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_INVALIDATEBLOCKERFLAGSCOMPINATION,
                )
            {
                status_string_list.push("processing".to_string());
            }
        }

        // statusString = statusStringList.join(", ")
        status_string_list.join(", ")
    }

    // =======================================================================
    // Extended concept-set debug string list (cpp 8301-8362).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::generateExtendedDebugConceptSetStringList`.
    /// cpp 8301-8362.
    ///
    /// Renders a node's reapply concept-label set as a string list: per concept
    /// descriptor (skipping the TOP tag `1`) it formats the concept, appends any
    /// propagation-binding ids and variable-binding-path bindings keyed by the
    /// per-concept hashes, and the descriptor's dependency string.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the label-set iterator, the
    /// `CConceptPropagationBindingSetHash`/`CConceptVariableBindingPathSetHash`
    /// lookups, the variable-binding-path descriptor chain, and `CConceptTextFormater`
    /// are all unported; the per-descriptor render is transcribed structurally over
    /// the deferred-empty iterator.
    pub fn generate_extended_debug_concept_set_string_list(
        &mut self,
        con_set: LabelSetId,
        prop_bind_set_hash: ConceptPropBindingSetHashId,
        var_bind_path_set_hash: ConceptVarBindPathSetHashId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Vec<String> {
        let mut con_set_string_list: Vec<String> = Vec::new();
        // conSetIt = conSet->getConceptLabelSetIterator(false, false, false)
        // W6-DEFER[api]: CReapplyConceptLabelSetIterator is an unported label-set
        // satellite; the per-descriptor loop is transcribed over the deferred-empty set.
        let con_set_descriptors: &[ConDescId] = &[];
        for &con_des in con_set_descriptors.iter() {
            // concept = conDes->getConcept(); conTag = conDes->getConceptTag()
            let concept = calc_alg_context
                .process_context()
                .con_desc(con_des)
                .get_concept();
            let con_tag = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_concept_tag();
            if con_tag != 1 {
                // conceptString = conDes ? CConceptTextFormater::getConceptString(conDes->getConcept(), conDes->isNegated()) : "null"
                // W6-DEFER[api]: CConceptTextFormater renders the concept term; the
                // negation flag is the ported `is_negated()`.
                let negated = calc_alg_context
                    .process_context()
                    .con_desc(con_des)
                    .is_negated();
                let mut concept_string = String::from("null");
                let _ = negated;

                // propBindSet = propBindSetHash->getPropagationBindingSet(concept, false)
                // if (propBindSet) { … " ~{<ids>}" }
                if prop_bind_set_hash != Id::NONE {
                    // W6-DEFER[api]: CPropagationBindingSet / CPropagationBindingMap walk —
                    // appends "<id>, …" of the binding ids as " ~{…}".
                    let prop_bind_set: Cint64 = INVALID;
                    if prop_bind_set != INVALID {
                        let binding_string = String::new();
                        concept_string += &format!(" ~{{{}}}", binding_string);
                    }
                }
                // varBindPathSet = varBindPathSetHash->getVariableBindingPathSet(concept, false)
                // if (varBindPathSet) { … " ~{<{pathID:v-…/i-…}>}" }
                if var_bind_path_set_hash != Id::NONE {
                    // W6-DEFER[api]: CVariableBindingPathSet / Map / Descriptor / Path /
                    // Binding chain — formats each path's variable/individual bindings.
                    let var_bind_path_set: Cint64 = INVALID;
                    if var_bind_path_set != INVALID {
                        let binding_string = String::new();
                        concept_string += &format!(" ~{{{}}}", binding_string);
                    }
                }
                // depTrackPoint = conDes->getDependencyTrackPoint()
                let dep_track_point = calc_alg_context
                    .process_context()
                    .con_desc(con_des)
                    .get_dependency_track_point();
                if dep_track_point != Id::NONE {
                    // conceptString += generateDebugDependencyString(depTrackPoint, ctx)
                    concept_string +=
                        &self.generate_debug_dependency_string(dep_track_point, calc_alg_context);
                }
                con_set_string_list.push(concept_string);
            }
        }
        con_set_string_list
    }

    // =======================================================================
    // Extended completion-graph model dump → file + cache (cpp 8368-8393).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::writeGeneratedExtendedDebugIndiModelStringList`.
    /// cpp 8368-8393.
    ///
    /// Generates the extended per-node model string list, writes it (one node per
    /// block, `<br>`→CRLF) to `filename`, and — when the list is under 5000 entries —
    /// caches it joined into `mDebugIndiModelString` (with the trailing clash summary
    /// appended). Returns the cached string.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `QFile` byte output is deferred; the string assembly
    /// and the cache fields are ported.
    pub fn write_generated_extended_debug_indi_model_string_list(
        &mut self,
        filename: &str,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        let mut indi_string_list: Vec<String> = Vec::new();
        // remainingDebugString = generateExtendedDebugIndiModelStringList(ctx, &indiStringList)
        let remaining_debug_string = self.generate_extended_debug_indi_model_string_list(
            calc_alg_context,
            Some(&mut indi_string_list),
        );

        // QFile file(filename); if (file.open(WriteOnly)) { … }
        // W6-DEFER[api]: byte output of each block (with "<br>"→"\r\n") then the
        // remaining string to `filename`. Transcribed as the deferred file write.
        let _ = filename;

        if indi_string_list.len() < 5000 {
            // mDebugIndiModelStringList = indiStringList
            self.debug_indi_model_string_list = indi_string_list.clone();
            // mDebugIndiModelString = mDebugIndiModelStringList.join("<br><p><br>\r\n")
            self.debug_indi_model_string =
                self.debug_indi_model_string_list.join("<br><p><br>\r\n");
            // mDebugIndiModelString += remainingDebugString
            self.debug_indi_model_string += &remaining_debug_string;
        }

        self.debug_indi_model_string.clone()
    }

    /// Port of the propagation-cut individual id collection inside
    /// `generateExtendedDebugIndiModelStringList`.
    pub(crate) fn collect_backend_neighbour_expansion_cut_individual_ids(
        &self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> std::collections::HashSet<Cint64> {
        let mut prop_cut_indi_nodes_ids = std::collections::HashSet::new();
        let exp_cont_data = calc_alg_context.backend_neighbour_expansion_controlling_data(false);
        if exp_cont_data.is_some() {
            for &prop_cut_indi_node in calc_alg_context
                .process_context()
                .backend_neighbour_expansion_controlling_data(exp_cont_data)
                .get_cut_backend_neighbour_expansion_individual_linker()
            {
                if prop_cut_indi_node.is_some() {
                    let indi_id = calc_alg_context
                        .process_context()
                        .node(prop_cut_indi_node)
                        .individual_node_id();
                    prop_cut_indi_nodes_ids.insert(indi_id);
                }
            }
        }
        prop_cut_indi_nodes_ids
    }

    // =======================================================================
    // Extended completion-graph model string list (cpp 8396-8625).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::generateExtendedDebugIndiModelStringList`.
    /// cpp 8396-8625.
    ///
    /// The full extended completion-graph dump: walks the individual-process-node
    /// vector, and for every available up-to-date node emits its ancestor/id/nominal
    /// header, status string (plus a backend-expansion-cut marker), nominal depth,
    /// its rendered concept set (via `generate_extended_debug_concept_set_string_list`),
    /// dependent-nominals / incremental-expansion strings, asserted data literals, and
    /// backend-sync association summary. A second pass folds merged-into nodes into
    /// their target's line and a `-> target` suffix; a third pass inserts the successor
    /// edge lines. Finally, when there is a clash, it appends the tracked-clash summary.
    /// When `list` is `Some`, the filtered list is returned through it and the cache is
    /// cleared; otherwise the cache fields are filled.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the node vector bounds, `getAvailableUpToDateIndividual`,
    /// the nominal/IRI formatters, the asserted-data-literal + backend-sync satellites,
    /// the successor iterators, the tracked-clash machinery, and `QFile` are all
    /// unported; the multi-pass structure is transcribed faithfully over the
    /// deferred-empty node range.
    pub fn generate_extended_debug_indi_model_string_list(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        list: Option<&mut Vec<String>>,
    ) -> String {
        // procDataBox = calcAlgContext->getUsedProcessingDataBox()
        // indiVec = procDataBox->getIndividualProcessNodeVector()
        let _indi_vec = calc_alg_context
            .processing_data_box()
            .individual_process_node_vector();
        // indiStart = indiVec->getItemMinIndex(); indiCount = indiVec->getItemCount()
        // W6-DEFER[api]: CIndividualProcessNodeVector bounds are unported; both default
        // to 0 so the (empty) deferred range is walked faithfully.
        let mut indi_start: Cint64 = 0;
        let indi_count: Cint64 = 0;
        let mut indi_string_list: Vec<String> = Vec::new();
        if indi_start > 0 {
            indi_start = 0;
        }

        // propCutIndiNodesIds from the backend-neighbour-expansion controlling
        // data's cut individual linker.
        let prop_cut_indi_nodes_ids =
            self.collect_backend_neighbour_expansion_cut_individual_ids(calc_alg_context);

        let indi_replace_offset: Cint64 = -indi_start;
        // Pass 1: render each available node.
        let mut i = indi_start;
        while i < indi_count {
            // indi = getAvailableUpToDateIndividual(i, ctx)
            let mut indi = self.get_available_up_to_date_individual(i, calc_alg_context);
            if indi != Id::NONE {
                // ancIndi = getAncestorIndividual(indi, ctx)
                let anc_indi = self.get_ancestor_individual(&mut indi, calc_alg_context);
                // conSet = indi->getReapplyConceptLabelSet(false)
                // propBindSetHash = indi->getConceptPropagationBindingSetHash(false)
                // varBindPathSetHash = indi->getConceptVariableBindingPathSetHash(false)
                let con_set: LabelSetId = calc_alg_context
                    .process_context()
                    .node(indi)
                    .reapply_con_label_set;
                let prop_bind_set_hash: ConceptPropBindingSetHashId = calc_alg_context
                    .process_context()
                    .node(indi)
                    .concept_prop_binding_set_hash;
                let var_bind_path_set_hash: ConceptVarBindPathSetHashId = calc_alg_context
                    .process_context()
                    .node(indi)
                    .concept_var_bind_path_set_hash;

                if con_set != Id::NONE {
                    // nominalString from indi->getNominalIndividual() IRI name (deferred).
                    let nominal_string = String::new(); // W6-DEFER[api]: CIRIName of nominal individual.
                    let anc_id_prefix = if anc_indi != Id::NONE {
                        format!(
                            "{}->",
                            calc_alg_context
                                .process_context()
                                .node(anc_indi)
                                .individual_node_id()
                        )
                    } else {
                        String::new()
                    };
                    let indi_id = calc_alg_context
                        .process_context()
                        .node(indi)
                        .individual_node_id();
                    let mut indi_string =
                        format!("[ {}{}{} ] = <br>", anc_id_prefix, indi_id, nominal_string);

                    // statusString = generateDebugIndiStatusString(indi, ctx)
                    let mut status_string =
                        self.generate_debug_indi_status_string(indi, calc_alg_context);
                    if prop_cut_indi_nodes_ids.contains(&i) {
                        status_string += ", backend-expansion-propagation-cutted";
                    }
                    // {{<status>}d<nominalLevelOrAncestorDepth>}
                    let depth = calc_alg_context
                        .process_context()
                        .node(indi)
                        .individual_nominal_level_or_ancestor_depth();
                    indi_string += &format!("{{{{{}}}d{}}}<br>", status_string, depth);

                    // conSetStringList = generateExtendedDebugConceptSetStringList(conSet, propBindSetHash, varBindPathSetHash, ctx)
                    let con_set_string_list = self.generate_extended_debug_concept_set_string_list(
                        con_set,
                        prop_bind_set_hash,
                        var_bind_path_set_hash,
                        calc_alg_context,
                    );

                    // depNomString = generateDebugDependentNominalsString(indi, ctx)
                    let dep_nom_string =
                        self.generate_debug_dependent_nominals_string(indi, calc_alg_context);
                    if !dep_nom_string.is_empty() {
                        indi_string +=
                            &format!("SuccessorDependentNominals: {}<br>\r\n", dep_nom_string);
                    }

                    // incExpString = generateDebugIncrementalExpansionString(indi, ctx)
                    let inc_exp_string =
                        self.generate_debug_incremental_expansion_string(indi, calc_alg_context);
                    if !inc_exp_string.is_empty() {
                        indi_string += &format!("{}<br>\r\n", inc_exp_string);
                    }

                    // conSetString = conSetStringList.join("<br>")
                    let con_set_string = con_set_string_list.join("<br>");
                    // $<sig>$<br>{<conSetString>}
                    // sig = conSet->getConceptSignatureValue()
                    // W6-DEFER[api]: getConceptSignatureValue is a label-set satellite.
                    let con_set_signature: Cint64 = 0;
                    indi_string += &format!("${}$<br>{{{}}} ", con_set_signature, con_set_string);

                    // Asserted data literals (indi->getAssertedDataLiteralLinker() chain).
                    // W6-DEFER[api]: CProcessAssertedDataLiteralLinker / CDataLiteral render
                    // (lexical value + optional datatype IRI) is an unported satellite chain.
                    let ass_data_lit_string = String::new();
                    if !ass_data_lit_string.is_empty() {
                        indi_string += &format!("<br>\n{}<br>\n", ass_data_lit_string);
                    }

                    // Backend-sync association summary (indi->getIndividualBackendCacheSynchronisationData(false)).
                    // W6-DEFER[api]: CIndividualNodeRepresentativeMemoryBackendCacheSynchronisationData
                    // + its association/queue/merging-flag accessors are unported; the
                    // "(based on backend data update id …)" line is deferred.

                    indi_string_list.push(indi_string);
                } else {
                    // concept set missing branch.
                    let nominal_string = String::new(); // W6-DEFER[api]: CIRIName of nominal individual.
                    let anc_id_prefix = if anc_indi != Id::NONE {
                        format!(
                            "{}->",
                            calc_alg_context
                                .process_context()
                                .node(anc_indi)
                                .individual_node_id()
                        )
                    } else {
                        String::new()
                    };
                    let indi_id = calc_alg_context
                        .process_context()
                        .node(indi)
                        .individual_node_id();
                    let indi_string = format!(
                        "[ {}{}{} ] = concept set missing<br>",
                        anc_id_prefix, indi_id, nominal_string
                    );
                    indi_string_list.push(indi_string);
                }
            } else {
                // unused slot → empty placeholder (kept for index alignment).
                indi_string_list.push(String::new());
            }
            i += 1;
        }

        // Pass 2a: append "+i" to the merged-into target's line.
        let mut i = indi_start;
        while i < indi_count {
            let indi = self.get_available_up_to_date_individual(i, calc_alg_context);
            if indi != Id::NONE
                && calc_alg_context
                    .process_context()
                    .node(indi)
                    .has_merged_into_individual_node_id()
            {
                let merged_into_id = calc_alg_context
                    .process_context()
                    .node(indi)
                    .merged_into_individual_node_id();
                let idx = indi_replace_offset + merged_into_id;
                if idx >= 0 && (idx as usize) < indi_string_list.len() {
                    let mut me_indi_string = indi_string_list[idx as usize].clone();
                    me_indi_string += &format!("+{}", i);
                    indi_string_list[idx as usize] = me_indi_string;
                } else {
                    // LOG(ERROR, …): merging cannot be resolved for printing — deferred log.
                }
            }
            i += 1;
        }

        // Pass 2b: append " -> target" to the merged node's own line.
        let mut i = indi_start;
        while i < indi_count {
            let indi = self.get_available_up_to_date_individual(i, calc_alg_context);
            if indi != Id::NONE
                && calc_alg_context
                    .process_context()
                    .node(indi)
                    .has_merged_into_individual_node_id()
            {
                let merged_into_id = calc_alg_context
                    .process_context()
                    .node(indi)
                    .merged_into_individual_node_id();
                let idx = indi_replace_offset + i;
                if idx >= 0 && (idx as usize) < indi_string_list.len() {
                    let mut indi_string = indi_string_list[idx as usize].clone();
                    indi_string += &format!(" -> {}", merged_into_id);
                    indi_string_list[idx as usize] = indi_string;
                } else {
                    // LOG(ERROR, …): deferred log.
                }
            }
            i += 1;
        }

        // Pass 3: insert the successor edge lines after each node.
        let mut succ_insertions: Cint64 = 0;
        let mut i = indi_start;
        while i < indi_count {
            let indi = self.get_available_up_to_date_individual(i, calc_alg_context);
            if indi != Id::NONE {
                // succIt = indi->getSuccessorIterator(); per successor → "\t--> <id>: <roles + deps>"
                // W6-DEFER[api]: CSuccessorIterator / CSuccessorRoleIterator + the link
                // role / dependency render are unported satellites; the per-successor
                // insert is transcribed over the deferred-empty successor set.
                let succ_indi_ids: &[Cint64] = &[];
                for &_succ_indi in succ_indi_ids.iter() {
                    let succ_string = String::new(); // built from the deferred role/dep render.
                    let pos = indi_replace_offset + i + 1 + succ_insertions;
                    succ_insertions += 1;
                    let pos = pos.clamp(0, indi_string_list.len() as Cint64);
                    indi_string_list.insert(pos as usize, succ_string);
                }
            }
            i += 1;
        }

        // filteredIndiStringList: drop the empty placeholders.
        let filtered_indi_string_list: Vec<String> = indi_string_list
            .into_iter()
            .filter(|s| !s.is_empty())
            .collect();

        if let Some(list_ref) = list {
            // mDebugIndiModelString.clear(); *list = filteredIndiStringList
            self.debug_indi_model_string.clear();
            *list_ref = filtered_indi_string_list;
        } else {
            if filtered_indi_string_list.len() >= 1_000_000 {
                // QFile dump to ./Debugging/CompletionTasks/tmp-<taskDepth>.txt
                // W6-DEFER[api]: oversized-list file dump (task-depth-named).
            } else {
                self.debug_indi_model_string_list = filtered_indi_string_list;
                self.debug_indi_model_string =
                    self.debug_indi_model_string_list.join("<br><p><br>\r\n");
            }
        }

        // Trailing clash summary, when the databox has a clashed descriptor linker.
        if calc_alg_context
            .processing_data_box()
            .has_clashed_descriptor_linker()
        {
            // trackedClashDescriptors = createTrackedClashesDescriptors(getClashedDescriptorLinker(), ctx)
            let clashed_descriptor_linker = calc_alg_context
                .processing_data_box()
                .clashed_descriptor_linker();
            let tracked_clash_descriptors = self.create_tracked_clashes_descriptors(
                clashed_descriptor_linker,
                calc_alg_context,
                INVALID,
                false,
            );

            // clashedSet / trackingLine over the tracked-clash machinery.
            // W6-DEFER[api]: integrate Unit 30 CTrackedClashedDescriptorHasher +
            // CTrackedClashedDependencyLine with the cache-writing flow.
            // clashedString = generateDebugTrackedClashedDescriptorSummaryString(trackedClashDescriptors, ctx)
            let mut clashed_string = self.generate_debug_tracked_clashed_descriptor_summary_string(
                tracked_clash_descriptors,
                calc_alg_context,
            );
            // if (initializeTrackingLine(&trackingLine, trackedClashDescriptors, ctx)) {
            //   clashedString += "\r\n\r\n" + writeDebugTrackingLineStringToFile(
            //     generateDebugTrackingLineString(&trackingLine, ctx), "clash-details", &trackingLine, ctx);
            // }
            // W6-DEFER[api]: tracking-line init + render + file write.
            let _ = &mut clashed_string;

            self.debug_indi_model_string = format!(
                "{}<br><p><br>\r\n<br><p><br>\r\nClashes<br><p><br>\r\n{}",
                self.debug_indi_model_string, clashed_string
            );
        }

        self.debug_indi_model_string.clone()
    }

    // =======================================================================
    // Compact completion-graph model string list (cpp 8629-8718).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::generateDebugIndiModelStringList`.
    /// cpp 8629-8718.
    ///
    /// The compact sibling of the extended dump: per available node it emits
    /// `[ anc->id, nominal ] = {conTag list}` (concept tags, `-` for negated, IRI name
    /// appended), folds merged-into nodes into their target (`+i` / ` -> target`), and
    /// inserts the successor role lines, joining with `\n`. Caches into
    /// `mDebugIndiModelStringList` / `mDebugIndiModelString` and returns the latter.
    ///
    /// KONCLUDE-PORT-NOTE[api]: same deferral surface as the extended variant (node
    /// vector bounds, `getAvailableUpToDateIndividual`, the label-set iterator, IRI
    /// formatters, successor iterators); transcribed over the deferred-empty range.
    pub fn generate_debug_indi_model_string_list(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // procDataBox / indiVec bounds (deferred 0).
        let _indi_vec = calc_alg_context
            .processing_data_box()
            .individual_process_node_vector();
        let indi_count: Cint64 = 0; // W6-DEFER[api]: indiVec->getItemCount()
        let mut indi_start: Cint64 = 0; // W6-DEFER[api]: indiVec->getItemMinIndex()
        let mut indi_string_list: Vec<String> = Vec::new();
        if indi_start > 0 {
            indi_start = 0;
        }
        let indi_replace_offset: Cint64 = -indi_start;

        // Pass 1: render each available node compactly.
        let mut i = indi_start;
        while i < indi_count {
            let mut indi = self.get_available_up_to_date_individual(i, calc_alg_context);
            if indi != Id::NONE {
                let anc_indi = self.get_ancestor_individual(&mut indi, calc_alg_context);
                let con_set: LabelSetId = calc_alg_context
                    .process_context()
                    .node(indi)
                    .reapply_con_label_set;
                if con_set != Id::NONE {
                    let nominal_string = String::new(); // W6-DEFER[api]: CIRIName of nominal individual.
                    let anc_id_prefix = if anc_indi != Id::NONE {
                        format!(
                            "{}->",
                            calc_alg_context
                                .process_context()
                                .node(anc_indi)
                                .individual_node_id()
                        )
                    } else {
                        String::new()
                    };
                    let indi_id = calc_alg_context
                        .process_context()
                        .node(indi)
                        .individual_node_id();
                    let mut indi_string =
                        format!("[ {}{}{} ] = ", anc_id_prefix, indi_id, nominal_string);

                    // conSetString from the label-set iterator: per descriptor with tag != 1,
                    // "<neg?->><conTag><classNameIRI>".
                    // W6-DEFER[api]: CReapplyConceptLabelSetIterator + CIRIName::getRecentIRIName
                    // of the concept's class name are unported; transcribed over the
                    // deferred-empty descriptor set.
                    let con_set_descriptors: &[ConDescId] = &[];
                    let mut con_set_string = String::new();
                    for &con_des in con_set_descriptors.iter() {
                        let concept = calc_alg_context
                            .process_context()
                            .con_desc(con_des)
                            .get_concept();
                        let con_tag = calc_alg_context
                            .ontology_arenas()
                            .concept(concept)
                            .get_concept_tag();
                        if con_tag != 1 {
                            let negated = calc_alg_context
                                .process_context()
                                .con_desc(con_des)
                                .is_negated();
                            let mut con_string =
                                format!("{}{}", if negated { "-" } else { "" }, con_tag);
                            // if (concept->hasClassName()) conString += CIRIName::getRecentIRIName(...)
                            let _ = calc_alg_context
                                .ontology_arenas()
                                .concept(concept)
                                .has_class_name();
                            // W6-DEFER[api]: class-name IRI append.
                            if !con_set_string.is_empty() {
                                con_set_string += ", ";
                            }
                            con_set_string += &con_string;
                        }
                    }
                    indi_string += &format!("{{{}}} ", con_set_string);
                    indi_string_list.push(indi_string);
                }
            }
            i += 1;
        }

        // Pass 2a: fold "+i" into the merged-into target.
        let mut i = indi_start;
        while i < indi_count {
            let indi = self.get_available_up_to_date_individual(i, calc_alg_context);
            if indi != Id::NONE
                && calc_alg_context
                    .process_context()
                    .node(indi)
                    .has_merged_into_individual_node_id()
            {
                let merged_into_id = calc_alg_context
                    .process_context()
                    .node(indi)
                    .merged_into_individual_node_id();
                // meIndiString = indiStringList.value(mergedIntoID)
                let read_idx = merged_into_id;
                if read_idx >= 0 && (read_idx as usize) < indi_string_list.len() {
                    let mut me_indi_string = indi_string_list[read_idx as usize].clone();
                    me_indi_string += &format!("+{}", i);
                    // indiStringList.replace(indiReplaceOffset + mergedIntoID + indiStart, meIndiString)
                    let write_idx = indi_replace_offset + merged_into_id + indi_start;
                    if write_idx >= 0 && (write_idx as usize) < indi_string_list.len() {
                        indi_string_list[write_idx as usize] = me_indi_string;
                    }
                }
            }
            i += 1;
        }

        // Pass 2b: append " -> target" to the merged node's line.
        let mut i = indi_start;
        while i < indi_count {
            let indi = self.get_available_up_to_date_individual(i, calc_alg_context);
            if indi != Id::NONE
                && calc_alg_context
                    .process_context()
                    .node(indi)
                    .has_merged_into_individual_node_id()
            {
                let merged_into_id = calc_alg_context
                    .process_context()
                    .node(indi)
                    .merged_into_individual_node_id();
                // indiString = indiStringList.value(i)
                if i >= 0 && (i as usize) < indi_string_list.len() {
                    let mut indi_string = indi_string_list[i as usize].clone();
                    indi_string += &format!(" -> {}", merged_into_id);
                    let write_idx = indi_replace_offset + i + indi_start;
                    if write_idx >= 0 && (write_idx as usize) < indi_string_list.len() {
                        indi_string_list[write_idx as usize] = indi_string;
                    }
                }
            }
            i += 1;
        }

        // Pass 3: insert successor role lines.
        let mut succ_insertions: Cint64 = 0;
        let mut i = indi_start;
        while i < indi_count {
            let indi = self.get_available_up_to_date_individual(i, calc_alg_context);
            if indi != Id::NONE {
                // W6-DEFER[api]: CSuccessorIterator / CSuccessorRoleIterator render
                // ("\t--> <id>: <roleTag><propertyIRI>, …").
                let succ_indi_ids: &[Cint64] = &[];
                for &_succ_indi in succ_indi_ids.iter() {
                    let succ_string = String::new();
                    let pos = indi_replace_offset + i + indi_start + 1 + succ_insertions;
                    succ_insertions += 1;
                    let pos = pos.clamp(0, indi_string_list.len() as Cint64);
                    indi_string_list.insert(pos as usize, succ_string);
                }
            }
            i += 1;
        }

        self.debug_indi_model_string_list = indi_string_list;
        self.debug_indi_model_string = self.debug_indi_model_string_list.join("\n");
        self.debug_indi_model_string.clone()
    }
}
