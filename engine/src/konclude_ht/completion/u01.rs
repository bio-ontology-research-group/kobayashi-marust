//! `completion::u01` — port unit #1 (family: **Core processing loop / driver**).
//!
//! Ports the two driver methods of
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`:
//!
//! - `createCalculationAlgorithmContext` (cpp 848-854) — the per-task context factory.
//! - `handleTask`                        (cpp 858-1657) — the master satisfiable-task
//!   processing loop (take-individual → initialize → rule-process → conclude, plus
//!   incremental merge, possible-instance merging, the result/caching epilogue, and
//!   the clash/stop/error/cancel exception handling).
//!
//! Both are inherent methods of `CompletionTaskHandleAlgorithm`; the rule-application
//! and helper methods they call (`takeNextProcessIndividual`, `individualNodeInitializing`,
//! `tableauRuleProcessing`, `addIndividualToProcessingQueue`, …) are sibling units
//! u02..u36 and are called here as `self.<snake>(…)` — they resolve once those units
//! land and the module is reconciled (see PORT.md wave plan).
//!
//! KONCLUDE-PORT-NOTE[exceptions]: Konclude drives clash / stop / error / cancel
//! control flow with C++ exceptions thrown deep inside the called rule methods and
//! caught in `handleTask`'s `try { … } catch (…) { … }`. Rust has no exceptions, so
//! the `try` body is ported as an immediately-invoked closure returning
//! `Result<(), HandleTaskException>`; the explicit `throw`s in `handleTask` itself
//! become `return Err(…)`, and the `catch` clauses become the `match` arms. Deep
//! throws from sibling rule methods will be threaded as the same `Result` when those
//! units are ported (their signatures gain the error channel); until then the
//! deferred stub calls cannot throw, so the clash/error catch arms are kept for
//! fidelity but are unreachable in the stub era.
//!
//! KONCLUDE-PORT-NOTE[api]: `CTaskProcessorContext`, `CTask`, `CTaskProcessorCommunicator`,
//! the satisfiable-task adapters, the backend/occurrence cache handlers and the
//! by-value message analysers are not-yet-ported subsystems (zero-size markers or
//! opaque `Cint64`). Every interaction with them is marked `// W3-DEFER[api]: <call>`
//! and replaced by a sensible default (`false` / `0` / `Id::NONE`) so the surrounding
//! control flow is preserved exactly without fabricating their behaviour.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(unused_assignments)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::process::{ClashDescId, ConProcDescId, NodeId, TrackPointId};
use super::clash::CalcSignal;
use super::context::CalculationAlgorithmContextBase;
use super::stubs::SatisfiableCalculationTask;

/// KONCLUDE-PORT-NOTE[api]: `CCalculationErrorProcessingException::ECCANCELED` is an
/// enum value in a not-yet-ported exception header. Placeholder constant (`1`,
/// distinct from the `0` "no error" sentinel); the real value lands with the
/// exception types. Used only to recognise the cancellation error code.
const EC_CANCELED: Cint64 = 1;

/// KONCLUDE-PORT-NOTE[exceptions]: the catch-clause taxonomy of `handleTask`'s
/// `try` block, modelled as the `Err` variant of the ported closure result.
#[derive(Debug)]
enum HandleTaskException {
    /// `catch (const CClashedConceptDescriptor*& clashConLinker)`.
    ClashedConcept,
    /// `catch (const CCalculationClashProcessingException& e)` — carries the
    /// clashed-dependency descriptor for `clashedBacktracking`.
    ClashProcessing(ClashDescId),
    /// `catch (const CCalculationStopProcessingException& e)` —
    /// `isTaskCompletedProcessed()` → `completed`.
    StopProcessing { completed: bool },
    /// `catch (const CCalculationErrorProcessingException& e)`.
    ErrorProcessing { has_error: bool, code: Cint64 },
    /// `catch (const CMemoryAllocationException&)`.
    MemoryAllocation,
    /// `catch (...)`.
    Other,
}

/// Bridge a deep clash/stop signal into the `handleTask` catch taxonomy.
///
/// KONCLUDE-PORT-NOTE[exceptions]: this is the CONSUME half of the C++
/// `throw CCalculation{Clash,Stop}ProcessingException` raised DEEP inside a called
/// `apply*Rule` (see `completion/clash.rs`). In the port the rule body plants the
/// throw on the per-task context (`raise_clash`/`raise_stop`) and returns; the
/// `handleTask` closure drains it after the rule call with `take_pending_signal`
/// and converts the resulting [`CalcSignal`] into the closure's `Err`, exactly the
/// `HandleTaskException` the existing catch arms already route
/// (`ClashProcessing → clashedBacktracking`, `StopProcessing → completion`). This is
/// the `into_handle_task_exception` adapter `clash.rs` left for this wave (kept here
/// because `HandleTaskException` is `u01`-private).
fn drained_signal_to_handle_task_exception(sig: CalcSignal) -> HandleTaskException {
    match sig {
        // throw CCalculationClashProcessingException(clashDepDes)
        CalcSignal::Clash(clash_dep_des) => HandleTaskException::ClashProcessing(clash_dep_des),
        // throw CCalculationStopProcessingException(taskCompleted)
        CalcSignal::Stop { task_completed } => HandleTaskException::StopProcessing {
            completed: task_completed,
        },
        // `take_pending_signal` only yields `Some(..)` for a pending throw, so the
        // `Continue` (no-throw) state is unreachable here.
        CalcSignal::Continue => HandleTaskException::Other,
    }
}

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createCalculationAlgorithmContext`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ pool-allocates a `CCalculationAlgorithmContextBase`
    /// and returns the raw pointer. The port returns the context BY VALUE (per
    /// `manifest/00-type-dag.md` §4 the per-thread context owns the databox), so the
    /// caller (`handleTask`) holds the single owner. The two `init*` calls populate it.
    pub fn create_calculation_algorithm_context(
        &mut self,
        processor_context: Cint64,
        process_context: Cint64,
        sat_calc_task: Id<SatisfiableCalculationTask>,
    ) -> CalculationAlgorithmContextBase {
        // CCalculationAlgorithmContextBase* calcAlgContext = CObjectAllocator<...>::allocateAndConstruct(...);
        let mut calc_alg_context = CalculationAlgorithmContextBase::new();
        // W3-DEFER[api]: calcAlgContext->initTaskProcessContext(processContext, satCalcTask);
        // W3-DEFER[api]: calcAlgContext->initCalculationAlgorithmContext(processorContext,
        //   mConceptPriorityStrategy, mIndividualPriorityStrategy, mTaskProcessingStrategy,
        //   mUnsatCachRetStrategy, mIndiNodeManager, mClashDesFactory, mDependencyFactory,
        //   mUnsatCacheHandler, mSatExpCacheHandler, mSatNodeExpCacheHandler);
        // (The init logic is a context-layer method body, ported with `context.rs`.)
        calc_alg_context
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::handleTask`.
    ///
    /// The master loop: per satisfiable task, repeatedly take the next process
    /// individual, initialize it, drain its concept-processing queue through the
    /// tableau rule dispatch, conclude it; then run the satisfiability epilogue
    /// (incremental merge, possible-instance merging, caching, message analysis).
    /// Clash / stop / error / cancel are handled via the `[exceptions]` closure.
    pub fn handle_task(&mut self, processor_context: Cint64, task: Cint64) -> bool {
        // CTaskHandleMemoryAllocationManager* processorMemoryManager = processorContext->getTaskHandleMemoryAllocationManager();
        // W3-DEFER[api]: processorContext->getTaskHandleMemoryAllocationManager()
        let processor_memory_manager: Cint64 = INVALID;
        // CTaskProcessorCommunicator* processorCommunicator = processorContext->getTaskProcessorCommunicator();
        // W3-DEFER[api]: processorContext->getTaskProcessorCommunicator()
        let processor_communicator: Cint64 = INVALID;

        // CTaskHandleMemoryAllocationManager* taskHandleMemMan = processorContext->getTaskHandleMemoryAllocationManager();
        // taskHandleMemMan->releaseAllMemory();
        // W3-DEFER[api]: taskHandleMemMan->releaseAllMemory()

        // CSatisfiableCalculationTask* satCalcTask = dynamic_cast<CSatisfiableCalculationTask*>(task);
        // W3-DEFER[api]: dynamic_cast<CSatisfiableCalculationTask*>(task)
        let sat_calc_task: Id<SatisfiableCalculationTask> = Id::NONE;

        if sat_calc_task.is_some() {
            // if (!processorCommunicator->verifyContinueTaskProcessing(satCalcTask)) { ... }
            // W3-DEFER[api]: processorCommunicator->verifyContinueTaskProcessing(satCalcTask)
            let verify_continue_task_processing = true;
            if !verify_continue_task_processing {
                // W3-DEFER[api]: satCalcTask->getTaskStatus()->isProcessable()
                let is_processable = true;
                if !is_processable {
                    // W3-DEFER[api]: processorCommunicator->communicateTaskComplete(satCalcTask)
                    return false;
                } else {
                    // continue later
                    return true;
                }
            }

            // readCalculationConfig(satCalcTask);
            self.read_calculation_config(sat_calc_task);

            self.last_unsat_cache_tested_indi_node = Id::NONE;
            self.last_analysing_branch_node_tree = Id::NONE;

            // CProcessContext* processContext = satCalcTask->getProcessContext(processorContext);
            // W3-DEFER[api]: satCalcTask->getProcessContext(processorContext)
            let process_context: Cint64 = INVALID;

            // CCalculationAlgorithmContextBase* calcAlgContext = createCalculationAlgorithmContext(...);
            let mut calc_alg_context =
                self.create_calculation_algorithm_context(processor_context, process_context, sat_calc_task);
            // mCalcAlgContext = calcAlgContext;  (opaque back-handle, [ownership])
            // W3-DEFER[api]: mProcessingDataBox = satCalcTask->getProcessingDataBox();

            let mut clashed = false;
            let mut satisfiable = false;
            let mut completed = false;
            let mut paused = false;
            let mut error = false;
            let mut canceled = false;
            let mut error_code: Cint64 = 0;

            // CProcessTagger* processTagger = calcAlgContext->getUsedProcessTagger();
            // CProcessingDataBox* processingDataBox = calcAlgContext->getUsedProcessingDataBox();
            // CNodeSwitchHistory* nodeSwitchHistory = processingDataBox->getNodeSwitchHistory(true);
            // W3-DEFER[api]: getUsedProcessTagger / getUsedProcessingDataBox / getNodeSwitchHistory
            // (processTagger + nodeSwitchHistory are reached through deferred accessors.)

            // Reset all cached processing-queue handles (cpp 905-927).
            self.processing_queue = Id::NONE;
            self.depth_first_processing_queue = Id::NONE;
            self.sig_block_rev_set = Id::NONE;
            self.reusing_review_data = Id::NONE;
            self.indi_immediate_pro_queue = Id::NONE;
            self.indi_det_exp_pro_queue = Id::NONE;
            self.indi_det_dept_first_exp_pro_queue = Id::NONE;
            self.value_space_triggering_pro_queue = Id::NONE;
            self.value_space_sat_checking_queue = Id::NONE;
            self.nominal_processing_queue = Id::NONE;
            self.depth_processing_queue = Id::NONE;
            self.early_indi_react_processing_queue = Id::NONE;
            self.late_indi_react_processing_queue = Id::NONE;
            self.indi_block_react_pro_queue = Id::NONE;
            self.indi_sig_block_upd_pro_queue = Id::NONE;
            self.delayed_nominal_processing_queue = Id::NONE;
            self.var_bind_con_batch_processing_queue = Id::NONE;
            self.role_assertion_processing_queue = Id::NONE;
            self.incremental_expansion_initializing_processing_queue = Id::NONE;
            self.incremental_expansion_processing_queue = Id::NONE;
            self.incremental_compatibility_checking_queue = Id::NONE;
            self.min_concept_processing_priority_level = 0.0;
            self.indi_node_conclude_unsat_caching = false;

            // mOccStatsCacheHandler->configureOntology(processingDataBox->getOntology());
            // W3-DEFER[api]: mOccStatsCacheHandler->configureOntology(...)

            // CSatisfiableTaskRepresentativeBackendUpdatingAdapter* repCacheUpdAd =
            //     satCalcTask->getSatisfiableRepresentativeBackendCacheUpdatingAdapter();
            // W3-DEFER[api]: satCalcTask->getSatisfiableRepresentativeBackendCacheUpdatingAdapter()
            let rep_cache_upd_ad: bool = false; // adapter present? (Id::NONE-equivalent)

            // --- the C++ try { … } block, ported as an immediately-invoked closure ---
            let try_result: Result<(), HandleTaskException> = (|| {
                // KONCLUDE-PORT-NOTE[exceptions]: the per-frame unwind check. After every
                // sibling rule/processing call below (the frames the C++ throw unwinds
                // THROUGH), drain a deep clash/stop the call may have raised on the
                // context and re-raise it as the closure `Err` the catch handles — the
                // cooperative-early-return port of the C++ stack-unwind (see clash.rs).
                macro_rules! drain_pending {
                    () => {
                        if let Some(sig) = calc_alg_context.take_pending_signal() {
                            return Err(drained_signal_to_handle_task_exception(sig));
                        }
                    };
                }

                // mBackendCacheHandler->setWorkingOntology(satCalcTask->getProcessingDataBox()->getOntology());
                // W3-DEFER[api]: mBackendCacheHandler->setWorkingOntology(...)

                // repCacheUpdAd && !processingDataBox->hasBackendCacheUpdateIndividualsInitialized()
                // W3-DEFER[api]: processingDataBox->hasBackendCacheUpdateIndividualsInitialized()
                let has_backend_cache_update_individuals_initialized = false;
                if rep_cache_upd_ad && !has_backend_cache_update_individuals_initialized {
                    // The full per-individual backend-cache-update seeding loop (cpp 948-1003):
                    // builds/localizes nominal individual nodes for each entry of the adapter's
                    // computation list and queues them for immediate processing.
                    // W3-DEFER[api]: repCacheUpdAd->getIndividualComputationList() and the whole
                    //   per-individual association-data / node-construction / queue-insertion loop
                    //   (getIndividualAssociationData, indiNodeVec->getLocalData/setLocalData,
                    //    indiNodeQueue->insertIndiviudalProcessNode, setConstructedIndividualNode).
                    // W3-DEFER[api]: processingDataBox->setBackendCacheUpdateIndividualsInitialized(true)
                }

                // if (processingDataBox->getBranchingInstruction()) { ... }
                // W3-DEFER[api]: processingDataBox->getBranchingInstruction()
                let has_branching_instruction = false;
                if has_branching_instruction {
                    // W3-DEFER[api]: branchingInstruction->getBranchingInstructionType()
                    let is_add_individual_concepts_type = false;
                    if is_add_individual_concepts_type {
                        // CIndividualProcessNode* newLocIndiNode =
                        //     getLocalizedIndividual(addConceptBrIn->getAddingIndividualNode(), false, calcAlgContext);
                        // W3-DEFER[api]: addConceptBrIn->getAddingIndividualNode()
                        let adding_individual_node: NodeId = Id::NONE;
                        let mut new_loc_indi_node: NodeId =
                            self.get_localized_individual(adding_individual_node, false, &mut calc_alg_context);
                        // CConceptProcessingQueue* newConProcQueue = newLocIndiNode->getConceptProcessingQueue(true);
                        // W3-DEFER[api]: newLocIndiNode->getConceptProcessingQueue(true)
                        // CDependencyTrackPoint* newDependencyTrackPoint = addConceptBrIn->getAddingDependencyTrackPoint();
                        // W3-DEFER[api]: addConceptBrIn->getAddingDependencyTrackPoint()
                        let new_dependency_track_point: TrackPointId = Id::NONE;

                        // for (addingConceptLinker = addConceptBrIn->getAddingConceptLinker(); ...; ++)
                        //   addConceptToIndividual(linker->getData(), linker->isNegated(),
                        //     newLocIndiNode, newDependencyTrackPoint, false, true, calcAlgContext);
                        // W3-DEFER[api]: addConceptBrIn->getAddingConceptLinker() iteration
                        //   (each element → self.add_concept_to_individual(concept, negated,
                        //    new_loc_indi_node, new_dependency_track_point, false, true, &mut ctx))

                        // if (calcAlgContext->getUsedUnsatisfiableCacheRetrievalStrategy()
                        //       ->testUnsatisfiableCacheForBranchedDisjuncts(nullptr, newLocIndiNode, nullptr))
                        //   addIndividualNodeForCacheUnsatisfiableRetrieval(newLocIndiNode, calcAlgContext);
                        // W3-DEFER[api]: testUnsatisfiableCacheForBranchedDisjuncts(...)
                        let test_unsat_cache_for_branched_disjuncts = false;
                        if test_unsat_cache_for_branched_disjuncts {
                            self.add_individual_node_for_cache_unsatisfiable_retrieval(
                                &mut new_loc_indi_node,
                                &mut calc_alg_context,
                            );
                        }
                        // addIndividualToProcessingQueue(newLocIndiNode, calcAlgContext);
                        self.add_individual_to_processing_queue(new_loc_indi_node, &mut calc_alg_context);
                        drain_pending!();
                    }
                    // processingDataBox->clearBranchingInstruction();
                    // W3-DEFER[api]: processingDataBox->clearBranchingInstruction()
                }

                // if (satCalcTask->getSatisfiableTaskIncrementalConsistencyTestingAdapter()) { ... }
                // The incremental-consistency adapter (`task::adapters`) is real and
                // resolvable from the threaded context; the presence test goes live.
                let has_incremental_consistency_testing_adapter = calc_alg_context
                    .satisfiable_task_incremental_consistency_testing_adapter(sat_calc_task)
                    .is_some();
                if has_incremental_consistency_testing_adapter {
                    // W3-DEFER[api]: processingDataBox->isIncrementalExpansionInitialised()
                    let is_incremental_expansion_initialised = false;
                    if !is_incremental_expansion_initialised {
                        // The incremental-compatibility-checking seeding loop (cpp 1033-1042):
                        // localizes each immediately-processing individual node, marks it directly
                        // changed + incremental-expanding, and queues it for compatibility checking.
                        // W3-DEFER[api]: getIncrementalCompatibilityCheckingQueue / getIndividualImmediatelyProcessingQueue
                        //   / getProcessIndividualNodeLinker iteration / getLocalizedIndividual /
                        //   getIncrementalExpansionData(true)->setDirectlyChanged(true) /
                        //   addProcessingRestrictionFlags / setIncrementalExpansionID /
                        //   mIncrementalCompatibilityCheckingQueue->insertProcessIndiviudal
                        // W3-DEFER[api]: processingDataBox->setIncrementalExpansionInitialised(true)
                    }
                }

                // if (processingDataBox->isReapplicationLastConceptDesciptorOnLastIndividualNodeRequired()) { ... }
                // W3-DEFER[api]: processingDataBox->isReapplicationLastConceptDesciptorOnLastIndividualNodeRequired()
                let is_reapplication_last_concept_descriptor_required = false;
                if is_reapplication_last_concept_descriptor_required {
                    let mut last_processing_indi_node: NodeId = Id::NONE;
                    let mut last_processing_con_des: ConProcDescId = Id::NONE;
                    // W3-DEFER[api]: processingDataBox->getLastProcessingIndividualNodeAndConceptDescriptor(out, out)
                    let got_last_processing = false;
                    if got_last_processing {
                        self.add_copied_concept_to_processing_queue(
                            last_processing_con_des,
                            &mut last_processing_indi_node,
                            &mut calc_alg_context,
                        );
                        drain_pending!();
                    }
                    // W3-DEFER[api]: processingDataBox->setReapplicationLastConceptDesciptorOnLastIndividualNodeRequired(false)
                }

                if self.conf_possible_instance_individuals_merging {
                    // CSatisfiableTaskRealizationPossibleInstancesMergingAdapter* possibleInstancesMergingAdapter =
                    //     satCalcTask->getSatisfiablePossibleInstancesMergingAdapter();
                    // W3-DEFER[api]: satCalcTask->getSatisfiablePossibleInstancesMergingAdapter()
                    let has_possible_instances_merging_adapter = false;
                    if has_possible_instances_merging_adapter {
                        // W3-DEFER[api]: possibleInstancesMergingAdapter->getIndividualTestingMergingLinker()
                        //   && indiTestingMergingLinker->isSatisfiableMerged()
                        let testing_merging_linker_satisfiable_merged = false;
                        if testing_merging_linker_satisfiable_merged {
                            canceled = true;
                            satisfiable = true;
                        }
                    }
                }

                // CIndividualProcessNode* indiProcNode = nullptr;
                // if (!canceled) indiProcNode = takeNextProcessIndividual(calcAlgContext);
                let mut indi_proc_node: NodeId = Id::NONE;
                if !canceled {
                    indi_proc_node = self.take_next_process_individual(&mut calc_alg_context);
                    drain_pending!();
                }
                let mut con_proc_des: ConProcDescId = Id::NONE;

                self.current_rec_proc_depth = 0;
                self.process_rule_to_task_processing_verification_count = 80;
                self.remain_process_rule_to_task_processing_verification =
                    self.process_rule_to_task_processing_verification_count;

                // KONCLUCE_TASK_ALGORITHM_MODEL_STRING_INSTRUCTION(mBeginTaskDebugIndiModelString = ...) — debug, deferred.

                let mut last_indi_proc_node: NodeId = Id::NONE;
                // STATINC(TASKPROCESSCHANGECOUNT, mCalcAlgContext); — stats macro, deferred.

                // CSatisfiableTaskCancellationAdapter* cancellationAdapter = satCalcTask->getCancellationAdapter();
                // if (cancellationAdapter && cancellationAdapter->canCancelTaskCalculation()) { canceled=true; throw ECCANCELED; }
                // W3-DEFER[api]: satCalcTask->getCancellationAdapter() / canCancelTaskCalculation()
                let can_cancel_task_calculation = false;
                if can_cancel_task_calculation {
                    canceled = true;
                    return Err(HandleTaskException::ErrorProcessing {
                        has_error: true,
                        code: EC_CANCELED,
                    });
                }

                // if (repCacheUpdAd && repCacheUpdAd->hasUnsatisfiableComputed()) { canceled=true; throw ECCANCELED; }
                // W3-DEFER[api]: repCacheUpdAd->hasUnsatisfiableComputed()
                let rep_cache_has_unsatisfiable_computed = false;
                if rep_cache_upd_ad && rep_cache_has_unsatisfiable_computed {
                    canceled = true;
                    return Err(HandleTaskException::ErrorProcessing {
                        has_error: true,
                        code: EC_CANCELED,
                    });
                }

                // CSatisfiableTaskRepresentativeBackendUpdatingAdapter* repBackCacheUpAdapter = ...;
                // if (repBackCacheUpAdapter) mBackendCacheHandler->checkRecomputationIdUsage(...);
                // W3-DEFER[api]: mBackendCacheHandler->checkRecomputationIdUsage(repBackCacheUpAdapter->...)

                // --- the main individual-processing loop (cpp 1112-1236) ---
                while indi_proc_node.is_some() && !canceled {
                    last_indi_proc_node = indi_proc_node;
                    con_proc_des = Id::NONE;

                    // The C++ `if (true)` guard (the signature-cache TODO is commented out).
                    if true {
                        // processTagger->incNodeSwitchTag();
                        // nodeSwitchHistory->addIndividualProcessNodeSwitch(indiProcNode, processTagger->getCurrentNodeSwitchTag());
                        // W3-DEFER[api]: processTagger->incNodeSwitchTag / nodeSwitchHistory->addIndividualProcessNodeSwitch
                        // mCalcAlgContext->setMinModificationIndividual(indiProcNode);
                        // W3-DEFER[api]: calcAlgContext->setMinModificationIndividual(indiProcNode)
                        // STATINC(INDIVIDUALNODESWITCHCOUNT, mCalcAlgContext); — deferred.

                        // initialize individual
                        let initialized_individual =
                            self.individual_node_initializing(indi_proc_node, &mut calc_alg_context);
                        drain_pending!();
                        if initialized_individual {
                            // (indiStartProcessingDebug block is debug-only, deferred.)

                            let mut continue_processing_individual =
                                self.continue_individual_processing(indi_proc_node, &mut calc_alg_context);
                            drain_pending!();

                            while continue_processing_individual && !canceled {
                                // CConceptProcessingQueue* conProcQueue = indiProcNode->getConceptProcessingQueue(true);
                                // conProcDes = conProcQueue->takeNextConceptDescriptorProcess();
                                // W3-DEFER[api]: indiProcNode->getConceptProcessingQueue(true)->takeNextConceptDescriptorProcess()
                                con_proc_des = Id::NONE;

                                // processingDataBox->setLastProcessingIndividualNodeAndConceptDescriptor(indiProcNode, conProcDes);
                                // W3-DEFER[api]: processingDataBox->setLastProcessingIndividualNodeAndConceptDescriptor(...)

                                // process concept
                                self.current_rec_proc_depth = 0;
                                self.applied_total_rule_count += 1;
                                // STATINC(RULEAPPLICATIONCOUNT, mCalcAlgContext); — deferred.
                                // KONCLUCE debug-model-string instructions — deferred.

                                continue_processing_individual = self.tableau_rule_processing(
                                    indi_proc_node,
                                    con_proc_des,
                                    &mut calc_alg_context,
                                );
                                // The clash/stop the rule dispatch may raise unwinds HERE
                                // (the C++ throw from inside `tableauRuleProcessing`), before
                                // the conclude-vs-reinsert branch below runs.
                                drain_pending!();

                                if continue_processing_individual {
                                    continue_processing_individual = self
                                        .continue_individual_processing(indi_proc_node, &mut calc_alg_context);
                                    drain_pending!();
                                } else {
                                    // addConceptToProcessingQueue(conProcDes, conProcQueue, indiProcNode, calcAlgContext);
                                    // KONCLUDE-PORT-NOTE[overload]: this is the unit-4 4-arg reinsert
                                    // overload `addConceptToProcessingQueue(CConceptProcessDescriptor*,
                                    // CConceptProcessingQueue*&, CIndividualProcessNode*&, ctx)` (cpp 27278).
                                    // Rust can't overload; the placeholder name `*_reinsert` is reconciled
                                    // to whatever unit 4 names it. The `conProcQueue` arg is deferred
                                    // (W3-DEFER[api]: the queue the descriptor was taken from).
                                    self.add_concept_to_processing_queue_reinsert(
                                        con_proc_des,
                                        // W3-RECONCILE[api]: conProcQueue arg (the queue the descriptor came from) deferred.
                                        Id::NONE,
                                        indi_proc_node,
                                        &mut calc_alg_context,
                                    );
                                    drain_pending!();
                                }

                                self.remain_process_rule_to_task_processing_verification -= 1;
                                if self.remain_process_rule_to_task_processing_verification <= 0 {
                                    self.remain_process_rule_to_task_processing_verification =
                                        self.process_rule_to_task_processing_verification_count;

                                    // if (cancellationAdapter && cancellationAdapter->canCancelTaskCalculation()) throw ECCANCELED;
                                    // W3-DEFER[api]: cancellationAdapter->canCancelTaskCalculation()
                                    let can_cancel = false;
                                    if can_cancel {
                                        canceled = true;
                                        return Err(HandleTaskException::ErrorProcessing {
                                            has_error: true,
                                            code: EC_CANCELED,
                                        });
                                    }

                                    // if (repCacheUpdAd && repCacheUpdAd->hasUnsatisfiableComputed()) throw ECCANCELED;
                                    // W3-DEFER[api]: repCacheUpdAd->hasUnsatisfiableComputed()
                                    let rep_unsat = false;
                                    if rep_cache_upd_ad && rep_unsat {
                                        canceled = true;
                                        return Err(HandleTaskException::ErrorProcessing {
                                            has_error: true,
                                            code: EC_CANCELED,
                                        });
                                    }

                                    // if (!processorCommunicator->verifyContinueTaskProcessing(satCalcTask)) { pause; throw StopProcessing(false); }
                                    // W3-DEFER[api]: processorCommunicator->verifyContinueTaskProcessing(satCalcTask)
                                    let verify_continue = true;
                                    if !verify_continue {
                                        // STATINC(TASKPROCESSPAUSECOUNT, mCalcAlgContext); — deferred.
                                        paused = true;
                                        calc_alg_context.base.set_current_individual_node(Id::NONE);
                                        self.add_individual_to_processing_queue(
                                            indi_proc_node,
                                            &mut calc_alg_context,
                                        );
                                        return Err(HandleTaskException::StopProcessing { completed: false });
                                    }
                                }
                            }

                            self.individual_node_conclusion(indi_proc_node, &mut calc_alg_context);
                            drain_pending!();
                        }

                        // if (mCalcAlgContext->isMinModificationUpdated()) nodeSwitchHistory->updateLastIndividualProcessNodeSwitch(...);
                        if calc_alg_context.base.is_min_modification_updated() {
                            // W3-DEFER[api]: nodeSwitchHistory->updateLastIndividualProcessNodeSwitch(
                            //   calcAlgContext->getMinModificationAncestorDepth(),
                            //   calcAlgContext->getMinModificationIndividualID())
                        }
                    }

                    indi_proc_node = Id::NONE;
                    if !canceled {
                        indi_proc_node = self.take_next_process_individual(&mut calc_alg_context);
                        drain_pending!();
                    }
                }

                // if (mOptIncrementalExpansion && !mProcessingDataBox->isIncrementalExpansionCachingMerged()) { ... }
                // W3-DEFER[api]: mProcessingDataBox->isIncrementalExpansionCachingMerged()
                let is_incremental_expansion_caching_merged = false;
                if self.opt_incremental_expansion && !is_incremental_expansion_caching_merged {
                    self.incremental_merge_with_previous_nondeterministic_completion_graph(
                        &mut calc_alg_context,
                    );
                    drain_pending!();
                    // W3-DEFER[api]: mProcessingDataBox->setIncrementalExpansionCachingMerged(true)
                }

                // KONCLUCE debug-model-string (mSatTaskDebugIndiModelString) — deferred.

                if self.conf_possible_instance_individuals_merging && !canceled {
                    // CSatisfiableTaskRealizationPossibleInstancesMergingAdapter* possibleInstancesMergingAdapter =
                    //     satCalcTask->getSatisfiablePossibleInstancesMergingAdapter();
                    // W3-DEFER[api]: satCalcTask->getSatisfiablePossibleInstancesMergingAdapter()
                    let has_possible_instances_merging_adapter = false;
                    if has_possible_instances_merging_adapter {
                        // (printMergingTask debug-write block deferred.)

                        // CPossibleInstancesIndividualsMergingData* possInstanceMergeingData =
                        //     possibleInstancesMergingAdapter->getPossibleInstanceMergingData();
                        // W3-DEFER[api]: possibleInstancesMergingAdapter->getPossibleInstanceMergingData()
                        let has_poss_instance_merging_data = false;
                        if has_poss_instance_merging_data {
                            // The streak/success bookkeeping over the last + current merged
                            // possible-instance linkers (cpp 1286-1303): for each not-yet-merged
                            // linker, bump the success counters and mark it satisfiable-merged.
                            // W3-DEFER[api]: processingDataBox->getLastMergedPossibleInstanceIndividualLinker()
                            //   / getCurrentMergedPossibleInstanceIndividualLinkersLinker() iteration /
                            //   isSatisfiableMerged / setSatisfiableMerged / possInstanceMergeingData->incMergingSuccess
                            //   (each success also does `++mStatPossibleInstanceMergingSuccessSubmitCount`).

                            // cint64 testingIndiId = possibleInstancesMergingAdapter->getTestingIndividualReference().getIndividualID();
                            // W3-DEFER[api]: possibleInstancesMergingAdapter->getTestingIndividualReference().getIndividualID()
                            let testing_indi_id: Cint64 = 0;

                            // if (!processingDataBox->isPossibleInstanceIndividualMergingStopped()) { ... } else { incMergingStreakFails(); }
                            // W3-DEFER[api]: processingDataBox->isPossibleInstanceIndividualMergingStopped()
                            let is_possible_instance_individual_merging_stopped = false;
                            if !is_possible_instance_individual_merging_stopped {
                                let testing_indi_node = self
                                    .get_corrected_nominal_individual_node(-testing_indi_id, &mut calc_alg_context);
                                // W3-DEFER[api]: possInstanceMergeingData passed to tryPossibleInstanceMerging
                                self.try_possible_instance_merging(
                                    testing_indi_node,
                                    INVALID,
                                    &mut calc_alg_context,
                                );
                                drain_pending!();
                            } else {
                                // W3-DEFER[api]: possInstanceMergeingData->incMergingStreakFails()
                            }
                        }
                    }
                }

                satisfiable = true;

                if self.conf_generate_queries {
                    // CCompletionGraphRandomWalkQueryGenerator queryGen;
                    // queryGen.generateQueries(calcAlgContext->getSatisfiableCalculationTask());
                    // W3-DEFER[api]: CCompletionGraphRandomWalkQueryGenerator::generateQueries(...)
                }

                Ok(())
            })();

            // --- the C++ catch clauses (cpp 1342-1371) ---
            match try_result {
                Ok(()) => {}
                Err(HandleTaskException::ClashedConcept) => {
                    clashed = true;
                    // KONCLUCE clashed debug-model-string — deferred.
                }
                Err(HandleTaskException::ClashProcessing(clash_con_linker)) => {
                    clashed = true;
                    // KONCLUCE clashed debug-model-string — deferred.
                    if self.conf_dependency_backtracking {
                        self.clashed_backtracking(clash_con_linker, &mut calc_alg_context);
                    }
                }
                Err(HandleTaskException::StopProcessing { completed: task_completed }) => {
                    if task_completed {
                        completed = true;
                    }
                }
                Err(HandleTaskException::ErrorProcessing { has_error, code }) => {
                    if has_error {
                        error = true;
                        error_code = code;
                        if error_code != EC_CANCELED {
                            // LOG(ERROR, ..., "Error occured, computation stopped.")
                        }
                    }
                }
                Err(HandleTaskException::MemoryAllocation) => {
                    error = true;
                    error_code = 2;
                }
                Err(HandleTaskException::Other) => {
                    error = true;
                    error_code = 3;
                }
            }

            // KONCLUCE end-task debug-model-string — deferred.

            // if (!error && repCacheUpdAd && repCacheUpdAd->hasUnsatisfiableComputed()) { error=true; completed=false; clashed=false; }
            // W3-DEFER[api]: repCacheUpdAd->hasUnsatisfiableComputed()
            let rep_cache_has_unsatisfiable_computed_post = false;
            if !error && rep_cache_upd_ad && rep_cache_has_unsatisfiable_computed_post {
                error = true;
                completed = false;
                clashed = false;
            }

            // The debugging-write-data block (cpp 1421-1486) selects a file name from the
            // task's adapters and dumps the model; entirely debug/IO, deferred.
            // W3-DEFER[api]: the mDebug/mConfDebuggingWriteData* adapter-driven debug dump.

            if completed {
                self.stat_stopped_count += 1;
            }
            // CBooleanTaskResult* satResult = satCalcTask->getSatisfiableCalculationTaskResult();
            // W3-DEFER[api]: satCalcTask->getSatisfiableCalculationTaskResult()
            if clashed {
                self.stat_clash_count += 1;
                // if (!satResult->hasResult()) satResult->installResult(false);
                // W3-DEFER[api]: satResult->hasResult() / satResult->installResult(false)
                completed = true;
            }
            if satisfiable {
                self.stat_satisfiable_count += 1;
                // STATINC(ROOTTASKSATISFIABLECOUNT, calcAlgContext); — deferred.
                // satResult->installResult(true);
                // W3-DEFER[api]: satResult->installResult(true)

                // if (!canceled && (mSatTaskConsAnalyser.analyseSatisfiableTask(...) ||
                //     mSatTaskIncConsAnalyser.analyseSatisfiableTask(...))) rebuildSignatureBlockingCandidateHash(...);
                // W3-DEFER[api]: mSatTaskConsAnalyser.analyseSatisfiableTask / mSatTaskIncConsAnalyser.analyseSatisfiableTask
                let cons_analyser_triggered = false;
                if !canceled && cons_analyser_triggered {
                    self.rebuild_signature_blocking_candidate_hash(&mut calc_alg_context);
                }

                // if (!canceled && (repBackUpd || (consAdapter && consAdapter->getConsitenceObserver())))
                //     mBackendCacheHandler->tryAssociateNodesWithBackendCache(...);
                // W3-DEFER[api]: satCalcTask->getSatisfiableRepresentativeBackendCacheUpdatingAdapter() /
                //   getConsistenceAdapter()->getConsitenceObserver()
                let backend_cache_association_required = false;
                if !canceled && backend_cache_association_required {
                    // W3-DEFER[api]: mBackendCacheHandler->tryAssociateNodesWithBackendCache(
                    //   processingDataBox->getLastBackendCacheIntegratedIndividualNodeLinker(),
                    //   satCalcTask->getSatisfiableRepresentativeBackendCacheUpdatingAdapter(), calcAlgContext)
                    // (The large commented-out prop-cut analysis block in the C++ is inert.)
                }

                if !canceled {
                    // The six by-value message analysers each read the calc config then analyse
                    // the satisfiable task; all are zero-size stubs until ported.
                    // W3-DEFER[api]: mClassMessAnalyser.readCalculationConfig / .analyseSatisfiableTask
                    // W3-DEFER[api]: mSatTaskPropClassAnalyser.readCalculationConfig / .analyseSatisfiableTask
                    // W3-DEFER[api]: mMarkerPropRealMessAnalyser.readCalculationConfig / .analyseSatisfiableTask
                    // W3-DEFER[api]: mPossAssCollAnalyser.readCalculationConfig / .analyseSatisfiableTask
                    // W3-DEFER[api]: mSatTaskCompAnswerAnalyser.readCalculationConfig / .analyseSatisfiableTask
                    // W3-DEFER[api]: mSatTaskPropBindingAnswerAnalyser.readCalculationConfig / .analyseSatisfiableTask
                    self.cache_satisfiable_individual_nodes(&mut calc_alg_context);
                }
                self.analyse_branching_statistics(&mut calc_alg_context);

                completed = true;
            }
            self.commit_cache_messages(&mut calc_alg_context);

            if error {
                // if (satCalcTask->hasActiveReferencedTask()) satCalcTask->clearUninitializedReferenceTasks();
                // W3-DEFER[api]: satCalcTask->hasActiveReferencedTask() / clearUninitializedReferenceTasks()
                // satCalcTask->getTaskStatus()->setError(error, errorCode);
                // W3-DEFER[api]: satCalcTask->getTaskStatus()->setError(error, errorCode)
                // processorCommunicator->communicateTaskError(satCalcTask);
                // W3-DEFER[api]: processorCommunicator->communicateTaskError(satCalcTask)
                return false;
            }

            if completed {
                // processorCommunicator->communicateTaskComplete(satCalcTask);
                // W3-DEFER[api]: processorCommunicator->communicateTaskComplete(satCalcTask)
                return false;
            }
            return true;
        }

        false
    }
}
