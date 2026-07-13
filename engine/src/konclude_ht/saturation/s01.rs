//! `saturation::s01` — SAT method-batch unit #1 (Driver + config + lifecycle).
//!
//! Faithful port of the FIRST saturation port unit (PU-SAT-1, groups A + B in
//! `manifest/03-saturation-calc.md`) of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`:
//!   - ctor jump-table + config defaults     `…::…SaturationTaskHandleAlgorithm` [43-172]
//!   - `readCalculationConfig`               [179-242]
//!   - `createCalculationAlgorithmContext`   [245-250]
//!   - `handleTask` (main saturation loop)   [254-514]
//!   - `hasRemainingExtensionProcessingNodes`            [689-698]
//!   - `hasRemainingMergingCriticalExtensionProcessingNodes` [702-713]
//!   - `continueNominalDelayedIndividualNodeProcessing`  [718-757]
//!   - `completeSaturatedIndividualNodes`    [760-785]
//!   - `hasRemainingProcessingNodes`         [788-793]
//!   - `setDelayedNominalProcessingOccured`  [6910-6912]
//!   - `setInsufficientNodeOccured`          [6915-6917]
//!   - `setProblematicEQCandidateOccured`    [6920-6922]
//!   - `addIndividualToProcessingQueue`      [7119-7125]
//!   - `addUninitializedIndividualToProcessingQueue` [7127-7131]
//!   - `addIndividualToCompletionQueue`      [7135-7141]
//! (The empty C++ `~CCalculationTableauApproximationSaturationTaskHandleAlgorithm`
//! dtor [175-176] maps to Rust `Drop`; no body needed.)
//!
//! CONTEXT CONVENTION — every saturation method takes the SHARED
//! `CCalculationAlgorithmContextBase* calcAlgContext`, so it is threaded as
//! `calc_alg_context: &mut super::super::completion::context::CalculationAlgorithmContextBase`.
//! Ids resolve via its accessors: saturation nodes
//! `calc_alg_context.process_context().sat_node(id)` / `_mut` / `_mut().alloc_sat_node`;
//! the per-test databox `calc_alg_context.processing_data_box_mut()`. Sibling
//! saturation methods are `self.x(...)`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ loop predicates take an explicit
//! `CProcessingDataBox* processingDataBox` param that is always
//! `calcAlgContext->getUsedProcessingDataBox()` (== the algorithm's
//! `mProcessingDataBox`). In the port the databox is OWNED BY the context, so the
//! redundant param is dropped and the databox is resolved from `calc_alg_context`.
//!
//! KONCLUDE-PORT-NOTE[api]: the `CIndividualSaturationProcessNodeLinker` queue
//! abstraction is COLLAPSED in the port — the databox queues hold `SatNodeId`
//! directly (`process/db5.rs`), so `linker->getData()` / `getProcessingIndividual()`
//! is the taken id itself, and the linker's `isProcessingQueued`/`setProcessingQueued`/
//! `clearProcessingQueued` flag (not yet ported) is a `// W2-DEFER[api]` stub.
//! The Task / Scheduler / processor-communicator / analyser / backend-cache
//! subsystems are not ported (`// W6-DEFER[api]`), exceptions become early returns
//! (`// W3-DEFER[exceptions]`), the rule member-fn-pointer jump tables are opaque
//! (`// W4-DEFER[pointer-alias]`), and `STATINC` is a stats macro no-op
//! (`// W3-DEFER[macro]`). Control flow and order of operations are preserved.

#![allow(
    unused_variables,
    unused_mut,
    unused_assignments,
    dead_code,
    clippy::collapsible_if,
    clippy::collapsible_else_if
)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::completion::stubs::{
    CalculationConfigurationExtension, SatisfiableCalculationTask,
};
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::ConceptId;
use super::super::process::SatNodeId;
use super::stubs::{
    SatisfiableTaskSaturationOccurrenceStatisticsCollector,
    SaturationNodeBackendAssociationCacheHandler,
};

impl super::algorithm::SaturationTaskHandleAlgorithm {
    /// Port of
    /// `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::CCalculationTableauApproximationSaturationTaskHandleAlgorithm`
    /// (the ctor, .cpp 43-172).
    ///
    /// KONCLUDE-PORT-NOTE[uninit]: `algorithm.rs::new()` already zero/empty-inits
    /// every field; this faithful ctor starts from it and then applies the two
    /// ctor-injected handles plus the specific (non-default) config-flag / size
    /// constants the C++ ctor assigns. The per-operator rule jump-table population
    /// is deferred (see the `[pointer-alias]` block below).
    pub fn new_with_handlers(
        backend_ass_cace_handler: Id<SaturationNodeBackendAssociationCacheHandler>,
        sat_task_occ_stat_collector: Id<SatisfiableTaskSaturationOccurrenceStatisticsCollector>,
    ) -> Self {
        // mProcessingDataBox = nullptr; mCalcAlgContext = nullptr; (already INVALID)
        let mut algo = Self::new();

        // mBackendAssCaceHandler = backendAssCaceHandler;
        algo.backend_ass_cace_handler = backend_ass_cace_handler;
        // mSatTaskOccStatCollector = satTaskOccStatCollector;
        algo.sat_task_occ_stat_collector = sat_task_occ_stat_collector;

        // mPosJumpFuncVec = &mPosTableauRuleJumpFuncVec[mRuleFuncCount/2];
        // mNegJumpFuncVec = &mNegTableauRuleJumpFuncVec[mRuleFuncCount/2];
        // for (i<mRuleFuncCount) { mPos/NegTableauRuleJumpFuncVec[i] = nullptr; }
        // W4-DEFER[pointer-alias]: `TableauRuleFunction` is a pointer-to-member of
        // the apply*Rule methods; the offset jump-func pointers and the per-operator
        // slot assignments (.cpp 53-108: CCDATATYPE→applyDATATYPERule,
        // CCBOTTOM→applyBOTTOMRule, CCATOM→applyNONERule, CCTOP/CCAND/CCAQAND/
        // CCIMPLAQAND/CCBRANCHAQAND/CCSUB/CCIMPLTRIG/CCBRANCHTRIG/CCEQ→applyANDRule,
        // CCALL/CCAQALL/CCIMPLALL/CCBRANCHALL/CCBRANCHAQALL/CCIMPLAQALL→applyALLRule,
        // CCSOME/CCAQSOME→applySOMERule, CCAQCHOOCE→applyAutomatChooseRule,
        // CCOR→applyORRule, CCIMPL/CCBRANCHIMPL→applyIMPLICATIONRule,
        // CCEQCAND→applyEQCANDRule, CCSELF→applySELFRule, CCATLEAST→applyATLEASTRule,
        // CCATMOST→applyATMOSTRule, CCVALUE→applyVALUERule, CCNOMINAL→applyNOMINALRule,
        // CCDATALITERAL→applyDATALITERALRule; plus the neg-vec entries
        // CCATMOST→applyATLEASTRule, CCATLEAST→applyATMOSTRule, CCOR/CCEQ→applyANDRule,
        // CCALL→applySOMERule, CCSOME→applyALLRule, CCAQCHOOCE→applyAutomatChooseRule,
        // CCAND→applyORRule, CCSUB/CCATOM→applyNONERule) become a dispatch table that
        // lands with the rule units (SAT u03/u04). The slots stay `INVALID` here
        // (already null from `new()`).

        // mLastConfig = nullptr; (already Id::NONE)
        // counters all 0; mDebugTestingSaturationTask = nullptr; (already from new())

        // --- the specific (non-default) config flags / sizes the ctor assigns ---
        algo.conf_implication_adding_skipping = true; // 139
        algo.conf_force_all_concept_insertion = false; // 140
        algo.conf_debugging_write_data = false; // 141
        algo.conf_debugging_write_data_saturation_tasks = false; // 142
        algo.conf_force_all_copy_instead_of_substituition = false; // 143

        algo.conf_add_critical_concepts_to_queues = false; // 145
        algo.conf_directly_critical_to_insufficient = true; // 146
        algo.conf_check_critical_concepts = false; // 147
        algo.conf_all_concepts_extension_processing = false; // 148
        algo.conf_functional_concepts_extension_processing = false; // 149
        algo.conf_concepts_extension_processing = false; // 150

        algo.conf_resolve_operand_concept_size = 100; // 152
        algo.conf_referred_node_many_concept_count = 500; // 153
        algo.conf_many_concept_referred_node_count_process_limit = 2; // 154
        algo.conf_referred_node_concept_count_process_limit = 1500; // 155
        algo.conf_referred_node_unprocessed_count_process_limit = 1; // 156
        algo.conf_referred_node_checking_depth = 5; // 157
        algo.conf_occurrence_statistics_collection = 1; // 158 (true)

        algo.conf_copy_node_from_top_individual_for_many_concepts = true; // 160
        algo.conf_force_many_concept_saturation = 0; // 161 (false)
        algo.wrote_functional_succ_pred_merging_debug_string = false; // 162

        algo.conf_detailed_merging_test_for_atmost_critical_testing = true; // 164
        algo.conf_simple_merging_test_for_atmost_critical_testing = true; // 165

        algo.conf_delayed_merging_critical_atmost_concepts = true; // 167
        algo.conf_delayed_merging_critical_atmost_concepts_cardinality_size = 100; // 168

        // mSuccessorConnectedNominalUpdatedCount / mMaximumCardinalityCandidatesUpdatedCount
        // = 0; (already from new())
        algo
    }

    /// Port of `readCalculationConfig` (.cpp 179-242).
    pub fn read_calculation_config(&mut self, sat_calc_task: Id<SatisfiableCalculationTask>) {
        // CCalculationConfigurationExtension* config = satCalcTask->getCalculationConfiguration();
        // W6-DEFER[api]: the Task subsystem (CSatisfiableCalculationTask) is not
        // ported; the configuration pointer is unavailable here.
        let config: Id<CalculationConfigurationExtension> = Id::NONE;
        if config != self.last_config {
            if config.is_some() {
                // W6-DEFER[api]: ontology / structure-summary reads
                //   CConcreteOntology* ontology = satCalcTask->getProcessingDataBox()->getOntology();
                //   COntologyStructureSummary* ontStructureSummary = ontology->getStructureSummary();
                self.conf_force_all_concept_insertion = false; // 185
                self.conf_force_all_copy_instead_of_substituition = false; // 186
                self.conf_implication_adding_skipping = true; // 187
                                                              // W6-DEFER[api]: config->isDebuggingWriteDataActivated() etc.
                self.conf_debugging_write_data = false; // 188 (config getter deferred)
                self.conf_debugging_write_data_saturation_tasks = false; // 189 (deferred)
                                                                         // if (!ontStructureSummary || !ontStructureSummary->hasOnlyELConceptClasses()
                                                                         //     || ontology->getABox()->getIndividualCount() > 0) { ... }
                                                                         // W6-DEFER[api]: structure-summary / ABox individual-count not ported;
                                                                         // reproduce the body (the common non-pure-EL path).
                {
                    self.conf_force_all_concept_insertion = true; // 191
                    self.conf_implication_adding_skipping = false; // 192
                }

                // W6-DEFER[api]: the following are config-getter driven; values deferred.
                self.conf_directly_critical_to_insufficient = true; // 195 isSaturationDirectCriticalToInsufficientActivated()
                self.conf_add_critical_concepts_to_queues = false; // 196 isSaturationCriticalConceptTestingActivated()
                self.conf_check_critical_concepts = false; // 197 isSaturationCriticalConceptTestingActivated()
                self.conf_concepts_extension_processing = false; // 198 isSaturationSuccessorExtensionActivated()
                self.conf_nominal_processing = false; // 199 isNominalSaturationActivated()

                self.conf_referred_node_many_concept_count = 500; // 201
                self.conf_many_concept_referred_node_count_process_limit = 2; // 202
                self.conf_referred_node_concept_count_process_limit = 1500; // 203
                self.conf_referred_node_unprocessed_count_process_limit = 1; // 204
                self.conf_referred_node_checking_depth = 5; // 205

                self.conf_occurrence_statistics_collection = 1; // 207 isOccurrenceStatisticsCollectionActivated()
            } else {
                self.conf_force_all_copy_instead_of_substituition = false; // 210
                self.conf_force_all_concept_insertion = true; // 211
                self.conf_implication_adding_skipping = true; // 212
                self.conf_nominal_processing = true; // 213
                self.conf_debugging_write_data = false; // 214
                self.conf_debugging_write_data_saturation_tasks = false; // 215

                self.conf_directly_critical_to_insufficient = true; // 217
                self.conf_add_critical_concepts_to_queues = false; // 218
                self.conf_check_critical_concepts = false; // 219
                self.conf_concepts_extension_processing = false; // 220

                self.conf_occurrence_statistics_collection = 1; // 222

                self.conf_referred_node_many_concept_count = 500; // 224
                self.conf_many_concept_referred_node_count_process_limit = 2; // 225
                self.conf_referred_node_concept_count_process_limit = 1500; // 226
                self.conf_referred_node_unprocessed_count_process_limit = 1; // 227
                self.conf_referred_node_checking_depth = 5; // 228
            }

            self.conf_all_concepts_extension_processing = self.conf_concepts_extension_processing; // 232
            self.conf_functional_concepts_extension_processing =
                self.conf_concepts_extension_processing; // 233

            self.last_config = config; // 235
                                       // W6-DEFER[api]: mBackendAssCaceHandler->readCalculationConfig(config);
                                       //                mBackendAssCaceHandler->setWorkingOntology(...);
        }

        //mConfForceAllConceptInsertion = true; (commented out in C++)
    }

    /// Port of `createCalculationAlgorithmContext` (.cpp 245-250).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ allocates a
    /// `CCalculationAlgorithmContextBase` from the process context's memory pool and
    /// runs `initTaskProcessContext` / `initCalculationAlgorithmContext`. In the port
    /// the context is OWNED by value (per `manifest/00-type-dag.md` §4: one context
    /// per worker thread); this returns a fresh owned context. The two `init*` calls
    /// (which wire `processorContext` / `processContext` / `satCalcTask` into the
    /// context's `mUsed*` cache) are `// W6-DEFER[api]` until the Task / Scheduler /
    /// ProcessContext-from-task plumbing is ported.
    pub fn create_calculation_algorithm_context(
        &mut self,
        processor_context: Cint64,
        process_context: Cint64,
        sat_calc_task: Id<SatisfiableCalculationTask>,
    ) -> CalculationAlgorithmContextBase {
        // CCalculationAlgorithmContextBase* calcAlgContext =
        //   CObjectAllocator<...>::allocateAndConstruct(processContext->getUsedMemoryAllocationManager());
        let calc_alg_context = CalculationAlgorithmContextBase::new();
        // W6-DEFER[api]: calcAlgContext->initTaskProcessContext(processContext, satCalcTask);
        // W6-DEFER[api]: calcAlgContext->initCalculationAlgorithmContext(processorContext);
        calc_alg_context
    }

    /// Port of `handleTask` (.cpp 254-514) — the main saturation loop driver.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `processorContext`/`task` belong to the unported
    /// Scheduler/Task subsystem (`// W6-DEFER[api]`, opaque `Cint64`). The
    /// `dynamic_cast<CSatisfiableCalculationTask*>` and every
    /// `processorCommunicator`/`taskHandleMemMan`/`CBooleanTaskResult`/analyser call
    /// is deferred; the full saturation loop body (the heart of the unit) is ported
    /// faithfully over the locally-owned `calc_alg_context`.
    pub fn handle_task(&mut self, processor_context: Cint64, task: Cint64) -> bool {
        // CTaskHandleMemoryAllocationManager* processorMemoryManager = processorContext->getTaskHandleMemoryAllocationManager();
        // CTaskProcessorCommunicator* processorCommunicator = processorContext->getTaskProcessorCommunicator();
        // CTaskHandleMemoryAllocationManager* taskHandleMemMan = processorContext->getTaskHandleMemoryAllocationManager();
        // taskHandleMemMan->releaseAllMemory();
        // W6-DEFER[api]: processor memory manager + communicator (Scheduler subsystem).

        // CSatisfiableCalculationTask* satCalcTask = dynamic_cast<CSatisfiableCalculationTask*>(task);
        // W6-DEFER[api]: the Task downcast is unavailable; the satisfiable-task path
        // is preserved structurally below.
        let sat_calc_task: Id<SatisfiableCalculationTask> = Id::NONE;
        if sat_calc_task.is_some() {
            // if (!processorCommunicator->verifyContinueTaskProcessing(satCalcTask)) {
            //     if (!satCalcTask->getTaskStatus()->isProcessable()) {
            //         processorCommunicator->communicateTaskComplete(satCalcTask); return false;
            //     } else { return true; /* continue later */ }
            // }
            // W6-DEFER[api]: task-processing verification (Scheduler subsystem).

            self.read_calculation_config(sat_calc_task); // 277

            self.insufficient_all_count = 0; // 280
            self.insufficient_atmost_count = 0; // 281
            self.insufficient_or_count = 0;
            self.insufficient_eqcand_count = 0;
            self.insufficient_value_count = 0;
            self.insufficient_nominal_count = 0;

            self.cached_completion_graph_loaded = false; // 284
            self.representative_data_loaded = false; // 285
            self.cached_completion_graph_missing = false; // 286
            self.det_cached_cg_indi_vector = Id::NONE; // 287
            self.non_det_cached_cg_indi_vector = Id::NONE; // 288
            self.non_det_consistency_cg = false; // 289
            self.det_consistency_cg = false; // 290

            // CProcessContext* processContext = satCalcTask->getProcessContext(processorContext);
            let process_context: Cint64 = INVALID; // W6-DEFER[api]
                                                   // CCalculationAlgorithmContextBase* calcAlgContext = createCalculationAlgorithmContext(...);
            let mut calc_alg_context = self.create_calculation_algorithm_context(
                processor_context,
                process_context,
                sat_calc_task,
            );
            // mCalcAlgContext = calcAlgContext; mProcessingDataBox = satCalcTask->getProcessingDataBox();
            // W4-DEFER[pointer-alias]: the self back-aliases of the by-value-owned
            // context/databox stay opaque; all resolution goes through calc_alg_context.
            self.calc_alg_context = INVALID;
            self.processing_data_box = INVALID;

            let mut clashed = false; // 297
            let mut satisfiable = false; // 298
            let mut completed = false; // 299
            let mut paused = false; // 300
            let mut error = false; // 301
            let mut error_code: Cint64 = 0; // 302

            // CProcessTagger* processTagger = calcAlgContext->getUsedProcessTagger();
            // CProcessingDataBox* processingDataBox = calcAlgContext->getUsedProcessingDataBox();
            // CNodeSwitchHistory* nodeSwitchHistory = processingDataBox->getNodeSwitchHistory(true);
            // W6-DEFER[api]: process tagger + node-switch history (not ported).

            let mut indi_processed_count: Cint64 = 0; // 310

            // CIndividualSaturationProcessNode* indiProcSatNode = nullptr; (loop-local below)
            // CConceptProcessDescriptor* conProcDes = nullptr;
            let process_rule_to_task_processing_verification_count: Cint64 = 10; // 315
            let mut remain_process_rule_to_task_processing_verification =
                process_rule_to_task_processing_verification_count; // 316
            let mut separated_saturation = false; // 317
            let mut has_first_processed_node_id = false; // 318
            let mut first_processed_node_id: Cint64 = 0; // 319

            let mut lastindi_proc_sat_node: SatNodeId = Id::NONE; // 321

            // W3-DEFER[exceptions]: the C++ wraps the loop in try { … } catch
            // (CCalculationErrorProcessingException / CMemoryAllocationException / …)
            // setting error/errorCode. Sibling-method throws are deferred, so the
            // body runs straight-line and error stays false.
            {
                // STATINC(TASKPROCESSCHANGECOUNT, calcAlgContext); — W3-DEFER[macro]

                self.continue_nominal_delayed_individual_node_processing(&mut calc_alg_context); // 326

                let mut wrote_extension_proc_debug_string = false; // 328

                while self.has_remaining_merging_critical_extension_processing_nodes(
                    &mut calc_alg_context,
                ) {
                    while self.has_remaining_extension_processing_nodes(&mut calc_alg_context) {
                        while self.has_remaining_processing_nodes(&mut calc_alg_context) {
                            while calc_alg_context
                                .processing_data_box()
                                .has_individual_saturation_process_node_linker()
                            {
                                // linker = take…(); indiProcSatNode = linker->getData();
                                let indi_proc_sat_node_linker = calc_alg_context
                                    .processing_data_box_mut()
                                    .take_individual_saturation_process_node_linker();
                                let mut indi_proc_sat_node = calc_alg_context
                                    .process_context()
                                    .indi_sat_process_node_linker(indi_proc_sat_node_linker)
                                    .get_processing_individual();
                                if calc_alg_context
                                    .process_context()
                                    .sat_node(indi_proc_sat_node)
                                    .is_separated()
                                {
                                    separated_saturation = true; // 340
                                }
                                let individual_id = calc_alg_context
                                    .process_context()
                                    .sat_node(indi_proc_sat_node)
                                    .get_individual_id();
                                if !has_first_processed_node_id
                                    || individual_id < first_processed_node_id
                                {
                                    has_first_processed_node_id = true; // 343
                                    first_processed_node_id = individual_id; // 344
                                }

                                lastindi_proc_sat_node = indi_proc_sat_node; // 347
                                                                             // STATINC(INDIVIDUALNODESWITCHCOUNT, calcAlgContext); — W3-DEFER[macro]
                                indi_processed_count += 1; // 349
                                                           // KONCLUCE_..._MODEL_STRING_INSTRUCTION(...) expands to nothing.
                                if self.individual_node_initializing(
                                    &mut indi_proc_sat_node,
                                    &mut calc_alg_context,
                                ) {
                                    let mut concept_saturation_process_linker = calc_alg_context
                                        .process_context_mut()
                                        .sat_node_take_concept_saturation_process_linker(
                                            indi_proc_sat_node,
                                        );
                                    while concept_saturation_process_linker.is_some() {
                                        // STATINC(RULEAPPLICATIONCOUNT, calcAlgContext); — W3-DEFER[macro]
                                        self.apply_tableau_saturation_rule(
                                            &mut indi_proc_sat_node,
                                            concept_saturation_process_linker,
                                            &mut calc_alg_context,
                                        );
                                        self.release_concept_saturation_process_linker(
                                            concept_saturation_process_linker,
                                            &mut calc_alg_context,
                                        );
                                        concept_saturation_process_linker = calc_alg_context
                                            .process_context_mut()
                                            .sat_node_take_concept_saturation_process_linker(
                                                indi_proc_sat_node,
                                            );
                                    }
                                }
                                calc_alg_context
                                    .process_context_mut()
                                    .indi_sat_process_node_linker_mut(indi_proc_sat_node_linker)
                                    .clear_processing_queued();
                                self.individual_node_conclusion(
                                    &mut indi_proc_sat_node,
                                    &mut calc_alg_context,
                                ); // 363
                            }

                            if calc_alg_context
                                .processing_data_box()
                                .has_individual_disjunct_common_concept_extract_process_linker()
                            {
                                let indi_disj_common_con_ext_process_linker = calc_alg_context
                                    .processing_data_box_mut()
                                    .take_individual_disjunct_common_concept_extract_process_linker(
                                    );
                                calc_alg_context
                                    .process_context_mut()
                                    .indi_sat_process_node_linker_mut(
                                        indi_disj_common_con_ext_process_linker,
                                    )
                                    .set_processing_queued(false);
                                let mut indi_proc_sat_node = calc_alg_context
                                    .process_context()
                                    .indi_sat_process_node_linker(
                                        indi_disj_common_con_ext_process_linker,
                                    )
                                    .get_processing_individual();
                                lastindi_proc_sat_node = indi_proc_sat_node; // 375
                                                                             // STATINC(INDIVIDUALNODESWITCHCOUNT, calcAlgContext); — W3-DEFER[macro]
                                indi_processed_count += 1; // 377
                                if self.individual_node_initializing(
                                    &mut indi_proc_sat_node,
                                    &mut calc_alg_context,
                                ) {
                                    self.update_extract_disjunct_common_concept(
                                        &mut indi_proc_sat_node,
                                        &mut calc_alg_context,
                                    ); // 379
                                }
                                self.individual_node_conclusion(
                                    &mut indi_proc_sat_node,
                                    &mut calc_alg_context,
                                ); // 381
                            }
                        }

                        self.process_next_successor_extensions(&mut calc_alg_context);
                        // 396
                    }

                    if self.conf_check_critical_concepts
                        && self.has_next_critical_concepts(&mut calc_alg_context)
                    {
                        while self.has_next_critical_concepts(&mut calc_alg_context) {
                            self.check_next_critical_concepts(&mut calc_alg_context);
                            // 414
                        }
                        self.check_critical_individuals(&mut calc_alg_context); // 416
                    }

                    if calc_alg_context
                        .processing_data_box()
                        .has_saturation_atmost_merging_process_linker()
                    {
                        self.try_atmost_concept_successor_merging(&mut calc_alg_context);
                        // 432
                    }
                }

                self.complete_saturated_individual_nodes(&mut calc_alg_context); // 438

                if self.conf_debugging_write_data && self.conf_debugging_write_data_saturation_tasks
                {
                    self.write_individual_saturation_statistics(&mut calc_alg_context);
                    // 443
                    // QString fileName(...); if (separatedSaturation) { ... }
                    // mEndSaturationDebugIndiModelString = writeGeneratedExtendedDebugIndiModelStringList(...);
                    // W6-DEFER[api]: debug-file writing (group O / DBG unit).
                }
                satisfiable = true; // 450

                //testRelevantConceptRoleRatio(calcAlgContext); (commented out)
            }

            // CBooleanTaskResult* satResult = satCalcTask->getSatisfiableCalculationTaskResult();
            // W6-DEFER[api]: the task result object (Task subsystem).
            if clashed {
                // if (!satResult->hasResult()) { satResult->installResult(false); }
                completed = true; // 474
            }
            if satisfiable {
                // STATINC(ROOTTASKSATISFIABLECOUNT, calcAlgContext); — W3-DEFER[macro]
                // mSatTaskSaturationIndiAnalyser.analyseSatisfiableTask(satCalcTask, mCalcAlgContext);
                // mSatTaskSaturationPreyAnalyser.analyseSatisfiableTask(satCalcTask, mCalcAlgContext);
                // W6-DEFER[api]: the by-value saturation analysers (not ported).
                self.try_associate_individual_nodes_with_backend_cache(
                    sat_calc_task,
                    &mut calc_alg_context,
                ); // 485
                   // satResult->installResult(true);
                completed = true; // 490
            }

            if completed {
                // if (mConfOccurrenceStatisticsCollection && satCalcTask->getOccurrenceStatisticsCollectingAdapter()
                //     || satCalcTask->getSaturationIndividualsAnalysationObserver()) {
                //     mSatTaskOccStatCollector->analyseSatisfiableTask(satCalcTask, calcAlgContext);
                // }
                // W6-DEFER[api]: occurrence-statistics collector (not ported).
            }

            if error {
                // satCalcTask->getTaskStatus()->setError(error, errorCode);
                // processorCommunicator->communicateTaskError(satCalcTask);
                return false; // 502
            }

            if completed {
                // processorCommunicator->communicateTaskComplete(satCalcTask);
                return false; // 507
            }
            return true; // 509
        }

        false // 513
    }

    /// Ctx-threaded driver: the LOOP BODY of `handleTask` (cpp 326–450) run
    /// against a caller-owned context.
    ///
    /// KONCLUDE-PORT-NOTE[driver]: `handle_task` above preserves Konclude's
    /// scheduler shape, but its task-creation preamble is W6-DEFER'd
    /// (`sat_calc_task == Id::NONE`), so its loop body is unreachable. This is the
    /// SAME loop body, faithful statement-for-statement to cpp 326–450, operating
    /// on the context the caller (the bridge's saturation pre-pass, or a future
    /// Task layer) already owns — the exact seam convention the completion layer
    /// uses (`run_completion_on` vs Konclude's satisfiable task handler). Returns
    /// `true` (the C++ `satisfiable = true` tail; a clash never terminates the
    /// saturation loop — clashes are recorded as node status flags, not raised).
    pub fn run_saturation_on(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // KONCLUDE-PORT-NOTE[budget]: port-side safety valve, NOT in the C++ (its
        // scheduler can interrupt tasks; this driver owns the whole loop). On
        // overrun the driver returns `false` BEFORE
        // `complete_saturated_individual_nodes` (see the bail at the bottom): a
        // tripped valve can leave CRITICAL concepts queued but never tested, so no
        // per-node flag is trustworthy — the caller must discard the whole pass.
        let budget = std::time::Duration::from_secs(
            std::env::var("KM_HT_SATURATION_BUDGET_S")
                .ok()
                .and_then(|s| s.parse::<u64>().ok())
                .unwrap_or(120),
        );
        let t0 = std::time::Instant::now();
        let progress = std::env::var_os("KM_BRIDGE_PROGRESS").is_some();
        let report_timeout = |stage: &str, this: &Self, ctx: &CalculationAlgorithmContextBase| {
            if progress {
                let pc = ctx.process_context();
                let (main_label_entries, additional_label_entries) =
                    pc.reapply_con_sat_label_entry_counts();
                eprintln!(
                    "BRIDGE-SATURATION-TIMEOUT: stage={} nodes={} rules={} and={} or={} some={} all={} atleast={} atmost={} substituted={} copied={} all-ext-init={} added={{all:{},some:{},impl:{},trigger:{},sub:{},else:{}}}",
                    stage,
                    ctx.process_context().sat_node_count(),
                    this.applied_total_rule_count,
                    this.applied_and_rule_count,
                    this.applied_or_rule_count,
                    this.applied_some_rule_count,
                    this.applied_all_rule_count,
                    this.applied_atleast_rule_count,
                    this.applied_atmost_rule_count,
                    this.substituited_indi_node_count,
                    this.copied_indi_node_count,
                    this.all_succ_ext_initialized_count,
                    this.added_all_concepts,
                    this.added_some_concepts,
                    this.added_impl_concepts,
                    this.added_trigg_concepts,
                    this.added_sub_concepts,
                    this.added_else_concepts,
                );
                if this.diagnostic_counters_enabled {
                    eprintln!(
                        "BRIDGE-SATURATION-COUNTERS: concept-adds={} concept-new={} all-rule={} all-back-prop={} successor-create={} max-label={}",
                        this.diagnostic_concept_add_attempt_count,
                        this.diagnostic_concept_add_new_count,
                        this.diagnostic_all_rule_count,
                        this.diagnostic_all_back_prop_count,
                        this.diagnostic_successor_create_count,
                        this.diagnostic_max_label_count,
                    );
                    eprintln!(
                        "BRIDGE-SATURATION-ARENAS: sat-nodes={} concept-descriptors={} concept-process-linkers={} label-sets={} label-main-entries={} label-additional-logical-entries={} backward-links={} backward-reapply={} backward-hashes={} implication-reapply={}",
                        pc.sat_node_count(),
                        pc.con_sat_desc_count(),
                        pc.con_sat_proc_linker_count(),
                        pc.reapply_con_sat_label_set_count(),
                        main_label_entries,
                        additional_label_entries,
                        pc.backward_sat_prop_link_count(),
                        pc.backward_sat_prop_reapply_desc_count(),
                        pc.role_backward_sat_prop_hash_count(),
                        pc.imp_reapply_con_sat_desc_count(),
                    );
                    let mut largest_labels = Vec::new();
                    for raw in 0..pc.sat_node_count() {
                        let node_id = SatNodeId::new(raw as Cint64);
                        let node = pc.sat_node(node_id);
                        let label_id = node.reapply_con_sat_label_set;
                        if label_id.is_none() {
                            continue;
                        }
                        let label = pc.reapply_con_sat_label_set(label_id);
                        largest_labels.push((
                            label.get_concept_count(),
                            node_id,
                            node.get_individual_id(),
                            label.concept_des_dep_hash.len(),
                            if label.has_additional_concept_des_dep_hash {
                                label.additional_concept_des_dep_hash.len()
                            } else {
                                0
                            },
                            node.copy_indi_node,
                            node.get_saturation_concept_reference_linking(),
                        ));
                    }
                    largest_labels.sort_unstable_by(|a, b| b.0.cmp(&a.0));
                    for (rank, entry) in largest_labels.iter().take(12).enumerate() {
                        let (count, node, individual, main, additional, copy, reference) = *entry;
                        let (root_concept, root_tag, root_op) = if reference.is_some() {
                            let concept = pc
                                .extended_con_ref_linking_data(reference)
                                .get_saturation_concept();
                            let root = ctx.ontology_arenas().concept(concept);
                            (
                                concept.raw,
                                root.get_concept_tag(),
                                root.get_operator_code(),
                            )
                        } else {
                            (INVALID, INVALID, INVALID)
                        };
                        eprintln!(
                            "BRIDGE-SATURATION-LARGEST-LABEL: rank={} node={} individual={} concepts={} main={} additional={} copy-node={} root-concept={} root-tag={} root-op={}",
                            rank + 1,
                            node.raw,
                            individual,
                            count,
                            main,
                            additional,
                            copy.raw,
                            root_concept,
                            root_tag,
                            root_op,
                        );
                    }
                    if let Some(target_tag) = std::env::var("KM_SAT_COUNTER_LABEL_TAG")
                        .ok()
                        .and_then(|value| value.parse::<Cint64>().ok())
                    {
                        for raw in 0..pc.sat_node_count() {
                            let node_id = SatNodeId::new(raw as Cint64);
                            let node = pc.sat_node(node_id);
                            let reference = node.get_saturation_concept_reference_linking();
                            if reference.is_none() {
                                continue;
                            }
                            let root_concept = pc
                                .extended_con_ref_linking_data(reference)
                                .get_saturation_concept();
                            if ctx
                                .ontology_arenas()
                                .concept(root_concept)
                                .get_concept_tag()
                                != target_tag
                            {
                                continue;
                            }
                            let root = ctx.ontology_arenas().concept(root_concept);
                            let mut root_operand_ops = std::collections::BTreeMap::new();
                            for operand in root.get_operand_list() {
                                let op = ctx
                                    .ontology_arenas()
                                    .concept(operand.target)
                                    .get_operator_code();
                                *root_operand_ops
                                    .entry((op, operand.negated))
                                    .or_insert(0usize) += 1;
                            }
                            let label_id = node.reapply_con_sat_label_set;
                            let mut label_ops = std::collections::BTreeMap::new();
                            let mut sample = Vec::new();
                            let mut descriptor = if label_id.is_some() {
                                pc.reapply_con_sat_label_set(label_id)
                                    .get_concept_saturation_description_linker()
                            } else {
                                super::satellites::ConceptSaturationDescriptorId::NONE
                            };
                            let mut walked = 0usize;
                            while descriptor.is_some() && walked <= pc.con_sat_desc_count() {
                                let data = pc.con_sat_desc(descriptor);
                                let concept = ctx.ontology_arenas().concept(data.get_concept());
                                *label_ops
                                    .entry((concept.get_operator_code(), data.get_negation()))
                                    .or_insert(0usize) += 1;
                                if sample.len() < 32 {
                                    sample.push((
                                        concept.get_concept_tag(),
                                        concept.get_operator_code(),
                                        data.get_negation(),
                                    ));
                                }
                                descriptor = data.get_next_concept_desciptor();
                                walked += 1;
                            }
                            eprintln!(
                                "BRIDGE-SATURATION-TARGET-LABEL: node={} individual={} root-tag={} root-operands={} root-operand-ops={:?} label-concepts={} label-ops={:?} head-sample={:?}",
                                node_id.raw,
                                node.get_individual_id(),
                                target_tag,
                                root.get_operand_count(),
                                root_operand_ops,
                                walked,
                                label_ops,
                                sample,
                            );
                        }
                    }
                }
            }
        };

        self.continue_nominal_delayed_individual_node_processing(calc_alg_context); // 326

        while t0.elapsed() < budget
            && self.has_remaining_merging_critical_extension_processing_nodes(calc_alg_context)
        {
            while t0.elapsed() < budget
                && self.has_remaining_extension_processing_nodes(calc_alg_context)
            {
                while t0.elapsed() < budget && self.has_remaining_processing_nodes(calc_alg_context)
                {
                    while t0.elapsed() < budget
                        && calc_alg_context
                            .processing_data_box()
                            .has_individual_saturation_process_node_linker()
                    {
                        let indi_proc_sat_node_linker = calc_alg_context
                            .processing_data_box_mut()
                            .take_individual_saturation_process_node_linker();
                        let mut indi_proc_sat_node = calc_alg_context
                            .process_context()
                            .indi_sat_process_node_linker(indi_proc_sat_node_linker)
                            .get_processing_individual();
                        // (separated-saturation + first-processed-node-id tracking,
                        // cpp 338–349: debug/statistics bookkeeping only.)
                        if self
                            .individual_node_initializing(&mut indi_proc_sat_node, calc_alg_context)
                        {
                            let mut concept_saturation_process_linker = calc_alg_context
                                .process_context_mut()
                                .sat_node_take_concept_saturation_process_linker(
                                    indi_proc_sat_node,
                                );
                            while concept_saturation_process_linker.is_some() {
                                // Konclude's task scheduler can interrupt between
                                // rule applications.  This synchronous driver
                                // must make the same check inside a large node's
                                // concept queue; checking only between nodes lets
                                // one item overrun the whole saturation budget.
                                if t0.elapsed() >= budget {
                                    report_timeout("concept-queue", self, calc_alg_context);
                                    return false;
                                }
                                self.apply_tableau_saturation_rule(
                                    &mut indi_proc_sat_node,
                                    concept_saturation_process_linker,
                                    calc_alg_context,
                                );
                                self.release_concept_saturation_process_linker(
                                    concept_saturation_process_linker,
                                    calc_alg_context,
                                );
                                concept_saturation_process_linker = calc_alg_context
                                    .process_context_mut()
                                    .sat_node_take_concept_saturation_process_linker(
                                        indi_proc_sat_node,
                                    );
                            }
                        }
                        calc_alg_context
                            .process_context_mut()
                            .indi_sat_process_node_linker_mut(indi_proc_sat_node_linker)
                            .clear_processing_queued();
                        self.individual_node_conclusion(&mut indi_proc_sat_node, calc_alg_context);
                        // 363
                    }

                    if calc_alg_context
                        .processing_data_box()
                        .has_individual_disjunct_common_concept_extract_process_linker()
                    {
                        let indi_disj_common_con_ext_process_linker = calc_alg_context
                            .processing_data_box_mut()
                            .take_individual_disjunct_common_concept_extract_process_linker();
                        calc_alg_context
                            .process_context_mut()
                            .indi_sat_process_node_linker_mut(
                                indi_disj_common_con_ext_process_linker,
                            )
                            .set_processing_queued(false);
                        let mut indi_proc_sat_node = calc_alg_context
                            .process_context()
                            .indi_sat_process_node_linker(indi_disj_common_con_ext_process_linker)
                            .get_processing_individual();
                        if self
                            .individual_node_initializing(&mut indi_proc_sat_node, calc_alg_context)
                        {
                            self.update_extract_disjunct_common_concept(
                                &mut indi_proc_sat_node,
                                calc_alg_context,
                            ); // 379
                        }
                        self.individual_node_conclusion(&mut indi_proc_sat_node, calc_alg_context);
                        // 381
                    }
                }

                self.process_next_successor_extensions(calc_alg_context); // 396
            }

            if self.conf_check_critical_concepts
                && self.has_next_critical_concepts(calc_alg_context)
            {
                // KONCLUDE-PORT-NOTE[budget]: same port-side valve as the outer loops —
                // an overrun here leaves the remaining critical nodes unchecked and
                // therefore un-completed (UNKNOWN to every consumer), a sound defer.
                while t0.elapsed() < budget && self.has_next_critical_concepts(calc_alg_context) {
                    self.check_next_critical_concepts(calc_alg_context); // 414
                }
                self.check_critical_individuals(calc_alg_context); // 416
            }

            if calc_alg_context
                .processing_data_box()
                .has_saturation_atmost_merging_process_linker()
            {
                self.try_atmost_concept_successor_merging(calc_alg_context); // 432
            }
        }

        // KONCLUDE-PORT-NOTE[budget]: if the valve tripped, work remains queued —
        // including possibly UNCHECKED critical concepts. Completing nodes now would
        // let a node with a pending (never-tested) critical ∀/⊔/≤ read as
        // SAT-certain in the outcome extraction. Skip completion and report the
        // abort; the caller must discard the whole saturation pass.
        if self.has_remaining_merging_critical_extension_processing_nodes(calc_alg_context) {
            report_timeout("outer-queue", self, calc_alg_context);
            return false; // budget overrun — results unusable
        }

        self.complete_saturated_individual_nodes(calc_alg_context); // 438
        true // 450 (satisfiable)
    }

    /// Port of `hasRemainingExtensionProcessingNodes` (.cpp 689-698).
    pub fn has_remaining_extension_processing_nodes(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if self.has_remaining_processing_nodes(calc_alg_context) {
            return true; // 691
        }
        let ext_pro_indi_queue =
            calc_alg_context.saturation_sucessor_extension_individual_node_processing_queue(false); // 693
                                                                                                    // if (extProIndiQueue && !extProIndiQueue->isEmpty()) { return true; }
        if ext_pro_indi_queue.is_some() {
            let not_empty = !calc_alg_context
                .process_context()
                .sat_succ_ext_ind_node_proc_queue(ext_pro_indi_queue)
                .is_empty();
            if not_empty {
                return true; // 695
            }
        }
        false // 697
    }

    /// Port of `hasRemainingMergingCriticalExtensionProcessingNodes` (.cpp 702-713).
    pub fn has_remaining_merging_critical_extension_processing_nodes(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if self.conf_check_critical_concepts && self.has_next_critical_concepts(calc_alg_context) {
            return true; // 704
        }
        if calc_alg_context
            .processing_data_box()
            .has_saturation_atmost_merging_process_linker()
        {
            return true; // 707
        }
        if self.has_remaining_extension_processing_nodes(calc_alg_context) {
            return true; // 710
        }
        false // 712
    }

    /// Port of `continueNominalDelayedIndividualNodeProcessing` (.cpp 718-757).
    pub fn continue_nominal_delayed_individual_node_processing(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut nominal_delayed_individual_node_processing_continued = false; // 719
        if calc_alg_context
            .processing_data_box()
            .has_nominal_delayed_individual_saturation_process_node_linker()
        {
            if self.is_consistence_data_available(calc_alg_context) {
                while calc_alg_context
                    .processing_data_box()
                    .has_nominal_delayed_individual_saturation_process_node_linker()
                {
                    // linker = take…(); indiProcessNode = linker->getProcessingIndividual();
                    let nominal_delayed_ind_sat_proc_node_linker = calc_alg_context
                        .processing_data_box_mut()
                        .take_nominal_delayed_individual_saturation_process_node_linker();
                    calc_alg_context
                        .process_context_mut()
                        .indi_sat_process_node_linker_mut(nominal_delayed_ind_sat_proc_node_linker)
                        .set_processing_queued(false);
                    let mut indi_process_node = calc_alg_context
                        .process_context()
                        .indi_sat_process_node_linker(nominal_delayed_ind_sat_proc_node_linker)
                        .get_processing_individual();

                    // CCriticalSaturationConceptTypeQueues* criticalConceptQueues =
                    //   indiProcessNode->getCriticalConceptTypeQueues(false);
                    // if (criticalConceptQueues && criticalConceptQueues->hasCriticalSaturationConceptsQueued()) {
                    //   CCriticalIndividualNodeProcessingQueue* q =
                    //     processingDataBox->getSaturationCriticalIndividualNodeProcessingQueue(true);
                    //   q->insertProcessIndiviudal(indiProcessNode);
                    //   criticalConceptQueues->setProcessNodeQueued(true);
                    // }
                    // W2-DEFER[api]: CCriticalSaturationConceptTypeQueues satellite
                    // (`get_critical_concept_type_queues` returns an opaque handle).

                    // CSaturationIndividualNodeNominalHandlingData* nominalHandlingData =
                    //   indiProcessNode->getNominalHandlingData(false);
                    // if (nominalHandlingData && nominalHandlingData->getDelayedNominalConceptSaturationProcessLinker()) {
                    //   while (nominalHandlingData->getDelayedNominalConceptSaturationProcessLinker()) {
                    //     CConceptSaturationProcessLinker* l = nominalHandlingData->takeDelayedNominalConceptSaturationProcessLinker();
                    //     l->clearNext();
                    //     indiProcessNode->addConceptSaturationProcessLinker(l);
                    //   }
                    //   addIndividualToProcessingQueue(indiProcessNode, calcAlgContext);
                    // }
                    // W2-DEFER[api]: CSaturationIndividualNodeNominalHandlingData satellite
                    // (`get_nominal_handling_data` returns an opaque handle); the
                    // re-queueing `addIndividualToProcessingQueue` is part of that block.

                    // indiProcessNode->getIndividualSaturationCompletionNodeLinker(true)->setProcessingQueued(false);
                    calc_alg_context
                        .process_context_mut()
                        .sat_node_set_individual_saturation_completion_node_linker_queued(
                            indi_process_node,
                            false,
                        ); // 747
                    self.add_individual_to_completion_queue(
                        &mut indi_process_node,
                        calc_alg_context,
                    ); // 748
                    nominal_delayed_individual_node_processing_continued = true;
                    // 749
                }

                calc_alg_context
                    .processing_data_box_mut()
                    .set_delayed_nominal_processing_occured(false); // 752
            }
        }
        nominal_delayed_individual_node_processing_continued // 756
    }

    /// Port of `completeSaturatedIndividualNodes` (.cpp 760-785).
    pub fn complete_saturated_individual_nodes(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut completed_individual_count: Cint64 = 0; // 762
        if calc_alg_context
            .processing_data_box()
            .has_individual_saturation_completion_node_linker()
        {
            while calc_alg_context
                .processing_data_box()
                .has_individual_saturation_completion_node_linker()
            {
                // linker = take…(); indiProcessNode = linker->getProcessingIndividual();
                let indi_process_node_linker = calc_alg_context
                    .processing_data_box_mut()
                    .take_individual_saturation_completion_node_linker();
                let indi_process_node = calc_alg_context
                    .process_context()
                    .indi_sat_process_node_linker(indi_process_node_linker)
                    .get_processing_individual(); // 765
                let mut complete_individual = true; // 767
                                                    // if (indiProcessNode->getIndirectStatusFlags()->hasMissedABoxConsistencyFlag())
                                                    // W2-DEFER[api]: the `hasMissedABoxConsistencyFlag` status bit is not
                                                    // yet ported; treated as unset (the common "complete now" path).
                let has_missed_abox_consistency = false;
                if has_missed_abox_consistency {
                    if !self.is_consistence_data_available(calc_alg_context) {
                        complete_individual = false; // 770
                        calc_alg_context
                            .processing_data_box_mut()
                            .add_nominal_delayed_individual_saturation_process_node_linker(
                                indi_process_node_linker,
                            ); // 771
                               // if (indiProcessNode->getReapplyConceptSaturationLabelSet(false)) {
                               //   …->setLastNominalIndependentConceptSaturationDescriptorLinker(
                               //       …->getConceptSaturationDescriptionLinker());
                               // }
                               // W2-DEFER[api]: the label-set last-nominal-independent linker
                               // accessors are not yet ported.
                    }
                }
                if complete_individual {
                    calc_alg_context
                        .processing_data_box_mut()
                        .add_individual_saturation_completed_node_linker(indi_process_node_linker); // 778
                    completed_individual_count += 1; // 779
                    calc_alg_context
                        .process_context_mut()
                        .sat_node_mut(indi_process_node)
                        .set_completed(true); // 780
                    let final_debug = super::sat_final_debug_tag();
                    let reference = calc_alg_context
                        .process_context()
                        .sat_node(indi_process_node)
                        .get_saturation_concept_reference_linking();
                    let reference_concept = if reference.is_some() {
                        calc_alg_context
                            .process_context()
                            .extended_con_ref_linking_data(reference)
                            .get_saturation_concept()
                    } else {
                        ConceptId::NONE
                    };
                    if reference_concept.is_some()
                        && final_debug
                            == Some(
                                calc_alg_context
                                    .ontology_arenas()
                                    .concept(reference_concept)
                                    .get_concept_tag(),
                            )
                    {
                        let label = calc_alg_context
                            .process_context()
                            .sat_node(indi_process_node)
                            .reapply_con_sat_label_set;
                        eprintln!(
                            "SAT-FINAL node={} tag={} label={} flags={:#x}",
                            indi_process_node.raw,
                            calc_alg_context
                                .ontology_arenas()
                                .concept(reference_concept)
                                .get_concept_tag(),
                            if label.is_some() {
                                calc_alg_context
                                    .process_context()
                                    .reapply_con_sat_label_set(label)
                                    .get_concept_count()
                            } else {
                                0
                            },
                            calc_alg_context
                                .process_context()
                                .sat_node(indi_process_node)
                                .indirect_status_flags
                                .get_flags(),
                        );
                        if label.is_some() {
                            let mut descriptor = calc_alg_context
                                .process_context()
                                .reapply_con_sat_label_set(label)
                                .get_concept_saturation_description_linker();
                            while descriptor.is_some() {
                                let (concept, negated, next) = {
                                    let value =
                                        calc_alg_context.process_context().con_sat_desc(descriptor);
                                    (
                                        value.get_concept(),
                                        value.get_negation(),
                                        value.get_next_concept_desciptor(),
                                    )
                                };
                                let concept_ref =
                                    calc_alg_context.ontology_arenas().concept(concept);
                                if !negated
                                    && matches!(
                                        concept_ref.get_operator_code(),
                                        super::super::model::op::CCSOME
                                            | super::super::model::op::CCAQSOME
                                    )
                                {
                                    let fillers = concept_ref
                                        .get_operand_list()
                                        .iter()
                                        .map(|operand| {
                                            calc_alg_context
                                                .ontology_arenas()
                                                .concept(operand.target)
                                                .get_concept_tag()
                                                .to_string()
                                        })
                                        .collect::<Vec<_>>()
                                        .join(",");
                                    eprintln!(
                                        "SAT-FINAL-SOME concept={} role={} fillers=[{}]",
                                        concept_ref.get_concept_tag(),
                                        if concept_ref.get_role().is_some() {
                                            calc_alg_context
                                                .ontology_arenas()
                                                .role(concept_ref.get_role())
                                                .get_role_tag()
                                        } else {
                                            -1
                                        },
                                        fillers,
                                    );
                                } else if concept_ref.get_operator_code()
                                    == super::super::model::op::CCAQCHOOCE
                                {
                                    let operands = concept_ref
                                        .get_operand_list()
                                        .iter()
                                        .map(|operand| {
                                            let target = calc_alg_context
                                                .ontology_arenas()
                                                .concept(operand.target);
                                            format!(
                                                "{}{}:{}",
                                                if operand.negated { "-" } else { "+" },
                                                target.get_concept_tag(),
                                                target.get_operator_code(),
                                            )
                                        })
                                        .collect::<Vec<_>>()
                                        .join(",");
                                    eprintln!(
                                        "SAT-FINAL-CHOOSE concept={} neg={} operands=[{}]",
                                        concept_ref.get_concept_tag(),
                                        negated,
                                        operands,
                                    );
                                }
                                descriptor = next;
                            }
                        }
                    }
                }
            }
        }
        completed_individual_count > 0 // 784
    }

    /// Port of `hasRemainingProcessingNodes` (.cpp 788-793).
    pub fn has_remaining_processing_nodes(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let pdb = calc_alg_context.processing_data_box();
        if pdb.has_individual_saturation_process_node_linker()
            || pdb.has_individual_disjunct_common_concept_extract_process_linker()
        {
            return true; // 790
        }
        false // 792
    }

    /// Port of `setDelayedNominalProcessingOccured` (.cpp 6910-6912).
    pub fn set_delayed_nominal_processing_occured(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        calc_alg_context
            .processing_data_box_mut()
            .set_delayed_nominal_processing_occured(true); // 6911
    }

    /// Port of `setInsufficientNodeOccured` (.cpp 6915-6917).
    pub fn set_insufficient_node_occured(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        calc_alg_context
            .processing_data_box_mut()
            .set_insufficient_node_occured(true); // 6916
    }

    /// Port of `setProblematicEQCandidateOccured` (.cpp 6920-6922).
    pub fn set_problematic_eq_candidate_occured(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        calc_alg_context
            .processing_data_box_mut()
            .set_problematic_eq_candidate_occured(true); // 6921
    }

    /// Port of `addIndividualToProcessingQueue` (.cpp 7119-7125).
    pub fn add_individual_to_processing_queue(
        &mut self,
        process_indi: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let process_node_linker = calc_alg_context
            .process_context_mut()
            .sat_node_individual_saturation_process_node_linker(*process_indi, true); // 7120
        if !calc_alg_context
            .process_context()
            .indi_sat_process_node_linker(process_node_linker)
            .is_processing_queued()
        {
            calc_alg_context
                .process_context_mut()
                .indi_sat_process_node_linker_mut(process_node_linker)
                .set_processing_queued(true);
            calc_alg_context
                .processing_data_box_mut()
                .add_individual_saturation_process_node_linker(process_node_linker);
            // 7123
        }
    }

    /// Port of `addUninitializedIndividualToProcessingQueue` (.cpp 7127-7131).
    pub fn add_uninitialized_individual_to_processing_queue(
        &mut self,
        process_indi: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if !calc_alg_context
            .process_context()
            .sat_node(*process_indi)
            .is_initialized()
        {
            self.add_individual_to_processing_queue(process_indi, calc_alg_context);
            // 7129
        }
    }

    /// Port of `addIndividualToCompletionQueue` (.cpp 7135-7141).
    pub fn add_individual_to_completion_queue(
        &mut self,
        process_indi: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if !calc_alg_context
            .process_context()
            .sat_node_individual_saturation_completion_node_linker_queued(*process_indi)
        {
            // CIndividualSaturationProcessNodeLinker* processNodeLinker =
            //   processIndi->getIndividualSaturationCompletionNodeLinker(true);
            calc_alg_context
                .process_context_mut()
                .sat_node_set_individual_saturation_completion_node_linker_queued(
                    *process_indi,
                    true,
                ); // 7137
            let process_node_linker = calc_alg_context
                .process_context_mut()
                .sat_node_individual_saturation_completion_node_linker(*process_indi, true);
            calc_alg_context
                .processing_data_box_mut()
                .add_individual_saturation_completion_node_linker(process_node_linker);
            // 7139
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::process::sat_node::IndividualSaturationProcessNode;
    use super::super::algorithm::SaturationTaskHandleAlgorithm;
    use super::*;

    #[test]
    fn has_remaining_extension_processing_nodes_reads_successor_extension_queue() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(23));
        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(true);

        assert!(!algo.has_remaining_extension_processing_nodes(&mut ctx));

        ctx.process_context_mut()
            .sat_succ_ext_ind_node_proc_queue_mut(queue)
            .insert_process_individual(node, 23);

        assert!(algo.has_remaining_extension_processing_nodes(&mut ctx));
    }
}
