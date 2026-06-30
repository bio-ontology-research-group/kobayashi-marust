//! `completion::u04` — port unit #4 of the completion task-handle algorithm
//! (family: Core processing loop / driver; 17 methods, cpp 19901–19992 +
//! 26692–27551).
//!
//! Source (READ-ONLY): Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! Ported methods (in cpp order):
//!   - `searchReactivateIndividualsProcessedPropagated`            [19901]
//!   - `propagateIndividualUnprocessed`                            [19958]
//!   - `propagateIndividualUnprocessed` (requiresConsFlag)         [19968]
//!   - `addConceptToIndividualSkipANDProcessing`                   [26692]
//!   - `insertConceptProcessDescriptorToProcessingQueue`          [27152]
//!   - `insertConceptProcessDescriptorToProcessingQueue` (binding) [27166]
//!   - `addConceptToProcessingQueue` (conceptDescriptor)           [27185]
//!   - `needsProcessingForConcept`                                 [27203]
//!   - `addConceptPreprocessedToProcessingQueue` (bindingCount)    [27216]
//!   - `addConceptPreprocessedToProcessingQueue` (skipFunction)    [27228]
//!   - `addConceptToProcessingQueue` (reinsert)                    [27278]
//!   - `addCopiedConceptToProcessingQueue`                         [27284]
//!   - `addConceptRestrictedToProcessingQueue` (dispatch)          [27311]
//!   - `addConceptRestrictedToProcessingQueue` (priorityOffset)    [27325]
//!   - `addConceptRestrictedFixedPriorityToProcessingQueue`        [27345]
//!   - `addIndividualToProcessingQueueBasedOnProcessingConcepts`   [27359]
//!   - `addIndividualToProcessingQueue`                            [27419]
//!
//! KONCLUDE-PORT-NOTE[ownership]: pointers become arena ids
//! (`CIndividualProcessNode*` → `NodeId`, `CConceptDescriptor*` → `ConDescId`,
//! `CConceptProcessDescriptor*` → `ConProcDescId`, `CDependencyTrackPoint*` →
//! `TrackPointId`, `CConceptProcessingQueue*` → `ConceptProcessingQueueId`); the
//! `calcAlgContext` pointer becomes a threaded `&mut CalculationAlgorithmContextBase`,
//! and `calcAlgContext->getProcessingDataBox()` is the owned databox reached via
//! `calc_alg_context.processing_data_box_mut()`.
//!
//! KONCLUDE-PORT-NOTE[api]: this is the FIRST completion unit; the per-thread node
//! arena resolver (`CIndividualProcessNodeVector::getLocalData`) is not yet wired
//! into the context, so every `indi->...` node-state read/write, every
//! concept-descriptor allocation, every priority-strategy / process-tagger call,
//! and every insert into a Process-layer queue stub is marked `// W3-DEFER[api]`
//! with a control-flow-preserving stub (`false`/`0`/`Id::NONE`/`INVALID`). The
//! databox queue GETTERS that already exist are routed through the context; only
//! the stub `insert*` on the returned handle is deferred. Branch/loop/recursion
//! structure is reproduced verbatim. Cross-unit algorithm calls
//! (`createConceptDescriptor`, `applyReapplyQueueConcepts`, `getLocalizedIndividual`,
//! `getSuccessorIndividual`, `getUpToDateIndividual`, `tableauRuleChoice`, the
//! `apply*Rule` jump targets, …) land in later units and are deferred likewise.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::op::CCFS_PROPAGATION_TYPE;
use super::super::model::ConceptId;
use super::super::process::ls1::CondensedReapplyQueueIterator;
use super::super::process::node::IndividualProcessNode;
use super::super::process::stubs::ConceptProcessingQueueId;
use super::super::process::{ConDescId, ConProcDescId, LabelSetId, NodeId, TrackPointId};

use super::algorithm::{DETERMINISTIC_PROCESS_PRIORITY, IMMEDIATELY_PROCESS_PRIORITY};
use super::context::CalculationAlgorithmContextBase;

/// KONCLUDE-PORT-NOTE[api]: `CProcessingRestrictionSpecification*` is not yet
/// ported; modelled as an opaque handle (`INVALID` == `nullptr`).
type ProcRestrictionHandle = Cint64;
/// KONCLUDE-PORT-NOTE[pointer-alias]: a `TableauRuleFunction` (pointer-to-member of
/// an `apply*Rule`) is an opaque rule-slot handle until those methods are ported.
type TableauRuleFunction = Cint64;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::searchReactivateIndividualsProcessedPropagated`.
    pub fn search_reactivate_individuals_processed_propagated(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: processingBlockedNodeLinker = indi->getProcessingBlockedIndividualsLinker();
        let processing_blocked_node_linker: Vec<NodeId> = Vec::new();
        for blocked_node in processing_blocked_node_linker {
            // W3-DEFER[api]: locBlockedNode = getLocalizedIndividual(blockedNode,true,calcAlgContext);
            let loc_blocked_node = blocked_node;
            // W3-DEFER[api]: locBlockedNode->addProcessingRestrictionFlags(PRFBLOCKINGRETESTDUEPROCESSINGCOMPLETED);
            let _ = IndividualProcessNode::PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED;
            self.add_individual_to_processing_queue(loc_blocked_node, calc_alg_context);
            // set blocking retest flag, clear processing blocked flag
        }
        // W3-DEFER[api]: indi->clearBlockedIndividualsLinker();

        // W3-DEFER[api]: indiID = indi->getIndividualNodeID();
        let indi_id: Cint64 = INVALID;

        // TODO: check multiple not processed ancestors
        // W3-DEFER[api]: succIt = indi->getSuccessorIterator(); ancDepth = indi->getIndividualAncestorDepth();
        let succ_it: Vec<NodeId> = Vec::new();
        let anc_depth: Cint64 = 0;
        for succ_link in succ_it {
            // W3-DEFER[api]: succIndi = getSuccessorIndividual(indi,succLink,calcAlgContext);
            let succ_indi = succ_link;
            // W3-DEFER[api]: succAncDepth = succIndi->getIndividualAncestorDepth();
            let succ_anc_depth: Cint64 = 0;
            if succ_anc_depth > anc_depth {
                // W3-DEFER[api]: !succIndi->hasPartialProcessingRestrictionFlags(PRFANCESTORALLPROCESSED)
                let succ_ancestor_all_processed = false;
                if !succ_ancestor_all_processed {
                    // test whether have unprocessed nominals or ancestor
                    let mut all_processed_ancestor = true;
                    // W3-DEFER[api]: connIt = succIndi->getConnectionSuccessorIterator();
                    let conn_it: Vec<Cint64> = Vec::new();
                    let mut conn_iter = conn_it.into_iter();
                    while all_processed_ancestor {
                        let conn_indi_node_id = match conn_iter.next() {
                            Some(v) => v,
                            None => break,
                        };
                        if conn_indi_node_id != indi_id {
                            // W3-DEFER[api]: ancNomIndi = getUpToDateIndividual(connIndiNodeID,calcAlgContext);
                            // W3-DEFER[api]: ancNomIndi->getIndividualAncestorDepth() / isNominalIndividualNode()
                            let anc_nom_ancestor_depth: Cint64 = 0;
                            let anc_nom_is_nominal = false;
                            if anc_nom_ancestor_depth >= anc_depth || anc_nom_is_nominal {
                                // W3-DEFER[api]: !ancNomIndi->hasPartialProcessingRestrictionFlags(PRFPROCESSINGCOMPLETED | PRFANCESTORALLPROCESSED)
                                let anc_nom_processed_or_all = false;
                                if !anc_nom_processed_or_all {
                                    all_processed_ancestor = false;
                                }
                            }
                        }
                    }
                    if all_processed_ancestor {
                        // W3-DEFER[api]: locSuccIndi = getLocalizedIndividual(succIndi,false,calcAlgContext);
                        let loc_succ_indi = succ_indi;
                        // W3-DEFER[api]: locSuccIndi->addProcessingRestrictionFlags(PRFANCESTORALLPROCESSED);
                        // W3-DEFER[api]: !locSuccIndi->hasPartialProcessingRestrictionFlags(PRFPROCESSINGCOMPLETED)
                        let loc_succ_processing_completed = false;
                        if !loc_succ_processing_completed {
                            // W3-DEFER[api]: locSuccIndi->hasPartialProcessingRestrictionFlags(PRFPROCESSINGBLOCKED)
                            let loc_succ_processing_blocked = false;
                            if loc_succ_processing_blocked {
                                // W3-DEFER[api]: locSuccIndi->addProcessingRestrictionFlags(PRFBLOCKINGRETESTDUEPROCESSINGCOMPLETED);
                                self.add_individual_to_processing_queue(loc_succ_indi, calc_alg_context);
                            }
                        } else {
                            // search recursive all nodes which has to be reactivated
                            self.search_reactivate_individuals_processed_propagated(
                                loc_succ_indi,
                                calc_alg_context,
                            );
                        }
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateIndividualUnprocessed`.
    pub fn propagate_individual_unprocessed(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.opt_processed_node_propagation {
            self.propagate_individual_unprocessed_cons(indi, false, calc_alg_context);
        } else if self.opt_processed_cons_node_propagation {
            self.propagate_individual_unprocessed_cons(indi, true, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateIndividualUnprocessed`
    /// (the `requiresConsFlag` overload).
    pub fn propagate_individual_unprocessed_cons(
        &mut self,
        indi: NodeId,
        requires_cons_flag: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: indi->hasPartialProcessingRestrictionFlags(PRFCONSNODEPREPARATIONINDINODE)
        let indi_cons_node_preparation = false;
        if !requires_cons_flag || indi_cons_node_preparation {
            // W3-DEFER[api]: indi->hasPartialProcessingRestrictionFlags(PRFPROCESSINGCOMPLETED)
            let indi_processing_completed = false;
            if indi_processing_completed {
                // W3-DEFER[api]: indi->clearProcessingRestrictionFlags(PRFPROCESSINGCOMPLETED);
                // W3-DEFER[api]: indi->hasPartialProcessingRestrictionFlags(PRFANCESTORALLPROCESSED)
                let indi_ancestor_all_processed = false;
                if indi_ancestor_all_processed {
                    // W3-DEFER[api]: succIt = indi->getSuccessorIterator(); ancDepth = indi->getIndividualAncestorDepth();
                    let succ_it: Vec<NodeId> = Vec::new();
                    let anc_depth: Cint64 = 0;
                    for succ_link in succ_it {
                        // W3-DEFER[api]: succIndi = getSuccessorIndividual(indi,succLink,calcAlgContext);
                        let succ_indi = succ_link;
                        // W3-DEFER[api]: succAncDepth = succIndi->getIndividualAncestorDepth();
                        let succ_anc_depth: Cint64 = 0;
                        if succ_anc_depth > anc_depth {
                            // W3-DEFER[api]: !succIndi->hasPartialProcessingRestrictionFlags(PRFANCESTORALLPROCESSED)
                            let succ_ancestor_all_processed = false;
                            if !succ_ancestor_all_processed {
                                // W3-DEFER[api]: locSuccIndi = getLocalizedIndividual(succIndi,false,calcAlgContext);
                                let loc_succ_indi = succ_indi;
                                // W3-DEFER[api]: locSuccIndi->clearProcessingRestrictionFlags(PRFANCESTORALLPROCESSED);
                                self.propagate_individual_unprocessed_cons(
                                    loc_succ_indi,
                                    // KONCLUDE-PORT-NOTE[overload]: C++ passes the flag value
                                    // PRFANCESTORALLPROCESSED here as the `requiresConsFlag` bool
                                    // argument (non-zero ⇒ true).
                                    IndividualProcessNode::PRF_ANCESTORALLPROCESSED != 0,
                                    calc_alg_context,
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToIndividualSkipANDProcessing`.
    pub fn add_concept_to_individual_skip_and_processing(
        &mut self,
        adding_concept: ConceptId,
        negate: bool,
        process_indi: NodeId,
        dependency_track_point: TrackPointId,
        allow_preprocessing: bool,
        allow_initalization: bool,
        mark_modification: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();

        // W3-DEFER[api]: conProQueue = processIndi->getConceptProcessingQueue(true);
        let con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        // W3-DEFER[api]: conLabelSet = processIndi->getReapplyConceptLabelSet(true);
        let con_label_set: LabelSetId = Id::NONE;

        debug_assert!(
            dependency_track_point != Id::NONE,
            "adding concept to individual: dependency track point missing"
        );
        debug_assert!(
            adding_concept != Id::NONE,
            "adding concept to individual: concept missing"
        );

        // W3-DEFER[api]: conceptDescriptor = createConceptDescriptor(calcAlgContext);
        //                conceptDescriptor->initConceptDescriptor(addingConcept,negate,dependencyTrackPoint);
        let concept_descriptor: ConDescId = Id::NONE;
        // CCondensedReapplyQueueIterator reapplyIt;
        // W3-DEFER[api]: contained = insertConceptsToIndividualConceptSet(conceptDescriptor,
        //                  dependencyTrackPoint,processIndi,conLabelSet,&reapplyIt,allowInitalization,calcAlgContext);
        let contained = false;
        let reapply_it_has_next = false; // reapplyIt.hasNext()
        if !contained {
            self.stat_con_des_insertion_count += 1;
            // W3-DEFER[api]: STATINC(CONCEPTSADDEDINDINODELABELSETCOUNT,calcAlgContext);
            // W3-DEFER[api]: addBlockingCoreConcept(conceptDescriptor,processIndi,conLabelSet,calcAlgContext);
            if mark_modification {
                // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi, calcAlgContext);
            }
            // KONCLUDE-PORT-NOTE[pointer-alias]: skipFunction = &applyANDRule (rule-slot handle).
            self.add_concept_preprocessed_to_processing_queue_skip(
                concept_descriptor,
                dependency_track_point,
                con_pro_queue,
                process_indi,
                allow_preprocessing,
                calc_alg_context,
                INVALID, // W3-DEFER[api]: &CCalculationTableauCompletionTaskHandleAlgorithm::applyANDRule
            );
            if reapply_it_has_next {
                // reapply reapplying concept
                // W3-DEFER[api]: applyReapplyQueueConcepts(processIndi,&reapplyIt,calcAlgContext);
            }
        } else {
            self.stat_con_des_contained_count += 1;
            // W3-DEFER[api]: releaseConceptDescriptor(conceptDescriptor,calcAlgContext);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::insertConceptProcessDescriptorToProcessingQueue`.
    pub fn insert_concept_process_descriptor_to_processing_queue(
        &mut self,
        con_pro_des: ConProcDescId,
        concept_processing_queue: ConceptProcessingQueueId,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: concept = conProDes->getConceptDescriptor()->getConcept();
        let concept: ConceptId = Id::NONE;
        // W3-DEFER[api]: conOperator = concept->getConceptOperator();

        // W3-DEFER[api]: conOperator->hasPartialOperatorCodeFlag(CCFS_PROPAGATION_TYPE)
        let has_propagation_type = false;
        if has_propagation_type {
            let _var_bind_con_batch_proc_queue = calc_alg_context
                .processing_data_box_mut()
                .get_variable_binding_concept_batch_processing_queue(true);
            // W3-DEFER[api]: varBindConBatchProcQueue->insertIndiviudalForConcept(concept,processIndi,conProDes);
        } else {
            // W3-DEFER[api]: conceptProcessingQueue->insertConceptProcessDescriptor(conProDes);
            let _ = concept_processing_queue;
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::insertConceptProcessDescriptorToProcessingQueue`
    /// (the `bindingCount` overload).
    pub fn insert_concept_process_descriptor_to_processing_queue_binding(
        &mut self,
        con_pro_des: ConProcDescId,
        concept_processing_queue: ConceptProcessingQueueId,
        binding_count: Cint64,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: concept = conProDes->getConceptDescriptor()->getConcept();
        let concept: ConceptId = Id::NONE;
        // W3-DEFER[api]: conOperator = concept->getConceptOperator();

        // W3-DEFER[api]: conOperator->hasPartialOperatorCodeFlag(CCFS_PROPAGATION_ALL_TYPE | CCFS_PROPAGATION_AND_TYPE)
        let has_propagation_all_and_type = false;
        // W3-DEFER[api]: conOperator->hasPartialOperatorCodeFlag(CCFS_PROPAGATION_TYPE)
        let has_propagation_type = false;
        if has_propagation_all_and_type {
            let _var_bind_con_batch_proc_queue = calc_alg_context
                .processing_data_box_mut()
                .get_variable_binding_concept_batch_processing_queue(true);
            // W3-DEFER[api]: varBindConBatchProcQueue->insertIndiviudalForBindingCount(concept,bindingCount,processIndi,conProDes);
        } else if has_propagation_type {
            let _var_bind_con_batch_proc_queue = calc_alg_context
                .processing_data_box_mut()
                .get_variable_binding_concept_batch_processing_queue(true);
            // W3-DEFER[api]: varBindConBatchProcQueue->insertIndiviudalForConcept(concept,processIndi,conProDes);
        } else {
            // W3-DEFER[api]: conceptProcessingQueue->insertConceptProcessDescriptor(conProDes);
            let _ = concept_processing_queue;
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToProcessingQueue`
    /// (the `conceptDescriptor` overload).
    pub fn add_concept_to_processing_queue(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        concept_processing_queue: ConceptProcessingQueueId,
        process_indi: NodeId,
        reapplied: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();

        if self.needs_processing_for_concept(concept_descriptor, dep_track_point, process_indi, calc_alg_context)
        {
            // W3-DEFER[api]: STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT,calcAlgContext);
            // W3-DEFER[api]: conProDes = allocateAndConstruct(taskMemMan);
            //                conProPriority = getUsedConceptPriorityStrategy()->getPriorityForConcept(conceptDescriptor,processIndi);
            //                conProDes->init(conceptDescriptor,conProPriority,reapplied,depTrackPoint);
            let con_pro_des: ConProcDescId = Id::NONE;

            self.insert_concept_process_descriptor_to_processing_queue(
                con_pro_des,
                concept_processing_queue,
                process_indi,
                calc_alg_context,
            );

            //propagateIndividualUnprocessed(processIndi,calcAlgContext);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::needsProcessingForConcept`.
    pub fn needs_processing_for_concept(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let func: TableauRuleFunction;
        // W3-DEFER[api]: opCode = conceptDescriptor->getConcept()->getOperatorCode();
        let op_code: Cint64 = 0;
        // W3-DEFER[api]: conNeg = conceptDescriptor->isNegated();
        let con_neg = false;
        if con_neg {
            func = self.neg_tableau_rule_jump_func_vec[op_code as usize];
        } else {
            func = self.pos_tableau_rule_jump_func_vec[op_code as usize];
        }
        func != INVALID
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptPreprocessedToProcessingQueue`
    /// (the `bindingCount` overload).
    pub fn add_concept_preprocessed_to_processing_queue(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        concept_processing_queue: ConceptProcessingQueueId,
        process_indi: NodeId,
        binding_count: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();

        // W3-DEFER[api]: STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT,calcAlgContext);
        // W3-DEFER[api]: conProPriority = getUsedConceptPriorityStrategy()->getPriorityForConcept(conceptDescriptor,processIndi);
        // W3-DEFER[api]: conProDes = allocateAndConstruct(taskMemMan);
        //                conProDes->init(conceptDescriptor,conProPriority,false,depTrackPoint);
        let con_pro_des: ConProcDescId = Id::NONE;
        self.insert_concept_process_descriptor_to_processing_queue_binding(
            con_pro_des,
            concept_processing_queue,
            binding_count,
            process_indi,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptPreprocessedToProcessingQueue`
    /// (the `allowPreprocessing` / `skipFunction` overload).
    pub fn add_concept_preprocessed_to_processing_queue_skip(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        concept_processing_queue: ConceptProcessingQueueId,
        process_indi: NodeId,
        mut allow_preprocessing: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        skip_function: TableauRuleFunction,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();

        // TODO: check necessary
        let func: TableauRuleFunction;
        // W3-DEFER[api]: opCode = conceptDescriptor->getConcept()->getOperatorCode();
        let op_code: Cint64 = 0;
        // W3-DEFER[api]: conNeg = conceptDescriptor->isNegated();
        let con_neg = false;
        if con_neg {
            func = self.neg_tableau_rule_jump_func_vec[op_code as usize];
        } else {
            func = self.pos_tableau_rule_jump_func_vec[op_code as usize];
        }
        if func == INVALID || func == skip_function {
            return;
        }

        allow_preprocessing &= self.conf_direct_rule_preprocessing;
        if self.current_rec_proc_depth > self.current_rec_proc_depth_limit {
            allow_preprocessing = false;
        }

        // W3-DEFER[api]: concept = conceptDescriptor->getConcept(); conOperator = concept->getConceptOperator();
        // W3-DEFER[api]: conOperator->hasPartialOperatorCodeFlag(CCFS_PROPAGATION_TYPE)
        let has_propagation_type = false;
        if has_propagation_type {
            allow_preprocessing = false;
        }

        // W3-DEFER[api]: STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT,calcAlgContext);
        // W3-DEFER[api]: conProPriority = getUsedConceptPriorityStrategy()->getPriorityForConcept(conceptDescriptor,processIndi);
        // W3-DEFER[api]: conProDes = allocateAndConstruct(taskMemMan);
        //                conProDes->init(conceptDescriptor,conProPriority,false,depTrackPoint);
        let con_pro_des: ConProcDescId = Id::NONE;
        // W3-DEFER[api]: conProPriority.getPriority()
        let con_pro_priority_value: f64 = 0.0;

        if allow_preprocessing && con_pro_priority_value >= IMMEDIATELY_PROCESS_PRIORITY as f64 {
            // W3-DEFER[api]: STATINC(RULEAPPLICATIONCOUNT,calcAlgContext);
            // W3-DEFER[api]: tableauRuleChoice(processIndi,conProDes,calcAlgContext);
            let _ = (process_indi, con_pro_des);
        } else {
            self.insert_concept_process_descriptor_to_processing_queue(
                con_pro_des,
                concept_processing_queue,
                process_indi,
                calc_alg_context,
            );
            //propagateIndividualUnprocessed(processIndi,calcAlgContext);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToProcessingQueue`
    /// (the `reinsertConProDes` overload).
    pub fn add_concept_to_processing_queue_reinsert(
        &mut self,
        reinsert_con_pro_des: ConProcDescId,
        concept_processing_queue: ConceptProcessingQueueId,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT,calcAlgContext);
        // W3-DEFER[api]: conceptProcessingQueue->reinsertConceptProcessDescriptor(reinsertConProDes);
        let _ = (reinsert_con_pro_des, concept_processing_queue);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addCopiedConceptToProcessingQueue`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ `CIndividualProcessNode*& processIndi` is
    /// reassigned (localisation), so it is threaded as `&mut NodeId`.
    pub fn add_copied_concept_to_processing_queue(
        &mut self,
        copy_con_pro_des: ConProcDescId,
        process_indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();

        // W3-DEFER[api]: processIndi->isLocalizationTagUpToDate(calcAlgContext->getUsedProcessTagger()->getCurrentLocalizationTag())
        let localization_tag_up_to_date = false;
        if !localization_tag_up_to_date {
            // W3-DEFER[api]: processIndi = getUpToDateIndividual(processIndi,calcAlgContext);
            *process_indi = *process_indi;
            // W3-DEFER[api]: processIndi->isLocalizationTagUpToDate(...)
            let localization_tag_up_to_date2 = false;
            if !localization_tag_up_to_date2 {
                // W3-DEFER[api]: STATINC(INDINODELOCALIZEDLOADCOUNT,calcAlgContext);
                // W3-DEFER[api]: indiProcNodeVec = calcAlgContext->getProcessingDataBox()->getIndividualProcessNodeVector();
                let _indi_proc_node_vec =
                    calc_alg_context.processing_data_box_mut().individual_process_node_vector();
                // W3-DEFER[api]: localicedIndi = allocateAndConstructAndParameterize(taskMemMan, getUsedProcessContext());
                //                localicedIndi->initIndividualProcessNode(processIndi);
                //                indiProcNodeVec->setLocalData(localicedIndi->getIndividualNodeID(),localicedIndi);
                //                processIndi = localicedIndi;
                //                calcAlgContext->getUsedProcessTagger()->incLocalizationTag();
            }
        }

        // W3-DEFER[api]: conProDes = allocateAndConstruct(taskMemMan);
        //                conProPriority = getUsedConceptPriorityStrategy()->getPriorityForConcept(copyConProDes->getConceptDescriptor(),processIndi);
        //                conProDes->initCopy(copyConProDes);
        let con_pro_des: ConProcDescId = Id::NONE;
        // W3-DEFER[api]: conceptProcessingQueue = processIndi->getConceptProcessingQueue(true);
        let concept_processing_queue: ConceptProcessingQueueId = Id::NONE;
        self.insert_concept_process_descriptor_to_processing_queue(
            con_pro_des,
            concept_processing_queue,
            *process_indi,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptRestrictedToProcessingQueue`
    /// (the dispatch overload that reads `procRestriction->getPriorityOffset()`).
    pub fn add_concept_restricted_to_processing_queue(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        concept_processing_queue: ConceptProcessingQueueId,
        process_indi: NodeId,
        reapplied: bool,
        proc_restriction: ProcRestrictionHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut inserted_with_priority_offset = false;
        if proc_restriction != INVALID {
            // W3-DEFER[api]: priorityOffset = procRestriction->getPriorityOffset();
            let priority_offset: f64 = 0.0;
            inserted_with_priority_offset = true;
            self.add_concept_restricted_to_processing_queue_offset(
                concept_descriptor,
                dep_track_point,
                concept_processing_queue,
                process_indi,
                reapplied,
                proc_restriction,
                priority_offset,
                calc_alg_context,
            );
        }
        if !inserted_with_priority_offset {
            self.add_concept_restricted_to_processing_queue_offset(
                concept_descriptor,
                dep_track_point,
                concept_processing_queue,
                process_indi,
                reapplied,
                proc_restriction,
                0.0,
                calc_alg_context,
            );
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptRestrictedToProcessingQueue`
    /// (the `priorityOffset` overload).
    pub fn add_concept_restricted_to_processing_queue_offset(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        concept_processing_queue: ConceptProcessingQueueId,
        process_indi: NodeId,
        reapplied: bool,
        proc_restriction: ProcRestrictionHandle,
        priority_offset: f64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();

        if self.needs_processing_for_concept(concept_descriptor, dep_track_point, process_indi, calc_alg_context)
        {
            // W3-DEFER[api]: STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT,calcAlgContext);
            // W3-DEFER[api]: conProDes = allocateAndConstruct(taskMemMan);
            //                conProPriority = getUsedConceptPriorityStrategy()->getPriorityForConcept(conceptDescriptor,processIndi);
            //                conProPriority.addPriorityOffset(priorityOffset);
            //                conProDes->init(conceptDescriptor,conProPriority,reapplied,depTrackPoint,procRestriction);
            let con_pro_des: ConProcDescId = Id::NONE;
            self.insert_concept_process_descriptor_to_processing_queue(
                con_pro_des,
                concept_processing_queue,
                process_indi,
                calc_alg_context,
            );

            //propagateIndividualUnprocessed(processIndi,calcAlgContext);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptRestrictedFixedPriorityToProcessingQueue`.
    pub fn add_concept_restricted_fixed_priority_to_processing_queue(
        &mut self,
        concept_descriptor: ConDescId,
        dep_track_point: TrackPointId,
        concept_processing_queue: ConceptProcessingQueueId,
        process_indi: NodeId,
        reapplied: bool,
        proc_restriction: ProcRestrictionHandle,
        priority: f64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();

        // W3-DEFER[api]: STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT,calcAlgContext);
        // W3-DEFER[api]: conProDes = allocateAndConstruct(taskMemMan);
        //                CConceptProcessPriority conProPriority(priority);
        //                conProDes->init(conceptDescriptor,conProPriority,reapplied,depTrackPoint,procRestriction);
        let con_pro_des: ConProcDescId = Id::NONE;
        let _ = priority;
        self.insert_concept_process_descriptor_to_processing_queue(
            con_pro_des,
            concept_processing_queue,
            process_indi,
            calc_alg_context,
        );

        //propagateIndividualUnprocessed(processIndi,calcAlgContext);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToProcessingQueueBasedOnProcessingConcepts`.
    pub fn add_individual_to_processing_queue_based_on_processing_concepts(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut individual_inserted = false;
        let current_individual_node = calc_alg_context.base.current_individual_node();

        // W3-DEFER[api]: conProQueue = individual->getConceptProcessingQueue(false);
        let con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        // W3-DEFER[api]: individual->getLastAssertedDataLiteralLinker() / getAssertedDataLiteralLinker()
        //                getAssertionDataLinker() / getLastProcessedAssertionDataLinker()
        //                getAdditionalDataAssertionsLinker() / getLastProcessedAdditionalDataAssertionLinker()
        let last_asserted_data_literal: Cint64 = INVALID;
        let asserted_data_literal: Cint64 = INVALID;
        let assertion_data: Cint64 = INVALID;
        let last_processed_assertion_data: Cint64 = INVALID;
        let additional_data_assertions: Cint64 = INVALID;
        let last_processed_additional_data_assertion: Cint64 = INVALID;
        if con_pro_queue == Id::NONE
            || last_asserted_data_literal != asserted_data_literal
            || assertion_data != last_processed_assertion_data
            || additional_data_assertions != last_processed_additional_data_assertion
        {
            if !self.conf_current_individual_queuing && current_individual_node == individual {
                individual_inserted = true;
            } else {
                // W3-DEFER[api]: individual->isImmediatelyProcessingQueued()
                let is_immediately_processing_queued = false;
                if !is_immediately_processing_queued {
                    // W3-DEFER[api]: individual->setImmediatelyProcessingQueued(true);
                    let _un_pr_queue = calc_alg_context
                        .processing_data_box_mut()
                        .get_individual_immediately_processing_queue(true);
                    // W3-DEFER[api]: unPrQueue->insertIndiviudalProcessNode(individual);
                    individual_inserted = true;
                }
            }
        } else {
            // W3-DEFER[api]: !conProQueue->isEmpty()
            let con_pro_queue_empty = true;
            if !con_pro_queue_empty {
                // W3-DEFER[api]: conProQueue->getNextConceptProcessPriority(&conProPri)
                let has_next_concept_process_priority = false;
                // W3-DEFER[api]: conProPri.getPriority()
                let priority: f64 = 0.0;
                if has_next_concept_process_priority {
                    if priority >= IMMEDIATELY_PROCESS_PRIORITY as f64 {
                        if !self.conf_current_individual_queuing && current_individual_node == individual {
                            individual_inserted = true;
                        } else {
                            // W3-DEFER[api]: individual->isImmediatelyProcessingQueued()
                            let is_immediately_processing_queued = false;
                            if !is_immediately_processing_queued {
                                // W3-DEFER[api]: individual->setImmediatelyProcessingQueued(true);
                                let _un_pr_queue = calc_alg_context
                                    .processing_data_box_mut()
                                    .get_individual_immediately_processing_queue(true);
                                // W3-DEFER[api]: unPrQueue->insertIndiviudalProcessNode(individual);
                                individual_inserted = true;
                            }
                        }
                    } else if {
                        // W3-DEFER[api]: individual->isNominalIndividualNode()
                        let is_nominal = false;
                        // W3-DEFER[api]: individual->getIndividualNominalLevelOrAncestorDepth()
                        let nominal_level_or_anc_depth: Cint64 = 0;
                        (self.opt_det_exp_preporcessing || (is_nominal && nominal_level_or_anc_depth <= 0))
                            && priority >= DETERMINISTIC_PROCESS_PRIORITY as f64
                    } {
                        // W3-DEFER[api]: individual->isDeterministicExpandingProcessingQueued()
                        let is_deterministic_expanding_queued = false;
                        if !is_deterministic_expanding_queued {
                            // W3-DEFER[api]: individual->setDeterministicExpandingProcessingQueued(true);
                            let _un_pr_queue = calc_alg_context
                                .processing_data_box_mut()
                                .get_individual_depth_deterministic_expansion_preprocessing_queue(true);
                            // W3-DEFER[api]: unPrQueue->insertProcessIndiviudal(individual);
                            individual_inserted = true;
                        }
                    } else {
                        // W3-DEFER[api]: individual->isRegularDepthProcessingQueued()
                        let is_regular_depth_queued = false;
                        if !is_regular_depth_queued {
                            // W3-DEFER[api]: individual->setRegularDepthProcessingQueued(true);

                            // W3-DEFER[api]: individual->isNominalIndividualNode()
                            let is_nominal = false;
                            // W3-DEFER[api]: individual->getIndividualNominalLevelOrAncestorDepth()
                            let nominal_level_or_anc_depth: Cint64 = 0;
                            if is_nominal && nominal_level_or_anc_depth <= 0 {
                                if !calc_alg_context
                                    .processing_data_box_mut()
                                    .has_nominal_non_deterministic_processing_nodes_sorted()
                                {
                                    // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
                                    // W3-DEFER[api]: linker = allocateAndConstruct(taskMemMan); linker->initLinker(individual);
                                    //                processingDataBox->addSortedNominalNonDeterministicProcessingNodeLinker(linker);
                                } else {
                                    let _nominal_pro_queue = calc_alg_context
                                        .processing_data_box_mut()
                                        .get_nominal_processing_queue(true);
                                    // W3-DEFER[api]: nominalProQueue->insertProcessIndiviudal(individual);
                                }
                            } else {
                                let _in_depth_pro_queue = calc_alg_context
                                    .processing_data_box_mut()
                                    .get_individual_depth_processing_queue(true);
                                // W3-DEFER[api]: inDepthProQueue->insertProcessIndiviudal(individual);
                            }
                            individual_inserted = true;
                        }
                    }
                }
            }
        }
        individual_inserted
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addIndividualToProcessingQueue`.
    pub fn add_individual_to_processing_queue(
        &mut self,
        individual: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let mut individual_inserted = false;

        // W3-DEFER[api]: individual->isNominalIndividualNode() / isExtendedQueueProcessing()
        let is_nominal = false;
        let is_extended_queue_processing = false;

        if self.conf_depth_orientated_processing && !is_nominal && !is_extended_queue_processing {
            // W3-DEFER[api]: individual->isProcessingQueued()
            let is_processing_queued = false;
            if !is_processing_queued {
                let mut deterministic_preprocessing_queued = false;
                if self.opt_det_exp_preporcessing {
                    deterministic_preprocessing_queued = true;
                    // W3-DEFER[api]: conProQueue = individual->getConceptProcessingQueue(false);
                    let con_pro_queue: ConceptProcessingQueueId = Id::NONE;
                    if con_pro_queue == Id::NONE {
                        // W3-DEFER[api]: conProQueue->getNextConceptProcessPriority(&conProPri)
                        let has_next_concept_process_priority = false;
                        // W3-DEFER[api]: conProPri.getPriority()
                        let priority: f64 = 0.0;
                        if has_next_concept_process_priority {
                            if priority < DETERMINISTIC_PROCESS_PRIORITY as f64 {
                                deterministic_preprocessing_queued = false;
                            }
                        }
                    }
                }
                if deterministic_preprocessing_queued {
                    let _un_pr_queue = calc_alg_context
                        .processing_data_box_mut()
                        .get_individual_depth_first_deterministic_expansion_processing_queue(true);
                    // W3-DEFER[api]: unPrQueue->insertIndiviudalProcessNode(individual);
                } else {
                    let _depth_processing_queue = calc_alg_context
                        .processing_data_box_mut()
                        .get_individual_depth_first_processing_queue(true);
                    // W3-DEFER[api]: depthProcessingQueue->insertIndiviudalProcessNode(individual);
                }
                // W3-DEFER[api]: individual->setProcessingQueued(true);
                individual_inserted = true;
            }
        } else {
            let mut insert_individual = true;
            let mut individual_blocked = false;
            // W3-DEFER[api]: individual->hasPartialProcessingRestrictionFlags(PRFDIRECTBLOCKED)
            let has_direct_blocked = false;
            if insert_individual && has_direct_blocked {
                individual_blocked = true;
                // W3-DEFER[api]: !individual->hasPartialProcessingRestrictionFlags(PRFBLOCKINGRETESTDUEDIRECTMODIFIED | PRFBLOCKINGRETESTDUEBLOCKERMODIFIED)
                let has_retest_direct_or_blocker_modified = false;
                if !has_retest_direct_or_blocker_modified {
                    insert_individual = false;
                }
            }
            // (commented-out SATISFIABLECACHED / SIGNATUREBLOCKINGCACHED blocks omitted as in source)
            // W3-DEFER[api]: individual->hasPartialProcessingRestrictionFlags(PRFCOMPLETIONGRAPHCACHED)
            let has_completion_graph_cached = false;
            if insert_individual && has_completion_graph_cached {
                individual_blocked = true;
                // W3-DEFER[api]: !individual->hasPartialProcessingRestrictionFlags(PRFRETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED | PRFCOMPLETIONGRAPHCACHINGINVALIDATED | PRFCOMPLETIONGRAPHCACHINGINVALID)
                let has_completion_graph_retest_or_invalid = false;
                if !has_completion_graph_retest_or_invalid {
                    insert_individual = false;
                }
            }
            // W3-DEFER[api]: individual->hasPartialProcessingRestrictionFlags(PRFINDIRECTBLOCKED)
            let has_indirect_blocked = false;
            if insert_individual && has_indirect_blocked {
                individual_blocked = true;
                // W3-DEFER[api]: !individual->hasPartialProcessingRestrictionFlags(PRFBLOCKINGRETESTDUEINDIRECTBLOCKERLOSS)
                let has_retest_indirect_blocker_loss = false;
                if !has_retest_indirect_blocker_loss {
                    insert_individual = false;
                }
            }
            // W3-DEFER[api]: individual->hasPartialProcessingRestrictionFlags(PRFANCESTORSATISFIABLECACHED)
            let has_ancestor_satisfiable_cached = false;
            if insert_individual && has_ancestor_satisfiable_cached {
                individual_blocked = true;
                // W3-DEFER[api]: !individual->hasPartialProcessingRestrictionFlags(PRFANCESTORSATISFIABLECACHEDABOLISHED)
                let has_ancestor_satisfiable_cached_abolished = false;
                if !has_ancestor_satisfiable_cached_abolished {
                    insert_individual = false;
                }
            }
            // W3-DEFER[api]: individual->hasPartialProcessingRestrictionFlags(PRFANCESTORSIGNATUREBLOCKINGCACHED)
            let has_ancestor_signature_blocking_cached = false;
            if insert_individual && has_ancestor_signature_blocking_cached {
                individual_blocked = true;
                // W3-DEFER[api]: !individual->hasPartialProcessingRestrictionFlags(PRFANCESTORSIGNATUREBLOCKINGCACHEDABOLISHED)
                let has_ancestor_signature_blocking_cached_abolished = false;
                if !has_ancestor_signature_blocking_cached_abolished {
                    insert_individual = false;
                }
            }
            // W3-DEFER[api]: individual->hasPartialProcessingRestrictionFlags(PRFANCESTORSATURATIONBLOCKINGCACHED)
            let has_ancestor_saturation_blocking_cached = false;
            if insert_individual && has_ancestor_saturation_blocking_cached {
                individual_blocked = true;
                // W3-DEFER[api]: !individual->hasPartialProcessingRestrictionFlags(PRFANCESTORSATURATIONBLOCKINGCACHEDABOLISHED)
                let has_ancestor_saturation_blocking_cached_abolished = false;
                if !has_ancestor_saturation_blocking_cached_abolished {
                    insert_individual = false;
                }
            }
            // W3-DEFER[api]: individual->hasPartialProcessingRestrictionFlags(PRFSYNCHRONIZEDBACKEND)
            //                && individual->hasPartialProcessingRestrictionFlags(PRFSYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED)
            let has_synchronized_backend_succ_expansion_blocked = false;
            if insert_individual && has_synchronized_backend_succ_expansion_blocked {
                individual_blocked = true;
                insert_individual = false;
            }
            // W3-DEFER[api]: individual->isDelayedNominalProcessingQueued()
            let is_delayed_nominal_processing_queued = false;
            if insert_individual && is_delayed_nominal_processing_queued {
                individual_blocked = true;
                insert_individual = false;
            }

            if individual_blocked && insert_individual {
                if self.conf_late_blocking_resolving {
                    // W3-DEFER[api]: individual->isBlockedReactivationProcessingQueued()
                    let is_blocked_reactivation_processing_queued = false;
                    if !is_blocked_reactivation_processing_queued {
                        // W3-DEFER[api]: individual->setBlockedReactivationProcessingQueued(true);
                        let _block_react_pro_queue = calc_alg_context
                            .processing_data_box_mut()
                            .get_blocked_reactivation_processing_queue(true);
                        // W3-DEFER[api]: blockReactProQueue->insertProcessIndiviudal(individual);
                        individual_inserted = true;
                    }
                } else {
                    individual_inserted = self
                        .add_individual_to_processing_queue_based_on_processing_concepts(individual, calc_alg_context);
                    if !individual_inserted {
                        // W3-DEFER[api]: individual->isRegularDepthProcessingQueued()
                        let is_regular_depth_processing_queued = false;
                        if !is_regular_depth_processing_queued {
                            // W3-DEFER[api]: individual->setRegularDepthProcessingQueued(true);
                            let _in_depth_pro_queue = calc_alg_context
                                .processing_data_box_mut()
                                .get_individual_depth_processing_queue(true);
                            // W3-DEFER[api]: inDepthProQueue->insertProcessIndiviudal(individual);
                            individual_inserted = true;
                        }
                    }
                }
            }

            if !individual_blocked {
                individual_inserted = self
                    .add_individual_to_processing_queue_based_on_processing_concepts(individual, calc_alg_context);
            }
        }
        if individual_inserted {
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT,calcAlgContext);
        }
        individual_inserted
    }
}
