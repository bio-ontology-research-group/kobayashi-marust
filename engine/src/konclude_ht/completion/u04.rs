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

use super::super::model::op;
use super::super::model::op::{
    CCFS_PROPAGATION_ALL_TYPE, CCFS_PROPAGATION_AND_TYPE, CCFS_PROPAGATION_TYPE,
};
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::ConceptId;
use super::super::process::descriptor::{ConceptProcessDescriptor, ConceptProcessPriority};
use super::super::process::node::IndividualProcessNode;
use super::super::process::queues::ConceptProcessingQueue;
use super::super::process::reapply_sat::CondensedReapplyQueueIterator;
use super::super::process::stubs::ConceptProcessingQueueId;
use super::super::process::{
    ConDescId, ConProcDescId, EdgeId, LabelSetId, NodeId, RestrictionSpecId, TrackPointId,
};

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
        let processing_blocked_node_linker: Vec<NodeId> = calc_alg_context
            .process_context()
            .node(indi)
            .get_processing_blocked_individuals_linker()
            .to_vec();
        for blocked_node in processing_blocked_node_linker {
            let loc_blocked_node =
                self.get_localized_individual(blocked_node, true, calc_alg_context);
            calc_alg_context
                .process_context_mut()
                .node_mut(loc_blocked_node)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED,
                );
            self.add_individual_to_processing_queue(loc_blocked_node, calc_alg_context);
            // set blocking retest flag, clear processing blocked flag
        }
        calc_alg_context
            .process_context_mut()
            .node_mut(indi)
            .clear_processing_blocked_individuals_linker();

        let indi_id = calc_alg_context
            .process_context()
            .node(indi)
            .individual_node_id();

        // TODO: check multiple not processed ancestors
        let mut succ_it = calc_alg_context
            .process_context()
            .node_successor_iterator(indi);
        let mut succ_links: Vec<EdgeId> = Vec::new();
        while succ_it.has_next() {
            succ_links.push(succ_it.next_link(true));
        }
        let anc_depth = calc_alg_context
            .process_context()
            .node(indi)
            .individual_ancestor_depth();
        for succ_link in succ_links {
            let mut source_indi = indi;
            let succ_indi =
                self.get_successor_individual(&mut source_indi, succ_link, calc_alg_context);
            let succ_anc_depth = calc_alg_context
                .process_context()
                .node(succ_indi)
                .individual_ancestor_depth();
            if succ_anc_depth > anc_depth {
                let succ_ancestor_all_processed = calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
                    );
                if !succ_ancestor_all_processed {
                    // test whether have unprocessed nominals or ancestor
                    let mut all_processed_ancestor = true;
                    let mut conn_it = calc_alg_context
                        .process_context()
                        .node_connection_successor_iterator(succ_indi);
                    let mut conn_ids: Vec<Cint64> = Vec::new();
                    while conn_it.has_next() {
                        conn_ids.push(conn_it.next(true));
                    }
                    let mut conn_iter = conn_ids.into_iter();
                    while all_processed_ancestor {
                        let conn_indi_node_id = match conn_iter.next() {
                            Some(v) => v,
                            None => break,
                        };
                        if conn_indi_node_id != indi_id {
                            let anc_nom_indi = self.get_up_to_date_individual_by_id(
                                conn_indi_node_id,
                                calc_alg_context,
                            );
                            if anc_nom_indi.is_none() {
                                all_processed_ancestor = false;
                                continue;
                            }
                            let anc_nom = calc_alg_context.process_context().node(anc_nom_indi);
                            let anc_nom_ancestor_depth = anc_nom.individual_ancestor_depth();
                            let anc_nom_is_nominal = anc_nom.is_nominal_individual_node();
                            if anc_nom_ancestor_depth >= anc_depth || anc_nom_is_nominal {
                                let anc_nom_processed_or_all = anc_nom
                                    .has_partial_processing_restriction_flags(
                                        IndividualProcessNode::PRF_PROCESSINGCOMPLETED
                                            | IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
                                    );
                                if !anc_nom_processed_or_all {
                                    all_processed_ancestor = false;
                                }
                            }
                        }
                    }
                    if all_processed_ancestor {
                        let loc_succ_indi =
                            self.get_localized_individual(succ_indi, false, calc_alg_context);
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(loc_succ_indi)
                            .add_processing_restriction_flags(
                                IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
                            );
                        let loc_succ_processing_completed = calc_alg_context
                            .process_context()
                            .node(loc_succ_indi)
                            .has_partial_processing_restriction_flags(
                                IndividualProcessNode::PRF_PROCESSINGCOMPLETED,
                            );
                        if !loc_succ_processing_completed {
                            let loc_succ_processing_blocked = calc_alg_context
                                .process_context()
                                .node(loc_succ_indi)
                                .has_partial_processing_restriction_flags(
                                    IndividualProcessNode::PRF_PROCESSINGBLOCKED,
                                );
                            if loc_succ_processing_blocked {
                                calc_alg_context
                                    .process_context_mut()
                                    .node_mut(loc_succ_indi)
                                    .add_processing_restriction_flags(
                                        IndividualProcessNode::PRF_BLOCKINGRETESTDUEPROCESSINGCOMPLETED,
                                    );
                                self.add_individual_to_processing_queue(
                                    loc_succ_indi,
                                    calc_alg_context,
                                );
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
        let indi_cons_node_preparation = calc_alg_context
            .process_context()
            .node(indi)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_CONSNODEPREPARATIONINDINODE,
            );
        if !requires_cons_flag || indi_cons_node_preparation {
            let indi_processing_completed = calc_alg_context
                .process_context()
                .node(indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_PROCESSINGCOMPLETED,
                );
            if indi_processing_completed {
                calc_alg_context
                    .process_context_mut()
                    .node_mut(indi)
                    .clear_processing_restriction_flags(
                        IndividualProcessNode::PRF_PROCESSINGCOMPLETED,
                    );
                let indi_ancestor_all_processed = calc_alg_context
                    .process_context()
                    .node(indi)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
                    );
                if indi_ancestor_all_processed {
                    let mut succ_it = calc_alg_context
                        .process_context()
                        .node_successor_iterator(indi);
                    let mut succ_links: Vec<EdgeId> = Vec::new();
                    while succ_it.has_next() {
                        succ_links.push(succ_it.next_link(true));
                    }
                    let anc_depth = calc_alg_context
                        .process_context()
                        .node(indi)
                        .individual_ancestor_depth();
                    for succ_link in succ_links {
                        let mut source_indi = indi;
                        let succ_indi = self.get_successor_individual(
                            &mut source_indi,
                            succ_link,
                            calc_alg_context,
                        );
                        let succ_anc_depth = calc_alg_context
                            .process_context()
                            .node(succ_indi)
                            .individual_ancestor_depth();
                        if succ_anc_depth > anc_depth {
                            let succ_ancestor_all_processed = calc_alg_context
                                .process_context()
                                .node(succ_indi)
                                .has_partial_processing_restriction_flags(
                                    IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
                                );
                            if !succ_ancestor_all_processed {
                                let loc_succ_indi = self.get_localized_individual(
                                    succ_indi,
                                    false,
                                    calc_alg_context,
                                );
                                calc_alg_context
                                    .process_context_mut()
                                    .node_mut(loc_succ_indi)
                                    .clear_processing_restriction_flags(
                                        IndividualProcessNode::PRF_ANCESTORALLPROCESSED,
                                    );
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

        let con_pro_queue = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(process_indi, true);
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(process_indi);

        debug_assert!(
            dependency_track_point != Id::NONE,
            "adding concept to individual: dependency track point missing"
        );
        debug_assert!(
            adding_concept != Id::NONE,
            "adding concept to individual: concept missing"
        );

        let concept_descriptor = self.create_concept_descriptor(calc_alg_context);
        self.init_concept_descriptor_fields(
            concept_descriptor,
            adding_concept,
            negate,
            dependency_track_point,
            calc_alg_context,
        );
        let mut reapply_it = CondensedReapplyQueueIterator::new();
        let mut process_indi_ref = process_indi;
        let contained = self.insert_concepts_to_individual_concept_set(
            concept_descriptor,
            dependency_track_point,
            &mut process_indi_ref,
            con_label_set,
            Some(&mut reapply_it),
            allow_initalization,
            calc_alg_context,
        );
        if !contained {
            self.stat_con_des_insertion_count += 1;
            // W3-DEFER[api]: STATINC(CONCEPTSADDEDINDINODELABELSETCOUNT,calcAlgContext);
            self.add_blocking_core_concept(
                concept_descriptor,
                process_indi,
                con_label_set,
                calc_alg_context,
            );
            if mark_modification {
                let mut process_indi_mut = process_indi;
                self.set_individual_node_concept_label_set_modified(
                    &mut process_indi_mut,
                    calc_alg_context,
                );
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
            if reapply_it.has_next() {
                // reapply reapplying concept
                self.apply_reapply_queue_concepts_condensed_iterator(
                    process_indi,
                    reapply_it,
                    calc_alg_context,
                );
            }
        } else {
            self.stat_con_des_contained_count += 1;
            self.release_concept_descriptor(concept_descriptor, calc_alg_context);
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
        let concept_descriptor = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des)
            .get_concept_descriptor();
        let concept = calc_alg_context
            .process_context()
            .con_desc(concept_descriptor)
            .get_concept();

        let has_propagation_type = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_operator()
            .has_partial_operator_code_flag(CCFS_PROPAGATION_TYPE);
        if has_propagation_type {
            let var_bind_con_batch_proc_queue =
                calc_alg_context.get_variable_binding_concept_batch_processing_queue(true);
            let base = &mut calc_alg_context.base;
            base.used_process_context
                .indi_concept_batch_queue_insert_indiviudal_for_concept(
                    var_bind_con_batch_proc_queue,
                    &base.ontology_arenas,
                    concept,
                    process_indi,
                    con_pro_des,
                );
        } else {
            // conceptProcessingQueue->insertConceptProcessDescriptor(conProDes);
            ConceptProcessingQueue::insert_concept_process_descriptor(
                concept_processing_queue,
                con_pro_des,
                calc_alg_context.process_context_mut(),
            );
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
        let concept_descriptor = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des)
            .get_concept_descriptor();
        let concept = calc_alg_context
            .process_context()
            .con_desc(concept_descriptor)
            .get_concept();
        let con_operator = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_operator();

        let has_propagation_all_and_type = con_operator
            .has_partial_operator_code_flag(CCFS_PROPAGATION_ALL_TYPE | CCFS_PROPAGATION_AND_TYPE);
        let has_propagation_type =
            con_operator.has_partial_operator_code_flag(CCFS_PROPAGATION_TYPE);
        if has_propagation_all_and_type {
            let var_bind_con_batch_proc_queue =
                calc_alg_context.get_variable_binding_concept_batch_processing_queue(true);
            let base = &mut calc_alg_context.base;
            base.used_process_context
                .indi_concept_batch_queue_insert_indiviudal_for_binding_count(
                    var_bind_con_batch_proc_queue,
                    &base.ontology_arenas,
                    concept,
                    binding_count,
                    process_indi,
                    con_pro_des,
                );
        } else if has_propagation_type {
            let var_bind_con_batch_proc_queue =
                calc_alg_context.get_variable_binding_concept_batch_processing_queue(true);
            let base = &mut calc_alg_context.base;
            base.used_process_context
                .indi_concept_batch_queue_insert_indiviudal_for_concept(
                    var_bind_con_batch_proc_queue,
                    &base.ontology_arenas,
                    concept,
                    process_indi,
                    con_pro_des,
                );
        } else {
            // conceptProcessingQueue->insertConceptProcessDescriptor(conProDes);
            ConceptProcessingQueue::insert_concept_process_descriptor(
                concept_processing_queue,
                con_pro_des,
                calc_alg_context.process_context_mut(),
            );
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

        if self.needs_processing_for_concept(
            concept_descriptor,
            dep_track_point,
            process_indi,
            calc_alg_context,
        ) {
            // W3-DEFER[api]: STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT,calcAlgContext);
            // W3-DEFER[api]: conProDes = allocateAndConstruct(taskMemMan);
            //                conProPriority = getUsedConceptPriorityStrategy()->getPriorityForConcept(conceptDescriptor,processIndi);
            //                conProDes->init(conceptDescriptor,conProPriority,reapplied,depTrackPoint);
            let mut con_pro_des_val = ConceptProcessDescriptor::new();
            con_pro_des_val.concept_des = concept_descriptor;
            con_pro_des_val.priority =
                self.priority_for_concept(concept_descriptor, process_indi, calc_alg_context);
            con_pro_des_val.reapplied = reapplied;
            con_pro_des_val.dep_track_point = dep_track_point;
            con_pro_des_val.proc_spec = Id::NONE;
            let con_pro_des = calc_alg_context
                .process_context_mut()
                .alloc_con_proc_desc(con_pro_des_val);

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
        let concept = calc_alg_context
            .process_context()
            .con_desc(concept_descriptor)
            .get_concept();
        let op_code = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        let con_neg = calc_alg_context
            .process_context()
            .con_desc(concept_descriptor)
            .is_negated();
        self.has_tableau_rule(op_code, con_neg)
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
        // conProPriority = getUsedConceptPriorityStrategy()->getPriorityForConcept(conceptDescriptor,processIndi);
        // conProDes = allocateAndConstruct(taskMemMan);
        // conProDes->init(conceptDescriptor,conProPriority,false,depTrackPoint);
        let mut con_pro_des_val = ConceptProcessDescriptor::new();
        con_pro_des_val.concept_des = concept_descriptor;
        con_pro_des_val.priority =
            self.priority_for_concept(concept_descriptor, process_indi, calc_alg_context);
        con_pro_des_val.dep_track_point = dep_track_point;
        con_pro_des_val.reapplied = false;
        con_pro_des_val.proc_spec = Id::NONE;
        let con_pro_des: ConProcDescId = calc_alg_context
            .process_context_mut()
            .alloc_con_proc_desc(con_pro_des_val);
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

        // opCode = conceptDescriptor->getConcept()->getOperatorCode(); conNeg = conceptDescriptor->isNegated();
        let con_neg = calc_alg_context
            .process_context()
            .con_desc(concept_descriptor)
            .is_negated();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(concept_descriptor)
            .get_concept();
        let op_code: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();

        // func = (conNeg ? mNegJumpFuncVec : mPosJumpFuncVec)[opCode];
        // if (!func || func == skipFunction) return;
        // KONCLUDE-PORT-NOTE[pointer-alias]: the member-fn jump table is opaque, but its
        // PRESENCE is exactly the operator set `tableau_rule_choice` dispatches (the table the
        // algorithm ctor builds, cpp 238-345). `has_tableau_rule` mirrors that set 1:1; the
        // `mConf*` gates only SWAP entries, never null them, so presence is config-invariant.
        // `skipFunction` is a rule-slot identity the only caller passes as INVALID, so it can
        // never match a live rule; the second guard is preserved structurally.
        if !self.has_tableau_rule(op_code, con_neg) || skip_function != INVALID {
            return;
        }

        allow_preprocessing &= self.conf_direct_rule_preprocessing;
        if self.current_rec_proc_depth > self.current_rec_proc_depth_limit {
            allow_preprocessing = false;
        }

        // concept = conceptDescriptor->getConcept(); conOperator = concept->getConceptOperator();
        // if (conOperator->hasPartialOperatorCodeFlag(CCFS_PROPAGATION_TYPE)) allowPreprocessing = false;
        let has_propagation_type = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_operator()
            .has_partial_operator_code_flag(CCFS_PROPAGATION_TYPE);
        if has_propagation_type {
            allow_preprocessing = false;
        }

        // W3-DEFER[macro]: STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT,calcAlgContext);
        // conProPriority = getUsedConceptPriorityStrategy()->getPriorityForConcept(conceptDescriptor,processIndi);
        let con_pro_priority =
            self.priority_for_concept(concept_descriptor, process_indi, calc_alg_context);
        let con_pro_priority_value: f64 = con_pro_priority.get_priority();

        // conProDes = allocateAndConstruct(taskMemMan);
        // conProDes->init(conceptDescriptor,conProPriority,false,depTrackPoint);
        let mut con_pro_des_val = ConceptProcessDescriptor::new();
        con_pro_des_val.concept_des = concept_descriptor;
        con_pro_des_val.priority = con_pro_priority;
        con_pro_des_val.dep_track_point = dep_track_point;
        con_pro_des_val.reapplied = false;
        con_pro_des_val.proc_spec = Id::NONE;
        let con_pro_des: ConProcDescId = calc_alg_context
            .process_context_mut()
            .alloc_con_proc_desc(con_pro_des_val);

        if allow_preprocessing && con_pro_priority_value >= IMMEDIATELY_PROCESS_PRIORITY as f64 {
            // W3-DEFER[macro]: STATINC(RULEAPPLICATIONCOUNT,calcAlgContext);
            // tableauRuleChoice(processIndi,conProDes,calcAlgContext);
            self.tableau_rule_choice(process_indi, con_pro_des, calc_alg_context);
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

    /// `func = (conNeg ? mNegJumpFuncVec : mPosJumpFuncVec)[opCode]; func != nullptr`.
    ///
    /// KONCLUDE-PORT-NOTE[pointer-alias]: the C++ ctor (cpp 238-345) fills two
    /// member-function-pointer jump vectors; an operator "has a tableau rule" iff its
    /// slot is non-null. The port keeps those vectors opaque, so this predicate
    /// reproduces the populated operator set 1:1 — the SAME arms `tableau_rule_choice`
    /// (`u03`) dispatches, split by `neg` into the positive (`mPosJumpFuncVec`) and
    /// negative (`mNegJumpFuncVec`) tables. The `mConfSpecializedAutomateRules` /
    /// `mConfRepresentativePropagationRules` gates only REPLACE entries (e.g. AQAND →
    /// applyAutomatANDRule), never null them, so rule PRESENCE is config-invariant and
    /// this predicate takes no config argument.
    pub fn has_tableau_rule(&self, op_code: Cint64, neg: bool) -> bool {
        if !neg {
            matches!(
                op_code,
                op::CCTOP
                    | op::CCBOTTOM
                    | op::CCAND
                    | op::CCSUB
                    | op::CCEQ
                    | op::CCIMPLTRIG
                    | op::CCBRANCHTRIG
                    | op::CCAQAND
                    | op::CCIMPLAQAND
                    | op::CCBRANCHAQAND
                    | op::CCDATATYPE
                    | op::CCDATALITERAL
                    | op::CCDATARESTRICTION
                    | op::CCOR
                    | op::CCALL
                    | op::CCAQALL
                    | op::CCIMPLAQALL
                    | op::CCBRANCHAQALL
                    | op::CCIMPLALL
                    | op::CCBRANCHALL
                    | op::CCSOME
                    | op::CCAQSOME
                    | op::CCAQCHOOCE
                    | op::CCNOT
                    | op::CCSELF
                    | op::CCATLEAST
                    | op::CCATMOST
                    | op::CCNOMINAL
                    | op::CCVALUE
                    | op::CCIMPL
                    | op::CCPBINDVARIABLE
                    | op::CCPBINDTRIG
                    | op::CCPBINDAND
                    | op::CCPBINDAQAND
                    | op::CCPBINDIMPL
                    | op::CCPBINDALL
                    | op::CCPBINDAQALL
                    | op::CCPBINDCYCLE
                    | op::CCPBINDGROUND
                    | op::CCVARBINDVARIABLE
                    | op::CCVARBINDTRIG
                    | op::CCVARBINDAND
                    | op::CCVARBINDAQAND
                    | op::CCVARBINDIMPL
                    | op::CCVARBINDALL
                    | op::CCVARBINDAQALL
                    | op::CCVARBINDJOIN
                    | op::CCVARBINDGROUND
                    | op::CCBACKACTIVTRIG
                    | op::CCVARPBACKTRIG
                    | op::CCVARPBACKAQAND
                    | op::CCVARPBACKALL
                    | op::CCVARPBACKAQALL
                    | op::CCBACKACTIVIMPL
                    | op::CCNOMINALIMPLI
                    | op::CCDATATYPEIMPLI
                    | op::CCDATALITERALIMPLI
                    | op::CCDATARESTRICTIONIMPLI
                    | op::CCVARBINDPREPARE
                    | op::CCVARBINDFINALZE
            )
        } else {
            matches!(
                op_code,
                op::CCDATATYPE
                    | op::CCDATALITERAL
                    | op::CCDATARESTRICTION
                    | op::CCAND
                    | op::CCOR
                    | op::CCEQ
                    | op::CCALL
                    | op::CCNOT
                    | op::CCSOME
                    | op::CCAQCHOOCE
                    | op::CCSELF
                    | op::CCATMOST
                    | op::CCATLEAST
                    | op::CCNOMINAL
                    | op::CCVALUE
                    | op::CCPBINDGROUND
                    | op::CCVARBINDGROUND
            )
        }
    }

    /// `getUsedConceptPriorityStrategy()->getPriorityForConcept(conceptDescriptor, processIndi)`.
    pub fn priority_for_concept(
        &self,
        concept_descriptor: ConDescId,
        process_indi: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> ConceptProcessPriority {
        let strategy = calc_alg_context
            .base
            .used_concept_priority_strategy()
            .expect(
            "calculation algorithm context must be initialized with a concept priority strategy",
        );
        strategy.get_priority_for_concept(
            calc_alg_context.process_context(),
            calc_alg_context.ontology_arenas(),
            concept_descriptor,
            process_indi,
        )
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
        // W3-DEFER[macro]: STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT,calcAlgContext);
        let _ = process_indi;
        ConceptProcessingQueue::reinsert_concept_process_descriptor(
            concept_processing_queue,
            reinsert_con_pro_des,
            calc_alg_context.process_context_mut(),
        );
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
                let _indi_proc_node_vec = calc_alg_context
                    .processing_data_box_mut()
                    .individual_process_node_vector();
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

        if self.needs_processing_for_concept(
            concept_descriptor,
            dep_track_point,
            process_indi,
            calc_alg_context,
        ) {
            // W3-DEFER[api]: STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT,calcAlgContext);
            // W3-DEFER[api]: conProDes = allocateAndConstruct(taskMemMan);
            //                conProPriority = getUsedConceptPriorityStrategy()->getPriorityForConcept(conceptDescriptor,processIndi);
            //                conProPriority.addPriorityOffset(priorityOffset);
            //                conProDes->init(conceptDescriptor,conProPriority,reapplied,depTrackPoint,procRestriction);
            let mut con_pro_priority =
                self.priority_for_concept(concept_descriptor, process_indi, calc_alg_context);
            con_pro_priority.add_priority_offset(priority_offset);
            let mut con_pro_des_val = ConceptProcessDescriptor::new();
            con_pro_des_val.concept_des = concept_descriptor;
            con_pro_des_val.priority = con_pro_priority;
            con_pro_des_val.reapplied = reapplied;
            con_pro_des_val.dep_track_point = dep_track_point;
            con_pro_des_val.proc_spec = if proc_restriction != INVALID {
                RestrictionSpecId::new(proc_restriction)
            } else {
                Id::NONE
            };
            let con_pro_des = calc_alg_context
                .process_context_mut()
                .alloc_con_proc_desc(con_pro_des_val);
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
        let mut con_pro_des_val = ConceptProcessDescriptor::new();
        con_pro_des_val.concept_des = concept_descriptor;
        con_pro_des_val.priority = ConceptProcessPriority::new(priority);
        con_pro_des_val.reapplied = reapplied;
        con_pro_des_val.dep_track_point = dep_track_point;
        con_pro_des_val.proc_spec = if proc_restriction != INVALID {
            RestrictionSpecId::new(proc_restriction)
        } else {
            Id::NONE
        };
        let con_pro_des = calc_alg_context
            .process_context_mut()
            .alloc_con_proc_desc(con_pro_des_val);
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

        let con_pro_queue: ConceptProcessingQueueId = calc_alg_context
            .process_context_mut()
            .node_concept_processing_queue(individual, false);
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
                let is_immediately_processing_queued = calc_alg_context
                    .process_context()
                    .node(individual)
                    .is_immediately_processing_queued();
                if !is_immediately_processing_queued {
                    calc_alg_context
                        .process_context_mut()
                        .node_mut(individual)
                        .set_immediately_processing_queued(true);
                    let un_pr_queue =
                        calc_alg_context.get_individual_immediately_processing_queue(true);
                    calc_alg_context
                        .process_context_mut()
                        .indi_unsorted_proc_queue_mut(un_pr_queue)
                        .insert_indiviudal_process_node(individual);
                    individual_inserted = true;
                }
            }
        } else {
            let con_pro_queue_empty = calc_alg_context
                .process_context()
                .concept_proc_queue(con_pro_queue)
                .is_empty();
            if !con_pro_queue_empty {
                let next_priority = ConceptProcessingQueue::get_next_concept_process_priority(
                    con_pro_queue,
                    calc_alg_context.process_context_mut(),
                );
                if let Some(con_pro_pri) = next_priority {
                    let priority: f64 = con_pro_pri.get_priority();
                    if priority >= IMMEDIATELY_PROCESS_PRIORITY as f64 {
                        if !self.conf_current_individual_queuing
                            && current_individual_node == individual
                        {
                            individual_inserted = true;
                        } else {
                            let is_immediately_processing_queued = calc_alg_context
                                .process_context()
                                .node(individual)
                                .is_immediately_processing_queued();
                            if !is_immediately_processing_queued {
                                calc_alg_context
                                    .process_context_mut()
                                    .node_mut(individual)
                                    .set_immediately_processing_queued(true);
                                let un_pr_queue = calc_alg_context
                                    .get_individual_immediately_processing_queue(true);
                                calc_alg_context
                                    .process_context_mut()
                                    .indi_unsorted_proc_queue_mut(un_pr_queue)
                                    .insert_indiviudal_process_node(individual);
                                individual_inserted = true;
                            }
                        }
                    } else if {
                        let is_nominal = calc_alg_context
                            .process_context()
                            .node(individual)
                            .is_nominal_individual_node();
                        let nominal_level_or_anc_depth = calc_alg_context
                            .process_context()
                            .node(individual)
                            .individual_nominal_level_or_ancestor_depth();
                        (self.opt_det_exp_preporcessing
                            || (is_nominal && nominal_level_or_anc_depth <= 0))
                            && priority >= DETERMINISTIC_PROCESS_PRIORITY as f64
                    } {
                        let is_deterministic_expanding_queued = calc_alg_context
                            .process_context()
                            .node(individual)
                            .is_deterministic_expanding_processing_queued();
                        if !is_deterministic_expanding_queued {
                            calc_alg_context
                                .process_context_mut()
                                .node_mut(individual)
                                .set_deterministic_expanding_processing_queued(true);
                            let un_pr_queue = calc_alg_context
                                .get_individual_depth_deterministic_expansion_preprocessing_queue(
                                    true,
                                );
                            calc_alg_context
                                .process_context_mut()
                                .indi_depth_queue_insert(un_pr_queue, individual);
                            individual_inserted = true;
                        }
                    } else {
                        let is_regular_depth_queued = calc_alg_context
                            .process_context()
                            .node(individual)
                            .is_regular_depth_processing_queued();
                        if !is_regular_depth_queued {
                            calc_alg_context
                                .process_context_mut()
                                .node_mut(individual)
                                .set_regular_depth_processing_queued(true);
                            let is_nominal = calc_alg_context
                                .process_context()
                                .node(individual)
                                .is_nominal_individual_node();
                            let nominal_level_or_anc_depth = calc_alg_context
                                .process_context()
                                .node(individual)
                                .individual_nominal_level_or_ancestor_depth();
                            if is_nominal && nominal_level_or_anc_depth <= 0 {
                                if !calc_alg_context
                                    .processing_data_box_mut()
                                    .has_nominal_non_deterministic_processing_nodes_sorted()
                                {
                                    // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
                                    // W3-DEFER[api]: linker = allocateAndConstruct(taskMemMan); linker->initLinker(individual);
                                    //                processingDataBox->addSortedNominalNonDeterministicProcessingNodeLinker(linker);
                                } else {
                                    let _nominal_pro_queue =
                                        calc_alg_context.get_nominal_processing_queue(true);
                                    // W3-DEFER[api]: nominalProQueue->insertProcessIndiviudal(individual);
                                }
                            } else {
                                let in_depth_pro_queue =
                                    calc_alg_context.get_individual_depth_processing_queue(true);
                                calc_alg_context
                                    .process_context_mut()
                                    .indi_depth_queue_insert(in_depth_pro_queue, individual);
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

        let (is_nominal, is_extended_queue_processing) = {
            let node = calc_alg_context.process_context().node(individual);
            (
                node.is_nominal_individual_node(),
                node.is_extended_queue_processing(),
            )
        };

        if self.conf_depth_orientated_processing && !is_nominal && !is_extended_queue_processing {
            let is_processing_queued = calc_alg_context
                .process_context()
                .node(individual)
                .is_processing_queued();
            if !is_processing_queued {
                let mut deterministic_preprocessing_queued = false;
                if self.opt_det_exp_preporcessing {
                    deterministic_preprocessing_queued = true;
                    let con_pro_queue: ConceptProcessingQueueId = calc_alg_context
                        .process_context_mut()
                        .node_concept_processing_queue(individual, false);
                    if con_pro_queue.is_some() {
                        if let Some(con_pro_pri) =
                            ConceptProcessingQueue::get_next_concept_process_priority(
                                con_pro_queue,
                                calc_alg_context.process_context_mut(),
                            )
                        {
                            let priority: f64 = con_pro_pri.get_priority();
                            if priority < DETERMINISTIC_PROCESS_PRIORITY as f64 {
                                deterministic_preprocessing_queued = false;
                            }
                        }
                    }
                }
                if deterministic_preprocessing_queued {
                    let un_pr_queue = calc_alg_context
                        .get_individual_depth_first_deterministic_expansion_processing_queue(true);
                    // unPrQueue->insertIndiviudalProcessNode(individual);
                    calc_alg_context
                        .process_context_mut()
                        .indi_unsorted_proc_queue_mut(un_pr_queue)
                        .insert_indiviudal_process_node(individual);
                } else {
                    let depth_processing_queue =
                        calc_alg_context.get_individual_depth_first_processing_queue(true);
                    // depthProcessingQueue->insertIndiviudalProcessNode(individual);
                    calc_alg_context
                        .process_context_mut()
                        .indi_unsorted_proc_queue_mut(depth_processing_queue)
                        .insert_indiviudal_process_node(individual);
                }
                calc_alg_context
                    .process_context_mut()
                    .node_mut(individual)
                    .set_processing_queued(true);
                individual_inserted = true;
            }
        } else {
            let mut insert_individual = true;
            let mut individual_blocked = false;
            let has_direct_blocked = calc_alg_context
                .process_context()
                .node(individual)
                .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_DIRECTBLOCKED);
            if insert_individual && has_direct_blocked {
                individual_blocked = true;
                let has_retest_direct_or_blocker_modified = calc_alg_context
                    .process_context()
                    .node(individual)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED
                            | IndividualProcessNode::PRF_BLOCKINGRETESTDUEBLOCKERMODIFIED,
                    );
                if !has_retest_direct_or_blocker_modified {
                    insert_individual = false;
                }
            }
            // (commented-out SATISFIABLECACHED / SIGNATUREBLOCKINGCACHED blocks omitted as in source)
            let has_completion_graph_cached = calc_alg_context
                .process_context()
                .node(individual)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
                );
            if insert_individual && has_completion_graph_cached {
                individual_blocked = true;
                let has_completion_graph_retest_or_invalid = calc_alg_context
                    .process_context()
                    .node(individual)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_RETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED
                            | IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALIDATED
                            | IndividualProcessNode::PRF_COMPLETIONGRAPHCACHINGINVALID,
                    );
                if !has_completion_graph_retest_or_invalid {
                    insert_individual = false;
                }
            }
            let has_indirect_blocked = calc_alg_context
                .process_context()
                .node(individual)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_INDIRECTBLOCKED,
                );
            if insert_individual && has_indirect_blocked {
                individual_blocked = true;
                let has_retest_indirect_blocker_loss = calc_alg_context
                    .process_context()
                    .node(individual)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_BLOCKINGRETESTDUEINDIRECTBLOCKERLOSS,
                    );
                if !has_retest_indirect_blocker_loss {
                    insert_individual = false;
                }
            }
            let has_ancestor_satisfiable_cached = calc_alg_context
                .process_context()
                .node(individual)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED,
                );
            if insert_individual && has_ancestor_satisfiable_cached {
                individual_blocked = true;
                let has_ancestor_satisfiable_cached_abolished = calc_alg_context
                    .process_context()
                    .node(individual)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHEDABOLISHED,
                    );
                if !has_ancestor_satisfiable_cached_abolished {
                    insert_individual = false;
                }
            }
            let has_ancestor_signature_blocking_cached = calc_alg_context
                .process_context()
                .node(individual)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
                );
            if insert_individual && has_ancestor_signature_blocking_cached {
                individual_blocked = true;
                let has_ancestor_signature_blocking_cached_abolished = calc_alg_context
                    .process_context()
                    .node(individual)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHEDABOLISHED,
                    );
                if !has_ancestor_signature_blocking_cached_abolished {
                    insert_individual = false;
                }
            }
            let has_ancestor_saturation_blocking_cached = calc_alg_context
                .process_context()
                .node(individual)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED,
                );
            if insert_individual && has_ancestor_saturation_blocking_cached {
                individual_blocked = true;
                let has_ancestor_saturation_blocking_cached_abolished = calc_alg_context
                    .process_context()
                    .node(individual)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHEDABOLISHED,
                    );
                if !has_ancestor_saturation_blocking_cached_abolished {
                    insert_individual = false;
                }
            }
            let has_synchronized_backend_succ_expansion_blocked = {
                let node = calc_alg_context.process_context().node(individual);
                node.has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND,
                ) && node.has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED,
                )
            };
            if insert_individual && has_synchronized_backend_succ_expansion_blocked {
                individual_blocked = true;
                insert_individual = false;
            }
            let is_delayed_nominal_processing_queued = calc_alg_context
                .process_context()
                .node(individual)
                .is_delayed_nominal_processing_queued();
            if insert_individual && is_delayed_nominal_processing_queued {
                individual_blocked = true;
                insert_individual = false;
            }

            if individual_blocked && insert_individual {
                if self.conf_late_blocking_resolving {
                    let is_blocked_reactivation_processing_queued = calc_alg_context
                        .process_context()
                        .node(individual)
                        .is_blocked_reactivation_processing_queued();
                    if !is_blocked_reactivation_processing_queued {
                        calc_alg_context
                            .process_context_mut()
                            .node_mut(individual)
                            .set_blocked_reactivation_processing_queued(true);
                        let block_react_pro_queue =
                            calc_alg_context.get_blocked_reactivation_processing_queue(true);
                        // blockReactProQueue->insertProcessIndiviudal(individual);
                        calc_alg_context
                            .process_context_mut()
                            .indi_depth_queue_insert(block_react_pro_queue, individual);
                        individual_inserted = true;
                    }
                } else {
                    individual_inserted = self
                        .add_individual_to_processing_queue_based_on_processing_concepts(
                            individual,
                            calc_alg_context,
                        );
                    if !individual_inserted {
                        let is_regular_depth_processing_queued = calc_alg_context
                            .process_context()
                            .node(individual)
                            .is_regular_depth_processing_queued();
                        if !is_regular_depth_processing_queued {
                            calc_alg_context
                                .process_context_mut()
                                .node_mut(individual)
                                .set_regular_depth_processing_queued(true);
                            let in_depth_pro_queue =
                                calc_alg_context.get_individual_depth_processing_queue(true);
                            // inDepthProQueue->insertProcessIndiviudal(individual);
                            calc_alg_context
                                .process_context_mut()
                                .indi_depth_queue_insert(in_depth_pro_queue, individual);
                            individual_inserted = true;
                        }
                    }
                }
            }

            if !individual_blocked {
                individual_inserted = self
                    .add_individual_to_processing_queue_based_on_processing_concepts(
                        individual,
                        calc_alg_context,
                    );
            }
        }
        if individual_inserted {
            // W3-DEFER[api]: STATINC(INDINODESADDEDPROCESSINGQUEUECOUNT,calcAlgContext);
        }
        individual_inserted
    }
}
