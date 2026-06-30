//! `completion::u06` — W3 method-batch unit #6 (Expansion rules family).
//!
//! Ports 8 methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (the variable-binding / representative-propagation expansion rules used by the
//! answering-propagation machinery), per `manifest/01-completion-methods.md`
//! Unit 6 (cpp 11161–12675):
//!   - `applyREPRESENTATIVEANDRule`        [11161-11232]
//!   - `applyVARIABLEBINDINGANDRule`       [11514-11578]
//!   - `applyVARBINDPROPAGATEALLRule`      [11833-11869]
//!   - `applyVARBINDVARIABLERule`          [11874-11998]
//!   - `applyVARBINDPROPAGATEJOINRule`     [12002-12220]
//!   - `applyVARBINDPROPAGATEGROUNDINGRule`[12418-12478]
//!   - `applyVARBINDPROPAGATEIMPLICATIONRule`[12481-12586]
//!   - `applyVARBINDPREPARERule`           [12593-12675]
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ signatures take `CIndividualProcessNode*&
//! processIndi, CConceptProcessDescriptor*& conProDes, bool negate,
//! CCalculationAlgorithmContextBase* calcAlgContext`. Ported as `process_indi:
//! &mut NodeId, con_pro_des: &mut ConProcDescId, negate: bool, calc_alg_context:
//! &mut CalculationAlgorithmContextBase` (pointer-to-pointer → `&mut Id`; the
//! context pointer → `&mut` of the per-thread context). All other arena pointers
//! become typed ids / opaque `Cint64`.
//!
//! KONCLUDE-PORT-NOTE[api]: these rules are wholly built on the variable-binding /
//! representative-propagation satellite subsystem (`CConceptRepresentativePropagationSetHash`,
//! `CRepresentativePropagationSet`, `CVariableBindingPathSet`, `CPropagationBindingSet`,
//! `CPropagationVariableBindingTransitionExtension`, `CVariableBindingTriggerHash`,
//! the variable-binding-path descriptor/linker family) PLUS ~20 sibling algorithm
//! methods (`createXXXDependency`, `propagateRepresentative`,
//! `propagateInitial/FreshVariableBindings`, `addConceptToIndividual*`,
//! `applyReapplyQueueConcepts`, …) and the concept/descriptor arena accessors —
//! NONE of which are ported yet, and none of which the algorithm has a wired arena
//! handle for here. Every such pointer dereference / call is reproduced as a
//! `// W3-DEFER[api]:` stub returning the minimal value (`Id::NONE`/`INVALID`/
//! `false`/`0`/empty), preserving the exact branch + loop structure and order of
//! operations. The real `self` state that IS ported (the `stat_*` counters, the
//! debug-write flags) is mutated faithfully. One deeply-entangled sub-block (the
//! join-rule transition-extension hash machinery) is marked `// PORT-PENDING`.
//!
//! W3-FILL-ASSESSMENT (2026-06-30): the keystone wave (node satellites, dependency
//! factory, clash/stop, node resolution) does NOT yet unblock this unit. The
//! var-binding / representative-propagation rule family remains deferred end-to-end
//! because its call graph is still in the opaque-`Cint64` skeleton state and three
//! foundational pieces are absent. PRECISE remaining blockers (named per-rule on the
//! `/// Port of` anchors below), split into the shared changes the reconcile must
//! make (`RECONCILE-NEED`) vs. genuinely-unported subsystems (`STILL-MISSING`):
//!   - RECONCILE-NEED [shared, completion/u11.rs + u33.rs]: the sibling propagation
//!     helpers `propagate_initial_variable_bindings` / `propagate_fresh_variable_bindings`
//!     (and `propagate_representative`) still take OPAQUE `Cint64` for their
//!     binding-set / binding-set-hash arguments; the now-existing typed
//!     `VarBindingPathSetId` / `PropagationBindingSetId` /
//!     `ConceptVariableBindingPathSetHashId` (binding_hash.rs) cannot be threaded
//!     through them until those signatures are re-typed. Wiring is therefore left
//!     deferred (passing typed ids would dangle; passing `Cint64` placeholders into a
//!     skeleton body is not faithful wiring).
//!   - RECONCILE-NEED [shared, process/context.rs]: no node-satellite lazy-alloc
//!     accessors `node_reapply_role_successor_hash` / `node_concept_processing_queue`
//!     / `node_concept_representative_propagation_set_hash` exist (only the var-binding-
//!     path-set + propagation-binding-set + reapply-concept-label-set hashes are wired).
//!   - RECONCILE-NEED [shared, process/representative.rs]: no
//!     `ConceptRepresentativePropagationSetHash::get_representative_propagation_set`.
//!   - STILL-MISSING: `CPropagationVariableBindingTransitionExtension` is a zero-size
//!     placeholder (propagation_binding.rs:91) — its mutators
//!     (`set_triggered_variable_individual_pair`, `add_analysed_..._return_matched`,
//!     `get/set_last_analysed_propagation_binding_descriptor`,
//!     `set/is_processing_completed`, `set_last_analysed_propagate_all_flag`) are
//!     unported (the W4.5 transition-extension unit).
//!   - STILL-MISSING: the `CCondensedReapplyQueue` reapply-queue out-param —
//!     `ls1::get_concept_descriptor_and_reapply_queue` does NOT return the
//!     `reapplyQueue` 4th argument, so every `reapplyQueue->isEmpty()` /
//!     `getConceptReapplyIterator` reapply branch stays deferred.
//!   - STILL-MISSING: the grounding handler (`mGroundingHandler->getGroundingConceptLinker`,
//!     `ConceptNominalSchemaGroundingHandler` stub) and the answerer
//!     binding-propagation adapter / propagation-steering controller (W4.5 sat
//!     sub-struct).
//! The leaf scalar descriptor/concept reads at each rule head (`con_des`/`concept`/
//! `dep_track_point`/`role`/`variable`/operand-list) are individually resolvable via
//! the u07/u08 idiom (`con_proc_desc`/`con_desc`/`ontology_arenas().concept`), but are
//! NOT un-deferred in isolation: each feeds only the still-stubbed control flow above,
//! so wiring them alone would change no behaviour while introducing dead borrows
//! across the `&mut` rule body. They land with the same reconcile that re-types the
//! binding call graph.

#![allow(
    unused_variables,
    unused_mut,
    unused_assignments,
    dead_code,
    clippy::collapsible_if,
    clippy::collapsible_else_if
)]

use super::super::model::op::{CCVARBINDJOIN, CCVARBINDVARIABLE};
use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, IndividualId, RoleId, VariableId};
use super::super::process::{
    ConDescId, ConProcDescId, EdgeId, LabelSetId, NodeId, RoleSuccHashId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyREPRESENTATIVEANDRule`.
    /// W3-FILL: deferred. RECONCILE-NEED: `ProcessContext::node_concept_representative_propagation_set_hash`
    /// (process/context.rs) + `get_representative_propagation_set` (process/representative.rs);
    /// `propagate_representative` (u33) still opaque-`Cint64`. No portable site.
    pub fn apply_representative_and_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: conProDes->getConceptDescriptor()
        let con_des: ConDescId = Id::NONE;
        // W3-DEFER[api]: conDes->getConcept()
        let concept: ConceptId = Id::NONE;
        let concept_negation: bool = negate;
        // W3-DEFER[api]: conProDes->getDependencyTrackPoint()
        let dep_track_point: TrackPointId = Id::NONE;
        // W3-DEFER[api]: concept->getOperandList()
        let op_con_linker: &[NegLink<ConceptId>] = &[];

        // W3-DEFER[api]: calcAlgContext->getUsedProcessingDataBox()
        let proc_data_box: Cint64 = INVALID;
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;

        // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(false)
        let mut con_set: LabelSetId = Id::NONE;
        let mut next_dep_track_point: TrackPointId = Id::NONE;

        let mut con_rep_prop_hash: Cint64 = INVALID;
        let mut prev_rep_prop_set: Cint64 = INVALID;
        let mut proc_rep_prop_des: Cint64 = INVALID;
        let mut prop_dep_track_point: TrackPointId = Id::NONE;

        // W3-DEFER[macro]: STATINC(VARBINDRULEANDAPPLICATIONCOUNT, calc_alg_context)

        for op_con_linker_it in op_con_linker.iter() {
            let binding_trigger_concept: ConceptId = op_con_linker_it.target;
            let binding_trigger_concept_negation: bool = op_con_linker_it.negated ^ concept_negation;

            if con_rep_prop_hash == INVALID {
                // W3-DEFER[api]: processIndi->getConceptRepresentativePropagationSetHash(true)
                con_rep_prop_hash = INVALID;
            }
            if prev_rep_prop_set == INVALID {
                // W3-DEFER[api]: conRepPropHash->getRepresentativePropagationSet(concept, false)
                prev_rep_prop_set = INVALID;
            }
            if prev_rep_prop_set != INVALID {
                // W3-DEFER[api]: prevRepPropSet->getOutgoingRepresentativePropagationDescriptorLinker()
                proc_rep_prop_des = INVALID;
            }
            if proc_rep_prop_des != INVALID {
                // W3-DEFER[api]: procRepPropDes->getDependencyTrackPoint()
                prop_dep_track_point = Id::NONE;
                // W3-DEFER[api]: conRepPropHash->getRepresentativePropagationSet(bindingTriggerConcept, true)
                let rep_prop_set: Cint64 = INVALID;

                let mut binding_con_des: ConDescId = Id::NONE;
                let mut binding_dep_track_point: TrackPointId = Id::NONE;
                let mut reapply_queue: Cint64 = INVALID;

                // W3-DEFER[api]: conSet->getConceptDescriptorAndReapplyQueue(bindingTriggerConcept, bindingConDes, bindingDepTrackPoint, reapplyQueue)
                let has_con_des_and_queue = false;
                if !has_con_des_and_queue {
                    self.stat_representative_propagate_count += 1;
                    if next_dep_track_point == Id::NONE {
                        // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(true)
                        con_set = Id::NONE;
                        // W3-DEFER[api]: createREPRESENTATIVEANDDependency(nextDepTrackPoint, processIndi, conDes, propDepTrackPoint, calcAlgContext)
                        next_dep_track_point = Id::NONE;
                    }
                    // W3-DEFER[api]: addConceptToIndividualReturnConceptDescriptor(bindingTriggerConcept, bindingTriggerConceptNegation, processIndi, nextDepTrackPoint, false, false, calcAlgContext)
                    binding_con_des = Id::NONE;
                    // W3-DEFER[api]: repPropSet->setConceptDescriptor(bindingConDes)
                    // W3-DEFER[api]: propagateRepresentative(processIndi, procRepPropDes, repPropSet, nextDepTrackPoint, calcAlgContext)
                } else {
                    // W3-DEFER[api]: requiresRepresentativePropagation(processIndi, procRepPropDes, repPropSet, calcAlgContext)
                    let requires_rep_prop = false;
                    if requires_rep_prop {
                        self.stat_representative_propagate_count += 1;
                        if next_dep_track_point == Id::NONE {
                            // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(true)
                            con_set = Id::NONE;
                            // W3-DEFER[api]: createREPRESENTATIVEANDDependency(...)
                            next_dep_track_point = Id::NONE;
                        }
                        // W3-DEFER[api]: propagateRepresentative(processIndi, procRepPropDes, repPropSet, nextDepTrackPoint, calcAlgContext)
                        // W3-DEFER[api]: repPropSet->getOutgoingRepresentativePropagationDescriptorLinker()->getRepresentativeVariableBindingPathSetData()->getRepresentatedVariableCount()
                        let var_count: Cint64 = 0;
                        // W3-DEFER[api]: reapplyConceptUpdatedRepresentative(processIndi, bindingConDes, bindingDepTrackPoint, varCount, conSet, reapplyQueue, calcAlgContext)
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARIABLEBINDINGANDRule`.
    /// W3-FILL: deferred. RECONCILE-NEED: `propagate_initial_variable_bindings` /
    /// `propagate_fresh_variable_bindings` (u11) take opaque-`Cint64` binding-set/hash args;
    /// re-type to `VarBindingPathSetId`/`ConceptVariableBindingPathSetHashId` to wire the
    /// typed accessors. STILL-MISSING: `CCondensedReapplyQueue` reapply branch.
    pub fn apply_variable_binding_and_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: conProDes->getConceptDescriptor()
        let con_des: ConDescId = Id::NONE;
        // W3-DEFER[api]: conDes->getConcept()
        let concept: ConceptId = Id::NONE;
        let concept_negation: bool = negate;
        // W3-DEFER[api]: conProDes->getDependencyTrackPoint()
        let dep_track_point: TrackPointId = Id::NONE;
        // W3-DEFER[api]: concept->getOperandList()
        let op_con_linker: &[NegLink<ConceptId>] = &[];

        // W3-DEFER[api]: calcAlgContext->getUsedProcessingDataBox()
        let proc_data_box: Cint64 = INVALID;
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;

        // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(false)
        let mut con_set: LabelSetId = Id::NONE;
        let mut next_dep_track_point: TrackPointId = Id::NONE;

        // W3-DEFER[macro]: STATINC(VARBINDRULEANDAPPLICATIONCOUNT, calc_alg_context)

        for op_con_linker_it in op_con_linker.iter() {
            let binding_trigger_concept: ConceptId = op_con_linker_it.target;
            let binding_trigger_concept_negation: bool = op_con_linker_it.negated ^ concept_negation;

            let mut binding_con_des: ConDescId = Id::NONE;
            let mut binding_dep_track_point: TrackPointId = Id::NONE;
            let mut reapply_queue: Cint64 = INVALID;

            // W3-DEFER[api]: conSet->getConceptDescriptorAndReapplyQueue(bindingTriggerConcept, bindingConDes, bindingDepTrackPoint, reapplyQueue)
            let has_con_des_and_queue = false;
            if !has_con_des_and_queue {
                if next_dep_track_point == Id::NONE {
                    // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(true)
                    con_set = Id::NONE;
                    // W3-DEFER[api]: createVARBINDPROPAGATEANDDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, calcAlgContext)
                    next_dep_track_point = Id::NONE;
                }
                // W3-DEFER[api]: addConceptToIndividualReturnConceptDescriptor(bindingTriggerConcept, bindingTriggerConceptNegation, processIndi, nextDepTrackPoint, false, false, calcAlgContext)
                binding_con_des = Id::NONE;

                // W3-DEFER[api]: processIndi->getConceptVariableBindingPathSetHash(true)
                let con_var_binding_set_hash: Cint64 = INVALID;
                // W3-DEFER[api]: conVarBindingSetHash->getVariableBindingPathSet(concept, false)
                let prev_var_binding_path_set: Cint64 = INVALID;
                // W3-DEFER[api]: conVarBindingSetHash->getVariableBindingPathSet(bindingTriggerConcept, true)
                let var_binding_path_set: Cint64 = INVALID;
                // W3-DEFER[api]: varBindingPathSet->setConceptDescriptor(bindingConDes)

                // W3-DEFER[api]: propagateInitialVariableBindings(processIndi, bindingConDes, varBindingPathSet, prevVarBindingPathSet, nullptr, conVarBindingSetHash, calcAlgContext)
            } else {
                // W3-DEFER[api]: processIndi->getConceptVariableBindingPathSetHash(true)
                let con_var_binding_set_hash: Cint64 = INVALID;
                // W3-DEFER[api]: conVarBindingSetHash->getVariableBindingPathSet(concept, false)
                let prev_var_binding_path_set: Cint64 = INVALID;
                // W3-DEFER[api]: conVarBindingSetHash->getVariableBindingPathSet(bindingTriggerConcept, true)
                let var_binding_path_set: Cint64 = INVALID;

                // W3-DEFER[api]: propagateFreshVariableBindings(processIndi, conDes, varBindingPathSet, prevVarBindingPathSet, nullptr, conVarBindingSetHash, calcAlgContext)
                let fresh_propagated = false;
                if fresh_propagated {
                    // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi, calcAlgContext)
                    // W3-DEFER[api]: processIndi->getConceptProcessingQueue(true)
                    let con_pro_queue: Cint64 = INVALID;
                    // W3-DEFER[api]: varBindingPathSet->getVariableBindingPathMap()->count()
                    let binding_count: Cint64 = 0;
                    // W3-DEFER[api]: addConceptPreprocessedToProcessingQueue(bindingConDes, bindingDepTrackPoint, conProQueue, processIndi, true, calcAlgContext)
                    // W3-DEFER[api]: reapplyQueue->isEmpty()
                    let reapply_queue_empty = true;
                    if !reapply_queue_empty {
                        // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(true)
                        con_set = Id::NONE;
                        // W3-DEFER[api]: CCondensedReapplyQueueIterator reapplyQueueIt(conSet->getConceptReapplyIterator(bindingConDes))
                        // W3-DEFER[api]: applyReapplyQueueConcepts(processIndi, &reapplyQueueIt, calcAlgContext)
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDPROPAGATEALLRule`.
    /// W3-FILL: deferred. RECONCILE-NEED: `ProcessContext::node_reapply_role_successor_hash`
    /// + `node_concept_processing_queue` (process/context.rs). STILL-MISSING:
    /// `getRoleSuccessorLinkIterator` (RS-1, satellites.rs). `propagate_variable_bindings_to_successor`
    /// (u11) reachable but the role-succ-hash else-branch + reapply branch stay blocked.
    pub fn apply_varbind_propagate_all_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: conProDes->getConceptDescriptor()
        let con_des: ConDescId = Id::NONE;
        // W3-DEFER[api]: conDes->getConcept()
        let concept: ConceptId = Id::NONE;
        // W3-DEFER[api]: concept->getRole()
        let role: RoleId = Id::NONE;
        // W3-DEFER[api]: conProDes->getDependencyTrackPoint()
        let dep_track_point: TrackPointId = Id::NONE;
        // W3-DEFER[api]: concept->getOperandCount()
        let op_count: Cint64 = 0;
        // W3-DEFER[api]: concept->getOperandList()
        let op_linker: &[NegLink<ConceptId>] = &[];
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;

        // W3-DEFER[api]: concept->getOperandList()
        let concept_op_linker: &[NegLink<ConceptId>] = &[];

        // W3-DEFER[macro]: STATINC(VARBINDRULEALLAPPLICATIONCOUNT, calc_alg_context)

        // W3-DEFER[api]: getLinkProcessingRestriction(conProDes)  [sibling unit 3]
        let rest_link: EdgeId = Id::NONE;
        if rest_link != Id::NONE {
            // W3-DEFER[api]: getSuccessorIndividual(processIndi, restLink, calcAlgContext)
            let succ_indi: NodeId = Id::NONE;

            // W3-DEFER[api]: propagateVariableBindingsToSuccessor(processIndi, succIndi, opLinker, negate, conDes, restLink, calcAlgContext)
        } else {
            // W3-DEFER[api]: processIndi->getReapplyRoleSuccessorHash(false)
            let role_succ_hash: RoleSuccHashId = Id::NONE;
            if role_succ_hash != Id::NONE {
                // W3-DEFER[api]: roleSuccHash->getRoleSuccessorLinkIterator(role) — iterate while hasNext():
                //   link = roleSuccIt.next(true);
                //   succIndi = getSuccessorIndividual(processIndi, link, calcAlgContext);
                //   propagateVariableBindingsToSuccessor(processIndi, succIndi, opLinker, negate, conDes, link, calcAlgContext);
            }
        }
        // W3-DEFER[api]: conProDes->isConceptReapplied()
        let is_concept_reapplied = false;
        if !is_concept_reapplied {
            // W3-DEFER[api]: isConceptInReapplyQueue(conDes, role, processIndi, calcAlgContext)
            let in_reapply_queue = false;
            if !in_reapply_queue {
                // W3-DEFER[api]: addConceptToReapplyQueue(conDes, role, processIndi, true, depTrackPoint, calcAlgContext)
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDVARIABLERule`.
    /// W3-FILL: deferred. STILL-MISSING: `CPropagationVariableBindingTransitionExtension`
    /// is a zero-size placeholder (propagation_binding.rs:91); its analysis mutators
    /// (`get/set_last_analysed_propagation_binding_descriptor`,
    /// `add_analysed_..._return_matched`, `set_triggered_variable_individual_pair`,
    /// `set/is_processing_completed`, `set_last_analysed_propagate_all_flag`) drive the whole
    /// rule and are unported (W4.5). RECONCILE-NEED: `node_concept_processing_queue`.
    pub fn apply_varbind_variable_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: conProDes->getConceptDescriptor()
        let con_des: ConDescId = Id::NONE;
        // W3-DEFER[api]: conDes->getConcept()
        let concept: ConceptId = Id::NONE;
        // W3-DEFER[api]: concept->getVariable()
        let variable: VariableId = Id::NONE;
        let concept_negation: bool = negate;
        // W3-DEFER[api]: conProDes->getDependencyTrackPoint()
        let dep_track_point: TrackPointId = Id::NONE;
        // W3-DEFER[api]: concept->getOperandList()
        let op_con_linker: &[NegLink<ConceptId>] = &[];

        // W3-DEFER[api]: opConLinker->getData() / opConLinker->isNegated()  (head operand)
        let binding_trigger_concept: ConceptId =
            op_con_linker.first().map(|l| l.target).unwrap_or(Id::NONE);
        let binding_trigger_concept_negation: bool =
            op_con_linker.first().map(|l| l.negated).unwrap_or(false);

        // W3-DEFER[api]: calcAlgContext->getUsedProcessContext()
        let process_context: Cint64 = INVALID;
        // W3-DEFER[api]: calcAlgContext->getUsedProcessingDataBox()
        let proc_data_box: Cint64 = INVALID;
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;

        // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(false)
        let mut con_set: LabelSetId = Id::NONE;
        let mut binding_con_des: ConDescId = Id::NONE;
        let mut binding_dep_track_point: TrackPointId = Id::NONE;
        let mut reapply_queue: Cint64 = INVALID;

        // W3-DEFER[macro]: STATINC(VARBINDRULEBINDAPPLICATIONCOUNT, calc_alg_context)

        let mut update_ext = false;

        // W3-DEFER[api]: processIndi->getConceptPropagationBindingSetHash(false)
        let con_prop_binding_set_hash: Cint64 = INVALID;
        if con_prop_binding_set_hash != INVALID {
            // W3-DEFER[api]: conPropBindingSetHash->getPropagationBindingSet(concept, false)
            let prop_binding_set: Cint64 = INVALID;
            if prop_binding_set != INVALID {
                // W3-DEFER[api]: propBindingSet->getPropagationVariableBindingTransitionExtension(false)
                let prop_var_bind_trans_ext: Cint64 = INVALID;
                // W3-DEFER[api]: !propVarBindTransExt || !propVarBindTransExt->isProcessingCompleted()
                let processing_not_completed = true;
                if processing_not_completed {
                    // W3-DEFER[api]: !propVarBindTransExt || propBindingSet->hasPropagateAllFlag()
                    let no_ext_or_propagate_all = true;
                    if no_ext_or_propagate_all {
                        update_ext = true;
                    } else {
                        // W3-DEFER[api]: propVarBindTransExt->getLastAnalysedPropagationBindingDescriptor()
                        let last_analy_prop_bind_des: Cint64 = INVALID;
                        // W3-DEFER[api]: propBindingSet->getPropagationBindingDescriptorLinker()
                        let prop_bind_des: Cint64 = INVALID;
                        if last_analy_prop_bind_des != prop_bind_des {
                            update_ext = true;
                        }
                    }
                }
            }
        }

        if update_ext {
            if !self.first_binding_creation_debug_written {
                self.first_binding_creation_debug_written = true;
                if self.conf_debugging_write_data {
                    let writing_folder = "./Debugging/CompletionTasks/";
                    // W3-DEFER[api]: mEndTaskDebugIndiModelString = generateExtendedDebugIndiModelStringList(calcAlgContext)
                    self.end_task_debug_indi_model_string = String::new();
                    // W3-DEFER[api]: QFile write of "first-binding-creation-task.txt"
                    let _ = writing_folder;
                }
            }

            // W3-DEFER[api]: processIndi->getConceptPropagationBindingSetHash(true)
            let con_prop_binding_set_hash: Cint64 = INVALID;
            // W3-DEFER[api]: conPropBindingSetHash->getPropagationBindingSet(concept, true)
            let prop_binding_set: Cint64 = INVALID;
            // W3-DEFER[api]: propBindingSet->getPropagationVariableBindingTransitionExtension(true)
            let prop_var_bind_trans_ext: Cint64 = INVALID;

            // W3-DEFER[api]: propVarBindTransExt->getLastAnalysedPropagationBindingDescriptor()
            let last_analy_prop_bind_des: Cint64 = INVALID;
            // W3-DEFER[api]: propBindingSet->getPropagationBindingDescriptorLinker()
            let prop_bind_des: Cint64 = INVALID;

            // W3-DEFER[api]: propVarBindTransExt->setTriggeredVariableIndividualPair(variable, processIndi)
            let mut create_var_binding = false;
            // W3-DEFER[api]: propBindingSet->hasPropagateAllFlag()
            create_var_binding = false;
            // W3-DEFER[api]: for (propBindDesIt = propBindDes; propBindDesIt != lastAnalyPropBindDes; propBindDesIt = propBindDesIt->getNext()):
            //   if propVarBindTransExt->addAnalysedPropagationBindingDescriptorReturnMatched(propBindDesIt): createVarBinding = true;
            // W3-DEFER[api]: propVarBindTransExt->setLastAnalysedPropagationBindingDescriptor(propBindDes)
            // W3-DEFER[api]: propVarBindTransExt->setLastAnalysedPropagateAllFlag(propBindingSet->hasPropagateAllFlag())

            if create_var_binding {
                self.stat_var_binding_created_count += 1;
                // W3-DEFER[macro]: STATINC(VARBINDVARIABLEBINDCOUNT, calc_alg_context)
                // W3-DEFER[api]: propVarBindTransExt->setProcessingCompleted(true)

                // W3-DEFER[api]: processIndi->getConceptVariableBindingPathSetHash(true)
                let con_var_binding_path_set_hash: Cint64 = INVALID;
                // W3-DEFER[api]: conVarBindingPathSetHash->getVariableBindingPathSet(bindingTriggerConcept, true)
                let var_bind_path_set: Cint64 = INVALID;

                // W3-DEFER[api]: calcAlgContext->getUsedProcessingDataBox()
                let processing_data_box: Cint64 = INVALID;
                // W3-DEFER[api]: processingDataBox->getNextVariableBindingPathID(true)
                let next_path_prop_id: Cint64 = 0;

                let mut next_dep_track_point: TrackPointId = Id::NONE;
                // W3-DEFER[api]: createVARBINDVARIABLEDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, calcAlgContext)
                next_dep_track_point = Id::NONE;

                // W3-DEFER[api]: conSet->getConceptDescriptorAndReapplyQueue(bindingTriggerConcept, bindingConDes, bindingDepTrackPoint, reapplyQueue)
                let has_con_des_and_queue = false;
                if !has_con_des_and_queue {
                    // W3-DEFER[api]: addConceptToIndividualReturnConceptDescriptor(bindingTriggerConcept, bindingTriggerConceptNegation, processIndi, nextDepTrackPoint, false, false, calcAlgContext)
                    binding_con_des = Id::NONE;
                } else {
                    // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi, calcAlgContext)
                    // W3-DEFER[api]: processIndi->getConceptProcessingQueue(true)
                    let con_pro_queue: Cint64 = INVALID;
                    // W3-DEFER[api]: addConceptPreprocessedToProcessingQueue(bindingConDes, bindingDepTrackPoint, conProQueue, processIndi, true, calcAlgContext)
                    // W3-DEFER[api]: reapplyQueue->isEmpty()
                    let reapply_queue_empty = true;
                    if !reapply_queue_empty {
                        // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(true)
                        con_set = Id::NONE;
                        // W3-DEFER[api]: CCondensedReapplyQueueIterator reapplyQueueIt(conSet->getConceptReapplyIterator(bindingConDes))
                        // W3-DEFER[api]: applyReapplyQueueConcepts(processIndi, &reapplyQueueIt, calcAlgContext)
                    }
                }

                // W3-DEFER[api]: varBindPathSet->setConceptDescriptor(bindingConDes)
                // W3-DEFER[memory-pool]: allocate+init CVariableBinding(nextDepTrackPoint, processIndi, variable)
                let var_binding: Cint64 = INVALID;
                // W3-DEFER[memory-pool]: allocate+init CVariableBindingDescriptor(varBinding)
                let var_binding_des: Cint64 = INVALID;
                // W3-DEFER[memory-pool]: allocate+init CVariableBindingPath(nextPathPropID, varBindingDes)
                let var_binding_path: Cint64 = INVALID;
                // W3-DEFER[memory-pool]: allocate+init CVariableBindingPathDescriptor(varBindingPath, nextDepTrackPoint)
                let var_binding_path_des: Cint64 = INVALID;
                // W3-DEFER[api]: varBindPathSet->addVariableBindingPath(varBindingPathDes)
                // W3-DEFER[api]: conVarBindingPathSetHash->setLastVariableBindingDescriptionLinker(varBindingPathDes)
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDPROPAGATEJOINRule`.
    /// W3-FILL: deferred (existing PORT-PENDING `todo!` kept). STILL-MISSING: the
    /// transition-extension join machinery (cpp 12076–12206) — `CVariableBindingTriggerHash` /
    /// `CVariableBindingPathJoiningHash` over `CPropagationVariableBindingTransitionExtension`
    /// (W4.5) + `triggerVariableBindingPathJoining`/`propagateVariableBindingsJoins` (u11).
    pub fn apply_varbind_propagate_join_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: conProDes->getConceptDescriptor()
        let con_des: ConDescId = Id::NONE;
        // W3-DEFER[api]: conDes->getConcept()
        let concept: ConceptId = Id::NONE;
        // W3-DEFER[api]: conProDes->getDependencyTrackPoint()
        let dep_track_point: TrackPointId = Id::NONE;
        // W3-DEFER[api]: concept->getOperandCount()
        let op_count: Cint64 = 0;
        // W3-DEFER[api]: concept->getOperandList()
        let op_linker: &[NegLink<ConceptId>] = &[];
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;

        // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(false)
        let mut con_set: LabelSetId = Id::NONE;
        let mut join_con_des: ConDescId = Id::NONE;
        let mut join_dep_track_point: TrackPointId = Id::NONE;
        let mut reapply_queue: Cint64 = INVALID;

        // W3-DEFER[api]: opLinker->getData() / opLinker->isNegated()  (head = join concept)
        let join_concept: ConceptId = op_linker.first().map(|l| l.target).unwrap_or(Id::NONE);
        let join_concept_negation: bool = op_linker.first().map(|l| l.negated).unwrap_or(false);
        // W3-DEFER[api]: opLinker->getNext()  (tail = trigger operands)
        let trigger_linker: &[NegLink<ConceptId>] = if op_linker.is_empty() {
            &[]
        } else {
            &op_linker[1..]
        };

        // W3-DEFER[api]: concept->getVariableLinker()
        let var_linker: &[VariableId] = &[];

        // W3-DEFER[macro]: STATINC(VARBINDRULEJOINAPPLICATIONCOUNT, calc_alg_context)

        let mut propagate_joins = false;
        let mut create_join_concept = false;
        // W3-DEFER[api]: conSet->getConceptDescriptorAndReapplyQueue(joinConcept, joinConDes, joinDepTrackPoint, reapplyQueue)
        let has_join_des_and_queue = false;
        if !has_join_des_and_queue {
            // search next not existing trigger
            let mut all_triggers_available = true;
            // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(true)
            con_set = Id::NONE;
            let mut trigger_break_idx: Option<usize> = None;
            for (idx, next_trigger) in trigger_linker.iter().enumerate() {
                if !all_triggers_available {
                    break;
                }
                let trigger_concept: ConceptId = next_trigger.target;
                let mut trigger_con_des: ConDescId = Id::NONE;
                let mut trigger_dep_track_point: TrackPointId = Id::NONE;
                // W3-DEFER[api]: conSet->getConceptDescriptor(triggerConcept, triggerConDes, triggerDepTrackPoint)
                let has_trigger_con_des = false;
                if has_trigger_con_des {
                    // W3-DEFER[api]: triggerConDes->isNegated() == nextTrigger->isNegated()
                    let trigger_des_negated = false;
                    if trigger_des_negated == next_trigger.negated {
                        return;
                    }
                } else {
                    all_triggers_available = false;
                    trigger_break_idx = Some(idx);
                    break;
                }
            }

            if !all_triggers_available {
                // install to trigger
                if let Some(idx) = trigger_break_idx {
                    let next_trigger = &trigger_linker[idx];
                    let trigger_concept: ConceptId = next_trigger.target;
                    let trigger_negation: bool = !next_trigger.negated;
                    // W3-DEFER[api]: isConceptInReapplyQueue(conDes, triggerConcept, triggerNegation, processIndi, calcAlgContext)
                    let in_reapply_queue = false;
                    if !in_reapply_queue {
                        // W3-DEFER[api]: addConceptToReapplyQueue(conDes, triggerConcept, triggerNegation, processIndi, nullptr, depTrackPoint, calcAlgContext)
                    }
                }
            } else {
                propagate_joins = true;
                create_join_concept = true;
            }
        } else {
            propagate_joins = true;
        }

        let mut propagations_done = false;
        if propagate_joins {
            for next_trigger in trigger_linker.iter() {
                let trigger_concept: ConceptId = next_trigger.target;
                // W3-DEFER[api]: isConceptInReapplyQueue(conDes, triggerConcept, false, processIndi, calcAlgContext)
                let in_reapply_queue = false;
                if !in_reapply_queue {
                    // W3-DEFER[api]: addConceptToReapplyQueue(conDes, triggerConcept, false, processIndi, nullptr, depTrackPoint, calcAlgContext)
                }
            }

            // W3-DEFER[api]: processIndi->getConceptPropagationBindingSetHash(false)
            let con_prop_binding_set_hash: Cint64 = INVALID;
            // W3-DEFER[api]: processIndi->getConceptVariableBindingPathSetHash(false)
            let var_binding_path_set_hash: Cint64 = INVALID;
            let mut prop_binding_set: Cint64 = INVALID;
            if con_prop_binding_set_hash != INVALID && var_binding_path_set_hash != INVALID {
                // W3-DEFER[api]: conPropBindingSetHash->getPropagationBindingSet(concept, false)
                prop_binding_set = INVALID;
                if prop_binding_set != INVALID {
                    // PORT-PENDING: the transition-extension join machinery (cpp 12076–12206)
                    // iterates the not-yet-ported CVariableBindingTriggerHash /
                    // CVariableBindingPathJoiningHash over CPropagationVariableBindingTransitionExtension,
                    // calling propagateVariableBindingsJoins / triggerVariableBindingPathJoining
                    // (sibling unit 11) and setting propagationsDone. Too entangled to skeleton
                    // before the variable-binding-path subsystem + unit-11 helpers land.
                    // Behaviour preserved: propagationsDone stays false until ported.
                    todo!("W3-DEFER: applyVARBINDPROPAGATEJOINRule transition-extension join machinery (cpp 12076-12206)");
                }
            }
        }

        if propagations_done {
            if !create_join_concept {
                // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi, calcAlgContext)
                // W3-DEFER[api]: processIndi->getConceptProcessingQueue(true)
                let con_pro_queue: Cint64 = INVALID;
                // W3-DEFER[api]: addConceptPreprocessedToProcessingQueue(joinConDes, joinDepTrackPoint, conProQueue, processIndi, true, calcAlgContext)
                // W3-DEFER[api]: reapplyQueue->isEmpty()
                let reapply_queue_empty = true;
                if !reapply_queue_empty {
                    // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(true)
                    con_set = Id::NONE;
                    // W3-DEFER[api]: CCondensedReapplyQueueIterator reapplyQueueIt(conSet->getConceptReapplyIterator(joinConDes))
                    // W3-DEFER[api]: applyReapplyQueueConcepts(processIndi, &reapplyQueueIt, calcAlgContext)
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDPROPAGATEGROUNDINGRule`.
    /// W3-FILL: deferred. STILL-MISSING: the grounding handler
    /// `mGroundingHandler->getGroundingConceptLinker` (`ConceptNominalSchemaGroundingHandler`
    /// stub) — supplies the whole `newGroundedLinker`; nothing fires without it.
    pub fn apply_varbind_propagate_grounding_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;

        // W3-DEFER[api]: conProDes->getConceptDescriptor()
        let con_des: ConDescId = Id::NONE;
        // W3-DEFER[api]: conProDes->getDependencyTrackPoint()
        let dep_track_point: TrackPointId = Id::NONE;
        // W3-DEFER[api]: conDes->getConcept()
        let concept: ConceptId = Id::NONE;
        // W3-DEFER[api]: conDes->isNegated()
        let negated: bool = false;
        // W3-DEFER[api]: concept->getOperandCount()
        let op_count: Cint64 = 0;

        // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(false)
        let con_set: LabelSetId = Id::NONE;

        // W3-DEFER[api]: processIndi->getConceptVariableBindingPathSetHash(false)
        let con_var_bind_path_set_hash: Cint64 = INVALID;
        // W3-DEFER[api]: conVarBindPathSetHash->getVariableBindingPathSet(concept, false)
        let var_bind_path_set: Cint64 = INVALID;

        // W3-DEFER[macro]: STATINC(VARBINDRULEGROUNDINGAPPLICATIONCOUNT, calc_alg_context)

        if var_bind_path_set != INVALID {
            // W3-DEFER[macro]: KONCLUCE_TASK_ALGORITHM_MODEL_STRING_INSTRUCTION(mBeforeGroundingDebugIndiModelString = generateExtendedDebugIndiModelStringList(...))

            // W3-DEFER[api]: mGroundingHandler->getGroundingConceptLinker(processIndi, varBindPathSet, concept, negated, groundedConVarBindPathDesHash, calcAlgContext)
            let grounded_con_var_bind_path_des_hash: Cint64 = INVALID;
            let new_grounded_linker: &[NegLink<ConceptId>] = &[];

            if !new_grounded_linker.is_empty() {
                for new_grounded_linker_it in new_grounded_linker.iter() {
                    // W3-DEFER[macro]: STATINC(VARBINDGROUNDINGCOUNT, calc_alg_context)
                    self.stat_var_binding_grounding_count += 1;
                    let new_grounded_concept: ConceptId = new_grounded_linker_it.target;
                    let new_grounded_concept_negation: bool = new_grounded_linker_it.negated;

                    let mut base_dependency_track_point: TrackPointId = Id::NONE;
                    let additionals_dependencies: Cint64 = INVALID;
                    // collect dependencies
                    // W3-DEFER[api]: iterate groundedConVarBindPathDesHash for newGroundedConcept:
                    //   varBindPathDes = it.value(); propVarDepTrackPoint = varBindPathDes->getDependencyTrackPoint();
                    //   if propVarDepTrackPoint && !baseDependencyTrackPoint: baseDependencyTrackPoint = propVarDepTrackPoint;

                    if base_dependency_track_point == Id::NONE {
                        base_dependency_track_point = dep_track_point;
                    }

                    let mut next_dep_track_point: TrackPointId = Id::NONE;
                    // W3-DEFER[api]: createVARBINDPROPAGATEGROUNDINGDependency(nextDepTrackPoint, processIndi, conDes, baseDependencyTrackPoint, additionalsDependencies, calcAlgContext)
                    next_dep_track_point = Id::NONE;

                    // W3-DEFER[api]: addConceptToIndividual(newGroundedConcept, newGroundedConceptNegation, processIndi, nextDepTrackPoint, true, false, calcAlgContext)
                }
            }

            // W3-DEFER[macro]: KONCLUCE_TASK_ALGORITHM_MODEL_STRING_INSTRUCTION(mAfterGroundingDebugIndiModelString = generateExtendedDebugIndiModelStringList(...))
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDPROPAGATEIMPLICATIONRule`.
    /// W3-FILL: deferred. `create_connection_dependency` (u29) /
    /// `create_varbind_propagate_implication_dependency` (u28) are typed-callable, but the
    /// rule core lands in `propagate_initial_variable_bindings`/`propagate_fresh_variable_bindings`
    /// (u11), still opaque-`Cint64`. RECONCILE-NEED: re-type u11 binding args.
    /// STILL-MISSING: `CCondensedReapplyQueue` reapply branch.
    pub fn apply_varbind_propagate_implication_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: conProDes->getConceptDescriptor()
        let con_des: ConDescId = Id::NONE;
        // W3-DEFER[api]: conDes->getConcept()
        let concept: ConceptId = Id::NONE;
        // W3-DEFER[api]: conProDes->getDependencyTrackPoint()
        let dep_track_point: TrackPointId = Id::NONE;
        // W3-DEFER[api]: concept->getOperandCount()
        let op_count: Cint64 = 0;
        // W3-DEFER[api]: concept->getOperandList()
        let op_linker: &[NegLink<ConceptId>] = &[];
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;

        // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(false)
        let mut con_set: LabelSetId = Id::NONE;
        let mut binding_con_des: ConDescId = Id::NONE;
        let mut binding_dep_track_point: TrackPointId = Id::NONE;
        let mut reapply_queue: Cint64 = INVALID;

        // W3-DEFER[api]: opLinker->getData() / opLinker->isNegated()  (head = binding trigger)
        let binding_trigger_concept: ConceptId =
            op_linker.first().map(|l| l.target).unwrap_or(Id::NONE);
        let binding_trigger_concept_negation: bool =
            op_linker.first().map(|l| l.negated).unwrap_or(false);
        // W3-DEFER[api]: opLinker->getNext()  (tail = trigger operands)
        let trigger_linker: &[NegLink<ConceptId>] = if op_linker.is_empty() {
            &[]
        } else {
            &op_linker[1..]
        };

        // W3-DEFER[macro]: STATINC(VARBINDRULEIMPLICATIONAPPLICATIONCOUNT, calc_alg_context)

        // W3-DEFER[api]: conSet->getConceptDescriptorAndReapplyQueue(bindingTriggerConcept, bindingConDes, bindingDepTrackPoint, reapplyQueue)
        let has_binding_des_and_queue = false;
        if !has_binding_des_and_queue {
            // search next not existing trigger
            let mut all_triggers_available = true;
            // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(true)
            con_set = Id::NONE;
            let mut trigger_break_idx: Option<usize> = None;
            for (idx, next_trigger) in trigger_linker.iter().enumerate() {
                let trigger_concept: ConceptId = next_trigger.target;
                let mut trigger_con_des: ConDescId = Id::NONE;
                let mut trigger_dep_track_point: TrackPointId = Id::NONE;
                // W3-DEFER[api]: conSet->getConceptDescriptor(triggerConcept, triggerConDes, triggerDepTrackPoint)
                let has_trigger_con_des = false;
                if has_trigger_con_des {
                    // W3-DEFER[api]: triggerConDes->isNegated() == nextTrigger->isNegated()
                    let trigger_des_negated = false;
                    if trigger_des_negated == next_trigger.negated {
                        return;
                    }
                } else {
                    all_triggers_available = false;
                    trigger_break_idx = Some(idx);
                    break;
                }
            }

            if !all_triggers_available {
                // install to trigger
                if let Some(idx) = trigger_break_idx {
                    let next_trigger = &trigger_linker[idx];
                    let trigger_concept: ConceptId = next_trigger.target;
                    let trigger_negation: bool = !next_trigger.negated;
                    // W3-DEFER[api]: isConceptInReapplyQueue(conDes, triggerConcept, triggerNegation, processIndi, calcAlgContext)
                    let in_reapply_queue = false;
                    if !in_reapply_queue {
                        // W3-DEFER[api]: addConceptToReapplyQueue(conDes, triggerConcept, triggerNegation, processIndi, nullptr, depTrackPoint, calcAlgContext)
                    }
                }
            } else {
                let mut trigger_deps: Cint64 = INVALID;
                for trigger_linker_it in trigger_linker.iter() {
                    let trigger_concept: ConceptId = trigger_linker_it.target;
                    let mut trigger_con_des: ConDescId = Id::NONE;
                    let mut trigger_dep_track_point: TrackPointId = Id::NONE;
                    // W3-DEFER[api]: conSet->getConceptDescriptor(triggerConcept, triggerConDes, triggerDepTrackPoint)
                    // W3-DEFER[api]: createCONNECTIONDependency(processIndi, triggerConDes, triggerDepTrackPoint, calcAlgContext)
                    let conn_dep: Cint64 = INVALID;
                    // W3-DEFER[api]: connDep->setNext(triggerDeps)
                    trigger_deps = conn_dep;
                }

                self.stat_var_binding_implication_count += 1;
                let mut next_dep_track_point: TrackPointId = Id::NONE;
                // W3-DEFER[api]: createVARBINDPROPAGATEIMPLICATIONDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, triggerDeps, calcAlgContext)
                next_dep_track_point = Id::NONE;

                // W3-DEFER[api]: addConceptToIndividualReturnConceptDescriptor(bindingTriggerConcept, bindingTriggerConceptNegation, processIndi, nextDepTrackPoint, true, false, calcAlgContext)
                binding_con_des = Id::NONE;

                // W3-DEFER[api]: processIndi->getConceptVariableBindingPathSetHash(true)
                let con_var_binding_set_hash: Cint64 = INVALID;
                // W3-DEFER[api]: conVarBindingSetHash->getVariableBindingPathSet(concept, false)
                let prev_var_binding_path_set: Cint64 = INVALID;
                // W3-DEFER[api]: conVarBindingSetHash->getVariableBindingPathSet(bindingTriggerConcept, true)
                let var_binding_path_set: Cint64 = INVALID;
                // W3-DEFER[api]: varBindingPathSet->setConceptDescriptor(bindingConDes)

                // W3-DEFER[api]: propagateInitialVariableBindings(processIndi, bindingConDes, varBindingPathSet, prevVarBindingPathSet, triggerDeps, conVarBindingSetHash, calcAlgContext)
            }
        } else {
            let mut trigger_deps: Cint64 = INVALID;
            for trigger_linker_it in trigger_linker.iter() {
                let trigger_concept: ConceptId = trigger_linker_it.target;
                let mut trigger_con_des: ConDescId = Id::NONE;
                let mut trigger_dep_track_point: TrackPointId = Id::NONE;
                // W3-DEFER[api]: conSet->getConceptDescriptor(triggerConcept, triggerConDes, triggerDepTrackPoint)
                // W3-DEFER[api]: createCONNECTIONDependency(processIndi, triggerConDes, triggerDepTrackPoint, calcAlgContext)
                let conn_dep: Cint64 = INVALID;
                // W3-DEFER[api]: connDep->setNext(triggerDeps)
                trigger_deps = conn_dep;
            }
            self.stat_var_binding_implication_count += 1;

            // W3-DEFER[api]: processIndi->getConceptVariableBindingPathSetHash(true)
            let con_var_binding_set_hash: Cint64 = INVALID;
            // W3-DEFER[api]: conVarBindingSetHash->getVariableBindingPathSet(concept, false)
            let prev_var_binding_path_set: Cint64 = INVALID;
            // W3-DEFER[api]: conVarBindingSetHash->getVariableBindingPathSet(bindingTriggerConcept, true)
            let var_binding_path_set: Cint64 = INVALID;

            // W3-DEFER[api]: propagateFreshVariableBindings(processIndi, conDes, varBindingPathSet, prevVarBindingPathSet, triggerDeps, conVarBindingSetHash, calcAlgContext)
            let fresh_propagated = false;
            if fresh_propagated {
                // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi, calcAlgContext)
                // W3-DEFER[api]: processIndi->getConceptProcessingQueue(true)
                let con_pro_queue: Cint64 = INVALID;
                // W3-DEFER[api]: varBindingPathSet->getVariableBindingPathMap()->count()
                let binding_count: Cint64 = 0;
                // W3-DEFER[api]: addConceptPreprocessedToProcessingQueue(bindingConDes, bindingDepTrackPoint, conProQueue, processIndi, bindingCount, calcAlgContext)
                // W3-DEFER[api]: reapplyQueue->isEmpty()
                let reapply_queue_empty = true;
                if !reapply_queue_empty {
                    // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(true)
                    con_set = Id::NONE;
                    // W3-DEFER[api]: CCondensedReapplyQueueIterator reapplyQueueIt(conSet->getConceptReapplyIterator(bindingConDes))
                    // W3-DEFER[api]: applyReapplyQueueConcepts(processIndi, &reapplyQueueIt, calcAlgContext)
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDPREPARERule`.
    /// W3-FILL: deferred. STILL-MISSING: `getSatisfiableAnswererBindingPropagationAdapter` +
    /// `getAnswererPropagationSteeringController` (W4.5 sat sub-struct) — the outer guard;
    /// nothing runs without it. Also `get_propagation_binding_set` localize-alloc still
    /// W3b-deferred (binding_hash.rs) + RECONCILE-NEED `node_concept_processing_queue`.
    pub fn apply_varbind_prepare_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: conProDes->getConceptDescriptor()
        let con_des: ConDescId = Id::NONE;
        // W3-DEFER[api]: conDes->getConcept()
        let concept: ConceptId = Id::NONE;
        let concept_negation: bool = negate;
        // W3-DEFER[api]: conProDes->getDependencyTrackPoint()
        let dep_track_point: TrackPointId = Id::NONE;
        // W3-DEFER[api]: concept->getOperandList()
        let op_con_linker: &[NegLink<ConceptId>] = &[];

        // W3-DEFER[api]: calcAlgContext->getUsedProcessingDataBox()
        let proc_data_box: Cint64 = INVALID;
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;

        // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(false)
        let mut con_set: LabelSetId = Id::NONE;
        let mut next_dep_track_point: TrackPointId = Id::NONE;

        // W3-DEFER[macro]: STATINC(VARBINDRULEANDAPPLICATIONCOUNT, calc_alg_context)

        // W3-DEFER[api]: calcAlgContext->getSatisfiableCalculationTask()->getSatisfiableAnswererBindingPropagationAdapter()
        let answerer_message_adapter: Cint64 = INVALID;
        if answerer_message_adapter != INVALID {
            // W3-DEFER[api]: answererMessageAdapter->getAnswererPropagationSteeringController()
            let propagation_steering_controller: Cint64 = INVALID;
            if propagation_steering_controller != INVALID {
                for op_con_linker_it in op_con_linker.iter() {
                    let binding_trigger_concept: ConceptId = op_con_linker_it.target;
                    let binding_trigger_concept_negation: bool =
                        op_con_linker_it.negated ^ concept_negation;

                    let mut binding_con_des: ConDescId = Id::NONE;
                    let mut binding_dep_track_point: TrackPointId = Id::NONE;
                    let mut reapply_queue: Cint64 = INVALID;

                    // W3-DEFER[api]: conSet->getConceptDescriptorAndReapplyQueue(bindingTriggerConcept, bindingConDes, bindingDepTrackPoint, reapplyQueue)
                    let has_con_des_and_queue = false;
                    if !has_con_des_and_queue {
                        let mut propagate_all = false;
                        let mut propagate_nominal = false;
                        let mut propagate_bindings = false;
                        let mut variable: VariableId = Id::NONE;
                        // W3-DEFER[api]: processIndi->getNominalIndividual()
                        let nominal_indi: IndividualId = Id::NONE;
                        // W3-DEFER[api]: bindingTriggerConcept->getOperatorCode()
                        let binding_trigger_operator_code: Cint64 = 0;
                        if binding_trigger_operator_code == CCVARBINDJOIN {
                            propagate_all = true;
                            propagate_bindings = true;
                        } else {
                            // W3-DEFER[api]: bindingTriggerConcept->getVariable()
                            variable = Id::NONE;
                            if binding_trigger_operator_code == CCVARBINDVARIABLE {
                                propagate_bindings = true;
                            } else {
                                // W3-DEFER[api]: concept->getVariable()
                                variable = Id::NONE;
                            }
                            if variable != Id::NONE {
                                // W3-DEFER[api]: propagationSteeringController->isPreparationBindingAllIndividuals(variable)
                                propagate_all = false;
                                if nominal_indi != Id::NONE {
                                    // W3-DEFER[api]: propagationSteeringController->isPreparationBindingNominalIndividual(variable, nominalIndi)
                                    propagate_nominal = false;
                                }
                            }
                        }

                        if next_dep_track_point == Id::NONE {
                            // W3-DEFER[api]: processIndi->getReapplyConceptLabelSet(true)
                            con_set = Id::NONE;
                            if propagate_bindings {
                                // W3-DEFER[api]: createVARBINDPROPAGATEANDDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, calcAlgContext)
                                next_dep_track_point = Id::NONE;
                            } else {
                                // W3-DEFER[api]: createANDDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, calcAlgContext)
                                next_dep_track_point = Id::NONE;
                            }
                        }

                        let mut prop_binding_set: Cint64 = INVALID;
                        if propagate_bindings {
                            // W3-DEFER[api]: processIndi->getConceptPropagationBindingSetHash(true)
                            let con_prop_binding_set_hash: Cint64 = INVALID;
                            // W3-DEFER[api]: conPropBindingSetHash->getPropagationBindingSet(bindingTriggerConcept, true)
                            prop_binding_set = INVALID;
                            if propagate_all | propagate_nominal {
                                // W3-DEFER[api]: propBindingSet->setPropagateAllFlag(true)
                            }
                        }

                        // W3-DEFER[api]: addConceptToIndividualReturnConceptDescriptor(bindingTriggerConcept, bindingTriggerConceptNegation, processIndi, nextDepTrackPoint, false, false, calcAlgContext)
                        binding_con_des = Id::NONE;
                        if prop_binding_set != INVALID {
                            // W3-DEFER[api]: propBindingSet->setConceptDescriptor(bindingConDes)
                        }
                    }
                }
            }
        }
    }
}
