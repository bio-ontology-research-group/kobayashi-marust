//! `completion::u07` — W3 method-batch unit #7 (Expansion-rule family, batch 3).
//!
//! Faithful port of 12 expansion-rule methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (manifest `01-completion-methods.md`, "Unit 7", cpp ranges 12681–14097):
//!   - `applyVARBINDFINALIZERule`          [12681-12725]
//!   - `applyBINDPROPAGATEGROUNDINGRule`   [12828-13040]
//!   - `applyBINDPROPAGATECYCLERule`       [13048-13288]
//!   - `applyBINDPROPAGATEALLRule`         [13467-13503]
//!   - `applyBINDPROPAGATEIMPLICATIONRule` [13510-13610]
//!   - `applyBINDPROPAGATEANDRule`         [13614-13616]
//!   - `applyBINDPROPAGATEANDFLAGALLRule`  [13620-13623]
//!   - `applyBINDVARIABLERule`             [13694-13769]
//!   - `applyDATATYPERule`                 [14009-14031]
//!   - `applyDATARESTRICTIONRule`          [14037-14053]
//!   - `applyDATALITERALRule`              [14058-14077]
//!   - `applyDATALITERALIMPLICATIONRule`   [14082-14097]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each rule is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase` (the C++ `CCalculationAlgorithmContextBase*`).
//! The `CIndividualProcessNode*&` / `CConceptProcessDescriptor*&` out/in-out
//! pointer-references become `&mut NodeId` / `&mut ConProcDescId` (arena ids).
//!
//! W3.5-RECONCILE: this unit is ported AGAINST the live arena context (PORT.md
//! §"W3.5"). Every reachable C++ `obj->getX()` deref now resolves through the
//! real accessor convention — descriptor/concept reads via
//! `calc_alg_context.process_context().con_proc_desc(id)` /
//! `.con_desc(id)` and `calc_alg_context.ontology_arenas().concept(id)`, the
//! databox via `calc_alg_context.processing_data_box()`. So the rule preludes are
//! FAITHFUL, not stubs.
//!
//! KONCLUDE-PORT-NOTE[api]: the four binding-PROPAGATION rules
//! (GROUNDING / CYCLE / IMPLICATION / BINDVARIABLE) and the answerer FINALIZE rule
//! are built on subsystems that are still genuinely unported and have NO threaded
//! handle in the port yet:
//!   * the propagation-binding satellite subsystem — the node lazy-getters
//!     `getReapplyConceptLabelSet` / `getConceptPropagationBindingSetHash` /
//!     `getReapplyRoleSuccessorHash` / `getConceptProcessingQueue` (node.rs is only
//!     PN-1-ported) and the satellite types `CPropagationBindingSet` /
//!     `CConceptPropagationBindingSetHash` / `CPropagationBinding(Descriptor)` /
//!     `CPropagationBindingMap` / `CReapplyConceptLabelSet::getConceptDescriptor…`;
//!   * the dependency factory (`create*Dependency`, lands in the dependency-tracking
//!     units u28/u29) — kept as `// W6-DEFER[api]` comment stubs (NOT `self` calls)
//!     so the incremental reconcile build stays green;
//!   * `mGroundingHandler` (the nominal-schema grounding handler), `mDatatypeHandler`
//!     (the datatype value-space handler) and the answerer message adapter /
//!     marker-individual hash (Task / message-analyser subsystems).
//! Each such interaction is reproduced as a `// W6-DEFER[api]` stub returning the
//! null/empty value (`Id::NONE`/`INVALID`/`false`), so the surrounding branch + loop
//! structure and order of operations are preserved EXACTLY without fabricating the
//! absent behaviour. Because the propagation-binding-set ENTRY is null until the
//! satellite subsystem lands, the gated inner bodies correctly short-circuit (no
//! bindings exist yet ⇒ no propagation). One method (the dual-map binding-cycle
//! merge, `applyBINDPROPAGATECYCLERule`) is too entangled in the unported
//! `CPropagationBindingMap` merge-iteration to skeletonise usefully and is marked
//! `// PORT-PENDING` with a faithful prose outline; its signature is preserved.
//!
//! The CLEANLY portable rules — the two `applyBINDPROPAGATEAND*` delegators and the
//! four `applyDATA*Rule` rules (whose only unported dependency is the deferred
//! `mDatatypeHandler`, the rest being real concept-arena reads + sibling-rule
//! dispatch) — are ported in FULL.
//!
//! W3.6-RECONCILE-NOTE: since this header was written, much of the propagation-binding
//! satellite subsystem HAS landed — the node lazy-getters
//! (`ctx.node_reapply_concept_label_set` / `…_concept_propagation_binding_set_hash` /
//! `…_concept_variable_binding_path_set_hash`), the satellite-type methods
//! (`get_propagation_binding_set` → `PropagationBindingSetId`,
//! `get_concept_descriptor_and_reapply_queue`, `add_propagation_binding`, …) and ALL the
//! `create*Dependency` wrappers this unit needs are now ported. The four binding rules
//! below nonetheless REMAIN deferred because their cores still depend on subsystems that
//! are unported OR unreconciled: (1) the per-binding emission helpers
//! `propagate_initial/fresh_propagation_bindings` (u33/u34) are still PORT-PENDING
//! skeletons typed on opaque `Cint64`, NOT the `PropagationBindingSetId` the satellite
//! lookups now return — they cannot be called without first reconciling their signatures
//! (an edit to u33/u34, out of scope for this unit); (2) `mGroundingHandler`
//! (grounding rule), the answerer message adapter (finalize rule), `mDatatypeHandler`
//! (data rules) and the `CReapplyRoleSuccessorHash` satellite + iterator (the ∀-fan-out
//! loop) are all still unported. Each blocked site below carries a `// RECONCILE-NEED:`
//! naming exactly what must land first.

#![allow(dead_code, unused_variables, unused_mut, unused_assignments)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, RoleId, VariableId};
use super::super::process::{
    ConDescId, ConProcDescId, EdgeId, LabelSetId, NodeId, RoleSuccHashId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDFINALIZERule`.
    pub fn apply_varbind_finalize_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_des_id = *con_pro_des;
        // conDes = conProDes->getConceptDescriptor()
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_concept_descriptor();
        // concept = conDes->getConcept()
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        let concept_negation: bool = negate;
        // depTrackPoint = conProDes->getDependencyTrackPoint()
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        // opConLinker = concept->getOperandList()  (read; finalize does not iterate it)

        // procDataBox = calcAlgContext->getUsedProcessingDataBox()  (reachable databox)
        // W6-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;

        // W6-DEFER[api]: conSet = processIndi->getReapplyConceptLabelSet(false)
        //               (node label-set satellite getter not yet ported, node.rs = PN-1)
        let mut con_set: LabelSetId = Id::NONE;

        // W6-DEFER[macro]: STATINC(VARBINDRULEANDAPPLICATIONCOUNT, calcAlgContext)

        // topConcept = procDataBox->getOntologyTopConcept()  (real databox read)
        let top_concept: ConceptId = calc_alg_context.processing_data_box().ontology_top_concept();

        // W6-DEFER[api]: answererMessageAdapter =
        //   calcAlgContext->getSatisfiableCalculationTask()
        //                 ->getSatisfiableAnswererBindingPropagationAdapter()
        // (the answerer Task/message-adapter subsystem is not ported; null ⇒ the
        //  finalize-with-clashing / finalize-with-binding-extraction block is skipped)
        // RECONCILE-NEED: answerer message adapter + AnswererPropagationSteeringController
        //   + MarkerIndividualNodeHash (Task/W4.5 sat sub-structs) — until they land this
        //   whole finalize body stays a faithful no-op; the createVARBINDPROPAGATEANDDependency
        //   site here is reachable only inside the adapter-gated branch.
        let answerer_message_adapter: Cint64 = INVALID;
        if answerer_message_adapter != INVALID {
            // W6-DEFER[api]: propagationSteeringController =
            //   answererMessageAdapter->getAnswererPropagationSteeringController()
            let propagation_steering_controller: Cint64 = INVALID;
            if propagation_steering_controller != INVALID {
                // W6-DEFER[api]: propagationSteeringController->finalizeWithClashing()
                let finalize_with_clashing = false;
                if finalize_with_clashing {
                    let mut next_dep_track_point: TrackPointId = Id::NONE;
                    if next_dep_track_point == Id::NONE {
                        // W6-DEFER[api]: conSet = processIndi->getReapplyConceptLabelSet(true)
                        con_set = Id::NONE;
                        // W6-DEFER[api]: createVARBINDPROPAGATEANDDependency(
                        //   nextDepTrackPoint, processIndi, conDes, depTrackPoint, calcAlgContext)
                        next_dep_track_point = Id::NONE;
                    }
                    // W6-DEFER[api]: addConceptToIndividualReturnConceptDescriptor(
                    //   topConcept, true, processIndi, nextDepTrackPoint, false, false, calcAlgContext)
                }
                // W6-DEFER[api]: propagationSteeringController->finalizeWithBindingExtraction()
                let finalize_with_binding_extraction = false;
                if finalize_with_binding_extraction {
                    let mut nondeterministically = true;
                    if dep_track_point != Id::NONE {
                        // W6-DEFER[api]: depTrackPoint->getBranchingTag() <= 0
                        let branching_tag: Cint64 = 0;
                        if branching_tag <= 0 {
                            nondeterministically = false;
                        }
                    }
                    // W6-DEFER[api]: calcAlgContext->getProcessingDataBox()
                    //   ->getMarkerIndividualNodeHash(true)
                    //   ->addMarkerIndividualNode(concept, processIndi, nondeterministically)
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyBINDPROPAGATEGROUNDINGRule`.
    ///
    /// Reachable prelude is real; the grounding body is gated on the unported
    /// propagation-binding-set hash (entry null ⇒ short-circuits, matching C++
    /// `if (propBindSet) { … }`). The grounding-linker production (`mGroundingHandler`),
    /// the dependency factory and the node label-set/queue satellites are deferred.
    pub fn apply_bind_propagate_grounding_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_des_id = *con_pro_des;
        // W6-DEFER[memory-pool]: taskMemMan
        let task_mem_man: Cint64 = INVALID;

        // conDes / depTrackPoint / concept / negated / opCount / opConLinker (real reads)
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_concept_descriptor();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        let negated: bool = calc_alg_context.process_context().con_desc(con_des).is_negated();
        let op_count: Cint64 = calc_alg_context.ontology_arenas().concept(concept).get_operand_count();
        let op_con_linker: Vec<NegLink<ConceptId>> =
            calc_alg_context.ontology_arenas().concept(concept).get_operand_list().to_vec();

        // W6-DEFER[api]: conSet = processIndi->getReapplyConceptLabelSet(false)
        let mut con_set: LabelSetId = Id::NONE;

        // W6-DEFER[api]: conPropBindSetHash = processIndi->getConceptPropagationBindingSetHash(false)
        //               propBindSet = conPropBindSetHash->getPropagationBindingSet(concept, false)
        // The node satellite getter (`ctx.node_concept_propagation_binding_set_hash`) and
        // the set lookup (`ConceptPropagationBindingSetHash::get_propagation_binding_set`,
        // → `PropagationBindingSetId`) NOW exist; but the grounding body below is gated on
        // `mGroundingHandler->getGroundingConceptLinker(...)`, which is unported, so the
        // whole body still short-circuits (newGroundedLinker stays null). The read is left
        // as the `INVALID` short-circuit to keep the dead body inert until grounding lands.
        // RECONCILE-NEED: CConceptNominalSchemaGroundingHandler (`mGroundingHandler`) —
        //   getGroundingConceptLinker + groundedConPropBindDesHash/additionalPropBindDesHash;
        //   once present, wire conSet/conPropBindSetHash node-getters + the dep creators
        //   (create_bind_propagate_grounding_dependency / create_propagate_connection_dependency,
        //   both already ported) + propagate_initial/fresh helpers (see RECONCILE-NEED below).
        let prop_bind_set: Cint64 = INVALID;

        if prop_bind_set != INVALID {
            // W6-DEFER[macro]: STATINC(PBINDRULEGROUNDINGAPPLICATIONCOUNT, calcAlgContext)

            if op_con_linker.is_empty() {
                // --- no operands: directly ground the concept ---
                // W6-DEFER[api]: newGroundedLinker = mGroundingHandler->getGroundingConceptLinker(
                //   processIndi, propBindSet, concept, negated,
                //   groundedConPropBindDesHash, additionalPropBindDesHash, calcAlgContext)
                let new_grounded_linker: Cint64 = INVALID;
                if new_grounded_linker != INVALID {
                    // for each newGroundedConcept in newGroundedLinker:
                    //   STATINC(PBINDGROUNDINGCOUNT)
                    //   collect baseDependencyTrackPoint + additionalsDependencies from
                    //     groundedConPropBindDesHash / additionalPropBindDesHash via
                    //     createPROPAGATECONNECTIONDependency(...)   [W6-DEFER[api] dep factory]
                    //   nextDepTrackPoint = createBINDPROPAGATEGROUNDINGDependency(...)  [W6-DEFER]
                    //   addConceptToIndividual(newGroundedConcept, neg, processIndi,
                    //     nextDepTrackPoint, true, false, calcAlgContext)  [W6-DEFER[api]]
                    // W6-DEFER[api]: grounded-concept emission (unported grounding subsystem)
                }
            } else {
                // --- has operands: ground + propagate per binding trigger ---
                // W6-DEFER[api]: newGroundedLinker = mGroundingHandler->getGroundingConceptLinker(...)
                let new_grounded_linker: Cint64 = INVALID;
                if new_grounded_linker != INVALID {
                    for op_con_linker_it in op_con_linker.iter() {
                        let binding_trigger_concept: ConceptId = op_con_linker_it.target;
                        let binding_trigger_concept_negation: bool = op_con_linker_it.negated;

                        let mut binding_con_des: ConDescId = Id::NONE;
                        let mut binding_dep_track_point: TrackPointId = Id::NONE;
                        let mut reapply_queue: Cint64 = INVALID;

                        // W6-DEFER[api]: prevPropBindingSet = propBindSet;
                        //   newPropBindingSet = conPropBindSetHash->getPropagationBindingSet(
                        //     bindingTriggerConcept, true)
                        let mut created_bind_concept = false;
                        let mut done_bind_propagations = false;

                        // W6-DEFER[api]: conSet->getConceptDescriptorAndReapplyQueue(
                        //   bindingTriggerConcept, bindingConDes, bindingDepTrackPoint, reapplyQueue)
                        let has_con_des_and_queue = false;
                        if !has_con_des_and_queue {
                            // create the binding-trigger concept + grounding dependency
                            //   baseDependencyTrackPoint from groundedConPropBindDesHash /
                            //     additionalPropBindDesHash (createPROPAGATECONNECTIONDependency)
                            //   nextDepTrackPoint = createBINDPROPAGATEGROUNDINGDependency(...)
                            //   bindingConDes = addConceptToIndividualReturnConceptDescriptor(...)
                            //   conSet = processIndi->getReapplyConceptLabelSet(true)
                            // W6-DEFER[api]: binding-trigger concept creation (dep factory + node satellites)
                            created_bind_concept = true;
                        }

                        // for each newGroundedConcept: add fresh propagation bindings to
                        //   newPropBindingSet (createPROPAGATEBINDINGDependency + new
                        //   CPropagationBindingDescriptor) when not already contained.
                        // W6-DEFER[api]: propagation-binding emission (unported binding subsystem)

                        if done_bind_propagations {
                            if !created_bind_concept {
                                // W6-DEFER[api]: propagateFreshPropagationBindings(processIndi, conDes,
                                //   newPropBindingSet, prevPropBindingSet, nullptr, calcAlgContext)
                                let propagated_fresh = false;
                                if propagated_fresh {
                                    // W6-DEFER[api]: setIndividualNodeConceptLabelSetModified(...)
                                    // W6-DEFER[api]: conProQueue = processIndi->getConceptProcessingQueue(true)
                                    // W6-DEFER[api]: addConceptPreprocessedToProcessingQueue(
                                    //   bindingConDes, bindingDepTrackPoint, conProQueue, processIndi, true, ...)
                                    // if (!reapplyQueue->isEmpty()) { reapply iterator over conSet }
                                    // W6-DEFER[api]: applyReapplyQueueConcepts(processIndi, &reapplyQueueIt, ...)
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyBINDPROPAGATECYCLERule`.
    ///
    /// PORT-PENDING: the reachable prelude (conDes/concept/operand-trigger reads) is
    /// faithful, but the body is a synchronised dual-iteration merge over two
    /// `CPropagationBindingMap`s (`cyclePropConceptBindingMap` × `cycleTriggerConcept
    /// BindingMap`) of the unported propagation-binding satellite subsystem, plus the
    /// dependency factory and the per-binding reapply-install path. It is too
    /// entangled in absent types to skeletonise without fabricating their merge
    /// semantics; the signature is preserved and the full C++ algorithm is recorded
    /// below for the reconcile pass once the binding subsystem lands.
    ///
    /// C++ outline (cpp 13048-13288):
    /// ```text
    /// read conDes/depTrackPoint/concept/opCount/opLinker
    /// bindingTriggerConcept = opLinker[0]; cycleTriggerConcept = opLinker[1]
    /// conSet = getReapplyConceptLabelSet(false)
    /// // decide addCycleCloseConcept / testCycleBindingClosed via
    /// //   conSet->getConceptDescriptorAndReapplyQueue / getConceptDescriptor
    /// if testCycleBindingClosed:
    ///   conPropBindingSetHash = getConceptPropagationBindingSetHash(false)
    ///   cycleTriggerConceptBindingSet / cyclePropConceptBindingSet lookups;
    ///   cycleTriggerConceptNewBinding = newSpecialPropagationBindingDescriptor->binding
    ///   cycleBindingPropagation = (cyclePropagationConceptDescriptor != null)
    /// if cycleBindingPropagation:
    ///   STATINC(PBINDRULECYCLEAPPLICATIONCOUNT)
    ///   if addCycleCloseConcept: createBINDPROPAGATECYCLEDependency + addConcept…
    ///   merge-iterate cyclePropConceptBindingMap (itCycle) vs
    ///     cycleTriggerConceptBindingMap (itTrigger):
    ///       triggerID < cycleID -> ++itTrigger
    ///       triggerID == cycleID -> propagate cycle binding into newPropBindSet
    ///         (createPROPAGATECONNECTIONDependency ×2 + createPROPAGATEBINDINGDependency,
    ///          new CPropagationBindingDescriptor into newPropBindMap, apply reapply queue)
    ///       else -> cross-individual cycle close: resolve bindedIndiNode via
    ///         getUpToDateIndividual + getCorrectedMergedIntoIndividualNode, look up
    ///         its binding set; if trigger binding present, propagate; else install a
    ///         CPropagationBindingReapplyConceptDescriptor on the binded individual.
    ///   if newPropBindSet && newPropBindDesLinker: addPropagationBindingDescriptorLinker
    /// if propagations && !addCycleCloseConcept:
    ///   setIndividualNodeConceptLabelSetModified; addConceptPreprocessedToProcessingQueue;
    ///   reapply queue iterator if non-empty
    /// if !isConceptInReapplyQueue(conDes, cycleTriggerConcept, !cycleTriggerConceptNegation, …):
    ///   addConceptToReapplyQueue(conDes, cycleTriggerConcept, !cycleTriggerConceptNegation, …)
    /// ```
    pub fn apply_bind_propagate_cycle_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_des_id = *con_pro_des;
        // conDes / depTrackPoint / concept (real reads)
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_concept_descriptor();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        let op_linker: Vec<NegLink<ConceptId>> =
            calc_alg_context.ontology_arenas().concept(concept).get_operand_list().to_vec();
        // bindingTriggerConcept = opLinker[0], cycleTriggerConcept = opLinker[1]
        let binding_trigger_concept: ConceptId =
            op_linker.first().map(|l| l.target).unwrap_or(Id::NONE);
        let binding_trigger_concept_negation: bool =
            op_linker.first().map(|l| l.negated).unwrap_or(false);
        let cycle_trigger_concept: ConceptId =
            op_linker.get(1).map(|l| l.target).unwrap_or(Id::NONE);
        let cycle_trigger_concept_negation: bool =
            op_linker.get(1).map(|l| l.negated).unwrap_or(false);

        // PORT-PENDING: dual-map propagation-binding merge (see outline above).
        // Now-available: the propagation-binding satellite types
        // (binding_hash/propagation_binding), the dep creators
        // (create_bind_propagate_cycle_dependency / create_propagate_connection_dependency /
        // create_propagate_binding_dependency, all ported), and the cross-individual
        // resolver `get_corrected_merged_into_individual_node` (u14, ported) + `get_up_to_date_individual`.
        // Still-blocked: the per-binding emission path runs through
        // `propagate_*_propagation_bindings` (u33/u34), which are PORT-PENDING skeletons
        // typed on opaque `Cint64`, not the `PropagationBindingSetId` the satellite
        // lookups now return; and the `CPropagationBindingMap` sorted dual-iteration
        // (itCycle vs itTrigger) merge-walk accessor is not exposed yet.
        // RECONCILE-NEED: reconcile u33/u34 propagate_initial/fresh_propagation_bindings
        //   from `Cint64` to `PropagationBindingSetId`/`PropagationBindingSetHandle`, and
        //   expose a `CPropagationBindingMap` ordered-iterator pair, before this merge can
        //   be ported faithfully.
        todo!(
            "applyBINDPROPAGATECYCLERule body needs the propagation-binding emission helpers \
             (u33/u34) reconciled to PropagationBindingSetId + a CPropagationBindingMap \
             dual-iteration accessor"
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyBINDPROPAGATEALLRule`.
    pub fn apply_bind_propagate_all_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_des_id = *con_pro_des;
        // conDes / concept / role / depTrackPoint / opCount / opLinker (real reads)
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        let role: RoleId = calc_alg_context.ontology_arenas().concept(concept).get_role();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let op_count: Cint64 = calc_alg_context.ontology_arenas().concept(concept).get_operand_count();
        // opLinker / conceptOpLinker = concept->getOperandList() (passed to the
        // propagation helper; not iterated here)

        // W6-DEFER[macro]: STATINC(PBINDRULEALLAPPLICATIONCOUNT, calcAlgContext)

        // restLink = getLinkProcessingRestriction(conProDes)  (sibling helper, unit u03)
        let rest_link: EdgeId = self.get_link_processing_restriction(con_pro_des_id, calc_alg_context);
        if rest_link != Id::NONE {
            // succIndi = getSuccessorIndividual(processIndi, restLink, calcAlgContext)
            let mut succ_indi: NodeId = self.get_successor_individual(process_indi, rest_link, calc_alg_context);
            // propagatePropagationBindingsToSuccessor(processIndi, succIndi, opLinker, negate,
            //   conDes, restLink, calcAlgContext)
            self.propagate_propagation_bindings_to_successor(
                *process_indi,
                &mut succ_indi,
                concept,
                negate,
                con_des,
                rest_link,
                calc_alg_context,
            );
        } else {
            // W6-DEFER[api]: roleSuccHash = processIndi->getReapplyRoleSuccessorHash(false)
            //   (node role-successor-hash satellite getter not yet ported ⇒ null ⇒
            //    no successor links to propagate over)
            // RECONCILE-NEED: `CReapplyRoleSuccessorHash` + `CRoleSuccessorLinkIterator`
            //   are still W2-DEFER stubs (process/pn3.rs get_reapply_role_successor_hash
            //   does not allocate; process/rs1.rs get_role_successor_link_iterator returns a
            //   non-functional unit). The successor-propagation helper
            //   (propagate_propagation_bindings_to_successor) + get_successor_individual are
            //   ready; only the role-successor-hash satellite/iterator block this loop.
            let role_succ_hash: RoleSuccHashId = Id::NONE;
            if role_succ_hash != Id::NONE {
                // roleSuccIt = roleSuccHash->getRoleSuccessorLinkIterator(role)
                // while (roleSuccIt.hasNext()) {
                //   link = roleSuccIt.next(true)
                //   succIndi = getSuccessorIndividual(processIndi, link, calcAlgContext)
                //   propagatePropagationBindingsToSuccessor(processIndi, succIndi, opLinker,
                //     negate, conDes, link, calcAlgContext)
                // }
                // W6-DEFER[api]: role-successor iteration (unported role-succ-hash satellite)
            }
        }
        // if (!conProDes->isConceptReapplied())
        let is_concept_reapplied = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .is_concept_reapplied();
        if !is_concept_reapplied {
            // if (!isConceptInReapplyQueue(conDes, role, processIndi, calcAlgContext))
            if !self.is_concept_in_reapply_queue_role(con_des, role, *process_indi, calc_alg_context) {
                // addConceptToReapplyQueue(conDes, role, processIndi, true, depTrackPoint, calcAlgContext)
                self.add_concept_to_reapply_queue_role(
                    con_des,
                    role,
                    *process_indi,
                    true,
                    dep_track_point,
                    calc_alg_context,
                );
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyBINDPROPAGATEIMPLICATIONRule`.
    ///
    /// Reachable prelude (conDes/concept/operand-trigger reads + the trigger
    /// availability search) is faithful; the propagation-binding-set creation and the
    /// fresh-binding propagation are gated behind the unported binding subsystem and
    /// the dependency factory (`createCONNECTION` / `createBINDPROPAGATEIMPLICATION`),
    /// kept as control-flow-preserving `// W6-DEFER[api]` stubs.
    pub fn apply_bind_propagate_implication_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_des_id = *con_pro_des;
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let op_count: Cint64 = calc_alg_context.ontology_arenas().concept(concept).get_operand_count();
        let op_linker: Vec<NegLink<ConceptId>> =
            calc_alg_context.ontology_arenas().concept(concept).get_operand_list().to_vec();

        // W6-DEFER[memory-pool]: taskMemMan
        // W6-DEFER[macro]: STATINC(PBINDRULEIMPLICATIONAPPLICATIONCOUNT, calcAlgContext)

        // W6-DEFER[api]: conSet = processIndi->getReapplyConceptLabelSet(false)
        let mut con_set: LabelSetId = Id::NONE;
        let mut binding_con_des: ConDescId = Id::NONE;
        let mut binding_dep_track_point: TrackPointId = Id::NONE;
        let mut reapply_queue: Cint64 = INVALID;

        // bindingTriggerConcept = opLinker[0]; triggerLinker = opLinker[1..]
        let binding_trigger_concept: ConceptId =
            op_linker.first().map(|l| l.target).unwrap_or(Id::NONE);
        let binding_trigger_concept_negation: bool =
            op_linker.first().map(|l| l.negated).unwrap_or(false);
        let trigger_linker: Vec<NegLink<ConceptId>> = op_linker.iter().skip(1).copied().collect();

        // W6-DEFER[api]: conSet->getConceptDescriptorAndReapplyQueue(
        //   bindingTriggerConcept, bindingConDes, bindingDepTrackPoint, reapplyQueue)
        let has_binding_con_des_and_queue = false;
        if !has_binding_con_des_and_queue {
            // search next not-existing trigger
            let mut all_triggers_available = true;
            // W6-DEFER[api]: conSet = processIndi->getReapplyConceptLabelSet(true)
            con_set = Id::NONE;
            let mut missing_trigger_index: Option<usize> = None;
            for (i, next_trigger) in trigger_linker.iter().enumerate() {
                let trigger_concept: ConceptId = next_trigger.target;
                // W6-DEFER[api]: conSet->getConceptDescriptor(triggerConcept, triggerConDes, …)
                let has_trigger_con_des = false;
                let trigger_con_des_negated = false;
                if has_trigger_con_des {
                    if trigger_con_des_negated == next_trigger.negated {
                        return;
                    }
                } else {
                    all_triggers_available = false;
                    missing_trigger_index = Some(i);
                    break;
                }
            }

            if !all_triggers_available {
                // install to the first missing trigger
                if let Some(i) = missing_trigger_index {
                    let next_trigger = trigger_linker[i];
                    let trigger_concept: ConceptId = next_trigger.target;
                    let trigger_negation: bool = !next_trigger.negated;
                    if !self.is_concept_in_reapply_queue_concept(
                        con_des,
                        trigger_concept,
                        trigger_negation,
                        *process_indi,
                        calc_alg_context,
                    ) {
                        self.add_concept_to_reapply_queue_concept(
                            con_des,
                            trigger_concept,
                            trigger_negation,
                            *process_indi,
                            false,
                            dep_track_point,
                            calc_alg_context,
                        );
                    }
                }
            } else {
                // collect trigger dependencies, create the implication binding concept
                // and propagate the initial bindings.
                // for each trigger: createCONNECTIONDependency(processIndi, triggerConDes, …)
                // W6-DEFER[api]: triggerDeps connection-dependency chain (dep factory)
                // nextDepTrackPoint = createBINDPROPAGATEIMPLICATIONDependency(...)
                // bindingConDes = addConceptToIndividualReturnConceptDescriptor(
                //   bindingTriggerConcept, bindingTriggerConceptNegation, processIndi, …)
                // conPropBindingSetHash = processIndi->getConceptPropagationBindingSetHash(true)
                // prevPropBindingSet = …getPropagationBindingSet(concept, false)
                // propBindingSet = …getPropagationBindingSet(bindingTriggerConcept, true)
                // propBindingSet->setConceptDescriptor(bindingConDes)
                // propagateInitialPropagationBindings(processIndi, bindingConDes,
                //   propBindingSet, prevPropBindingSet, triggerDeps, calcAlgContext)
                // W6-DEFER[api]: implication binding creation + initial propagation
                // Now-available: create_connection_dependency (u29) +
                // create_bind_propagate_implication_dependency (ported),
                // add_concept_to_individual_return_concept_descriptor (u36),
                // node_concept_propagation_binding_set_hash + get_propagation_binding_set
                // (→ PropagationBindingSetId) + set_concept_descriptor.
                // RECONCILE-NEED: the final `propagate_initial_propagation_bindings` (u33)
                //   still takes opaque `Cint64`, not `PropagationBindingSetId`; reconcile its
                //   signature (and u34's `propagate_fresh_*`) before wiring this branch, else
                //   the set id cannot be passed. Left deferred to avoid editing u33/u34 here.
            }
        } else {
            // existing binding concept: refresh propagated bindings
            // collect trigger dependencies (createCONNECTIONDependency)
            // conPropBindingSetHash = processIndi->getConceptPropagationBindingSetHash(true)
            // prevPropBindingSet / propBindingSet lookups
            // W6-DEFER[api]: propagateFreshPropagationBindings(processIndi, conDes,
            //   propBindingSet, prevPropBindingSet, triggerDeps, calcAlgContext)
            let propagated_fresh = false;
            if propagated_fresh {
                // W6-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi, …)
                // W6-DEFER[api]: conProQueue = processIndi->getConceptProcessingQueue(true)
                // W6-DEFER[api]: addConceptPreprocessedToProcessingQueue(
                //   bindingConDes, bindingDepTrackPoint, conProQueue, processIndi, true, …)
                // if (!reapplyQueue->isEmpty()) reapply iterator over conSet
                // W6-DEFER[api]: applyReapplyQueueConcepts(processIndi, &reapplyQueueIt, …)
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyBINDPROPAGATEANDRule`.
    pub fn apply_bind_propagate_and_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // propagatePropagationBindings(processIndi, conProDes, negate, false, calcAlgContext)
        self.propagate_propagation_bindings(process_indi, con_pro_des, negate, false, calc_alg_context);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyBINDPROPAGATEANDFLAGALLRule`.
    pub fn apply_bind_propagate_and_flag_all_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // ++mStatBackPropActivationCount
        self.stat_back_prop_activation_count += 1;
        // propagatePropagationBindings(processIndi, conProDes, negate, true, calcAlgContext)
        self.propagate_propagation_bindings(process_indi, con_pro_des, negate, true, calc_alg_context);
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyBINDVARIABLERule`.
    ///
    /// Reachable prelude (conDes/concept/variable/operand-trigger reads) is faithful;
    /// the propagation-binding-set creation + `CPropagationBinding` allocation and the
    /// fresh-binding propagation are gated behind the unported binding subsystem, kept
    /// as control-flow-preserving `// W6-DEFER[api]` stubs.
    pub fn apply_bind_variable_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_des_id = *con_pro_des;
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        // variable = concept->getVariable()
        let variable: Option<VariableId> = calc_alg_context.ontology_arenas().concept(concept).get_variable();
        let concept_negation: bool = negate;
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let op_con_linker: Vec<NegLink<ConceptId>> =
            calc_alg_context.ontology_arenas().concept(concept).get_operand_list().to_vec();

        // bindingTriggerConcept = opConLinker[0]
        let binding_trigger_concept: ConceptId =
            op_con_linker.first().map(|l| l.target).unwrap_or(Id::NONE);
        let binding_trigger_concept_negation: bool =
            op_con_linker.first().map(|l| l.negated).unwrap_or(false);

        // processContext / procDataBox reachable; W6-DEFER[memory-pool]: taskMemMan
        // W6-DEFER[api]: conSet = processIndi->getReapplyConceptLabelSet(false)
        let mut con_set: LabelSetId = Id::NONE;
        let mut binding_con_des: ConDescId = Id::NONE;
        let mut binding_dep_track_point: TrackPointId = Id::NONE;
        let mut reapply_queue: Cint64 = INVALID;

        // W6-DEFER[macro]: STATINC(PBINDRULEBINDNAPPLICATIONCOUNT, calcAlgContext)

        // W6-DEFER[api]: conSet->getConceptDescriptorAndReapplyQueue(
        //   bindingTriggerConcept, bindingConDes, bindingDepTrackPoint, reapplyQueue)
        let has_binding_con_des_and_queue = false;
        if !has_binding_con_des_and_queue {
            // W6-DEFER[macro]: STATINC(PBINDVARIABLEBINDCOUNT, calcAlgContext)
            // nextDepTrackPoint = createBINDVARIABLEDependency(...)  [W6-DEFER dep factory]
            // conSet = processIndi->getReapplyConceptLabelSet(true)
            // bindingConDes = addConceptToIndividualReturnConceptDescriptor(
            //   bindingTriggerConcept, bindingTriggerConceptNegation, processIndi, …)
            // conPropBindingSetHash = processIndi->getConceptPropagationBindingSetHash(true)
            // prevPropBindingSet/propBindingSet lookups; propBindingSet->setConceptDescriptor(...)
            // propagateInitialPropagationBindings(processIndi, bindingConDes,
            //   propBindingSet, prevPropBindingSet, nullptr, calcAlgContext)
            // propVarBinding = new CPropagationBinding(nextPropBindingID, …, variable)
            //   nextPropBindingID = procDataBox->getNextBindingPropagationID(true)
            // propBindDes = new CPropagationBindingDescriptor(propVarBinding, nextDepTrackPoint)
            // propBindingSet->addPropagationBinding(propBindDes, true)
            // W6-DEFER[api]: fresh variable-binding creation
            // Now-available: create_bind_variable_dependency (ported),
            // add_concept_to_individual_return_concept_descriptor (u36),
            // node_concept_propagation_binding_set_hash + get_propagation_binding_set,
            // add_propagation_binding / get_new_special_propagation_binding_descriptor
            // (process/propagation_binding.rs).
            // RECONCILE-NEED: (a) `propagate_initial_propagation_bindings` (u33) takes
            //   opaque `Cint64`, not `PropagationBindingSetId` — reconcile before wiring;
            //   (b) the `CPropagationBinding(Descriptor)` constructors + the databox
            //   `getNextBindingPropagationID` are needed to allocate the new variable binding.
            //   Left deferred to avoid editing u33/u34/databox here.
        } else {
            // existing binding concept
            // conPropBindingSetHash = processIndi->getConceptPropagationBindingSetHash(true)
            // prevPropBindingSet/propBindingSet lookups
            let mut new_var_bind_created = false;
            // W6-DEFER[api]: propBindingSet->getNewSepcialPropagationBindingDescriptor()
            let has_new_special_binding_descriptor = false;
            if !has_new_special_binding_descriptor {
                // W6-DEFER[macro]: STATINC(PBINDVARIABLEBINDCOUNT, calcAlgContext)
                // nextDepTrackPoint = createBINDVARIABLEDependency(...)
                // propVarBinding/propBindDes allocation + addPropagationBinding(propBindDes, true)
                // W6-DEFER[api]: new variable binding allocation (unported binding subsystem)
                new_var_bind_created = true;
            }

            // W6-DEFER[api]: propagateFreshPropagationBindings(processIndi, conDes,
            //   propBindingSet, prevPropBindingSet, nullptr, calcAlgContext)
            let propagated_fresh = false;
            if propagated_fresh || new_var_bind_created {
                // W6-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi, …)
                // W6-DEFER[api]: conProQueue = processIndi->getConceptProcessingQueue(true)
                // W6-DEFER[api]: addConceptPreprocessedToProcessingQueue(
                //   bindingConDes, bindingDepTrackPoint, conProQueue, processIndi, true, …)
                // if (!reapplyQueue->isEmpty()) reapply iterator over conSet
                // W6-DEFER[api]: applyReapplyQueueConcepts(processIndi, &reapplyQueueIt, …)
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyDATATYPERule`.
    pub fn apply_datatype_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_des_id = *con_pro_des;
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();

        // if (mDatatypeHandler && mConfDatatypeReasoning)
        //   mDatatypeHandler->addDatatype(processIndi, concept, negate, depTrackPoint, calcAlgContext)
        if self.datatype_handler != Id::NONE && self.conf_datatype_reasoning {
            // W6-DEFER[api]: mDatatypeHandler->addDatatype(...)  (datatype value-space handler not ported)
        }

        // if (!negate || concept->getOperandCount() <= 1) applyANDRule else applyORRule
        let op_count: Cint64 = calc_alg_context.ontology_arenas().concept(concept).get_operand_count();
        if !negate || op_count <= 1 {
            self.apply_and_rule(process_indi, con_pro_des, negate, calc_alg_context);
        } else {
            self.apply_or_rule(process_indi, con_pro_des, negate, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyDATARESTRICTIONRule`.
    pub fn apply_data_restriction_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_des_id = *con_pro_des;
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();

        // if (mDatatypeHandler && mConfDatatypeReasoning)
        //   mDatatypeHandler->addDataRestriction(processIndi, concept, negate, depTrackPoint, calcAlgContext)
        if self.datatype_handler != Id::NONE && self.conf_datatype_reasoning {
            // W6-DEFER[api]: mDatatypeHandler->addDataRestriction(...)  (datatype handler not ported)
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyDATALITERALRule`.
    pub fn apply_data_literal_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_des_id = *con_pro_des;
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        // dataLiteral = concept->getDataLiteral()
        // KONCLUDE-PORT-NOTE[api]: CDataLiteral* is an opaque `Cint64` handle (the
        // concrete data-literal model is not ported); `INVALID` == `nullptr`.
        let data_literal: Cint64 = calc_alg_context.ontology_arenas().concept(concept).get_data_literal();
        if data_literal != INVALID {
            let dep_track_point: TrackPointId = calc_alg_context
                .process_context()
                .con_proc_desc(con_pro_des_id)
                .get_dependency_track_point();

            // if (mDatatypeHandler && mConfDatatypeReasoning)
            //   mDatatypeHandler->addDataLiteral(processIndi, dataLiteral, negate, depTrackPoint, calcAlgContext)
            if self.datatype_handler != Id::NONE && self.conf_datatype_reasoning {
                // W6-DEFER[api]: mDatatypeHandler->addDataLiteral(...)  (datatype handler not ported)
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyDATALITERALIMPLICATIONRule`.
    pub fn apply_data_literal_implication_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_pro_des_id = *con_pro_des;
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        // dataLiteral = concept->getDataLiteral()  ([api] opaque handle)
        let data_literal: Cint64 = calc_alg_context.ontology_arenas().concept(concept).get_data_literal();
        if data_literal != INVALID {
            let dep_track_point: TrackPointId = calc_alg_context
                .process_context()
                .con_proc_desc(con_pro_des_id)
                .get_dependency_track_point();
            // triggerConcept = concept->getOperandList()->getData()  (first operand)
            let trigger_concept: ConceptId =
                calc_alg_context.ontology_arenas().concept(concept).get_operand_list().first()
                    .map(|l| l.target)
                    .unwrap_or(Id::NONE);
            let mut triggered_concepts: ConDescId = Id::NONE;
            // if (mDatatypeHandler && mConfDatatypeReasoning) {
            //   mDatatypeHandler->triggerDataLiteralConcept(processIndi, dataLiteral, negate,
            //     depTrackPoint, triggerConcept, triggeredConcepts, calcAlgContext)
            //   if (triggeredConcepts) addtriggeredValueSpaceConcepts(processIndi, triggeredConcepts, calcAlgContext)
            // }
            if self.datatype_handler != Id::NONE && self.conf_datatype_reasoning {
                // W6-DEFER[api]: mDatatypeHandler->triggerDataLiteralConcept(...) — sets triggeredConcepts
                // (datatype handler not ported ⇒ triggeredConcepts stays null ⇒ the
                //  addtriggeredValueSpaceConcepts emission below does not fire)
                if triggered_concepts != Id::NONE {
                    // addtriggeredValueSpaceConcepts(processIndi, triggeredConcepts, calcAlgContext)
                    self.addtriggered_value_space_concepts(*process_indi, triggered_concepts, calc_alg_context);
                }
            }
        }
    }
}
