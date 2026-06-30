//! `completion::u11` — W3 method-batch unit #11 (Variable-binding / binding-propagation family).
//!
//! Ports the 11 methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! that implement the variable-binding-path propagation / join machinery used by
//! the answering-propagation rules (`applyVARBIND*Rule`, ported as stubs in u06),
//! per `manifest/01-completion-methods.md` Unit 11:
//!   - `hasCommonVariableBindings`                 [10617-10647]
//!   - `propagateInitialVariableBindings`          [11581-11609]
//!   - `propagateFreshVariableBindings`            [11612-11666]
//!   - `propagateVariableBindingsToSuccessor`      [11671-11734]
//!   - `propagateInitialVariableBindingsToSuccessor` [11741-11769]
//!   - `propagateFreshVariableBindingsToSuccessor` [11774-11830]
//!   - `propagateVariableBindingsJoins`            [12226-12285]
//!   - `createVariableBindingPathKey`              [12291-12317]
//!   - `triggerVariableBindingPathJoining`         [12321-12336]
//!   - `forceVariableBindingJoinCreated`           [12341-12349]
//!   - `getJoinedVariableBindingPath`              [12353-12413]
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ pointer-to-pointer out-params
//! (`CIndividualProcessNode*& processIndi`, `CConceptDescriptor*& joinConDes`,
//! `CVariableBindingPathSet*& varBindingPathSet`) become `&mut Id`/`&mut Cint64`;
//! by-value node pointers become `NodeId`; the context pointer becomes
//! `&mut CalculationAlgorithmContextBase` (the per-thread context). Ported arena
//! ids (`NodeId`/`ConDescId`/`EdgeId`/`TrackPointId`/`ConceptId`) are used where
//! the referenced type is already ported.
//!
//! KONCLUDE-PORT-NOTE[api]: this whole family is built on the variable-binding-path
//! satellite subsystem — `CVariableBindingPath`, `CVariableBindingPathSet`,
//! `CVariableBindingPathMap`, `CVariableBindingPathDescriptor`, `CVariableBinding`,
//! `CVariableBindingDescriptor`, `CConceptVariableBindingPathSetHash`,
//! `CVariableBindingPathJoiningHash`/`...JoiningData`, `CVariableBindingTriggerHash`,
//! `CVariableBindingPathMergingHash`, `CRepresentativeVariableBindingPathMap` — NONE
//! of which are ported yet, and for none of which the algorithm holds a wired arena
//! handle here. As in u06, every such pointer deref / hash lookup / linker walk is
//! reproduced as a `// W3-DEFER[api]:` stub returning the minimal value
//! (`INVALID`/`Id::NONE`/`false`/`0`), and every iteration over an unported
//! container is reproduced STRUCTURALLY over an empty deferred iterator (`&[]`),
//! preserving the exact branch/loop structure and order of operations (the same
//! empty-slice idiom u06 uses for the operand linkers). The real `self` state that
//! IS ported — the `stat_var_binding_*` counters and `map_comparison_direct_lookup_factor`
//! — is read/mutated faithfully. The unported satellite descriptor allocations are
//! `// W3-DEFER[memory-pool]`. The four dependency-node creators
//! (`createPROPAGATEVARIABLEBINDING*Dependency`, `createVARBINDPROPAGATEJOINDependency`)
//! belong to the merge/dependency family (not this unit) and are `// W3-DEFER[api]`.
//! Unit-11-internal sibling methods are called as real `self.x(...)`.

#![allow(
    unused_variables,
    unused_mut,
    unused_assignments,
    dead_code,
    clippy::collapsible_if,
    clippy::collapsible_else_if
)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::ConceptId;
use super::super::process::{ConDescId, EdgeId, NodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::hasCommonVariableBindings`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `CRepresentativeVariableBindingPathMap*` is unported
    /// → opaque `Cint64`. Its `count()`/`contains(key)`/sorted-key dual-cursor walk
    /// are deferred; only `mMapComparisonDirectLookupFactor` is ported state.
    pub fn has_common_variable_bindings(
        &mut self,
        process_indi: &mut NodeId,
        left_rep_var_bind_map: Cint64,
        right_rep_var_bind_map: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[api]: rightRepVarBindMap->count()
        let right_count: Cint64 = 0;
        // W3-DEFER[api]: leftRepVarBindMap->count()
        let left_count: Cint64 = 0;
        if right_count < left_count {
            return self.has_common_variable_bindings(
                process_indi,
                right_rep_var_bind_map,
                left_rep_var_bind_map,
                calc_alg_context,
            );
        }

        if left_count * self.map_comparison_direct_lookup_factor < right_count {
            // W3-DEFER[api]: for it1 in leftRepVarBindMap: if rightRepVarBindMap->contains(it1.key()) return true
            // (empty deferred iteration — CRepresentativeVariableBindingPathMap unported)
            let left_map_iter: &[Cint64] = &[];
            for _it1 in left_map_iter.iter() {
                // W3-DEFER[api]: rightRepVarBindMap->contains(it1.key())
                let contained = false;
                if contained {
                    return true;
                }
            }
            false
        } else {
            // W3-DEFER[api]: the sorted dual-cursor merge-walk of leftRepVarBindMap /
            // rightRepVarBindMap (advance the smaller key; return true on a shared
            // key1 == key2). Reproduced structurally over empty deferred iterators.
            let left_map_iter: &[Cint64] = &[];
            let right_map_iter: &[Cint64] = &[];
            let mut i1 = 0usize;
            let mut i2 = 0usize;
            while i1 < left_map_iter.len() && i2 < right_map_iter.len() {
                let key1 = left_map_iter[i1];
                let key2 = right_map_iter[i2];
                if key1 == key2 {
                    return true;
                }
                if key1 < key2 {
                    i1 += 1;
                } else if key2 < key1 {
                    i2 += 1;
                }
            }
            false
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateInitialVariableBindings`.
    pub fn propagate_initial_variable_bindings(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        new_var_binding_set: Cint64,
        prev_var_binding_set: Cint64,
        other_dependencies: Cint64,
        con_var_binding_set_hash: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;
        let mut propagations = false;
        // CVariableBindingPathDescriptor* newVarBindPathDesLinker = nullptr;
        let mut new_var_bind_path_des_linker: Cint64 = INVALID;
        if prev_var_binding_set != INVALID {
            // W3-DEFER[api]: newVarBindingSet->copyVariableBindingPaths(prevVarBindingSet->getVariableBindingPathMap())
            // W3-DEFER[api]: CVariableBindingPathMap* varBindMap = newVarBindingSet->getVariableBindingPathMap()
            // Reproduced structurally over an empty deferred iterator (map unported).
            let var_bind_map_iter: &[Cint64] = &[];
            for _it in var_bind_map_iter.iter() {
                self.stat_var_binding_propagate_count += 1;
                self.stat_var_binding_propagate_initial_count += 1;
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDCOUNT, calcAlgContext)
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDINITIALCOUNT, calcAlgContext)
                // W3-DEFER[api]: CVariableBindingPathMapData& varBindPathMapData = it.value()
                // W3-DEFER[api]: prevVarBindPathDes = varBindPathMapData.getVariableBindingPathDescriptor()
                // W3-DEFER[memory-pool]: newVarBindPathDes = allocateAndConstruct<CVariableBindingPathDescriptor>(taskMemMan)
                let new_var_bind_path_des: Cint64 = INVALID;
                let mut new_dep_track_point: TrackPointId = Id::NONE;
                // W3-DEFER[api]: createPROPAGATEVARIABLEBINDINGDependency(newDepTrackPoint, processIndi, conDes, prevVarBindPathDes->getDependencyTrackPoint(), otherDependencies, calcAlgContext)
                // W3-DEFER[api]: newVarBindPathDes->initVariableBindingPathDescriptor(prevVarBindPathDes->getVariableBindingPath(), newDepTrackPoint)
                // W3-DEFER[api]: varBindPathMapData.setVariableBindingPathDescriptor(newVarBindPathDes)
                // W3-DEFER[api]: newVarBindPathDesLinker = newVarBindPathDes->append(newVarBindPathDesLinker)
                new_var_bind_path_des_linker = new_var_bind_path_des;
                propagations = true;
            }
            if new_var_bind_path_des_linker != INVALID {
                // W3-DEFER[api]: newVarBindingSet->addVariableBindingPathDescriptorLinker(newVarBindPathDesLinker)
                // W3-DEFER[api]: conVarBindingSetHash->setLastVariableBindingDescriptionLinker(newVarBindPathDesLinker)
            }
        }
        propagations
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateFreshVariableBindings`.
    pub fn propagate_fresh_variable_bindings(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        new_var_binding_set: Cint64,
        prev_var_binding_set: Cint64,
        other_dependencies: Cint64,
        con_var_binding_set_hash: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;
        let mut propagations = false;
        if prev_var_binding_set != INVALID {
            // W3-DEFER[api]: prevVarBindPathMap = prevVarBindingSet->getVariableBindingPathMap()
            // W3-DEFER[api]: newVarBindPathMap = newVarBindingSet->getVariableBindingPathMap()
            // The sorted merge-walk advances itNew while (newPropID < prevPropID),
            // skips equal keys, and propagates each prev-only key (doPropagation).
            // Reproduced structurally over the prev-only key set (empty deferred).
            let mut new_var_bind_path_des_linker: Cint64 = INVALID;
            let prev_only_iter: &[Cint64] = &[];
            for _it_prev in prev_only_iter.iter() {
                // doPropagation == true for these prev-only keys.
                self.stat_var_binding_propagate_count += 1;
                self.stat_var_binding_propagate_fresh_count += 1;
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDCOUNT, calcAlgContext)
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDFRESHCOUNT, calcAlgContext)
                // W3-DEFER[api]: prevVarBindPathDes = itPrev.value().getVariableBindingPathDescriptor()
                // W3-DEFER[memory-pool]: newVarBindPathDes = allocateAndConstruct<CVariableBindingPathDescriptor>(taskMemMan)
                let new_var_bind_path_des: Cint64 = INVALID;
                let mut new_dep_track_point: TrackPointId = Id::NONE;
                // W3-DEFER[api]: createPROPAGATEVARIABLEBINDINGDependency(newDepTrackPoint, processIndi, conDes, prevVarBindPathDes->getDependencyTrackPoint(), otherDependencies, calcAlgContext)
                // W3-DEFER[api]: varBindingPath = prevVarBindPathDes->getVariableBindingPath()
                // W3-DEFER[api]: newVarBindPathDes->initVariableBindingPathDescriptor(varBindingPath, newDepTrackPoint)
                // W3-DEFER[api]: itNew = newVarBindPathMap->insert(varBindingPath->getPropagationID(), CVariableBindingPathMapData(newVarBindPathDes))
                // W3-DEFER[api]: newVarBindPathDesLinker = newVarBindPathDes->append(newVarBindPathDesLinker)
                new_var_bind_path_des_linker = new_var_bind_path_des;
                propagations = true;
            }
            if new_var_bind_path_des_linker != INVALID {
                // W3-DEFER[api]: newVarBindingSet->addVariableBindingPathDescriptorLinker(newVarBindPathDesLinker)
                // W3-DEFER[api]: conVarBindingSetHash->setLastVariableBindingDescriptionLinker(newVarBindPathDesLinker)
            }
        }
        propagations
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateVariableBindingsToSuccessor`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `processIndi` is by-value (`NodeId`), `succIndi`
    /// is the `*&` out-param (`&mut NodeId`); `conceptOpLinker` is the ported
    /// `CSortedNegLinker<CConcept*>` chain (`&[NegLink<ConceptId>]`, head→tail).
    pub fn propagate_variable_bindings_to_successor(
        &mut self,
        mut process_indi: NodeId,
        succ_indi: &mut NodeId,
        concept_op_linker: &[NegLink<ConceptId>],
        negate: bool,
        con_des: ConDescId,
        rest_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;
        // W3-DEFER[api]: conDes->getDependencyTrackPoint()
        let dep_track_point: TrackPointId = Id::NONE;
        // W3-DEFER[api]: conDes->getConcept()
        let concept: ConceptId = Id::NONE;

        // W3-DEFER[api]: succIndi = getLocalizedIndividual(succIndi, false, calcAlgContext)  [sibling]
        // (deferred — leaves succIndi unchanged)
        // W3-DEFER[api]: CReapplyConceptLabelSet* conSet = succIndi->getReapplyConceptLabelSet(false)
        let mut con_set: Cint64 = INVALID;

        // create dependency
        let mut next_dep_track_point: TrackPointId = Id::NONE;
        let mut continue_propagation = false;

        for concept_op_linker_it in concept_op_linker.iter() {
            let op_concept: ConceptId = concept_op_linker_it.target;
            let op_con_neg: bool = concept_op_linker_it.negated ^ negate;

            let mut binding_con_des: ConDescId = Id::NONE;
            let mut binding_dep_track_point: TrackPointId = Id::NONE;
            let mut reapply_queue: Cint64 = INVALID;
            // W3-DEFER[api]: conSet->getConceptDescriptorAndReapplyQueue(opConcept, bindingConDes, bindingDepTrackPoint, reapplyQueue)
            let has_con_des_and_queue = false;

            if !has_con_des_and_queue {
                if next_dep_track_point == Id::NONE {
                    // W3-DEFER[api]: conSet = succIndi->getReapplyConceptLabelSet(true)
                    con_set = INVALID;
                    // W3-DEFER[api]: createVARBINDPROPAGATEALLDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, restLink->getDependencyTrackPoint(), calcAlgContext)
                    next_dep_track_point = Id::NONE;
                }
                // W3-DEFER[api]: bindingConDes = addConceptToIndividualReturnConceptDescriptor(opConcept, opConNeg, succIndi, nextDepTrackPoint, false, false, calcAlgContext)
                binding_con_des = Id::NONE;

                // W3-DEFER[api]: conVarBindingPathSetHash = processIndi->getConceptVariableBindingPathSetHash(true)
                let con_var_binding_path_set_hash: Cint64 = INVALID;
                // W3-DEFER[api]: prevVarBindingPathSet = conVarBindingPathSetHash->getVariableBindingPathSet(concept, false)
                let prev_var_binding_path_set: Cint64 = INVALID;
                // W3-DEFER[api]: succConVarBindingPathSetHash = succIndi->getConceptVariableBindingPathSetHash(true)
                let succ_con_var_binding_path_set_hash: Cint64 = INVALID;
                // W3-DEFER[api]: succVarBindingPathSet = succConVarBindingPathSetHash->getVariableBindingPathSet(opConcept, true)
                let succ_var_binding_path_set: Cint64 = INVALID;
                // W3-DEFER[api]: succVarBindingPathSet->setConceptDescriptor(bindingConDes)

                self.propagate_initial_variable_bindings_to_successor(
                    &mut process_indi,
                    *succ_indi,
                    binding_con_des,
                    succ_var_binding_path_set,
                    prev_var_binding_path_set,
                    rest_link,
                    succ_con_var_binding_path_set_hash,
                    calc_alg_context,
                );
                continue_propagation = true;
            } else {
                // W3-DEFER[api]: conVarBindingPathSetHash = processIndi->getConceptVariableBindingPathSetHash(true)
                let con_var_binding_path_set_hash: Cint64 = INVALID;
                // W3-DEFER[api]: prevVarBindingPathSet = conVarBindingPathSetHash->getVariableBindingPathSet(concept, false)
                let prev_var_binding_path_set: Cint64 = INVALID;
                // W3-DEFER[api]: succConVarBindingPathSetHash = succIndi->getConceptVariableBindingPathSetHash(true)
                let succ_con_var_binding_path_set_hash: Cint64 = INVALID;
                // W3-DEFER[api]: succVarBindingPathSet = succConVarBindingPathSetHash->getVariableBindingPathSet(opConcept, true)
                let succ_var_binding_path_set: Cint64 = INVALID;

                if self.propagate_fresh_variable_bindings_to_successor(
                    &mut process_indi,
                    *succ_indi,
                    con_des,
                    succ_var_binding_path_set,
                    prev_var_binding_path_set,
                    rest_link,
                    succ_con_var_binding_path_set_hash,
                    calc_alg_context,
                ) {
                    // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(succIndi, calcAlgContext)
                    // W3-DEFER[api]: CConceptProcessingQueue* conProQueue = succIndi->getConceptProcessingQueue(true)
                    let con_pro_queue: Cint64 = INVALID;
                    // W3-DEFER[api]: cint64 bindingCount = succVarBindingPathSet->getVariableBindingPathMap()->count()
                    let binding_count: Cint64 = 0;
                    // W3-DEFER[api]: addConceptPreprocessedToProcessingQueue(bindingConDes, bindingDepTrackPoint, conProQueue, succIndi, true, calcAlgContext)
                    if reapply_queue != INVALID {
                        // W3-DEFER[api]: reapplyQueue->isEmpty()
                        let reapply_queue_empty = true;
                        if !reapply_queue_empty {
                            // W3-DEFER[api]: conSet = succIndi->getReapplyConceptLabelSet(true)
                            con_set = INVALID;
                            // W3-DEFER[api]: CCondensedReapplyQueueIterator reapplyQueueIt(conSet->getConceptReapplyIterator(bindingConDes))
                            // W3-DEFER[api]: applyReapplyQueueConcepts(succIndi, &reapplyQueueIt, calcAlgContext)
                        }
                    }
                    continue_propagation = true;
                }
            }
        }

        if continue_propagation {
            // W3-DEFER[api]: addIndividualToProcessingQueue(succIndi, calcAlgContext)  [sibling, core queue mgmt]
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateInitialVariableBindingsToSuccessor`.
    pub fn propagate_initial_variable_bindings_to_successor(
        &mut self,
        process_indi: &mut NodeId,
        succ_indi: NodeId,
        con_des: ConDescId,
        new_var_binding_path_set: Cint64,
        prev_var_binding_path_set: Cint64,
        rest_link: EdgeId,
        con_var_binding_set_hash: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;
        let mut propagations = false;
        let mut new_var_bind_path_des_linker: Cint64 = INVALID;
        if prev_var_binding_path_set != INVALID {
            // W3-DEFER[api]: newVarBindingPathSet->copyVariableBindingPaths(prevVarBindingPathSet->getVariableBindingPathMap())
            // W3-DEFER[api]: CVariableBindingPathMap* varBindPathMap = newVarBindingPathSet->getVariableBindingPathMap()
            // Reproduced structurally over an empty deferred iterator (map unported).
            let var_bind_path_map_iter: &[Cint64] = &[];
            for _it in var_bind_path_map_iter.iter() {
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDCOUNT, calcAlgContext)
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDINITIALCOUNT, calcAlgContext)
                self.stat_var_binding_propagate_succ_count += 1;
                self.stat_var_binding_propagate_succ_initial_count += 1;
                // W3-DEFER[api]: CVariableBindingPathMapData& varBindPathMapData = it.value()
                // W3-DEFER[api]: prevVarBindPathDes = varBindPathMapData.getVariableBindingPathDescriptor()
                // W3-DEFER[memory-pool]: newVarBindPathDes = allocateAndConstruct<CVariableBindingPathDescriptor>(taskMemMan)
                let new_var_bind_path_des: Cint64 = INVALID;
                let mut new_dep_track_point: TrackPointId = Id::NONE;
                // W3-DEFER[api]: createPROPAGATEVARIABLEBINDINGSSUCCESSORDependency(newDepTrackPoint, processIndi, conDes, prevVarBindPathDes->getDependencyTrackPoint(), restLink->getDependencyTrackPoint(), calcAlgContext)
                // W3-DEFER[api]: newVarBindPathDes->initVariableBindingPathDescriptor(prevVarBindPathDes->getVariableBindingPath(), newDepTrackPoint)
                // W3-DEFER[api]: varBindPathMapData.setVariableBindingPathDescriptor(newVarBindPathDes)
                // W3-DEFER[api]: newVarBindPathDesLinker = newVarBindPathDes->append(newVarBindPathDesLinker)
                new_var_bind_path_des_linker = new_var_bind_path_des;
                propagations = true;
            }
            if new_var_bind_path_des_linker != INVALID {
                // W3-DEFER[api]: newVarBindingPathSet->addVariableBindingPathDescriptorLinker(newVarBindPathDesLinker)
                // W3-DEFER[api]: conVarBindingSetHash->setLastVariableBindingDescriptionLinker(newVarBindPathDesLinker)
            }
        }
        propagations
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateFreshVariableBindingsToSuccessor`.
    pub fn propagate_fresh_variable_bindings_to_successor(
        &mut self,
        process_indi: &mut NodeId,
        succ_indi: NodeId,
        con_des: ConDescId,
        new_var_binding_path_set: Cint64,
        prev_var_binding_path_set: Cint64,
        rest_link: EdgeId,
        con_var_binding_set_hash: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;
        let mut propagations = false;
        if prev_var_binding_path_set != INVALID {
            // W3-DEFER[api]: prevVarBindPathMap = prevVarBindingPathSet->getVariableBindingPathMap()
            // W3-DEFER[api]: newVarBindPathMap = newVarBindingPathSet->getVariableBindingPathMap()
            // The sorted merge-walk advances itNew while (newPropID < prevPropID),
            // skips equal keys, and propagates each prev-only key (doPropagation).
            // Reproduced structurally over the prev-only key set (empty deferred).
            let mut new_var_bind_path_des_linker: Cint64 = INVALID;
            let prev_only_iter: &[Cint64] = &[];
            for _it_prev in prev_only_iter.iter() {
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDCOUNT, calcAlgContext)
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDFRESHCOUNT, calcAlgContext)
                self.stat_var_binding_propagate_succ_count += 1;
                self.stat_var_binding_propagate_succ_fresh_count += 1;
                // W3-DEFER[api]: prevVarBindPathDes = itPrev.value().getVariableBindingPathDescriptor()
                // W3-DEFER[memory-pool]: newVarBindPathDes = allocateAndConstruct<CVariableBindingPathDescriptor>(taskMemMan)
                let new_var_bind_path_des: Cint64 = INVALID;
                let mut new_dep_track_point: TrackPointId = Id::NONE;
                // W3-DEFER[api]: createPROPAGATEVARIABLEBINDINGSSUCCESSORDependency(newDepTrackPoint, processIndi, conDes, prevVarBindPathDes->getDependencyTrackPoint(), restLink->getDependencyTrackPoint(), calcAlgContext)
                // W3-DEFER[api]: varBindingPath = prevVarBindPathDes->getVariableBindingPath()
                // W3-DEFER[api]: newVarBindPathDes->initVariableBindingPathDescriptor(varBindingPath, newDepTrackPoint)
                // W3-DEFER[api]: itNew = newVarBindPathMap->insert(varBindingPath->getPropagationID(), CVariableBindingPathMapData(newVarBindPathDes))
                // W3-DEFER[api]: newVarBindPathDesLinker = newVarBindPathDes->append(newVarBindPathDesLinker)
                new_var_bind_path_des_linker = new_var_bind_path_des;
                propagations = true;
            }
            if new_var_bind_path_des_linker != INVALID {
                // W3-DEFER[api]: newVarBindingPathSet->addVariableBindingPathDescriptorLinker(newVarBindPathDesLinker)
                // W3-DEFER[api]: conVarBindingSetHash->setLastVariableBindingDescriptionLinker(newVarBindPathDesLinker)
            }
        }
        propagations
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateVariableBindingsJoins`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `joinConDes` (`CConceptDescriptor*&`) →
    /// `&mut ConDescId`; `varBindingPathSet` (`CVariableBindingPathSet*&`) →
    /// `&mut Cint64`. `processIndi` is by-value (`NodeId`).
    pub fn propagate_variable_bindings_joins(
        &mut self,
        process_indi: NodeId,
        joining_con_des: ConDescId,
        join_concept: ConceptId,
        var_bind_path_des: Cint64,
        left_trigger_path: bool,
        var_bind_path_join_hash: Cint64,
        var_binding_path_set_hash: Cint64,
        join_con_des: &mut ConDescId,
        var_binding_path_set: &mut Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;
        // W3-DEFER[api]: joiningConcept = joiningConDes->getConcept()
        let joining_concept: ConceptId = Id::NONE;
        // W3-DEFER[api]: varLinker = joiningConcept->getVariableLinker()
        let var_linker: Cint64 = INVALID;

        // W3-DEFER[api]: varBindPath = varBindPathDes->getVariableBindingPath()
        let var_bind_path: Cint64 = INVALID;
        // W3-DEFER[api]: varBindPathJoinData = varBindPathJoinHash->getVariableBindingPathJoiningData(CVariableBindingPathJoiningHasher(varBindPath, varLinker), true)
        let mut var_bind_path_join_data: Cint64 = INVALID;
        // W3-DEFER[api]: varBindDes = varBindPath->getVariableBindingDescriptorLinker()
        let var_bind_des: Cint64 = INVALID;

        if var_bind_path_join_data == INVALID {
            // W3-DEFER[memory-pool]: varBindPathJoinData = allocateAndConstruct<CVariableBindingPathJoiningData>(taskMemMan)
            var_bind_path_join_data = INVALID;
            let key_var_bind_des_linker: Cint64 =
                self.create_variable_binding_path_key(process_indi, var_linker, var_bind_des, calc_alg_context);
            // W3-DEFER[api]: varBindPathJoinData->initVariableBindingPathJoiningData(keyVarBindDesLinker, nullptr, nullptr)
            // W3-DEFER[api]: varBindPathJoinHash->insertVariableBindingPathJoiningData(CVariableBindingPathJoiningHasher(varBindPathJoinData), varBindPathJoinData)
        }

        // CVariableBindingPathDescriptor* otherVarBindPathDes
        let mut other_var_bind_path_des: Cint64 = INVALID;
        if left_trigger_path {
            // W3-DEFER[api]: otherVarBindPathDes = varBindPathJoinData->getRightVariableBindingPathDescriptorLinker()
            other_var_bind_path_des = INVALID;
        } else {
            // W3-DEFER[api]: otherVarBindPathDes = varBindPathJoinData->getLeftVariableBindingPathDescriptorLinker()
            other_var_bind_path_des = INVALID;
        }

        let mut added_var_bind_path = false;
        // for (otherVarBindPathDesIt = otherVarBindPathDes; it; it = it->getNext())
        // Reproduced structurally over the (empty, deferred) other-side linker chain.
        let other_linker_iter: &[Cint64] = &[];
        for _other_var_bind_path_des_it in other_linker_iter.iter() {
            // W3-DEFER[macro]: STATINC(VARBINDJOINCOMBINECOUNT, calcAlgContext)
            self.stat_var_binding_join_combines_count += 1;

            // W3-DEFER[api]: otherVarBindPathDesIt->getVariableBindingPath()
            let other_var_bind_path: Cint64 = INVALID;
            // W3-DEFER[api]: varBindPathDes->getVariableBindingPath()
            let left_var_bind_path: Cint64 = INVALID;
            let merged_var_bind_path: Cint64 =
                self.get_joined_variable_binding_path(left_var_bind_path, other_var_bind_path, calc_alg_context);
            // W3-DEFER[memory-pool]: mergedVarBindPathDes = allocateAndConstruct<CVariableBindingPathDescriptor>(...)
            let merged_var_bind_path_des: Cint64 = INVALID;

            let mut merged_dependency_track_point: TrackPointId = Id::NONE;
            // W3-DEFER[api]: createVARBINDPROPAGATEJOINDependency(mergedDependencyTrackPoint, processIndi, joiningConDes, varBindPathDes->getDependencyTrackPoint(), otherVarBindPathDesIt->getDependencyTrackPoint(), calcAlgContext)

            self.force_variable_binding_join_created(
                process_indi,
                joining_con_des,
                join_concept,
                join_con_des,
                merged_dependency_track_point,
                var_binding_path_set,
                var_binding_path_set_hash,
                calc_alg_context,
            );

            // W3-DEFER[api]: mergedVarBindPathDes->initVariableBindingPathDescriptor(mergedVarBindPath, mergedDependencyTrackPoint)
            // W3-DEFER[api]: varBindingPathSet->addVariableBindingPath(mergedVarBindPathDes)
            added_var_bind_path = true;
        }

        // W3-DEFER[memory-pool]: newVarBindPathDes = allocateAndConstruct<CVariableBindingPathDescriptor>(taskMemMan)
        let new_var_bind_path_des: Cint64 = INVALID;
        // W3-DEFER[api]: newVarBindPathDes->initVariableBindingPathDescriptor(varBindPath, varBindPathDes->getDependencyTrackPoint())

        if left_trigger_path {
            // W3-DEFER[api]: varBindingPathSetHash->setLastVariableBindingDescriptionLinker(newVarBindPathDes)
            // W3-DEFER[api]: varBindPathJoinData->addLeftVariableBindingPathDescriptorLinker(newVarBindPathDes)
        } else {
            // W3-DEFER[api]: varBindingPathSetHash->setLastVariableBindingDescriptionLinker(newVarBindPathDes)
            // W3-DEFER[api]: varBindPathJoinData->addRightVariableBindingPathDescriptorLinker(newVarBindPathDes)
        }

        added_var_bind_path
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createVariableBindingPathKey`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: `varLinker` (`CSortedLinker<CVariable*>*`) and the
    /// `CVariableBindingDescriptor*` chain are unported → opaque `Cint64`; the
    /// parallel walk (advance both on a variable match, else advance only the
    /// binding-descriptor cursor) is reproduced structurally over empty iterators.
    pub fn create_variable_binding_path_key(
        &mut self,
        process_indi: NodeId,
        var_linker: Cint64,
        var_bind_des: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;

        let mut key_var_bind_des_linker: Cint64 = INVALID;
        let mut last_key_var_bind_des_linker: Cint64 = INVALID;
        let mut var_linker_it: Cint64 = var_linker;
        let mut var_bind_des_it: Cint64 = var_bind_des;
        // while (varLinkerIt) { ... }  — the CSortedLinker / descriptor chains are
        // unported; the walk is deferred (varLinkerIt starts INVALID ⇒ no iterations).
        while var_linker_it != INVALID {
            // W3-DEFER[api]: varBind = varBindDesIt->getVariableBinding()
            // W3-DEFER[api]: if (varBind->getBindedVariable() == varLinkerIt->getData())
            let variable_matches = false;
            if variable_matches {
                // W3-DEFER[memory-pool]: nextKeyVarBindDesLinker = allocateAndConstruct<CVariableBindingDescriptor>(taskMemMan)
                let next_key_var_bind_des_linker: Cint64 = INVALID;
                // W3-DEFER[api]: nextKeyVarBindDesLinker->initVariableBindingDescriptor(varBind)
                if last_key_var_bind_des_linker != INVALID {
                    // W3-DEFER[api]: lastKeyVarBindDesLinker->setNext(nextKeyVarBindDesLinker)
                    last_key_var_bind_des_linker = next_key_var_bind_des_linker;
                } else {
                    key_var_bind_des_linker = next_key_var_bind_des_linker;
                    last_key_var_bind_des_linker = next_key_var_bind_des_linker;
                }
                // W3-DEFER[api]: varLinkerIt = varLinkerIt->getNext()
                var_linker_it = INVALID;
                // W3-DEFER[api]: varBindDesIt = varBindDesIt->getNext()
                var_bind_des_it = INVALID;
            } else {
                // W3-DEFER[api]: varBindDesIt = varBindDesIt->getNext()
                var_bind_des_it = INVALID;
            }
        }
        key_var_bind_des_linker
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::triggerVariableBindingPathJoining`.
    pub fn trigger_variable_binding_path_joining(
        &mut self,
        process_indi: NodeId,
        var_bind_path_des: Cint64,
        var_bind_des: Cint64,
        left_triggered: bool,
        var_bind_trigger_hash: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut next_var_bind_des_trigger: Cint64 = var_bind_des;
        if next_var_bind_des_trigger != INVALID {
            // while (nextVarBindDesTrigger) { ... }  — unported descriptor chain,
            // deferred (starts INVALID once we follow getNext ⇒ structural only).
            while next_var_bind_des_trigger != INVALID {
                // W3-DEFER[api]: varBind = nextVarBindDesTrigger->getVariableBinding()
                // W3-DEFER[api]: nextVarBindDesTrigger = nextVarBindDesTrigger->getNext()
                next_var_bind_des_trigger = INVALID;
                // W3-DEFER[api]: varBindTriggerHash->tryInsertVariableBindingTrigger(varBind->getBindedVariable(), varBind->getBindedIndividual(), varBindPathDes, nextVarBindDesTrigger, leftTriggered)
                let inserted = false;
                if !inserted {
                    // already present — continue walking
                } else {
                    // W3-DEFER[macro]: STATINC(VARBINDJOINTRIGGERINSTALLCOUNT, calcAlgContext)
                    return true;
                }
            }
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::forceVariableBindingJoinCreated`.
    pub fn force_variable_binding_join_created(
        &mut self,
        process_indi: NodeId,
        joining_con_des: ConDescId,
        join_concept: ConceptId,
        join_con_des: &mut ConDescId,
        merged_dependency_track_point: TrackPointId,
        var_binding_path_set: &mut Cint64,
        var_binding_path_set_hash: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if *join_con_des == Id::NONE {
            // W3-DEFER[api]: joinConDes = addConceptToIndividualReturnConceptDescriptor(joinConcept, false, processIndi, mergedDependencyTrackPoint, false, false, calcAlgContext)
            *join_con_des = Id::NONE;
        }
        if *var_binding_path_set == INVALID {
            // W3-DEFER[api]: varBindingPathSet = varBindingPathSetHash->getVariableBindingPathSet(joinConcept, true)
            *var_binding_path_set = INVALID;
            // W3-DEFER[api]: varBindingPathSet->setConceptDescriptor(joinConDes)
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getJoinedVariableBindingPath`.
    pub fn get_joined_variable_binding_path(
        &mut self,
        left_var_bind_path: Cint64,
        right_var_bind_path: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // W3-DEFER[memory-pool]: calcAlgContext->getUsedProcessTaskMemoryAllocationManager()
        let task_mem_man: Cint64 = INVALID;
        // W3-DEFER[api]: processingDataBox = calcAlgContext->getUsedProcessingDataBox()
        // W3-DEFER[api]: varBindPathMergingHash = processingDataBox->getVariableBindingPathMergingHash(true)
        let var_bind_path_merging_hash: Cint64 = INVALID;

        // W3-DEFER[api]: mergeHashData = varBindPathMergingHash->getMergedVariableBindingPathData(leftVarBindPath, rightVarBindPath)
        let merge_hash_data: Cint64 = INVALID;
        // W3-DEFER[api]: mergedVarBindPath = mergeHashData->getVariableBindingPath()
        let mut merged_var_bind_path: Cint64 = INVALID;
        if merged_var_bind_path == INVALID {
            // W3-DEFER[macro]: STATINC(VARBINDJOINCREATENEWCOUNT, calcAlgContext)

            // W3-DEFER[api]: leftVarBindDesIt = leftVarBindPath->getVariableBindingDescriptorLinker()
            let mut left_var_bind_des_it: Cint64 = INVALID;
            // W3-DEFER[api]: rightVarBindDesIt = rightVarBindPath->getVariableBindingDescriptorLinker()
            let mut right_var_bind_des_it: Cint64 = INVALID;

            let mut merged_var_bind_des: Cint64 = INVALID;
            let mut last_merged_var_bind_des: Cint64 = INVALID;

            // The sorted merge of the two descriptor chains (advance the <= side,
            // both on equality). Unported chains ⇒ both start INVALID ⇒ no iterations.
            while left_var_bind_des_it != INVALID || right_var_bind_des_it != INVALID {
                let mut next_merged_var_bind_des: Cint64 = INVALID;
                if left_var_bind_des_it != INVALID && right_var_bind_des_it != INVALID {
                    // W3-DEFER[api]: leftLE = *leftVarBindDesIt->getVariableBinding() <= *rightVarBindDesIt->getVariableBinding()
                    let left_le = false;
                    // W3-DEFER[api]: rightLE = *rightVarBindDesIt->getVariableBinding() <= *leftVarBindDesIt->getVariableBinding()
                    let right_le = false;
                    if left_le && right_le {
                        // W3-DEFER[memory-pool]: allocateAndConstruct<CVariableBindingDescriptor>(taskMemMan)
                        // W3-DEFER[api]: nextMergedVarBindDes->initVariableBindingDescriptor(leftVarBindDesIt->getVariableBinding())
                        next_merged_var_bind_des = INVALID;
                        // W3-DEFER[api]: leftVarBindDesIt = leftVarBindDesIt->getNext()
                        left_var_bind_des_it = INVALID;
                        // W3-DEFER[api]: rightVarBindDesIt = rightVarBindDesIt->getNext()
                        right_var_bind_des_it = INVALID;
                    } else if right_le {
                        // W3-DEFER[memory-pool]: allocateAndConstruct + init from rightVarBindDesIt
                        next_merged_var_bind_des = INVALID;
                        // W3-DEFER[api]: rightVarBindDesIt = rightVarBindDesIt->getNext()
                        right_var_bind_des_it = INVALID;
                    } else if left_le {
                        // W3-DEFER[memory-pool]: allocateAndConstruct + init from leftVarBindDesIt
                        next_merged_var_bind_des = INVALID;
                        // W3-DEFER[api]: leftVarBindDesIt = leftVarBindDesIt->getNext()
                        left_var_bind_des_it = INVALID;
                    }
                } else if left_var_bind_des_it != INVALID {
                    // W3-DEFER[memory-pool]: allocateAndConstruct + init from leftVarBindDesIt
                    next_merged_var_bind_des = INVALID;
                    // W3-DEFER[api]: leftVarBindDesIt = leftVarBindDesIt->getNext()
                    left_var_bind_des_it = INVALID;
                } else if right_var_bind_des_it != INVALID {
                    // W3-DEFER[memory-pool]: allocateAndConstruct + init from rightVarBindDesIt
                    next_merged_var_bind_des = INVALID;
                    // W3-DEFER[api]: rightVarBindDesIt = rightVarBindDesIt->getNext()
                    right_var_bind_des_it = INVALID;
                }

                if next_merged_var_bind_des != INVALID {
                    if last_merged_var_bind_des != INVALID {
                        // W3-DEFER[api]: lastMergedVarBindDes->setNext(nextMergedVarBindDes)
                        last_merged_var_bind_des = next_merged_var_bind_des;
                    } else {
                        merged_var_bind_des = next_merged_var_bind_des;
                        last_merged_var_bind_des = next_merged_var_bind_des;
                    }
                }
            }

            // W3-DEFER[memory-pool]: mergedVarBindPath = allocateAndConstruct<CVariableBindingPath>(taskMemMan)
            // W3-DEFER[api]: mergedVarBindPath->initVariableBindingPath(processingDataBox->getNextVariableBindingPathID(true), mergedVarBindDes)
            merged_var_bind_path = INVALID;
            // W3-DEFER[api]: mergeHashData->setVariableBindingPath(mergedVarBindPath)
        }
        merged_var_bind_path
    }
}
