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
use super::super::model::{ConceptId, VariableId};
use super::super::process::binding_hash::{
    ConceptVariableBindingPathSetHash, ConceptVariableBindingPathSetHashId,
};
use super::super::process::varbind::{
    RepresentativeVariableBindingPathMap, VarBindingDescriptorId, VarBindingPathDescriptorId,
    VarBindingPathId, VarBindingPathSetId, VariableBindingDescriptor, VariableBindingPath,
    VariableBindingPathDescriptor, VariableBindingPathJoiningData, VariableBindingPathJoiningHash,
    VariableBindingPathJoiningHashId, VariableBindingPathJoiningHasher,
    VariableBindingPathMergingHash, VariableBindingPathSet, VariableBindingTriggerHash,
    VariableBindingTriggerHashId,
};
use super::super::process::{ConDescId, DepLinkId, EdgeId, LabelSetId, NodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::hasCommonVariableBindings`.
    pub fn has_common_variable_bindings(
        &mut self,
        process_indi: &mut NodeId,
        left_rep_var_bind_map: &RepresentativeVariableBindingPathMap,
        right_rep_var_bind_map: &RepresentativeVariableBindingPathMap,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let right_count = right_rep_var_bind_map.count();
        let left_count = left_rep_var_bind_map.count();
        if right_count < left_count {
            return self.has_common_variable_bindings(
                process_indi,
                right_rep_var_bind_map,
                left_rep_var_bind_map,
                calc_alg_context,
            );
        }

        if left_count * self.map_comparison_direct_lookup_factor < right_count {
            for key in left_rep_var_bind_map.map.keys() {
                if right_rep_var_bind_map.contains(*key) {
                    return true;
                }
            }
            false
        } else {
            let mut left_map_iter = left_rep_var_bind_map
                .map
                .keys()
                .copied()
                .collect::<Vec<_>>();
            let mut right_map_iter = right_rep_var_bind_map
                .map
                .keys()
                .copied()
                .collect::<Vec<_>>();
            left_map_iter.sort_unstable();
            right_map_iter.sort_unstable();
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
        new_var_binding_set: VarBindingPathSetId,
        prev_var_binding_set: VarBindingPathSetId,
        other_dependencies: DepLinkId,
        con_var_binding_set_hash: ConceptVariableBindingPathSetHashId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut propagations = false;
        let mut new_var_bind_path_des_linker: VarBindingPathDescriptorId = Id::NONE;
        if prev_var_binding_set.is_some() {
            let prev_map = {
                let pc = calc_alg_context.process_context();
                pc.vbpath_set(prev_var_binding_set)
                    .get_variable_binding_path_map()
                    .clone()
            };
            calc_alg_context
                .process_context_mut()
                .vbpath_set_mut(new_var_binding_set)
                .copy_variable_binding_paths(Some(&prev_map));

            let mut path_keys: Vec<Cint64> = {
                let pc = calc_alg_context.process_context();
                pc.vbpath_set(new_var_binding_set)
                    .get_variable_binding_path_map()
                    .map
                    .keys()
                    .copied()
                    .collect()
            };
            path_keys.sort();

            for prop_id in path_keys {
                self.stat_var_binding_propagate_count += 1;
                self.stat_var_binding_propagate_initial_count += 1;
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDCOUNT, calcAlgContext)
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDINITIALCOUNT, calcAlgContext)

                let prev_var_bind_path_des = calc_alg_context
                    .process_context()
                    .vbpath_set(new_var_binding_set)
                    .get_variable_binding_path_map()
                    .value(prop_id)
                    .get_variable_binding_path_descriptor();
                let (var_binding_path, prev_dep_track_point) = {
                    let pc = calc_alg_context.process_context();
                    let prev_des = pc.vbpath_des(prev_var_bind_path_des);
                    (
                        prev_des.get_variable_binding_path(),
                        prev_des.get_dependency_track_point(),
                    )
                };
                let new_var_bind_path_des = calc_alg_context
                    .process_context_mut()
                    .alloc_vbpath_des(VariableBindingPathDescriptor::new());
                let mut new_dep_track_point: TrackPointId = Id::NONE;
                let _bind_dep_node = self.create_propagate_variable_binding_dependency(
                    &mut new_dep_track_point,
                    process_indi,
                    con_des,
                    prev_dep_track_point,
                    other_dependencies,
                    calc_alg_context,
                );
                if new_dep_track_point.is_none() {
                    // W6-DEFER[api]: createPROPAGATEVARIABLEBINDINGDependency is
                    // called at the C++ point, but dependency-base materialization
                    // still returns no track point; carry the previous dependency.
                    new_dep_track_point = prev_dep_track_point;
                }
                calc_alg_context
                    .process_context_mut()
                    .vbpath_des_mut(new_var_bind_path_des)
                    .init_variable_binding_path_descriptor(var_binding_path, new_dep_track_point);
                calc_alg_context
                    .process_context_mut()
                    .vbpath_set_mut(new_var_binding_set)
                    .get_variable_binding_path_map_mut()
                    .entry_mut(prop_id)
                    .set_variable_binding_path_descriptor(new_var_bind_path_des);
                if new_var_bind_path_des_linker.is_none() {
                    new_var_bind_path_des_linker = new_var_bind_path_des;
                } else {
                    VariableBindingPathDescriptor::append(
                        calc_alg_context.process_context_mut(),
                        new_var_bind_path_des,
                        new_var_bind_path_des_linker,
                    );
                    new_var_bind_path_des_linker = new_var_bind_path_des;
                }
                propagations = true;
            }
            if new_var_bind_path_des_linker.is_some() {
                VariableBindingPathSet::add_variable_binding_path_descriptor_linker(
                    calc_alg_context.process_context_mut(),
                    new_var_binding_set,
                    new_var_bind_path_des_linker,
                );
                calc_alg_context
                    .process_context_mut()
                    .con_var_bind_path_set_hash_mut(con_var_binding_set_hash)
                    .set_last_variable_binding_description_linker(new_var_bind_path_des_linker);
            }
        }
        propagations
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateFreshVariableBindings`.
    pub fn propagate_fresh_variable_bindings(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        new_var_binding_set: VarBindingPathSetId,
        prev_var_binding_set: VarBindingPathSetId,
        other_dependencies: DepLinkId,
        con_var_binding_set_hash: ConceptVariableBindingPathSetHashId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut propagations = false;
        if prev_var_binding_set.is_some() {
            let mut new_var_bind_path_des_linker: VarBindingPathDescriptorId = Id::NONE;
            let (prev_keys, new_keys): (Vec<Cint64>, Vec<Cint64>) = {
                let pc = calc_alg_context.process_context();
                let mut prev_keys: Vec<Cint64> = pc
                    .vbpath_set(prev_var_binding_set)
                    .get_variable_binding_path_map()
                    .map
                    .keys()
                    .copied()
                    .collect();
                let mut new_keys: Vec<Cint64> = pc
                    .vbpath_set(new_var_binding_set)
                    .get_variable_binding_path_map()
                    .map
                    .keys()
                    .copied()
                    .collect();
                prev_keys.sort();
                new_keys.sort();
                (prev_keys, new_keys)
            };
            let mut i_prev = 0;
            let mut i_new = 0;
            while i_prev < prev_keys.len() {
                let prop_id = prev_keys[i_prev];
                let mut do_propagation = true;
                while i_new < new_keys.len() && new_keys[i_new] < prop_id {
                    i_new += 1;
                }
                if i_new < new_keys.len() && new_keys[i_new] == prop_id {
                    do_propagation = false;
                    i_new += 1;
                }
                i_prev += 1;
                if !do_propagation {
                    continue;
                }
                self.stat_var_binding_propagate_count += 1;
                self.stat_var_binding_propagate_fresh_count += 1;
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDCOUNT, calcAlgContext)
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDFRESHCOUNT, calcAlgContext)

                let prev_var_bind_path_des = calc_alg_context
                    .process_context()
                    .vbpath_set(prev_var_binding_set)
                    .get_variable_binding_path_map()
                    .value(prop_id)
                    .get_variable_binding_path_descriptor();
                let (var_binding_path, prev_dep_track_point) = {
                    let pc = calc_alg_context.process_context();
                    let prev_des = pc.vbpath_des(prev_var_bind_path_des);
                    (
                        prev_des.get_variable_binding_path(),
                        prev_des.get_dependency_track_point(),
                    )
                };
                let new_var_bind_path_des = calc_alg_context
                    .process_context_mut()
                    .alloc_vbpath_des(VariableBindingPathDescriptor::new());
                let mut new_dep_track_point: TrackPointId = Id::NONE;
                let _bind_dep_node = self.create_propagate_variable_binding_dependency(
                    &mut new_dep_track_point,
                    process_indi,
                    con_des,
                    prev_dep_track_point,
                    other_dependencies,
                    calc_alg_context,
                );
                if new_dep_track_point.is_none() {
                    // W6-DEFER[api]: dependency-base backend is not materialized
                    // yet; carry the previous dependency track point.
                    new_dep_track_point = prev_dep_track_point;
                }
                calc_alg_context
                    .process_context_mut()
                    .vbpath_des_mut(new_var_bind_path_des)
                    .init_variable_binding_path_descriptor(var_binding_path, new_dep_track_point);
                calc_alg_context
                    .process_context_mut()
                    .vbpath_set_mut(new_var_binding_set)
                    .get_variable_binding_path_map_mut()
                    .entry_mut(prop_id)
                    .set_variable_binding_path_descriptor(new_var_bind_path_des);
                if new_var_bind_path_des_linker.is_none() {
                    new_var_bind_path_des_linker = new_var_bind_path_des;
                } else {
                    VariableBindingPathDescriptor::append(
                        calc_alg_context.process_context_mut(),
                        new_var_bind_path_des,
                        new_var_bind_path_des_linker,
                    );
                    new_var_bind_path_des_linker = new_var_bind_path_des;
                }
                propagations = true;
            }
            if new_var_bind_path_des_linker.is_some() {
                VariableBindingPathSet::add_variable_binding_path_descriptor_linker(
                    calc_alg_context.process_context_mut(),
                    new_var_binding_set,
                    new_var_bind_path_des_linker,
                );
                calc_alg_context
                    .process_context_mut()
                    .con_var_bind_path_set_hash_mut(con_var_binding_set_hash)
                    .set_last_variable_binding_description_linker(new_var_bind_path_des_linker);
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

        for concept_op_linker_it in concept_op_linker.iter() {
            let op_concept: ConceptId = concept_op_linker_it.target;
            let op_con_neg: bool = concept_op_linker_it.negated ^ negate;

            let mut binding_con_des: ConDescId = Id::NONE;
            let mut binding_dep_track_point: TrackPointId = Id::NONE;
            let op_concept_tag = calc_alg_context
                .ontology_arenas()
                .concept(op_concept)
                .get_concept_tag();
            let mut binding_con_des: ConDescId = Id::NONE;
            let mut binding_dep_track_point: TrackPointId = Id::NONE;
            let has_con_des_and_queue = calc_alg_context
                .process_context()
                .label_set(con_set)
                .get_concept_descriptor_and_reapply_queue_by_tag(
                    op_concept_tag,
                    &mut binding_con_des,
                    &mut binding_dep_track_point,
                );

            if !has_con_des_and_queue {
                if next_dep_track_point == Id::NONE {
                    con_set = calc_alg_context
                        .process_context_mut()
                        .node_reapply_concept_label_set(*succ_indi);
                    let link_dep_track_point = calc_alg_context
                        .process_context()
                        .edge(rest_link)
                        .get_dependency_track_point();
                    let mut process_indi_ref = process_indi;
                    let _bind_dep_node = self.create_varbind_propagate_all_dependency(
                        &mut next_dep_track_point,
                        &mut process_indi_ref,
                        con_des,
                        dep_track_point,
                        link_dep_track_point,
                        calc_alg_context,
                    );
                    if next_dep_track_point.is_none() {
                        // W6-DEFER[api]: the dependency factory call is present at
                        // the C++ point, but the dependency-base backend is still
                        // not materialized; carry the premise dependency meanwhile.
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

                let con_var_binding_path_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_variable_binding_path_set_hash(process_indi);
                let concept_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag();
                let prev_var_binding_path_set =
                    ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                        calc_alg_context.process_context_mut(),
                        con_var_binding_path_set_hash,
                        concept_tag,
                        false,
                    );
                let succ_con_var_binding_path_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_variable_binding_path_set_hash(*succ_indi);
                let succ_var_binding_path_set =
                    ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                        calc_alg_context.process_context_mut(),
                        succ_con_var_binding_path_set_hash,
                        op_concept_tag,
                        true,
                    );
                calc_alg_context
                    .process_context_mut()
                    .vbpath_set_mut(succ_var_binding_path_set)
                    .set_concept_descriptor(binding_con_des);

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
                let con_var_binding_path_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_variable_binding_path_set_hash(process_indi);
                let concept_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag();
                let prev_var_binding_path_set =
                    ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                        calc_alg_context.process_context_mut(),
                        con_var_binding_path_set_hash,
                        concept_tag,
                        false,
                    );
                let succ_con_var_binding_path_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_variable_binding_path_set_hash(*succ_indi);
                let succ_var_binding_path_set =
                    ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                        calc_alg_context.process_context_mut(),
                        succ_con_var_binding_path_set_hash,
                        op_concept_tag,
                        true,
                    );

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
                        INVALID,
                    );
                    // W3-DEFER[api]: the concrete `CCondensedReapplyQueue*`
                    // out-param from getConceptDescriptorAndReapplyQueue is not
                    // exposed by the label-set API yet, so the guarded
                    // reapplyQueue->isEmpty() / iterator drain remains deferred.
                    continue_propagation = true;
                }
            }
        }

        if continue_propagation {
            self.add_individual_to_processing_queue(*succ_indi, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateInitialVariableBindingsToSuccessor`.
    pub fn propagate_initial_variable_bindings_to_successor(
        &mut self,
        process_indi: &mut NodeId,
        succ_indi: NodeId,
        con_des: ConDescId,
        new_var_binding_path_set: VarBindingPathSetId,
        prev_var_binding_path_set: VarBindingPathSetId,
        rest_link: EdgeId,
        con_var_binding_set_hash: ConceptVariableBindingPathSetHashId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut propagations = false;
        let mut new_var_bind_path_des_linker: VarBindingPathDescriptorId = Id::NONE;
        if prev_var_binding_path_set.is_some() {
            let prev_map = {
                let pc = calc_alg_context.process_context();
                pc.vbpath_set(prev_var_binding_path_set)
                    .get_variable_binding_path_map()
                    .clone()
            };
            calc_alg_context
                .process_context_mut()
                .vbpath_set_mut(new_var_binding_path_set)
                .copy_variable_binding_paths(Some(&prev_map));

            let mut path_keys: Vec<Cint64> = {
                let pc = calc_alg_context.process_context();
                pc.vbpath_set(new_var_binding_path_set)
                    .get_variable_binding_path_map()
                    .map
                    .keys()
                    .copied()
                    .collect()
            };
            path_keys.sort();

            for prop_id in path_keys {
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDCOUNT, calcAlgContext)
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDINITIALCOUNT, calcAlgContext)
                self.stat_var_binding_propagate_succ_count += 1;
                self.stat_var_binding_propagate_succ_initial_count += 1;

                let prev_var_bind_path_des = calc_alg_context
                    .process_context()
                    .vbpath_set(new_var_binding_path_set)
                    .get_variable_binding_path_map()
                    .value(prop_id)
                    .get_variable_binding_path_descriptor();
                let (var_binding_path, prev_dep_track_point) = {
                    let pc = calc_alg_context.process_context();
                    let prev_des = pc.vbpath_des(prev_var_bind_path_des);
                    (
                        prev_des.get_variable_binding_path(),
                        prev_des.get_dependency_track_point(),
                    )
                };
                let link_dep_track_point = calc_alg_context
                    .process_context()
                    .edge(rest_link)
                    .get_dependency_track_point();
                let new_var_bind_path_des = calc_alg_context
                    .process_context_mut()
                    .alloc_vbpath_des(VariableBindingPathDescriptor::new());
                let mut new_dep_track_point: TrackPointId = Id::NONE;
                let _bind_dep_node = self.create_propagate_variable_bindings_successor_dependency(
                    &mut new_dep_track_point,
                    process_indi,
                    con_des,
                    prev_dep_track_point,
                    link_dep_track_point,
                    calc_alg_context,
                );
                if new_dep_track_point.is_none() {
                    // W6-DEFER[api]: createPROPAGATEVARIABLEBINDINGSSUCCESSORDependency
                    // is called at the C++ point; carry the previous dependency
                    // track point until the dependency-base backend lands.
                    new_dep_track_point = prev_dep_track_point;
                }
                calc_alg_context
                    .process_context_mut()
                    .vbpath_des_mut(new_var_bind_path_des)
                    .init_variable_binding_path_descriptor(var_binding_path, new_dep_track_point);
                calc_alg_context
                    .process_context_mut()
                    .vbpath_set_mut(new_var_binding_path_set)
                    .get_variable_binding_path_map_mut()
                    .entry_mut(prop_id)
                    .set_variable_binding_path_descriptor(new_var_bind_path_des);
                if new_var_bind_path_des_linker.is_none() {
                    new_var_bind_path_des_linker = new_var_bind_path_des;
                } else {
                    VariableBindingPathDescriptor::append(
                        calc_alg_context.process_context_mut(),
                        new_var_bind_path_des,
                        new_var_bind_path_des_linker,
                    );
                    new_var_bind_path_des_linker = new_var_bind_path_des;
                }
                propagations = true;
            }
            if new_var_bind_path_des_linker.is_some() {
                VariableBindingPathSet::add_variable_binding_path_descriptor_linker(
                    calc_alg_context.process_context_mut(),
                    new_var_binding_path_set,
                    new_var_bind_path_des_linker,
                );
                calc_alg_context
                    .process_context_mut()
                    .con_var_bind_path_set_hash_mut(con_var_binding_set_hash)
                    .set_last_variable_binding_description_linker(new_var_bind_path_des_linker);
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
        new_var_binding_path_set: VarBindingPathSetId,
        prev_var_binding_path_set: VarBindingPathSetId,
        rest_link: EdgeId,
        con_var_binding_set_hash: ConceptVariableBindingPathSetHashId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut propagations = false;
        if prev_var_binding_path_set.is_some() {
            let mut new_var_bind_path_des_linker: VarBindingPathDescriptorId = Id::NONE;
            let (prev_keys, new_keys): (Vec<Cint64>, Vec<Cint64>) = {
                let pc = calc_alg_context.process_context();
                let mut prev_keys: Vec<Cint64> = pc
                    .vbpath_set(prev_var_binding_path_set)
                    .get_variable_binding_path_map()
                    .map
                    .keys()
                    .copied()
                    .collect();
                let mut new_keys: Vec<Cint64> = pc
                    .vbpath_set(new_var_binding_path_set)
                    .get_variable_binding_path_map()
                    .map
                    .keys()
                    .copied()
                    .collect();
                prev_keys.sort();
                new_keys.sort();
                (prev_keys, new_keys)
            };
            let mut i_prev = 0;
            let mut i_new = 0;
            while i_prev < prev_keys.len() {
                let prop_id = prev_keys[i_prev];
                let mut do_propagation = true;
                while i_new < new_keys.len() && new_keys[i_new] < prop_id {
                    i_new += 1;
                }
                if i_new < new_keys.len() && new_keys[i_new] == prop_id {
                    do_propagation = false;
                    i_new += 1;
                }
                i_prev += 1;
                if !do_propagation {
                    continue;
                }
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDCOUNT, calcAlgContext)
                // W3-DEFER[macro]: STATINC(VARBINDPROPAGATEDFRESHCOUNT, calcAlgContext)
                self.stat_var_binding_propagate_succ_count += 1;
                self.stat_var_binding_propagate_succ_fresh_count += 1;

                let prev_var_bind_path_des = calc_alg_context
                    .process_context()
                    .vbpath_set(prev_var_binding_path_set)
                    .get_variable_binding_path_map()
                    .value(prop_id)
                    .get_variable_binding_path_descriptor();
                let (var_binding_path, prev_dep_track_point) = {
                    let pc = calc_alg_context.process_context();
                    let prev_des = pc.vbpath_des(prev_var_bind_path_des);
                    (
                        prev_des.get_variable_binding_path(),
                        prev_des.get_dependency_track_point(),
                    )
                };
                let link_dep_track_point = calc_alg_context
                    .process_context()
                    .edge(rest_link)
                    .get_dependency_track_point();
                let new_var_bind_path_des = calc_alg_context
                    .process_context_mut()
                    .alloc_vbpath_des(VariableBindingPathDescriptor::new());
                let mut new_dep_track_point: TrackPointId = Id::NONE;
                let _bind_dep_node = self.create_propagate_variable_bindings_successor_dependency(
                    &mut new_dep_track_point,
                    process_indi,
                    con_des,
                    prev_dep_track_point,
                    link_dep_track_point,
                    calc_alg_context,
                );
                if new_dep_track_point.is_none() {
                    // W6-DEFER[api]: dependency-base backend is not materialized
                    // yet; carry the previous dependency track point.
                    new_dep_track_point = prev_dep_track_point;
                }
                calc_alg_context
                    .process_context_mut()
                    .vbpath_des_mut(new_var_bind_path_des)
                    .init_variable_binding_path_descriptor(var_binding_path, new_dep_track_point);
                calc_alg_context
                    .process_context_mut()
                    .vbpath_set_mut(new_var_binding_path_set)
                    .get_variable_binding_path_map_mut()
                    .entry_mut(prop_id)
                    .set_variable_binding_path_descriptor(new_var_bind_path_des);
                if new_var_bind_path_des_linker.is_none() {
                    new_var_bind_path_des_linker = new_var_bind_path_des;
                } else {
                    VariableBindingPathDescriptor::append(
                        calc_alg_context.process_context_mut(),
                        new_var_bind_path_des,
                        new_var_bind_path_des_linker,
                    );
                    new_var_bind_path_des_linker = new_var_bind_path_des;
                }
                propagations = true;
            }
            if new_var_bind_path_des_linker.is_some() {
                VariableBindingPathSet::add_variable_binding_path_descriptor_linker(
                    calc_alg_context.process_context_mut(),
                    new_var_binding_path_set,
                    new_var_bind_path_des_linker,
                );
                calc_alg_context
                    .process_context_mut()
                    .con_var_bind_path_set_hash_mut(con_var_binding_set_hash)
                    .set_last_variable_binding_description_linker(new_var_bind_path_des_linker);
            }
        }
        propagations
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::propagateVariableBindingsJoins`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `joinConDes` (`CConceptDescriptor*&`) →
    /// `&mut ConDescId`; `varBindingPathSet` (`CVariableBindingPathSet*&`) →
    /// `&mut VarBindingPathSetId`. `processIndi` is by-value (`NodeId`).
    pub fn propagate_variable_bindings_joins(
        &mut self,
        process_indi: NodeId,
        joining_con_des: ConDescId,
        join_concept: ConceptId,
        var_bind_path_des: VarBindingPathDescriptorId,
        left_trigger_path: bool,
        var_bind_path_join_hash: VariableBindingPathJoiningHashId,
        var_binding_path_set_hash: ConceptVariableBindingPathSetHashId,
        join_con_des: &mut ConDescId,
        var_binding_path_set: &mut VarBindingPathSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let joining_concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(joining_con_des)
            .get_concept();
        let var_linker: Vec<VariableId> = calc_alg_context
            .ontology_arenas()
            .concept(joining_concept)
            .get_variable_linker()
            .to_vec();

        let var_bind_path: VarBindingPathId = calc_alg_context
            .process_context()
            .vbpath_des(var_bind_path_des)
            .get_variable_binding_path();
        let hasher = VariableBindingPathJoiningHasher::new_from_path(
            calc_alg_context.process_context(),
            var_bind_path,
            &var_linker,
        );
        let mut hash = std::mem::replace(
            calc_alg_context
                .process_context_mut()
                .vbpath_join_hash_mut(var_bind_path_join_hash),
            VariableBindingPathJoiningHash::new(INVALID),
        );
        let mut var_bind_path_join_data = hash.get_variable_binding_path_joining_data(
            calc_alg_context.process_context_mut(),
            &hasher,
            true,
        );
        *calc_alg_context
            .process_context_mut()
            .vbpath_join_hash_mut(var_bind_path_join_hash) = hash;
        let var_bind_des: VarBindingDescriptorId = calc_alg_context
            .process_context()
            .vbpath(var_bind_path)
            .get_variable_binding_descriptor_linker();

        if var_bind_path_join_data.is_none() {
            var_bind_path_join_data = calc_alg_context
                .process_context_mut()
                .alloc_vbpath_join_data(VariableBindingPathJoiningData::new());
            let key_var_bind_des_linker: VarBindingDescriptorId = self
                .create_variable_binding_path_key(
                    process_indi,
                    &var_linker,
                    var_bind_des,
                    calc_alg_context,
                );
            calc_alg_context
                .process_context_mut()
                .vbpath_join_data_mut(var_bind_path_join_data)
                .init_variable_binding_path_joining_data(
                    key_var_bind_des_linker,
                    Id::NONE,
                    Id::NONE,
                );
            let data_hasher = VariableBindingPathJoiningHasher::new_from_joining_data(
                calc_alg_context.process_context_mut(),
                var_bind_path_join_data,
            );
            let mut hash = std::mem::replace(
                calc_alg_context
                    .process_context_mut()
                    .vbpath_join_hash_mut(var_bind_path_join_hash),
                VariableBindingPathJoiningHash::new(INVALID),
            );
            hash.insert_variable_binding_path_joining_data(&data_hasher, var_bind_path_join_data);
            *calc_alg_context
                .process_context_mut()
                .vbpath_join_hash_mut(var_bind_path_join_hash) = hash;
        }

        // CVariableBindingPathDescriptor* otherVarBindPathDes
        let other_var_bind_path_des: VarBindingPathDescriptorId = if left_trigger_path {
            calc_alg_context
                .process_context()
                .vbpath_join_data(var_bind_path_join_data)
                .get_right_variable_binding_path_descriptor_linker()
        } else {
            calc_alg_context
                .process_context()
                .vbpath_join_data(var_bind_path_join_data)
                .get_left_variable_binding_path_descriptor_linker()
        };

        let mut added_var_bind_path = false;
        let mut other_var_bind_path_des_it = other_var_bind_path_des;
        while other_var_bind_path_des_it.is_some() {
            // W3-DEFER[macro]: STATINC(VARBINDJOINCOMBINECOUNT, calcAlgContext)
            self.stat_var_binding_join_combines_count += 1;

            let other_var_bind_path: VarBindingPathId = calc_alg_context
                .process_context()
                .vbpath_des(other_var_bind_path_des_it)
                .get_variable_binding_path();
            let left_var_bind_path: VarBindingPathId = calc_alg_context
                .process_context()
                .vbpath_des(var_bind_path_des)
                .get_variable_binding_path();
            let merged_var_bind_path: VarBindingPathId = self.get_joined_variable_binding_path(
                left_var_bind_path,
                other_var_bind_path,
                calc_alg_context,
            );
            let merged_var_bind_path_des = calc_alg_context
                .process_context_mut()
                .alloc_vbpath_des(VariableBindingPathDescriptor::new());

            let mut merged_dependency_track_point: TrackPointId = Id::NONE;
            let mut dep_process_indi = process_indi;
            let prev_dep = calc_alg_context
                .process_context()
                .vbpath_des(var_bind_path_des)
                .get_dependency_track_point();
            let other_dep = calc_alg_context
                .process_context()
                .vbpath_des(other_var_bind_path_des_it)
                .get_dependency_track_point();
            let _bind_join_dep_node = self.create_varbind_propagate_join_dependency(
                &mut merged_dependency_track_point,
                &mut dep_process_indi,
                joining_con_des,
                prev_dep,
                other_dep,
                calc_alg_context,
            );
            if merged_dependency_track_point.is_none() {
                merged_dependency_track_point = prev_dep;
            }

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

            calc_alg_context
                .process_context_mut()
                .vbpath_des_mut(merged_var_bind_path_des)
                .init_variable_binding_path_descriptor(
                    merged_var_bind_path,
                    merged_dependency_track_point,
                );
            VariableBindingPathSet::add_variable_binding_path(
                calc_alg_context.process_context_mut(),
                *var_binding_path_set,
                merged_var_bind_path_des,
            );
            added_var_bind_path = true;
            other_var_bind_path_des_it = calc_alg_context
                .process_context()
                .vbpath_des(other_var_bind_path_des_it)
                .get_next();
        }

        let new_var_bind_path_des = calc_alg_context
            .process_context_mut()
            .alloc_vbpath_des(VariableBindingPathDescriptor::new());
        let dep = calc_alg_context
            .process_context()
            .vbpath_des(var_bind_path_des)
            .get_dependency_track_point();
        calc_alg_context
            .process_context_mut()
            .vbpath_des_mut(new_var_bind_path_des)
            .init_variable_binding_path_descriptor(var_bind_path, dep);

        if left_trigger_path {
            calc_alg_context
                .process_context_mut()
                .con_var_bind_path_set_hash_mut(var_binding_path_set_hash)
                .set_last_variable_binding_description_linker(new_var_bind_path_des);
            VariableBindingPathJoiningData::add_left_variable_binding_path_descriptor_linker(
                calc_alg_context.process_context_mut(),
                var_bind_path_join_data,
                new_var_bind_path_des,
            );
        } else {
            calc_alg_context
                .process_context_mut()
                .con_var_bind_path_set_hash_mut(var_binding_path_set_hash)
                .set_last_variable_binding_description_linker(new_var_bind_path_des);
            VariableBindingPathJoiningData::add_right_variable_binding_path_descriptor_linker(
                calc_alg_context.process_context_mut(),
                var_bind_path_join_data,
                new_var_bind_path_des,
            );
        }

        added_var_bind_path
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createVariableBindingPathKey`.
    ///
    pub fn create_variable_binding_path_key(
        &mut self,
        process_indi: NodeId,
        var_linker: &[VariableId],
        var_bind_des: VarBindingDescriptorId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> VarBindingDescriptorId {
        let mut key_var_bind_des_linker: VarBindingDescriptorId = Id::NONE;
        let mut last_key_var_bind_des_linker: VarBindingDescriptorId = Id::NONE;
        let mut var_linker_it: usize = 0;
        let mut var_bind_des_it: VarBindingDescriptorId = var_bind_des;
        while var_linker_it < var_linker.len() && var_bind_des_it.is_some() {
            let var_bind = calc_alg_context
                .process_context()
                .var_binding_des(var_bind_des_it)
                .get_variable_binding();
            let variable_matches = calc_alg_context
                .process_context()
                .var_binding(var_bind)
                .get_binded_variable()
                == var_linker[var_linker_it];
            if variable_matches {
                let next_key_var_bind_des_linker = calc_alg_context
                    .process_context_mut()
                    .alloc_var_binding_des(VariableBindingDescriptor::new());
                calc_alg_context
                    .process_context_mut()
                    .var_binding_des_mut(next_key_var_bind_des_linker)
                    .init_variable_binding_descriptor(var_bind);
                if last_key_var_bind_des_linker.is_some() {
                    calc_alg_context
                        .process_context_mut()
                        .var_binding_des_mut(last_key_var_bind_des_linker)
                        .set_next(next_key_var_bind_des_linker);
                    last_key_var_bind_des_linker = next_key_var_bind_des_linker;
                } else {
                    key_var_bind_des_linker = next_key_var_bind_des_linker;
                    last_key_var_bind_des_linker = next_key_var_bind_des_linker;
                }
                var_linker_it += 1;
                var_bind_des_it = calc_alg_context
                    .process_context()
                    .var_binding_des(var_bind_des_it)
                    .get_next();
            } else {
                var_bind_des_it = calc_alg_context
                    .process_context()
                    .var_binding_des(var_bind_des_it)
                    .get_next();
            }
        }
        key_var_bind_des_linker
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::triggerVariableBindingPathJoining`.
    pub fn trigger_variable_binding_path_joining(
        &mut self,
        process_indi: NodeId,
        var_bind_path_des: VarBindingPathDescriptorId,
        var_bind_des: VarBindingDescriptorId,
        left_triggered: bool,
        var_bind_trigger_hash: VariableBindingTriggerHashId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut next_var_bind_des_trigger: VarBindingDescriptorId = var_bind_des;
        if next_var_bind_des_trigger.is_some() {
            while next_var_bind_des_trigger.is_some() {
                let var_bind = calc_alg_context
                    .process_context()
                    .var_binding_des(next_var_bind_des_trigger)
                    .get_variable_binding();
                next_var_bind_des_trigger = calc_alg_context
                    .process_context()
                    .var_binding_des(next_var_bind_des_trigger)
                    .get_next();
                let variable = calc_alg_context
                    .process_context()
                    .var_binding(var_bind)
                    .get_binded_variable();
                let indi_node = calc_alg_context
                    .process_context()
                    .var_binding(var_bind)
                    .get_binded_individual();
                let mut trigger_hash = std::mem::replace(
                    calc_alg_context
                        .process_context_mut()
                        .vbtrigger_hash_mut(var_bind_trigger_hash),
                    VariableBindingTriggerHash::new(INVALID),
                );
                let inserted = trigger_hash.try_insert_variable_binding_trigger(
                    calc_alg_context.process_context_mut(),
                    variable,
                    indi_node,
                    var_bind_path_des,
                    next_var_bind_des_trigger,
                    left_triggered,
                );
                *calc_alg_context
                    .process_context_mut()
                    .vbtrigger_hash_mut(var_bind_trigger_hash) = trigger_hash;
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
        var_binding_path_set: &mut VarBindingPathSetId,
        var_binding_path_set_hash: ConceptVariableBindingPathSetHashId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if *join_con_des == Id::NONE {
            let mut process_indi_mut = process_indi;
            *join_con_des = self.add_concept_to_individual_return_concept_descriptor(
                join_concept,
                false,
                &mut process_indi_mut,
                merged_dependency_track_point,
                false,
                false,
                calc_alg_context,
            );
        }
        if var_binding_path_set.is_none() {
            let join_tag = calc_alg_context
                .ontology_arenas()
                .concept(join_concept)
                .get_concept_tag();
            *var_binding_path_set =
                ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                    calc_alg_context.process_context_mut(),
                    var_binding_path_set_hash,
                    join_tag,
                    true,
                );
            calc_alg_context
                .process_context_mut()
                .vbpath_set_mut(*var_binding_path_set)
                .set_concept_descriptor(*join_con_des);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::getJoinedVariableBindingPath`.
    pub fn get_joined_variable_binding_path(
        &mut self,
        left_var_bind_path: VarBindingPathId,
        right_var_bind_path: VarBindingPathId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> VarBindingPathId {
        let var_bind_path_merging_hash = {
            let current = calc_alg_context
                .processing_data_box()
                .use_var_binding_path_merging_hash;
            let loc = calc_alg_context
                .processing_data_box()
                .loc_var_binding_path_merging_hash;
            if loc.is_none() {
                let new_hash = calc_alg_context
                    .process_context_mut()
                    .alloc_vbpath_merging_hash(VariableBindingPathMergingHash::new(INVALID));
                if current.is_some() {
                    let prev_map = calc_alg_context
                        .process_context()
                        .vbpath_merging_hash(current)
                        .map
                        .clone();
                    calc_alg_context
                        .process_context_mut()
                        .vbpath_merging_hash_mut(new_hash)
                        .map = prev_map;
                }
                calc_alg_context
                    .processing_data_box_mut()
                    .loc_var_binding_path_merging_hash = new_hash;
                calc_alg_context
                    .processing_data_box_mut()
                    .use_var_binding_path_merging_hash = new_hash;
                new_hash
            } else {
                current
            }
        };
        let mut merge_hash = std::mem::replace(
            calc_alg_context
                .process_context_mut()
                .vbpath_merging_hash_mut(var_bind_path_merging_hash),
            VariableBindingPathMergingHash::new(INVALID),
        );
        let mut merged_var_bind_path = merge_hash
            .get_merged_variable_binding_path_data(
                calc_alg_context.process_context(),
                left_var_bind_path,
                right_var_bind_path,
            )
            .get_variable_binding_path();
        if merged_var_bind_path.is_none() {
            // W3-DEFER[macro]: STATINC(VARBINDJOINCREATENEWCOUNT, calcAlgContext)

            let mut left_var_bind_des_it = calc_alg_context
                .process_context()
                .vbpath(left_var_bind_path)
                .get_variable_binding_descriptor_linker();
            let mut right_var_bind_des_it = calc_alg_context
                .process_context()
                .vbpath(right_var_bind_path)
                .get_variable_binding_descriptor_linker();

            let mut merged_var_bind_des: VarBindingDescriptorId = Id::NONE;
            let mut last_merged_var_bind_des: VarBindingDescriptorId = Id::NONE;

            while left_var_bind_des_it.is_some() || right_var_bind_des_it.is_some() {
                let mut next_binding = Id::NONE;
                if left_var_bind_des_it.is_some() && right_var_bind_des_it.is_some() {
                    let left_binding = calc_alg_context
                        .process_context()
                        .var_binding_des(left_var_bind_des_it)
                        .get_variable_binding();
                    let right_binding = calc_alg_context
                        .process_context()
                        .var_binding_des(right_var_bind_des_it)
                        .get_variable_binding();
                    let left_le = calc_alg_context
                        .process_context()
                        .var_binding(left_binding)
                        .le_binding(
                            calc_alg_context
                                .process_context()
                                .var_binding(right_binding),
                        );
                    let right_le = calc_alg_context
                        .process_context()
                        .var_binding(right_binding)
                        .le_binding(calc_alg_context.process_context().var_binding(left_binding));
                    if left_le && right_le {
                        next_binding = left_binding;
                        left_var_bind_des_it = calc_alg_context
                            .process_context()
                            .var_binding_des(left_var_bind_des_it)
                            .get_next();
                        right_var_bind_des_it = calc_alg_context
                            .process_context()
                            .var_binding_des(right_var_bind_des_it)
                            .get_next();
                    } else if right_le {
                        next_binding = right_binding;
                        right_var_bind_des_it = calc_alg_context
                            .process_context()
                            .var_binding_des(right_var_bind_des_it)
                            .get_next();
                    } else if left_le {
                        next_binding = left_binding;
                        left_var_bind_des_it = calc_alg_context
                            .process_context()
                            .var_binding_des(left_var_bind_des_it)
                            .get_next();
                    }
                } else if left_var_bind_des_it.is_some() {
                    next_binding = calc_alg_context
                        .process_context()
                        .var_binding_des(left_var_bind_des_it)
                        .get_variable_binding();
                    left_var_bind_des_it = calc_alg_context
                        .process_context()
                        .var_binding_des(left_var_bind_des_it)
                        .get_next();
                } else if right_var_bind_des_it.is_some() {
                    next_binding = calc_alg_context
                        .process_context()
                        .var_binding_des(right_var_bind_des_it)
                        .get_variable_binding();
                    right_var_bind_des_it = calc_alg_context
                        .process_context()
                        .var_binding_des(right_var_bind_des_it)
                        .get_next();
                }

                if next_binding.is_some() {
                    let next_merged_var_bind_des = calc_alg_context
                        .process_context_mut()
                        .alloc_var_binding_des(VariableBindingDescriptor::new());
                    calc_alg_context
                        .process_context_mut()
                        .var_binding_des_mut(next_merged_var_bind_des)
                        .init_variable_binding_descriptor(next_binding);
                    if last_merged_var_bind_des.is_some() {
                        calc_alg_context
                            .process_context_mut()
                            .var_binding_des_mut(last_merged_var_bind_des)
                            .set_next(next_merged_var_bind_des);
                        last_merged_var_bind_des = next_merged_var_bind_des;
                    } else {
                        merged_var_bind_des = next_merged_var_bind_des;
                        last_merged_var_bind_des = next_merged_var_bind_des;
                    }
                }
            }

            merged_var_bind_path = calc_alg_context
                .process_context_mut()
                .alloc_vbpath(VariableBindingPath::new());
            let next_path_id = calc_alg_context
                .processing_data_box_mut()
                .next_variable_binding_path_id(true);
            calc_alg_context
                .process_context_mut()
                .vbpath_mut(merged_var_bind_path)
                .init_variable_binding_path(next_path_id, merged_var_bind_des);
            merge_hash
                .get_merged_variable_binding_path_data(
                    calc_alg_context.process_context(),
                    left_var_bind_path,
                    right_var_bind_path,
                )
                .set_variable_binding_path(merged_var_bind_path);
        }
        *calc_alg_context
            .process_context_mut()
            .vbpath_merging_hash_mut(var_bind_path_merging_hash) = merge_hash;
        merged_var_bind_path
    }
}
