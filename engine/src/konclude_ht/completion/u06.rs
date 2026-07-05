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
//! KONCLUDE-PORT-NOTE[api]: this unit was originally an opaque W3 skeleton over
//! the variable-binding / representative-propagation satellite subsystem. The
//! representative AND path is now live through W57 (`applyREPRESENTATIVEANDRule`,
//! `createREPRESENTATIVEANDDependency`, `propagateRepresentative`,
//! `updateRepresentativePropagationSet`, and `requiresRepresentativePropagation`).
//! The remaining deferred paths in this unit are the wider variable-binding and
//! propagation-binding transition-extension tails plus rule-specific dependency
//! wrappers that still carry explicit `W3-DEFER` markers at their C++ call sites.

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
use super::super::process::binding_hash::{
    ConceptPropagationBindingSetHash, ConceptVariableBindingPathSetHash,
};
use super::super::process::propagation_binding::{
    PropagationBindingSet, PropagationVariableBindingTransitionExtension,
};
use super::super::process::representative::{
    ConceptRepresentativePropagationSetHash, ConceptRepresentativePropagationSetHashId,
    RepresentativePropagationDescriptorId, RepresentativePropagationSetId,
    RepresentativeVariableBindingPathSetData,
};
use super::super::process::varbind::{
    VarBindingPathDescriptorId, VarBindingPathSetId, VarBindingTriggerLinkerId, VariableBinding,
    VariableBindingDescriptor, VariableBindingPath, VariableBindingPathDescriptor,
    VariableBindingPathSet,
};
use super::super::process::{
    ConDescId, ConProcDescId, DepLinkId, EdgeId, LabelSetId, NodeId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;
use super::grounding::ConceptNominalSchemaGroundingHandler;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyREPRESENTATIVEANDRule`.
    /// W51-W56 ported the representative-propagation hash, set lookup, and typed
    /// propagation helpers this rule calls; the body below is the live
    /// representative-AND integration point.
    pub fn apply_representative_and_rule(
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let concept_negation: bool = negate;
        let _dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let op_con_linker = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        let mut con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);

        let mut con_rep_prop_hash: ConceptRepresentativePropagationSetHashId = Id::NONE;
        let mut prev_rep_prop_set: RepresentativePropagationSetId = Id::NONE;
        let mut proc_rep_prop_des: RepresentativePropagationDescriptorId = Id::NONE;
        let mut prop_dep_track_point: TrackPointId = Id::NONE;
        let mut next_dep_track_point: TrackPointId = Id::NONE;

        // W3-DEFER[macro]: STATINC(VARBINDRULEANDAPPLICATIONCOUNT, calc_alg_context)

        for op_con_linker_it in op_con_linker.iter() {
            let binding_trigger_concept: ConceptId = op_con_linker_it.target;
            let binding_trigger_concept_negation: bool =
                op_con_linker_it.negated ^ concept_negation;

            if con_rep_prop_hash.is_none() {
                con_rep_prop_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_representative_propagation_set_hash(*process_indi);
            }
            if prev_rep_prop_set.is_none() {
                prev_rep_prop_set =
                    ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                        calc_alg_context.process_context_mut(),
                        con_rep_prop_hash,
                        concept,
                        false,
                    );
            }
            if prev_rep_prop_set.is_some() {
                proc_rep_prop_des = calc_alg_context
                    .process_context()
                    .rep_prop_set(prev_rep_prop_set)
                    .get_outgoing_representative_propagation_descriptor_linker();
            }
            if proc_rep_prop_des.is_some() {
                prop_dep_track_point = calc_alg_context
                    .process_context()
                    .rep_prop_des(proc_rep_prop_des)
                    .get_dependency_track_point();
                let rep_prop_set =
                    ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                        calc_alg_context.process_context_mut(),
                        con_rep_prop_hash,
                        binding_trigger_concept,
                        true,
                    );

                let mut binding_con_des: ConDescId = Id::NONE;
                let mut binding_dep_track_point: TrackPointId = Id::NONE;
                let binding_trigger_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(binding_trigger_concept)
                    .get_concept_tag();
                let mut reapply_queue_empty = true;

                let has_con_des_and_queue = calc_alg_context
                    .process_context()
                    .label_set(con_set)
                    .get_concept_descriptor_and_reapply_queue_state_by_tag(
                        binding_trigger_tag,
                        &mut binding_con_des,
                        &mut binding_dep_track_point,
                        &mut reapply_queue_empty,
                    );
                if !has_con_des_and_queue {
                    self.stat_representative_propagate_count += 1;
                    if next_dep_track_point == Id::NONE {
                        con_set = calc_alg_context
                            .process_context_mut()
                            .node_reapply_concept_label_set(*process_indi);
                        let _rep_prop_dep_node = self.create_representative_and_dependency(
                            &mut next_dep_track_point,
                            process_indi,
                            con_des,
                            prop_dep_track_point,
                            calc_alg_context,
                        );
                    }
                    binding_con_des = self.add_concept_to_individual_return_concept_descriptor(
                        binding_trigger_concept,
                        binding_trigger_concept_negation,
                        process_indi,
                        next_dep_track_point,
                        false,
                        false,
                        calc_alg_context,
                    );
                    calc_alg_context
                        .process_context_mut()
                        .rep_prop_set_mut(rep_prop_set)
                        .set_concept_descriptor(binding_con_des);
                    self.propagate_representative(
                        process_indi,
                        proc_rep_prop_des,
                        rep_prop_set,
                        next_dep_track_point,
                        calc_alg_context,
                    );
                } else {
                    let requires_rep_prop = self.requires_representative_propagation(
                        process_indi,
                        proc_rep_prop_des,
                        rep_prop_set,
                        calc_alg_context,
                    );
                    if requires_rep_prop {
                        self.stat_representative_propagate_count += 1;
                        if next_dep_track_point == Id::NONE {
                            con_set = calc_alg_context
                                .process_context_mut()
                                .node_reapply_concept_label_set(*process_indi);
                            let _rep_prop_dep_node = self.create_representative_and_dependency(
                                &mut next_dep_track_point,
                                process_indi,
                                con_des,
                                prop_dep_track_point,
                                calc_alg_context,
                            );
                        }
                        self.propagate_representative(
                            process_indi,
                            proc_rep_prop_des,
                            rep_prop_set,
                            next_dep_track_point,
                            calc_alg_context,
                        );
                        let out_rep_prop_des = calc_alg_context
                            .process_context()
                            .rep_prop_set(rep_prop_set)
                            .get_outgoing_representative_propagation_descriptor_linker();
                        let rep_data = calc_alg_context
                            .process_context()
                            .rep_prop_des(out_rep_prop_des)
                            .get_representative_variable_binding_path_set_data();
                        let var_count = RepresentativeVariableBindingPathSetData::get_representated_variable_count(
                            calc_alg_context.process_context(),
                            rep_data,
                        );
                        self.reapply_concept_updated_representative_binding_count(
                            *process_indi,
                            binding_con_des,
                            binding_dep_track_point,
                            var_count,
                            con_set,
                            INVALID,
                            calc_alg_context,
                        );
                        let _ = reapply_queue_empty;
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARIABLEBINDINGANDRule`.
    /// W37: descriptor/label/hash reads and same-node initial/fresh propagation
    /// are live. STILL-MISSING: the concrete `CCondensedReapplyQueue*` out-param
    /// from `getConceptDescriptorAndReapplyQueue` for the existing-trigger
    /// reapply drain.
    pub fn apply_variable_binding_and_rule(
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let concept_negation: bool = negate;
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let op_con_linker = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        let mut con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);
        let mut next_dep_track_point: TrackPointId = Id::NONE;

        // W3-DEFER[macro]: STATINC(VARBINDRULEANDAPPLICATIONCOUNT, calc_alg_context)

        for op_con_linker_it in op_con_linker.iter() {
            let binding_trigger_concept: ConceptId = op_con_linker_it.target;
            let binding_trigger_concept_negation: bool =
                op_con_linker_it.negated ^ concept_negation;

            let mut binding_con_des: ConDescId = Id::NONE;
            let mut binding_dep_track_point: TrackPointId = Id::NONE;
            let binding_trigger_tag = calc_alg_context
                .ontology_arenas()
                .concept(binding_trigger_concept)
                .get_concept_tag();
            let mut reapply_queue_empty = true;

            let has_con_des_and_queue = calc_alg_context
                .process_context()
                .label_set(con_set)
                .get_concept_descriptor_and_reapply_queue_state_by_tag(
                    binding_trigger_tag,
                    &mut binding_con_des,
                    &mut binding_dep_track_point,
                    &mut reapply_queue_empty,
                );
            if !has_con_des_and_queue {
                if next_dep_track_point == Id::NONE {
                    con_set = calc_alg_context
                        .process_context_mut()
                        .node_reapply_concept_label_set(*process_indi);
                    let _bind_dep_node = self.create_varbind_propagate_and_dependency(
                        &mut next_dep_track_point,
                        process_indi,
                        con_des,
                        dep_track_point,
                        calc_alg_context,
                    );
                    if next_dep_track_point.is_none() {
                        // W6-DEFER[api]: createVARBINDPROPAGATEANDDependency is
                        // called at the C++ point, but dependency-base
                        // materialization still returns no track point.
                        next_dep_track_point = dep_track_point;
                    }
                }
                binding_con_des = self.add_concept_to_individual_return_concept_descriptor(
                    binding_trigger_concept,
                    binding_trigger_concept_negation,
                    process_indi,
                    next_dep_track_point,
                    false,
                    false,
                    calc_alg_context,
                );

                let con_var_binding_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_variable_binding_path_set_hash(*process_indi);
                let concept_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag();
                let prev_var_binding_path_set =
                    ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                        calc_alg_context.process_context_mut(),
                        con_var_binding_set_hash,
                        concept_tag,
                        false,
                    );
                let var_binding_path_set =
                    ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                        calc_alg_context.process_context_mut(),
                        con_var_binding_set_hash,
                        binding_trigger_tag,
                        true,
                    );
                calc_alg_context
                    .process_context_mut()
                    .vbpath_set_mut(var_binding_path_set)
                    .set_concept_descriptor(binding_con_des);

                self.propagate_initial_variable_bindings(
                    process_indi,
                    binding_con_des,
                    var_binding_path_set,
                    prev_var_binding_path_set,
                    super::super::process::DepLinkId::NONE,
                    con_var_binding_set_hash,
                    calc_alg_context,
                );
            } else {
                let con_var_binding_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_variable_binding_path_set_hash(*process_indi);
                let concept_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag();
                let prev_var_binding_path_set =
                    ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                        calc_alg_context.process_context_mut(),
                        con_var_binding_set_hash,
                        concept_tag,
                        false,
                    );
                let var_binding_path_set =
                    ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                        calc_alg_context.process_context_mut(),
                        con_var_binding_set_hash,
                        binding_trigger_tag,
                        true,
                    );

                let fresh_propagated = self.propagate_fresh_variable_bindings(
                    process_indi,
                    con_des,
                    var_binding_path_set,
                    prev_var_binding_path_set,
                    super::super::process::DepLinkId::NONE,
                    con_var_binding_set_hash,
                    calc_alg_context,
                );
                if fresh_propagated {
                    self.set_individual_node_concept_label_set_modified(
                        process_indi,
                        calc_alg_context,
                    );
                    let con_pro_queue = calc_alg_context
                        .process_context_mut()
                        .node_concept_processing_queue(*process_indi, true);
                    self.add_concept_preprocessed_to_processing_queue_skip(
                        binding_con_des,
                        binding_dep_track_point,
                        con_pro_queue,
                        *process_indi,
                        true,
                        calc_alg_context,
                        INVALID,
                    );
                    let (_, reapply_queue_it) = calc_alg_context
                        .process_context_mut()
                        .node_concept_descriptor_and_reapply_iterator_by_tag(
                            *process_indi,
                            binding_trigger_tag,
                            binding_trigger_concept_negation,
                            true,
                            &mut binding_con_des,
                            &mut binding_dep_track_point,
                        );
                    self.apply_reapply_queue_concepts_condensed_iterator(
                        *process_indi,
                        reapply_queue_it,
                        calc_alg_context,
                    );
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDPROPAGATEALLRule`.
    /// The node role-successor hash and concept-processing queue accessors are
    /// live; this rule now fans out through the current role-successor iterator
    /// surface and reapply queue helpers.
    pub fn apply_varbind_propagate_all_rule(
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let role: RoleId = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_role();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let concept_op_linker = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        // W3-DEFER[macro]: STATINC(VARBINDRULEALLAPPLICATIONCOUNT, calc_alg_context)

        let rest_link: EdgeId =
            self.get_link_processing_restriction(con_pro_des_id, calc_alg_context);
        if rest_link != Id::NONE {
            let mut succ_indi: NodeId =
                self.get_successor_individual(process_indi, rest_link, calc_alg_context);
            self.propagate_variable_bindings_to_successor(
                *process_indi,
                &mut succ_indi,
                &concept_op_linker,
                negate,
                con_des,
                rest_link,
                calc_alg_context,
            );
        } else {
            let role_succ_hash = calc_alg_context
                .process_context()
                .node_reapply_role_successor_hash_existing(*process_indi);
            if role_succ_hash.is_some() {
                let mut role_succ_it = calc_alg_context
                    .process_context()
                    .role_succ_hash(role_succ_hash)
                    .get_role_successor_link_iterator(
                        calc_alg_context.process_context().edges(),
                        role,
                    );
                while role_succ_it.has_next() {
                    let link = role_succ_it.next(true);
                    let mut succ_indi =
                        self.get_successor_individual(process_indi, link, calc_alg_context);
                    self.propagate_variable_bindings_to_successor(
                        *process_indi,
                        &mut succ_indi,
                        &concept_op_linker,
                        negate,
                        con_des,
                        link,
                        calc_alg_context,
                    );
                }
            }
        }
        let is_concept_reapplied = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .is_concept_reapplied();
        if !is_concept_reapplied {
            if !self.is_concept_in_reapply_queue_role(
                con_des,
                role,
                *process_indi,
                calc_alg_context,
            ) {
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

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDVARIABLERule`.
    /// W3-FILL: deferred. STILL-MISSING: `CPropagationVariableBindingTransitionExtension`
    /// analysis state is still incomplete; its analysis mutators
    /// (`get/set_last_analysed_propagation_binding_descriptor`,
    /// `add_analysed_..._return_matched`, `set_triggered_variable_individual_pair`,
    /// `set/is_processing_completed`, `set_last_analysed_propagate_all_flag`) drive the whole
    /// rule and remain the gating surface. The node concept-processing queue is live.
    pub fn apply_varbind_variable_rule(
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let variable: VariableId = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_variable()
            .unwrap_or(Id::NONE);
        let concept_negation: bool = negate;
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let op_con_linker = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        let binding_trigger_concept: ConceptId =
            op_con_linker.first().map(|l| l.target).unwrap_or(Id::NONE);
        let binding_trigger_concept_negation: bool =
            op_con_linker.first().map(|l| l.negated).unwrap_or(false);
        let binding_trigger_tag = calc_alg_context
            .ontology_arenas()
            .concept(binding_trigger_concept)
            .get_concept_tag();

        let mut con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);
        let mut binding_con_des: ConDescId = Id::NONE;
        let mut binding_dep_track_point: TrackPointId = Id::NONE;

        // W3-DEFER[macro]: STATINC(VARBINDRULEBINDAPPLICATIONCOUNT, calc_alg_context)

        let mut update_ext = false;

        let con_prop_binding_set_hash = calc_alg_context
            .process_context()
            .node(*process_indi)
            .use_concept_prop_binding_set_hash;
        let concept_tag = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_tag();
        if con_prop_binding_set_hash.is_some() {
            let prop_binding_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
                calc_alg_context.process_context_mut(),
                con_prop_binding_set_hash,
                concept_tag,
                false,
            );
            if prop_binding_set.is_some() {
                let prop_var_bind_trans_ext = calc_alg_context
                    .process_context()
                    .prop_binding_set(prop_binding_set)
                    .prop_var_bind_trans_extension;
                let processing_not_completed = prop_var_bind_trans_ext.is_none()
                    || !calc_alg_context
                        .process_context()
                        .prop_var_bind_trans_ext(prop_var_bind_trans_ext)
                        .is_processing_completed();
                if processing_not_completed {
                    if prop_var_bind_trans_ext.is_none()
                        || calc_alg_context
                            .process_context()
                            .prop_binding_set(prop_binding_set)
                            .has_propagate_all_flag()
                    {
                        update_ext = true;
                    } else {
                        let last_analy_prop_bind_des = calc_alg_context
                            .process_context()
                            .prop_var_bind_trans_ext(prop_var_bind_trans_ext)
                            .get_last_analysed_propagation_binding_descriptor();
                        let prop_bind_des = calc_alg_context
                            .process_context()
                            .prop_binding_set(prop_binding_set)
                            .get_propagation_binding_descriptor_linker();
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

            let con_prop_binding_set_hash = calc_alg_context
                .process_context_mut()
                .node_concept_propagation_binding_set_hash(*process_indi);
            let prop_binding_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
                calc_alg_context.process_context_mut(),
                con_prop_binding_set_hash,
                concept_tag,
                true,
            );
            let prop_var_bind_trans_ext =
                PropagationBindingSet::get_propagation_variable_binding_transition_extension(
                    calc_alg_context.process_context_mut(),
                    prop_binding_set,
                    true,
                );

            let last_analy_prop_bind_des = calc_alg_context
                .process_context()
                .prop_var_bind_trans_ext(prop_var_bind_trans_ext)
                .get_last_analysed_propagation_binding_descriptor();
            let prop_bind_des = calc_alg_context
                .process_context()
                .prop_binding_set(prop_binding_set)
                .get_propagation_binding_descriptor_linker();

            {
                let indi_id = calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .individual_node_id();
                calc_alg_context
                    .process_context_mut()
                    .prop_var_bind_trans_ext_mut(prop_var_bind_trans_ext)
                    .set_triggered_variable_individual_pair_value((variable, indi_id));
            }
            let mut create_var_binding = false;
            create_var_binding = calc_alg_context
                .process_context()
                .prop_binding_set(prop_binding_set)
                .has_propagate_all_flag();
            let mut prop_bind_des_it = prop_bind_des;
            while prop_bind_des_it != last_analy_prop_bind_des && prop_bind_des_it.is_some() {
                if PropagationVariableBindingTransitionExtension::add_analysed_propagation_binding_descriptor_return_matched(
                    calc_alg_context.process_context_mut(),
                    prop_var_bind_trans_ext,
                    prop_bind_des_it,
                    None,
                ) {
                    create_var_binding = true;
                }
                prop_bind_des_it = calc_alg_context
                    .process_context()
                    .prop_binding_des(prop_bind_des_it)
                    .get_next();
            }
            let propagate_all_flag = calc_alg_context
                .process_context()
                .prop_binding_set(prop_binding_set)
                .has_propagate_all_flag();
            calc_alg_context
                .process_context_mut()
                .prop_var_bind_trans_ext_mut(prop_var_bind_trans_ext)
                .set_last_analysed_propagation_binding_descriptor(prop_bind_des)
                .set_last_analysed_propagate_all_flag(propagate_all_flag);

            if create_var_binding {
                self.stat_var_binding_created_count += 1;
                // W3-DEFER[macro]: STATINC(VARBINDVARIABLEBINDCOUNT, calc_alg_context)
                calc_alg_context
                    .process_context_mut()
                    .prop_var_bind_trans_ext_mut(prop_var_bind_trans_ext)
                    .set_processing_completed(true);

                let con_var_binding_path_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_variable_binding_path_set_hash(*process_indi);
                let var_bind_path_set =
                    ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                        calc_alg_context.process_context_mut(),
                        con_var_binding_path_set_hash,
                        binding_trigger_tag,
                        true,
                    );

                let next_path_prop_id = calc_alg_context
                    .processing_data_box_mut()
                    .next_variable_binding_path_id(true);

                let mut next_dep_track_point: TrackPointId = Id::NONE;
                let _bind_dep_node = self.create_varbind_variable_dependency(
                    &mut next_dep_track_point,
                    process_indi,
                    con_des,
                    dep_track_point,
                    calc_alg_context,
                );
                if next_dep_track_point.is_none() {
                    // W6-DEFER[api]: dependency-base materialization currently
                    // returns no track point; carry the premise dependency.
                    next_dep_track_point = dep_track_point;
                }

                let mut reapply_queue_empty = true;
                let has_con_des_and_queue = calc_alg_context
                    .process_context()
                    .label_set(con_set)
                    .get_concept_descriptor_and_reapply_queue_state_by_tag(
                        binding_trigger_tag,
                        &mut binding_con_des,
                        &mut binding_dep_track_point,
                        &mut reapply_queue_empty,
                    );
                if !has_con_des_and_queue {
                    binding_con_des = self.add_concept_to_individual_return_concept_descriptor(
                        binding_trigger_concept,
                        binding_trigger_concept_negation,
                        process_indi,
                        next_dep_track_point,
                        false,
                        false,
                        calc_alg_context,
                    );
                } else {
                    self.set_individual_node_concept_label_set_modified(
                        process_indi,
                        calc_alg_context,
                    );
                    let con_pro_queue = calc_alg_context
                        .process_context_mut()
                        .node_concept_processing_queue(*process_indi, true);
                    let binding_count = calc_alg_context
                        .process_context()
                        .vbpath_set(var_bind_path_set)
                        .get_variable_binding_path_map()
                        .count();
                    self.add_concept_preprocessed_to_processing_queue(
                        binding_con_des,
                        binding_dep_track_point,
                        con_pro_queue,
                        *process_indi,
                        binding_count,
                        calc_alg_context,
                    );
                    if !reapply_queue_empty {
                        let (_, reapply_queue_it) = calc_alg_context
                            .process_context_mut()
                            .node_concept_descriptor_and_reapply_iterator_by_tag(
                                *process_indi,
                                binding_trigger_tag,
                                binding_trigger_concept_negation,
                                true,
                                &mut binding_con_des,
                                &mut binding_dep_track_point,
                            );
                        self.apply_reapply_queue_concepts_condensed_iterator(
                            *process_indi,
                            reapply_queue_it,
                            calc_alg_context,
                        );
                    }
                }

                calc_alg_context
                    .process_context_mut()
                    .vbpath_set_mut(var_bind_path_set)
                    .set_concept_descriptor(binding_con_des);
                let var_binding = calc_alg_context
                    .process_context_mut()
                    .alloc_var_binding(VariableBinding::new());
                calc_alg_context
                    .process_context_mut()
                    .var_binding_mut(var_binding)
                    .init_variable_binding(next_dep_track_point, *process_indi, variable);
                let var_binding_des = calc_alg_context
                    .process_context_mut()
                    .alloc_var_binding_des(VariableBindingDescriptor::new());
                calc_alg_context
                    .process_context_mut()
                    .var_binding_des_mut(var_binding_des)
                    .init_variable_binding_descriptor(var_binding);
                let var_binding_path = calc_alg_context
                    .process_context_mut()
                    .alloc_vbpath(VariableBindingPath::new());
                calc_alg_context
                    .process_context_mut()
                    .vbpath_mut(var_binding_path)
                    .init_variable_binding_path(next_path_prop_id, var_binding_des);
                let var_binding_path_des = calc_alg_context
                    .process_context_mut()
                    .alloc_vbpath_des(VariableBindingPathDescriptor::new());
                calc_alg_context
                    .process_context_mut()
                    .vbpath_des_mut(var_binding_path_des)
                    .init_variable_binding_path_descriptor(var_binding_path, next_dep_track_point);
                VariableBindingPathSet::add_variable_binding_path(
                    calc_alg_context.process_context_mut(),
                    var_bind_path_set,
                    var_binding_path_des,
                );
                calc_alg_context
                    .process_context_mut()
                    .con_var_bind_path_set_hash_mut(con_var_binding_path_set_hash)
                    .set_last_variable_binding_description_linker(var_binding_path_des);
            }
        }
    }
    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDPROPAGATEJOINRule`.
    /// W42: public descriptor/trigger checks plus the transition-extension join
    /// scan/replay block are live over the typed W41 helpers. STILL-MISSING:
    /// dependency-base materialization for `createVARBINDPROPAGATEJOINDependency`.
    pub fn apply_varbind_propagate_join_rule(
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let op_linker = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        let con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);
        let mut join_con_des: ConDescId = Id::NONE;
        let mut join_dep_track_point: TrackPointId = Id::NONE;

        let join_concept: ConceptId = op_linker.first().map(|l| l.target).unwrap_or(Id::NONE);
        let join_concept_negation: bool = op_linker.first().map(|l| l.negated).unwrap_or(false);
        let join_tag = calc_alg_context
            .ontology_arenas()
            .concept(join_concept)
            .get_concept_tag();
        let trigger_linker: Vec<NegLink<ConceptId>> = op_linker.iter().skip(1).copied().collect();

        // W3-DEFER[macro]: STATINC(VARBINDRULEJOINAPPLICATIONCOUNT, calc_alg_context)

        let mut propagate_joins = false;
        let mut create_join_concept = false;
        let mut reapply_queue_empty = true;
        let has_join_des_and_queue = calc_alg_context
            .process_context()
            .label_set(con_set)
            .get_concept_descriptor_and_reapply_queue_state_by_tag(
                join_tag,
                &mut join_con_des,
                &mut join_dep_track_point,
                &mut reapply_queue_empty,
            );
        if !has_join_des_and_queue {
            // search next not existing trigger
            let mut all_triggers_available = true;
            let mut trigger_break_idx: Option<usize> = None;
            for (idx, next_trigger) in trigger_linker.iter().enumerate() {
                let trigger_concept: ConceptId = next_trigger.target;
                let mut trigger_con_des: ConDescId = Id::NONE;
                let mut trigger_dep_track_point: TrackPointId = Id::NONE;
                let trigger_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(trigger_concept)
                    .get_concept_tag();
                let has_trigger_con_des = calc_alg_context
                    .process_context()
                    .label_set(con_set)
                    .get_concept_descriptor_by_tag(
                        trigger_tag,
                        &mut trigger_con_des,
                        &mut trigger_dep_track_point,
                    );
                if has_trigger_con_des {
                    let trigger_des_negated = calc_alg_context
                        .process_context()
                        .con_desc(trigger_con_des)
                        .is_negated();
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
                if !self.is_concept_in_reapply_queue_concept(
                    con_des,
                    trigger_concept,
                    false,
                    *process_indi,
                    calc_alg_context,
                ) {
                    self.add_concept_to_reapply_queue_concept(
                        con_des,
                        trigger_concept,
                        false,
                        *process_indi,
                        false,
                        dep_track_point,
                        calc_alg_context,
                    );
                }
            }

            let con_prop_binding_set_hash = calc_alg_context
                .process_context()
                .node(*process_indi)
                .use_concept_prop_binding_set_hash;
            let var_binding_path_set_hash = calc_alg_context
                .process_context()
                .node(*process_indi)
                .use_concept_var_bind_path_set_hash;
            if con_prop_binding_set_hash.is_some() && var_binding_path_set_hash.is_some() {
                let concept_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag();
                let prop_binding_set =
                    ConceptPropagationBindingSetHash::get_propagation_binding_set(
                        calc_alg_context.process_context_mut(),
                        con_prop_binding_set_hash,
                        concept_tag,
                        false,
                    );
                if prop_binding_set.is_some() && trigger_linker.len() >= 2 {
                    let prop_var_bind_trans_ext =
                        PropagationBindingSet::get_propagation_variable_binding_transition_extension(
                            calc_alg_context.process_context_mut(),
                            prop_binding_set,
                            false,
                        );

                    let left_concept = trigger_linker[0].target;
                    let right_concept = trigger_linker[1].target;
                    let left_tag = calc_alg_context
                        .ontology_arenas()
                        .concept(left_concept)
                        .get_concept_tag();
                    let right_tag = calc_alg_context
                        .ontology_arenas()
                        .concept(right_concept)
                        .get_concept_tag();

                    let left_var_bind_path_set =
                        ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                            calc_alg_context.process_context_mut(),
                            var_binding_path_set_hash,
                            left_tag,
                            false,
                        );
                    let right_var_bind_path_set =
                        ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                            calc_alg_context.process_context_mut(),
                            var_binding_path_set_hash,
                            right_tag,
                            false,
                        );

                    let mut examine_trans_ext = false;
                    if left_var_bind_path_set.is_some() && right_var_bind_path_set.is_some() {
                        if prop_var_bind_trans_ext.is_none() {
                            examine_trans_ext = true;
                        } else {
                            let prop_set_ref = calc_alg_context
                                .process_context()
                                .prop_binding_set(prop_binding_set);
                            let ext_ref = calc_alg_context
                                .process_context()
                                .prop_var_bind_trans_ext(prop_var_bind_trans_ext);
                            if ext_ref.get_last_analysed_propagate_all_flag()
                                != prop_set_ref.get_propagate_all_flag()
                                || ext_ref.get_last_analysed_propagation_binding_descriptor()
                                    != prop_set_ref.get_propagation_binding_descriptor_linker()
                                || ext_ref.get_left_last_variable_binding_path_joining_descriptor()
                                    != calc_alg_context
                                        .process_context()
                                        .vbpath_set(left_var_bind_path_set)
                                        .get_variable_binding_path_descriptor_linker()
                                || ext_ref.get_right_last_variable_binding_path_joining_descriptor()
                                    != calc_alg_context
                                        .process_context()
                                        .vbpath_set(right_var_bind_path_set)
                                        .get_variable_binding_path_descriptor_linker()
                            {
                                examine_trans_ext = true;
                            }
                        }
                    }

                    if examine_trans_ext {
                        let con_prop_binding_set_hash = calc_alg_context
                            .process_context_mut()
                            .node_concept_propagation_binding_set_hash(*process_indi);
                        let var_binding_path_set_hash = calc_alg_context
                            .process_context_mut()
                            .node_concept_variable_binding_path_set_hash(*process_indi);
                        let prop_binding_set =
                            ConceptPropagationBindingSetHash::get_propagation_binding_set(
                                calc_alg_context.process_context_mut(),
                                con_prop_binding_set_hash,
                                concept_tag,
                                true,
                            );
                        let prop_var_bind_trans_ext =
                            PropagationBindingSet::get_propagation_variable_binding_transition_extension(
                                calc_alg_context.process_context_mut(),
                                prop_binding_set,
                                true,
                            );

                        let mut join_var_binding_path_set: VarBindingPathSetId = Id::NONE;

                        let var_bind_trigger_hash =
                            PropagationVariableBindingTransitionExtension::get_variable_binding_trigger_hash(
                                calc_alg_context.process_context_mut(),
                                prop_var_bind_trans_ext,
                                true,
                            );
                        let var_bind_path_join_hash =
                            PropagationVariableBindingTransitionExtension::get_variable_binding_path_joining_hash(
                                calc_alg_context.process_context_mut(),
                                prop_var_bind_trans_ext,
                                true,
                            );

                        let last_analy_prop_bind_des = calc_alg_context
                            .process_context()
                            .prop_var_bind_trans_ext(prop_var_bind_trans_ext)
                            .get_last_analysed_propagation_binding_descriptor();
                        let prop_bind_des = calc_alg_context
                            .process_context()
                            .prop_binding_set(prop_binding_set)
                            .get_propagation_binding_descriptor_linker();
                        let prop_all_flag = calc_alg_context
                            .process_context()
                            .prop_binding_set(prop_binding_set)
                            .has_propagate_all_flag();

                        if prop_all_flag {
                            let trigger_heads: Vec<VarBindingTriggerLinkerId> = {
                                let trigger_hash_ref = calc_alg_context
                                    .process_context()
                                    .vbtrigger_hash(var_bind_trigger_hash);
                                trigger_hash_ref
                                    .map
                                    .values()
                                    .map(|data| data.get_variable_binding_trigger_linker())
                                    .collect()
                            };
                            {
                                let trigger_hash = calc_alg_context
                                    .process_context_mut()
                                    .vbtrigger_hash_mut(var_bind_trigger_hash);
                                for data in trigger_hash.map.values_mut() {
                                    data.set_triggered(true);
                                    data.clear_variable_binding_trigger_linker();
                                }
                            }
                            for var_bind_trigger_linker in trigger_heads {
                                let mut var_bind_trigger_it = var_bind_trigger_linker;
                                while var_bind_trigger_it.is_some() {
                                    // W3-DEFER[macro]: STATINC(VARBINDJOINTRIGGEREXECUTECOUNT, calcAlgContext)
                                    let var_bind_path_des = calc_alg_context
                                        .process_context()
                                        .vbtrigger_linker(var_bind_trigger_it)
                                        .get_variable_binding_path_descriptor();
                                    let left_triggered = calc_alg_context
                                        .process_context()
                                        .vbtrigger_linker(var_bind_trigger_it)
                                        .is_left_triggered();

                                    propagations_done |= self.propagate_variable_bindings_joins(
                                        *process_indi,
                                        con_des,
                                        join_concept,
                                        var_bind_path_des,
                                        left_triggered,
                                        var_bind_path_join_hash,
                                        var_binding_path_set_hash,
                                        &mut join_con_des,
                                        &mut join_var_binding_path_set,
                                        calc_alg_context,
                                    );
                                    var_bind_trigger_it = calc_alg_context
                                        .process_context()
                                        .vbtrigger_linker(var_bind_trigger_it)
                                        .get_next();
                                }
                            }
                        } else {
                            let mut prop_bind_des_it = prop_bind_des;
                            while prop_bind_des_it.is_some()
                                && prop_bind_des_it != last_analy_prop_bind_des
                            {
                                let mut var_bind_trigger_linker: VarBindingTriggerLinkerId =
                                    Id::NONE;
                                if PropagationVariableBindingTransitionExtension::add_analysed_propagation_binding_descriptor_return_matched(
                                    calc_alg_context.process_context_mut(),
                                    prop_var_bind_trans_ext,
                                    prop_bind_des_it,
                                    Some(&mut var_bind_trigger_linker),
                                ) {
                                    let mut var_bind_trigger_it = var_bind_trigger_linker;
                                    while var_bind_trigger_it.is_some() {
                                        // W3-DEFER[macro]: STATINC(VARBINDJOINTRIGGEREXECUTECOUNT, calcAlgContext)
                                        let var_bind_path_des = calc_alg_context
                                            .process_context()
                                            .vbtrigger_linker(var_bind_trigger_it)
                                            .get_variable_binding_path_descriptor();
                                        let var_bind_trigger_des = calc_alg_context
                                            .process_context()
                                            .vbtrigger_linker(var_bind_trigger_it)
                                            .get_next_trigger_variable_binding_descriptor();
                                        let left_triggered = calc_alg_context
                                            .process_context()
                                            .vbtrigger_linker(var_bind_trigger_it)
                                            .is_left_triggered();

                                        if !self.trigger_variable_binding_path_joining(
                                            *process_indi,
                                            var_bind_path_des,
                                            var_bind_trigger_des,
                                            left_triggered,
                                            var_bind_trigger_hash,
                                            calc_alg_context,
                                        ) {
                                            propagations_done |= self.propagate_variable_bindings_joins(
                                                *process_indi,
                                                con_des,
                                                join_concept,
                                                var_bind_path_des,
                                                left_triggered,
                                                var_bind_path_join_hash,
                                                var_binding_path_set_hash,
                                                &mut join_con_des,
                                                &mut join_var_binding_path_set,
                                                calc_alg_context,
                                            );
                                        }
                                        var_bind_trigger_it = calc_alg_context
                                            .process_context()
                                            .vbtrigger_linker(var_bind_trigger_it)
                                            .get_next();
                                    }
                                }
                                prop_bind_des_it = calc_alg_context
                                    .process_context()
                                    .prop_binding_des(prop_bind_des_it)
                                    .get_next();
                            }
                        }

                        {
                            let ext = calc_alg_context
                                .process_context_mut()
                                .prop_var_bind_trans_ext_mut(prop_var_bind_trans_ext);
                            ext.set_last_analysed_propagation_binding_descriptor(prop_bind_des);
                            ext.set_last_analysed_propagate_all_flag(prop_all_flag);
                        }

                        let left_last = calc_alg_context
                            .process_context()
                            .prop_var_bind_trans_ext(prop_var_bind_trans_ext)
                            .get_left_last_variable_binding_path_joining_descriptor();
                        let left_head = calc_alg_context
                            .process_context()
                            .vbpath_set(left_var_bind_path_set)
                            .get_variable_binding_path_descriptor_linker();
                        if left_last != left_head {
                            let mut var_bind_path_des: VarBindingPathDescriptorId = left_head;
                            while var_bind_path_des.is_some() && var_bind_path_des != left_last {
                                let var_bind_path = calc_alg_context
                                    .process_context()
                                    .vbpath_des(var_bind_path_des)
                                    .get_variable_binding_path();
                                let var_bind_trigger_des = calc_alg_context
                                    .process_context()
                                    .vbpath(var_bind_path)
                                    .get_variable_binding_descriptor_linker();
                                let left_triggered = true;

                                if prop_all_flag
                                    || !self.trigger_variable_binding_path_joining(
                                        *process_indi,
                                        var_bind_path_des,
                                        var_bind_trigger_des,
                                        left_triggered,
                                        var_bind_trigger_hash,
                                        calc_alg_context,
                                    )
                                {
                                    propagations_done |= self.propagate_variable_bindings_joins(
                                        *process_indi,
                                        con_des,
                                        join_concept,
                                        var_bind_path_des,
                                        left_triggered,
                                        var_bind_path_join_hash,
                                        var_binding_path_set_hash,
                                        &mut join_con_des,
                                        &mut join_var_binding_path_set,
                                        calc_alg_context,
                                    );
                                }
                                var_bind_path_des = calc_alg_context
                                    .process_context()
                                    .vbpath_des(var_bind_path_des)
                                    .get_next();
                            }
                            calc_alg_context
                                .process_context_mut()
                                .prop_var_bind_trans_ext_mut(prop_var_bind_trans_ext)
                                .set_left_last_variable_binding_path_joining_descriptor(left_head);
                        }

                        let right_last = calc_alg_context
                            .process_context()
                            .prop_var_bind_trans_ext(prop_var_bind_trans_ext)
                            .get_right_last_variable_binding_path_joining_descriptor();
                        let right_head = calc_alg_context
                            .process_context()
                            .vbpath_set(right_var_bind_path_set)
                            .get_variable_binding_path_descriptor_linker();
                        if right_last != right_head {
                            let mut var_bind_path_des: VarBindingPathDescriptorId = right_head;
                            while var_bind_path_des.is_some() && var_bind_path_des != right_last {
                                let var_bind_path = calc_alg_context
                                    .process_context()
                                    .vbpath_des(var_bind_path_des)
                                    .get_variable_binding_path();
                                let var_bind_trigger_des = calc_alg_context
                                    .process_context()
                                    .vbpath(var_bind_path)
                                    .get_variable_binding_descriptor_linker();
                                let left_triggered = false;

                                if prop_all_flag
                                    || !self.trigger_variable_binding_path_joining(
                                        *process_indi,
                                        var_bind_path_des,
                                        var_bind_trigger_des,
                                        left_triggered,
                                        var_bind_trigger_hash,
                                        calc_alg_context,
                                    )
                                {
                                    propagations_done |= self.propagate_variable_bindings_joins(
                                        *process_indi,
                                        con_des,
                                        join_concept,
                                        var_bind_path_des,
                                        left_triggered,
                                        var_bind_path_join_hash,
                                        var_binding_path_set_hash,
                                        &mut join_con_des,
                                        &mut join_var_binding_path_set,
                                        calc_alg_context,
                                    );
                                }
                                var_bind_path_des = calc_alg_context
                                    .process_context()
                                    .vbpath_des(var_bind_path_des)
                                    .get_next();
                            }
                            calc_alg_context
                                .process_context_mut()
                                .prop_var_bind_trans_ext_mut(prop_var_bind_trans_ext)
                                .set_right_last_variable_binding_path_joining_descriptor(
                                    right_head,
                                );
                        }
                    }
                }
            }
        }

        if propagations_done {
            if !create_join_concept {
                self.set_individual_node_concept_label_set_modified(process_indi, calc_alg_context);
                let con_pro_queue = calc_alg_context
                    .process_context_mut()
                    .node_concept_processing_queue(*process_indi, true);
                let binding_count = if join_con_des.is_some() {
                    let path_hash = calc_alg_context
                        .process_context()
                        .node(*process_indi)
                        .use_concept_var_bind_path_set_hash;
                    if path_hash.is_some() {
                        let join_set =
                            ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                                calc_alg_context.process_context_mut(),
                                path_hash,
                                join_tag,
                                false,
                            );
                        if join_set.is_some() {
                            calc_alg_context
                                .process_context()
                                .vbpath_set(join_set)
                                .get_variable_binding_path_map()
                                .count()
                        } else {
                            0
                        }
                    } else {
                        0
                    }
                } else {
                    0
                };
                self.add_concept_preprocessed_to_processing_queue(
                    join_con_des,
                    join_dep_track_point,
                    con_pro_queue,
                    *process_indi,
                    binding_count,
                    calc_alg_context,
                );
                if !reapply_queue_empty {
                    let (_, reapply_queue_it) = calc_alg_context
                        .process_context_mut()
                        .node_concept_descriptor_and_reapply_iterator_by_tag(
                            *process_indi,
                            join_tag,
                            join_concept_negation,
                            true,
                            &mut join_con_des,
                            &mut join_dep_track_point,
                        );
                    self.apply_reapply_queue_concepts_condensed_iterator(
                        *process_indi,
                        reapply_queue_it,
                        calc_alg_context,
                    );
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDPROPAGATEGROUNDINGRule`.
    /// W46: the `CVariableBindingPathSet*` grounding handler overload is live.
    pub fn apply_varbind_propagate_grounding_rule(
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
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let _negated: bool = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .is_negated();
        let _op_count: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_count();

        let _con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);

        let con_var_bind_path_set_hash = calc_alg_context
            .process_context()
            .node(*process_indi)
            .use_concept_var_bind_path_set_hash;
        let concept_tag = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_tag();
        let var_bind_path_set = if con_var_bind_path_set_hash.is_some() {
            ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                calc_alg_context.process_context_mut(),
                con_var_bind_path_set_hash,
                concept_tag,
                false,
            )
        } else {
            Id::NONE
        };

        // W3-DEFER[macro]: STATINC(VARBINDRULEGROUNDINGAPPLICATIONCOUNT, calc_alg_context)

        if var_bind_path_set.is_some() {
            // W3-DEFER[macro]: KONCLUCE_TASK_ALGORITHM_MODEL_STRING_INSTRUCTION(mBeforeGroundingDebugIndiModelString = generateExtendedDebugIndiModelStringList(...))

            let grounding_hash = calc_alg_context.processing_data_box().use_grounding_hash;
            let mut grounding_handler = ConceptNominalSchemaGroundingHandler::new();
            let grounding_result = grounding_handler
                .get_grounding_concept_linker_for_varbind_path_set(
                    *process_indi,
                    var_bind_path_set,
                    concept,
                    negate,
                    grounding_hash,
                    &mut calc_alg_context.base,
                );
            let new_grounded_linker = grounding_result.new_linker;

            if !new_grounded_linker.is_empty() {
                for new_grounded_linker_it in new_grounded_linker.iter() {
                    // W3-DEFER[macro]: STATINC(VARBINDGROUNDINGCOUNT, calc_alg_context)
                    self.stat_var_binding_grounding_count += 1;
                    let new_grounded_concept: ConceptId = new_grounded_linker_it.target;
                    let new_grounded_concept_negation: bool = new_grounded_linker_it.negated;

                    let mut base_dependency_track_point: TrackPointId = Id::NONE;
                    let additionals_dependencies: Cint64 = INVALID;
                    if let Some(var_bind_path_des) = grounding_result
                        .grounded_con_var_bind_path_des_hash
                        .get(&new_grounded_concept)
                    {
                        let prop_var_dep_track_point = calc_alg_context
                            .process_context()
                            .vbpath_des(*var_bind_path_des)
                            .get_dependency_track_point();
                        if prop_var_dep_track_point.is_some()
                            && base_dependency_track_point.is_none()
                        {
                            base_dependency_track_point = prop_var_dep_track_point;
                        }
                    }

                    if base_dependency_track_point == Id::NONE {
                        base_dependency_track_point = dep_track_point;
                    }

                    let mut next_dep_track_point: TrackPointId = Id::NONE;
                    let _grounding_dep = self.create_varbind_propagate_grounding_dependency(
                        &mut next_dep_track_point,
                        process_indi,
                        con_des,
                        base_dependency_track_point,
                        DepLinkId::NONE,
                        calc_alg_context,
                    );
                    if next_dep_track_point.is_none() {
                        // Konclude returns nullptr when dependency building is
                        // disabled; keep the previous dependency track point in
                        // that configuration.
                        next_dep_track_point = base_dependency_track_point;
                    }

                    self.add_concept_to_individual(
                        new_grounded_concept,
                        new_grounded_concept_negation,
                        process_indi,
                        next_dep_track_point,
                        true,
                        false,
                        calc_alg_context,
                    );
                }
            }

            // W3-DEFER[macro]: KONCLUCE_TASK_ALGORITHM_MODEL_STRING_INSTRUCTION(mAfterGroundingDebugIndiModelString = generateExtendedDebugIndiModelStringList(...))
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDPROPAGATEIMPLICATIONRule`.
    /// W39: descriptor/trigger lookup and same-node initial/fresh propagation
    /// are live. STILL-MISSING: dependency-base object materialization for the
    /// trigger `CDependency*` chain; the dependency factory calls remain at the
    /// C++ points and carry `DepLinkId::NONE` as the base-chain placeholder.
    pub fn apply_varbind_propagate_implication_rule(
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(con_pro_des_id)
            .get_dependency_track_point();
        let op_linker = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        let con_set: LabelSetId = calc_alg_context
            .process_context_mut()
            .node_reapply_concept_label_set(*process_indi);
        let mut binding_con_des: ConDescId = Id::NONE;
        let mut binding_dep_track_point: TrackPointId = Id::NONE;

        let binding_trigger_concept: ConceptId =
            op_linker.first().map(|l| l.target).unwrap_or(Id::NONE);
        let binding_trigger_concept_negation: bool =
            op_linker.first().map(|l| l.negated).unwrap_or(false);
        let binding_trigger_tag = calc_alg_context
            .ontology_arenas()
            .concept(binding_trigger_concept)
            .get_concept_tag();
        let trigger_linker: Vec<NegLink<ConceptId>> = op_linker.iter().skip(1).copied().collect();

        // W3-DEFER[macro]: STATINC(VARBINDRULEIMPLICATIONAPPLICATIONCOUNT, calc_alg_context)

        let mut reapply_queue_empty = true;
        let has_binding_des_and_queue = calc_alg_context
            .process_context()
            .label_set(con_set)
            .get_concept_descriptor_and_reapply_queue_state_by_tag(
                binding_trigger_tag,
                &mut binding_con_des,
                &mut binding_dep_track_point,
                &mut reapply_queue_empty,
            );
        if !has_binding_des_and_queue {
            // search next not existing trigger
            let mut all_triggers_available = true;
            let mut trigger_break_idx: Option<usize> = None;
            for (idx, next_trigger) in trigger_linker.iter().enumerate() {
                let trigger_concept: ConceptId = next_trigger.target;
                let mut trigger_con_des: ConDescId = Id::NONE;
                let mut trigger_dep_track_point: TrackPointId = Id::NONE;
                let trigger_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(trigger_concept)
                    .get_concept_tag();
                let has_trigger_con_des = calc_alg_context
                    .process_context()
                    .label_set(con_set)
                    .get_concept_descriptor_by_tag(
                        trigger_tag,
                        &mut trigger_con_des,
                        &mut trigger_dep_track_point,
                    );
                if has_trigger_con_des {
                    let trigger_des_negated = calc_alg_context
                        .process_context()
                        .con_desc(trigger_con_des)
                        .is_negated();
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
                let trigger_deps = DepLinkId::NONE;
                for trigger_linker_it in trigger_linker.iter() {
                    let trigger_concept: ConceptId = trigger_linker_it.target;
                    let mut trigger_con_des: ConDescId = Id::NONE;
                    let mut trigger_dep_track_point: TrackPointId = Id::NONE;
                    let trigger_tag = calc_alg_context
                        .ontology_arenas()
                        .concept(trigger_concept)
                        .get_concept_tag();
                    let _has_trigger_con_des = calc_alg_context
                        .process_context()
                        .label_set(con_set)
                        .get_concept_descriptor_by_tag(
                            trigger_tag,
                            &mut trigger_con_des,
                            &mut trigger_dep_track_point,
                        );
                    let _conn_dep = self.create_connection_dependency(
                        process_indi,
                        trigger_con_des,
                        trigger_dep_track_point,
                        calc_alg_context,
                    );
                    // W6-DEFER[api]: CDependency::setNext(triggerDeps) base-chain
                    // materialization is not ported; pass DepLinkId::NONE below.
                }

                self.stat_var_binding_implication_count += 1;
                let mut next_dep_track_point: TrackPointId = Id::NONE;
                let _impl_dep_node = self.create_varbind_propagate_implication_dependency(
                    &mut next_dep_track_point,
                    process_indi,
                    con_des,
                    dep_track_point,
                    trigger_deps,
                    calc_alg_context,
                );
                if next_dep_track_point.is_none() {
                    // W6-DEFER[api]: dependency-base materialization currently
                    // returns no track point; carry the premise dependency.
                    next_dep_track_point = dep_track_point;
                }

                binding_con_des = self.add_concept_to_individual_return_concept_descriptor(
                    binding_trigger_concept,
                    binding_trigger_concept_negation,
                    process_indi,
                    next_dep_track_point,
                    true,
                    false,
                    calc_alg_context,
                );

                let con_var_binding_set_hash = calc_alg_context
                    .process_context_mut()
                    .node_concept_variable_binding_path_set_hash(*process_indi);
                let concept_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_concept_tag();
                let prev_var_binding_path_set =
                    ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                        calc_alg_context.process_context_mut(),
                        con_var_binding_set_hash,
                        concept_tag,
                        false,
                    );
                let var_binding_path_set =
                    ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                        calc_alg_context.process_context_mut(),
                        con_var_binding_set_hash,
                        binding_trigger_tag,
                        true,
                    );
                calc_alg_context
                    .process_context_mut()
                    .vbpath_set_mut(var_binding_path_set)
                    .set_concept_descriptor(binding_con_des);

                self.propagate_initial_variable_bindings(
                    process_indi,
                    binding_con_des,
                    var_binding_path_set,
                    prev_var_binding_path_set,
                    trigger_deps,
                    con_var_binding_set_hash,
                    calc_alg_context,
                );
            }
        } else {
            let trigger_deps = DepLinkId::NONE;
            for trigger_linker_it in trigger_linker.iter() {
                let trigger_concept: ConceptId = trigger_linker_it.target;
                let mut trigger_con_des: ConDescId = Id::NONE;
                let mut trigger_dep_track_point: TrackPointId = Id::NONE;
                let trigger_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(trigger_concept)
                    .get_concept_tag();
                let _has_trigger_con_des = calc_alg_context
                    .process_context()
                    .label_set(con_set)
                    .get_concept_descriptor_by_tag(
                        trigger_tag,
                        &mut trigger_con_des,
                        &mut trigger_dep_track_point,
                    );
                let _conn_dep = self.create_connection_dependency(
                    process_indi,
                    trigger_con_des,
                    trigger_dep_track_point,
                    calc_alg_context,
                );
                // W6-DEFER[api]: CDependency::setNext(triggerDeps) base-chain
                // materialization is not ported; pass DepLinkId::NONE below.
            }
            self.stat_var_binding_implication_count += 1;

            let con_var_binding_set_hash = calc_alg_context
                .process_context_mut()
                .node_concept_variable_binding_path_set_hash(*process_indi);
            let concept_tag = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_concept_tag();
            let prev_var_binding_path_set =
                ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                    calc_alg_context.process_context_mut(),
                    con_var_binding_set_hash,
                    concept_tag,
                    false,
                );
            let var_binding_path_set =
                ConceptVariableBindingPathSetHash::get_variable_binding_path_set(
                    calc_alg_context.process_context_mut(),
                    con_var_binding_set_hash,
                    binding_trigger_tag,
                    true,
                );

            let fresh_propagated = self.propagate_fresh_variable_bindings(
                process_indi,
                con_des,
                var_binding_path_set,
                prev_var_binding_path_set,
                trigger_deps,
                con_var_binding_set_hash,
                calc_alg_context,
            );
            if fresh_propagated {
                self.set_individual_node_concept_label_set_modified(process_indi, calc_alg_context);
                let con_pro_queue = calc_alg_context
                    .process_context_mut()
                    .node_concept_processing_queue(*process_indi, true);
                let binding_count = calc_alg_context
                    .process_context()
                    .vbpath_set(var_binding_path_set)
                    .get_variable_binding_path_map()
                    .count();
                self.add_concept_preprocessed_to_processing_queue(
                    binding_con_des,
                    binding_dep_track_point,
                    con_pro_queue,
                    *process_indi,
                    binding_count,
                    calc_alg_context,
                );
                let (_, reapply_queue_it) = calc_alg_context
                    .process_context_mut()
                    .node_concept_descriptor_and_reapply_iterator_by_tag(
                        *process_indi,
                        binding_trigger_tag,
                        binding_trigger_concept_negation,
                        true,
                        &mut binding_con_des,
                        &mut binding_dep_track_point,
                    );
                self.apply_reapply_queue_concepts_condensed_iterator(
                    *process_indi,
                    reapply_queue_it,
                    calc_alg_context,
                );
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVARBINDPREPARERule`.
    /// W3-FILL: deferred. STILL-MISSING: `getSatisfiableAnswererBindingPropagationAdapter` +
    /// `getAnswererPropagationSteeringController` (W4.5 sat sub-struct) — the outer guard;
    /// nothing runs without it. The concept-processing queue is live; the remaining
    /// blocker is the answerer/steering adapter plus the exact prepare-rule binding path.
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
