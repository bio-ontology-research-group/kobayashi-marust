//! `completion::grounding` — port of
//! `CConceptNominalSchemaGroundingHandler`.
//!
//! This module is being ported function-by-function from
//! `Source/Reasoner/Kernel/Algorithm/CConceptNominalSchemaGroundingHandler.cpp`.

#![allow(dead_code)]

use super::super::model::concept::Concept;
use super::super::model::ontology::NominalSchemaTemplateId;
use super::super::model::op::{CCAND, CCNOMINAL, CCNOMVAR, CCOR};
use super::super::model::{ConceptId, NegLink};
use super::super::process::grounding_hash::{
    ConceptNominalSchemaGroundingData, ConceptNominalSchemaGroundingHashId,
};
use super::super::process::node::IndividualProcessNode;
use super::super::process::varbind::{
    RepresentativeVariableBindingPathMap, VarBindingDescriptorId, VarBindingPathDescriptorId,
    VarBindingPathId, VarBindingPathSetId,
};
use super::super::process::{ConDescId, NodeId};
use super::context::CalculationAlgorithmContext;
use std::collections::HashMap;

/// Port of `TConceptPropagationBindingPair`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ConceptPropagationBindingPair {
    pub nominal_concept: ConceptId,
    pub propagation_binding_descriptor: ConDescId,
}

/// Return value for the `CVariableBindingPathSet*` grounding overload.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GroundingConceptLinkerResult {
    pub new_linker: Vec<NegLink<ConceptId>>,
    pub grounded_con_var_bind_path_des_hash: HashMap<ConceptId, VarBindingPathDescriptorId>,
}

/// Return value for the `CRepresentativeVariableBindingPathMap*` grounding overload.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RepresentativeGroundingConceptLinkerResult {
    pub new_linker: Vec<NegLink<ConceptId>>,
    pub grounded_con_var_bind_path_hash: HashMap<ConceptId, VarBindingPathId>,
}

/// Port of `CConceptNominalSchemaGroundingHandler`.
#[derive(Debug, Clone)]
pub struct ConceptNominalSchemaGroundingHandler {
    /// `mLocalizedExtensions`.
    pub localized_extensions: bool,
    /// `mConfReuseGroundedNominalSchemaConcepts`.
    pub conf_reuse_grounded_nominal_schema_concepts: bool,
}

impl Default for ConceptNominalSchemaGroundingHandler {
    fn default() -> Self {
        ConceptNominalSchemaGroundingHandler {
            localized_extensions: false,
            conf_reuse_grounded_nominal_schema_concepts: true,
        }
    }
}

impl ConceptNominalSchemaGroundingHandler {
    /// Port of `CConceptNominalSchemaGroundingHandler::CConceptNominalSchemaGroundingHandler`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `addConceptOperand`.
    pub fn add_concept_operand(
        &self,
        concept: ConceptId,
        op_concept: ConceptId,
        negated: bool,
        calc_alg_context: &mut CalculationAlgorithmContext,
    ) {
        calc_alg_context
            .ontology_arenas_mut()
            .concept_mut(concept)
            .add_operand_linker(op_concept, negated)
            .inc_operand_count(1);
    }

    /// Port of `createNominalSchemaConceptCopy`.
    pub fn create_nominal_schema_concept_copy(
        &self,
        concept: ConceptId,
        calc_alg_context: &mut CalculationAlgorithmContext,
    ) -> ConceptId {
        let con_tag = calc_alg_context.ontology_arenas().concept_count();
        let mut concept_copy = Concept::new();
        {
            let source = calc_alg_context.ontology_arenas().concept(concept);
            concept_copy.init_concept_copy(source);
        }
        concept_copy.set_operand_count(0);
        concept_copy.set_operand_list(Vec::new());
        concept_copy.set_concept_tag(con_tag);
        calc_alg_context
            .ontology_arenas_mut()
            .alloc_concept(concept_copy)
    }

    /// Port of the structural
    /// `createGroundedNominalSchemaConcept(CConcept*, CBOXHASH<...>*, QHash<...>*, ...)`.
    pub fn create_grounded_nominal_schema_concept(
        &mut self,
        concept: ConceptId,
        nominal_schema_template: NominalSchemaTemplateId,
        nom_sch_con_individual_hash: &HashMap<ConceptId, ConceptPropagationBindingPair>,
        grounding_hash: ConceptNominalSchemaGroundingHashId,
        calc_alg_context: &mut CalculationAlgorithmContext,
    ) -> ConceptId {
        let template_values = calc_alg_context
            .ontology_arenas()
            .nominal_schema_template(nominal_schema_template)
            .template_nominal_schema_concepts_for(concept)
            .to_vec();
        if template_values.is_empty() {
            return concept;
        }

        let op_code = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        if op_code == CCNOMVAR {
            return nom_sch_con_individual_hash
                .get(&concept)
                .map(|pair| pair.nominal_concept)
                .unwrap_or(ConceptId::NONE);
        }

        if self.conf_reuse_grounded_nominal_schema_concepts && grounding_hash.is_some() {
            let test_data = self.grounding_data_for_template_values(
                concept,
                &template_values,
                nom_sch_con_individual_hash,
            );
            if let Some(replace_con_data) = calc_alg_context
                .used_process_context()
                .grounding_hash(grounding_hash)
                .value(&test_data)
            {
                return replace_con_data.get_grounded_concept();
            }
        }

        self.force_extension_localisation();
        let copied_concept = self.create_nominal_schema_concept_copy(concept, calc_alg_context);
        let operands = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();
        for op_con_linker in operands {
            let new_op_concept = self.create_grounded_nominal_schema_concept(
                op_con_linker.target,
                nominal_schema_template,
                nom_sch_con_individual_hash,
                grounding_hash,
                calc_alg_context,
            );
            self.add_concept_operand(
                copied_concept,
                new_op_concept,
                op_con_linker.negated,
                calc_alg_context,
            );
        }

        if self.conf_reuse_grounded_nominal_schema_concepts && grounding_hash.is_some() {
            let mut test_data = self.grounding_data_for_template_values(
                concept,
                &template_values,
                nom_sch_con_individual_hash,
            );
            test_data.set_grounded_concept(copied_concept);
            calc_alg_context
                .used_process_context_mut()
                .grounding_hash_mut(grounding_hash)
                .insert(test_data);
        }

        copied_concept
    }

    /// Port of linker-emitting
    /// `createGroundedNominalSchemaConcept(CConcept*, bool, CReapplyConceptLabelSet*, ...)`.
    pub fn create_grounded_nominal_schema_concept_linker(
        &mut self,
        process_node: NodeId,
        concept: ConceptId,
        negated: bool,
        nominal_schema_template: NominalSchemaTemplateId,
        nom_sch_con_individual_hash: &HashMap<ConceptId, ConceptPropagationBindingPair>,
        grounding_hash: ConceptNominalSchemaGroundingHashId,
        calc_alg_context: &mut CalculationAlgorithmContext,
    ) -> Vec<NegLink<ConceptId>> {
        let op_code = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        if (!negated && op_code == CCAND) || (negated && op_code == CCOR) {
            let operands = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            let mut con_linker = Vec::new();
            for op_con_linker in operands {
                let op_con_negation = op_con_linker.negated ^ negated;
                let mut tmp_con_linker = self.create_grounded_nominal_schema_concept_linker(
                    process_node,
                    op_con_linker.target,
                    op_con_negation,
                    nominal_schema_template,
                    nom_sch_con_individual_hash,
                    grounding_hash,
                    calc_alg_context,
                );
                tmp_con_linker.extend(con_linker);
                con_linker = tmp_con_linker;
            }
            con_linker
        } else {
            let grounded_concept = self.create_grounded_nominal_schema_concept(
                concept,
                nominal_schema_template,
                nom_sch_con_individual_hash,
                grounding_hash,
                calc_alg_context,
            );
            let label_set = calc_alg_context
                .used_process_context()
                .node(process_node)
                .use_reapply_con_label_set;
            let already_contained = label_set.is_some()
                && calc_alg_context
                    .used_process_context()
                    .label_set(label_set)
                    .contains_concept_get_negated(grounded_concept, None);
            if already_contained {
                Vec::new()
            } else {
                vec![NegLink {
                    target: grounded_concept,
                    negated,
                }]
            }
        }
    }

    /// Port of `createNominalSchemaGroundingConcepts(..., CPROCESSINGHASH<CConcept*,TConceptPropagationBindingPair>*, CNominalSchemaTemplate*, ...)`.
    pub fn create_nominal_schema_grounding_concepts(
        &mut self,
        process_node: NodeId,
        concept: ConceptId,
        negated: bool,
        nominal_schema_var_binded_nominal_hash: &HashMap<
            ConceptId,
            Vec<ConceptPropagationBindingPair>,
        >,
        nominal_schema_template: NominalSchemaTemplateId,
        grounding_hash: ConceptNominalSchemaGroundingHashId,
        calc_alg_context: &mut CalculationAlgorithmContext,
    ) -> Vec<NegLink<ConceptId>> {
        let mut nom_schema_concepts: Vec<ConceptId> = calc_alg_context
            .ontology_arenas()
            .nominal_schema_template(nominal_schema_template)
            .get_nominal_schema_concept_set()
            .iter()
            .copied()
            .collect();
        nom_schema_concepts.sort_by_key(|concept| concept.raw);

        let mut selected = HashMap::new();
        let mut new_grounded_con_linker = Vec::new();
        self.create_nominal_schema_grounding_concepts_rec(
            0,
            &nom_schema_concepts,
            process_node,
            concept,
            negated,
            nominal_schema_var_binded_nominal_hash,
            &mut selected,
            nominal_schema_template,
            grounding_hash,
            calc_alg_context,
            &mut new_grounded_con_linker,
        );
        new_grounded_con_linker
    }

    #[allow(clippy::too_many_arguments)]
    fn create_nominal_schema_grounding_concepts_rec(
        &mut self,
        var_index: usize,
        nom_schema_concepts: &[ConceptId],
        process_node: NodeId,
        concept: ConceptId,
        negated: bool,
        nominal_schema_var_binded_nominal_hash: &HashMap<
            ConceptId,
            Vec<ConceptPropagationBindingPair>,
        >,
        selected: &mut HashMap<ConceptId, ConceptPropagationBindingPair>,
        nominal_schema_template: NominalSchemaTemplateId,
        grounding_hash: ConceptNominalSchemaGroundingHashId,
        calc_alg_context: &mut CalculationAlgorithmContext,
        new_grounded_con_linker: &mut Vec<NegLink<ConceptId>>,
    ) {
        if var_index == nom_schema_concepts.len() {
            let mut op_con_linker = self.create_grounded_nominal_schema_concept_linker(
                process_node,
                concept,
                negated,
                nominal_schema_template,
                selected,
                grounding_hash,
                calc_alg_context,
            );
            op_con_linker.extend(std::mem::take(new_grounded_con_linker));
            *new_grounded_con_linker = op_con_linker;
            return;
        }

        let nom_sch_concept = nom_schema_concepts[var_index];
        let Some(candidates) = nominal_schema_var_binded_nominal_hash.get(&nom_sch_concept) else {
            return;
        };
        for candidate in candidates {
            selected.insert(nom_sch_concept, *candidate);
            self.create_nominal_schema_grounding_concepts_rec(
                var_index + 1,
                nom_schema_concepts,
                process_node,
                concept,
                negated,
                nominal_schema_var_binded_nominal_hash,
                selected,
                nominal_schema_template,
                grounding_hash,
                calc_alg_context,
                new_grounded_con_linker,
            );
        }
        selected.remove(&nom_sch_concept);
    }

    /// Port of `getGroundingConceptLinker(CIndividualProcessNode*, CVariableBindingPathSet*, ...)`.
    pub fn get_grounding_concept_linker_for_varbind_path_set(
        &mut self,
        process_node: NodeId,
        var_bind_path_set: VarBindingPathSetId,
        concept: ConceptId,
        negated: bool,
        grounding_hash: ConceptNominalSchemaGroundingHashId,
        calc_alg_context: &mut CalculationAlgorithmContext,
    ) -> GroundingConceptLinkerResult {
        self.localized_extensions = false;
        let nom_sch_templ_id = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_parameter();
        let nominal_schema_template = calc_alg_context
            .ontology_arenas()
            .nominal_schema_template_data(nom_sch_templ_id);
        if nominal_schema_template.is_none() {
            return GroundingConceptLinkerResult::default();
        }

        let template_concept = calc_alg_context
            .ontology_arenas()
            .nominal_schema_template(nominal_schema_template)
            .get_template_concept();
        let template_concept_nom_sch_var_set = calc_alg_context
            .ontology_arenas()
            .nominal_schema_template(nominal_schema_template)
            .get_nominal_schema_concept_set()
            .clone();
        let var_bind_path_entries: Vec<VarBindingPathDescriptorId> = calc_alg_context
            .used_process_context()
            .vbpath_set(var_bind_path_set)
            .get_variable_binding_path_map()
            .map
            .values()
            .map(|data| data.get_variable_binding_path_descriptor())
            .filter(|des| des.is_some())
            .collect();

        let mut result = GroundingConceptLinkerResult::default();
        for var_bind_path_des in var_bind_path_entries {
            let var_bind_path = calc_alg_context
                .used_process_context()
                .vbpath_des(var_bind_path_des)
                .get_variable_binding_path();

            let mut nominal_schema_var_binded_nominal_hash: HashMap<
                ConceptId,
                Vec<ConceptPropagationBindingPair>,
            > = HashMap::new();
            let mut all_nominal_concept_set: Option<Vec<ConceptId>> = None;

            let mut var_bind_des_it: VarBindingDescriptorId = calc_alg_context
                .used_process_context()
                .vbpath(var_bind_path)
                .get_variable_binding_descriptor_linker();
            while var_bind_des_it.is_some() {
                let var_bind = calc_alg_context
                    .used_process_context()
                    .var_binding_des(var_bind_des_it)
                    .get_variable_binding();
                let variable = calc_alg_context
                    .used_process_context()
                    .var_binding(var_bind)
                    .get_binded_variable();
                let binded_indi_node = calc_alg_context
                    .used_process_context()
                    .var_binding(var_bind)
                    .get_binded_individual();
                if calc_alg_context
                    .ontology_arenas()
                    .variable(variable)
                    .is_nominal_variable()
                {
                    let nom_sch_var_concept = calc_alg_context
                        .ontology_arenas()
                        .variable(variable)
                        .get_nominal_variable_concept();
                    if template_concept_nom_sch_var_set.contains(&nom_sch_var_concept) {
                        let nominal_concept =
                            self.get_nominal_concept(binded_indi_node, false, calc_alg_context);
                        if nominal_concept.is_some() {
                            nominal_schema_var_binded_nominal_hash
                                .entry(nom_sch_var_concept)
                                .or_default()
                                .push(ConceptPropagationBindingPair {
                                    nominal_concept,
                                    propagation_binding_descriptor: ConDescId::NONE,
                                });
                        }
                    }
                }
                var_bind_des_it = calc_alg_context
                    .used_process_context()
                    .var_binding_des(var_bind_des_it)
                    .get_next();
            }

            let mut template_vars: Vec<ConceptId> =
                template_concept_nom_sch_var_set.iter().copied().collect();
            template_vars.sort_by_key(|concept| concept.raw);
            for nom_sch_var_concept in template_vars {
                if !nominal_schema_var_binded_nominal_hash.contains_key(&nom_sch_var_concept) {
                    if all_nominal_concept_set.is_none() {
                        all_nominal_concept_set =
                            Some(self.collect_all_nominal_concepts(calc_alg_context));
                    }
                    for nominal_concept in all_nominal_concept_set.as_deref().unwrap_or(&[]) {
                        nominal_schema_var_binded_nominal_hash
                            .entry(nom_sch_var_concept)
                            .or_default()
                            .push(ConceptPropagationBindingPair {
                                nominal_concept: *nominal_concept,
                                propagation_binding_descriptor: ConDescId::NONE,
                            });
                    }
                }
            }

            let mut tmp_new_linker = self.create_nominal_schema_grounding_concepts(
                process_node,
                template_concept,
                negated,
                &nominal_schema_var_binded_nominal_hash,
                nominal_schema_template,
                grounding_hash,
                calc_alg_context,
            );
            if !tmp_new_linker.is_empty() {
                for tmp_new_linker_it in tmp_new_linker.iter() {
                    result
                        .grounded_con_var_bind_path_des_hash
                        .insert(tmp_new_linker_it.target, var_bind_path_des);
                }
                tmp_new_linker.extend(result.new_linker);
                result.new_linker = tmp_new_linker;
            }
        }

        result
    }

    /// Port of `getGroundingConceptLinker(CIndividualProcessNode*, CRepresentativeVariableBindingPathMap*, ...)`.
    pub fn get_grounding_concept_linker_for_representative_varbind_path_map(
        &mut self,
        process_node: NodeId,
        rep_var_bind_path_set_map: &RepresentativeVariableBindingPathMap,
        concept: ConceptId,
        negated: bool,
        grounding_hash: ConceptNominalSchemaGroundingHashId,
        calc_alg_context: &mut CalculationAlgorithmContext,
    ) -> RepresentativeGroundingConceptLinkerResult {
        self.localized_extensions = false;
        let nom_sch_templ_id = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_parameter();
        let nominal_schema_template = calc_alg_context
            .ontology_arenas()
            .nominal_schema_template_data(nom_sch_templ_id);
        if nominal_schema_template.is_none() {
            return RepresentativeGroundingConceptLinkerResult::default();
        }

        let template_concept = calc_alg_context
            .ontology_arenas()
            .nominal_schema_template(nominal_schema_template)
            .get_template_concept();
        let template_concept_nom_sch_var_set = calc_alg_context
            .ontology_arenas()
            .nominal_schema_template(nominal_schema_template)
            .get_nominal_schema_concept_set()
            .clone();

        let mut map_entries: Vec<(i64, VarBindingPathId)> = rep_var_bind_path_set_map
            .map
            .iter()
            .map(|(key, data)| (*key, data.get_variable_binding_path()))
            .filter(|(_, path)| path.is_some())
            .collect();
        map_entries.sort_by_key(|(key, _)| *key);

        let mut result = RepresentativeGroundingConceptLinkerResult::default();
        for (_, var_bind_path) in map_entries {
            let mut nominal_schema_var_binded_nominal_hash: HashMap<
                ConceptId,
                Vec<ConceptPropagationBindingPair>,
            > = HashMap::new();
            let mut all_nominal_concept_set: Option<Vec<ConceptId>> = None;

            let mut var_bind_des_it: VarBindingDescriptorId = calc_alg_context
                .used_process_context()
                .vbpath(var_bind_path)
                .get_variable_binding_descriptor_linker();
            while var_bind_des_it.is_some() {
                let var_bind = calc_alg_context
                    .used_process_context()
                    .var_binding_des(var_bind_des_it)
                    .get_variable_binding();
                let variable = calc_alg_context
                    .used_process_context()
                    .var_binding(var_bind)
                    .get_binded_variable();
                let binded_indi_node = calc_alg_context
                    .used_process_context()
                    .var_binding(var_bind)
                    .get_binded_individual();
                if calc_alg_context
                    .ontology_arenas()
                    .variable(variable)
                    .is_nominal_variable()
                {
                    let nom_sch_var_concept = calc_alg_context
                        .ontology_arenas()
                        .variable(variable)
                        .get_nominal_variable_concept();
                    if template_concept_nom_sch_var_set.contains(&nom_sch_var_concept) {
                        let nominal_concept =
                            self.get_nominal_concept(binded_indi_node, false, calc_alg_context);
                        if nominal_concept.is_some() {
                            nominal_schema_var_binded_nominal_hash
                                .entry(nom_sch_var_concept)
                                .or_default()
                                .push(ConceptPropagationBindingPair {
                                    nominal_concept,
                                    propagation_binding_descriptor: ConDescId::NONE,
                                });
                        }
                    }
                }
                var_bind_des_it = calc_alg_context
                    .used_process_context()
                    .var_binding_des(var_bind_des_it)
                    .get_next();
            }

            let mut template_vars: Vec<ConceptId> =
                template_concept_nom_sch_var_set.iter().copied().collect();
            template_vars.sort_by_key(|concept| concept.raw);
            for nom_sch_var_concept in template_vars {
                if !nominal_schema_var_binded_nominal_hash.contains_key(&nom_sch_var_concept) {
                    if all_nominal_concept_set.is_none() {
                        all_nominal_concept_set =
                            Some(self.collect_all_nominal_concepts(calc_alg_context));
                    }
                    for nominal_concept in all_nominal_concept_set.as_deref().unwrap_or(&[]) {
                        nominal_schema_var_binded_nominal_hash
                            .entry(nom_sch_var_concept)
                            .or_default()
                            .push(ConceptPropagationBindingPair {
                                nominal_concept: *nominal_concept,
                                propagation_binding_descriptor: ConDescId::NONE,
                            });
                    }
                }
            }

            let mut tmp_new_linker = self.create_nominal_schema_grounding_concepts(
                process_node,
                template_concept,
                negated,
                &nominal_schema_var_binded_nominal_hash,
                nominal_schema_template,
                grounding_hash,
                calc_alg_context,
            );
            if !tmp_new_linker.is_empty() {
                for tmp_new_linker_it in tmp_new_linker.iter() {
                    result
                        .grounded_con_var_bind_path_hash
                        .insert(tmp_new_linker_it.target, var_bind_path);
                }
                tmp_new_linker.extend(result.new_linker);
                result.new_linker = tmp_new_linker;
            }
        }

        result
    }

    fn grounding_data_for_template_values(
        &self,
        grounding_concept: ConceptId,
        template_values: &[ConceptId],
        nom_sch_con_individual_hash: &HashMap<ConceptId, ConceptPropagationBindingPair>,
    ) -> ConceptNominalSchemaGroundingData {
        let mut data = ConceptNominalSchemaGroundingData::new();
        data.set_grounding_concept(grounding_concept);
        for nom_schem_concept in template_values {
            if let Some(pair) = nom_sch_con_individual_hash.get(nom_schem_concept) {
                data.add_binded_nominal_schema_concept(pair.nominal_concept);
            }
        }
        data
    }

    /// Port of `forceExtensionLocalisation`.
    pub fn force_extension_localisation(&mut self) -> bool {
        if !self.localized_extensions {
            self.localized_extensions = true;
            return true;
        }
        false
    }

    /// Port of `collectAllNominalConcepts`.
    ///
    /// C++ lazily allocates and fills `allNominalConceptSet` from the ABox
    /// `CIndividualVector`, inserting every non-negated `CCNOMINAL` assertion
    /// concept. The Rust port returns the populated set as ids.
    pub fn collect_all_nominal_concepts(
        &self,
        calc_alg_context: &CalculationAlgorithmContext,
    ) -> Vec<ConceptId> {
        let mut all_nominal_concepts = Vec::new();
        for individual in calc_alg_context.ontology_arenas().individual_iter() {
            for ass_con_linker in individual.get_assertion_concept_linker() {
                let ass_con = ass_con_linker.target;
                let ass_con_negation = ass_con_linker.negated;
                if !ass_con_negation
                    && ass_con.is_some()
                    && calc_alg_context
                        .ontology_arenas()
                        .concept(ass_con)
                        .get_operator_code()
                        == CCNOMINAL
                    && !all_nominal_concepts.contains(&ass_con)
                {
                    all_nominal_concepts.push(ass_con);
                }
            }
        }
        all_nominal_concepts
    }

    /// Port of `getNominalConcept(CIndividualProcessNode*, bool, ...)`.
    pub fn get_nominal_concept(
        &self,
        process_node: NodeId,
        force_not_pruned: bool,
        calc_alg_context: &CalculationAlgorithmContext,
    ) -> ConceptId {
        let process_node_ref = calc_alg_context.used_process_context().node(process_node);
        let individual_node_id = process_node_ref.individual_node_id();
        if individual_node_id < 0 {
            return ConceptId::NONE;
        }

        let indi_node = calc_alg_context
            .used_process_context()
            .node(NodeId::new(individual_node_id));
        self.get_nominal_concept_from_node(indi_node, force_not_pruned, calc_alg_context)
    }

    fn get_nominal_concept_from_node(
        &self,
        indi_node: &IndividualProcessNode,
        force_not_pruned: bool,
        calc_alg_context: &CalculationAlgorithmContext,
    ) -> ConceptId {
        if force_not_pruned
            && indi_node
                .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_PURGEDBLOCKED)
        {
            return ConceptId::NONE;
        }

        let nom_indi = indi_node.nominal_individual();
        if nom_indi.is_none() {
            return ConceptId::NONE;
        }
        let nom_indi = calc_alg_context.ontology_arenas().individual(nom_indi);
        for ass_linker in nom_indi.get_assertion_concept_linker() {
            let ass_concept = ass_linker.target;
            if !ass_linker.negated
                && ass_concept.is_some()
                && calc_alg_context
                    .ontology_arenas()
                    .concept(ass_concept)
                    .get_operator_code()
                    == CCNOMINAL
            {
                return ass_concept;
            }
        }
        ConceptId::NONE
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::concept::Concept;
    use super::super::super::model::individual::{Individual, Variable};
    use super::super::super::model::op::{
        CCALL, CCAND, CCATOM, CCNOMVAR, CCVARBINDJOIN, CCVARBINDVARIABLE,
    };
    use super::super::super::model::role::Role;
    use super::super::super::model::{NegLink, VariableId};
    use super::super::super::process::binding_hash::{
        ConceptPropagationBindingSetHash, ConceptVariableBindingPathSetHash,
        ConceptVariableBindingPathSetHashData,
    };
    use super::super::super::process::context::ProcessContext;
    use super::super::super::process::dependency::{DepKind, DependencyNode};
    use super::super::super::process::descriptor::{ConceptDescriptor, ConceptProcessDescriptor};
    use super::super::super::process::edge::IndividualLinkEdge;
    use super::super::super::process::grounding_hash::ConceptNominalSchemaGroundingHash;
    use super::super::super::process::node::IndividualProcessNode;
    use super::super::super::process::representative::{
        ConceptRepresentativePropagationSetHash, RepresentativePropagationDescriptor,
        RepresentativePropagationDescriptorId, RepresentativePropagationMap,
        RepresentativePropagationSet, RepresentativePropagationSetId,
        RepresentativeVariableBindingPathSetData, RepresentativeVariableBindingPathSetDataId,
        RepresentativeVariableBindingPathSetHash, RepresentativeVariableBindingPathSetMigrateData,
    };
    use super::super::super::process::rs1::ReapplyQueueIterator;
    use super::super::super::process::varbind::{
        RepresentativeVariableBindingPathMap, RepresentativeVariableBindingPathMapData,
        VarBindingDescriptorId, VarBindingId, VarBindingPathId, VariableBinding,
        VariableBindingDescriptor, VariableBindingPath, VariableBindingPathDescriptor,
        VariableBindingPathSet,
    };
    use super::super::super::process::{NodeId, TrackPointId};
    use super::super::algorithm::CompletionTaskHandleAlgorithm;
    use super::super::context::CalculationAlgorithmContext;
    use super::super::context::CalculationAlgorithmContextBase;
    use super::super::strategy::ConceptProcessingPriorityStrategy;
    use super::*;

    fn test_context() -> CalculationAlgorithmContext {
        let mut ctx = CalculationAlgorithmContext::new();
        ctx.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        ctx
    }

    fn test_base_context() -> CalculationAlgorithmContextBase {
        let mut ctx = CalculationAlgorithmContextBase::new();
        ctx.base.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        ctx
    }

    #[test]
    fn collect_all_nominal_concepts_matches_abox_nominal_assertions() {
        let mut ctx = test_context();
        let mut nominal = Concept::new();
        nominal.set_operator_code(CCNOMINAL);
        let nominal = ctx.ontology_arenas_mut().alloc_concept(nominal);
        let mut neg_nominal = Concept::new();
        neg_nominal.set_operator_code(CCNOMINAL);
        let neg_nominal = ctx.ontology_arenas_mut().alloc_concept(neg_nominal);
        let mut atom = Concept::new();
        atom.set_operator_code(CCATOM);
        let atom = ctx.ontology_arenas_mut().alloc_concept(atom);

        let mut individual = Individual::new(0);
        individual.add_assertion_concept_linker(NegLink {
            target: atom,
            negated: false,
        });
        individual.add_assertion_concept_linker(NegLink {
            target: neg_nominal,
            negated: true,
        });
        individual.add_assertion_concept_linker(NegLink {
            target: nominal,
            negated: false,
        });
        ctx.ontology_arenas_mut().alloc_individual(individual);

        let handler = ConceptNominalSchemaGroundingHandler::new();
        assert_eq!(handler.collect_all_nominal_concepts(&ctx), vec![nominal]);
    }

    #[test]
    fn get_nominal_concept_respects_purged_blocked_force_guard() {
        let mut ctx = test_context();
        let mut nominal = Concept::new();
        nominal.set_operator_code(CCNOMINAL);
        let nominal = ctx.ontology_arenas_mut().alloc_concept(nominal);

        let mut individual = Individual::new(0);
        individual.add_assertion_concept_linker(NegLink {
            target: nominal,
            negated: false,
        });
        let individual = ctx.ontology_arenas_mut().alloc_individual(individual);

        let mut node = IndividualProcessNode::default();
        node.set_individual_node_id(0);
        node.set_nominal_individual(individual);
        let node = ctx.used_process_context_mut().alloc_node(node);

        let handler = ConceptNominalSchemaGroundingHandler::new();
        assert_eq!(handler.get_nominal_concept(node, false, &ctx), nominal);

        ctx.used_process_context_mut()
            .node_mut(node)
            .add_processing_restriction_flags(IndividualProcessNode::PRF_PURGEDBLOCKED);
        assert_eq!(handler.get_nominal_concept(node, false, &ctx), nominal);
        assert_eq!(
            handler.get_nominal_concept(node, true, &ctx),
            ConceptId::NONE
        );
    }

    #[test]
    fn grounding_handler_constructor_matches_konclude_defaults() {
        let handler = ConceptNominalSchemaGroundingHandler::new();
        assert!(!handler.localized_extensions);
        assert!(handler.conf_reuse_grounded_nominal_schema_concepts);
    }

    #[test]
    fn create_nominal_schema_concept_copy_resets_operands_and_assigns_extended_tag() {
        let mut ctx = test_context();
        let operand = ctx.ontology_arenas_mut().alloc_concept(Concept::new());
        let mut source = Concept::new();
        source.set_operator_code(CCATOM);
        source.set_concept_tag(41);
        source.add_operand_linker(operand, true);
        source.inc_operand_count(1);
        let source = ctx.ontology_arenas_mut().alloc_concept(source);

        let handler = ConceptNominalSchemaGroundingHandler::new();
        let copied = handler.create_nominal_schema_concept_copy(source, &mut ctx);
        let copied_concept = ctx.ontology_arenas().concept(copied);

        assert_eq!(copied_concept.get_operator_code(), CCATOM);
        assert_eq!(copied_concept.get_concept_tag(), copied.raw);
        assert_eq!(copied_concept.get_operand_count(), 0);
        assert!(copied_concept.get_operand_list().is_empty());
    }

    #[test]
    fn add_concept_operand_appends_and_increments_count() {
        let mut ctx = test_context();
        let concept = ctx.ontology_arenas_mut().alloc_concept(Concept::new());
        let operand = ctx.ontology_arenas_mut().alloc_concept(Concept::new());

        let handler = ConceptNominalSchemaGroundingHandler::new();
        handler.add_concept_operand(concept, operand, true, &mut ctx);

        let concept = ctx.ontology_arenas().concept(concept);
        assert_eq!(concept.get_operand_count(), 1);
        assert_eq!(
            concept.get_operand_list(),
            &[NegLink {
                target: operand,
                negated: true
            }]
        );
    }

    #[test]
    fn create_grounded_nominal_schema_concept_replaces_nominal_variable() {
        let mut ctx = test_context();
        let mut nom_var = Concept::new();
        nom_var.set_operator_code(CCNOMVAR);
        let nom_var = ctx.ontology_arenas_mut().alloc_concept(nom_var);
        let mut nominal = Concept::new();
        nominal.set_operator_code(CCNOMINAL);
        let nominal = ctx.ontology_arenas_mut().alloc_concept(nominal);

        let mut templ = super::super::super::model::ontology::NominalSchemaTemplate::new();
        let mut template_hash = HashMap::new();
        template_hash.insert(nom_var, vec![nom_var]);
        templ.set_template_concept_nominal_schema_concept_hash(template_hash);
        let templ = ctx
            .ontology_arenas_mut()
            .alloc_nominal_schema_template(templ);

        let mut bindings = HashMap::new();
        bindings.insert(
            nom_var,
            ConceptPropagationBindingPair {
                nominal_concept: nominal,
                propagation_binding_descriptor: ConDescId::NONE,
            },
        );
        let grounding_hash = ctx
            .used_process_context_mut()
            .alloc_grounding_hash(ConceptNominalSchemaGroundingHash::new(0));

        let mut handler = ConceptNominalSchemaGroundingHandler::new();
        assert_eq!(
            handler.create_grounded_nominal_schema_concept(
                nom_var,
                templ,
                &bindings,
                grounding_hash,
                &mut ctx,
            ),
            nominal
        );
    }

    #[test]
    fn create_grounded_nominal_schema_concept_copies_and_reuses_structural_grounding() {
        let mut ctx = test_context();
        let mut nom_var = Concept::new();
        nom_var.set_operator_code(CCNOMVAR);
        let nom_var = ctx.ontology_arenas_mut().alloc_concept(nom_var);
        let mut nominal = Concept::new();
        nominal.set_operator_code(CCNOMINAL);
        let nominal = ctx.ontology_arenas_mut().alloc_concept(nominal);

        let mut source = Concept::new();
        source.set_operator_code(CCAND);
        source.add_operand_linker(nom_var, false);
        source.inc_operand_count(1);
        let source = ctx.ontology_arenas_mut().alloc_concept(source);

        let mut templ = super::super::super::model::ontology::NominalSchemaTemplate::new();
        let mut template_hash = HashMap::new();
        template_hash.insert(source, vec![nom_var]);
        template_hash.insert(nom_var, vec![nom_var]);
        templ.set_template_concept_nominal_schema_concept_hash(template_hash);
        let templ = ctx
            .ontology_arenas_mut()
            .alloc_nominal_schema_template(templ);

        let mut bindings = HashMap::new();
        bindings.insert(
            nom_var,
            ConceptPropagationBindingPair {
                nominal_concept: nominal,
                propagation_binding_descriptor: ConDescId::NONE,
            },
        );
        let grounding_hash = ctx
            .used_process_context_mut()
            .alloc_grounding_hash(ConceptNominalSchemaGroundingHash::new(0));

        let mut handler = ConceptNominalSchemaGroundingHandler::new();
        let grounded = handler.create_grounded_nominal_schema_concept(
            source,
            templ,
            &bindings,
            grounding_hash,
            &mut ctx,
        );
        assert_ne!(grounded, source);
        assert!(handler.localized_extensions);
        let grounded_concept = ctx.ontology_arenas().concept(grounded);
        assert_eq!(grounded_concept.get_operator_code(), CCAND);
        assert_eq!(grounded_concept.get_operand_count(), 1);
        assert_eq!(
            grounded_concept.get_operand_list(),
            &[NegLink {
                target: nominal,
                negated: false
            }]
        );

        let reused = handler.create_grounded_nominal_schema_concept(
            source,
            templ,
            &bindings,
            grounding_hash,
            &mut ctx,
        );
        assert_eq!(reused, grounded);
    }

    #[test]
    fn create_grounded_nominal_schema_concept_linker_flattens_positive_and() {
        let mut ctx = test_context();
        let mut nom_var_a = Concept::new();
        nom_var_a.set_operator_code(CCNOMVAR);
        let nom_var_a = ctx.ontology_arenas_mut().alloc_concept(nom_var_a);
        let mut nom_var_b = Concept::new();
        nom_var_b.set_operator_code(CCNOMVAR);
        let nom_var_b = ctx.ontology_arenas_mut().alloc_concept(nom_var_b);
        let mut nominal_a = Concept::new();
        nominal_a.set_operator_code(CCNOMINAL);
        let nominal_a = ctx.ontology_arenas_mut().alloc_concept(nominal_a);
        let mut nominal_b = Concept::new();
        nominal_b.set_operator_code(CCNOMINAL);
        let nominal_b = ctx.ontology_arenas_mut().alloc_concept(nominal_b);

        let mut conjunction = Concept::new();
        conjunction.set_operator_code(CCAND);
        conjunction.add_operand_linker(nom_var_a, false);
        conjunction.add_operand_linker(nom_var_b, true);
        conjunction.inc_operand_count(2);
        let conjunction = ctx.ontology_arenas_mut().alloc_concept(conjunction);

        let mut templ = super::super::super::model::ontology::NominalSchemaTemplate::new();
        let mut template_hash = HashMap::new();
        template_hash.insert(conjunction, vec![nom_var_a, nom_var_b]);
        template_hash.insert(nom_var_a, vec![nom_var_a]);
        template_hash.insert(nom_var_b, vec![nom_var_b]);
        templ.set_template_concept_nominal_schema_concept_hash(template_hash);
        let templ = ctx
            .ontology_arenas_mut()
            .alloc_nominal_schema_template(templ);

        let mut bindings = HashMap::new();
        bindings.insert(
            nom_var_a,
            ConceptPropagationBindingPair {
                nominal_concept: nominal_a,
                propagation_binding_descriptor: ConDescId::NONE,
            },
        );
        bindings.insert(
            nom_var_b,
            ConceptPropagationBindingPair {
                nominal_concept: nominal_b,
                propagation_binding_descriptor: ConDescId::NONE,
            },
        );
        let grounding_hash = ctx
            .used_process_context_mut()
            .alloc_grounding_hash(ConceptNominalSchemaGroundingHash::new(0));
        let node = ctx
            .used_process_context_mut()
            .alloc_node(IndividualProcessNode::default());

        let mut handler = ConceptNominalSchemaGroundingHandler::new();
        let linkers = handler.create_grounded_nominal_schema_concept_linker(
            node,
            conjunction,
            false,
            templ,
            &bindings,
            grounding_hash,
            &mut ctx,
        );

        assert_eq!(
            linkers,
            vec![
                NegLink {
                    target: nominal_b,
                    negated: true
                },
                NegLink {
                    target: nominal_a,
                    negated: false
                },
            ]
        );
    }

    #[test]
    fn get_grounding_concept_linker_for_varbind_path_set_grounds_bound_nominal_variable() {
        let mut ctx = test_context();
        let mut nom_var_concept = Concept::new();
        nom_var_concept.set_operator_code(CCNOMVAR);
        let nom_var_concept = ctx.ontology_arenas_mut().alloc_concept(nom_var_concept);
        let mut nominal = Concept::new();
        nominal.set_operator_code(CCNOMINAL);
        let nominal = ctx.ontology_arenas_mut().alloc_concept(nominal);

        let trigger_concept = Concept::new();
        let trigger_concept = ctx.ontology_arenas_mut().alloc_concept(trigger_concept);

        let mut variable = Variable::new();
        variable.init_variable(nom_var_concept, 0);
        let variable = ctx.ontology_arenas_mut().alloc_variable(variable);

        let mut individual = Individual::new(0);
        individual.add_assertion_concept_linker(NegLink {
            target: nominal,
            negated: false,
        });
        let individual = ctx.ontology_arenas_mut().alloc_individual(individual);

        let mut node = IndividualProcessNode::default();
        node.set_individual_node_id(0);
        node.set_nominal_individual(individual);
        let node = ctx.used_process_context_mut().alloc_node(node);

        let mut binding = VariableBinding::new();
        binding.init_variable_binding(TrackPointId::NONE, node, variable);
        let binding = ctx.used_process_context_mut().alloc_var_binding(binding);
        let mut binding_des = VariableBindingDescriptor::new();
        binding_des.init_variable_binding_descriptor(binding);
        let binding_des = ctx
            .used_process_context_mut()
            .alloc_var_binding_des(binding_des);
        let mut path = VariableBindingPath::new();
        path.init_variable_binding_path(77, binding_des);
        let path = ctx.used_process_context_mut().alloc_vbpath(path);
        let mut path_des = VariableBindingPathDescriptor::new();
        path_des.init_variable_binding_path_descriptor(path, TrackPointId::NONE);
        let path_des = ctx.used_process_context_mut().alloc_vbpath_des(path_des);
        let path_set = ctx
            .used_process_context_mut()
            .alloc_vbpath_set(VariableBindingPathSet::new(0));
        VariableBindingPathSet::add_variable_binding_path(
            ctx.used_process_context_mut(),
            path_set,
            path_des,
        );

        let mut templ = super::super::super::model::ontology::NominalSchemaTemplate::new();
        templ.set_template_concept(nom_var_concept);
        let mut template_set = std::collections::HashSet::new();
        template_set.insert(nom_var_concept);
        templ.set_nominal_schema_concept_set(template_set);
        let mut template_hash = HashMap::new();
        template_hash.insert(nom_var_concept, vec![nom_var_concept]);
        templ.set_template_concept_nominal_schema_concept_hash(template_hash);
        let templ = ctx
            .ontology_arenas_mut()
            .alloc_nominal_schema_template(templ);
        ctx.ontology_arenas_mut()
            .concept_mut(trigger_concept)
            .set_parameter(templ.raw);

        let grounding_hash = ctx
            .used_process_context_mut()
            .alloc_grounding_hash(ConceptNominalSchemaGroundingHash::new(0));
        let mut handler = ConceptNominalSchemaGroundingHandler::new();
        let result = handler.get_grounding_concept_linker_for_varbind_path_set(
            node,
            path_set,
            trigger_concept,
            false,
            grounding_hash,
            &mut ctx,
        );

        assert_eq!(
            result.new_linker,
            vec![NegLink {
                target: nominal,
                negated: false
            }]
        );
        assert_eq!(
            result.grounded_con_var_bind_path_des_hash.get(&nominal),
            Some(&path_des)
        );
    }

    #[test]
    fn get_grounding_concept_linker_for_representative_map_records_selected_path() {
        let mut ctx = test_context();
        let mut nom_var_concept = Concept::new();
        nom_var_concept.set_operator_code(CCNOMVAR);
        let nom_var_concept = ctx.ontology_arenas_mut().alloc_concept(nom_var_concept);
        let mut nominal = Concept::new();
        nominal.set_operator_code(CCNOMINAL);
        let nominal = ctx.ontology_arenas_mut().alloc_concept(nominal);

        let trigger_concept = Concept::new();
        let trigger_concept = ctx.ontology_arenas_mut().alloc_concept(trigger_concept);

        let mut variable = Variable::new();
        variable.init_variable(nom_var_concept, 0);
        let variable = ctx.ontology_arenas_mut().alloc_variable(variable);

        let mut individual = Individual::new(0);
        individual.add_assertion_concept_linker(NegLink {
            target: nominal,
            negated: false,
        });
        let individual = ctx.ontology_arenas_mut().alloc_individual(individual);

        let mut node = IndividualProcessNode::default();
        node.set_individual_node_id(0);
        node.set_nominal_individual(individual);
        let node = ctx.used_process_context_mut().alloc_node(node);

        let mut binding = VariableBinding::new();
        binding.init_variable_binding(TrackPointId::NONE, node, variable);
        let binding = ctx.used_process_context_mut().alloc_var_binding(binding);
        let mut binding_des = VariableBindingDescriptor::new();
        binding_des.init_variable_binding_descriptor(binding);
        let binding_des = ctx
            .used_process_context_mut()
            .alloc_var_binding_des(binding_des);
        let mut path = VariableBindingPath::new();
        path.init_variable_binding_path(101, binding_des);
        let path = ctx.used_process_context_mut().alloc_vbpath(path);

        let mut rep_map = RepresentativeVariableBindingPathMap::new(0);
        rep_map.insert(
            101,
            RepresentativeVariableBindingPathMapData::new(
                path,
                RepresentativeVariableBindingPathSetDataId::NONE,
            ),
        );

        let mut templ = super::super::super::model::ontology::NominalSchemaTemplate::new();
        templ.set_template_concept(nom_var_concept);
        let mut template_set = std::collections::HashSet::new();
        template_set.insert(nom_var_concept);
        templ.set_nominal_schema_concept_set(template_set);
        let mut template_hash = HashMap::new();
        template_hash.insert(nom_var_concept, vec![nom_var_concept]);
        templ.set_template_concept_nominal_schema_concept_hash(template_hash);
        let templ = ctx
            .ontology_arenas_mut()
            .alloc_nominal_schema_template(templ);
        ctx.ontology_arenas_mut()
            .concept_mut(trigger_concept)
            .set_parameter(templ.raw);

        let grounding_hash = ctx
            .used_process_context_mut()
            .alloc_grounding_hash(ConceptNominalSchemaGroundingHash::new(0));
        let mut handler = ConceptNominalSchemaGroundingHandler::new();
        let result = handler.get_grounding_concept_linker_for_representative_varbind_path_map(
            node,
            &rep_map,
            trigger_concept,
            false,
            grounding_hash,
            &mut ctx,
        );

        assert_eq!(
            result.new_linker,
            vec![NegLink {
                target: nominal,
                negated: false
            }]
        );
        assert_eq!(
            result.grounded_con_var_bind_path_hash.get(&nominal),
            Some(&path)
        );
    }

    #[test]
    fn apply_varbind_propagate_grounding_rule_adds_grounded_concept_from_path_set() {
        let mut ctx = test_base_context();
        let mut nom_var_concept = Concept::new();
        nom_var_concept.set_operator_code(CCNOMVAR);
        let nom_var_concept = ctx.ontology_arenas_mut().alloc_concept(nom_var_concept);
        let mut nominal = Concept::new();
        nominal.set_operator_code(CCNOMINAL);
        let nominal = ctx.ontology_arenas_mut().alloc_concept(nominal);
        ctx.ontology_arenas_mut()
            .concept_mut(nominal)
            .set_concept_tag(nominal.raw);

        let mut trigger_concept = Concept::new();
        trigger_concept.set_concept_tag(901);
        let trigger_concept = ctx.ontology_arenas_mut().alloc_concept(trigger_concept);

        let mut variable = Variable::new();
        variable.init_variable(nom_var_concept, 0);
        let variable = ctx.ontology_arenas_mut().alloc_variable(variable);

        let mut individual = Individual::new(0);
        individual.add_assertion_concept_linker(NegLink {
            target: nominal,
            negated: false,
        });
        let individual = ctx.ontology_arenas_mut().alloc_individual(individual);

        let mut node = IndividualProcessNode::default();
        node.set_individual_node_id(0);
        node.set_nominal_individual(individual);
        let mut node = ctx.process_context_mut().alloc_node(node);

        let mut binding = VariableBinding::new();
        binding.init_variable_binding(TrackPointId::NONE, node, variable);
        let binding = ctx.process_context_mut().alloc_var_binding(binding);
        let mut binding_des = VariableBindingDescriptor::new();
        binding_des.init_variable_binding_descriptor(binding);
        let binding_des = ctx.process_context_mut().alloc_var_binding_des(binding_des);
        let mut path = VariableBindingPath::new();
        path.init_variable_binding_path(88, binding_des);
        let path = ctx.process_context_mut().alloc_vbpath(path);
        let mut path_des = VariableBindingPathDescriptor::new();
        path_des.init_variable_binding_path_descriptor(path, TrackPointId::NONE);
        let path_des = ctx.process_context_mut().alloc_vbpath_des(path_des);
        let path_set = ctx
            .process_context_mut()
            .alloc_vbpath_set(VariableBindingPathSet::new(0));
        VariableBindingPathSet::add_variable_binding_path(
            ctx.process_context_mut(),
            path_set,
            path_des,
        );

        let mut path_hash = ConceptVariableBindingPathSetHash::new(0);
        path_hash.map.insert(
            901,
            ConceptVariableBindingPathSetHashData {
                loc_variable_binding_path_set: path_set,
                use_variable_binding_path_set: path_set,
            },
        );
        let path_hash = ctx
            .process_context_mut()
            .alloc_con_var_bind_path_set_hash(path_hash);
        ctx.process_context_mut()
            .node_mut(node)
            .use_concept_var_bind_path_set_hash = path_hash;

        let mut templ = super::super::super::model::ontology::NominalSchemaTemplate::new();
        templ.set_template_concept(nom_var_concept);
        let mut template_set = std::collections::HashSet::new();
        template_set.insert(nom_var_concept);
        templ.set_nominal_schema_concept_set(template_set);
        let mut template_hash = HashMap::new();
        template_hash.insert(nom_var_concept, vec![nom_var_concept]);
        templ.set_template_concept_nominal_schema_concept_hash(template_hash);
        let templ = ctx
            .ontology_arenas_mut()
            .alloc_nominal_schema_template(templ);
        ctx.ontology_arenas_mut()
            .concept_mut(trigger_concept)
            .set_parameter(templ.raw);

        let mut con_desc = ConceptDescriptor::new();
        con_desc.concept = trigger_concept;
        con_desc.negated = false;
        let con_desc = ctx.process_context_mut().alloc_con_desc(con_desc);
        let mut con_proc_desc = ConceptProcessDescriptor::new();
        con_proc_desc.concept_des = con_desc;
        let mut con_proc_desc = ctx.process_context_mut().alloc_con_proc_desc(con_proc_desc);

        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;
        algo.apply_varbind_propagate_grounding_rule(&mut node, &mut con_proc_desc, false, &mut ctx);

        let label_set = ctx.process_context().node(node).use_reapply_con_label_set;
        assert!(label_set.is_some());
        assert!(ctx
            .process_context()
            .label_set(label_set)
            .contains_concept(nominal, false));
        let mut added_con_des = ConDescId::NONE;
        let mut added_dep_track_point = TrackPointId::NONE;
        assert!(ctx
            .process_context()
            .label_set(label_set)
            .get_concept_descriptor(nominal, &mut added_con_des, &mut added_dep_track_point,));
        added_dep_track_point = ctx
            .process_context()
            .con_desc(added_con_des)
            .get_dependency_track_point();
        assert!(added_dep_track_point.is_some());
        let dep_node = ctx
            .process_context()
            .track_point(added_dep_track_point)
            .dependency_node();
        assert_eq!(
            ctx.process_context().dep_node(dep_node).kind(),
            DepKind::VarBindPropagateGrounding
        );
    }

    #[test]
    fn create_representative_grounding_dependency_records_selected_path() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;

        let con_desc = ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let path = ctx
            .process_context_mut()
            .alloc_vbpath(VariableBindingPath::new());
        let prev_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let prev_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(prev_dep);
        ctx.process_context_mut()
            .track_point_mut(prev_track_point)
            .add_maximum_branching_tag_candidate(5);
        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let mut continue_track_point = TrackPointId::NONE;

        let dep = algo.create_representative_grounding_dependency(
            &mut continue_track_point,
            &mut node,
            con_desc,
            prev_track_point,
            path,
            &mut ctx,
        );

        assert!(dep.is_some());
        assert!(continue_track_point.is_some());
        let dep_node = ctx.process_context().dep_node(dep);
        assert_eq!(dep_node.kind(), DepKind::RepresentativeGrounding);
        assert!(dep_node.is_representative_select_dependency_node());
        assert_eq!(dep_node.concept_descriptor(), con_desc);
        assert_eq!(dep_node.previous_dependency_track_point(), prev_track_point);
        assert_eq!(dep_node.selected_variable_binding_path(), path);
        assert_eq!(
            ctx.process_context()
                .track_point(continue_track_point)
                .dependency_node(),
            dep
        );
        assert_eq!(
            ctx.process_context()
                .track_point(continue_track_point)
                .get_branching_tag(),
            5
        );
    }

    #[test]
    fn create_representative_and_dependency_materializes_continuation() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;

        let con_desc = ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let prev_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
        let prev_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(prev_dep);
        ctx.process_context_mut()
            .track_point_mut(prev_track_point)
            .add_maximum_branching_tag_candidate(6);
        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let mut continue_track_point = TrackPointId::NONE;

        let dep = algo.create_representative_and_dependency(
            &mut continue_track_point,
            &mut node,
            con_desc,
            prev_track_point,
            &mut ctx,
        );

        assert!(dep.is_some());
        assert!(continue_track_point.is_some());
        let dep_node = ctx.process_context().dep_node(dep);
        assert_eq!(dep_node.kind(), DepKind::RepresentativeAnd);
        assert_eq!(dep_node.concept_descriptor(), con_desc);
        assert_eq!(dep_node.previous_dependency_track_point(), prev_track_point);
        assert_eq!(
            ctx.process_context()
                .track_point(continue_track_point)
                .dependency_node(),
            dep
        );
        assert_eq!(
            ctx.process_context()
                .track_point(continue_track_point)
                .get_branching_tag(),
            6
        );
    }

    #[test]
    fn create_representative_all_dependency_records_link_dependency() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;

        let con_desc = ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let prev_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let prev_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(prev_dep);
        ctx.process_context_mut()
            .track_point_mut(prev_track_point)
            .add_maximum_branching_tag_candidate(7);
        let link_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
        let link_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(link_dep);
        ctx.process_context_mut()
            .track_point_mut(link_track_point)
            .add_maximum_branching_tag_candidate(13);
        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let mut continue_track_point = TrackPointId::NONE;

        let dep = algo.create_representative_all_dependency(
            &mut continue_track_point,
            &mut node,
            con_desc,
            prev_track_point,
            link_track_point,
            &mut ctx,
        );

        assert!(dep.is_some());
        assert!(continue_track_point.is_some());
        let dep_node = ctx.process_context().dep_node(dep);
        assert_eq!(dep_node.kind(), DepKind::RepresentativeAll);
        assert_eq!(dep_node.concept_descriptor(), con_desc);
        assert_eq!(dep_node.previous_dependency_track_point(), prev_track_point);
        let prev_link = match dep_node {
            DependencyNode::DetLink { prev, .. } => *prev,
            _ => panic!("RepresentativeAll must use the one-back-edge dependency shape"),
        };
        assert_eq!(
            ctx.process_context()
                .dep_link(prev_link)
                .previous_dependency_track_point(),
            link_track_point
        );
        assert_eq!(
            ctx.process_context()
                .track_point(continue_track_point)
                .dependency_node(),
            dep
        );
        assert_eq!(
            ctx.process_context()
                .track_point(continue_track_point)
                .get_branching_tag(),
            // max over BOTH back-edges: the bound link dependency is CHAINED
            // onto additional-after (Konclude addAfterDependency), so its tag
            // (13) dominates the prev tag (7).
            13
        );
    }

    #[test]
    fn create_representative_join_dependency_records_other_dependency() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;

        let con_desc = ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let prev_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let prev_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(prev_dep);
        ctx.process_context_mut()
            .track_point_mut(prev_track_point)
            .add_maximum_branching_tag_candidate(8);
        let other_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
        let other_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(other_dep);
        ctx.process_context_mut()
            .track_point_mut(other_track_point)
            .add_maximum_branching_tag_candidate(14);
        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let mut continue_track_point = TrackPointId::NONE;

        let dep = algo.create_representative_join_dependency(
            &mut continue_track_point,
            &mut node,
            con_desc,
            prev_track_point,
            other_track_point,
            &mut ctx,
        );

        assert!(dep.is_some());
        assert!(continue_track_point.is_some());
        let dep_node = ctx.process_context().dep_node(dep);
        assert_eq!(dep_node.kind(), DepKind::RepresentativeJoin);
        assert_eq!(dep_node.concept_descriptor(), con_desc);
        assert_eq!(dep_node.previous_dependency_track_point(), prev_track_point);
        let prev_link = match dep_node {
            DependencyNode::DetLink { prev, .. } => *prev,
            _ => panic!("RepresentativeJoin must use the one-back-edge dependency shape"),
        };
        assert_eq!(
            ctx.process_context()
                .dep_link(prev_link)
                .previous_dependency_track_point(),
            other_track_point
        );
        assert_eq!(
            ctx.process_context()
                .track_point(continue_track_point)
                .dependency_node(),
            dep
        );
        assert_eq!(
            ctx.process_context()
                .track_point(continue_track_point)
                .get_branching_tag(),
            // max over BOTH back-edges (the chained other-dependency tag 14
            // dominates the prev tag 8) — see the RepresentativeAll twin.
            14
        );
    }

    #[test]
    fn create_resolve_representative_dependency_records_maps_and_additional_dependency() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;

        let con_desc = ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let prev_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let prev_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(prev_dep);
        ctx.process_context_mut()
            .track_point_mut(prev_track_point)
            .add_maximum_branching_tag_candidate(3);
        let additional_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
        let additional_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(additional_dep);
        ctx.process_context_mut()
            .track_point_mut(additional_track_point)
            .add_maximum_branching_tag_candidate(12);
        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let mut rep_var_map = RepresentativeVariableBindingPathMap::new(0);
        rep_var_map.insert(
            23,
            RepresentativeVariableBindingPathMapData::new(
                VarBindingPathId::NONE,
                RepresentativeVariableBindingPathSetDataId::NONE,
            ),
        );
        let mut rep_prop_map = RepresentativePropagationMap::new(0);
        rep_prop_map.entry_mut(17);
        let mut continue_track_point = TrackPointId::NONE;

        let dep = algo.create_resolve_representative_dependency(
            &mut continue_track_point,
            &mut node,
            con_desc,
            Some(&rep_var_map),
            Some(&rep_prop_map),
            prev_track_point,
            additional_track_point,
            &mut ctx,
        );

        assert!(dep.is_some());
        assert!(continue_track_point.is_some());
        let dep_node = ctx.process_context().dep_node(dep);
        assert_eq!(dep_node.kind(), DepKind::ResolveRepresentative);
        assert!(dep_node.is_representative_resolve_dependency_node());
        assert_eq!(dep_node.concept_descriptor(), con_desc);
        assert_eq!(dep_node.previous_dependency_track_point(), prev_track_point);
        assert_eq!(
            dep_node
                .resolve_representative_variable_binding_path_map()
                .unwrap()
                .count(),
            1
        );
        assert_eq!(
            dep_node
                .resolve_representative_propagation_map()
                .unwrap()
                .count(),
            1
        );
        assert!(dep_node.has_additional_dependencies());
        let additional_link = dep_node.additional_after_dependencies();
        assert_eq!(
            ctx.process_context()
                .dep_link(additional_link)
                .previous_dependency_track_point(),
            additional_track_point
        );
        assert_eq!(
            ctx.process_context()
                .track_point(continue_track_point)
                .dependency_node(),
            dep
        );
        assert_eq!(
            ctx.process_context()
                .track_point(continue_track_point)
                .get_branching_tag(),
            12
        );
    }

    #[test]
    fn create_resolve_representative_dependency_omits_null_additional_dependency() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;

        let con_desc = ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let prev_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let prev_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(prev_dep);
        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let rep_var_map = RepresentativeVariableBindingPathMap::new(0);
        let rep_prop_map = RepresentativePropagationMap::new(0);
        let mut continue_track_point = TrackPointId::NONE;

        let dep = algo.create_resolve_representative_dependency(
            &mut continue_track_point,
            &mut node,
            con_desc,
            Some(&rep_var_map),
            Some(&rep_prop_map),
            prev_track_point,
            TrackPointId::NONE,
            &mut ctx,
        );

        let dep_node = ctx.process_context().dep_node(dep);
        assert_eq!(dep_node.kind(), DepKind::ResolveRepresentative);
        assert_eq!(dep_node.previous_dependency_track_point(), prev_track_point);
        assert!(!dep_node.has_additional_dependencies());
        assert!(dep_node.additional_after_dependencies().is_none());
        assert_eq!(
            ctx.process_context()
                .track_point(continue_track_point)
                .dependency_node(),
            dep
        );
    }

    #[test]
    fn propagate_representative_adds_incoming_descriptor_to_set() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();

        let rep_data = ctx
            .process_context_mut()
            .alloc_rep_var_bind_path_set_data(RepresentativeVariableBindingPathSetData::new(0, 0));
        ctx.process_context_mut()
            .rep_var_bind_path_set_data_mut(rep_data)
            .set_representative_id(91)
            .add_key_signature_value(17);
        let source_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let source_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(source_dep);
        let source_des = ctx
            .process_context_mut()
            .alloc_rep_prop_des(RepresentativePropagationDescriptor::new());
        ctx.process_context_mut()
            .rep_prop_des_mut(source_des)
            .init_representative_descriptor(rep_data, source_track_point);
        let rep_set = ctx
            .process_context_mut()
            .alloc_rep_prop_set(RepresentativePropagationSet::new(0));
        let next_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
        let next_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(next_dep);
        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());

        algo.propagate_representative(&mut node, source_des, rep_set, next_track_point, &mut ctx);

        let incoming = ctx
            .process_context()
            .rep_prop_set(rep_set)
            .get_incoming_representative_propagation_descriptor_linker();
        assert!(incoming.is_some());
        let incoming_des = ctx.process_context().rep_prop_des(incoming);
        assert_eq!(
            incoming_des.get_representative_variable_binding_path_set_data(),
            rep_data
        );
        assert_eq!(incoming_des.get_dependency_track_point(), next_track_point);
        assert_eq!(
            ctx.process_context()
                .rep_prop_set(rep_set)
                .get_representative_propagation_descriptor(ctx.process_context(), rep_data),
            incoming
        );
        assert_eq!(
            ctx.process_context()
                .rep_prop_set(rep_set)
                .get_outgoing_representative_propagation_descriptor_linker(),
            incoming
        );
        assert_eq!(
            ctx.process_context()
                .rep_prop_set(rep_set)
                .get_last_processed_incoming_representative_propagation_descriptor_linker(),
            incoming
        );
        assert_eq!(
            ctx.process_context()
                .rep_var_bind_path_set_data(rep_data)
                .get_share_count(),
            1
        );
    }

    #[test]
    fn update_representative_propagation_set_folds_new_incoming_into_previous_outgoing() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;

        let con_desc = ctx
            .process_context_mut()
            .alloc_con_desc(ConceptDescriptor::new());
        let rep_set = ctx
            .process_context_mut()
            .alloc_rep_prop_set(RepresentativePropagationSet::new(0));
        ctx.process_context_mut()
            .rep_prop_set_mut(rep_set)
            .set_concept_descriptor(con_desc);

        let old_rep_data = ctx
            .process_context_mut()
            .alloc_rep_var_bind_path_set_data(RepresentativeVariableBindingPathSetData::new(0, 0));
        ctx.process_context_mut()
            .rep_var_bind_path_set_data_mut(old_rep_data)
            .set_representative_id(11)
            .add_key_signature_value(11)
            .set_share_count(1)
            .set_use_count(1)
            .set_migratable(true);
        let old_migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            ctx.process_context_mut(),
            old_rep_data,
            true,
        );
        ctx.process_context_mut()
            .rep_var_bind_path_set_migrate_data_mut(old_migrate_data)
            .get_representative_containing_map_mut()
            .insert_contained_representative(11, old_rep_data, true);
        let mut old_map_data =
            RepresentativeVariableBindingPathMapData::new(VarBindingPathId::NONE, old_rep_data);
        old_map_data.resolve_rep_var_bind_path_set_data_id = 11;
        ctx.process_context_mut()
            .rep_var_bind_path_set_migrate_data_mut(old_migrate_data)
            .get_representative_variable_binding_path_map_mut()
            .insert(101, old_map_data);

        let new_rep_data = ctx
            .process_context_mut()
            .alloc_rep_var_bind_path_set_data(RepresentativeVariableBindingPathSetData::new(0, 0));
        ctx.process_context_mut()
            .rep_var_bind_path_set_data_mut(new_rep_data)
            .set_representative_id(13)
            .add_key_signature_value(13);
        let new_migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            ctx.process_context_mut(),
            new_rep_data,
            true,
        );
        let mut new_map_data =
            RepresentativeVariableBindingPathMapData::new(VarBindingPathId::NONE, new_rep_data);
        new_map_data.resolve_rep_var_bind_path_set_data_id = 13;
        ctx.process_context_mut()
            .rep_var_bind_path_set_migrate_data_mut(new_migrate_data)
            .get_representative_variable_binding_path_map_mut()
            .insert(203, new_map_data);

        let old_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let old_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(old_dep);
        let new_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
        let new_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(new_dep);
        let outgoing_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
        let outgoing_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(outgoing_dep);

        let old_in_des = ctx
            .process_context_mut()
            .alloc_rep_prop_des(RepresentativePropagationDescriptor::new());
        ctx.process_context_mut()
            .rep_prop_des_mut(old_in_des)
            .init_representative_descriptor(old_rep_data, old_track_point);
        RepresentativePropagationSet::add_incoming_representative_propagation(
            ctx.process_context_mut(),
            rep_set,
            old_in_des,
        );
        ctx.process_context_mut()
            .rep_prop_set_mut(rep_set)
            .set_last_processed_incoming_representative_propagation_descriptor_linker(old_in_des);

        let old_out_des = ctx
            .process_context_mut()
            .alloc_rep_prop_des(RepresentativePropagationDescriptor::new());
        ctx.process_context_mut()
            .rep_prop_des_mut(old_out_des)
            .init_representative_descriptor(old_rep_data, outgoing_track_point);
        ctx.process_context_mut()
            .rep_prop_set_mut(rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(old_out_des);

        let new_in_des = ctx
            .process_context_mut()
            .alloc_rep_prop_des(RepresentativePropagationDescriptor::new());
        ctx.process_context_mut()
            .rep_prop_des_mut(new_in_des)
            .init_representative_descriptor(new_rep_data, new_track_point);
        RepresentativePropagationSet::add_incoming_representative_propagation(
            ctx.process_context_mut(),
            rep_set,
            new_in_des,
        );

        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        algo.update_representative_propagation_set(&mut node, rep_set, &mut ctx);

        let outgoing = ctx
            .process_context()
            .rep_prop_set(rep_set)
            .get_outgoing_representative_propagation_descriptor_linker();
        assert!(outgoing.is_some());
        assert_ne!(outgoing, old_out_des);
        assert_eq!(
            ctx.process_context().rep_prop_des(outgoing).get_next(),
            old_out_des
        );
        assert_eq!(
            ctx.process_context()
                .rep_prop_set(rep_set)
                .get_last_processed_incoming_representative_propagation_descriptor_linker(),
            new_in_des
        );

        let folded_rep_data = ctx
            .process_context()
            .rep_prop_des(outgoing)
            .get_representative_variable_binding_path_set_data();
        let folded_migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            ctx.process_context_mut(),
            folded_rep_data,
            false,
        );
        let folded_migrate = ctx
            .process_context()
            .rep_var_bind_path_set_migrate_data(folded_migrate_data);
        assert!(folded_migrate
            .get_representative_containing_map()
            .contains(11));
        assert!(folded_migrate
            .get_representative_containing_map()
            .contains(13));
        assert!(folded_migrate
            .get_representative_variable_binding_path_map()
            .contains(101));
        assert!(folded_migrate
            .get_representative_variable_binding_path_map()
            .contains(203));
        assert_eq!(
            folded_migrate
                .get_representative_variable_binding_path_map()
                .value(203)
                .get_resolve_representative_variable_binding_path_set_data_id(),
            13
        );

        let folded_track_point = ctx
            .process_context()
            .rep_prop_des(outgoing)
            .get_dependency_track_point();
        let folded_dep = ctx
            .process_context()
            .track_point(folded_track_point)
            .dependency_node();
        let folded_dep_node = ctx.process_context().dep_node(folded_dep);
        assert_eq!(folded_dep_node.kind(), DepKind::ResolveRepresentative);
        assert_eq!(
            folded_dep_node.previous_dependency_track_point(),
            new_track_point
        );
        assert!(folded_dep_node.has_additional_dependencies());
        let additional = folded_dep_node.additional_after_dependencies();
        assert_eq!(
            ctx.process_context()
                .dep_link(additional)
                .previous_dependency_track_point(),
            outgoing_track_point
        );
        assert_eq!(
            folded_dep_node
                .resolve_representative_variable_binding_path_map()
                .unwrap()
                .count(),
            2
        );
        assert_eq!(
            folded_dep_node
                .resolve_representative_propagation_map()
                .unwrap()
                .count(),
            2
        );
    }

    fn make_representative_descriptor_with_paths(
        ctx: &mut CalculationAlgorithmContextBase,
        rep_id: i64,
        path_ids: &[i64],
    ) -> (
        RepresentativeVariableBindingPathSetDataId,
        RepresentativePropagationDescriptorId,
    ) {
        let rep_data = ctx
            .process_context_mut()
            .alloc_rep_var_bind_path_set_data(RepresentativeVariableBindingPathSetData::new(0, 0));
        ctx.process_context_mut()
            .rep_var_bind_path_set_data_mut(rep_data)
            .set_representative_id(rep_id)
            .add_key_signature_value(rep_id);
        let migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            ctx.process_context_mut(),
            rep_data,
            true,
        );
        for path_id in path_ids {
            let mut map_data =
                RepresentativeVariableBindingPathMapData::new(VarBindingPathId::NONE, rep_data);
            map_data.resolve_rep_var_bind_path_set_data_id = rep_id;
            ctx.process_context_mut()
                .rep_var_bind_path_set_migrate_data_mut(migrate_data)
                .get_representative_variable_binding_path_map_mut()
                .insert(*path_id, map_data);
        }
        let dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(dep);
        let descriptor = ctx
            .process_context_mut()
            .alloc_rep_prop_des(RepresentativePropagationDescriptor::new());
        ctx.process_context_mut()
            .rep_prop_des_mut(descriptor)
            .init_representative_descriptor(rep_data, track_point);
        (rep_data, descriptor)
    }

    fn make_var_binding(
        ctx: &mut ProcessContext,
        variable: VariableId,
        individual: NodeId,
    ) -> VarBindingId {
        let binding = ctx.alloc_var_binding(VariableBinding::new());
        ctx.var_binding_mut(binding).init_variable_binding(
            TrackPointId::NONE,
            individual,
            variable,
        );
        binding
    }

    fn make_var_binding_path(
        ctx: &mut ProcessContext,
        prop_id: i64,
        bindings: &[VarBindingId],
    ) -> VarBindingPathId {
        let mut head = VarBindingDescriptorId::NONE;
        let mut last = VarBindingDescriptorId::NONE;
        for binding in bindings {
            let descriptor = ctx.alloc_var_binding_des(VariableBindingDescriptor::new());
            ctx.var_binding_des_mut(descriptor)
                .init_variable_binding_descriptor(*binding);
            if last.is_some() {
                ctx.var_binding_des_mut(last).set_next(descriptor);
            } else {
                head = descriptor;
            }
            last = descriptor;
        }
        let path = ctx.alloc_vbpath(VariableBindingPath::new());
        ctx.vbpath_mut(path)
            .init_variable_binding_path(prop_id, head);
        path
    }

    fn make_representative_descriptor_with_var_path(
        ctx: &mut CalculationAlgorithmContextBase,
        rep_id: i64,
        prop_id: i64,
        var_path: VarBindingPathId,
    ) -> (
        RepresentativeVariableBindingPathSetDataId,
        RepresentativePropagationDescriptorId,
    ) {
        let rep_data = ctx
            .process_context_mut()
            .alloc_rep_var_bind_path_set_data(RepresentativeVariableBindingPathSetData::new(0, 0));
        ctx.process_context_mut()
            .rep_var_bind_path_set_data_mut(rep_data)
            .set_representative_id(rep_id)
            .add_key_signature_value(rep_id);
        let migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            ctx.process_context_mut(),
            rep_data,
            true,
        );
        let mut map_data = RepresentativeVariableBindingPathMapData::new(var_path, rep_data);
        map_data.resolve_rep_var_bind_path_set_data_id = rep_id;
        ctx.process_context_mut()
            .rep_var_bind_path_set_migrate_data_mut(migrate_data)
            .get_representative_variable_binding_path_map_mut()
            .insert(prop_id, map_data);
        let rep_hash = ctx.representative_variable_binding_path_set_hash(true);
        RepresentativeVariableBindingPathSetHash::insert_representative_variable_binding_path_set_data(
            ctx.process_context_mut(),
            rep_hash,
            rep_data,
        );

        let dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(dep);
        let descriptor = ctx
            .process_context_mut()
            .alloc_rep_prop_des(RepresentativePropagationDescriptor::new());
        ctx.process_context_mut()
            .rep_prop_des_mut(descriptor)
            .init_representative_descriptor(rep_data, track_point);
        (rep_data, descriptor)
    }

    fn make_representative_set_with_outgoing(
        ctx: &mut CalculationAlgorithmContextBase,
        outgoing_rep_data: RepresentativeVariableBindingPathSetDataId,
        outgoing_descriptor: RepresentativePropagationDescriptorId,
    ) -> RepresentativePropagationSetId {
        let rep_set = ctx
            .process_context_mut()
            .alloc_rep_prop_set(RepresentativePropagationSet::new(0));
        ctx.process_context_mut()
            .rep_prop_set_mut(rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(outgoing_descriptor);
        let rep_id = ctx
            .process_context()
            .rep_var_bind_path_set_data(outgoing_rep_data)
            .get_representative_id();
        ctx.process_context_mut()
            .rep_prop_set_mut(rep_set)
            .get_representative_propagation_map_mut()
            .entry_mut(rep_id)
            .set_representative_propagation_descriptor(outgoing_descriptor);
        rep_set
    }

    #[test]
    fn requires_representative_propagation_rejects_known_representative_id() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let (avail_rep_data, avail_des) =
            make_representative_descriptor_with_paths(&mut ctx, 41, &[1, 2, 3]);
        let (_prop_rep_data, prop_des) =
            make_representative_descriptor_with_paths(&mut ctx, 41, &[4]);
        let rep_set = make_representative_set_with_outgoing(&mut ctx, avail_rep_data, avail_des);
        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());

        assert!(!algo.requires_representative_propagation(&mut node, prop_des, rep_set, &mut ctx));
    }

    #[test]
    fn requires_representative_propagation_rejects_contained_representative() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let (avail_rep_data, avail_des) =
            make_representative_descriptor_with_paths(&mut ctx, 43, &[1, 2, 3]);
        let (prop_rep_data, prop_des) =
            make_representative_descriptor_with_paths(&mut ctx, 47, &[4]);
        let rep_set = ctx
            .process_context_mut()
            .alloc_rep_prop_set(RepresentativePropagationSet::new(0));
        ctx.process_context_mut()
            .rep_prop_set_mut(rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(avail_des);
        let avail_migrate_data = RepresentativeVariableBindingPathSetData::get_migrate_data(
            ctx.process_context_mut(),
            avail_rep_data,
            false,
        );
        ctx.process_context_mut()
            .rep_var_bind_path_set_migrate_data_mut(avail_migrate_data)
            .get_representative_containing_map_mut()
            .insert_contained_representative(47, prop_rep_data, true);
        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());

        assert!(!algo.requires_representative_propagation(&mut node, prop_des, rep_set, &mut ctx));
    }

    #[test]
    fn requires_representative_propagation_direct_lookup_detects_missing_path() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let avail_paths: Vec<i64> = (1..=40).collect();
        let (_avail_rep_data, avail_des) =
            make_representative_descriptor_with_paths(&mut ctx, 53, &avail_paths);
        let (_prop_rep_data, prop_des) =
            make_representative_descriptor_with_paths(&mut ctx, 59, &[7, 99]);
        let rep_set = ctx
            .process_context_mut()
            .alloc_rep_prop_set(RepresentativePropagationSet::new(0));
        ctx.process_context_mut()
            .rep_prop_set_mut(rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(avail_des);
        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());

        assert!(algo.requires_representative_propagation(&mut node, prop_des, rep_set, &mut ctx));

        let (_prop_rep_data, subset_prop_des) =
            make_representative_descriptor_with_paths(&mut ctx, 61, &[7, 8]);
        assert!(!algo.requires_representative_propagation(
            &mut node,
            subset_prop_des,
            rep_set,
            &mut ctx
        ));
    }

    #[test]
    fn requires_representative_propagation_merge_walk_detects_missing_path() {
        let mut ctx = test_base_context();
        let mut algo = CompletionTaskHandleAlgorithm::new();
        let (_avail_rep_data, avail_des) =
            make_representative_descriptor_with_paths(&mut ctx, 67, &[10, 30, 50]);
        let rep_set = ctx
            .process_context_mut()
            .alloc_rep_prop_set(RepresentativePropagationSet::new(0));
        ctx.process_context_mut()
            .rep_prop_set_mut(rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(avail_des);
        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());

        let (_missing_rep_data, missing_prop_des) =
            make_representative_descriptor_with_paths(&mut ctx, 71, &[10, 20]);
        assert!(algo.requires_representative_propagation(
            &mut node,
            missing_prop_des,
            rep_set,
            &mut ctx
        ));

        let (_subset_rep_data, subset_prop_des) =
            make_representative_descriptor_with_paths(&mut ctx, 73, &[10, 50]);
        assert!(!algo.requires_representative_propagation(
            &mut node,
            subset_prop_des,
            rep_set,
            &mut ctx
        ));
    }

    #[test]
    fn apply_representative_and_rule_adds_missing_trigger_and_propagates_representative() {
        let mut ctx = test_base_context();
        let mut trigger = Concept::new();
        trigger.set_operator_code(CCATOM);
        let trigger = ctx.ontology_arenas_mut().alloc_concept(trigger);
        ctx.ontology_arenas_mut()
            .concept_mut(trigger)
            .set_concept_tag(trigger.raw);

        let mut source = Concept::new();
        source.set_operator_code(CCAND);
        source.add_operand_linker(trigger, false);
        let source = ctx.ontology_arenas_mut().alloc_concept(source);
        ctx.ontology_arenas_mut()
            .concept_mut(source)
            .set_concept_tag(source.raw);

        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let con_rep_prop_hash = ctx
            .process_context_mut()
            .node_concept_representative_propagation_set_hash(node);
        let source_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                con_rep_prop_hash,
                source,
                true,
            );
        let (source_rep_data, source_rep_des) =
            make_representative_descriptor_with_paths(&mut ctx, 101, &[301]);
        ctx.process_context_mut()
            .rep_prop_set_mut(source_rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(source_rep_des);

        let mut source_con_desc = ConceptDescriptor::new();
        source_con_desc.concept = source;
        source_con_desc.negated = false;
        let source_con_desc = ctx.process_context_mut().alloc_con_desc(source_con_desc);
        let mut con_proc_desc = ConceptProcessDescriptor::new();
        con_proc_desc.concept_des = source_con_desc;
        con_proc_desc.dep_track_point = ctx
            .process_context()
            .rep_prop_des(source_rep_des)
            .get_dependency_track_point();
        let mut con_proc_desc = ctx.process_context_mut().alloc_con_proc_desc(con_proc_desc);

        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;
        algo.apply_representative_and_rule(&mut node, &mut con_proc_desc, false, &mut ctx);

        let label_set = ctx.process_context().node(node).use_reapply_con_label_set;
        assert!(label_set.is_some());
        assert!(ctx
            .process_context()
            .label_set(label_set)
            .contains_concept(trigger, false));

        let trigger_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                con_rep_prop_hash,
                trigger,
                false,
            );
        assert!(trigger_rep_set.is_some());
        let outgoing = ctx
            .process_context()
            .rep_prop_set(trigger_rep_set)
            .get_outgoing_representative_propagation_descriptor_linker();
        assert!(outgoing.is_some());
        assert_eq!(
            ctx.process_context()
                .rep_prop_des(outgoing)
                .get_representative_variable_binding_path_set_data(),
            source_rep_data
        );
        assert_eq!(
            ctx.process_context()
                .rep_prop_set(trigger_rep_set)
                .get_last_processed_incoming_representative_propagation_descriptor_linker(),
            outgoing
        );
        assert!(ctx
            .process_context()
            .rep_prop_set(trigger_rep_set)
            .get_concept_descriptor()
            .is_some());

        let propagated_track_point = ctx
            .process_context()
            .rep_prop_des(outgoing)
            .get_dependency_track_point();
        let propagated_dep = ctx
            .process_context()
            .track_point(propagated_track_point)
            .dependency_node();
        let dep_node = ctx.process_context().dep_node(propagated_dep);
        assert_eq!(dep_node.kind(), DepKind::RepresentativeAnd);
        assert_eq!(
            dep_node.previous_dependency_track_point(),
            ctx.process_context()
                .rep_prop_des(source_rep_des)
                .get_dependency_track_point()
        );
        assert_eq!(algo.stat_representative_propagate_count, 1);
    }

    #[test]
    fn apply_representative_and_rule_refreshes_existing_trigger_propagation() {
        let mut ctx = test_base_context();
        let mut trigger = Concept::new();
        trigger.set_operator_code(CCATOM);
        let trigger = ctx.ontology_arenas_mut().alloc_concept(trigger);
        ctx.ontology_arenas_mut()
            .concept_mut(trigger)
            .set_concept_tag(trigger.raw);

        let mut source = Concept::new();
        source.set_operator_code(CCAND);
        source.add_operand_linker(trigger, false);
        let source = ctx.ontology_arenas_mut().alloc_concept(source);
        ctx.ontology_arenas_mut()
            .concept_mut(source)
            .set_concept_tag(source.raw);

        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let con_rep_prop_hash = ctx
            .process_context_mut()
            .node_concept_representative_propagation_set_hash(node);
        let source_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                con_rep_prop_hash,
                source,
                true,
            );
        let (source_rep_data, source_rep_des) =
            make_representative_descriptor_with_paths(&mut ctx, 111, &[401]);
        ctx.process_context_mut()
            .rep_prop_set_mut(source_rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(source_rep_des);

        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;
        let trigger_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let trigger_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(trigger_dep);
        let existing_trigger_con_desc = algo.add_concept_to_individual_return_concept_descriptor(
            trigger,
            false,
            &mut node,
            trigger_track_point,
            false,
            false,
            &mut ctx,
        );

        let trigger_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                con_rep_prop_hash,
                trigger,
                true,
            );
        ctx.process_context_mut()
            .rep_prop_set_mut(trigger_rep_set)
            .set_concept_descriptor(existing_trigger_con_desc);

        let mut source_con_desc = ConceptDescriptor::new();
        source_con_desc.concept = source;
        source_con_desc.negated = false;
        let source_con_desc = ctx.process_context_mut().alloc_con_desc(source_con_desc);
        let mut con_proc_desc = ConceptProcessDescriptor::new();
        con_proc_desc.concept_des = source_con_desc;
        con_proc_desc.dep_track_point = ctx
            .process_context()
            .rep_prop_des(source_rep_des)
            .get_dependency_track_point();
        let mut con_proc_desc = ctx.process_context_mut().alloc_con_proc_desc(con_proc_desc);

        algo.stat_representative_propagate_count = 0;
        algo.apply_representative_and_rule(&mut node, &mut con_proc_desc, false, &mut ctx);

        let outgoing = ctx
            .process_context()
            .rep_prop_set(trigger_rep_set)
            .get_outgoing_representative_propagation_descriptor_linker();
        assert!(outgoing.is_some());
        assert_eq!(
            ctx.process_context()
                .rep_prop_des(outgoing)
                .get_representative_variable_binding_path_set_data(),
            source_rep_data
        );
        assert_eq!(
            ctx.process_context()
                .rep_prop_set(trigger_rep_set)
                .get_last_processed_incoming_representative_propagation_descriptor_linker(),
            outgoing
        );
        assert_eq!(algo.stat_representative_propagate_count, 1);
    }

    #[test]
    fn propagate_representative_to_successor_adds_operand_and_propagates() {
        let mut ctx = test_base_context();
        let mut operand = Concept::new();
        operand.set_operator_code(CCATOM);
        let operand = ctx.ontology_arenas_mut().alloc_concept(operand);
        ctx.ontology_arenas_mut()
            .concept_mut(operand)
            .set_concept_tag(operand.raw);

        let mut source = Concept::new();
        source.set_operator_code(CCAND);
        source.add_operand_linker(operand, false);
        let source = ctx.ontology_arenas_mut().alloc_concept(source);
        ctx.ontology_arenas_mut()
            .concept_mut(source)
            .set_concept_tag(source.raw);
        let operands = ctx
            .ontology_arenas()
            .concept(source)
            .get_operand_list()
            .to_vec();

        let process_node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let mut succ_node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());

        let con_rep_prop_hash = ctx
            .process_context_mut()
            .node_concept_representative_propagation_set_hash(process_node);
        let source_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                con_rep_prop_hash,
                source,
                true,
            );
        let (source_rep_data, source_rep_des) =
            make_representative_descriptor_with_paths(&mut ctx, 121, &[501]);
        ctx.process_context_mut()
            .rep_prop_set_mut(source_rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(source_rep_des);

        let mut source_con_desc = ConceptDescriptor::new();
        source_con_desc.concept = source;
        source_con_desc.negated = false;
        source_con_desc.dep_track_point = ctx
            .process_context()
            .rep_prop_des(source_rep_des)
            .get_dependency_track_point();
        let source_con_desc = ctx.process_context_mut().alloc_con_desc(source_con_desc);

        let link_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
        let link_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(link_dep);
        let mut edge = IndividualLinkEdge::new();
        edge.set_source_individual(process_node)
            .set_destination_individual(succ_node)
            .set_dependency_track_point(link_track_point);
        let edge = ctx.process_context_mut().alloc_edge(edge);

        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;
        algo.propagate_representative_to_successor(
            process_node,
            &mut succ_node,
            &operands,
            false,
            source_con_desc,
            edge,
            &mut ctx,
        );

        let succ_label_set = ctx
            .process_context()
            .node(succ_node)
            .use_reapply_con_label_set;
        assert!(succ_label_set.is_some());
        assert!(ctx
            .process_context()
            .label_set(succ_label_set)
            .contains_concept(operand, false));

        let succ_rep_hash = ctx
            .process_context_mut()
            .node_concept_representative_propagation_set_hash(succ_node);
        let succ_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                succ_rep_hash,
                operand,
                false,
            );
        assert!(succ_rep_set.is_some());
        let outgoing = ctx
            .process_context()
            .rep_prop_set(succ_rep_set)
            .get_outgoing_representative_propagation_descriptor_linker();
        assert!(outgoing.is_some());
        assert_eq!(
            ctx.process_context()
                .rep_prop_des(outgoing)
                .get_representative_variable_binding_path_set_data(),
            source_rep_data
        );
        assert!(ctx
            .process_context()
            .rep_prop_set(succ_rep_set)
            .get_concept_descriptor()
            .is_some());

        let propagated_track_point = ctx
            .process_context()
            .rep_prop_des(outgoing)
            .get_dependency_track_point();
        let propagated_dep = ctx
            .process_context()
            .track_point(propagated_track_point)
            .dependency_node();
        let dep_node = ctx.process_context().dep_node(propagated_dep);
        assert_eq!(dep_node.kind(), DepKind::RepresentativeAll);
        assert_eq!(
            dep_node.previous_dependency_track_point(),
            ctx.process_context()
                .rep_prop_des(source_rep_des)
                .get_dependency_track_point()
        );
        let prev_link = match dep_node {
            DependencyNode::DetLink { prev, .. } => *prev,
            _ => panic!("RepresentativeAll must use the one-back-edge dependency shape"),
        };
        assert_eq!(
            ctx.process_context()
                .dep_link(prev_link)
                .previous_dependency_track_point(),
            link_track_point
        );
        assert_eq!(algo.stat_representative_propagate_succ_count, 1);
    }

    #[test]
    fn apply_representative_all_rule_fans_out_over_role_successors() {
        let mut ctx = test_base_context();
        let mut role = Role::new();
        role.set_role_tag(616);
        let role = ctx.ontology_arenas_mut().alloc_role(role);

        let mut operand = Concept::new();
        operand.set_operator_code(CCATOM);
        let operand = ctx.ontology_arenas_mut().alloc_concept(operand);
        ctx.ontology_arenas_mut()
            .concept_mut(operand)
            .set_concept_tag(operand.raw);

        let mut all_concept = Concept::new();
        all_concept.set_operator_code(CCALL);
        all_concept.set_role(role);
        all_concept.add_operand_linker(operand, false);
        all_concept.set_operand_count(1);
        let all_concept = ctx.ontology_arenas_mut().alloc_concept(all_concept);
        ctx.ontology_arenas_mut()
            .concept_mut(all_concept)
            .set_concept_tag(all_concept.raw);

        let process_node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let succ_node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());

        let con_rep_prop_hash = ctx
            .process_context_mut()
            .node_concept_representative_propagation_set_hash(process_node);
        let source_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                con_rep_prop_hash,
                all_concept,
                true,
            );
        let (source_rep_data, source_rep_des) =
            make_representative_descriptor_with_paths(&mut ctx, 131, &[601]);
        ctx.process_context_mut()
            .rep_prop_set_mut(source_rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(source_rep_des);

        let mut all_con_desc = ConceptDescriptor::new();
        all_con_desc.concept = all_concept;
        all_con_desc.negated = false;
        all_con_desc.dep_track_point = ctx
            .process_context()
            .rep_prop_des(source_rep_des)
            .get_dependency_track_point();
        let all_con_desc = ctx.process_context_mut().alloc_con_desc(all_con_desc);
        let mut con_proc_desc = ConceptProcessDescriptor::new();
        con_proc_desc.concept_des = all_con_desc;
        con_proc_desc.dep_track_point = ctx
            .process_context()
            .rep_prop_des(source_rep_des)
            .get_dependency_track_point();
        let mut con_proc_desc = ctx.process_context_mut().alloc_con_proc_desc(con_proc_desc);

        let link_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
        let link_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(link_dep);
        let mut edge = IndividualLinkEdge::new();
        edge.set_source_individual(process_node)
            .set_destination_individual(succ_node)
            .set_link_role(role)
            .set_dependency_track_point(link_track_point);
        let edge = ctx.process_context_mut().alloc_edge(edge);
        let mut reapply_it = ReapplyQueueIterator::empty();
        ctx.process_context_mut()
            .node_install_individual_link(process_node, edge, &mut reapply_it);

        let mut process_node_ref = process_node;
        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;
        algo.apply_representative_all_rule(
            &mut process_node_ref,
            &mut con_proc_desc,
            false,
            &mut ctx,
        );

        let succ_label_set = ctx
            .process_context()
            .node(succ_node)
            .use_reapply_con_label_set;
        assert!(succ_label_set.is_some());
        assert!(ctx
            .process_context()
            .label_set(succ_label_set)
            .contains_concept(operand, false));

        let succ_rep_hash = ctx
            .process_context_mut()
            .node_concept_representative_propagation_set_hash(succ_node);
        let succ_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                succ_rep_hash,
                operand,
                false,
            );
        let outgoing = ctx
            .process_context()
            .rep_prop_set(succ_rep_set)
            .get_outgoing_representative_propagation_descriptor_linker();
        assert!(outgoing.is_some());
        assert_eq!(
            ctx.process_context()
                .rep_prop_des(outgoing)
                .get_representative_variable_binding_path_set_data(),
            source_rep_data
        );
        assert!(algo.is_concept_in_reapply_queue_role(all_con_desc, role, process_node, &mut ctx));
        assert_eq!(algo.stat_representative_propagate_succ_count, 1);
    }

    #[test]
    fn apply_representative_implication_rule_adds_binding_trigger_and_propagates() {
        let mut ctx = test_base_context();
        let mut binding_trigger = Concept::new();
        binding_trigger.set_operator_code(CCATOM);
        let binding_trigger = ctx.ontology_arenas_mut().alloc_concept(binding_trigger);
        ctx.ontology_arenas_mut()
            .concept_mut(binding_trigger)
            .set_concept_tag(binding_trigger.raw);

        let mut trigger = Concept::new();
        trigger.set_operator_code(CCATOM);
        let trigger = ctx.ontology_arenas_mut().alloc_concept(trigger);
        ctx.ontology_arenas_mut()
            .concept_mut(trigger)
            .set_concept_tag(trigger.raw);

        let mut implication = Concept::new();
        implication.set_operator_code(CCAND);
        implication.add_operand_linker(binding_trigger, false);
        implication.add_operand_linker(trigger, true);
        implication.set_operand_count(2);
        let implication = ctx.ontology_arenas_mut().alloc_concept(implication);
        ctx.ontology_arenas_mut()
            .concept_mut(implication)
            .set_concept_tag(implication.raw);

        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let con_rep_prop_hash = ctx
            .process_context_mut()
            .node_concept_representative_propagation_set_hash(node);
        let source_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                con_rep_prop_hash,
                implication,
                true,
            );
        let (source_rep_data, source_rep_des) =
            make_representative_descriptor_with_paths(&mut ctx, 141, &[701]);
        ctx.process_context_mut()
            .rep_prop_set_mut(source_rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(source_rep_des);

        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;
        let trigger_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let trigger_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(trigger_dep);
        algo.add_concept_to_individual_return_concept_descriptor(
            trigger,
            false,
            &mut node,
            trigger_track_point,
            false,
            false,
            &mut ctx,
        );

        let mut implication_con_desc = ConceptDescriptor::new();
        implication_con_desc.concept = implication;
        implication_con_desc.negated = false;
        implication_con_desc.dep_track_point = ctx
            .process_context()
            .rep_prop_des(source_rep_des)
            .get_dependency_track_point();
        let implication_con_desc = ctx
            .process_context_mut()
            .alloc_con_desc(implication_con_desc);
        let mut con_proc_desc = ConceptProcessDescriptor::new();
        con_proc_desc.concept_des = implication_con_desc;
        con_proc_desc.dep_track_point = ctx
            .process_context()
            .rep_prop_des(source_rep_des)
            .get_dependency_track_point();
        let mut con_proc_desc = ctx.process_context_mut().alloc_con_proc_desc(con_proc_desc);

        algo.apply_representative_implication_rule(&mut node, &mut con_proc_desc, false, &mut ctx);

        let label_set = ctx.process_context().node(node).use_reapply_con_label_set;
        assert!(label_set.is_some());
        assert!(ctx
            .process_context()
            .label_set(label_set)
            .contains_concept(binding_trigger, false));

        let rep_set = ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
            ctx.process_context_mut(),
            con_rep_prop_hash,
            binding_trigger,
            false,
        );
        assert!(rep_set.is_some());
        let outgoing = ctx
            .process_context()
            .rep_prop_set(rep_set)
            .get_outgoing_representative_propagation_descriptor_linker();
        assert!(outgoing.is_some());
        assert_eq!(
            ctx.process_context()
                .rep_prop_des(outgoing)
                .get_representative_variable_binding_path_set_data(),
            source_rep_data
        );

        let dep_track_point = ctx
            .process_context()
            .rep_prop_des(outgoing)
            .get_dependency_track_point();
        let dep_node = ctx
            .process_context()
            .track_point(dep_track_point)
            .dependency_node();
        let dep = ctx.process_context().dep_node(dep_node);
        assert_eq!(dep.kind(), DepKind::RepresentativeImplication);
        let trigger_link = dep.additional_after_dependencies();
        assert!(trigger_link.is_some());
        let conn_track_point = ctx
            .process_context()
            .dep_link(trigger_link)
            .previous_dependency_track_point();
        let conn_dep = ctx
            .process_context()
            .track_point(conn_track_point)
            .dependency_node();
        assert_eq!(
            ctx.process_context().dep_node(conn_dep).kind(),
            DepKind::Connection
        );
        assert_eq!(algo.stat_representative_implication_count, 1);
    }

    #[test]
    fn apply_representative_join_rule_creates_joined_representative() {
        let mut ctx = test_base_context();
        let join_variable = ctx.ontology_arenas_mut().alloc_variable(Variable::new());
        let side_variable = ctx.ontology_arenas_mut().alloc_variable(Variable::new());

        let mut join_concept = Concept::new();
        join_concept.set_operator_code(CCATOM);
        join_concept.set_variable_linker(vec![join_variable]);
        let join_concept = ctx.ontology_arenas_mut().alloc_concept(join_concept);
        ctx.ontology_arenas_mut()
            .concept_mut(join_concept)
            .set_concept_tag(join_concept.raw);

        let mut left_trigger = Concept::new();
        left_trigger.set_operator_code(CCATOM);
        let left_trigger = ctx.ontology_arenas_mut().alloc_concept(left_trigger);
        ctx.ontology_arenas_mut()
            .concept_mut(left_trigger)
            .set_concept_tag(left_trigger.raw);

        let mut right_trigger = Concept::new();
        right_trigger.set_operator_code(CCATOM);
        let right_trigger = ctx.ontology_arenas_mut().alloc_concept(right_trigger);
        ctx.ontology_arenas_mut()
            .concept_mut(right_trigger)
            .set_concept_tag(right_trigger.raw);

        let mut join_rule = Concept::new();
        join_rule.set_operator_code(CCVARBINDJOIN);
        join_rule.set_variable_linker(vec![join_variable]);
        join_rule.add_operand_linker(join_concept, false);
        join_rule.add_operand_linker(left_trigger, true);
        join_rule.add_operand_linker(right_trigger, true);
        join_rule.set_operand_count(3);
        let join_rule = ctx.ontology_arenas_mut().alloc_concept(join_rule);
        ctx.ontology_arenas_mut()
            .concept_mut(join_rule)
            .set_concept_tag(join_rule.raw);

        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let join_binding =
            make_var_binding(ctx.process_context_mut(), join_variable, NodeId::new(501));
        let side_binding =
            make_var_binding(ctx.process_context_mut(), side_variable, NodeId::new(502));
        let left_path =
            make_var_binding_path(ctx.process_context_mut(), 71, &[join_binding, side_binding]);
        let right_path = make_var_binding_path(ctx.process_context_mut(), 72, &[join_binding]);
        let (_left_rep_data, left_rep_des) =
            make_representative_descriptor_with_var_path(&mut ctx, 211, 71, left_path);
        let (_right_rep_data, right_rep_des) =
            make_representative_descriptor_with_var_path(&mut ctx, 223, 72, right_path);

        let rep_hash = ctx
            .process_context_mut()
            .node_concept_representative_propagation_set_hash(node);
        let left_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                rep_hash,
                left_trigger,
                true,
            );
        ctx.process_context_mut()
            .rep_prop_set_mut(left_rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(left_rep_des);
        let right_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                rep_hash,
                right_trigger,
                true,
            );
        ctx.process_context_mut()
            .rep_prop_set_mut(right_rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(right_rep_des);

        let prop_hash = ctx
            .process_context_mut()
            .node_concept_propagation_binding_set_hash(node);
        let prop_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
            ctx.process_context_mut(),
            prop_hash,
            join_rule.raw,
            true,
        );
        ctx.process_context_mut()
            .prop_binding_set_mut(prop_set)
            .set_propagate_all_flag(true);

        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;
        let premise_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
        let premise_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(premise_dep);
        algo.add_concept_to_individual_return_concept_descriptor(
            left_trigger,
            false,
            &mut node,
            premise_track_point,
            false,
            false,
            &mut ctx,
        );
        algo.add_concept_to_individual_return_concept_descriptor(
            right_trigger,
            false,
            &mut node,
            premise_track_point,
            false,
            false,
            &mut ctx,
        );

        let mut join_rule_con_desc = ConceptDescriptor::new();
        join_rule_con_desc.concept = join_rule;
        join_rule_con_desc.negated = false;
        join_rule_con_desc.dep_track_point = premise_track_point;
        let join_rule_con_desc = ctx.process_context_mut().alloc_con_desc(join_rule_con_desc);
        let mut con_proc_desc = ConceptProcessDescriptor::new();
        con_proc_desc.concept_des = join_rule_con_desc;
        con_proc_desc.dep_track_point = premise_track_point;
        let mut con_proc_desc = ctx.process_context_mut().alloc_con_proc_desc(con_proc_desc);

        algo.apply_representative_join_rule(&mut node, &mut con_proc_desc, false, &mut ctx);

        let label_set = ctx.process_context().node(node).use_reapply_con_label_set;
        assert!(label_set.is_some());
        assert!(ctx
            .process_context()
            .label_set(label_set)
            .contains_concept(join_concept, false));

        let join_rep_set =
            ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
                ctx.process_context_mut(),
                rep_hash,
                join_concept,
                false,
            );
        assert!(join_rep_set.is_some());
        let incoming = ctx
            .process_context()
            .rep_prop_set(join_rep_set)
            .get_incoming_representative_propagation_descriptor_linker();
        assert!(incoming.is_some());
        let joined_rep_data = ctx
            .process_context()
            .rep_prop_des(incoming)
            .get_representative_variable_binding_path_set_data();
        let joined_migrate = RepresentativeVariableBindingPathSetData::get_migrate_data(
            ctx.process_context_mut(),
            joined_rep_data,
            false,
        );
        assert_eq!(
            ctx.process_context()
                .rep_var_bind_path_set_migrate_data(joined_migrate)
                .get_representative_variable_binding_path_map()
                .count(),
            1
        );
        let join_dep_track_point = ctx
            .process_context()
            .rep_prop_des(incoming)
            .get_dependency_track_point();
        let join_dep = ctx
            .process_context()
            .track_point(join_dep_track_point)
            .dependency_node();
        assert_eq!(
            ctx.process_context().dep_node(join_dep).kind(),
            DepKind::RepresentativeJoin
        );

        let trans_ext = ctx
            .process_context()
            .prop_binding_set(prop_set)
            .prop_rep_trans_extension;
        assert!(trans_ext.is_some());
        let trans_ext = ctx.process_context().prop_rep_trans_ext(trans_ext);
        assert_eq!(
            trans_ext.get_left_last_representative_joining_descriptor(),
            left_rep_des
        );
        assert_eq!(
            trans_ext.get_right_last_representative_joining_descriptor(),
            right_rep_des
        );
        assert!(trans_ext.get_last_analysed_propagate_all_flag());
        assert_eq!(algo.stat_representative_join_count, 1);
        assert_eq!(algo.stat_representative_joined_count, 1);
    }

    #[test]
    fn apply_representative_bind_variable_rule_creates_representative_path() {
        let mut ctx = test_base_context();
        let variable = ctx.ontology_arenas_mut().alloc_variable(Variable::new());

        let mut binding_trigger = Concept::new();
        binding_trigger.set_operator_code(CCATOM);
        let binding_trigger = ctx.ontology_arenas_mut().alloc_concept(binding_trigger);
        ctx.ontology_arenas_mut()
            .concept_mut(binding_trigger)
            .set_concept_tag(binding_trigger.raw);

        let mut rep_bind = Concept::new();
        rep_bind.set_operator_code(CCVARBINDVARIABLE);
        rep_bind.set_variable_linker(vec![variable]);
        rep_bind.add_operand_linker(binding_trigger, false);
        rep_bind.set_operand_count(1);
        let rep_bind = ctx.ontology_arenas_mut().alloc_concept(rep_bind);
        ctx.ontology_arenas_mut()
            .concept_mut(rep_bind)
            .set_concept_tag(rep_bind.raw);

        let mut node = ctx
            .process_context_mut()
            .alloc_node(IndividualProcessNode::default());
        let prop_hash = ctx
            .process_context_mut()
            .node_concept_propagation_binding_set_hash(node);
        let rep_bind_tag = ctx.ontology_arenas().concept(rep_bind).get_concept_tag();
        let source_prop_set = ConceptPropagationBindingSetHash::get_propagation_binding_set(
            ctx.process_context_mut(),
            prop_hash,
            rep_bind_tag,
            true,
        );
        ctx.process_context_mut()
            .prop_binding_set_mut(source_prop_set)
            .set_propagate_all_flag(true);

        let premise_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeGrounding);
        let premise_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(premise_dep);
        let mut rep_bind_con_desc = ConceptDescriptor::new();
        rep_bind_con_desc.concept = rep_bind;
        rep_bind_con_desc.negated = false;
        rep_bind_con_desc.dep_track_point = premise_track_point;
        let rep_bind_con_desc = ctx.process_context_mut().alloc_con_desc(rep_bind_con_desc);
        let mut con_proc_desc = ConceptProcessDescriptor::new();
        con_proc_desc.concept_des = rep_bind_con_desc;
        con_proc_desc.dep_track_point = premise_track_point;
        let mut con_proc_desc = ctx.process_context_mut().alloc_con_proc_desc(con_proc_desc);

        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;
        algo.apply_representative_bind_variable_rule(
            &mut node,
            &mut con_proc_desc,
            false,
            &mut ctx,
        );

        let label_set = ctx.process_context().node(node).use_reapply_con_label_set;
        assert!(label_set.is_some());
        assert!(ctx
            .process_context()
            .label_set(label_set)
            .contains_concept(binding_trigger, false));

        let rep_hash = ctx
            .process_context_mut()
            .node_concept_representative_propagation_set_hash(node);
        let rep_set = ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
            ctx.process_context_mut(),
            rep_hash,
            binding_trigger,
            true,
        );
        assert!(rep_set.is_some());
        let outgoing = ctx
            .process_context()
            .rep_prop_set(rep_set)
            .get_outgoing_representative_propagation_descriptor_linker();
        assert!(outgoing.is_some());
        let rep_data = ctx
            .process_context()
            .rep_prop_des(outgoing)
            .get_representative_variable_binding_path_set_data();
        let rep_data_ref = ctx.process_context().rep_var_bind_path_set_data(rep_data);
        assert_eq!(rep_data_ref.get_use_count(), 1);
        assert_eq!(rep_data_ref.get_share_count(), 2);
        assert!(!rep_data_ref.is_migratable());

        let migrate = RepresentativeVariableBindingPathSetData::get_migrate_data(
            ctx.process_context_mut(),
            rep_data,
            false,
        );
        let rep_map = ctx
            .process_context()
            .rep_var_bind_path_set_migrate_data(migrate)
            .get_representative_variable_binding_path_map();
        assert_eq!(rep_map.count(), 1);
        let (path_prop_id, map_data) = rep_map.map.iter().next().unwrap();
        assert_eq!(*path_prop_id, 0);
        assert_eq!(
            map_data.get_resolve_representative_variable_binding_path_set_data(),
            rep_data
        );
        let var_binding_path = map_data.get_variable_binding_path();
        let var_binding_des = ctx
            .process_context()
            .vbpath(var_binding_path)
            .get_variable_binding_descriptor_linker();
        let var_binding = ctx
            .process_context()
            .var_binding_des(var_binding_des)
            .get_variable_binding();
        assert_eq!(
            ctx.process_context()
                .var_binding(var_binding)
                .get_binded_variable(),
            variable
        );
        assert_eq!(
            ctx.process_context()
                .var_binding(var_binding)
                .get_binded_individual(),
            node
        );

        let dep_track_point = ctx
            .process_context()
            .rep_prop_des(outgoing)
            .get_dependency_track_point();
        let dep_node = ctx
            .process_context()
            .track_point(dep_track_point)
            .dependency_node();
        assert_eq!(
            ctx.process_context().dep_node(dep_node).kind(),
            DepKind::RepresentativeBindVariable
        );
        assert_eq!(algo.stat_representative_created_count, 1);
        let trans_ext = ctx
            .process_context()
            .prop_binding_set(source_prop_set)
            .prop_var_bind_trans_extension;
        assert!(trans_ext.is_some());
        assert!(ctx
            .process_context()
            .prop_var_bind_trans_ext(trans_ext)
            .is_processing_completed());
    }

    #[test]
    fn apply_representative_grounding_rule_adds_grounded_concept_from_representative_map() {
        let mut ctx = test_base_context();
        let mut nom_var_concept = Concept::new();
        nom_var_concept.set_operator_code(CCNOMVAR);
        let nom_var_concept = ctx.ontology_arenas_mut().alloc_concept(nom_var_concept);
        let mut nominal = Concept::new();
        nominal.set_operator_code(CCNOMINAL);
        let nominal = ctx.ontology_arenas_mut().alloc_concept(nominal);
        ctx.ontology_arenas_mut()
            .concept_mut(nominal)
            .set_concept_tag(nominal.raw);

        let mut trigger_concept = Concept::new();
        trigger_concept.set_concept_tag(902);
        let trigger_concept = ctx.ontology_arenas_mut().alloc_concept(trigger_concept);

        let mut variable = Variable::new();
        variable.init_variable(nom_var_concept, 0);
        let variable = ctx.ontology_arenas_mut().alloc_variable(variable);

        let mut individual = Individual::new(0);
        individual.add_assertion_concept_linker(NegLink {
            target: nominal,
            negated: false,
        });
        let individual = ctx.ontology_arenas_mut().alloc_individual(individual);

        let mut node = IndividualProcessNode::default();
        node.set_individual_node_id(0);
        node.set_nominal_individual(individual);
        let mut node = ctx.process_context_mut().alloc_node(node);

        let mut binding = VariableBinding::new();
        binding.init_variable_binding(TrackPointId::NONE, node, variable);
        let binding = ctx.process_context_mut().alloc_var_binding(binding);
        let mut binding_des = VariableBindingDescriptor::new();
        binding_des.init_variable_binding_descriptor(binding);
        let binding_des = ctx.process_context_mut().alloc_var_binding_des(binding_des);
        let mut path = VariableBindingPath::new();
        path.init_variable_binding_path(188, binding_des);
        let path = ctx.process_context_mut().alloc_vbpath(path);

        let grounding_hash = ctx
            .process_context_mut()
            .alloc_grounding_hash(ConceptNominalSchemaGroundingHash::new(0));
        ctx.processing_data_box_mut().use_grounding_hash = grounding_hash;

        let rep_data = ctx
            .process_context_mut()
            .alloc_rep_var_bind_path_set_data(RepresentativeVariableBindingPathSetData::new(0, 0));
        ctx.process_context_mut()
            .rep_var_bind_path_set_data_mut(rep_data)
            .set_representative_id(77);
        let rep_migrate = ctx
            .process_context_mut()
            .alloc_rep_var_bind_path_set_migrate_data(
                RepresentativeVariableBindingPathSetMigrateData::new(0),
            );
        ctx.process_context_mut()
            .rep_var_bind_path_set_data_mut(rep_data)
            .use_migrate_data = rep_migrate;
        ctx.process_context_mut()
            .rep_var_bind_path_set_migrate_data_mut(rep_migrate)
            .get_representative_variable_binding_path_map_mut()
            .insert(
                188,
                RepresentativeVariableBindingPathMapData::new(path, rep_data),
            );

        let prev_dep = ctx
            .process_context_mut()
            .alloc_deterministic_dependency_node(DepKind::RepresentativeAnd);
        let prev_track_point = ctx
            .process_context_mut()
            .materialize_continue_dependency_track_point(prev_dep);
        let rep_des = ctx
            .process_context_mut()
            .alloc_rep_prop_des(RepresentativePropagationDescriptor::new());
        ctx.process_context_mut()
            .rep_prop_des_mut(rep_des)
            .init_representative_descriptor(rep_data, prev_track_point);
        let rep_hash = ctx
            .process_context_mut()
            .node_concept_representative_propagation_set_hash(node);
        let rep_set = ConceptRepresentativePropagationSetHash::get_representative_propagation_set(
            ctx.process_context_mut(),
            rep_hash,
            trigger_concept,
            true,
        );
        ctx.process_context_mut()
            .rep_prop_set_mut(rep_set)
            .set_outgoing_representative_propagation_descriptor_linker(rep_des);

        let mut templ = super::super::super::model::ontology::NominalSchemaTemplate::new();
        templ.set_template_concept(nom_var_concept);
        let mut template_set = std::collections::HashSet::new();
        template_set.insert(nom_var_concept);
        templ.set_nominal_schema_concept_set(template_set);
        let mut template_hash = HashMap::new();
        template_hash.insert(nom_var_concept, vec![nom_var_concept]);
        templ.set_template_concept_nominal_schema_concept_hash(template_hash);
        let templ = ctx
            .ontology_arenas_mut()
            .alloc_nominal_schema_template(templ);
        ctx.ontology_arenas_mut()
            .concept_mut(trigger_concept)
            .set_parameter(templ.raw);

        let mut con_desc = ConceptDescriptor::new();
        con_desc.concept = trigger_concept;
        con_desc.negated = false;
        con_desc.dep_track_point = TrackPointId::NONE;
        let con_desc = ctx.process_context_mut().alloc_con_desc(con_desc);
        let mut con_proc_desc = ConceptProcessDescriptor::new();
        con_proc_desc.concept_des = con_desc;
        let mut con_proc_desc = ctx.process_context_mut().alloc_con_proc_desc(con_proc_desc);

        let mut algo = CompletionTaskHandleAlgorithm::new();
        algo.conf_build_dependencies = true;
        algo.apply_representative_grounding_rule(&mut node, &mut con_proc_desc, false, &mut ctx);

        assert_eq!(algo.stat_representative_grounding_count, 1);
        let label_set = ctx.process_context().node(node).use_reapply_con_label_set;
        assert!(label_set.is_some());
        assert!(ctx
            .process_context()
            .label_set(label_set)
            .contains_concept(nominal, false));
        let mut added_con_des = ConDescId::NONE;
        let mut added_dep_track_point = TrackPointId::NONE;
        assert!(ctx
            .process_context()
            .label_set(label_set)
            .get_concept_descriptor(nominal, &mut added_con_des, &mut added_dep_track_point,));
        added_dep_track_point = ctx
            .process_context()
            .con_desc(added_con_des)
            .get_dependency_track_point();
        assert!(added_dep_track_point.is_some());
        let dep_node = ctx
            .process_context()
            .track_point(added_dep_track_point)
            .dependency_node();
        let dep = ctx.process_context().dep_node(dep_node);
        assert_eq!(dep.kind(), DepKind::RepresentativeGrounding);
        assert_eq!(dep.previous_dependency_track_point(), prev_track_point);
        assert_eq!(dep.selected_variable_binding_path(), path);
    }
}
