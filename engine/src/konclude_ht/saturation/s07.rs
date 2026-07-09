//! `saturation::s07` — Extension processing queue + dependent-individual fan-out
//! (saturation port unit #7 of 12; manifest `03-saturation-calc.md`, "PU-SAT-7").
//!
//! Faithful port of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`,
//! the **group F part 2** methods: the successor-extension processing-queue driver
//! (`processNextSuccessorExtensions` + the per-node ALL / FUNCTIONAL extension
//! processors), the dependent-individual fan-out helpers (`add*ToDependentIndividuals`),
//! the linked-successor collectors (`collectLinkedSuccessorNodes` +
//! `addLinkedSuccessorNodeFor{Concept,RoleAssertion}`), and the per-role
//! concept-extension-processing registrars (`add*ConceptExtensionProcessingRole`,
//! `addNewLinkedExtensionProcessingRole`). Group F part 1 (the `update*ALL/FUNCTIONAL*`
//! propagation routines + `installBackwardPropagationLink`) is the sibling unit
//! `saturation/s06.rs`; the group-G ATMOST cardinality merging is PU-SAT-8.
//!
//! Methods (cpp order; the `CIndividualSaturationProcessNode*&` self-node and the
//! trailing `CCalculationAlgorithmContextBase*` elided in this list):
//!   * `addSuccessorExtensionsALLConcept`                                            [2531–2552]
//!   * `processSuccessorFUNCTIONALConceptsExtensions`                                [2557–2641]
//!   * `processNextSuccessorExtensions`                                              [2646–2665]
//!   * `processSuccessorALLConceptsExtensions`                                       [2670–2713]
//!   * `addSuccessorExtensionToProcessingQueue`                                      [2717–2726]
//!   * `addProcessExtensionToDependentIndividuals`                                   [2729–2736]
//!   * `addALLProcessRoleExtensionToDependentIndividuals`                            [2738–2754]
//!   * `addFUNCTIONALProcessRoleExtensionLinkedSuccessorAddedToDependentIndividuals` [2757–2773]
//!   * `addFUNCTIONALQualifiedProcessAtmostConceptExtensionToDependentIndividuals`   [2778–2785]
//!   * `addFUNCTIONALProcessRoleExtensionLinkedPredecessorAddedToDependentIndividuals`[2790–2806]
//!   * `addFUNCTIONALProcessRoleExtensionFunctionalityAddedToDependentIndividuals`   [2808–2822]
//!   * `collectLinkedSuccessorNodes`                                                 [3194–3227]
//!   * `addLinkedSuccessorNodeForRoleAssertion`                                      [3234–3243]
//!   * `addLinkedSuccessorNodeForConcept`                                            [3250–3383]
//!   * `addALLConceptExtensionProcessingRole`                                        [6209–6233]
//!   * `addFUNCTIONALConceptExtensionProcessingRole`                                 [6238–6250]
//!   * `addQualifiedFUNCTIONALAtmostConceptExtensionProcessing`                      [6255–6267]
//!   * `addNewLinkedExtensionProcessingRole`                                         [6271–6357]
//!
//! CONTEXT CONVENTION (confirmed across s01–s06). Each method is a member of
//! `CCalculationTableauApproximationSaturationTaskHandleAlgorithm`, so it becomes
//! `&mut self`. The saturation `.h` declares every method with the SHARED
//! `CCalculationAlgorithmContextBase* calcAlgContext`, so per `PORT.md` the port
//! threads `calc_alg_context: &mut CalculationAlgorithmContextBase` — the same
//! context type the completion layer uses. The C++ member back-handle
//! `mProcessingDataBox`/`mCalcAlgContext` alias the same objects; the port routes
//! ALL access through the threaded `calc_alg_context`. A `CIndividualSaturationProcessNode*&`
//! out/in-out reference becomes `&mut SatNodeId`; a plain `CIndividualSaturationProcessNode*`
//! value becomes `SatNodeId`; `CRole*` becomes `RoleId`; `CConcept*` becomes
//! `ConceptId`; `CConceptSaturationDescriptor*` becomes `ConceptSaturationDescriptorId`
//! (a `process::stubs` marker id).
//!
//! Deferral landscape. Like the sibling s06, this whole unit sits on top of the
//! **successor-extension satellite tower** — a Process-layer subsystem with no Rust
//! struct in the tree yet (only marker references in `process::stubs` + the
//! manifests). Every body immediately dereferences one or more of:
//!   * `CSaturationIndividualNodeSuccessorExtensionData`
//!     (`sat_node->getSuccessorExtensionData`) and its `...ALLConceptsExtensionData`
//!     / `...FUNCTIONALConceptsExtensionData` faces;
//!   * `CSaturationSuccessorALLConceptExtensionData` and its extension-process worklist;
//!   * `CSaturationSuccessorExtensionIndividualNodeProcessingQueue` (the databox
//!     extension-processing queue; the top-level driver is live);
//!   * `CLinkedRoleSaturationSuccessorHash` / `CLinkedRoleSaturationSuccessorData`
//!     (per-role linked-successor chains + `addLinkedSuccessor` / `addLinkedVALUESuccessor`);
//!   * `CRoleBackwardSaturationPropagationHash` / `CRoleBackwardSaturationPropagationHashData`;
//!   * `CReapplyConceptSaturationLabelSet` / `CConceptSaturationDescriptor` /
//!     `CSaturationSuccessorRoleAssertionLinker` / `CXNegLinker<CIndividualSaturationProcessNode*>`
//!     (`getCopyDependingIndividualNodeLinker`);
//!   * `CConceptSaturationReferenceLinkingData` / `CSaturationConceptReferenceLinking`
//!     (the concept→saturation-individual-node reference linking).
//! and on the saturation **pool helpers** (PU-SAT-11): `create/releaseRoleSaturationProcessLinker`,
//! `create/releaseConceptSaturationProcessLinker`. Sibling methods owned by OTHER
//! saturation units (`installSuccessorPredecessorRoleFunctionalityConceptsExtension`,
//! `updateSuccessorRole(Qualified)FUNCTIONALConceptsExtensions`,
//! `updatePredecessorRoleFUNCTIONALConceptsExtensions`,
//! `updateSuccessorRoleALLConceptsExtensions`, `updateSuccessorALLConceptsExtensions`
//! from PU-SAT-6) are called as `self.x(...)`.
//!
//! Following the porting convention (PORT.md W3 keystone precedent, mirrored by
//! `saturation::s06`): each method below carries the faithful name + signature +
//! context threading, and a `// W4-DEFER[api]` body that transcribes the C++
//! control flow structurally so a later wave fills it without re-reading the
//! source. The unported satellite types appear as opaque `Cint64` (`INVALID` ==
//! the C++ `nullptr`). Logic is documented, never silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::op::{
    ConceptOperator, CCALL, CCAQSOME, CCATLEAST, CCATMOST, CCFS_ALL_AQALL_TYPE, CCFS_SOME_TYPE,
    CCSOME, CCVALUE,
};
use super::super::model::substrate::{Cint64, Id};
use super::super::model::{
    ConceptId, ConceptProcessDataId, RoleId, SaturationConceptReferenceLinkingId,
};
use super::super::process::stubs::{ConceptSaturationDescriptorId, RoleSaturationProcess};
use super::super::process::SatNodeId;
use super::satellites::{
    ConceptSaturationProcessLinker, LinkedRoleSaturationSuccessorHashId,
    RoleSaturationProcessLinker, SaturationSuccessorAllConceptExtensionDataId,
};

impl super::algorithm::SaturationTaskHandleAlgorithm {
    pub(in crate::konclude_ht) fn s07_concept_reference_node(
        concept: ConceptId,
        concept_negation: bool,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        if concept.is_none()
            || concept.index() >= calc_alg_context.ontology_arenas().concept_count() as usize
        {
            return SatNodeId::NONE;
        }
        let concept = calc_alg_context.ontology_arenas().concept(concept);
        if !concept.has_concept_data() {
            return SatNodeId::NONE;
        }
        let con_proc_data_id = ConceptProcessDataId::new(concept.get_concept_data());
        if con_proc_data_id.is_none()
            || con_proc_data_id.index()
                >= calc_alg_context
                    .ontology_arenas()
                    .concept_process_datas()
                    .len()
        {
            return SatNodeId::NONE;
        }
        let con_ref_linking_id = calc_alg_context
            .ontology_arenas()
            .concept_process_data(con_proc_data_id)
            .get_concept_reference_linking();
        if con_ref_linking_id.is_none()
            || con_ref_linking_id.index()
                >= calc_alg_context
                    .ontology_arenas()
                    .concept_saturation_reference_linking_datas()
                    .len()
        {
            return SatNodeId::NONE;
        }
        let sat_calc_ref_link_data_id = calc_alg_context
            .ontology_arenas()
            .concept_saturation_reference_linking_data(con_ref_linking_id)
            .get_concept_saturation_reference_linking_data(concept_negation);
        Self::s07_reference_linking_node(sat_calc_ref_link_data_id, calc_alg_context)
    }

    pub(in crate::konclude_ht) fn s07_existential_successor_reference_node(
        concept: ConceptId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        if concept.is_none()
            || concept.index() >= calc_alg_context.ontology_arenas().concept_count() as usize
        {
            return SatNodeId::NONE;
        }
        let concept = calc_alg_context.ontology_arenas().concept(concept);
        if !concept.has_concept_data() {
            return SatNodeId::NONE;
        }
        let con_proc_data_id = ConceptProcessDataId::new(concept.get_concept_data());
        if con_proc_data_id.is_none()
            || con_proc_data_id.index()
                >= calc_alg_context
                    .ontology_arenas()
                    .concept_process_datas()
                    .len()
        {
            return SatNodeId::NONE;
        }
        let con_ref_linking_id = calc_alg_context
            .ontology_arenas()
            .concept_process_data(con_proc_data_id)
            .get_concept_reference_linking();
        if con_ref_linking_id.is_none()
            || con_ref_linking_id.index()
                >= calc_alg_context
                    .ontology_arenas()
                    .concept_saturation_reference_linking_datas()
                    .len()
        {
            return SatNodeId::NONE;
        }
        let sat_calc_ref_link_data_id = calc_alg_context
            .ontology_arenas()
            .concept_saturation_reference_linking_data(con_ref_linking_id)
            .get_existential_successor_concept_saturation_reference_linking_data();
        Self::s07_reference_linking_node(sat_calc_ref_link_data_id, calc_alg_context)
    }

    fn s07_reference_linking_node(
        ref_linking: SaturationConceptReferenceLinkingId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        if ref_linking.is_none()
            || ref_linking.index()
                >= calc_alg_context
                    .ontology_arenas()
                    .saturation_concept_reference_linkings()
                    .len()
        {
            return SatNodeId::NONE;
        }
        let node = calc_alg_context
            .ontology_arenas()
            .saturation_concept_reference_linking(ref_linking)
            .get_individual_process_node_for_concept();
        if node.is_none() || node.index() >= calc_alg_context.process_context().sat_node_count() {
            SatNodeId::NONE
        } else {
            node
        }
    }

    fn s07_add_linked_successors_for_resolved_node(
        linked_role_succ_hash: LinkedRoleSaturationSuccessorHashId,
        role: RoleId,
        creation_role: RoleId,
        successor_node: SatNodeId,
        successor_count: Cint64,
        nominal_successor: bool,
        nominal_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if role.is_none()
            || role.index() >= calc_alg_context.ontology_arenas().role_count() as usize
        {
            return;
        }
        // KONCLUDE-PORT-NOTE[identity]: Konclude's indirect super-role lists START
        // with the role itself; the bridge builds strict lists. Without the identity
        // entry the successor is never registered under its own creation role and
        // `isCriticalALLConceptDescriptorInsufficient` sees an empty successor hash —
        // ∃r.B ⊓ ∀r.¬B then completes SAT-certain (unsound, caught by
        // `saturation_never_sat_certain_on_forall_exists_clash`).
        let super_roles = Self::saturation_indirect_super_roles(role, calc_alg_context);
        for super_role_it in super_roles {
            if !super_role_it.negated {
                if nominal_successor {
                    calc_alg_context
                        .process_context_mut()
                        .linked_role_successor_hash_add_linked_value_successor(
                            linked_role_succ_hash,
                            super_role_it.target,
                            nominal_id,
                            creation_role,
                        );
                } else {
                    calc_alg_context
                        .process_context_mut()
                        .linked_role_successor_hash_add_linked_successor(
                            linked_role_succ_hash,
                            super_role_it.target,
                            successor_node,
                            creation_role,
                            successor_count,
                        );
                }
            }
        }
    }

    fn s07_role_process_linker_chain_has_role(
        mut linker: super::satellites::RoleSaturationProcessLinkerId,
        role: RoleId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        while linker.is_some() {
            let linker_ref = calc_alg_context
                .process_context()
                .role_sat_proc_linker(linker);
            if linker_ref.get_role() == role {
                return true;
            }
            linker = linker_ref.get_next();
        }
        false
    }

    fn s07_create_role_process_linker(
        role: RoleId,
        old_head: super::satellites::RoleSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> super::satellites::RoleSaturationProcessLinkerId {
        let mut role_process_linker = RoleSaturationProcessLinker::new();
        role_process_linker
            .init_role_process_linker(role)
            .set_next(old_head);
        calc_alg_context
            .process_context_mut()
            .alloc_role_sat_proc_linker(role_process_linker)
    }

    fn s07_concept_process_linker_chain_has_descriptor(
        mut linker: super::satellites::ConceptSaturationProcessLinkerId,
        con_des: ConceptSaturationDescriptorId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        while linker.is_some() {
            let linker_ref = calc_alg_context
                .process_context()
                .con_sat_proc_linker(linker);
            if linker_ref.get_concept_saturation_descriptor() == con_des {
                return true;
            }
            linker = linker_ref.get_next();
        }
        false
    }

    fn s07_create_concept_process_linker(
        con_des: ConceptSaturationDescriptorId,
        old_head: super::satellites::ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> super::satellites::ConceptSaturationProcessLinkerId {
        let mut concept_process_linker = ConceptSaturationProcessLinker::new();
        concept_process_linker
            .init_concept_saturation_process_linker(con_des)
            .set_next(old_head);
        calc_alg_context
            .process_context_mut()
            .alloc_con_sat_proc_linker(concept_process_linker)
    }

    // =======================================================================
    // Extension processing-queue driver + per-node ALL/FUNCTIONAL processors
    // (cpp 2531–2726).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addSuccessorExtensionsALLConcept`.
    /// cpp 2531–2552.
    ///
    /// For a `∀`-type (or, when negated, a `∃`-type) concept, adds its operand
    /// concepts — negated for the `∃`/negated-`∀` case — into the per-(successor)
    /// ALL-concept successor-extension data. Returns whether a new operand concept
    /// was added.
    pub fn add_successor_extensions_all_concept(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        concept: ConceptId,
        concept_negation: bool,
        all_con_succ_ext_data: SaturationSuccessorAllConceptExtensionDataId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut new_concept_added = false;
        if concept.is_none()
            || concept.index() >= calc_alg_context.ontology_arenas().concept_count() as usize
            || all_con_succ_ext_data.is_none()
        {
            return false;
        }

        let mut add_operand_concepts = false;
        let mut use_negated_operand_concepts = false;
        let con_op_code = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        let con_op = ConceptOperator::new(con_op_code);
        if !concept_negation && con_op.has_partial_operator_code_flag(CCFS_ALL_AQALL_TYPE) {
            add_operand_concepts = true;
            use_negated_operand_concepts = false;
        }
        if concept_negation && con_op.has_partial_operator_code_flag(CCFS_SOME_TYPE) {
            add_operand_concepts = true;
            use_negated_operand_concepts = true;
        }
        if add_operand_concepts {
            let operands = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            for op_linker_it in operands {
                let op_concept = op_linker_it.target;
                let op_concept_negation = op_linker_it.negated ^ use_negated_operand_concepts;
                if op_concept.is_some()
                    && op_concept.index()
                        < calc_alg_context.ontology_arenas().concept_count() as usize
                {
                    let concept_tag = calc_alg_context
                        .ontology_arenas()
                        .concept(op_concept)
                        .get_concept_tag();
                    let map = calc_alg_context
                        .process_context()
                        .sat_successor_all_concept_ext_data(all_con_succ_ext_data)
                        .get_successor_concept_extension_map();
                    let modified = calc_alg_context
                        .process_context_mut()
                        .sat_successor_concept_extension_map_mut(map)
                        .add_extension_concept(op_concept, op_concept_negation, concept_tag);
                    if modified {
                        calc_alg_context
                            .process_context_mut()
                            .sat_successor_all_concept_ext_data_mut(all_con_succ_ext_data)
                            .concepts_updated_flag = true;
                    }
                    new_concept_added |= calc_alg_context
                        .process_context()
                        .sat_successor_all_concept_ext_data(all_con_succ_ext_data)
                        .concepts_updated_flag;
                }
            }
        }
        let _ = indi_proc_sat_node;
        new_concept_added
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::processSuccessorFUNCTIONALConceptsExtensions`.
    /// cpp 2557–2641.
    ///
    /// Processes the node's FUNCTIONAL-concepts successor-extension worklists:
    /// (re)collects the linked successors, installs successor/predecessor role
    /// functionality extensions for each newly functionality-added role (fanning the
    /// functionality-added flag out to dependent individuals and registering the
    /// predecessor + copy-initialising role linkers), then drains the linked-
    /// successor-added, linked-predecessor-added and qualified-functional-atmost
    /// worklists by delegating to the matching PU-SAT-6 update workers. Clears the
    /// extension-processing-queued flag. Returns whether anything updated.
    pub fn process_successor_functional_concepts_extensions(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated = false;
        if indi_proc_sat_node.is_none()
            || indi_proc_sat_node.index() >= calc_alg_context.process_context().sat_node_count()
        {
            return false;
        }
        let succ_extension_data = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(*indi_proc_sat_node, false);
        if succ_extension_data.is_none() {
            return false;
        }
        let functional_concepts_extension = calc_alg_context
            .process_context_mut()
            .sat_successor_extension_functional_concepts_extension_data(succ_extension_data, false);
        if functional_concepts_extension.is_none() {
            return false;
        }

        let mut initialized = false;

        self.collect_linked_successor_nodes(indi_proc_sat_node, calc_alg_context, -1);

        if !calc_alg_context
            .process_context()
            .sat_indi_node_functional_concept_ext_data(functional_concepts_extension)
            .is_successor_extension_initialized()
        {
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_functional_concept_ext_data_mut(functional_concepts_extension)
                .set_successor_extension_initialized(true);
            initialized = true;
        }

        let mut functionality_role_sat_proc_linker = {
            let functional_concepts_extension_data = calc_alg_context
                .process_context_mut()
                .sat_indi_node_functional_concept_ext_data_mut(functional_concepts_extension);
            let role_sat_proc_linker =
                functional_concepts_extension_data.functionality_added_role_process_linker;
            functional_concepts_extension_data.functionality_added_role_process_linker =
                super::satellites::RoleSaturationProcessLinkerId::NONE;
            role_sat_proc_linker
        };
        while functionality_role_sat_proc_linker.is_some() {
            let role = calc_alg_context
                .process_context()
                .role_sat_proc_linker(functionality_role_sat_proc_linker)
                .get_role();
            let tmp_role_sat_proc_linker = functionality_role_sat_proc_linker;
            functionality_role_sat_proc_linker = calc_alg_context
                .process_context()
                .role_sat_proc_linker(tmp_role_sat_proc_linker)
                .get_next();
            calc_alg_context
                .process_context_mut()
                .role_sat_proc_linker_mut(tmp_role_sat_proc_linker)
                .set_next(super::satellites::RoleSaturationProcessLinkerId::NONE);
            if self.install_successor_predecessor_role_functionality_concepts_extension(
                indi_proc_sat_node,
                role,
                calc_alg_context,
            ) {
                let old_head = calc_alg_context
                    .process_context()
                    .sat_indi_node_functional_concept_ext_data(functional_concepts_extension)
                    .linked_successor_added_role_process_linker;
                calc_alg_context
                    .process_context_mut()
                    .role_sat_proc_linker_mut(tmp_role_sat_proc_linker)
                    .set_next(old_head);
                calc_alg_context
                    .process_context_mut()
                    .sat_indi_node_functional_concept_ext_data_mut(functional_concepts_extension)
                    .linked_successor_added_role_process_linker = tmp_role_sat_proc_linker;

                self.add_functional_process_role_extension_functionality_added_to_dependent_individuals(
                    indi_proc_sat_node,
                    role,
                    calc_alg_context,
                );

                let old_head = calc_alg_context
                    .process_context()
                    .sat_indi_node_functional_concept_ext_data(functional_concepts_extension)
                    .linked_predecessor_added_role_process_linker;
                let pred_func_role_proc_linker =
                    Self::s07_create_role_process_linker(role, old_head, calc_alg_context);
                calc_alg_context
                    .process_context_mut()
                    .sat_indi_node_functional_concept_ext_data_mut(functional_concepts_extension)
                    .linked_predecessor_added_role_process_linker = pred_func_role_proc_linker;

                let old_head = calc_alg_context
                    .process_context()
                    .sat_indi_node_functional_concept_ext_data(functional_concepts_extension)
                    .copying_initializing_role_process_linker;
                let copy_init_role_linker =
                    Self::s07_create_role_process_linker(role, old_head, calc_alg_context);
                calc_alg_context
                    .process_context_mut()
                    .sat_indi_node_functional_concept_ext_data_mut(functional_concepts_extension)
                    .copying_initializing_role_process_linker = copy_init_role_linker;
            }
        }

        if !updated {
            let mut succ_linked_added_role_sat_proc_linker = {
                let functional_concepts_extension_data = calc_alg_context
                    .process_context_mut()
                    .sat_indi_node_functional_concept_ext_data_mut(functional_concepts_extension);
                let role_sat_proc_linker =
                    functional_concepts_extension_data.linked_successor_added_role_process_linker;
                functional_concepts_extension_data.linked_successor_added_role_process_linker =
                    super::satellites::RoleSaturationProcessLinkerId::NONE;
                role_sat_proc_linker
            };
            while succ_linked_added_role_sat_proc_linker.is_some() {
                let role = calc_alg_context
                    .process_context()
                    .role_sat_proc_linker(succ_linked_added_role_sat_proc_linker)
                    .get_role();
                let tmp_role_sat_proc_linker = succ_linked_added_role_sat_proc_linker;
                succ_linked_added_role_sat_proc_linker = calc_alg_context
                    .process_context()
                    .role_sat_proc_linker(tmp_role_sat_proc_linker)
                    .get_next();
                calc_alg_context
                    .process_context_mut()
                    .role_sat_proc_linker_mut(tmp_role_sat_proc_linker)
                    .set_next(super::satellites::RoleSaturationProcessLinkerId::NONE);
                updated |= self.update_successor_role_functional_concepts_extensions(
                    indi_proc_sat_node,
                    role,
                    calc_alg_context,
                );
                self.release_role_saturation_process_linker(
                    Id::<RoleSaturationProcess>::new(tmp_role_sat_proc_linker.raw),
                    calc_alg_context,
                );
            }
        }

        if !updated {
            let mut pred_linked_added_role_sat_proc_linker = {
                let functional_concepts_extension_data = calc_alg_context
                    .process_context_mut()
                    .sat_indi_node_functional_concept_ext_data_mut(functional_concepts_extension);
                let role_sat_proc_linker =
                    functional_concepts_extension_data.linked_predecessor_added_role_process_linker;
                functional_concepts_extension_data.linked_predecessor_added_role_process_linker =
                    super::satellites::RoleSaturationProcessLinkerId::NONE;
                role_sat_proc_linker
            };
            while pred_linked_added_role_sat_proc_linker.is_some() {
                let role = calc_alg_context
                    .process_context()
                    .role_sat_proc_linker(pred_linked_added_role_sat_proc_linker)
                    .get_role();
                let tmp_role_sat_proc_linker = pred_linked_added_role_sat_proc_linker;
                pred_linked_added_role_sat_proc_linker = calc_alg_context
                    .process_context()
                    .role_sat_proc_linker(tmp_role_sat_proc_linker)
                    .get_next();
                calc_alg_context
                    .process_context_mut()
                    .role_sat_proc_linker_mut(tmp_role_sat_proc_linker)
                    .set_next(super::satellites::RoleSaturationProcessLinkerId::NONE);
                updated |= self.update_predecessor_role_functional_concepts_extensions(
                    indi_proc_sat_node,
                    role,
                    calc_alg_context,
                );
                self.release_role_saturation_process_linker(
                    Id::<RoleSaturationProcess>::new(tmp_role_sat_proc_linker.raw),
                    calc_alg_context,
                );
            }
        }

        if !updated {
            let mut func_qual_atmost_con_sat_proc_linker = {
                let functional_concepts_extension_data = calc_alg_context
                    .process_context_mut()
                    .sat_indi_node_functional_concept_ext_data_mut(functional_concepts_extension);
                let con_sat_proc_linker =
                    functional_concepts_extension_data.qual_func_atmost_con_process_linker;
                functional_concepts_extension_data.qual_func_atmost_con_process_linker =
                    super::satellites::ConceptSaturationProcessLinkerId::NONE;
                con_sat_proc_linker
            };
            while func_qual_atmost_con_sat_proc_linker.is_some() {
                let con_des = calc_alg_context
                    .process_context()
                    .con_sat_proc_linker(func_qual_atmost_con_sat_proc_linker)
                    .get_concept_saturation_descriptor();
                let tmp_con_des_sat_proc_linker = func_qual_atmost_con_sat_proc_linker;
                func_qual_atmost_con_sat_proc_linker = calc_alg_context
                    .process_context()
                    .con_sat_proc_linker(tmp_con_des_sat_proc_linker)
                    .get_next();
                calc_alg_context
                    .process_context_mut()
                    .con_sat_proc_linker_mut(tmp_con_des_sat_proc_linker)
                    .set_next(super::satellites::ConceptSaturationProcessLinkerId::NONE);
                let func_qual_atleast_concept = calc_alg_context
                    .process_context()
                    .con_sat_desc(con_des)
                    .get_concept();
                let role = calc_alg_context
                    .ontology_arenas()
                    .concept(func_qual_atleast_concept)
                    .get_role();
                // KONCLUDE-PORT-NOTE[api]: the SAT-6 signature still represents
                // `CSortedNegLinker<CConcept*>* qualifiyConLinker` as opaque
                // `Cint64`; the concept arena keeps the operand list, so this
                // passes the existing null placeholder at the sibling boundary.
                updated |= self.update_successor_role_qualified_functional_concepts_extensions(
                    indi_proc_sat_node,
                    role,
                    -1,
                    calc_alg_context,
                );
                self.release_concept_saturation_process_linker(
                    tmp_con_des_sat_proc_linker,
                    calc_alg_context,
                );
                self.add_functional_qualified_process_atmost_concept_extension_to_dependent_individuals(
                    indi_proc_sat_node,
                    con_des,
                    calc_alg_context,
                );
            }
        }

        if calc_alg_context
            .process_context()
            .sat_indi_node_succ_ext_data(succ_extension_data)
            .is_extension_processing_queued()
        {
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_succ_ext_data_mut(succ_extension_data)
                .set_extension_processing_queued(false);
        }

        let _ = initialized;
        updated
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::processNextSuccessorExtensions`.
    /// cpp 2646–2665.
    ///
    /// Pops the next individual from the databox successor-extension processing
    /// queue and (when not separated) runs the configured ALL / FUNCTIONAL concept
    /// extension processors over it, until one reports an update; when none did,
    /// clears the current-process individual. Returns whether an extension was
    /// processed.
    pub fn process_next_successor_extensions(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut extension_processed = false;
        let ext_pro_indi_queue =
            calc_alg_context.saturation_sucessor_extension_individual_node_processing_queue(false);

        while !extension_processed
            && ext_pro_indi_queue.is_some()
            && !calc_alg_context
                .process_context()
                .sat_succ_ext_ind_node_proc_queue(ext_pro_indi_queue)
                .is_empty()
        {
            let mut indi_proc_sat_node = calc_alg_context
                .process_context_mut()
                .sat_succ_ext_ind_node_proc_queue_mut(ext_pro_indi_queue)
                .take_next_to_current_process_individual();
            if indi_proc_sat_node.is_some()
                && !calc_alg_context
                    .process_context()
                    .sat_node(indi_proc_sat_node)
                    .is_separated()
            {
                if !extension_processed && self.conf_all_concepts_extension_processing {
                    extension_processed |= self.process_successor_all_concepts_extensions(
                        &mut indi_proc_sat_node,
                        calc_alg_context,
                    );
                }
                if !extension_processed && self.conf_functional_concepts_extension_processing {
                    extension_processed |= self.process_successor_functional_concepts_extensions(
                        &mut indi_proc_sat_node,
                        calc_alg_context,
                    );
                }
            }
            if !extension_processed {
                calc_alg_context
                    .process_context_mut()
                    .sat_succ_ext_ind_node_proc_queue_mut(ext_pro_indi_queue)
                    .clear_current_process_individual();
            }
        }
        extension_processed
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::processSuccessorALLConceptsExtensions`.
    /// cpp 2670–2713.
    ///
    /// Processes the node's ALL-concepts successor-extension data: (re)collects the
    /// linked successors, lazily initialises the ALL-concepts extension (fanning the
    /// initialisation out to dependent individuals on first init), drains the per-
    /// role process-linker worklist via `updateSuccessorRoleALLConceptsExtensions`,
    /// clears the queued flags, then runs `updateSuccessorALLConceptsExtensions`.
    /// Returns whether anything updated.
    pub fn process_successor_all_concepts_extensions(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if indi_proc_sat_node.is_none()
            || indi_proc_sat_node.index() >= calc_alg_context.process_context().sat_node_count()
        {
            return false;
        }

        let succ_extension_data = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(*indi_proc_sat_node, false);
        if succ_extension_data.is_none() {
            return false;
        }
        let all_concepts_extension = calc_alg_context
            .process_context_mut()
            .sat_successor_extension_all_concepts_extension_data(succ_extension_data, false);
        if all_concepts_extension.is_none() {
            return false;
        }

        let mut initialized = false;

        self.collect_linked_successor_nodes(indi_proc_sat_node, calc_alg_context, -1);

        if !calc_alg_context
            .process_context()
            .sat_indi_node_all_concept_ext_data(all_concepts_extension)
            .is_successor_extension_initialized()
        {
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_all_concept_ext_data_mut(all_concepts_extension)
                .set_successor_extension_initialized(true);
            self.initialize_successor_all_concepts_extensions(indi_proc_sat_node, calc_alg_context);
            self.add_process_extension_to_dependent_individuals(
                indi_proc_sat_node,
                calc_alg_context,
            );
            initialized = true;
            self.all_succ_ext_initialized_count += 1;
        }

        let mut role_sat_proc_linker = {
            let all_concepts_extension_data = calc_alg_context
                .process_context_mut()
                .sat_indi_node_all_concept_ext_data_mut(all_concepts_extension);
            let role_sat_proc_linker = all_concepts_extension_data.role_process_linker;
            all_concepts_extension_data.role_process_linker =
                super::satellites::RoleSaturationProcessLinkerId::NONE;
            role_sat_proc_linker
        };
        while role_sat_proc_linker.is_some() {
            let role = calc_alg_context
                .process_context()
                .role_sat_proc_linker(role_sat_proc_linker)
                .get_role();
            let tmp_role_sat_proc_linker = role_sat_proc_linker;
            role_sat_proc_linker = calc_alg_context
                .process_context()
                .role_sat_proc_linker(tmp_role_sat_proc_linker)
                .get_next();
            calc_alg_context
                .process_context_mut()
                .role_sat_proc_linker_mut(tmp_role_sat_proc_linker)
                .set_next(super::satellites::RoleSaturationProcessLinkerId::NONE);
            self.update_successor_role_all_concepts_extensions(
                indi_proc_sat_node,
                role,
                calc_alg_context,
            );
            self.release_role_saturation_process_linker(
                Id::<RoleSaturationProcess>::new(tmp_role_sat_proc_linker.raw),
                calc_alg_context,
            );
        }

        if calc_alg_context
            .process_context()
            .sat_indi_node_all_concept_ext_data(all_concepts_extension)
            .is_extension_processing_queued()
        {
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_all_concept_ext_data_mut(all_concepts_extension)
                .set_extension_processing_queued(false);
        }
        if calc_alg_context
            .process_context()
            .sat_indi_node_succ_ext_data(succ_extension_data)
            .is_extension_processing_queued()
        {
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_succ_ext_data_mut(succ_extension_data)
                .set_extension_processing_queued(false);
        }

        let updated =
            self.update_successor_all_concepts_extensions(indi_proc_sat_node, calc_alg_context);
        let _ = initialized;
        updated
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addSuccessorExtensionToProcessingQueue`.
    /// cpp 2717–2726.
    ///
    /// Lazily allocates the node's successor-extension (+ ALL-concepts) data and,
    /// when not already queued, marks it queued and inserts the node into the
    /// databox successor-extension processing queue. Returns whether it was newly
    /// enqueued.
    pub fn add_successor_extension_to_processing_queue(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if indi_proc_sat_node.is_none()
            || indi_proc_sat_node.index() >= calc_alg_context.process_context().sat_node_count()
        {
            return false;
        }
        let succ_ext_data = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(*indi_proc_sat_node, true);
        let _succ_indi_all_con_ext_data = calc_alg_context
            .process_context_mut()
            .sat_successor_extension_all_concepts_extension_data(succ_ext_data, true);
        if !calc_alg_context
            .process_context()
            .sat_indi_node_succ_ext_data(succ_ext_data)
            .is_extension_processing_queued()
        {
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_succ_ext_data_mut(succ_ext_data)
                .set_extension_processing_queued(true);
            let queue = calc_alg_context
                .saturation_sucessor_extension_individual_node_processing_queue(true);
            let priority = calc_alg_context
                .process_context()
                .sat_node(*indi_proc_sat_node)
                .get_individual_id();
            calc_alg_context
                .process_context_mut()
                .sat_succ_ext_ind_node_proc_queue_mut(queue)
                .insert_process_individual(*indi_proc_sat_node, priority);
            true
        } else {
            false
        }
    }

    // =======================================================================
    // Dependent-individual fan-out helpers (cpp 2729–2822).
    // Each walks `indiProcSatNode->getCopyDependingIndividualNodeLinker()` and
    // re-queues / re-registers the matching extension on every dependent node.
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addProcessExtensionToDependentIndividuals`.
    /// cpp 2729–2736.
    ///
    /// Re-enqueues every copy-depending individual node for successor-extension
    /// processing.
    pub fn add_process_extension_to_dependent_individuals(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // Port of the C++ body (cpp 2729–2736). The copy-depending linker chain
        // (`CXNegLinker<CIndividualSaturationProcessNode*>`) is the SAT-1
        // `get_copy_depending_individual_node_linker()` slice (now ported), so the
        // fan-out loop resolves. `add_successor_extension_to_processing_queue` is the
        // sibling enqueue (this unit).
        //   for (depIndiLinkerIt in indiProcSatNode->getCopyDependingIndividualNodeLinker()) {
        //       depIndi = depIndiLinkerIt->getData();
        //       if (depIndi) addSuccessorExtensionToProcessingQueue(depIndi, calcAlgContext);
        //   }
        let dep_indis: Vec<SatNodeId> = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_copy_depending_individual_node_linker()
            .iter()
            .filter(|l| l.target.is_some())
            .map(|l| l.target)
            .collect();
        for mut dep_indi in dep_indis {
            self.add_successor_extension_to_processing_queue(&mut dep_indi, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addALLProcessRoleExtensionToDependentIndividuals`.
    /// cpp 2738–2754.
    ///
    /// For every copy-depending individual node, re-enqueues it for extension
    /// processing and (when its ALL-concepts extension is initialised and lacks a
    /// process-linker for `role`) registers a fresh role process-linker.
    pub fn add_all_process_role_extension_to_dependent_individuals(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let dep_indis: Vec<SatNodeId> = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_copy_depending_individual_node_linker()
            .iter()
            .filter(|l| l.target.is_some())
            .map(|l| l.target)
            .collect();
        for mut dep_indi in dep_indis {
            let succ_ext_data = calc_alg_context
                .process_context_mut()
                .sat_node_ext_successor_extension_data(dep_indi, true);
            let succ_indi_all_con_ext_data = calc_alg_context
                .process_context_mut()
                .sat_successor_extension_all_concepts_extension_data(succ_ext_data, true);
            self.add_successor_extension_to_processing_queue(&mut dep_indi, calc_alg_context);
            if calc_alg_context
                .process_context()
                .sat_indi_node_all_concept_ext_data(succ_indi_all_con_ext_data)
                .is_successor_extension_initialized()
            {
                let old_head = calc_alg_context
                    .process_context()
                    .sat_indi_node_all_concept_ext_data(succ_indi_all_con_ext_data)
                    .get_role_process_linker();
                if !Self::s07_role_process_linker_chain_has_role(old_head, role, calc_alg_context) {
                    let role_proc_linker =
                        Self::s07_create_role_process_linker(role, old_head, calc_alg_context);
                    calc_alg_context
                        .process_context_mut()
                        .sat_indi_node_all_concept_ext_data_mut(succ_indi_all_con_ext_data)
                        .role_process_linker = role_proc_linker;
                }
            }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addFUNCTIONALProcessRoleExtensionLinkedSuccessorAddedToDependentIndividuals`.
    /// cpp 2757–2773.
    ///
    /// For every copy-depending individual node, re-enqueues it and (when its
    /// FUNCTIONAL-concepts extension is initialised and lacks a linked-successor-added
    /// process-linker for `role`) registers a fresh linked-successor-added role
    /// process-linker.
    pub fn add_functional_process_role_extension_linked_successor_added_to_dependent_individuals(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let dep_indis: Vec<SatNodeId> = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_copy_depending_individual_node_linker()
            .iter()
            .filter(|l| l.target.is_some())
            .map(|l| l.target)
            .collect();
        for mut dep_indi in dep_indis {
            let succ_ext_data = calc_alg_context
                .process_context_mut()
                .sat_node_ext_successor_extension_data(dep_indi, true);
            let succ_indi_functional_con_ext_data = calc_alg_context
                .process_context_mut()
                .sat_successor_extension_functional_concepts_extension_data(succ_ext_data, true);
            self.add_successor_extension_to_processing_queue(&mut dep_indi, calc_alg_context);
            if calc_alg_context
                .process_context()
                .sat_indi_node_functional_concept_ext_data(succ_indi_functional_con_ext_data)
                .is_successor_extension_initialized()
            {
                let old_head = calc_alg_context
                    .process_context()
                    .sat_indi_node_functional_concept_ext_data(succ_indi_functional_con_ext_data)
                    .linked_successor_added_role_process_linker;
                if !Self::s07_role_process_linker_chain_has_role(old_head, role, calc_alg_context) {
                    let role_proc_linker =
                        Self::s07_create_role_process_linker(role, old_head, calc_alg_context);
                    calc_alg_context
                        .process_context_mut()
                        .sat_indi_node_functional_concept_ext_data_mut(
                            succ_indi_functional_con_ext_data,
                        )
                        .linked_successor_added_role_process_linker = role_proc_linker;
                }
            }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addFUNCTIONALQualifiedProcessAtmostConceptExtensionToDependentIndividuals`.
    /// cpp 2778–2785.
    ///
    /// For every copy-depending individual node, registers the qualified-functional-
    /// atmost concept extension processing for `con_des`.
    pub fn add_functional_qualified_process_atmost_concept_extension_to_dependent_individuals(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        con_des: ConceptSaturationDescriptorId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // Port of the C++ body (cpp 2778–2785). The copy-depending linker is the
        // SAT-1 `get_copy_depending_individual_node_linker()` slice (now ported);
        // `add_qualified_functional_atmost_concept_extension_processing` is the
        // sibling registrar (this unit).
        //   for (depIndiLinkerIt in indiProcSatNode->getCopyDependingIndividualNodeLinker()) {
        //       depIndi = depIndiLinkerIt->getData();
        //       if (depIndi) addQualifiedFUNCTIONALAtmostConceptExtensionProcessing(conDes, depIndi, calcAlgContext);
        //   }
        let dep_indis: Vec<SatNodeId> = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_copy_depending_individual_node_linker()
            .iter()
            .filter(|l| l.target.is_some())
            .map(|l| l.target)
            .collect();
        for mut dep_indi in dep_indis {
            self.add_qualified_functional_atmost_concept_extension_processing(
                con_des,
                &mut dep_indi,
                calc_alg_context,
            );
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addFUNCTIONALProcessRoleExtensionLinkedPredecessorAddedToDependentIndividuals`.
    /// cpp 2790–2806.
    ///
    /// For every copy-depending individual node whose FUNCTIONAL-concepts extension
    /// is initialised, re-enqueues it and (when it lacks a linked-predecessor-added
    /// process-linker for `role`) registers a fresh linked-predecessor-added role
    /// process-linker.
    pub fn add_functional_process_role_extension_linked_predecessor_added_to_dependent_individuals(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let dep_indis: Vec<SatNodeId> = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_copy_depending_individual_node_linker()
            .iter()
            .filter(|l| l.target.is_some())
            .map(|l| l.target)
            .collect();
        for mut dep_indi in dep_indis {
            let succ_ext_data = calc_alg_context
                .process_context_mut()
                .sat_node_ext_successor_extension_data(dep_indi, true);
            let succ_indi_functional_con_ext_data = calc_alg_context
                .process_context_mut()
                .sat_successor_extension_functional_concepts_extension_data(succ_ext_data, true);
            if calc_alg_context
                .process_context()
                .sat_indi_node_functional_concept_ext_data(succ_indi_functional_con_ext_data)
                .is_successor_extension_initialized()
            {
                self.add_successor_extension_to_processing_queue(&mut dep_indi, calc_alg_context);
                let old_head = calc_alg_context
                    .process_context()
                    .sat_indi_node_functional_concept_ext_data(succ_indi_functional_con_ext_data)
                    .linked_predecessor_added_role_process_linker;
                if !Self::s07_role_process_linker_chain_has_role(old_head, role, calc_alg_context) {
                    let role_proc_linker =
                        Self::s07_create_role_process_linker(role, old_head, calc_alg_context);
                    calc_alg_context
                        .process_context_mut()
                        .sat_indi_node_functional_concept_ext_data_mut(
                            succ_indi_functional_con_ext_data,
                        )
                        .linked_predecessor_added_role_process_linker = role_proc_linker;
                }
            }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addFUNCTIONALProcessRoleExtensionFunctionalityAddedToDependentIndividuals`.
    /// cpp 2808–2822.
    ///
    /// For every copy-depending individual node, re-enqueues it and (when it lacks a
    /// functionality-added process-linker for `role`) registers a fresh
    /// functionality-added role process-linker.
    pub fn add_functional_process_role_extension_functionality_added_to_dependent_individuals(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let dep_indis: Vec<SatNodeId> = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_copy_depending_individual_node_linker()
            .iter()
            .filter(|l| l.target.is_some())
            .map(|l| l.target)
            .collect();
        for mut dep_indi in dep_indis {
            let succ_ext_data = calc_alg_context
                .process_context_mut()
                .sat_node_ext_successor_extension_data(dep_indi, true);
            let succ_indi_functional_con_ext_data = calc_alg_context
                .process_context_mut()
                .sat_successor_extension_functional_concepts_extension_data(succ_ext_data, true);
            self.add_successor_extension_to_processing_queue(&mut dep_indi, calc_alg_context);
            let old_head = calc_alg_context
                .process_context()
                .sat_indi_node_functional_concept_ext_data(succ_indi_functional_con_ext_data)
                .functionality_added_role_process_linker;
            if !Self::s07_role_process_linker_chain_has_role(old_head, role, calc_alg_context) {
                let role_proc_linker =
                    Self::s07_create_role_process_linker(role, old_head, calc_alg_context);
                calc_alg_context
                    .process_context_mut()
                    .sat_indi_node_functional_concept_ext_data_mut(
                        succ_indi_functional_con_ext_data,
                    )
                    .functionality_added_role_process_linker = role_proc_linker;
            }
        }
    }

    // =======================================================================
    // Linked-successor collection (cpp 3194–3383).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::collectLinkedSuccessorNodes`.
    /// cpp 3194–3227.
    ///
    /// Incrementally (re)builds the node's `CLinkedRoleSaturationSuccessorHash`:
    /// walks the newly added concept-saturation descriptors (down to the last
    /// examined one) and, for each `∃`/`≥`/`VALUE` (or negated `∀`/`≤`) concept,
    /// adds its linked successor; then walks the newly added role-assertion linkers
    /// and adds each as a linked successor. Advances the last-examined watermarks.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ trailing `CLinkedRoleSaturationSuccessorHash*
    /// linkedRoleSuccHash` defaults to `nullptr` (lazily fetched from the node);
    /// Rust has no defaults, so the port keeps it as the last param
    /// `linked_role_succ_hash: Cint64` (`INVALID` == `nullptr`), matching the C++
    /// argument order (after `calcAlgContext`).
    pub fn collect_linked_successor_nodes(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        // `CLinkedRoleSaturationSuccessorHash* linkedRoleSuccHash` — satellite (default nullptr).
        linked_role_succ_hash: Cint64,
    ) {
        if indi_proc_sat_node.is_none()
            || indi_proc_sat_node.index() >= calc_alg_context.process_context().sat_node_count()
        {
            return;
        }
        let linked_role_succ_hash = if linked_role_succ_hash < 0 {
            calc_alg_context
                .process_context_mut()
                .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, true)
        } else {
            LinkedRoleSaturationSuccessorHashId::new(linked_role_succ_hash)
        };
        if linked_role_succ_hash.is_none()
            || linked_role_succ_hash.index()
                >= calc_alg_context
                    .process_context()
                    .linked_role_sat_succ_hash_count()
        {
            return;
        }

        let last_examined_con_des = calc_alg_context
            .process_context()
            .linked_role_sat_succ_hash(linked_role_succ_hash)
            .get_last_examined_concept_descriptor();
        let con_set = calc_alg_context
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(*indi_proc_sat_node, true);
        let con_des_linker = calc_alg_context
            .process_context()
            .reapply_con_sat_label_set(con_set)
            .get_concept_saturation_description_linker();

        let mut con_des_it = con_des_linker;
        while con_des_it.is_some() && con_des_it != last_examined_con_des {
            if con_des_it.index() >= calc_alg_context.process_context().con_sat_desc_count() {
                break;
            }
            let (concept, con_negation, next_con_des) = {
                let con_des_ref = calc_alg_context.process_context().con_sat_desc(con_des_it);
                (
                    con_des_ref.get_concept(),
                    con_des_ref.get_negation(),
                    con_des_ref.get_next_concept_desciptor(),
                )
            };
            if concept.is_some()
                && concept.index() < calc_alg_context.ontology_arenas().concept_count() as usize
            {
                let con_code = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_operator_code();
                if (!con_negation && (con_code == CCSOME || con_code == CCAQSOME))
                    || (con_negation && con_code == CCALL)
                {
                    self.add_linked_successor_node_for_concept(
                        con_des_it,
                        linked_role_succ_hash,
                        indi_proc_sat_node,
                        calc_alg_context,
                    );
                }
                if (!con_negation && con_code == CCATLEAST)
                    || (con_negation && con_code == CCATMOST)
                {
                    self.add_linked_successor_node_for_concept(
                        con_des_it,
                        linked_role_succ_hash,
                        indi_proc_sat_node,
                        calc_alg_context,
                    );
                }
                if !con_negation && con_code == CCVALUE {
                    self.add_linked_successor_node_for_concept(
                        con_des_it,
                        linked_role_succ_hash,
                        indi_proc_sat_node,
                        calc_alg_context,
                    );
                }
            }
            con_des_it = next_con_des;
        }

        let last_sat_succ_role_ass_linker = calc_alg_context
            .process_context()
            .linked_role_sat_succ_hash(linked_role_succ_hash)
            .get_last_examined_role_assertion_linker();
        let sat_succ_role_ass_linker = calc_alg_context
            .process_context()
            .sat_node_ext_role_assertion_linker(*indi_proc_sat_node);
        let mut sat_succ_role_ass_linker_it = sat_succ_role_ass_linker;
        while sat_succ_role_ass_linker_it.is_some()
            && sat_succ_role_ass_linker_it.raw != last_sat_succ_role_ass_linker
        {
            if sat_succ_role_ass_linker_it.index()
                >= calc_alg_context
                    .process_context()
                    .sat_succ_role_assertion_linker_count()
            {
                break;
            }
            let (role, role_negation, dest_node, next_linker) = {
                let linker = calc_alg_context
                    .process_context()
                    .sat_succ_role_assertion_linker(sat_succ_role_ass_linker_it);
                (
                    linker.get_assertion_role(),
                    linker.get_assertion_role_negation(),
                    linker.get_assertion_destination_node(),
                    linker.get_next(),
                )
            };
            self.add_linked_successor_node_for_role_assertion(
                dest_node,
                role,
                role_negation,
                linked_role_succ_hash,
                indi_proc_sat_node,
                calc_alg_context,
            );
            sat_succ_role_ass_linker_it = next_linker;
        }

        calc_alg_context
            .process_context_mut()
            .linked_role_sat_succ_hash_mut(linked_role_succ_hash)
            .set_last_examined_role_assertion_linker(sat_succ_role_ass_linker.raw)
            .set_last_examined_concept_descriptor(con_des_linker);
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addLinkedSuccessorNodeForRoleAssertion`.
    /// cpp 3234–3243.
    ///
    /// For each indirect super-role of the assertion role whose (inversion-adjusted)
    /// polarity is positive, adds `dest_node` as a linked successor (cardinality 1,
    /// role-assertion flag set) on the linked-role-successor hash.
    pub fn add_linked_successor_node_for_role_assertion(
        &mut self,
        // `CIndividualSaturationProcessNode* destNode` (by value).
        dest_node: SatNodeId,
        role: RoleId,
        role_inversion: bool,
        linked_role_succ_hash: LinkedRoleSaturationSuccessorHashId,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // KONCLUDE-PORT-NOTE[identity]: self-inclusive super-role list (see
        // `s07_add_linked_successors_for_resolved_node`).
        let super_roles = Self::saturation_indirect_super_roles(role, calc_alg_context);
        for super_role_it in super_roles {
            if !super_role_it.negated ^ role_inversion {
                calc_alg_context
                    .process_context_mut()
                    .linked_role_successor_hash_add_linked_successor(
                        linked_role_succ_hash,
                        super_role_it.target,
                        dest_node,
                        role,
                        1,
                    );
            }
        }
        let _ = indi_proc_sat_node;
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addLinkedSuccessorNodeForConcept`.
    /// cpp 3250–3383.
    ///
    /// Resolves the successor individual node a `∃`/`≥`/`VALUE` (or negated `∀`/`≤`)
    /// concept points at — first via the concept's existential-successor saturation
    /// reference linking, else via the first operand concept's reference linking,
    /// else via the (data-)top concept's reference linking — and, for each positive
    /// indirect super-role, adds it as a linked successor (a VALUE-nominal successor
    /// keyed by nominal id, or a node successor with the computed cardinality).
    pub fn add_linked_successor_node_for_concept(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
        linked_role_succ_hash: LinkedRoleSaturationSuccessorHashId,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if con_des.is_none()
            || con_des.index() >= calc_alg_context.process_context().con_sat_desc_count()
        {
            return;
        }
        let (concept, con_negation) = {
            let con_des_ref = calc_alg_context.process_context().con_sat_desc(con_des);
            (con_des_ref.get_concept(), con_des_ref.get_negation())
        };
        if concept.is_none()
            || concept.index() >= calc_alg_context.ontology_arenas().concept_count() as usize
        {
            return;
        }

        let (role, cardinality, con_code, operands, mut nominal_successor, nominal_id) = {
            let concept_ref = calc_alg_context.ontology_arenas().concept(concept);
            let role = concept_ref.get_role();
            let param = concept_ref.get_parameter();
            let cardinality = param + if con_negation { 1 } else { 0 };
            let con_code = concept_ref.get_operator_code();
            let operands = concept_ref.get_operand_list().to_vec();
            let mut nominal_successor = false;
            let mut nominal_id = 0;
            if !con_negation && con_code == CCVALUE {
                let nominal_individual = concept_ref.get_nominal_individual();
                if nominal_individual.is_none()
                    || nominal_individual.index()
                        >= calc_alg_context.ontology_arenas().individual_count() as usize
                {
                    return;
                }
                nominal_successor = true;
                nominal_id = calc_alg_context
                    .ontology_arenas()
                    .individual(nominal_individual)
                    .get_individual_id();
            }
            (
                role,
                cardinality,
                con_code,
                operands,
                nominal_successor,
                nominal_id,
            )
        };

        let mut add_successor = false;
        let mut successor_count = 0;
        if !con_negation && con_code == CCVALUE {
            add_successor = true;
            successor_count = 1;
        }
        if (!con_negation && (con_code == CCSOME || con_code == CCAQSOME))
            || (con_negation && con_code == CCALL)
        {
            add_successor = true;
            successor_count = 1;
            nominal_successor = false;
        }
        if cardinality >= 1
            && ((!con_negation && con_code == CCATLEAST) || (con_negation && con_code == CCATMOST))
        {
            add_successor = true;
            successor_count = cardinality;
            nominal_successor = false;
        }
        if !add_successor {
            return;
        }

        let mut found_special_indi_node = false;
        let mut found_operand_indi_node = false;
        let exist_indi_node =
            Self::s07_existential_successor_reference_node(concept, calc_alg_context);
        if exist_indi_node.is_some() {
            found_special_indi_node = true;
            Self::s07_add_linked_successors_for_resolved_node(
                linked_role_succ_hash,
                role,
                role,
                exist_indi_node,
                successor_count,
                nominal_successor,
                nominal_id,
                calc_alg_context,
            );
        }

        if !found_special_indi_node {
            for concept_op_linker_it in operands {
                found_operand_indi_node = true;
                let op_concept = concept_op_linker_it.target;
                let op_con_negation = concept_op_linker_it.negated ^ con_negation;
                let exist_indi_node =
                    Self::s07_concept_reference_node(op_concept, op_con_negation, calc_alg_context);
                if exist_indi_node.is_some() {
                    Self::s07_add_linked_successors_for_resolved_node(
                        linked_role_succ_hash,
                        role,
                        role,
                        exist_indi_node,
                        successor_count,
                        nominal_successor,
                        nominal_id,
                        calc_alg_context,
                    );
                }
            }
        }

        if !found_special_indi_node && !found_operand_indi_node {
            let base_top_concept = if role.is_some()
                && role.index() < calc_alg_context.ontology_arenas().role_count() as usize
                && calc_alg_context.ontology_arenas().role(role).is_data_role()
            {
                calc_alg_context
                    .processing_data_box()
                    .ontology_top_data_range_concept()
            } else {
                calc_alg_context
                    .processing_data_box()
                    .ontology_top_concept()
            };
            let exist_indi_node =
                Self::s07_concept_reference_node(base_top_concept, false, calc_alg_context);
            if exist_indi_node.is_some() {
                Self::s07_add_linked_successors_for_resolved_node(
                    linked_role_succ_hash,
                    role,
                    role,
                    exist_indi_node,
                    successor_count,
                    nominal_successor,
                    nominal_id,
                    calc_alg_context,
                );
            }
        }
        let _ = indi_proc_sat_node;
    }

    // =======================================================================
    // Per-role concept-extension-processing registration (cpp 6209–6357).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addALLConceptExtensionProcessingRole`.
    /// cpp 6209–6233.
    ///
    /// When ALL-concepts extension processing is enabled and the role-backward-
    /// propagation data has not yet queued ALL-concepts processing, marks it queued,
    /// enqueues the node for extension processing, and (when the ALL-concepts
    /// extension is initialised and lacks a process-linker for `role`) registers a
    /// fresh role process-linker.
    pub fn add_all_concept_extension_processing_role(
        &mut self,
        role: RoleId,
        back_prop_hash_data: &mut super::satellites::RoleBackwardSaturationPropagationHashData,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if !self.conf_all_concepts_extension_processing {
            return;
        }
        if back_prop_hash_data.role_all_concepts_processing_queued {
            return;
        }
        back_prop_hash_data.role_all_concepts_processing_queued = true;
        let succ_ext_data = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(*indi_proc_sat_node, true);
        let succ_indi_all_con_ext_data = calc_alg_context
            .process_context_mut()
            .sat_successor_extension_all_concepts_extension_data(succ_ext_data, true);
        self.add_successor_extension_to_processing_queue(indi_proc_sat_node, calc_alg_context);

        if calc_alg_context
            .process_context()
            .sat_indi_node_all_concept_ext_data(succ_indi_all_con_ext_data)
            .is_successor_extension_initialized()
        {
            let old_head = calc_alg_context
                .process_context()
                .sat_indi_node_all_concept_ext_data(succ_indi_all_con_ext_data)
                .get_role_process_linker();
            if !Self::s07_role_process_linker_chain_has_role(old_head, role, calc_alg_context) {
                let role_process_linker =
                    Self::s07_create_role_process_linker(role, old_head, calc_alg_context);
                calc_alg_context
                    .process_context_mut()
                    .sat_indi_node_all_concept_ext_data_mut(succ_indi_all_con_ext_data)
                    .role_process_linker = role_process_linker;
            }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addFUNCTIONALConceptExtensionProcessingRole`.
    /// cpp 6238–6250.
    ///
    /// When FUNCTIONAL-concepts extension processing is enabled, enqueues the node
    /// for extension processing and (when it lacks a functionality-added process-
    /// linker for `role`) registers a fresh functionality-added role process-linker.
    pub fn add_functional_concept_extension_processing_role(
        &mut self,
        role: RoleId,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if !self.conf_functional_concepts_extension_processing {
            return;
        }
        let succ_ext_data = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(*indi_proc_sat_node, true);
        let succ_indi_functional_con_ext_data = calc_alg_context
            .process_context_mut()
            .sat_successor_extension_functional_concepts_extension_data(succ_ext_data, true);
        self.add_successor_extension_to_processing_queue(indi_proc_sat_node, calc_alg_context);

        let old_head = calc_alg_context
            .process_context()
            .sat_indi_node_functional_concept_ext_data(succ_indi_functional_con_ext_data)
            .functionality_added_role_process_linker;
        if !Self::s07_role_process_linker_chain_has_role(old_head, role, calc_alg_context) {
            let role_process_linker =
                Self::s07_create_role_process_linker(role, old_head, calc_alg_context);
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_functional_concept_ext_data_mut(succ_indi_functional_con_ext_data)
                .functionality_added_role_process_linker = role_process_linker;
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addQualifiedFUNCTIONALAtmostConceptExtensionProcessing`.
    /// cpp 6255–6267.
    ///
    /// When FUNCTIONAL-concepts extension processing is enabled, enqueues the node
    /// for extension processing and (when it lacks a qualified-functional-atmost
    /// concept process-linker for `con_des`) registers a fresh concept process-linker.
    pub fn add_qualified_functional_atmost_concept_extension_processing(
        &mut self,
        con_des: ConceptSaturationDescriptorId,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if !self.conf_functional_concepts_extension_processing {
            return;
        }
        let succ_ext_data = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(*indi_proc_sat_node, true);
        let succ_indi_functional_con_ext_data = calc_alg_context
            .process_context_mut()
            .sat_successor_extension_functional_concepts_extension_data(succ_ext_data, true);
        self.add_successor_extension_to_processing_queue(indi_proc_sat_node, calc_alg_context);

        let old_head = calc_alg_context
            .process_context()
            .sat_indi_node_functional_concept_ext_data(succ_indi_functional_con_ext_data)
            .qual_func_atmost_con_process_linker;
        if !Self::s07_concept_process_linker_chain_has_descriptor(
            old_head,
            con_des,
            calc_alg_context,
        ) {
            let con_process_linker =
                Self::s07_create_concept_process_linker(con_des, old_head, calc_alg_context);
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_functional_concept_ext_data_mut(succ_indi_functional_con_ext_data)
                .qual_func_atmost_con_process_linker = con_process_linker;
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::addNewLinkedExtensionProcessingRole`.
    /// cpp 6271–6357.
    ///
    /// On a newly linked successor for `role`, (re)queues extension processing for
    /// the already-initialised faces of the node's successor-extension data. For the
    /// ALL face (when `queue_all_extension`), determines whether queuing is required
    /// (caching the answer on the linked-successor data, deriving it from the role-
    /// backward-propagation reapply linker) and, if so, marks queued + registers an
    /// ALL role process-linker. For the FUNCTIONAL face (when `queue_functional_extension`
    /// and queuing is required), marks queued + registers linked-successor-added and
    /// linked-predecessor-added role process-linkers. Enqueues the node once if any
    /// face was queued.
    pub fn add_new_linked_extension_processing_role(
        &mut self,
        role: RoleId,
        indi_proc_sat_node: &mut SatNodeId,
        queue_all_extension: bool,
        queue_functional_extension: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if !self.conf_concepts_extension_processing
            || indi_proc_sat_node.is_none()
            || indi_proc_sat_node.index() >= calc_alg_context.process_context().sat_node_count()
        {
            return;
        }

        let succ_ext_data = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(*indi_proc_sat_node, false);
        if succ_ext_data.is_none() {
            return;
        }
        let succ_indi_all_con_ext_data = calc_alg_context
            .process_context_mut()
            .sat_successor_extension_all_concepts_extension_data(succ_ext_data, false);
        let succ_indi_functional_con_ext_data = calc_alg_context
            .process_context_mut()
            .sat_successor_extension_functional_concepts_extension_data(succ_ext_data, false);

        let succ_all_extension_initialized = succ_indi_all_con_ext_data.is_some()
            && calc_alg_context
                .process_context()
                .sat_indi_node_all_concept_ext_data(succ_indi_all_con_ext_data)
                .is_successor_extension_initialized();
        let succ_functional_extension_initialized = succ_indi_functional_con_ext_data.is_some()
            && calc_alg_context
                .process_context()
                .sat_indi_node_functional_concept_ext_data(succ_indi_functional_con_ext_data)
                .is_successor_extension_initialized();
        if !succ_all_extension_initialized && !succ_functional_extension_initialized {
            return;
        }

        let linked_succ_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, false);
        if linked_succ_hash.is_none() {
            return;
        }
        let succ_data = calc_alg_context
            .process_context_mut()
            .linked_role_successor_data(linked_succ_hash, role, true);
        if succ_data.is_none() {
            return;
        }

        let mut queue_processing = false;
        if succ_all_extension_initialized
            && !calc_alg_context
                .process_context()
                .linked_role_sat_succ_data(succ_data)
                .role_all_concepts_processing_queued
            && queue_all_extension
        {
            let mut all_queueing_required = calc_alg_context
                .process_context()
                .linked_role_sat_succ_data(succ_data)
                .role_all_concepts_queuing_required;
            if !all_queueing_required {
                let backward_prop_hash = calc_alg_context
                    .process_context()
                    .sat_node(*indi_proc_sat_node)
                    .role_back_prop_hash;
                if backward_prop_hash.is_some() {
                    if let Some(backward_prop_data) = calc_alg_context
                        .process_context()
                        .role_backward_sat_prop_hash(backward_prop_hash)
                        .get_role_backward_propagation_data_hash()
                        .get(&role)
                    {
                        if backward_prop_data.reapply_linker.is_some() {
                            all_queueing_required = true;
                            calc_alg_context
                                .process_context_mut()
                                .linked_role_sat_succ_data_mut(succ_data)
                                .role_all_concepts_queuing_required = true;
                        }
                    }
                }
            }

            if all_queueing_required {
                calc_alg_context
                    .process_context_mut()
                    .linked_role_sat_succ_data_mut(succ_data)
                    .role_all_concepts_processing_queued = true;
                queue_processing = true;
                let old_head = calc_alg_context
                    .process_context()
                    .sat_indi_node_all_concept_ext_data(succ_indi_all_con_ext_data)
                    .get_role_process_linker();
                if !Self::s07_role_process_linker_chain_has_role(old_head, role, calc_alg_context) {
                    let linker =
                        Self::s07_create_role_process_linker(role, old_head, calc_alg_context);
                    calc_alg_context
                        .process_context_mut()
                        .sat_indi_node_all_concept_ext_data_mut(succ_indi_all_con_ext_data)
                        .role_process_linker = linker;
                }
            }
        }

        if succ_functional_extension_initialized
            && !calc_alg_context
                .process_context()
                .linked_role_sat_succ_data(succ_data)
                .role_functional_concepts_processing_queued
            && calc_alg_context
                .process_context()
                .linked_role_sat_succ_data(succ_data)
                .role_functional_concepts_queuing_required
            && queue_functional_extension
        {
            calc_alg_context
                .process_context_mut()
                .linked_role_sat_succ_data_mut(succ_data)
                .role_functional_concepts_processing_queued = true;
            queue_processing = true;

            let linked_successor_head = calc_alg_context
                .process_context()
                .sat_indi_node_functional_concept_ext_data(succ_indi_functional_con_ext_data)
                .linked_successor_added_role_process_linker;
            if !Self::s07_role_process_linker_chain_has_role(
                linked_successor_head,
                role,
                calc_alg_context,
            ) {
                let linker = Self::s07_create_role_process_linker(
                    role,
                    linked_successor_head,
                    calc_alg_context,
                );
                calc_alg_context
                    .process_context_mut()
                    .sat_indi_node_functional_concept_ext_data_mut(
                        succ_indi_functional_con_ext_data,
                    )
                    .linked_successor_added_role_process_linker = linker;
            }

            let linked_predecessor_head = calc_alg_context
                .process_context()
                .sat_indi_node_functional_concept_ext_data(succ_indi_functional_con_ext_data)
                .linked_predecessor_added_role_process_linker;
            if !Self::s07_role_process_linker_chain_has_role(
                linked_predecessor_head,
                role,
                calc_alg_context,
            ) {
                let linker = Self::s07_create_role_process_linker(
                    role,
                    linked_predecessor_head,
                    calc_alg_context,
                );
                calc_alg_context
                    .process_context_mut()
                    .sat_indi_node_functional_concept_ext_data_mut(
                        succ_indi_functional_con_ext_data,
                    )
                    .linked_predecessor_added_role_process_linker = linker;
            }
        }

        if queue_processing {
            self.add_successor_extension_to_processing_queue(indi_proc_sat_node, calc_alg_context);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::concept::Concept;
    use super::super::super::model::concept_process::{
        ConceptProcessData, ConceptSaturationReferenceLinkingData,
        SaturationConceptReferenceLinking,
    };
    use super::super::super::model::individual::Individual;
    use super::super::super::model::op::{CCALL, CCATLEAST, CCSOME, CCTOP, CCVALUE};
    use super::super::super::model::role::Role;
    use super::super::super::model::substrate::{NegLink, INVALID};
    use super::super::super::process::sat_node::IndividualSaturationProcessNode;
    use super::super::algorithm::SaturationTaskHandleAlgorithm;
    use super::super::satellites::{
        BackwardSaturationPropagationReapplyDescriptor, ConceptSaturationDescriptor,
        RoleBackwardSaturationPropagationHashData,
    };
    use super::*;

    fn make_role(ctx: &mut CalculationAlgorithmContextBase, tag: Cint64) -> RoleId {
        let mut role = Role::new();
        role.init_with_tag(tag);
        ctx.ontology_arenas_mut().alloc_role(role)
    }

    fn make_concept(
        ctx: &mut CalculationAlgorithmContextBase,
        op: Cint64,
        role: RoleId,
        param: Cint64,
    ) -> ConceptId {
        let mut concept = Concept::new();
        concept
            .set_operator_code(op)
            .set_role(role)
            .set_parameter(param);
        ctx.ontology_arenas_mut().alloc_concept(concept)
    }

    fn set_concept_tag(ctx: &mut CalculationAlgorithmContextBase, concept: ConceptId, tag: Cint64) {
        ctx.ontology_arenas_mut()
            .concept_mut(concept)
            .set_concept_tag(tag);
    }

    fn make_descriptor(
        ctx: &mut CalculationAlgorithmContextBase,
        concept: ConceptId,
        negated: bool,
    ) -> ConceptSaturationDescriptorId {
        let mut descriptor = ConceptSaturationDescriptor::new();
        descriptor.init_concept_saturation_descriptor(concept, negated);
        ctx.process_context_mut().alloc_con_sat_desc(descriptor)
    }

    fn prepend_descriptor_to_label_set(
        ctx: &mut CalculationAlgorithmContextBase,
        node: SatNodeId,
        descriptor: ConceptSaturationDescriptorId,
    ) {
        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(node, true);
        let old_head = ctx
            .process_context()
            .reapply_con_sat_label_set(label_set)
            .get_concept_saturation_description_linker();
        let new_head = ctx
            .process_context_mut()
            .append_concept_saturation_descriptor_chain(descriptor, old_head);
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(label_set)
            .concept_sat_des_linker = new_head;
    }

    fn set_reference_node(
        ctx: &mut CalculationAlgorithmContextBase,
        concept: ConceptId,
        negated: bool,
        node: SatNodeId,
    ) {
        let mut sat_linking = SaturationConceptReferenceLinking::new();
        sat_linking.set_individual_process_node_for_concept(node);
        let sat_linking = ctx
            .ontology_arenas_mut()
            .alloc_saturation_concept_reference_linking(sat_linking);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_saturation_reference_linking_data(sat_linking, negated);
        attach_reference_data(ctx, concept, ref_data);
    }

    fn set_existential_reference_node(
        ctx: &mut CalculationAlgorithmContextBase,
        concept: ConceptId,
        node: SatNodeId,
    ) {
        let mut sat_linking = SaturationConceptReferenceLinking::new();
        sat_linking.set_individual_process_node_for_concept(node);
        let sat_linking = ctx
            .ontology_arenas_mut()
            .alloc_saturation_concept_reference_linking(sat_linking);
        let mut ref_data = ConceptSaturationReferenceLinkingData::new();
        ref_data.set_existential_successor_concept_saturation_reference_linking_data(sat_linking);
        attach_reference_data(ctx, concept, ref_data);
    }

    fn attach_reference_data(
        ctx: &mut CalculationAlgorithmContextBase,
        concept: ConceptId,
        ref_data: ConceptSaturationReferenceLinkingData,
    ) {
        let ref_data = ctx
            .ontology_arenas_mut()
            .alloc_concept_saturation_reference_linking_data(ref_data);
        let mut proc_data = ConceptProcessData::new();
        proc_data.set_concept_reference_linking(ref_data);
        let proc_data = ctx
            .ontology_arenas_mut()
            .alloc_concept_process_data(proc_data);
        ctx.ontology_arenas_mut()
            .concept_mut(concept)
            .set_concept_data(proc_data.raw);
    }

    fn value_successor_data_for_nominal(
        ctx: &mut CalculationAlgorithmContextBase,
        hash: LinkedRoleSaturationSuccessorHashId,
        role: RoleId,
        nominal_id: Cint64,
    ) -> super::super::satellites::SaturationSuccessorDataId {
        let role_data = ctx
            .process_context_mut()
            .linked_role_successor_data(hash, role, false);
        if role_data.is_none() {
            return super::super::satellites::SaturationSuccessorDataId::NONE;
        }
        ctx.process_context()
            .linked_role_sat_succ_data(role_data)
            .succ_node_data_map
            .get(&nominal_id)
            .copied()
            .unwrap_or(super::super::satellites::SaturationSuccessorDataId::NONE)
    }

    fn role_process_chain_contains(
        ctx: &CalculationAlgorithmContextBase,
        mut linker: super::super::satellites::RoleSaturationProcessLinkerId,
        role: RoleId,
    ) -> bool {
        while linker.is_some() {
            let linker_ref = ctx.process_context().role_sat_proc_linker(linker);
            if linker_ref.get_role() == role {
                return true;
            }
            linker = linker_ref.get_next();
        }
        false
    }

    fn role_process_chain_role_count(
        ctx: &CalculationAlgorithmContextBase,
        mut linker: super::super::satellites::RoleSaturationProcessLinkerId,
        role: RoleId,
    ) -> usize {
        let mut count = 0;
        while linker.is_some() {
            let linker_ref = ctx.process_context().role_sat_proc_linker(linker);
            if linker_ref.get_role() == role {
                count += 1;
            }
            linker = linker_ref.get_next();
        }
        count
    }

    fn concept_process_chain_descriptor_count(
        ctx: &CalculationAlgorithmContextBase,
        mut linker: super::super::satellites::ConceptSaturationProcessLinkerId,
        descriptor: ConceptSaturationDescriptorId,
    ) -> usize {
        let mut count = 0;
        while linker.is_some() {
            let linker_ref = ctx.process_context().con_sat_proc_linker(linker);
            if linker_ref.get_concept_saturation_descriptor() == descriptor {
                count += 1;
            }
            linker = linker_ref.get_next();
        }
        count
    }

    fn make_sat_node_with_individual(
        ctx: &mut CalculationAlgorithmContextBase,
        individual_id: Cint64,
    ) -> SatNodeId {
        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
        ctx.process_context_mut()
            .sat_node_mut(node)
            .set_individual_id(individual_id);
        node
    }

    #[test]
    fn s07_process_next_successor_extensions_missing_queue_returns_false() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        assert!(!algo.process_next_successor_extensions(&mut ctx));
        assert!(ctx
            .saturation_sucessor_extension_individual_node_processing_queue(false)
            .is_none());
    }

    #[test]
    fn s07_process_next_successor_extensions_clears_unprocessed_node() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(71));
        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(true);
        ctx.process_context_mut()
            .sat_succ_ext_ind_node_proc_queue_mut(queue)
            .insert_process_individual(node, 71);

        assert!(!algo.process_next_successor_extensions(&mut ctx));
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_empty());
    }

    #[test]
    fn s07_process_next_successor_extensions_skips_separated_node() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(73));
        ctx.process_context_mut()
            .sat_node_mut(node)
            .set_separated(true);
        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(true);
        ctx.process_context_mut()
            .sat_succ_ext_ind_node_proc_queue_mut(queue)
            .insert_process_individual(node, 73);
        algo.conf_all_concepts_extension_processing = true;
        algo.conf_functional_concepts_extension_processing = true;

        assert!(!algo.process_next_successor_extensions(&mut ctx));
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_empty());
    }

    #[test]
    fn s07_add_successor_extensions_all_concept_adds_all_operands() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 7991);
        let operand_a = make_concept(&mut ctx, CCTOP, RoleId::NONE, 0);
        let operand_b = make_concept(&mut ctx, CCTOP, RoleId::NONE, 0);
        set_concept_tag(&mut ctx, operand_a, 7993);
        set_concept_tag(&mut ctx, operand_b, 7995);
        let concept = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCALL)
                .set_role(role)
                .add_operand_linker(operand_a, false)
                .add_operand_linker(operand_b, true)
                .set_operand_count(2);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let mut source = make_sat_node_with_individual(&mut ctx, 7997);
        let succ = make_sat_node_with_individual(&mut ctx, 7999);
        let all_ext = ctx
            .process_context_mut()
            .sat_node_all_concepts_extension_data(source, true);
        let linked = ctx
            .process_context_mut()
            .sat_all_linked_successor_individual_concepts_extension_data(all_ext, succ, true);
        let role_ext = ctx
            .process_context_mut()
            .sat_role_successor_all_concept_extension_data(linked, role, true);

        assert!(algo.add_successor_extensions_all_concept(
            &mut source,
            concept,
            false,
            role_ext,
            &mut ctx,
        ));
        ctx.process_context_mut()
            .sat_successor_all_concept_ext_data_mut(role_ext)
            .clear_updated_flags();
        assert!(!algo.add_successor_extensions_all_concept(
            &mut source,
            concept,
            false,
            role_ext,
            &mut ctx,
        ));

        let map = ctx
            .process_context()
            .sat_successor_all_concept_ext_data(role_ext)
            .get_successor_concept_extension_map();
        let map_ref = ctx
            .process_context()
            .sat_successor_concept_extension_map(map)
            .get_successor_concept_extension_map();
        assert!(map_ref.get(&7993).unwrap().positive);
        assert!(!map_ref.get(&7993).unwrap().negative);
        assert!(!map_ref.get(&7995).unwrap().positive);
        assert!(map_ref.get(&7995).unwrap().negative);
    }

    #[test]
    fn s07_add_successor_extensions_all_concept_negated_some_flips_operands() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 8001);
        let operand = make_concept(&mut ctx, CCTOP, RoleId::NONE, 0);
        set_concept_tag(&mut ctx, operand, 8003);
        let concept = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCSOME)
                .set_role(role)
                .add_operand_linker(operand, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let mut source = make_sat_node_with_individual(&mut ctx, 8005);
        let succ = make_sat_node_with_individual(&mut ctx, 8007);
        let all_ext = ctx
            .process_context_mut()
            .sat_node_all_concepts_extension_data(source, true);
        let linked = ctx
            .process_context_mut()
            .sat_all_linked_successor_individual_concepts_extension_data(all_ext, succ, true);
        let role_ext = ctx
            .process_context_mut()
            .sat_role_successor_all_concept_extension_data(linked, role, true);

        assert!(algo.add_successor_extensions_all_concept(
            &mut source,
            concept,
            true,
            role_ext,
            &mut ctx,
        ));

        let map = ctx
            .process_context()
            .sat_successor_all_concept_ext_data(role_ext)
            .get_successor_concept_extension_map();
        let map_ref = ctx
            .process_context()
            .sat_successor_concept_extension_map(map)
            .get_successor_concept_extension_map();
        assert!(!map_ref.get(&8003).unwrap().positive);
        assert!(map_ref.get(&8003).unwrap().negative);
    }

    #[test]
    fn s07_all_successor_extension_data_promotes_only_role_to_hash() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role_a = make_role(&mut ctx, 8011);
        let role_b = make_role(&mut ctx, 8013);
        let source = make_sat_node_with_individual(&mut ctx, 8015);
        let succ = make_sat_node_with_individual(&mut ctx, 8017);
        let all_ext = ctx
            .process_context_mut()
            .sat_node_all_concepts_extension_data(source, true);
        let linked = ctx
            .process_context_mut()
            .sat_all_linked_successor_individual_concepts_extension_data(all_ext, succ, true);

        let role_a_ext = ctx
            .process_context_mut()
            .sat_role_successor_all_concept_extension_data(linked, role_a, true);
        assert!(role_a_ext.is_some());
        assert_eq!(
            ctx.process_context()
                .sat_linked_succ_indi_all_concept_ext_data(linked)
                .only_role,
            role_a
        );

        let role_b_ext = ctx
            .process_context_mut()
            .sat_role_successor_all_concept_extension_data(linked, role_b, true);
        assert!(role_b_ext.is_some());
        assert_ne!(role_a_ext, role_b_ext);

        let linked_ref = ctx
            .process_context()
            .sat_linked_succ_indi_all_concept_ext_data(linked);
        assert!(linked_ref.only_role.is_none());
        assert_eq!(
            linked_ref.role_concept_extension_hash.get(&role_a).copied(),
            Some(role_a_ext)
        );
        assert_eq!(
            linked_ref.role_concept_extension_hash.get(&role_b).copied(),
            Some(role_b_ext)
        );
        assert_eq!(
            ctx.process_context_mut()
                .sat_role_successor_all_concept_extension_data(linked, role_a, false),
            role_a_ext
        );
        assert_eq!(
            ctx.process_context_mut()
                .sat_role_successor_all_concept_extension_data(linked, role_b, false),
            role_b_ext
        );
    }

    #[test]
    fn s07_process_successor_all_initializes_clears_flags_and_fans_out() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut source = make_sat_node_with_individual(&mut ctx, 8001);
        let dep = make_sat_node_with_individual(&mut ctx, 8003);
        ctx.process_context_mut()
            .sat_node_mut(source)
            .add_copy_depending_individual_node_linker(NegLink {
                target: dep,
                negated: false,
            });

        let succ_ext = ctx
            .process_context_mut()
            .sat_node_ext_successor_extension_data(source, true);
        let all_ext = ctx
            .process_context_mut()
            .sat_successor_extension_all_concepts_extension_data(succ_ext, true);
        ctx.process_context_mut()
            .sat_indi_node_succ_ext_data_mut(succ_ext)
            .set_extension_processing_queued(true);
        ctx.process_context_mut()
            .sat_indi_node_all_concept_ext_data_mut(all_ext)
            .set_extension_processing_queued(true);

        assert!(!algo.process_successor_all_concepts_extensions(&mut source, &mut ctx));

        assert_eq!(algo.all_succ_ext_initialized_count, 1);
        assert!(ctx
            .process_context()
            .sat_indi_node_all_concept_ext_data(all_ext)
            .is_successor_extension_initialized());
        assert!(!ctx
            .process_context()
            .sat_indi_node_succ_ext_data(succ_ext)
            .is_extension_processing_queued());
        assert!(!ctx
            .process_context()
            .sat_indi_node_all_concept_ext_data(all_ext)
            .is_extension_processing_queued());

        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(dep, 8003));
    }

    #[test]
    fn s07_process_successor_all_drains_role_process_linkers() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role_a = make_role(&mut ctx, 8005);
        let role_b = make_role(&mut ctx, 8007);
        let mut source = make_sat_node_with_individual(&mut ctx, 8009);
        let succ_ext = ctx
            .process_context_mut()
            .sat_node_ext_successor_extension_data(source, true);
        let all_ext = ctx
            .process_context_mut()
            .sat_successor_extension_all_concepts_extension_data(succ_ext, true);

        let mut tail = RoleSaturationProcessLinker::new();
        tail.init_role_process_linker(role_b);
        let tail = ctx.process_context_mut().alloc_role_sat_proc_linker(tail);
        let mut head = RoleSaturationProcessLinker::new();
        head.init_role_process_linker(role_a).set_next(tail);
        let head = ctx.process_context_mut().alloc_role_sat_proc_linker(head);
        {
            let all_data = ctx
                .process_context_mut()
                .sat_indi_node_all_concept_ext_data_mut(all_ext);
            all_data
                .set_successor_extension_initialized(true)
                .set_extension_processing_queued(true);
            all_data.role_process_linker = head;
        }
        ctx.process_context_mut()
            .sat_indi_node_succ_ext_data_mut(succ_ext)
            .set_extension_processing_queued(true);

        assert!(!algo.process_successor_all_concepts_extensions(&mut source, &mut ctx));

        assert!(ctx
            .process_context()
            .sat_indi_node_all_concept_ext_data(all_ext)
            .get_role_process_linker()
            .is_none());
        assert!(ctx
            .process_context()
            .role_sat_proc_linker(head)
            .get_next()
            .is_none());
        assert!(ctx
            .process_context()
            .role_sat_proc_linker(tail)
            .get_next()
            .is_none());
        let released: Vec<Cint64> = ctx
            .processing_data_box()
            .remaining_role_saturation_process_linker()
            .iter()
            .map(|linker| linker.raw)
            .collect();
        assert!(released.contains(&head.raw));
        assert!(released.contains(&tail.raw));
        assert!(!ctx
            .process_context()
            .sat_indi_node_succ_ext_data(succ_ext)
            .is_extension_processing_queued());
        assert!(!ctx
            .process_context()
            .sat_indi_node_all_concept_ext_data(all_ext)
            .is_extension_processing_queued());
    }

    #[test]
    fn s07_process_successor_functional_initializes_and_clears_successor_queue() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut source = make_sat_node_with_individual(&mut ctx, 8011);
        let succ_ext = ctx
            .process_context_mut()
            .sat_node_ext_successor_extension_data(source, true);
        let functional_ext = ctx
            .process_context_mut()
            .sat_successor_extension_functional_concepts_extension_data(succ_ext, true);
        ctx.process_context_mut()
            .sat_indi_node_succ_ext_data_mut(succ_ext)
            .set_extension_processing_queued(true);

        assert!(!algo.process_successor_functional_concepts_extensions(&mut source, &mut ctx));

        assert!(ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(functional_ext)
            .is_successor_extension_initialized());
        assert!(!ctx
            .process_context()
            .sat_indi_node_succ_ext_data(succ_ext)
            .is_extension_processing_queued());
    }

    #[test]
    fn s07_process_successor_functional_drains_role_linkers() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role_a = make_role(&mut ctx, 8013);
        let role_b = make_role(&mut ctx, 8015);
        let mut source = make_sat_node_with_individual(&mut ctx, 8017);
        let succ_ext = ctx
            .process_context_mut()
            .sat_node_ext_successor_extension_data(source, true);
        let functional_ext = ctx
            .process_context_mut()
            .sat_successor_extension_functional_concepts_extension_data(succ_ext, true);

        let mut succ_linker = RoleSaturationProcessLinker::new();
        succ_linker.init_role_process_linker(role_a);
        let succ_linker = ctx
            .process_context_mut()
            .alloc_role_sat_proc_linker(succ_linker);
        let mut pred_linker = RoleSaturationProcessLinker::new();
        pred_linker.init_role_process_linker(role_b);
        let pred_linker = ctx
            .process_context_mut()
            .alloc_role_sat_proc_linker(pred_linker);
        {
            let functional_data = ctx
                .process_context_mut()
                .sat_indi_node_functional_concept_ext_data_mut(functional_ext);
            functional_data.set_successor_extension_initialized(true);
            functional_data.linked_successor_added_role_process_linker = succ_linker;
            functional_data.linked_predecessor_added_role_process_linker = pred_linker;
        }

        assert!(!algo.process_successor_functional_concepts_extensions(&mut source, &mut ctx));

        let functional_data = ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(functional_ext);
        assert!(functional_data
            .linked_successor_added_role_process_linker
            .is_none());
        assert!(functional_data
            .linked_predecessor_added_role_process_linker
            .is_none());
        assert!(ctx
            .process_context()
            .role_sat_proc_linker(succ_linker)
            .get_next()
            .is_none());
        assert!(ctx
            .process_context()
            .role_sat_proc_linker(pred_linker)
            .get_next()
            .is_none());
        let released: Vec<Cint64> = ctx
            .processing_data_box()
            .remaining_role_saturation_process_linker()
            .iter()
            .map(|linker| linker.raw)
            .collect();
        assert!(released.contains(&succ_linker.raw));
        assert!(released.contains(&pred_linker.raw));
    }

    #[test]
    fn s07_process_successor_functional_drains_qualified_atmost_and_fans_out() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        algo.conf_functional_concepts_extension_processing = true;
        let role = make_role(&mut ctx, 8019);
        let concept = make_concept(&mut ctx, CCATLEAST, role, 1);
        let descriptor = make_descriptor(&mut ctx, concept, false);
        let mut source = make_sat_node_with_individual(&mut ctx, 8021);
        let dep = make_sat_node_with_individual(&mut ctx, 8023);
        ctx.process_context_mut()
            .sat_node_mut(source)
            .add_copy_depending_individual_node_linker(NegLink {
                target: dep,
                negated: false,
            });
        let succ_ext = ctx
            .process_context_mut()
            .sat_node_ext_successor_extension_data(source, true);
        let functional_ext = ctx
            .process_context_mut()
            .sat_successor_extension_functional_concepts_extension_data(succ_ext, true);
        let mut qual_linker = ConceptSaturationProcessLinker::new();
        qual_linker.init_concept_saturation_process_linker(descriptor);
        let qual_linker = ctx
            .process_context_mut()
            .alloc_con_sat_proc_linker(qual_linker);
        {
            let functional_data = ctx
                .process_context_mut()
                .sat_indi_node_functional_concept_ext_data_mut(functional_ext);
            functional_data.set_successor_extension_initialized(true);
            functional_data.qual_func_atmost_con_process_linker = qual_linker;
        }

        assert!(!algo.process_successor_functional_concepts_extensions(&mut source, &mut ctx));

        assert!(ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(functional_ext)
            .qual_func_atmost_con_process_linker
            .is_none());
        assert!(ctx
            .process_context()
            .con_sat_proc_linker(qual_linker)
            .get_next()
            .is_none());
        let released: Vec<Cint64> = ctx
            .processing_data_box()
            .remaining_concept_saturation_process_linker()
            .iter()
            .map(|linker| linker.raw)
            .collect();
        assert!(released.contains(&qual_linker.raw));

        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(dep, 8023));
        let dep_succ_ext = ctx
            .process_context()
            .indi_sat_node_ext_data(ctx.process_context().sat_node(dep).indi_extension_data)
            .get_successor_extension_data();
        let dep_functional_ext = ctx
            .process_context()
            .sat_indi_node_succ_ext_data(dep_succ_ext)
            .get_functional_concepts_extension_data();
        let dep_head = ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(dep_functional_ext)
            .qual_func_atmost_con_process_linker;
        assert_eq!(
            concept_process_chain_descriptor_count(&ctx, dep_head, descriptor),
            1
        );
    }

    #[test]
    fn s07_add_successor_extension_to_processing_queue_creates_all_face_and_queues_once() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(81));
        ctx.process_context_mut()
            .sat_node_mut(node)
            .set_individual_id(81);

        assert!(algo.add_successor_extension_to_processing_queue(&mut node, &mut ctx));
        let node_ext = ctx.process_context().sat_node(node).indi_extension_data;
        assert!(node_ext.is_some());
        let succ_ext = ctx
            .process_context()
            .indi_sat_node_ext_data(node_ext)
            .get_successor_extension_data();
        assert!(succ_ext.is_some());
        assert!(ctx
            .process_context()
            .sat_indi_node_succ_ext_data(succ_ext)
            .is_extension_processing_queued());
        let all_ext = ctx
            .process_context()
            .sat_indi_node_succ_ext_data(succ_ext)
            .get_all_concepts_extension_data();
        assert!(all_ext.is_some());
        assert_eq!(
            ctx.process_context()
                .sat_indi_node_all_concept_ext_data(all_ext)
                .indi_process_node,
            node
        );
        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(node, 81));

        assert!(!algo.add_successor_extension_to_processing_queue(&mut node, &mut ctx));
        assert_eq!(
            ctx.process_context()
                .sat_succ_ext_ind_node_proc_queue(queue)
                .get_queued_individual_count(),
            1
        );
    }

    #[test]
    fn s07_add_new_linked_extension_processing_role_queues_all_extension_from_backward_reapply() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        algo.conf_concepts_extension_processing = true;
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 3011);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(3013));
        ctx.process_context_mut()
            .sat_node_mut(node)
            .set_individual_id(3013);
        let succ_ext = ctx
            .process_context_mut()
            .sat_node_ext_successor_extension_data(node, true);
        let all_ext = ctx
            .process_context_mut()
            .sat_successor_extension_all_concepts_extension_data(succ_ext, true);
        ctx.process_context_mut()
            .sat_indi_node_all_concept_ext_data_mut(all_ext)
            .set_successor_extension_initialized(true);
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data =
            ctx.process_context_mut()
                .linked_role_successor_data(linked_hash, role, true);
        let backward_hash = ctx
            .process_context_mut()
            .sat_node_role_backward_propagation_hash(node, true);
        let reapply = ctx
            .process_context_mut()
            .alloc_backward_sat_prop_reapply_desc({
                let mut descriptor = BackwardSaturationPropagationReapplyDescriptor::new();
                descriptor.init_backward_propagation_reapply_descriptor(
                    ConceptSaturationDescriptorId::NONE,
                );
                descriptor
            });
        ctx.process_context_mut()
            .role_backward_sat_prop_hash_mut(backward_hash)
            .get_role_backward_propagation_data_hash_mut()
            .entry(role)
            .or_insert_with(RoleBackwardSaturationPropagationHashData::new)
            .reapply_linker = reapply;

        algo.add_new_linked_extension_processing_role(role, &mut node, true, false, &mut ctx);

        let succ = ctx.process_context().linked_role_sat_succ_data(succ_data);
        assert!(succ.role_all_concepts_queuing_required);
        assert!(succ.role_all_concepts_processing_queued);
        let all_head = ctx
            .process_context()
            .sat_indi_node_all_concept_ext_data(all_ext)
            .get_role_process_linker();
        assert!(role_process_chain_contains(&ctx, all_head, role));
        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(node, 3013));
    }

    #[test]
    fn s07_add_new_linked_extension_processing_role_queues_functional_extension() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        algo.conf_concepts_extension_processing = true;
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 3021);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(3023));
        ctx.process_context_mut()
            .sat_node_mut(node)
            .set_individual_id(3023);
        let succ_ext = ctx
            .process_context_mut()
            .sat_node_ext_successor_extension_data(node, true);
        let functional_ext = ctx
            .process_context_mut()
            .sat_successor_extension_functional_concepts_extension_data(succ_ext, true);
        ctx.process_context_mut()
            .sat_indi_node_functional_concept_ext_data_mut(functional_ext)
            .set_successor_extension_initialized(true);
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data =
            ctx.process_context_mut()
                .linked_role_successor_data(linked_hash, role, true);
        ctx.process_context_mut()
            .linked_role_sat_succ_data_mut(succ_data)
            .role_functional_concepts_queuing_required = true;

        algo.add_new_linked_extension_processing_role(role, &mut node, false, true, &mut ctx);

        assert!(
            ctx.process_context()
                .linked_role_sat_succ_data(succ_data)
                .role_functional_concepts_processing_queued
        );
        let functional_data = ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(functional_ext);
        assert!(role_process_chain_contains(
            &ctx,
            functional_data.linked_successor_added_role_process_linker,
            role
        ));
        assert!(role_process_chain_contains(
            &ctx,
            functional_data.linked_predecessor_added_role_process_linker,
            role
        ));
        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(node, 3023));
    }

    #[test]
    fn s07_all_process_role_extension_fans_out_to_initialized_dependents() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 3031);
        let mut source = make_sat_node_with_individual(&mut ctx, 3033);
        let initialized_dep = make_sat_node_with_individual(&mut ctx, 3035);
        let uninitialized_dep = make_sat_node_with_individual(&mut ctx, 3037);
        ctx.process_context_mut()
            .sat_node_mut(source)
            .add_copy_depending_individual_node_linker(NegLink {
                target: initialized_dep,
                negated: false,
            })
            .add_copy_depending_individual_node_linker(NegLink {
                target: uninitialized_dep,
                negated: false,
            });
        let initialized_all_ext = {
            let succ_ext = ctx
                .process_context_mut()
                .sat_node_ext_successor_extension_data(initialized_dep, true);
            let all_ext = ctx
                .process_context_mut()
                .sat_successor_extension_all_concepts_extension_data(succ_ext, true);
            ctx.process_context_mut()
                .sat_indi_node_all_concept_ext_data_mut(all_ext)
                .set_successor_extension_initialized(true);
            all_ext
        };

        algo.add_all_process_role_extension_to_dependent_individuals(&mut source, role, &mut ctx);

        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(initialized_dep, 3035));
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(uninitialized_dep, 3037));
        let head = ctx
            .process_context()
            .sat_indi_node_all_concept_ext_data(initialized_all_ext)
            .get_role_process_linker();
        assert!(role_process_chain_contains(&ctx, head, role));

        algo.add_all_process_role_extension_to_dependent_individuals(&mut source, role, &mut ctx);
        let head = ctx
            .process_context()
            .sat_indi_node_all_concept_ext_data(initialized_all_ext)
            .get_role_process_linker();
        assert_eq!(role_process_chain_role_count(&ctx, head, role), 1);
    }

    #[test]
    fn s07_functional_linked_successor_fanout_queues_all_and_registers_initialized() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 3041);
        let mut source = make_sat_node_with_individual(&mut ctx, 3043);
        let initialized_dep = make_sat_node_with_individual(&mut ctx, 3045);
        let uninitialized_dep = make_sat_node_with_individual(&mut ctx, 3047);
        ctx.process_context_mut()
            .sat_node_mut(source)
            .add_copy_depending_individual_node_linker(NegLink {
                target: initialized_dep,
                negated: false,
            })
            .add_copy_depending_individual_node_linker(NegLink {
                target: uninitialized_dep,
                negated: false,
            });
        let initialized_functional_ext = {
            let succ_ext = ctx
                .process_context_mut()
                .sat_node_ext_successor_extension_data(initialized_dep, true);
            let functional_ext = ctx
                .process_context_mut()
                .sat_successor_extension_functional_concepts_extension_data(succ_ext, true);
            ctx.process_context_mut()
                .sat_indi_node_functional_concept_ext_data_mut(functional_ext)
                .set_successor_extension_initialized(true);
            functional_ext
        };

        algo.add_functional_process_role_extension_linked_successor_added_to_dependent_individuals(
            &mut source,
            role,
            &mut ctx,
        );

        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(initialized_dep, 3045));
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(uninitialized_dep, 3047));
        let head = ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(initialized_functional_ext)
            .linked_successor_added_role_process_linker;
        assert!(role_process_chain_contains(&ctx, head, role));
    }

    #[test]
    fn s07_functional_linked_predecessor_fanout_queues_only_initialized_dependents() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 3051);
        let mut source = make_sat_node_with_individual(&mut ctx, 3053);
        let initialized_dep = make_sat_node_with_individual(&mut ctx, 3055);
        let uninitialized_dep = make_sat_node_with_individual(&mut ctx, 3057);
        ctx.process_context_mut()
            .sat_node_mut(source)
            .add_copy_depending_individual_node_linker(NegLink {
                target: initialized_dep,
                negated: false,
            })
            .add_copy_depending_individual_node_linker(NegLink {
                target: uninitialized_dep,
                negated: false,
            });
        let initialized_functional_ext = {
            let succ_ext = ctx
                .process_context_mut()
                .sat_node_ext_successor_extension_data(initialized_dep, true);
            let functional_ext = ctx
                .process_context_mut()
                .sat_successor_extension_functional_concepts_extension_data(succ_ext, true);
            ctx.process_context_mut()
                .sat_indi_node_functional_concept_ext_data_mut(functional_ext)
                .set_successor_extension_initialized(true);
            functional_ext
        };

        algo.add_functional_process_role_extension_linked_predecessor_added_to_dependent_individuals(
            &mut source,
            role,
            &mut ctx,
        );

        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(initialized_dep, 3055));
        assert!(!ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(uninitialized_dep, 3057));
        let head = ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(initialized_functional_ext)
            .linked_predecessor_added_role_process_linker;
        assert!(role_process_chain_contains(&ctx, head, role));
    }

    #[test]
    fn s07_functionality_added_fanout_queues_and_registers_without_initialized_guard() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 3061);
        let mut source = make_sat_node_with_individual(&mut ctx, 3063);
        let dep = make_sat_node_with_individual(&mut ctx, 3065);
        ctx.process_context_mut()
            .sat_node_mut(source)
            .add_copy_depending_individual_node_linker(NegLink {
                target: dep,
                negated: false,
            });

        algo.add_functional_process_role_extension_functionality_added_to_dependent_individuals(
            &mut source,
            role,
            &mut ctx,
        );

        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(dep, 3065));
        let node_ext = ctx.process_context().sat_node(dep).indi_extension_data;
        let succ_ext = ctx
            .process_context()
            .indi_sat_node_ext_data(node_ext)
            .get_successor_extension_data();
        let functional_ext = ctx
            .process_context_mut()
            .sat_successor_extension_functional_concepts_extension_data(succ_ext, false);
        let head = ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(functional_ext)
            .functionality_added_role_process_linker;
        assert!(role_process_chain_contains(&ctx, head, role));
    }

    #[test]
    fn s07_all_concept_extension_processing_role_queues_flags_and_deduplicates() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 3067);
        let mut node = make_sat_node_with_individual(&mut ctx, 3069);
        let mut back_prop_data = RoleBackwardSaturationPropagationHashData::new();

        algo.add_all_concept_extension_processing_role(
            role,
            &mut back_prop_data,
            &mut node,
            &mut ctx,
        );
        assert!(!back_prop_data.role_all_concepts_processing_queued);
        assert!(ctx
            .saturation_sucessor_extension_individual_node_processing_queue(false)
            .is_none());
        assert!(ctx
            .process_context()
            .sat_node(node)
            .indi_extension_data
            .is_none());

        let succ_ext = ctx
            .process_context_mut()
            .sat_node_ext_successor_extension_data(node, true);
        let all_ext = ctx
            .process_context_mut()
            .sat_successor_extension_all_concepts_extension_data(succ_ext, true);
        ctx.process_context_mut()
            .sat_indi_node_all_concept_ext_data_mut(all_ext)
            .set_successor_extension_initialized(true);

        algo.conf_all_concepts_extension_processing = true;
        algo.add_all_concept_extension_processing_role(
            role,
            &mut back_prop_data,
            &mut node,
            &mut ctx,
        );

        assert!(back_prop_data.role_all_concepts_processing_queued);
        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(node, 3069));
        let head = ctx
            .process_context()
            .sat_indi_node_all_concept_ext_data(all_ext)
            .get_role_process_linker();
        assert_eq!(role_process_chain_role_count(&ctx, head, role), 1);

        back_prop_data.role_all_concepts_processing_queued = false;
        algo.add_all_concept_extension_processing_role(
            role,
            &mut back_prop_data,
            &mut node,
            &mut ctx,
        );
        let head = ctx
            .process_context()
            .sat_indi_node_all_concept_ext_data(all_ext)
            .get_role_process_linker();
        assert_eq!(role_process_chain_role_count(&ctx, head, role), 1);
    }

    #[test]
    fn s07_functional_concept_extension_processing_role_queues_and_deduplicates() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 3071);
        let mut node = make_sat_node_with_individual(&mut ctx, 3073);

        algo.add_functional_concept_extension_processing_role(role, &mut node, &mut ctx);
        assert!(ctx
            .saturation_sucessor_extension_individual_node_processing_queue(false)
            .is_none());
        assert!(ctx
            .process_context()
            .sat_node(node)
            .indi_extension_data
            .is_none());

        algo.conf_functional_concepts_extension_processing = true;
        algo.add_functional_concept_extension_processing_role(role, &mut node, &mut ctx);

        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(node, 3073));
        let node_ext = ctx.process_context().sat_node(node).indi_extension_data;
        let succ_ext = ctx
            .process_context()
            .indi_sat_node_ext_data(node_ext)
            .get_successor_extension_data();
        let functional_ext = ctx
            .process_context_mut()
            .sat_successor_extension_functional_concepts_extension_data(succ_ext, false);
        let head = ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(functional_ext)
            .functionality_added_role_process_linker;
        assert!(role_process_chain_contains(&ctx, head, role));

        algo.add_functional_concept_extension_processing_role(role, &mut node, &mut ctx);
        let head = ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(functional_ext)
            .functionality_added_role_process_linker;
        assert_eq!(role_process_chain_role_count(&ctx, head, role), 1);
    }

    #[test]
    fn s07_qualified_functional_atmost_extension_processing_queues_and_deduplicates() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 3081);
        let concept = make_concept(&mut ctx, CCATLEAST, role, 1);
        let descriptor = make_descriptor(&mut ctx, concept, false);
        let mut node = make_sat_node_with_individual(&mut ctx, 3083);

        algo.add_qualified_functional_atmost_concept_extension_processing(
            descriptor, &mut node, &mut ctx,
        );
        assert!(ctx
            .saturation_sucessor_extension_individual_node_processing_queue(false)
            .is_none());
        assert!(ctx
            .process_context()
            .sat_node(node)
            .indi_extension_data
            .is_none());

        algo.conf_functional_concepts_extension_processing = true;
        algo.add_qualified_functional_atmost_concept_extension_processing(
            descriptor, &mut node, &mut ctx,
        );

        let queue = ctx.saturation_sucessor_extension_individual_node_processing_queue(false);
        assert!(queue.is_some());
        assert!(ctx
            .process_context()
            .sat_succ_ext_ind_node_proc_queue(queue)
            .is_individual_queued(node, 3083));
        let node_ext = ctx.process_context().sat_node(node).indi_extension_data;
        let succ_ext = ctx
            .process_context()
            .indi_sat_node_ext_data(node_ext)
            .get_successor_extension_data();
        let functional_ext = ctx
            .process_context_mut()
            .sat_successor_extension_functional_concepts_extension_data(succ_ext, false);
        let head = ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(functional_ext)
            .qual_func_atmost_con_process_linker;
        assert_eq!(
            concept_process_chain_descriptor_count(&ctx, head, descriptor),
            1
        );

        algo.add_qualified_functional_atmost_concept_extension_processing(
            descriptor, &mut node, &mut ctx,
        );
        let head = ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(functional_ext)
            .qual_func_atmost_con_process_linker;
        assert_eq!(
            concept_process_chain_descriptor_count(&ctx, head, descriptor),
            1
        );
    }

    #[test]
    fn s07_add_linked_successor_node_for_role_assertion_adds_positive_super_roles() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 1001);
        let positive_super = make_role(&mut ctx, 1003);
        let negated_super = make_role(&mut ctx, 1005);
        ctx.ontology_arenas_mut()
            .role_mut(role)
            .add_indirect_super_role_linker(NegLink {
                target: positive_super,
                negated: false,
            })
            .add_indirect_super_role_linker(NegLink {
                target: negated_super,
                negated: true,
            });
        let mut source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(1501));
        let dest = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(1503));
        let hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(source, true);

        algo.add_linked_successor_node_for_role_assertion(
            dest,
            role,
            false,
            hash,
            &mut source,
            &mut ctx,
        );

        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                positive_super,
                dest,
                Some(role),
                1,
            ));
        assert!(!ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                negated_super,
                dest,
                Some(role),
                1,
            ));
        let role_data =
            ctx.process_context_mut()
                .linked_role_successor_data(hash, positive_super, false);
        let succ_data = ctx
            .process_context()
            .linked_role_successor_node_data(role_data, dest);
        assert!(!ctx.process_context().sat_succ_data(succ_data).extension);
    }

    #[test]
    fn s07_add_linked_successor_node_for_role_assertion_inversion_selects_negated_supers() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 1011);
        let positive_super = make_role(&mut ctx, 1013);
        let negated_super = make_role(&mut ctx, 1015);
        ctx.ontology_arenas_mut()
            .role_mut(role)
            .add_indirect_super_role_linker(NegLink {
                target: positive_super,
                negated: false,
            })
            .add_indirect_super_role_linker(NegLink {
                target: negated_super,
                negated: true,
            });
        let mut source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(1511));
        let dest = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(1513));
        let hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(source, true);

        algo.add_linked_successor_node_for_role_assertion(
            dest,
            role,
            true,
            hash,
            &mut source,
            &mut ctx,
        );

        assert!(!ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                positive_super,
                dest,
                Some(role),
                1,
            ));
        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                negated_super,
                dest,
                Some(role),
                1,
            ));
    }

    #[test]
    fn s07_add_linked_successor_node_for_concept_uses_existential_reference_first() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 2011);
        let positive_super = make_role(&mut ctx, 2013);
        let negated_super = make_role(&mut ctx, 2015);
        ctx.ontology_arenas_mut()
            .role_mut(role)
            .add_indirect_super_role_linker(NegLink {
                target: positive_super,
                negated: false,
            })
            .add_indirect_super_role_linker(NegLink {
                target: negated_super,
                negated: true,
            });
        let concept = make_concept(&mut ctx, CCSOME, role, 0);
        let descriptor = make_descriptor(&mut ctx, concept, false);
        let mut source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2101));
        let direct_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2103));
        set_existential_reference_node(&mut ctx, concept, direct_node);
        let hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(source, true);

        algo.add_linked_successor_node_for_concept(descriptor, hash, &mut source, &mut ctx);

        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                positive_super,
                direct_node,
                Some(role),
                1,
            ));
        assert!(!ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                negated_super,
                direct_node,
                Some(role),
                1,
            ));
    }

    #[test]
    fn s07_add_linked_successor_node_for_concept_uses_operand_reference_when_no_special_node() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 2021);
        let positive_super = make_role(&mut ctx, 2023);
        ctx.ontology_arenas_mut()
            .role_mut(role)
            .add_indirect_super_role_linker(NegLink {
                target: positive_super,
                negated: false,
            });
        let concept = make_concept(&mut ctx, CCATLEAST, role, 2);
        let operand = make_concept(&mut ctx, CCTOP, RoleId::NONE, 0);
        ctx.ontology_arenas_mut()
            .concept_mut(concept)
            .add_operand_linker(operand, true);
        let descriptor = make_descriptor(&mut ctx, concept, false);
        let mut source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2201));
        let operand_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2203));
        set_reference_node(&mut ctx, operand, true, operand_node);
        let hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(source, true);

        algo.add_linked_successor_node_for_concept(descriptor, hash, &mut source, &mut ctx);

        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                positive_super,
                operand_node,
                Some(role),
                2,
            ));
    }

    #[test]
    fn s07_add_linked_successor_node_for_concept_uses_top_only_without_operands() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 2031);
        let positive_super = make_role(&mut ctx, 2033);
        ctx.ontology_arenas_mut()
            .role_mut(role)
            .add_indirect_super_role_linker(NegLink {
                target: positive_super,
                negated: false,
            });
        let concept = make_concept(&mut ctx, CCSOME, role, 0);
        let descriptor = make_descriptor(&mut ctx, concept, false);
        let top_concept = make_concept(&mut ctx, CCTOP, RoleId::NONE, 0);
        ctx.processing_data_box_mut().ontology_top_concept = top_concept;
        let mut source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2301));
        let top_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2303));
        set_reference_node(&mut ctx, top_concept, false, top_node);
        let hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(source, true);

        algo.add_linked_successor_node_for_concept(descriptor, hash, &mut source, &mut ctx);

        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                positive_super,
                top_node,
                Some(role),
                1,
            ));

        let operand = make_concept(&mut ctx, CCTOP, RoleId::NONE, 0);
        ctx.ontology_arenas_mut()
            .concept_mut(concept)
            .add_operand_linker(operand, false);
        let mut source_with_operand = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2305));
        let hash_with_operand = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(source_with_operand, true);
        algo.add_linked_successor_node_for_concept(
            descriptor,
            hash_with_operand,
            &mut source_with_operand,
            &mut ctx,
        );
        let role_data = ctx.process_context_mut().linked_role_successor_data(
            hash_with_operand,
            positive_super,
            false,
        );
        assert_eq!(
            ctx.process_context()
                .linked_role_successor_node_data(role_data, top_node),
            super::super::satellites::SaturationSuccessorDataId::NONE
        );
    }

    #[test]
    fn s07_add_linked_successor_node_for_concept_adds_value_nominal_successor() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 2041);
        let positive_super = make_role(&mut ctx, 2043);
        ctx.ontology_arenas_mut()
            .role_mut(role)
            .add_indirect_super_role_linker(NegLink {
                target: positive_super,
                negated: false,
            });
        let concept = make_concept(&mut ctx, CCVALUE, role, 0);
        let nominal = ctx
            .ontology_arenas_mut()
            .alloc_individual(Individual::new(90210));
        ctx.ontology_arenas_mut()
            .concept_mut(concept)
            .set_nominal_individual(nominal);
        let descriptor = make_descriptor(&mut ctx, concept, false);
        let mut source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2401));
        let reference_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2403));
        set_existential_reference_node(&mut ctx, concept, reference_node);
        let hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(source, true);

        algo.add_linked_successor_node_for_concept(descriptor, hash, &mut source, &mut ctx);

        let succ_data = value_successor_data_for_nominal(&mut ctx, hash, positive_super, 90210);
        assert!(succ_data.is_some());
        let succ = ctx.process_context().sat_succ_data(succ_data);
        assert!(succ.value_nominal_connection);
        assert_eq!(succ.value_nominal_id, 90210);
        assert_eq!(succ.succ_indi_node, SatNodeId::NONE);
        assert_eq!(succ.succ_count, 1);
        assert_eq!(succ.active_count, 1);
        assert_eq!(
            succ.creation_role_linker,
            vec![NegLink {
                target: role,
                negated: false
            }]
        );
    }

    #[test]
    fn s07_collect_linked_successor_nodes_collects_concepts_and_sets_watermark() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 2051);
        let positive_super = make_role(&mut ctx, 2053);
        ctx.ontology_arenas_mut()
            .role_mut(role)
            .add_indirect_super_role_linker(NegLink {
                target: positive_super,
                negated: false,
            });
        let concept = make_concept(&mut ctx, CCSOME, role, 0);
        let descriptor = make_descriptor(&mut ctx, concept, false);
        let mut source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2501));
        let dest = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2503));
        set_existential_reference_node(&mut ctx, concept, dest);
        prepend_descriptor_to_label_set(&mut ctx, source, descriptor);

        algo.collect_linked_successor_nodes(&mut source, &mut ctx, INVALID);

        let hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(source, false);
        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                positive_super,
                dest,
                Some(role),
                1,
            ));
        assert_eq!(
            ctx.process_context()
                .linked_role_sat_succ_hash(hash)
                .get_last_examined_concept_descriptor(),
            descriptor
        );
        let succ_count_after_first = ctx.process_context().sat_succ_data_count();

        algo.collect_linked_successor_nodes(&mut source, &mut ctx, hash.raw);

        assert_eq!(
            ctx.process_context().sat_succ_data_count(),
            succ_count_after_first
        );
    }

    #[test]
    fn s07_collect_linked_successor_nodes_collects_only_new_role_assertions() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 2061);
        let positive_super = make_role(&mut ctx, 2063);
        ctx.ontology_arenas_mut()
            .role_mut(role)
            .add_indirect_super_role_linker(NegLink {
                target: positive_super,
                negated: false,
            });
        let mut source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2601));
        let first_dest = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2603));
        ctx.process_context_mut()
            .sat_node_ext_add_role_assertion(source, first_dest, role, false);

        algo.collect_linked_successor_nodes(&mut source, &mut ctx, INVALID);

        let hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(source, false);
        let first_head = ctx
            .process_context()
            .sat_node_ext_role_assertion_linker(source);
        assert_eq!(
            ctx.process_context()
                .linked_role_sat_succ_hash(hash)
                .get_last_examined_role_assertion_linker(),
            first_head.raw
        );
        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                positive_super,
                first_dest,
                Some(role),
                1,
            ));

        let second_dest = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(2605));
        ctx.process_context_mut()
            .sat_node_ext_add_role_assertion(source, second_dest, role, false);
        let second_head = ctx
            .process_context()
            .sat_node_ext_role_assertion_linker(source);

        algo.collect_linked_successor_nodes(&mut source, &mut ctx, hash.raw);

        assert_eq!(
            ctx.process_context()
                .linked_role_sat_succ_hash(hash)
                .get_last_examined_role_assertion_linker(),
            second_head.raw
        );
        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                positive_super,
                second_dest,
                Some(role),
                1,
            ));
        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                hash,
                positive_super,
                first_dest,
                Some(role),
                1,
            ));
    }
}
