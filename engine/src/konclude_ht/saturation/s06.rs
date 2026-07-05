//! `saturation::s06` — Successor ALL / FUNCTIONAL extension propagation
//! (saturation port unit #6 of 12; manifest `03-saturation-calc.md`, "PU-SAT-6").
//!
//! Faithful port of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`,
//! the **group F part 1** methods: the `update*ALL/FUNCTIONAL*` successor- and
//! predecessor-extension propagation routines plus the backward-propagation-link
//! installer. (The group-G cardinality-merging methods that physically interleave
//! in the same cpp span — `getInverseRole` 1175, `createAncestorSuccessorMergingExtension`
//! 1202, the `isLinkedIndividualSuccessorNodeMergingSubset` / `isSuccessorCreationRoleMergingSubset`
//! / `isIndividualNodeLabelMergingSubset` / `deactivateSubsetMergeableSuccessorLinks`
//! predicates 1335–1473 — belong to PU-SAT-8 and are NOT ported here.)
//!
//! Methods (cpp order, with the `CIndividualSaturationProcessNode*&` self-node and
//! the trailing `CCalculationAlgorithmContextBase*` elided):
//!   * `getSucessorExtensionData`                              [908–915]
//!   * `initializeSuccessorALLConceptsExtensions`             [919–941]
//!   * `updateSuccessorRoleALLConceptsExtensions(succData)`   [943–1014]
//!   * `installSuccessorPredecessorRoleFunctionalityConceptsExtension` [1018–1044]
//!   * `updateSuccessorRoleFUNCTIONALConceptsExtensions(role)`         [1047–1061]
//!   * `updateSuccessorRoleQualifiedFUNCTIONALConceptsExtensions(qual)` [1064–1075]
//!   * `updatePredecessorRoleFUNCTIONALConceptsExtensions(role)`        [1079–1103]
//!   * `updatePredecessorRoleFUNCTIONALConceptsExtensions(succData,link)` [1113–1143]
//!   * `updateSuccessorRoleFUNCTIONALConceptsExtensions(succData)`      [1514–1683]
//!   * `updateSuccessorRoleQualifiedFUNCTIONALConceptsExtensions(qual,succData)` [1690–1825]
//!   * `updateSuccessorRoleALLConceptsExtensions(role)`       [1831–1850]
//!   * `updateSuccessorALLConceptsExtensions`                 [1852–1966]
//!   * `installBackwardPropagationLink`                       [1974–2016]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each is a member of
//! `CCalculationTableauApproximationSaturationTaskHandleAlgorithm`, so it becomes
//! `&mut self` plus the threaded per-thread context. The saturation algorithm's
//! methods take the SHARED `CCalculationAlgorithmContextBase*` (header lines
//! 235–307), so the port threads `calc_alg_context: &mut CalculationAlgorithmContextBase`
//! — the same context type the completion layer uses. A `CIndividualSaturationProcessNode*&`
//! out/in-out reference becomes `&mut SatNodeId`; a plain `CIndividualSaturationProcessNode*`
//! value becomes `SatNodeId`; `CRole*` becomes `RoleId`.
//!
//! KONCLUDE-PORT-NOTE[overload]: C++ overloads (Rust cannot) are disambiguated by
//! a `_for_succ_data` suffix on the worker overload that takes the resolved
//! `CLinkedRoleSaturationSuccessorData*` (the short, role-keyed dispatcher keeps
//! the plain name and calls the worker). This mirrors the completion-layer
//! `_by_id` overload-split convention (PORT.md, W3 reconcile notes).
//!
//! Deferral landscape. This whole unit sits on top of the **successor-extension
//! satellite tower**, a Process-layer subsystem that is NOT yet ported (it has no
//! Rust struct anywhere in the tree — only marker references in `process::stubs`
//! and the manifests). Concretely, every body immediately dereferences one or more
//! of:
//!   * `CSaturationIndividualNodeSuccessorExtensionData` (`sat_node->getSuccessorExtensionData`)
//!     and its `...ALLConceptsExtensionData` / `...FUNCTIONALConceptsExtensionData` faces;
//!   * `CLinkedRoleSaturationSuccessorHash` / `CLinkedRoleSaturationSuccessorData` /
//!     `CSaturationSuccessorData` (the per-role linked-successor chains + node-data maps);
//!   * `CSaturationSuccessorExtensionData` / `CSaturationSuccessorALLConceptExtensionData` /
//!     `CSaturationSuccessorFUNCTIONALConceptExtensionData` / `CSaturationPredecessorFUNCTIONALConceptExtensionData`;
//!   * `CRoleBackwardSaturationPropagationHash` / `CRoleBackwardSaturationPropagationHashData` /
//!     `CBackwardSaturationPropagationLink` / `CBackwardSaturationPropagationReapplyDescriptor`;
//!   * `CSaturationIndividualNodeExtensionResolveData` / `CIndividualSaturationSuccessorLinkDataLinker` /
//!     `CSaturationSuccessorConceptExtensionMap`;
//!   * `CConceptSaturationDescriptor` / `CReapplyConceptSaturationLabelSet` / `CRoleSaturationProcessLinker`;
//! and on sibling methods owned by OTHER saturation units (PU-SAT-7/8/10/11):
//! `createAncestorSuccessorMergingExtension`, `deactivateSubsetMergeableSuccessorLinks`,
//! `collectResolveIndividualExtendableConceptMap`, `getResolvedIndividualNodeExtension`,
//! `getResolvedIndividualNodeExtensionSuccessor`, `addNewLinkedExtensionProcessingRole`,
//! `addConceptFilteredToIndividual`, `applyBackwardPropagationConcepts`,
//! `addSuccessorExtensionToProcessingQueue`, the `create*/release*` pool helpers,
//! and the status-flag/nominal/cardinality propagators (`updateIndirectAddingIndividualStatusFlags`,
//! `updateAddingSuccessorConnectedNominal`, `updateMaxCardinalityCandidates`).
//!
//! Following the porting convention (PORT.md W3 keystone precedent, mirrored by
//! `completion::u17`): each method below carries the faithful name + signature +
//! context threading, and a `// W6-DEFER[api]` body that transcribes the C++
//! control flow structurally so a later wave fills it without re-reading the
//! source. The unported satellite/sibling types appear as opaque `Cint64`
//! (`INVALID` == the C++ `nullptr`). Logic is documented, never silently dropped.
//! A few queue-flag helpers are substrate-portable now that the linked-role
//! successor and role-backward-propagation hashes have typed arenas; the deeper
//! successor-extension-data workers remain deferred.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::substrate::Cint64;
use super::super::model::{ConceptId, RoleId};
use super::super::process::SatNodeId;
use super::satellites::{
    BackwardSaturationPropagationLink, BackwardSaturationPropagationLinkId,
    LinkedRoleSaturationSuccessorDataId, RoleBackwardSaturationPropagationHashData,
    RoleSaturationProcessLinker, RoleSaturationProcessLinkerId, SaturationConceptExtensionMapId,
    SaturationSuccessorDataId, SaturationSuccessorExtensionDataId,
};

impl super::algorithm::SaturationTaskHandleAlgorithm {
    // =======================================================================
    // Successor-extension-data lazy getter (cpp 908–915).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getSucessorExtensionData`.
    /// cpp 908–915. (C++ spelling `getSucessor...` with a single `c` preserved.)
    ///
    /// Lazily allocates and initialises the `CSaturationSuccessorExtensionData`
    /// hanging off a `CLinkedRoleSaturationSuccessorData` (when `create`), and
    /// returns it.
    ///
    /// Returns the extension-data handle (`INVALID` == `nullptr`).
    pub fn get_sucessor_extension_data(
        &mut self,
        succ_data: LinkedRoleSaturationSuccessorDataId,
        create: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SaturationSuccessorExtensionDataId {
        calc_alg_context
            .process_context_mut()
            .linked_role_successor_extension_data(succ_data, create)
    }

    // =======================================================================
    // Successor ALL-concepts extension propagation (cpp 919–1014, 1831–1966).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::initializeSuccessorALLConceptsExtensions`.
    /// cpp 919–941.
    ///
    /// Seeds the node's ALL-concepts successor-extension data: for every per-role
    /// linked-successor chain that has a backward-propagation reapply linker, clears
    /// its queued flag and runs `updateSuccessorRoleALLConceptsExtensions` over it.
    pub fn initialize_successor_all_concepts_extensions(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let succ_ext = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(*indi_proc_sat_node, true);
        calc_alg_context
            .process_context_mut()
            .sat_successor_extension_all_concepts_extension_data(succ_ext, true);

        let linked_succ_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, false);
        if linked_succ_hash.is_some() {
            let role_succ_pairs: Vec<_> = calc_alg_context
                .process_context()
                .linked_role_sat_succ_hash(linked_succ_hash)
                .get_linked_role_successor_hash()
                .iter()
                .map(|(role, succ_data)| (*role, *succ_data))
                .collect();
            let backward_prop_hash = calc_alg_context
                .process_context_mut()
                .sat_node_role_backward_propagation_hash(*indi_proc_sat_node, false);
            if backward_prop_hash.is_some() {
                for (role, succ_data) in role_succ_pairs {
                    let back_prop_data = calc_alg_context
                        .process_context()
                        .role_backward_sat_prop_hash(backward_prop_hash)
                        .get_role_backward_propagation_data_hash()
                        .get(&role)
                        .cloned();
                    if let Some(back_prop_data) = back_prop_data {
                        if back_prop_data.reapply_linker.is_some() {
                            if let Some(data) = calc_alg_context
                                .process_context_mut()
                                .role_backward_sat_prop_hash_mut(backward_prop_hash)
                                .get_role_backward_propagation_data_hash_mut()
                                .get_mut(&role)
                            {
                                data.role_all_concepts_processing_queued = false;
                            }
                            self.update_successor_role_all_concepts_extensions_for_succ_data(
                                indi_proc_sat_node,
                                role,
                                succ_data,
                                back_prop_data,
                                calc_alg_context,
                            );
                        }
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::updateSuccessorRoleALLConceptsExtensions`
    /// (the `CLinkedRoleSaturationSuccessorData* succData` + `CRoleBackwardSaturationPropagationHashData&` worker overload).
    /// cpp 943–1014. [overload] `_for_succ_data` suffix.
    ///
    /// For one role's linked-successor chain, walks the (incrementally tracked)
    /// link linkers and the backward-propagation reapply descriptors, adding the
    /// required successor cardinality and the propagated ALL-concept operands into
    /// the per-(successor,creation-role) ALL-concept extension data, queuing
    /// extension processing for any that changed; finally advances the
    /// last-examined link / reapply-descriptor watermarks.
    pub fn update_successor_role_all_concepts_extensions_for_succ_data(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        succ_data: LinkedRoleSaturationSuccessorDataId,
        backward_prop_data: RoleBackwardSaturationPropagationHashData,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if succ_data.is_none() || backward_prop_data.reapply_linker.is_none() {
            return;
        }
        let succ_ext = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(*indi_proc_sat_node, true);
        let all_ext = calc_alg_context
            .process_context_mut()
            .sat_successor_extension_all_concepts_extension_data(succ_ext, true);

        let sat_succ_ext_data = self.get_sucessor_extension_data(succ_data, true, calc_alg_context);
        let last_examined_link_linker = calc_alg_context
            .process_context()
            .sat_succ_ext_data(sat_succ_ext_data)
            .get_last_examined_link_linker();
        let last_examined_all_con_rea_des = calc_alg_context
            .process_context()
            .sat_succ_ext_data(sat_succ_ext_data)
            .get_last_examined_all_concept_reapply_descriptor();
        let last_link = calc_alg_context
            .process_context()
            .linked_role_sat_succ_data(succ_data)
            .get_last_successor_link_data();

        let all_con_updated = last_examined_all_con_rea_des != backward_prop_data.reapply_linker;
        let mut continue_iterate_links = all_con_updated;
        let mut iterate_full_all_con_rea_des = false;
        if last_examined_link_linker != last_link {
            continue_iterate_links = true;
            iterate_full_all_con_rea_des = true;
        }

        let mut link_linker_it = last_link;
        while link_linker_it.is_some() && continue_iterate_links {
            let (
                value_nominal_connection,
                succ_indi_node,
                creation_role_linker,
                succ_count,
                next_link,
            ) = {
                let link_ref = calc_alg_context
                    .process_context()
                    .sat_succ_data(link_linker_it);
                (
                    link_ref.value_nominal_connection,
                    link_ref.succ_indi_node,
                    link_ref.creation_role_linker.clone(),
                    link_ref.succ_count,
                    link_ref.next_link,
                )
            };
            if !value_nominal_connection {
                for creation_role_linker_it in creation_role_linker {
                    let creation_role = creation_role_linker_it.target;
                    let linked_succ_indi_all_ext = calc_alg_context
                        .process_context_mut()
                        .sat_all_linked_successor_individual_concepts_extension_data(
                            all_ext,
                            succ_indi_node,
                            true,
                        );
                    let all_con_succ_ext_data = calc_alg_context
                        .process_context_mut()
                        .sat_role_successor_all_concept_extension_data(
                            linked_succ_indi_all_ext,
                            creation_role,
                            true,
                        );

                    let mut concepts_for_succ_indi_node_modified = calc_alg_context
                        .process_context_mut()
                        .sat_successor_all_concept_ext_data_mut(all_con_succ_ext_data)
                        .add_required_successor_cardinality(succ_count);

                    let mut continue_iterate_all_reap_con_des = true;
                    let mut back_reapply_it = backward_prop_data.reapply_linker;
                    while back_reapply_it.is_some() && continue_iterate_all_reap_con_des {
                        let reapply_con_des = calc_alg_context
                            .process_context()
                            .backward_sat_prop_reapply_desc(back_reapply_it)
                            .get_reapply_concept_saturation_descriptor();
                        let (concept, concept_negation) = {
                            let con_des = calc_alg_context
                                .process_context()
                                .con_sat_desc(reapply_con_des);
                            (con_des.get_concept(), con_des.get_negation())
                        };
                        concepts_for_succ_indi_node_modified |= self
                            .add_successor_extensions_all_concept(
                                indi_proc_sat_node,
                                concept,
                                concept_negation,
                                all_con_succ_ext_data,
                                calc_alg_context,
                            );

                        back_reapply_it = calc_alg_context
                            .process_context()
                            .backward_sat_prop_reapply_desc(back_reapply_it)
                            .get_next();
                        if back_reapply_it == last_examined_all_con_rea_des
                            && !iterate_full_all_con_rea_des
                        {
                            continue_iterate_all_reap_con_des = false;
                        }
                    }

                    if concepts_for_succ_indi_node_modified
                        && !calc_alg_context
                            .process_context()
                            .sat_successor_all_concept_ext_data(all_con_succ_ext_data)
                            .is_extension_processing_queued()
                    {
                        let old_head = calc_alg_context
                            .process_context()
                            .sat_indi_node_all_concept_ext_data(all_ext)
                            .get_extension_process_data_linker();
                        calc_alg_context
                            .process_context_mut()
                            .sat_successor_all_concept_ext_data_mut(all_con_succ_ext_data)
                            .next = old_head;
                        calc_alg_context
                            .process_context_mut()
                            .sat_successor_all_concept_ext_data_mut(all_con_succ_ext_data)
                            .set_extension_processing_queued(true);
                        calc_alg_context
                            .process_context_mut()
                            .sat_indi_node_all_concept_ext_data_mut(all_ext)
                            .add_extension_process_data(all_con_succ_ext_data);
                    }
                }
            }

            link_linker_it = next_link;
            if link_linker_it == last_examined_link_linker {
                if !all_con_updated {
                    continue_iterate_links = false;
                } else {
                    iterate_full_all_con_rea_des = false;
                }
            }
        }
        calc_alg_context
            .process_context_mut()
            .sat_succ_ext_data_mut(sat_succ_ext_data)
            .set_last_examined_link_linker(last_link)
            .set_last_examined_all_concept_reapply_descriptor(backward_prop_data.reapply_linker);
        let _ = role;
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::updateSuccessorRoleALLConceptsExtensions`
    /// (the role-keyed dispatcher overload). cpp 1831–1850.
    ///
    /// Looks up the role's linked-successor data and its backward-propagation
    /// reapply linker; if present, clears the queued flags and delegates to the
    /// `_for_succ_data` worker.
    pub fn update_successor_role_all_concepts_extensions(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let linked_succ_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, false);
        if linked_succ_hash.is_some() {
            let succ_data = calc_alg_context
                .process_context()
                .linked_role_sat_succ_hash(linked_succ_hash)
                .get_linked_role_successor_data(role);
            if succ_data.is_some() {
                calc_alg_context
                    .process_context_mut()
                    .linked_role_sat_succ_data_mut(succ_data)
                    .role_all_concepts_processing_queued = false;
                let backward_prop_hash = calc_alg_context
                    .process_context_mut()
                    .sat_node_role_backward_propagation_hash(*indi_proc_sat_node, false);
                if backward_prop_hash.is_some() {
                    let back_prop_data = calc_alg_context
                        .process_context()
                        .role_backward_sat_prop_hash(backward_prop_hash)
                        .get_role_backward_propagation_data_hash()
                        .get(&role)
                        .cloned();
                    if let Some(back_prop_data) = back_prop_data {
                        if back_prop_data.reapply_linker.is_some() {
                            if let Some(data) = calc_alg_context
                                .process_context_mut()
                                .role_backward_sat_prop_hash_mut(backward_prop_hash)
                                .get_role_backward_propagation_data_hash_mut()
                                .get_mut(&role)
                            {
                                data.role_all_concepts_processing_queued = false;
                            }
                            self.update_successor_role_all_concepts_extensions_for_succ_data(
                                indi_proc_sat_node,
                                role,
                                succ_data,
                                back_prop_data,
                                calc_alg_context,
                            );
                        }
                    }
                }
            }
        }
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::updateSuccessorALLConceptsExtensions`.
    /// cpp 1852–1966.
    ///
    /// Drains the node's queued ALL-concept successor-extension worklist: for each
    /// queued `CSaturationSuccessorALLConceptExtensionData`, resolves the (possibly
    /// merged/extended) successor node for its concept-extension map, and when the
    /// resolved node or the required successor cardinality changed, rewires the
    /// per-(super-role) linked-successor connections (deactivating the old, adding
    /// the new, installing a backward-propagation link on negated super-roles),
    /// propagates status flags / connected nominals / cardinality candidates, and
    /// advances the per-extension watermarks. Returns whether anything updated.
    pub fn update_successor_all_concepts_extensions(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated = false;
        let linked_succ_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, false);
        if linked_succ_hash.is_none() {
            return false;
        }
        let succ_ext = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(*indi_proc_sat_node, false);
        if succ_ext.is_none() {
            return false;
        }
        let all_ext = calc_alg_context
            .process_context_mut()
            .sat_successor_extension_all_concepts_extension_data(succ_ext, false);
        if all_ext.is_none() {
            return false;
        }

        while calc_alg_context
            .process_context()
            .sat_indi_node_all_concept_ext_data(all_ext)
            .has_extension_process_data()
        {
            let sat_suc_all_con_ext_data = calc_alg_context
                .process_context()
                .sat_indi_node_all_concept_ext_data(all_ext)
                .get_extension_process_data_linker();
            let next = calc_alg_context
                .process_context()
                .sat_successor_all_concept_ext_data(sat_suc_all_con_ext_data)
                .next;
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_all_concept_ext_data_mut(all_ext)
                .extension_process_linker = next;
            calc_alg_context
                .process_context_mut()
                .sat_successor_all_concept_ext_data_mut(sat_suc_all_con_ext_data)
                .clear_next()
                .set_extension_processing_queued(false);

            let (
                sat_suc_con_ext_map,
                indi_node,
                role,
                mut last_resolved_indi_node,
                last_succ_card,
                required_succ_card,
                concepts_updated,
            ) = {
                let ext_ref = calc_alg_context
                    .process_context()
                    .sat_successor_all_concept_ext_data(sat_suc_all_con_ext_data);
                (
                    ext_ref.get_successor_concept_extension_map(),
                    ext_ref.get_individual_node(),
                    ext_ref.get_role(),
                    ext_ref.get_last_resolved_individual_node(),
                    ext_ref.get_last_connected_successor_cardinality(),
                    ext_ref.get_required_successor_cardinality(),
                    ext_ref.has_concepts_updated_flag(),
                )
            };
            if last_resolved_indi_node.is_none() {
                last_resolved_indi_node = indi_node;
            }

            let mut only_successor_cardinality_updated = true;
            let mut resolved_indi_node = last_resolved_indi_node;
            if concepts_updated {
                resolved_indi_node = self.get_resolved_individual_node_extension_successor(
                    indi_node,
                    sat_suc_con_ext_map,
                    calc_alg_context,
                );
                if last_resolved_indi_node != resolved_indi_node {
                    only_successor_cardinality_updated = false;
                }
            }

            if last_resolved_indi_node != resolved_indi_node || last_succ_card != required_succ_card
            {
                updated = true;
                let mut backward_link_connected = false;
                let super_roles = calc_alg_context
                    .ontology_arenas()
                    .role(role)
                    .get_indirect_super_role_list()
                    .to_vec();

                if last_resolved_indi_node.is_some() {
                    for super_role_it in super_roles.iter().copied() {
                        if !super_role_it.negated {
                            calc_alg_context
                                .process_context_mut()
                                .linked_role_successor_hash_deactivate_linked_successor(
                                    linked_succ_hash,
                                    super_role_it.target,
                                    last_resolved_indi_node,
                                    role,
                                );
                        }
                    }
                }

                for super_role_it in super_roles.iter().copied() {
                    let super_role = super_role_it.target;
                    if !super_role_it.negated {
                        calc_alg_context
                            .process_context_mut()
                            .linked_role_successor_hash_add_extension_successor(
                                linked_succ_hash,
                                super_role,
                                resolved_indi_node,
                                role,
                                required_succ_card,
                            );
                        self.add_new_linked_extension_processing_role(
                            super_role,
                            indi_proc_sat_node,
                            false,
                            true,
                            calc_alg_context,
                        );
                    } else if !only_successor_cardinality_updated {
                        backward_link_connected = true;
                        let mut back_prop_link = BackwardSaturationPropagationLink::new();
                        back_prop_link
                            .init_backward_propagation_link(*indi_proc_sat_node, super_role);
                        let back_prop_link = calc_alg_context
                            .process_context_mut()
                            .alloc_backward_sat_prop_link(back_prop_link);
                        self.install_backward_propagation_link(
                            *indi_proc_sat_node,
                            resolved_indi_node,
                            super_role,
                            back_prop_link,
                            true,
                            true,
                            calc_alg_context,
                        );
                    }
                }

                let resolved_indirect_flags = calc_alg_context
                    .process_context()
                    .sat_node(resolved_indi_node)
                    .indirect_status_flags;
                self.update_indirect_adding_individual_status_flags(
                    *indi_proc_sat_node,
                    &resolved_indirect_flags,
                    calc_alg_context,
                );
                let resolved_succ_conn_nom_set = calc_alg_context
                    .process_context_mut()
                    .sat_node_successor_connected_nominal_set(resolved_indi_node, false);
                self.update_adding_successor_connected_nominal_set(
                    *indi_proc_sat_node,
                    resolved_succ_conn_nom_set,
                    calc_alg_context,
                );
                let (resolved_max_atleast_cardinality, resolved_max_atmost_cardinality) = {
                    let resolved_ref = calc_alg_context
                        .process_context()
                        .sat_node(resolved_indi_node);
                    (
                        resolved_ref.get_max_atleast_cardinality_candidate(),
                        resolved_ref.get_max_atmost_cardinality_candidate(),
                    )
                };
                self.update_max_cardinality_candidates(
                    *indi_proc_sat_node,
                    resolved_max_atleast_cardinality,
                    resolved_max_atmost_cardinality,
                    calc_alg_context,
                );
                if !only_successor_cardinality_updated && !backward_link_connected {
                    calc_alg_context
                        .process_context_mut()
                        .sat_node_mut(resolved_indi_node)
                        .add_non_inverse_connected_individual_node_linker(*indi_proc_sat_node);
                }
                calc_alg_context
                    .process_context_mut()
                    .sat_successor_all_concept_ext_data_mut(sat_suc_all_con_ext_data)
                    .set_last_resolved_individual_node(resolved_indi_node)
                    .set_last_connected_successor_cardinality(required_succ_card);
            }
        }
        updated
    }

    // =======================================================================
    // Successor / predecessor FUNCTIONAL-concepts extension propagation
    // (cpp 1018–1143, 1514–1825).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::installSuccessorPredecessorRoleFunctionalityConceptsExtension`.
    /// cpp 1018–1044.
    ///
    /// Marks a role for FUNCTIONAL successor-concepts queuing (on the linked-role
    /// successor data) and for predecessor-merging queuing (on the role-backward-
    /// propagation data). Returns whether either flag was newly set.
    pub fn install_successor_predecessor_role_functionality_concepts_extension(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut installed = false;
        let linked_succ_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, false);
        if linked_succ_hash.is_some() {
            let succ_data = calc_alg_context
                .process_context_mut()
                .linked_role_successor_data(linked_succ_hash, role, true);
            if succ_data.is_some()
                && !calc_alg_context
                    .process_context()
                    .linked_role_sat_succ_data(succ_data)
                    .role_functional_concepts_queuing_required
            {
                calc_alg_context
                    .process_context_mut()
                    .linked_role_sat_succ_data_mut(succ_data)
                    .role_functional_concepts_queuing_required = true;
                installed = true;
            }
        }

        let backward_prop_hash = calc_alg_context
            .process_context_mut()
            .sat_node_role_backward_propagation_hash(*indi_proc_sat_node, true);
        if backward_prop_hash.is_some() {
            let back_prop_data = calc_alg_context
                .process_context_mut()
                .role_backward_sat_prop_hash_mut(backward_prop_hash)
                .get_role_backward_propagation_data_hash_mut()
                .entry(role)
                .or_default();
            if !back_prop_data.role_predecessor_merging_queuing_required {
                back_prop_data.role_predecessor_merging_queuing_required = true;
                installed = true;
            }
        }
        installed
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::updateSuccessorRoleFUNCTIONALConceptsExtensions`
    /// (the role-keyed dispatcher overload). cpp 1047–1061.
    ///
    /// Looks up the role's linked-successor data; if FUNCTIONAL-concepts queuing is
    /// required and the successor count exceeds one, clears the queued flag and
    /// delegates to the `_for_succ_data` worker. Returns whether anything updated.
    pub fn update_successor_role_functional_concepts_extensions(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated = false;
        let linked_succ_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, false);
        if linked_succ_hash.is_some() {
            let succ_data = calc_alg_context
                .process_context()
                .linked_role_sat_succ_hash(linked_succ_hash)
                .get_linked_role_successor_data(role);
            if succ_data.is_some()
                && calc_alg_context
                    .process_context()
                    .linked_role_sat_succ_data(succ_data)
                    .role_functional_concepts_queuing_required
            {
                let succ_count = {
                    let succ_data_ref = calc_alg_context
                        .process_context_mut()
                        .linked_role_sat_succ_data_mut(succ_data);
                    succ_data_ref.role_functional_concepts_processing_queued = false;
                    succ_data_ref.get_successor_count()
                };
                if succ_count > 1 {
                    updated |= self
                        .update_successor_role_functional_concepts_extensions_for_succ_data(
                            indi_proc_sat_node,
                            role,
                            succ_data,
                            calc_alg_context,
                        );
                }
            }
        }
        updated
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::updateSuccessorRoleFUNCTIONALConceptsExtensions`
    /// (the `CLinkedRoleSaturationSuccessorData* succData` worker overload).
    /// cpp 1514–1683. [overload] `_for_succ_data` suffix.
    ///
    /// When a role has >1 active non-nominal successor each of cardinality ≤1
    /// (functional), merges them into one resolved node: builds the merge link-data
    /// list, picks the max-label successor as the copy base, collects the union
    /// concept-extension map, resolves the merged node, then rewires every super-
    /// role connection (deactivating originals, adding the resolved successor, or
    /// installing a backward-propagation link for negated creation-super-roles),
    /// and propagates the resolved node's status flags / connected nominals /
    /// cardinality candidates. Returns whether a merge happened.
    pub fn update_successor_role_functional_concepts_extensions_for_succ_data(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        succ_data: LinkedRoleSaturationSuccessorDataId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated = false;
        let linked_succ_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, false);
        if succ_data.is_some() && linked_succ_hash.is_some() {
            let functional_ext = calc_alg_context
                .process_context_mut()
                .sat_node_functional_concepts_extension_data(*indi_proc_sat_node, true);
            let role_func_con_ext_data = calc_alg_context
                .process_context_mut()
                .sat_functional_successor_concepts_extension_data(functional_ext, role, true);
            let last_examined_linked_succ = calc_alg_context
                .process_context()
                .sat_successor_functional_concept_ext_data(role_func_con_ext_data)
                .get_last_examined_linked_successor_data();
            let last_linked_succ = calc_alg_context
                .process_context()
                .linked_role_sat_succ_data(succ_data)
                .get_last_successor_link_data();
            if last_linked_succ != last_examined_linked_succ {
                // KONCLUDE-PORT-NOTE[api]: exact side-effect call still waits on the typed
                // `deactivateSubsetMergeableSuccessorLinks` linked-hash/map surface:
                //   succDataMap = succData->getSuccessorNodeDataMap(false);
                //   deactivateSubsetMergeableSuccessorLinks(indiProcSatNode,
                //       linkedSuccHash, succDataMap, role, ctx);
                let mut succ_count = 0;
                let mut max_succ_cardinality = Cint64::MIN;
                let mut last_linked_succ_it = last_linked_succ;
                while last_linked_succ_it.is_some() {
                    let (active_count, value_nominal_connection, successor_count, next_link) = {
                        let linked_succ_data = calc_alg_context
                            .process_context()
                            .sat_succ_data(last_linked_succ_it);
                        (
                            linked_succ_data.active_count,
                            linked_succ_data.value_nominal_connection,
                            linked_succ_data.succ_count,
                            linked_succ_data.next_link,
                        )
                    };
                    if active_count >= 1 && !value_nominal_connection {
                        succ_count += 1;
                        max_succ_cardinality = max_succ_cardinality.max(successor_count);
                    }
                    last_linked_succ_it = next_link;
                }
                if succ_count > 1 && max_succ_cardinality <= 1 {
                    let mut merging_succ_data_linker =
                        super::satellites::IndividualSaturationSuccessorLinkDataLinkerId::NONE;
                    let mut max_label_resolve_indi_linked_succ_data =
                        SaturationSuccessorDataId::NONE;
                    let mut max_label_resolve_indi_concept_count = 0;
                    let mut succ_data_map_entries: Vec<(Cint64, SaturationSuccessorDataId)> =
                        calc_alg_context
                            .process_context()
                            .linked_role_sat_succ_data(succ_data)
                            .get_successor_node_data_map()
                            .iter()
                            .map(|(succ_id, linked_succ_data)| (*succ_id, *linked_succ_data))
                            .collect();
                    succ_data_map_entries.sort_by_key(|(succ_id, _)| *succ_id);

                    for (_, linked_succ_data) in succ_data_map_entries.iter().copied() {
                        let (active_count, value_nominal_connection, succ_indi_node) = {
                            let linked_succ_data_ref = calc_alg_context
                                .process_context()
                                .sat_succ_data(linked_succ_data);
                            (
                                linked_succ_data_ref.active_count,
                                linked_succ_data_ref.value_nominal_connection,
                                linked_succ_data_ref.succ_indi_node,
                            )
                        };
                        if active_count >= 1 && !value_nominal_connection {
                            let succ_label_con_count = {
                                let con_set = calc_alg_context
                                    .process_context_mut()
                                    .sat_node_reapply_concept_saturation_label_set(
                                        succ_indi_node,
                                        false,
                                    );
                                if con_set.is_some() {
                                    calc_alg_context
                                        .process_context()
                                        .reapply_con_sat_label_set(con_set)
                                        .get_concept_count()
                                } else {
                                    0
                                }
                            };
                            if max_label_resolve_indi_linked_succ_data.is_none()
                                && succ_label_con_count > max_label_resolve_indi_concept_count
                            {
                                max_label_resolve_indi_concept_count = succ_label_con_count;
                                max_label_resolve_indi_linked_succ_data = linked_succ_data;
                            }
                            let tmp_merging_succ_data_linker = self
                                .create_individual_saturation_successor_link_data_linker(
                                    calc_alg_context,
                                );
                            calc_alg_context
                                .process_context_mut()
                                .indi_sat_succ_link_data_linker_mut(tmp_merging_succ_data_linker)
                                .init_successor_link_data_linker(linked_succ_data)
                                .set_next(merging_succ_data_linker);
                            merging_succ_data_linker = tmp_merging_succ_data_linker;
                        }
                    }

                    let mut con_ext_map = SaturationConceptExtensionMapId::NONE;
                    let resolve_linked_succ_data = max_label_resolve_indi_linked_succ_data;
                    let mut copy_indi_proc_sat_node = if resolve_linked_succ_data.is_some() {
                        calc_alg_context
                            .process_context()
                            .sat_succ_data(resolve_linked_succ_data)
                            .succ_indi_node
                    } else {
                        SatNodeId::NONE
                    };
                    let mut merging_succ_data_linker_it = merging_succ_data_linker;
                    while merging_succ_data_linker_it.is_some() {
                        let (linked_succ_data, next_linker) = {
                            let linker_ref = calc_alg_context
                                .process_context()
                                .indi_sat_succ_link_data_linker(merging_succ_data_linker_it);
                            (linker_ref.get_data(), linker_ref.get_next())
                        };
                        if linked_succ_data != resolve_linked_succ_data {
                            let succ_node = calc_alg_context
                                .process_context()
                                .sat_succ_data(linked_succ_data)
                                .succ_indi_node;
                            self.collect_resolve_individual_extendable_concept_map(
                                copy_indi_proc_sat_node,
                                succ_node,
                                &mut con_ext_map,
                                calc_alg_context,
                            );
                        }
                        merging_succ_data_linker_it = next_linker;
                    }
                    self.release_individual_saturation_successor_link_data_linker(
                        merging_succ_data_linker,
                        calc_alg_context,
                    );
                    if copy_indi_proc_sat_node.is_some() {
                        let succ_ext = calc_alg_context
                            .process_context_mut()
                            .sat_node_ext_successor_extension_data(copy_indi_proc_sat_node, true);
                        let mut resolve_data = calc_alg_context
                            .process_context_mut()
                            .sat_successor_extension_base_extension_resolve_data(succ_ext, true);
                        resolve_data = self.get_resolved_individual_node_extension_for_con_map(
                            resolve_data,
                            con_ext_map,
                            &mut copy_indi_proc_sat_node,
                            calc_alg_context,
                        );
                        let resolved_indi_node = calc_alg_context
                            .process_context()
                            .sat_indi_node_ext_resolve_data(resolve_data)
                            .get_processing_individual_node();
                        calc_alg_context
                            .process_context_mut()
                            .sat_successor_functional_concept_ext_data_mut(role_func_con_ext_data)
                            .set_last_resolved_individual_node(resolved_indi_node);
                        let mut backward_link_connected = false;
                        let mut connection_already_exist = false;
                        for (_, linked_succ_data) in succ_data_map_entries.iter().copied() {
                            let (
                                active_count,
                                value_nominal_connection,
                                link_succ_count,
                                succ_node,
                                creation_roles,
                            ) = {
                                let linked_succ_data_ref = calc_alg_context
                                    .process_context()
                                    .sat_succ_data(linked_succ_data);
                                (
                                    linked_succ_data_ref.active_count,
                                    linked_succ_data_ref.value_nominal_connection,
                                    linked_succ_data_ref.succ_count,
                                    linked_succ_data_ref.succ_indi_node,
                                    linked_succ_data_ref.creation_role_linker.clone(),
                                )
                            };
                            if active_count >= 1 && !value_nominal_connection {
                                let _link_succ_count = link_succ_count;
                                for creation_role_linker_it in creation_roles {
                                    if !creation_role_linker_it.negated {
                                        let creation_role = creation_role_linker_it.target;
                                        let mut make_new_successor_connections = true;
                                        let mut remove_previous_successor_connections = true;
                                        if calc_alg_context
                                            .process_context()
                                            .linked_role_successor_hash_has_active_linked_successor(
                                                linked_succ_hash,
                                                creation_role,
                                                resolved_indi_node,
                                                None,
                                                1,
                                            )
                                        {
                                            connection_already_exist = true;
                                            make_new_successor_connections = false;
                                            if succ_node == resolved_indi_node {
                                                remove_previous_successor_connections = false;
                                            }
                                        }
                                        let creation_super_roles = calc_alg_context
                                            .ontology_arenas()
                                            .role(creation_role)
                                            .get_indirect_super_role_list()
                                            .to_vec();
                                        for creation_super_role_it in creation_super_roles {
                                            let creation_super_role = creation_super_role_it.target;
                                            if !creation_super_role_it.negated {
                                                if remove_previous_successor_connections {
                                                    calc_alg_context
                                                        .process_context_mut()
                                                        .linked_role_successor_hash_deactivate_linked_successor(
                                                            linked_succ_hash,
                                                            creation_super_role,
                                                            succ_node,
                                                            creation_role,
                                                        );
                                                }
                                                if make_new_successor_connections {
                                                    calc_alg_context
                                                        .process_context_mut()
                                                        .linked_role_successor_hash_add_extension_successor(
                                                            linked_succ_hash,
                                                            creation_super_role,
                                                            resolved_indi_node,
                                                            creation_role,
                                                            1,
                                                        );
                                                }
                                            } else if make_new_successor_connections {
                                                backward_link_connected = true;
                                                let mut back_prop_link =
                                                    BackwardSaturationPropagationLink::new();
                                                back_prop_link.init_backward_propagation_link(
                                                    *indi_proc_sat_node,
                                                    creation_super_role,
                                                );
                                                let back_prop_link = calc_alg_context
                                                    .process_context_mut()
                                                    .alloc_backward_sat_prop_link(back_prop_link);
                                                self.install_backward_propagation_link(
                                                    *indi_proc_sat_node,
                                                    resolved_indi_node,
                                                    creation_super_role,
                                                    back_prop_link,
                                                    true,
                                                    true,
                                                    calc_alg_context,
                                                );
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        let resolved_indirect_flags = calc_alg_context
                            .process_context()
                            .sat_node(resolved_indi_node)
                            .indirect_status_flags;
                        self.update_indirect_adding_individual_status_flags(
                            *indi_proc_sat_node,
                            &resolved_indirect_flags,
                            calc_alg_context,
                        );
                        let resolved_succ_conn_nom_set = calc_alg_context
                            .process_context_mut()
                            .sat_node_successor_connected_nominal_set(resolved_indi_node, false);
                        self.update_adding_successor_connected_nominal_set(
                            *indi_proc_sat_node,
                            resolved_succ_conn_nom_set,
                            calc_alg_context,
                        );
                        let (resolved_max_atleast_cardinality, resolved_max_atmost_cardinality) = {
                            let resolved_ref = calc_alg_context
                                .process_context()
                                .sat_node(resolved_indi_node);
                            (
                                resolved_ref.get_max_atleast_cardinality_candidate(),
                                resolved_ref.get_max_atmost_cardinality_candidate(),
                            )
                        };
                        self.update_max_cardinality_candidates(
                            *indi_proc_sat_node,
                            resolved_max_atleast_cardinality,
                            resolved_max_atmost_cardinality,
                            calc_alg_context,
                        );

                        if !connection_already_exist && !backward_link_connected {
                            calc_alg_context
                                .process_context_mut()
                                .sat_node_mut(resolved_indi_node)
                                .add_non_inverse_connected_individual_node_linker(
                                    *indi_proc_sat_node,
                                );
                        }
                        updated = true;
                    }
                }
            }
        }
        // Driven start-to-finish by the FUNCTIONAL-concept extension-data + linked-
        // successor + backward-propagation satellites and by PU-SAT-8/10/11 siblings,
        // none yet ported.
        let _ = (role, linked_succ_hash);
        updated
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::updateSuccessorRoleQualifiedFUNCTIONALConceptsExtensions`
    /// (the qualifying-concept-linker dispatcher overload). cpp 1064–1075.
    ///
    /// Looks up the role's linked-successor data; if it has >1 successors, delegates
    /// to the `_for_succ_data` qualified worker. Returns whether anything updated.
    pub fn update_successor_role_qualified_functional_concepts_extensions(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        // `CSortedNegLinker<CConcept*>* qualifiyConLinker` (C++ spelling preserved)
        qualifiy_con_linker: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated = false;
        let linked_succ_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, false);
        if linked_succ_hash.is_some() {
            let succ_data = calc_alg_context
                .process_context()
                .linked_role_sat_succ_hash(linked_succ_hash)
                .get_linked_role_successor_data(role);
            if succ_data.is_some()
                && calc_alg_context
                    .process_context()
                    .linked_role_sat_succ_data(succ_data)
                    .get_successor_count()
                    > 1
            {
                updated |= self
                    .update_successor_role_qualified_functional_concepts_extensions_for_succ_data(
                        indi_proc_sat_node,
                        role,
                        qualifiy_con_linker,
                        succ_data,
                        calc_alg_context,
                    );
            }
        }
        updated
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::updateSuccessorRoleQualifiedFUNCTIONALConceptsExtensions`
    /// (the `CLinkedRoleSaturationSuccessorData* succData` worker overload).
    /// cpp 1690–1825. [overload] `_for_succ_data` suffix.
    ///
    /// The qualified analogue of `update_successor_role_functional_concepts_extensions_for_succ_data`:
    /// merging is restricted to the active non-nominal successors whose label
    /// actually contains one of the qualifying concepts; otherwise the merge-and-
    /// rewire flow (resolve a copy base, union the extendable concept maps, resolve
    /// the merged node, deactivate/add/backward-link the super-role connections, and
    /// propagate status/nominal/cardinality data) is the same. Returns whether a
    /// merge happened.
    pub fn update_successor_role_qualified_functional_concepts_extensions_for_succ_data(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        // `CSortedNegLinker<CConcept*>* qualifiyConLinker`
        qualifiy_con_linker: Cint64,
        // `CLinkedRoleSaturationSuccessorData* succData`
        succ_data: LinkedRoleSaturationSuccessorDataId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated = false;
        // W6-DEFER[api]: faithful C++ body —
        //   linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //   indiProcSatNodeFunctionalConSuccExt =
        //       indiProcSatNode->getSuccessorExtensionData()->getFUNCTIONALConceptsExtensionData(true);
        //   if (succData) {
        //       succDataMap = succData->getSuccessorNodeDataMap(false);
        //       succCount = 0; maxSuccCardinality = CINT64_MIN; mergingSuccDataLinker = nullptr;
        //       maxLabelResolveIndiLinkedSuccData = nullptr; maxLabelResolveIndiConceptCount = 0;
        //       for (it = succData->getLastSuccessorLinkData(); it; it = it->mNextLink)
        //           if (it->mActiveCount >= 1 && !it->mVALUENominalConnection) {
        //               succConSet = it->mSuccIndiNode->getReapplyConceptSaturationLabelSet(false);
        //               containsQualification = false;
        //               for (q in qualifiyConLinker) if (succConSet->containsConcept(q->getData(), q->isNegated())) { containsQualification = true; break; }
        //               if (containsQualification) {
        //                   succCount++; maxSuccCardinality = qMax(maxSuccCardinality, it->mSuccCount);
        //                   succLabelConCount = succConSet->getConceptCount();
        //                   if (!maxLabelResolveIndiLinkedSuccData && succLabelConCount > maxLabelResolveIndiConceptCount) {
        //                       maxLabelResolveIndiConceptCount = succLabelConCount; maxLabelResolveIndiLinkedSuccData = it; }
        //                   tmp = createIndividualSaturationSuccessorLinkDataLinker(ctx); tmp->initSuccessorLinkDataLinker(it);
        //                   mergingSuccDataLinker = tmp->append(mergingSuccDataLinker);
        //               }
        //           }
        //       if (succCount > 1 && maxSuccCardinality <= 1) {
        //           // identical merge-resolve-rewire flow as the unqualified worker (cpp 1736–1819):
        //           //   pick copy base = maxLabelResolveIndiLinkedSuccData->mSuccIndiNode;
        //           //   collectResolveIndividualExtendableConceptMap over the others;
        //           //   resolveData = getResolvedIndividualNodeExtension(base resolve data, conExtMap, copy, ctx);
        //           //   resolvedIndiNode = resolveData->getProcessingIndividualNode();
        //           //   for ((succID, linkedSuccData) in succDataMap) if (active && !nominal)
        //           //       for (creationRole in linkedSuccData->mCreationRoleLinker) if (!negated)
        //           //           { hasActiveLinkedSuccessor guard; for (creationSuperRole) deactivate / addExtension / installBackwardPropagationLink }
        //           //   updateIndirectAddingIndividualStatusFlags / updateAddingSuccessorConnectedNominal / updateMaxCardinalityCandidates;
        //           updated = true;
        //       }
        //       releaseIndividualSaturationSuccessorLinkDataLinker(mergingSuccDataLinker, ctx);
        //   }
        //   return updated;
        // Same not-yet-ported satellite tower + PU-SAT-10/11 siblings as the
        // unqualified worker; additionally needs `CReapplyConceptSaturationLabelSet::containsConcept`.
        let _ = (indi_proc_sat_node, role, qualifiy_con_linker, succ_data);
        updated
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::updatePredecessorRoleFUNCTIONALConceptsExtensions`
    /// (the role-keyed dispatcher overload). cpp 1079–1103.
    ///
    /// If the role-backward-propagation data requires predecessor-merging queuing
    /// and carries a backward-propagation link chain, clears the queued flag, looks
    /// up the role's linked-successor data, and (when it has ≥1 successor) delegates
    /// to the `_for_succ_data` worker. Returns whether anything updated.
    pub fn update_predecessor_role_functional_concepts_extensions(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated = false;
        let backward_prop_hash = calc_alg_context
            .process_context_mut()
            .sat_node_role_backward_propagation_hash(*indi_proc_sat_node, true);
        if backward_prop_hash.is_some() {
            let (queuing_required, back_prop_link_linker) = {
                let back_prop_data = calc_alg_context
                    .process_context_mut()
                    .role_backward_sat_prop_hash_mut(backward_prop_hash)
                    .get_role_backward_propagation_data_hash_mut()
                    .entry(role)
                    .or_default();
                let queuing_required = back_prop_data.role_predecessor_merging_queuing_required;
                if queuing_required {
                    back_prop_data.role_predecessor_merging_processing_queued = false;
                }
                (queuing_required, back_prop_data.link_linker)
            };
            if queuing_required && back_prop_link_linker.is_some() {
                let linked_succ_hash = calc_alg_context
                    .process_context_mut()
                    .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, false);
                if linked_succ_hash.is_some() {
                    let succ_data = calc_alg_context
                        .process_context()
                        .linked_role_sat_succ_hash(linked_succ_hash)
                        .get_linked_role_successor_data(role);
                    if succ_data.is_some()
                        && calc_alg_context
                            .process_context()
                            .linked_role_sat_succ_data(succ_data)
                            .get_successor_count()
                            >= 1
                    {
                        updated |= self
                            .update_predecessor_role_functional_concepts_extensions_for_succ_data(
                                indi_proc_sat_node,
                                role,
                                succ_data,
                                back_prop_link_linker,
                                calc_alg_context,
                            );
                    }
                }
            }
        }
        updated
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::updatePredecessorRoleFUNCTIONALConceptsExtensions`
    /// (the `succData` + `CBackwardSaturationPropagationLink* backPropLinkLinker` worker overload).
    /// cpp 1113–1143. [overload] `_for_succ_data` suffix.
    ///
    /// Finds the first active linked successor of the role; for every backward-
    /// propagation link source predecessor/ancestor distinct from that successor,
    /// creates an ancestor↔successor merging extension. Returns whether anything
    /// updated.
    pub fn update_predecessor_role_functional_concepts_extensions_for_succ_data(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        // `CLinkedRoleSaturationSuccessorData* succData`
        succ_data: LinkedRoleSaturationSuccessorDataId,
        // `CBackwardSaturationPropagationLink* backPropLinkLinker`
        back_prop_link_linker: BackwardSaturationPropagationLinkId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated = false;
        let _linked_succ_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, false);
        let _functional_ext = calc_alg_context
            .process_context_mut()
            .sat_node_functional_concepts_extension_data(*indi_proc_sat_node, true);
        if succ_data.is_some() {
            let mut linked_succ_it = calc_alg_context
                .process_context()
                .linked_role_sat_succ_data(succ_data)
                .get_last_successor_link_data();
            let mut active_linked_succ = SaturationSuccessorDataId::NONE;
            while linked_succ_it.is_some() && active_linked_succ.is_none() {
                let linked_succ_ref = calc_alg_context
                    .process_context()
                    .sat_succ_data(linked_succ_it);
                if linked_succ_ref.get_active_count() >= 1 {
                    active_linked_succ = linked_succ_it;
                }
                linked_succ_it = linked_succ_ref.get_next();
            }
            if active_linked_succ.is_some() {
                let (succ_indi_node, creation_role_linker) = {
                    let active_ref = calc_alg_context
                        .process_context()
                        .sat_succ_data(active_linked_succ);
                    (
                        active_ref.succ_indi_node,
                        active_ref.creation_role_linker.clone(),
                    )
                };
                if succ_indi_node.is_some() {
                    let mut back_prop_link_linker_it = back_prop_link_linker;
                    while back_prop_link_linker_it.is_some() {
                        let back_prop_ref = calc_alg_context
                            .process_context()
                            .backward_sat_prop_link(back_prop_link_linker_it);
                        let pred_anc_indi_node = back_prop_ref.get_source_individual();
                        let next = back_prop_ref.get_next();
                        if succ_indi_node != pred_anc_indi_node {
                            updated |= self.create_ancestor_successor_merging_extension(
                                indi_proc_sat_node,
                                role,
                                succ_indi_node,
                                pred_anc_indi_node,
                                creation_role_linker.clone(),
                                calc_alg_context,
                            );
                        }
                        back_prop_link_linker_it = next;
                    }
                }
            }
        }
        updated
    }

    // =======================================================================
    // Backward-propagation-link installation (cpp 1974–2016).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::installBackwardPropagationLink`.
    /// cpp 1974–2016.
    ///
    /// Installs a backward-propagation `link` for `role` on the destination node's
    /// role-backward-propagation data (deduplicating by source individual). On a
    /// fresh install, replays any pending reapply descriptor onto the source node
    /// (when `applyBackPropDes`). When predecessor-merging queuing is required and
    /// `queueFunctionalProcessing` is set, enqueues the destination node for
    /// successor-extension processing and registers a role process-linker for its
    /// FUNCTIONAL-concepts extension data. Returns whether the link was installed.
    pub fn install_backward_propagation_link(
        &mut self,
        source_indi_proc_sat_node: SatNodeId,
        dest_indi_proc_sat_node: SatNodeId,
        role: RoleId,
        link: BackwardSaturationPropagationLinkId,
        apply_back_prop_des: bool,
        queue_functional_processing: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut link_installed = false;
        if dest_indi_proc_sat_node.is_none() || link.is_none() {
            return false;
        }

        let resolved_indi_back_prop_hash = calc_alg_context
            .process_context_mut()
            .sat_node_role_backward_propagation_hash(dest_indi_proc_sat_node, true);
        if resolved_indi_back_prop_hash.is_none() {
            return false;
        }

        let link_source = calc_alg_context
            .process_context()
            .backward_sat_prop_link(link)
            .get_source_individual();
        let (old_head, reapply_linker, install_link) = {
            let back_prop_hash = calc_alg_context
                .process_context()
                .role_backward_sat_prop_hash(resolved_indi_back_prop_hash);
            let data = back_prop_hash
                .get_role_backward_propagation_data_hash()
                .get(&role);
            let old_head = data
                .map(|data| data.link_linker)
                .unwrap_or(BackwardSaturationPropagationLinkId::NONE);
            let reapply_linker = data.map(|data| data.reapply_linker).unwrap_or(
                super::satellites::BackwardSaturationPropagationReapplyDescriptorId::NONE,
            );
            let install_link = old_head.is_none()
                || calc_alg_context
                    .process_context()
                    .backward_sat_prop_link(old_head)
                    .get_source_individual()
                    != link_source;
            (old_head, reapply_linker, install_link)
        };

        if install_link {
            link_installed = true;
            calc_alg_context
                .process_context_mut()
                .backward_sat_prop_link_mut(link)
                .set_next(old_head);
            calc_alg_context
                .process_context_mut()
                .role_backward_sat_prop_hash_mut(resolved_indi_back_prop_hash)
                .get_role_backward_propagation_data_hash_mut()
                .entry(role)
                .or_default()
                .link_linker = link;

            if reapply_linker.is_some() && apply_back_prop_des {
                self.apply_backward_propagation_concepts(
                    source_indi_proc_sat_node,
                    reapply_linker,
                    calc_alg_context,
                );
            }
        }

        let queue_predecessor_merging = {
            let data = calc_alg_context
                .process_context()
                .role_backward_sat_prop_hash(resolved_indi_back_prop_hash)
                .get_role_backward_propagation_data_hash()
                .get(&role);
            data.map(|data| {
                data.role_predecessor_merging_queuing_required
                    && queue_functional_processing
                    && !data.role_predecessor_merging_processing_queued
            })
            .unwrap_or(false)
        };

        if queue_predecessor_merging {
            calc_alg_context
                .process_context_mut()
                .role_backward_sat_prop_hash_mut(resolved_indi_back_prop_hash)
                .get_role_backward_propagation_data_hash_mut()
                .entry(role)
                .or_default()
                .role_predecessor_merging_processing_queued = true;

            let mut dest_node = dest_indi_proc_sat_node;
            self.add_successor_extension_to_processing_queue(&mut dest_node, calc_alg_context);

            let succ_ext_data = calc_alg_context
                .process_context_mut()
                .sat_node_ext_successor_extension_data(dest_indi_proc_sat_node, false);
            if succ_ext_data.is_some() {
                let functional_ext = calc_alg_context
                    .process_context_mut()
                    .sat_successor_extension_functional_concepts_extension_data(
                        succ_ext_data,
                        false,
                    );
                if functional_ext.is_some()
                    && calc_alg_context
                        .process_context()
                        .sat_indi_node_functional_concept_ext_data(functional_ext)
                        .is_successor_extension_initialized()
                {
                    let predecessor_role_linker = calc_alg_context
                        .process_context()
                        .sat_indi_node_functional_concept_ext_data(functional_ext)
                        .linked_predecessor_added_role_process_linker;
                    if !Self::role_process_linker_chain_has_role(
                        predecessor_role_linker,
                        role,
                        calc_alg_context,
                    ) {
                        let old_head = predecessor_role_linker;
                        let mut role_process_linker = RoleSaturationProcessLinker::new();
                        role_process_linker
                            .init_role_process_linker(role)
                            .set_next(old_head);
                        let role_process_linker = calc_alg_context
                            .process_context_mut()
                            .alloc_role_sat_proc_linker(role_process_linker);
                        calc_alg_context
                            .process_context_mut()
                            .sat_indi_node_functional_concept_ext_data_mut(functional_ext)
                            .linked_predecessor_added_role_process_linker = role_process_linker;
                    }
                }
            }
        }
        link_installed
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyBackwardPropagationConcepts`.
    /// cpp 7101–7115.
    ///
    /// Replays each backward-propagation reapply descriptor on the source node by
    /// adding every operand of the descriptor's concept with operand polarity xor
    /// descriptor polarity.
    pub fn apply_backward_propagation_concepts(
        &mut self,
        mut source_indi_node: SatNodeId,
        mut back_prop_reapply_des_it: super::satellites::BackwardSaturationPropagationReapplyDescriptorId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        while back_prop_reapply_des_it.is_some() {
            let (reapply_con_sat_des, next_reapply) = {
                let reapply_ref = calc_alg_context
                    .process_context()
                    .backward_sat_prop_reapply_desc(back_prop_reapply_des_it);
                (
                    reapply_ref.get_reapply_concept_saturation_descriptor(),
                    reapply_ref.get_next(),
                )
            };
            let (reapply_concept, reapply_con_negation) = {
                let con_sat_des_ref = calc_alg_context
                    .process_context()
                    .con_sat_desc(reapply_con_sat_des);
                (
                    con_sat_des_ref.get_concept(),
                    con_sat_des_ref.get_negation(),
                )
            };
            let operands: Vec<(ConceptId, bool)> = calc_alg_context
                .ontology_arenas()
                .concept(reapply_concept)
                .get_operand_list()
                .iter()
                .map(|op| (op.target, op.negated ^ reapply_con_negation))
                .collect();
            for (op_concept, op_negation) in operands {
                self.add_concept_filtered_to_individual(
                    op_concept,
                    op_negation,
                    &mut source_indi_node,
                    calc_alg_context,
                );
            }
            back_prop_reapply_des_it = next_reapply;
        }
    }

    fn role_process_linker_chain_has_role(
        mut linker: RoleSaturationProcessLinkerId,
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
}

#[cfg(test)]
mod tests {
    use super::super::super::model::concept::Concept;
    use super::super::super::model::op::CCALL;
    use super::super::super::model::role::Role;
    use super::super::super::model::substrate::INVALID;
    use super::super::super::model::Id;
    use super::super::super::process::sat_node::IndividualSaturationProcessNode;
    use super::super::algorithm::SaturationTaskHandleAlgorithm;
    use super::*;

    fn role(ctx: &mut CalculationAlgorithmContextBase, tag: Cint64) -> RoleId {
        let mut role = Role::new();
        role.set_role_tag(tag);
        ctx.ontology_arenas_mut().alloc_role(role)
    }

    fn atom(ctx: &mut CalculationAlgorithmContextBase, tag: Cint64) -> ConceptId {
        let mut concept = Concept::new();
        concept.set_concept_tag(tag);
        ctx.ontology_arenas_mut().alloc_concept(concept)
    }

    fn concept_with_operand(
        ctx: &mut CalculationAlgorithmContextBase,
        tag: Cint64,
        operand: ConceptId,
        operand_negated: bool,
    ) -> ConceptId {
        let mut concept = Concept::new();
        concept.set_concept_tag(tag);
        concept.add_operand_linker(operand, operand_negated);
        ctx.ontology_arenas_mut().alloc_concept(concept)
    }

    fn add_self_indirect_super_role(ctx: &mut CalculationAlgorithmContextBase, role: RoleId) {
        ctx.ontology_arenas_mut()
            .role_mut(role)
            .add_indirect_super_role_linker(super::super::super::model::substrate::NegLink {
                target: role,
                negated: false,
            });
    }

    fn add_negated_indirect_super_role(
        ctx: &mut CalculationAlgorithmContextBase,
        role: RoleId,
        super_role: RoleId,
    ) {
        ctx.ontology_arenas_mut()
            .role_mut(role)
            .add_indirect_super_role_linker(super::super::super::model::substrate::NegLink {
                target: super_role,
                negated: true,
            });
    }

    fn active_successor(
        ctx: &mut CalculationAlgorithmContextBase,
        succ_count: Cint64,
    ) -> SaturationSuccessorDataId {
        let succ = ctx
            .process_context_mut()
            .alloc_sat_succ_data(super::super::satellites::SaturationSuccessorData::new());
        ctx.process_context_mut()
            .sat_succ_data_mut(succ)
            .set_successor_count(succ_count)
            .set_active_count(1);
        succ
    }

    fn set_sat_label_count(
        ctx: &mut CalculationAlgorithmContextBase,
        node: SatNodeId,
        count: Cint64,
    ) {
        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(node, true);
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(label_set)
            .concept_count = count;
    }

    #[test]
    fn s06_install_functionality_extension_creates_backward_prop_requirement() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 601);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(603));

        assert!(
            algo.install_successor_predecessor_role_functionality_concepts_extension(
                &mut node, role, &mut ctx
            )
        );

        let back_hash = ctx.process_context().sat_node(node).role_back_prop_hash;
        let data = ctx
            .process_context()
            .role_backward_sat_prop_hash(back_hash)
            .get_role_backward_propagation_data_hash()
            .get(&role)
            .expect("role bucket should be created");
        assert!(data.role_predecessor_merging_queuing_required);
        assert!(ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, false)
            .is_none());
    }

    #[test]
    fn s06_install_functionality_extension_updates_existing_linked_successor_bucket() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 611);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(613));
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);

        assert!(
            algo.install_successor_predecessor_role_functionality_concepts_extension(
                &mut node, role, &mut ctx
            )
        );

        let succ_data = ctx
            .process_context()
            .linked_role_sat_succ_hash(linked_hash)
            .get_linked_role_successor_data(role);
        assert!(
            ctx.process_context()
                .linked_role_sat_succ_data(succ_data)
                .role_functional_concepts_queuing_required
        );
        let back_hash = ctx.process_context().sat_node(node).role_back_prop_hash;
        assert!(
            ctx.process_context()
                .role_backward_sat_prop_hash(back_hash)
                .get_role_backward_propagation_data_hash()
                .get(&role)
                .unwrap()
                .role_predecessor_merging_queuing_required
        );
    }

    #[test]
    fn s06_install_functionality_extension_is_idempotent() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 621);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(623));
        ctx.process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);

        assert!(
            algo.install_successor_predecessor_role_functionality_concepts_extension(
                &mut node, role, &mut ctx
            )
        );
        assert!(
            !algo.install_successor_predecessor_role_functionality_concepts_extension(
                &mut node, role, &mut ctx
            )
        );
    }

    #[test]
    fn s06_update_functional_extensions_without_linked_hash_returns_false() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 631);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(633));

        assert!(
            !algo.update_successor_role_functional_concepts_extensions(&mut node, role, &mut ctx)
        );
    }

    #[test]
    fn s06_update_functional_extensions_without_role_bucket_returns_false() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 641);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(643));
        ctx.process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);

        assert!(
            !algo.update_successor_role_functional_concepts_extensions(&mut node, role, &mut ctx)
        );
    }

    #[test]
    fn s06_update_functional_extensions_clears_processing_flag_for_single_successor() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 651);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(653));
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data =
            ctx.process_context_mut()
                .linked_role_successor_data(linked_hash, role, true);
        ctx.process_context_mut()
            .linked_role_sat_succ_data_mut(succ_data)
            .set_successor_count(1);
        {
            let succ_data_ref = ctx
                .process_context_mut()
                .linked_role_sat_succ_data_mut(succ_data);
            succ_data_ref.role_functional_concepts_queuing_required = true;
            succ_data_ref.role_functional_concepts_processing_queued = true;
        }

        assert!(
            !algo.update_successor_role_functional_concepts_extensions(&mut node, role, &mut ctx)
        );
        let succ_data_ref = ctx.process_context().linked_role_sat_succ_data(succ_data);
        assert!(succ_data_ref.role_functional_concepts_queuing_required);
        assert!(!succ_data_ref.role_functional_concepts_processing_queued);
    }

    #[test]
    fn s06_update_qualified_functional_extensions_without_linked_hash_returns_false() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 652);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(654));

        assert!(
            !algo.update_successor_role_qualified_functional_concepts_extensions(
                &mut node, role, INVALID, &mut ctx
            )
        );
    }

    #[test]
    fn s06_update_qualified_functional_extensions_without_role_bucket_returns_false() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 656);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(658));
        ctx.process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);

        assert!(
            !algo.update_successor_role_qualified_functional_concepts_extensions(
                &mut node, role, INVALID, &mut ctx
            )
        );
    }

    #[test]
    fn s06_update_qualified_functional_extensions_ignores_single_successor() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 660);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(662));
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data =
            ctx.process_context_mut()
                .linked_role_successor_data(linked_hash, role, true);
        ctx.process_context_mut()
            .linked_role_sat_succ_data_mut(succ_data)
            .set_successor_count(1);

        assert!(
            !algo.update_successor_role_qualified_functional_concepts_extensions(
                &mut node, role, INVALID, &mut ctx
            )
        );
        assert_eq!(
            ctx.process_context()
                .linked_role_sat_succ_data(succ_data)
                .get_successor_count(),
            1
        );
    }

    #[test]
    fn s06_update_qualified_functional_extensions_delegates_multi_successor_boundary() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 664);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(666));
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data =
            ctx.process_context_mut()
                .linked_role_successor_data(linked_hash, role, true);
        ctx.process_context_mut()
            .linked_role_sat_succ_data_mut(succ_data)
            .set_successor_count(2);

        assert!(
            !algo.update_successor_role_qualified_functional_concepts_extensions(
                &mut node, role, INVALID, &mut ctx
            )
        );
        assert_eq!(
            ctx.process_context()
                .linked_role_sat_succ_data(succ_data)
                .get_successor_count(),
            2
        );
    }

    #[test]
    fn s06_update_all_worker_adds_required_cardinality_and_all_operands() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let base_role = role(&mut ctx, 654);
        let creation_role = role(&mut ctx, 655);
        let operand = atom(&mut ctx, 656);
        let mut all_concept = Concept::new();
        all_concept
            .set_operator_code(CCALL)
            .add_operand_linker(operand, false)
            .set_operand_count(1);
        let all_concept = ctx.ontology_arenas_mut().alloc_concept(all_concept);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(657));
        let succ_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(658));
        let succ_data = ctx.process_context_mut().alloc_linked_role_sat_succ_data(
            super::super::satellites::LinkedRoleSaturationSuccessorData::new(),
        );
        let succ = active_successor(&mut ctx, 3);
        {
            let succ_ref = ctx.process_context_mut().sat_succ_data_mut(succ);
            succ_ref.succ_indi_node = succ_node;
            succ_ref
                .creation_role_linker
                .push(super::super::super::model::substrate::NegLink {
                    target: creation_role,
                    negated: false,
                });
        }
        ctx.process_context_mut()
            .linked_role_sat_succ_data_mut(succ_data)
            .set_last_successor_link_data(succ);
        let mut descriptor = super::super::satellites::ConceptSaturationDescriptor::new();
        descriptor.init_concept_saturation_descriptor(all_concept, false);
        let descriptor = ctx.process_context_mut().alloc_con_sat_desc(descriptor);
        let mut reapply =
            super::super::satellites::BackwardSaturationPropagationReapplyDescriptor::new();
        reapply.init_backward_propagation_reapply_descriptor(descriptor);
        let reapply = ctx
            .process_context_mut()
            .alloc_backward_sat_prop_reapply_desc(reapply);
        let mut back_prop_data = RoleBackwardSaturationPropagationHashData::new();
        back_prop_data.reapply_linker = reapply;

        algo.update_successor_role_all_concepts_extensions_for_succ_data(
            &mut node,
            base_role,
            succ_data,
            back_prop_data,
            &mut ctx,
        );

        let all_ext = ctx
            .process_context_mut()
            .sat_node_all_concepts_extension_data(node, false);
        let linked_all = ctx
            .process_context_mut()
            .sat_all_linked_successor_individual_concepts_extension_data(all_ext, succ_node, false);
        let role_ext = ctx
            .process_context_mut()
            .sat_role_successor_all_concept_extension_data(linked_all, creation_role, false);
        let role_ext_ref = ctx
            .process_context()
            .sat_successor_all_concept_ext_data(role_ext);
        assert_eq!(role_ext_ref.required_successor_count, 3);
        assert!(role_ext_ref.is_extension_processing_queued());
        assert_eq!(
            ctx.process_context()
                .sat_indi_node_all_concept_ext_data(all_ext)
                .get_extension_process_data_linker(),
            role_ext
        );
        let map = ctx
            .process_context()
            .sat_successor_concept_extension_map(role_ext_ref.get_successor_concept_extension_map())
            .get_successor_concept_extension_map();
        assert!(map.get(&656).unwrap().positive);
        let succ_ext = ctx
            .process_context()
            .linked_role_sat_succ_data(succ_data)
            .extension_data;
        assert_eq!(
            ctx.process_context()
                .sat_succ_ext_data(succ_ext)
                .get_last_examined_link_linker(),
            succ
        );
        assert_eq!(
            ctx.process_context()
                .sat_succ_ext_data(succ_ext)
                .get_last_examined_all_concept_reapply_descriptor(),
            reapply
        );
    }

    #[test]
    fn s06_update_all_dispatcher_clears_role_processing_flags() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 659);
        let operand = atom(&mut ctx, 660);
        let mut all_concept = Concept::new();
        all_concept
            .set_operator_code(CCALL)
            .add_operand_linker(operand, false)
            .set_operand_count(1);
        let all_concept = ctx.ontology_arenas_mut().alloc_concept(all_concept);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(661));
        let succ_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(662));
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data =
            ctx.process_context_mut()
                .linked_role_successor_data(linked_hash, role, true);
        let succ = active_successor(&mut ctx, 1);
        {
            let succ_ref = ctx.process_context_mut().sat_succ_data_mut(succ);
            succ_ref.succ_indi_node = succ_node;
            succ_ref
                .creation_role_linker
                .push(super::super::super::model::substrate::NegLink {
                    target: role,
                    negated: false,
                });
        }
        {
            let succ_data_ref = ctx
                .process_context_mut()
                .linked_role_sat_succ_data_mut(succ_data);
            succ_data_ref.set_last_successor_link_data(succ);
            succ_data_ref.role_all_concepts_processing_queued = true;
        }
        let mut descriptor = super::super::satellites::ConceptSaturationDescriptor::new();
        descriptor.init_concept_saturation_descriptor(all_concept, false);
        let descriptor = ctx.process_context_mut().alloc_con_sat_desc(descriptor);
        let mut reapply =
            super::super::satellites::BackwardSaturationPropagationReapplyDescriptor::new();
        reapply.init_backward_propagation_reapply_descriptor(descriptor);
        let reapply = ctx
            .process_context_mut()
            .alloc_backward_sat_prop_reapply_desc(reapply);
        let back_hash = ctx
            .process_context_mut()
            .sat_node_role_backward_propagation_hash(node, true);
        {
            let back_data = ctx
                .process_context_mut()
                .role_backward_sat_prop_hash_mut(back_hash)
                .get_role_backward_propagation_data_hash_mut()
                .entry(role)
                .or_default();
            back_data.reapply_linker = reapply;
            back_data.role_all_concepts_processing_queued = true;
        }

        algo.update_successor_role_all_concepts_extensions(&mut node, role, &mut ctx);

        assert!(
            !ctx.process_context()
                .linked_role_sat_succ_data(succ_data)
                .role_all_concepts_processing_queued
        );
        assert!(
            !ctx.process_context()
                .role_backward_sat_prop_hash(back_hash)
                .get_role_backward_propagation_data_hash()
                .get(&role)
                .unwrap()
                .role_all_concepts_processing_queued
        );
    }

    #[test]
    fn s06_update_all_extensions_rewires_positive_super_role() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 663);
        add_self_indirect_super_role(&mut ctx, role);
        let operand = atom(&mut ctx, 664);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(665));
        let succ_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(666));
        ctx.process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let all_ext = ctx
            .process_context_mut()
            .sat_node_all_concepts_extension_data(node, true);
        let linked = ctx
            .process_context_mut()
            .sat_all_linked_successor_individual_concepts_extension_data(all_ext, succ_node, true);
        let role_ext = ctx
            .process_context_mut()
            .sat_role_successor_all_concept_extension_data(linked, role, true);
        let map = ctx
            .process_context()
            .sat_successor_all_concept_ext_data(role_ext)
            .get_successor_concept_extension_map();
        ctx.process_context_mut()
            .sat_successor_concept_extension_map_mut(map)
            .add_extension_concept(operand, false, 664);
        ctx.process_context_mut()
            .sat_successor_all_concept_ext_data_mut(role_ext)
            .add_required_successor_cardinality(2);
        ctx.process_context_mut()
            .sat_successor_all_concept_ext_data_mut(role_ext)
            .set_extension_processing_queued(true);
        ctx.process_context_mut()
            .sat_indi_node_all_concept_ext_data_mut(all_ext)
            .add_extension_process_data(role_ext);

        assert!(algo.update_successor_all_concepts_extensions(&mut node, &mut ctx));

        let resolved = ctx
            .process_context()
            .sat_successor_all_concept_ext_data(role_ext)
            .get_last_resolved_individual_node();
        assert!(resolved.is_some());
        assert_ne!(resolved, succ_node);
        assert_eq!(
            ctx.process_context()
                .sat_successor_all_concept_ext_data(role_ext)
                .get_last_connected_successor_cardinality(),
            2
        );
        assert!(!ctx
            .process_context()
            .sat_successor_all_concept_ext_data(role_ext)
            .is_extension_processing_queued());
        assert!(ctx
            .process_context()
            .sat_node(resolved)
            .get_non_inverse_connected_individual_node_linker()
            .contains(&node));
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, false);
        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                linked_hash,
                role,
                resolved,
                Some(role),
                2,
            ));
    }

    #[test]
    fn s06_update_all_extensions_installs_backward_link_for_negated_super_role() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role_id = role(&mut ctx, 667);
        let super_role = role(&mut ctx, 668);
        add_negated_indirect_super_role(&mut ctx, role_id, super_role);
        let operand = atom(&mut ctx, 669);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(670));
        let succ_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(671));
        ctx.process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let all_ext = ctx
            .process_context_mut()
            .sat_node_all_concepts_extension_data(node, true);
        let linked = ctx
            .process_context_mut()
            .sat_all_linked_successor_individual_concepts_extension_data(all_ext, succ_node, true);
        let role_ext = ctx
            .process_context_mut()
            .sat_role_successor_all_concept_extension_data(linked, role_id, true);
        let map = ctx
            .process_context()
            .sat_successor_all_concept_ext_data(role_ext)
            .get_successor_concept_extension_map();
        ctx.process_context_mut()
            .sat_successor_concept_extension_map_mut(map)
            .add_extension_concept(operand, false, 669);
        ctx.process_context_mut()
            .sat_successor_all_concept_ext_data_mut(role_ext)
            .add_required_successor_cardinality(1);
        ctx.process_context_mut()
            .sat_successor_all_concept_ext_data_mut(role_ext)
            .set_extension_processing_queued(true);
        ctx.process_context_mut()
            .sat_indi_node_all_concept_ext_data_mut(all_ext)
            .add_extension_process_data(role_ext);

        assert!(algo.update_successor_all_concepts_extensions(&mut node, &mut ctx));

        let resolved = ctx
            .process_context()
            .sat_successor_all_concept_ext_data(role_ext)
            .get_last_resolved_individual_node();
        assert!(resolved.is_some());
        let back_hash = ctx.process_context().sat_node(resolved).role_back_prop_hash;
        let back_data = ctx
            .process_context()
            .role_backward_sat_prop_hash(back_hash)
            .get_role_backward_propagation_data_hash()
            .get(&super_role)
            .expect("negated super-role should install backward propagation data");
        assert_eq!(
            ctx.process_context()
                .backward_sat_prop_link(back_data.link_linker)
                .get_source_individual(),
            node
        );
        assert!(!ctx
            .process_context()
            .sat_node(resolved)
            .get_non_inverse_connected_individual_node_linker()
            .contains(&node));
    }

    #[test]
    fn s06_update_functional_worker_ignores_only_value_nominal_successors() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 661);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(663));
        ctx.process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data = ctx.process_context_mut().alloc_linked_role_sat_succ_data(
            super::super::satellites::LinkedRoleSaturationSuccessorData::new(),
        );
        let succ_a = active_successor(&mut ctx, 1);
        let succ_b = active_successor(&mut ctx, 1);
        ctx.process_context_mut()
            .sat_succ_data_mut(succ_a)
            .set_next(succ_b);
        ctx.process_context_mut()
            .sat_succ_data_mut(succ_a)
            .value_nominal_connection = true;
        ctx.process_context_mut()
            .sat_succ_data_mut(succ_b)
            .value_nominal_connection = true;
        ctx.process_context_mut()
            .linked_role_sat_succ_data_mut(succ_data)
            .set_last_successor_link_data(succ_a);

        assert!(
            !algo.update_successor_role_functional_concepts_extensions_for_succ_data(
                &mut node, role, succ_data, &mut ctx
            )
        );
    }

    #[test]
    fn s06_update_functional_worker_stops_when_max_cardinality_exceeds_one() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 671);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(673));
        ctx.process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data = ctx.process_context_mut().alloc_linked_role_sat_succ_data(
            super::super::satellites::LinkedRoleSaturationSuccessorData::new(),
        );
        let succ_a = active_successor(&mut ctx, 1);
        let succ_b = active_successor(&mut ctx, 2);
        ctx.process_context_mut()
            .sat_succ_data_mut(succ_a)
            .set_next(succ_b);
        ctx.process_context_mut()
            .linked_role_sat_succ_data_mut(succ_data)
            .set_last_successor_link_data(succ_a);

        assert!(
            !algo.update_successor_role_functional_concepts_extensions_for_succ_data(
                &mut node, role, succ_data, &mut ctx
            )
        );
    }

    #[test]
    fn s06_update_functional_worker_obeys_last_examined_cursor() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 681);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(683));
        ctx.process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data = ctx.process_context_mut().alloc_linked_role_sat_succ_data(
            super::super::satellites::LinkedRoleSaturationSuccessorData::new(),
        );
        let succ_a = active_successor(&mut ctx, 1);
        ctx.process_context_mut()
            .linked_role_sat_succ_data_mut(succ_data)
            .set_last_successor_link_data(succ_a);
        let functional_ext = ctx
            .process_context_mut()
            .sat_node_functional_concepts_extension_data(node, true);
        let role_func_data = ctx
            .process_context_mut()
            .sat_functional_successor_concepts_extension_data(functional_ext, role, true);
        ctx.process_context_mut()
            .sat_successor_functional_concept_ext_data_mut(role_func_data)
            .set_last_examined_linked_successor_data(succ_a);

        assert!(
            !algo.update_successor_role_functional_concepts_extensions_for_succ_data(
                &mut node, role, succ_data, &mut ctx
            )
        );
        assert_eq!(
            ctx.process_context()
                .sat_successor_functional_concept_ext_data(role_func_data)
                .get_last_examined_linked_successor_data(),
            succ_a
        );
    }

    #[test]
    fn s06_install_backward_propagation_link_prepends_and_deduplicates_head_source() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 685);
        let source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(686));
        let dest = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(687));
        let mut link = BackwardSaturationPropagationLink::new();
        link.init_backward_propagation_link(source, role);
        let link = ctx.process_context_mut().alloc_backward_sat_prop_link(link);

        assert!(
            algo.install_backward_propagation_link(source, dest, role, link, true, true, &mut ctx)
        );
        let hash = ctx.process_context().sat_node(dest).role_back_prop_hash;
        let head = ctx
            .process_context()
            .role_backward_sat_prop_hash(hash)
            .get_role_backward_propagation_data_hash()
            .get(&role)
            .unwrap()
            .link_linker;
        assert_eq!(head, link);
        assert_eq!(
            ctx.process_context()
                .backward_sat_prop_link(head)
                .get_source_individual(),
            source
        );

        let mut duplicate = BackwardSaturationPropagationLink::new();
        duplicate.init_backward_propagation_link(source, role);
        let duplicate = ctx
            .process_context_mut()
            .alloc_backward_sat_prop_link(duplicate);
        assert!(!algo.install_backward_propagation_link(
            source, dest, role, duplicate, true, true, &mut ctx
        ));
        assert_eq!(
            ctx.process_context()
                .role_backward_sat_prop_hash(hash)
                .get_role_backward_propagation_data_hash()
                .get(&role)
                .unwrap()
                .link_linker,
            link
        );
    }

    #[test]
    fn s06_install_backward_propagation_link_queues_functional_predecessor_role() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 688);
        let source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(689));
        let dest = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(690));
        let hash = ctx
            .process_context_mut()
            .sat_node_role_backward_propagation_hash(dest, true);
        ctx.process_context_mut()
            .role_backward_sat_prop_hash_mut(hash)
            .get_role_backward_propagation_data_hash_mut()
            .entry(role)
            .or_default()
            .role_predecessor_merging_queuing_required = true;
        let functional_ext = ctx
            .process_context_mut()
            .sat_node_functional_concepts_extension_data(dest, true);
        ctx.process_context_mut()
            .sat_indi_node_functional_concept_ext_data_mut(functional_ext)
            .set_successor_extension_initialized(true);
        let mut link = BackwardSaturationPropagationLink::new();
        link.init_backward_propagation_link(source, role);
        let link = ctx.process_context_mut().alloc_backward_sat_prop_link(link);

        assert!(
            algo.install_backward_propagation_link(source, dest, role, link, true, true, &mut ctx)
        );

        let data = ctx
            .process_context()
            .role_backward_sat_prop_hash(hash)
            .get_role_backward_propagation_data_hash()
            .get(&role)
            .unwrap();
        assert!(data.role_predecessor_merging_processing_queued);
        let predecessor_linker = ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(functional_ext)
            .linked_predecessor_added_role_process_linker;
        assert_eq!(
            ctx.process_context()
                .role_sat_proc_linker(predecessor_linker)
                .get_role(),
            role
        );
    }

    #[test]
    fn s06_install_backward_propagation_link_replays_reapply_descriptor_operands() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 692);
        let operand = atom(&mut ctx, 694);
        let reapply_concept = concept_with_operand(&mut ctx, 696, operand, false);
        let source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(698));
        let dest = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(700));
        let source_label = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(source, true);
        let mut descriptor = super::super::satellites::ConceptSaturationDescriptor::new();
        descriptor.init_concept_saturation_descriptor(reapply_concept, true);
        let descriptor = ctx.process_context_mut().alloc_con_sat_desc(descriptor);
        let mut reapply =
            super::super::satellites::BackwardSaturationPropagationReapplyDescriptor::new();
        reapply.init_backward_propagation_reapply_descriptor(descriptor);
        let reapply = ctx
            .process_context_mut()
            .alloc_backward_sat_prop_reapply_desc(reapply);
        let hash = ctx
            .process_context_mut()
            .sat_node_role_backward_propagation_hash(dest, true);
        ctx.process_context_mut()
            .role_backward_sat_prop_hash_mut(hash)
            .get_role_backward_propagation_data_hash_mut()
            .entry(role)
            .or_default()
            .reapply_linker = reapply;
        let mut link = BackwardSaturationPropagationLink::new();
        link.init_backward_propagation_link(source, role);
        let link = ctx.process_context_mut().alloc_backward_sat_prop_link(link);

        assert!(
            algo.install_backward_propagation_link(source, dest, role, link, true, false, &mut ctx)
        );

        let mut added_descriptor = super::super::satellites::ConceptSaturationDescriptorId::NONE;
        let mut imp_reapply =
            super::super::satellites::ImplicationReapplyConceptSaturationDescriptorId::NONE;
        let operand_tag = ctx.ontology_arenas().concept(operand).get_concept_tag();
        assert!(ctx
            .process_context()
            .reapply_con_sat_label_set(source_label)
            .get_concept_saturation_descriptor_by_tag(
                operand_tag,
                &mut added_descriptor,
                &mut imp_reapply,
            ));
        assert!(ctx
            .process_context()
            .con_sat_desc(added_descriptor)
            .get_negation());
    }

    #[test]
    fn s06_update_predecessor_functional_clears_processing_flag_and_dispatches_to_boundary() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 711);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(713));
        let pred = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(715));
        let succ_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(717));
        let mut back_link = BackwardSaturationPropagationLink::new();
        back_link.init_backward_propagation_link(pred, role);
        let back_link = ctx
            .process_context_mut()
            .alloc_backward_sat_prop_link(back_link);
        let back_hash = ctx
            .process_context_mut()
            .sat_node_role_backward_propagation_hash(node, true);
        {
            let data = ctx
                .process_context_mut()
                .role_backward_sat_prop_hash_mut(back_hash)
                .get_role_backward_propagation_data_hash_mut()
                .entry(role)
                .or_default();
            data.role_predecessor_merging_queuing_required = true;
            data.role_predecessor_merging_processing_queued = true;
            data.link_linker = back_link;
        }
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data =
            ctx.process_context_mut()
                .linked_role_successor_data(linked_hash, role, true);
        let active_succ = active_successor(&mut ctx, 1);
        ctx.process_context_mut()
            .sat_succ_data_mut(active_succ)
            .succ_indi_node = succ_node;
        {
            let succ_data_ref = ctx
                .process_context_mut()
                .linked_role_sat_succ_data_mut(succ_data);
            succ_data_ref.set_successor_count(1);
            succ_data_ref.set_last_successor_link_data(active_succ);
        }

        assert!(
            !algo.update_predecessor_role_functional_concepts_extensions(&mut node, role, &mut ctx)
        );

        let data = ctx
            .process_context()
            .role_backward_sat_prop_hash(back_hash)
            .get_role_backward_propagation_data_hash()
            .get(&role)
            .unwrap();
        assert!(data.role_predecessor_merging_queuing_required);
        assert!(!data.role_predecessor_merging_processing_queued);
    }

    #[test]
    fn s06_update_functional_worker_builds_and_releases_merge_linker_head() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = role(&mut ctx, 691);
        add_self_indirect_super_role(&mut ctx, role);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(693));
        ctx.process_context_mut()
            .sat_node_mut(node)
            .init_individual_saturation_process_node(693, Id::NONE, Id::NONE);
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data =
            ctx.process_context_mut()
                .linked_role_successor_data(linked_hash, role, true);
        let succ_node_a = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(695));
        let succ_node_b = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(697));
        ctx.process_context_mut()
            .sat_node_mut(succ_node_a)
            .init_individual_saturation_process_node(695, Id::NONE, Id::NONE);
        ctx.process_context_mut()
            .sat_node_mut(succ_node_b)
            .init_individual_saturation_process_node(697, Id::NONE, Id::NONE);
        set_sat_label_count(&mut ctx, succ_node_a, 1);
        set_sat_label_count(&mut ctx, succ_node_b, 3);
        let succ_a = active_successor(&mut ctx, 1);
        let succ_b = active_successor(&mut ctx, 1);
        {
            let succ_a_ref = ctx.process_context_mut().sat_succ_data_mut(succ_a);
            succ_a_ref.set_next(succ_b);
            succ_a_ref.succ_indi_node = succ_node_a;
            succ_a_ref
                .creation_role_linker
                .push(super::super::super::model::substrate::NegLink {
                    target: role,
                    negated: false,
                });
        }
        {
            let succ_b_ref = ctx.process_context_mut().sat_succ_data_mut(succ_b);
            succ_b_ref.succ_indi_node = succ_node_b;
            succ_b_ref
                .creation_role_linker
                .push(super::super::super::model::substrate::NegLink {
                    target: role,
                    negated: false,
                });
        }
        {
            let succ_data_ref = ctx
                .process_context_mut()
                .linked_role_sat_succ_data_mut(succ_data);
            succ_data_ref.set_last_successor_link_data(succ_a);
            succ_data_ref
                .get_successor_node_data_map_mut()
                .insert(695, succ_a);
            succ_data_ref
                .get_successor_node_data_map_mut()
                .insert(697, succ_b);
        }

        assert!(
            algo.update_successor_role_functional_concepts_extensions_for_succ_data(
                &mut node, role, succ_data, &mut ctx
            )
        );
        let released_head = ctx
            .processing_data_box()
            .remaining_individual_successor_link_data_linker();
        assert!(released_head.is_some());
        let released_head_ref = ctx
            .process_context()
            .indi_sat_succ_link_data_linker(released_head);
        assert_eq!(released_head_ref.get_data(), succ_b);
        assert!(released_head_ref.get_next().is_none());
        let functional_ext = ctx
            .process_context_mut()
            .sat_node_functional_concepts_extension_data(node, false);
        let role_func_data = ctx
            .process_context_mut()
            .sat_functional_successor_concepts_extension_data(functional_ext, role, false);
        let resolved_node = ctx
            .process_context()
            .sat_successor_functional_concept_ext_data(role_func_data)
            .get_last_resolved_individual_node();
        assert_eq!(resolved_node, succ_node_a);
        assert_ne!(resolved_node, succ_node_b);
        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                linked_hash,
                role,
                succ_node_a,
                Some(role),
                1,
            ));
        assert!(!ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                linked_hash,
                role,
                succ_node_b,
                Some(role),
                1,
            ));
        assert_eq!(
            ctx.process_context()
                .sat_succ_data(succ_b)
                .get_active_count(),
            0
        );
    }

    #[test]
    fn s06_update_functional_worker_installs_backward_link_for_negated_creation_super_role() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role_id = role(&mut ctx, 701);
        let creation_role = role(&mut ctx, 702);
        let super_role = role(&mut ctx, 703);
        add_negated_indirect_super_role(&mut ctx, creation_role, super_role);
        let mut node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(705));
        ctx.process_context_mut()
            .sat_node_mut(node)
            .init_individual_saturation_process_node(705, Id::NONE, Id::NONE);
        let linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(node, true);
        let succ_data =
            ctx.process_context_mut()
                .linked_role_successor_data(linked_hash, role_id, true);
        let succ_node_a = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(707));
        let succ_node_b = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(709));
        ctx.process_context_mut()
            .sat_node_mut(succ_node_a)
            .init_individual_saturation_process_node(707, Id::NONE, Id::NONE);
        ctx.process_context_mut()
            .sat_node_mut(succ_node_b)
            .init_individual_saturation_process_node(709, Id::NONE, Id::NONE);
        set_sat_label_count(&mut ctx, succ_node_a, 2);
        set_sat_label_count(&mut ctx, succ_node_b, 1);
        let succ_a = active_successor(&mut ctx, 1);
        let succ_b = active_successor(&mut ctx, 1);
        {
            let succ_a_ref = ctx.process_context_mut().sat_succ_data_mut(succ_a);
            succ_a_ref.set_next(succ_b);
            succ_a_ref.succ_indi_node = succ_node_a;
            succ_a_ref
                .creation_role_linker
                .push(super::super::super::model::substrate::NegLink {
                    target: creation_role,
                    negated: false,
                });
        }
        {
            let succ_b_ref = ctx.process_context_mut().sat_succ_data_mut(succ_b);
            succ_b_ref.succ_indi_node = succ_node_b;
            succ_b_ref
                .creation_role_linker
                .push(super::super::super::model::substrate::NegLink {
                    target: creation_role,
                    negated: false,
                });
        }
        {
            let succ_data_ref = ctx
                .process_context_mut()
                .linked_role_sat_succ_data_mut(succ_data);
            succ_data_ref.set_last_successor_link_data(succ_a);
            succ_data_ref
                .get_successor_node_data_map_mut()
                .insert(707, succ_a);
            succ_data_ref
                .get_successor_node_data_map_mut()
                .insert(709, succ_b);
        }

        assert!(
            algo.update_successor_role_functional_concepts_extensions_for_succ_data(
                &mut node, role_id, succ_data, &mut ctx
            )
        );

        let resolved_node = {
            let functional_ext = ctx
                .process_context_mut()
                .sat_node_functional_concepts_extension_data(node, false);
            let role_func_data = ctx
                .process_context_mut()
                .sat_functional_successor_concepts_extension_data(functional_ext, role_id, false);
            ctx.process_context()
                .sat_successor_functional_concept_ext_data(role_func_data)
                .get_last_resolved_individual_node()
        };
        assert_eq!(resolved_node, succ_node_a);
        let hash = ctx
            .process_context()
            .sat_node(resolved_node)
            .role_back_prop_hash;
        let head = ctx
            .process_context()
            .role_backward_sat_prop_hash(hash)
            .get_role_backward_propagation_data_hash()
            .get(&super_role)
            .unwrap()
            .link_linker;
        assert_eq!(
            ctx.process_context()
                .backward_sat_prop_link(head)
                .get_source_individual(),
            node
        );
        assert_eq!(
            ctx.process_context()
                .backward_sat_prop_link(head)
                .get_link_role(),
            super_role
        );
        assert!(!ctx
            .process_context()
            .sat_node(resolved_node)
            .has_non_inverse_connected_individual_node_linker());
    }
}
