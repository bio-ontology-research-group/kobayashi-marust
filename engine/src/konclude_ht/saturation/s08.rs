//! `saturation::s08` — ATMOST / cardinality successor merging
//! (saturation port unit #8 of 12; manifest `03-saturation-calc.md`, "PU-SAT-8",
//! group G — the SHIQ-hard cardinality-merging core).
//!
//! Faithful port of the **group-G** methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
//! — the ATMOST/at-most successor-merging machinery, including the group-G
//! `getInverseRole` / `createAncestorSuccessorMergingExtension` / merge-subset
//! predicates that the group-F unit (`s06`) explicitly excluded as belonging here.
//!
//! Methods (cpp order; the trailing `CCalculationAlgorithmContextBase*` elided):
//!   * `getInverseRole`                                      [1175–1197]  (LIVE)
//!   * `createAncestorSuccessorMergingExtension`             [1202–1292]
//!   * `isLinkedIndividualSuccessorNodeMergingSubset(data)`  [1335–1339]
//!   * `isLinkedIndividualSuccessorNodeMergingSubset(nodes)` [1343–1366]  `_for_nodes`
//!   * `isSuccessorCreationRoleMergingSubset(linker)`        [1370–1380]
//!   * `isSuccessorCreationRoleMergingSubset(role)`          [1382–1391]  `_for_role`
//!   * `isIndividualNodeLabelMergingSubset`                  [1393–1416]
//!   * `deactivateSubsetMergeableSuccessorLinks`            [1421–1473]
//!   * `markNominalATMOSTRestrictedAncestorsAsInsufficient`  [2824–2848]
//!   * `markATMOSTRestrictedAncestorsAsInsufficient`         [2852–2930]
//!   * `collectATMOSTConceptRelevantSuccessors`              [3779–3961]
//!   * `tryATMOSTConceptSuccessorMerging`                    [3969–4027]
//!   * `reconnectMergedLinkedSuccessors`                     [4034–4131]
//!   * `testMergedSuccessorLinkingProblematic`               [4136–4247]
//!   * `tryIndividiualATMOSTConceptSuccessorMerging`         [4250–4453]  (C++ typo preserved)
//!   * `isIndividualSuccessorLinkCardinalityMergeable(data)` [4467–4471]
//!   * `isIndividualSuccessorLinkCardinalityMergeable(nodes)`[4473–4493] `_for_nodes`
//!   * `getSuccessorLinkSimplyMergeableCardinalityCount`     [4498–4580]
//!   * `isIndividualSuccessorLinkCardinalityExtendedMergeable(data)`  [4599–4603]
//!   * `isIndividualSuccessorLinkCardinalityExtendedMergeable(nodes)` [4605–4635] `_for_nodes`
//!   * `getIndividualNodeQualifiedSuccessorCount`            [4637–4713]
//!   * `isIndividualNodeLabelMergingProblematic`             [4716–4803]
//!   * `getSuccessorLinkExtendedMergeableCardinalityCount`   [4808–4831]
//!
//! ## Context convention
//!
//! The saturation `.h` declares every method with the SHARED
//! `CCalculationAlgorithmContextBase* calcAlgContext` (NOT a distinct saturation
//! context), so per `PORT.md` the port threads
//! `calc_alg_context: &mut super::super::completion::context::CalculationAlgorithmContextBase`.
//! Saturation nodes resolve through `ctx.process_context().sat_node(id)` / `_mut`;
//! the per-test databox through `ctx.processing_data_box()` / `_mut`; the static
//! TBox/RBox roles/concepts through `ctx.ontology_arenas()`. The member back-handle
//! `mCalcAlgContext` aliases the passed `calcAlgContext` (same object); the port
//! routes all access through the parameter. Sibling methods are `self.x(...)`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member, so `&mut self`. A
//! `CIndividualSaturationProcessNode*&` in/out reference becomes `&mut SatNodeId`;
//! a by-value `CIndividualSaturationProcessNode*` becomes `SatNodeId`; `CRole*` →
//! `RoleId`. `cint64&` / `bool&` out-params become `&mut Cint64` / `&mut bool`;
//! a `CSaturationSuccessorData**` out-pointer stays opaque until the merge-distinct
//! containers are ported.
//!
//! KONCLUDE-PORT-NOTE[overload]: C++ overloads (Rust cannot) are disambiguated by
//! a suffix on the worker overload — `_for_nodes` (the explicit-node merge-subset /
//! cardinality-mergeable workers) and `_for_role` (the single-role creation-role
//! subset worker). The short dispatcher keeps the plain name and calls the worker,
//! mirroring the s06 `_for_succ_data` and completion-layer `_by_id` conventions.
//!
//! ## Deferral landscape
//!
//! Like the group-F unit, this whole cardinality-merging core sits on the
//! not-yet-ported **successor-extension / merging satellite tower** (no Rust struct
//! yet — only `process::stubs` / manifest markers). Every body but `getInverseRole`
//! immediately dereferences one or more of:
//!   * `CSaturationSuccessorData` (`mSuccIndiNode` / `mActiveCount` / `mSuccCount` /
//!     `mCreationRoleLinker` / `mVALUENominalConnection` / `mVALUENominalID` /
//!     `mSuccNodeDataMap`), `CLinkedRoleSaturationSuccessorData` / `...Hash`;
//!   * `CSaturationATMOSTSuccessorMergingData` / `CSaturationATMOSTSuccessorMergingHashData`
//!     (the merging worklist + found/mergeable/min cardinalities + distinct hash/set
//!     + remaining-mergeable-cardinality hash);
//!   * `CIndividualSaturationSuccessorLinkDataLinker` (the merge link-data chain) +
//!     `CSaturationIndividualNodeExtensionResolveData` / `...SuccessorExtensionData` /
//!     `...FUNCTIONALConceptsExtensionData`;
//!   * `CRoleBackwardSaturationPropagationHash(Data)` / `CBackwardSaturationPropagationLink`
//!     / `CBackwardSaturationPropagationReapplyDescriptor`;
//!   * `CReapplyConceptSaturationLabelSet` / `CConceptSaturationDescriptor` /
//!     `CCriticalPredecessorRoleCardinalityHash` / `CSaturationConceptDataItem` /
//!     `CConceptRoleBranchingTrigger`;
//! and on sibling methods owned by OTHER saturation units: `collectLinkedSuccessorNodes`,
//! `addConceptFilteredToIndividual`, `preprocessResolvedIndividualNode`,
//! `addNewLinkedExtensionProcessingRole`, `installBackwardPropagationLink`,
//! `getResolvedIndividualNodeExtension`, `getCorrectedNode`,
//! `updateDirectAddingIndividualStatusFlags`, `setInsufficientNodeOccured`,
//! `addCriticalConceptForDependentNodes`, `createIndividualSaturationSuccessorLinkDataLinker`,
//! `testAutomateTransitionOperandsAddable`.
//!
//! Following the convention (`s06`, `completion::u17`): each deferred method below
//! carries the faithful name + signature + context threading, and a `// W4-DEFER[api]`
//! body that transcribes the C++ control flow structurally so a later wave fills it
//! without re-reading the source. Unported satellite/sibling handles appear as
//! opaque `Cint64` (`INVALID` == the C++ `nullptr`). Logic is documented, never
//! dropped. Only `getInverseRole` (pure `CRole` model logic) is ported LIVE.
//!
//! ## Post-W4.5 reconcile status (saturation un-defer wave)
//!
//! Re-evaluated after the W4.5 saturation satellites + node-resolution +
//! dependency-factory landed: **no group-G method un-defers in this wave.** Every
//! body but `getInverseRole` still sits on at least one part of the merging tower
//! that is NOT yet ported, so all `// W4-DEFER[api]` bodies stay faithful skeletons.
//! The narrowed, still-missing blockers (what each remaining un-defer is waiting on):
//!   * the **ATMOST merging satellites** — `CSaturationATMOSTSuccessorMergingData` /
//!     `...HashData` (merged linked-successor hash, merge-distinct hash/set, the
//!     remaining-mergeable-cardinality hash) and the databox ATMOST-merging
//!     process-linker queue (`hasSaturationATMOSTMergingProcessLinker`);
//!   * the **ATMOST mutating merge surface** beyond subset deactivation —
//!     `increaseLinkedSuccessorCount` and the process-owned merge-distinct multimap
//!     view needed to wire the larger group-G bodies into live `tryIndividiual...`.
//!   * the **FUNCTIONAL/ALL successor-extension data** + `getRoleBackwardPropagationHash`
//!     + `CCriticalPredecessorRoleCardinalityHash` (all still opaque `Cint64` in sat1);
//!   * the **deep** `CReapplyConceptSaturationLabelSet` bodies (`containsConcept`,
//!     `getConceptDescriptorAndReapplyQueue`) — only simple accessors are ported;
//!   * the **status-flag masks** are now available on
//!     `IndividualSaturationProcessNodeStatusFlags` (see the focused sat1
//!     regression for `INDSATFLAGINSUFFICIENT` / `hasInsufficientFlag` /
//!     `hasClashedFlag`); no longer a group-G blocker.
//! No live (non-deferred) site calls these group-G methods, so the signatures stay
//! as-is until that coordinated reconcile.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::op::{
    CCAND, CCAQAND, CCATLEAST, CCATMOST, CCATOM, CCBRANCHAQAND, CCF_ATLEAST, CCF_ATMOST, CCF_SELF,
    CCFS_AQALL_TYPE, CCFS_SOME_TYPE, CCIMPLAQAND, CCOR, CCSUB,
};
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, NegLink, RoleId};
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::SatNodeId;
use super::satellites::{
    BackwardSaturationPropagationLink, BackwardSaturationPropagationLinkId,
    ConceptSaturationDescriptorId, ImplicationReapplyConceptSaturationDescriptorId,
    IndividualSaturationSuccessorLinkDataLinkerId, LinkedRoleSaturationSuccessorDataId,
    LinkedRoleSaturationSuccessorHashId, ReapplyConceptSaturationLabelSetId,
    SaturationSuccessorDataId,
};

const CCT_ATMOST: Cint64 = 1;

impl super::algorithm::SaturationTaskHandleAlgorithm {
    // =======================================================================
    // Inverse-role resolution (cpp 1175–1197). PORTED LIVE — pure CRole logic.
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getInverseRole`.
    /// cpp 1175–1197.
    ///
    /// Resolves `role`'s inverse: the explicit inverse if present, otherwise a
    /// negated (== inverse) entry of its inverse-equivalent-role list, otherwise a
    /// negated indirect super-role whose own indirect super-role list contains
    /// `role` negated (the role inverse reachable through the super-role lattice).
    /// Returns `RoleId::NONE` (== `nullptr`) when none is found.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the `CSortedNegLinker<CRole*>` chains are the
    /// model's `Vec<NegLink<RoleId>>`; each list is snapshotted with `.to_vec()`
    /// before iterating so the nested inner-role borrow does not alias the outer
    /// borrow of `calc_alg_context` (behaviour identical, matching `s03`).
    pub fn get_inverse_role(
        &mut self,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> RoleId {
        let mut inv_role: RoleId = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_inverse_role();
        if inv_role.is_none() {
            let inv_eq_role_list = calc_alg_context
                .ontology_arenas()
                .role(role)
                .get_inverse_equivalent_role_list()
                .to_vec();
            for inv_eq_role_linker_it in &inv_eq_role_list {
                if inv_role.is_some() {
                    break;
                }
                if inv_eq_role_linker_it.negated {
                    inv_role = inv_eq_role_linker_it.target;
                }
            }
        }
        if inv_role.is_none() {
            // KONCLUDE-PORT-NOTE[identity]: self-inclusive super-role list (see s02).
            let super_role_list =
                Self::saturation_indirect_super_roles(role, calc_alg_context);
            for inv_super_role_linker_it in &super_role_list {
                if inv_role.is_some() {
                    break;
                }
                if inv_super_role_linker_it.negated {
                    let inv_super_role = inv_super_role_linker_it.target;
                    // KONCLUDE-PORT-NOTE[identity]: self-inclusive super-role list (see s02).
                    let super_super_role_list =
                        Self::saturation_indirect_super_roles(inv_super_role, calc_alg_context);
                    for super_super_role_linker_it in &super_super_role_list {
                        if inv_role.is_some() {
                            break;
                        }
                        if super_super_role_linker_it.negated
                            && super_super_role_linker_it.target == role
                        {
                            inv_role = inv_super_role;
                        }
                    }
                }
            }
        }
        inv_role
    }

    // =======================================================================
    // Ancestor↔successor functional-merging extension (cpp 1202–1292).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::createAncestorSuccessorMergingExtension`.
    /// cpp 1202–1292.
    ///
    /// When a functional role forces a successor and an ancestor of `indiProcSatNode`
    /// to coincide, forwards the successor node's label onto the ancestor and rewires
    /// the ancestor's inverse-role successor links toward `indiProcSatNode` (adding
    /// extension successors on non-negated inverse-creation-super-roles, installing a
    /// backward-propagation link on negated ones), recording the forwarding on the
    /// successor's FUNCTIONAL-concepts extension data so it happens once per
    /// (ancestor, creation-role). Returns whether anything was newly forwarded.
    pub fn create_ancestor_successor_merging_extension(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        // `CIndividualSaturationProcessNode* succSatNode`
        succ_sat_node: SatNodeId,
        // `CIndividualSaturationProcessNode* ancSatNode`
        anc_sat_node: SatNodeId,
        // `CXNegLinker<CRole*>* creationRoleLinker` — satellite-owned linker.
        creation_role_linker: Vec<NegLink<RoleId>>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut anc_sat_node_ref = anc_sat_node;
        self.collect_linked_successor_nodes(&mut anc_sat_node_ref, calc_alg_context, INVALID);
        let inv_role = self.get_inverse_role(role, calc_alg_context);
        let anc_linked_succ_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(anc_sat_node, true);
        let mut anc_succ_link_data = SaturationSuccessorDataId::NONE;
        if anc_linked_succ_hash.is_some() {
            let anc_succ_data = calc_alg_context
                .process_context()
                .linked_role_sat_succ_hash(anc_linked_succ_hash)
                .get_linked_role_successor_data(inv_role);
            if anc_succ_data.is_some() {
                let indi_id = calc_alg_context
                    .process_context()
                    .sat_node(*indi_proc_sat_node)
                    .get_individual_id();
                anc_succ_link_data = calc_alg_context
                    .process_context()
                    .linked_role_sat_succ_data(anc_succ_data)
                    .get_successor_node_data_map()
                    .get(&indi_id)
                    .copied()
                    .unwrap_or(SaturationSuccessorDataId::NONE);
            }
        }

        if anc_succ_link_data.is_some()
            && calc_alg_context
                .process_context()
                .sat_succ_data(anc_succ_link_data)
                .get_active_count()
                >= 1
        {
            let mut updated = false;
            let func_con_ext_data = calc_alg_context
                .process_context_mut()
                .sat_node_functional_concepts_extension_data(succ_sat_node, true);
            if !calc_alg_context
                .process_context()
                .sat_indi_node_functional_concept_ext_data(func_con_ext_data)
                .has_individual_node_forwarding_predecessor_merged_node(anc_sat_node)
            {
                let succ_con_set = calc_alg_context
                    .process_context()
                    .sat_node(succ_sat_node)
                    .reapply_con_sat_label_set;
                if succ_con_set.is_some() {
                    let mut con_sat_des_it = calc_alg_context
                        .process_context()
                        .reapply_con_sat_label_set(succ_con_set)
                        .get_concept_saturation_description_linker();
                    while con_sat_des_it.is_some() {
                        let (concept, negation, next) = {
                            let con_sat_des_ref = calc_alg_context
                                .process_context()
                                .con_sat_desc(con_sat_des_it);
                            (
                                con_sat_des_ref.get_concept(),
                                con_sat_des_ref.get_negation(),
                                con_sat_des_ref.get_next_concept_desciptor(),
                            )
                        };
                        let mut anc_node_ref = anc_sat_node;
                        self.add_concept_filtered_to_individual(
                            concept,
                            negation,
                            &mut anc_node_ref,
                            calc_alg_context,
                        );
                        con_sat_des_it = next;
                    }
                }
                calc_alg_context
                    .process_context_mut()
                    .sat_node_mut(succ_sat_node)
                    .add_copy_depending_individual_node_linker(NegLink {
                        target: anc_sat_node,
                        negated: false,
                    });
                self.preprocess_resolved_individual_node(anc_sat_node, calc_alg_context);
            }

            for creation_role_linker_it in creation_role_linker {
                if !creation_role_linker_it.negated {
                    let creation_role = creation_role_linker_it.target;
                    if !calc_alg_context
                        .process_context()
                        .sat_indi_node_functional_concept_ext_data(func_con_ext_data)
                        .has_individual_node_forwarding_predecessor_merged(
                            anc_sat_node,
                            creation_role,
                        )
                    {
                        updated = true;
                        calc_alg_context
                            .process_context_mut()
                            .sat_indi_node_functional_concept_ext_data_mut(func_con_ext_data)
                            .set_individual_node_forwarding_predecessor_merged(
                                anc_sat_node,
                                creation_role,
                            );
                        let inv_creation_role =
                            self.get_inverse_role(creation_role, calc_alg_context);
                        if inv_creation_role.is_some()
                            && !calc_alg_context
                                .process_context()
                                .linked_role_successor_hash_has_active_linked_successor(
                                    anc_linked_succ_hash,
                                    inv_creation_role,
                                    *indi_proc_sat_node,
                                    None,
                                    1,
                                )
                        {
                            // KONCLUDE-PORT-NOTE[identity]: self-inclusive super-role list (see s02).
                            let inv_creation_super_roles =
                                Self::saturation_indirect_super_roles(
                                    inv_creation_role,
                                    calc_alg_context,
                                );
                            for inv_creation_super_role_it in inv_creation_super_roles {
                                let creation_super_role = inv_creation_super_role_it.target;
                                if !inv_creation_super_role_it.negated {
                                    calc_alg_context
                                        .process_context_mut()
                                        .linked_role_successor_hash_add_extension_successor(
                                            anc_linked_succ_hash,
                                            creation_super_role,
                                            *indi_proc_sat_node,
                                            inv_creation_role,
                                            1,
                                        );
                                    let mut anc_node_ref = anc_sat_node;
                                    self.add_new_linked_extension_processing_role(
                                        creation_super_role,
                                        &mut anc_node_ref,
                                        true,
                                        true,
                                        calc_alg_context,
                                    );
                                } else {
                                    let mut back_prop_link =
                                        BackwardSaturationPropagationLink::new();
                                    back_prop_link.init_backward_propagation_link(
                                        anc_sat_node,
                                        creation_super_role,
                                    );
                                    let back_prop_link = calc_alg_context
                                        .process_context_mut()
                                        .alloc_backward_sat_prop_link(back_prop_link);
                                    self.install_backward_propagation_link(
                                        anc_sat_node,
                                        *indi_proc_sat_node,
                                        creation_super_role,
                                        back_prop_link,
                                        true,
                                        false,
                                        calc_alg_context,
                                    );
                                }
                            }
                        }
                    }
                }
            }
            return updated;
        }
        false
    }

    // =======================================================================
    // Subset-mergeability predicates (cpp 1335–1473).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isLinkedIndividualSuccessorNodeMergingSubset`
    /// (the `CSaturationSuccessorData*`/`CSaturationSuccessorData*` dispatcher overload). cpp 1335–1339.
    ///
    /// Unwraps both successor data's `mSuccIndiNode` and delegates to `_for_nodes`.
    pub fn is_linked_individual_successor_node_merging_subset(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        // `CSaturationSuccessorData* subsetIndiSuccData`
        subset_indi_succ_data: SaturationSuccessorDataId,
        // `CSaturationSuccessorData* superIndiSuccData`
        super_indi_succ_data: SaturationSuccessorDataId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let subset_indi_succ_node = calc_alg_context
            .process_context()
            .sat_succ_data(subset_indi_succ_data)
            .get_successor_individual_node();
        let super_indi_succ_node = calc_alg_context
            .process_context()
            .sat_succ_data(super_indi_succ_data)
            .get_successor_individual_node();
        self.is_linked_individual_successor_node_merging_subset_for_nodes(
            indi_proc_sat_node,
            subset_indi_succ_node,
            subset_indi_succ_data,
            super_indi_succ_node,
            super_indi_succ_data,
            role,
            calc_alg_context,
        )
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isLinkedIndividualSuccessorNodeMergingSubset`
    /// (the explicit-node worker overload). cpp 1343–1366. [overload] `_for_nodes` suffix.
    ///
    /// True when the subset successor's link can be merged into the super successor's:
    /// neither is a VALUE-nominal connection; the subset node has no integrated
    /// nominal and no applied data value; the super link is active; the subset
    /// successor cardinality does not exceed the super's; the role's creation-role
    /// set is a merging subset of the super's; and the subset node's label is a
    /// merging subset of the super node's (AND-concepts not ignored).
    pub fn is_linked_individual_successor_node_merging_subset_for_nodes(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        // `CIndividualSaturationProcessNode* subsetIndiSuccNode`
        subset_indi_succ_node: SatNodeId,
        subset_indi_succ_data: SaturationSuccessorDataId,
        super_indi_succ_node: SatNodeId,
        super_indi_succ_data: SaturationSuccessorDataId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let (
            subset_value_nominal,
            subset_succ_count,
            super_value_nominal,
            super_active_count,
            super_succ_count,
            super_creation_roles,
        ) = {
            let process_context = calc_alg_context.process_context();
            let subset_data = process_context.sat_succ_data(subset_indi_succ_data);
            let super_data = process_context.sat_succ_data(super_indi_succ_data);
            (
                subset_data.value_nominal_connection,
                subset_data.succ_count,
                super_data.value_nominal_connection,
                super_data.active_count,
                super_data.succ_count,
                super_data.creation_role_linker.clone(),
            )
        };
        if subset_value_nominal || super_value_nominal {
            return false;
        }
        {
            let subset_node = calc_alg_context
                .process_context()
                .sat_node(subset_indi_succ_node);
            if subset_node.has_nominal_integrated() {
                return false;
            }
            if subset_node.has_data_value_applied() {
                return false;
            }
        }
        if super_active_count <= 0 {
            return false;
        }
        if subset_succ_count > super_succ_count {
            return false;
        }
        if !self.is_successor_creation_role_merging_subset_for_role(
            role,
            &super_creation_roles,
            calc_alg_context,
        ) {
            return false;
        }
        if !self.is_individual_node_label_merging_subset(
            subset_indi_succ_node,
            super_indi_succ_node,
            false,
            calc_alg_context,
        ) {
            return false;
        }
        let _ = indi_proc_sat_node;
        true
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isSuccessorCreationRoleMergingSubset`
    /// (the `CXNegLinker<CRole*>*`/`CXNegLinker<CRole*>*` overload). cpp 1370–1380.
    ///
    /// True when every non-negated creation-role of `subCreationRoleLinker` is
    /// itself contained in `superCreationRoleLinker` (per the `_for_role` worker).
    pub fn is_successor_creation_role_merging_subset(
        &mut self,
        // `CXNegLinker<CRole*>* subCreationRoleLinker`
        sub_creation_role_linker: &[NegLink<RoleId>],
        // `CXNegLinker<CRole*>* superCreationRoleLinker`
        super_creation_role_linker: &[NegLink<RoleId>],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        for sub_creation_role_linker_it in sub_creation_role_linker.iter() {
            if !sub_creation_role_linker_it.negated
                && !self.is_successor_creation_role_merging_subset_for_role(
                    sub_creation_role_linker_it.target,
                    super_creation_role_linker,
                    calc_alg_context,
                )
            {
                return false;
            }
        }
        true
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isSuccessorCreationRoleMergingSubset`
    /// (the single-role worker overload). cpp 1382–1391. [overload] `_for_role` suffix.
    ///
    /// True when `subCreationRole` occurs non-negated in `superCreationRoleLinker`.
    pub fn is_successor_creation_role_merging_subset_for_role(
        &mut self,
        sub_creation_role: RoleId,
        // `CXNegLinker<CRole*>* superCreationRoleLinker`
        super_creation_role_linker: &[NegLink<RoleId>],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = calc_alg_context;
        for super_creation_role_linker_it in super_creation_role_linker.iter() {
            if !super_creation_role_linker_it.negated
                && super_creation_role_linker_it.target == sub_creation_role
            {
                return true;
            }
        }
        false
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isIndividualNodeLabelMergingSubset`.
    /// cpp 1393–1416.
    ///
    /// True when the subset node's saturation label is a subset of the super node's:
    /// vacuously true if the subset has no label; false if the subset has a label but
    /// the super does not, or if the subset has more concepts; otherwise every subset
    /// concept (skipping AND/AQAND-family positives and OR negatives when
    /// `ignoreANDConcepts`) must be contained in the super label with the same
    /// negation.
    pub fn is_individual_node_label_merging_subset(
        &mut self,
        // `CIndividualSaturationProcessNode* subsetIndiSuccNode`
        subset_indi_succ_node: SatNodeId,
        // `CIndividualSaturationProcessNode* superIndiSuccNode`
        super_indi_succ_node: SatNodeId,
        ignore_and_concepts: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let subset_con_set = calc_alg_context
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(subset_indi_succ_node, false);
        let super_con_set = calc_alg_context
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(super_indi_succ_node, false);

        if super_con_set.is_none() && subset_con_set.is_some() {
            return false;
        }
        if subset_con_set.is_some() && super_con_set.is_some() {
            let (subset_count, super_count, mut subset_iterator) = {
                let process_context = calc_alg_context.process_context();
                let subset_ref = process_context.reapply_con_sat_label_set(subset_con_set);
                let super_ref = process_context.reapply_con_sat_label_set(super_con_set);
                (
                    subset_ref.get_concept_count(),
                    super_ref.get_concept_count(),
                    subset_ref.get_iterator(true, false),
                )
            };
            if subset_count > super_count {
                return false;
            }
            while subset_iterator.has_next() {
                let con_des = subset_iterator.get_concept_saturation_descriptor();
                if con_des.is_some() {
                    let (concept, negation, con_code) = {
                        let process_context = calc_alg_context.process_context();
                        let con_des_ref = process_context.con_sat_desc(con_des);
                        let concept = con_des_ref.get_concept();
                        let negation = con_des_ref.get_negation();
                        let con_code = calc_alg_context
                            .ontology_arenas()
                            .concept(concept)
                            .get_operator_code();
                        (concept, negation, con_code)
                    };
                    let check_containment = !ignore_and_concepts
                        || (!negation
                            && con_code != CCAND
                            && con_code != CCAQAND
                            && con_code != CCIMPLAQAND
                            && con_code != CCBRANCHAQAND)
                        || (negation && con_code != CCOR);
                    if check_containment
                        && Self::sat_label_set_contains_concept_get_negation(
                            super_con_set,
                            concept,
                            calc_alg_context,
                        ) != Some(negation)
                    {
                        return false;
                    }
                }
                subset_iterator.move_next();
            }
        }
        true
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::deactivateSubsetMergeableSuccessorLinks`.
    /// cpp 1421–1473.
    ///
    /// For every active, mergeable (non-data/-nominal/-VALUE-nominal) successor in
    /// `succDataMap`, if it is a linked-individual merging subset of some other active
    /// successor under one of its non-negated creation roles, deactivates that role's
    /// linked successor on every non-negated creation-super-role. Accumulates the
    /// removed successor cardinality (diagnostic). Returns `linksDeactivated` (note:
    /// the C++ never sets it — preserved faithfully; the method is driven for side
    /// effects on `linkedSuccHash`).
    pub fn deactivate_subset_mergeable_successor_links(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        // `CLinkedRoleSaturationSuccessorHash* linkedSuccHash`
        linked_succ_hash: LinkedRoleSaturationSuccessorHashId,
        // `CPROCESSMAP<cint64,CSaturationSuccessorData*>* succDataMap`
        succ_data_map: LinkedRoleSaturationSuccessorDataId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let links_deactivated = false;
        let mut removed_succ_card_count: Cint64 = 0;
        if linked_succ_hash.is_none() || succ_data_map.is_none() {
            let _ = role;
            return links_deactivated;
        }
        let succ_data_entries: Vec<(Cint64, SaturationSuccessorDataId)> = calc_alg_context
            .process_context()
            .linked_role_sat_succ_data(succ_data_map)
            .get_successor_node_data_map()
            .iter()
            .map(|(indi_id, succ_data)| (*indi_id, *succ_data))
            .collect();
        for (indi_id, succ_link_data) in succ_data_entries.iter().copied() {
            if calc_alg_context
                .process_context()
                .sat_succ_data(succ_link_data)
                .active_count
                > 0
            {
                let (succ_card, succ_node, value_nominal_connection, creation_roles) = {
                    let succ_data_ref = calc_alg_context
                        .process_context()
                        .sat_succ_data(succ_link_data);
                    (
                        succ_data_ref.succ_count,
                        succ_data_ref.succ_indi_node,
                        succ_data_ref.value_nominal_connection,
                        succ_data_ref.creation_role_linker.clone(),
                    )
                };

                let mut node_mergeable = true;
                if succ_node.is_some() {
                    let succ_node_ref = calc_alg_context.process_context().sat_node(succ_node);
                    if succ_node_ref.has_data_value_applied()
                        || succ_node_ref.has_nominal_integrated()
                    {
                        node_mergeable = false;
                    }
                }
                if value_nominal_connection {
                    node_mergeable = false;
                }

                if node_mergeable {
                    for creation_role_linker_it in creation_roles.iter() {
                        if !creation_role_linker_it.negated {
                            let creation_role = creation_role_linker_it.target;
                            let mut deactivate_link = false;
                            for (merge_indi_id, merge_succ_link_data) in
                                succ_data_entries.iter().copied()
                            {
                                if !deactivate_link && indi_id != merge_indi_id {
                                    if calc_alg_context
                                        .process_context()
                                        .sat_succ_data(merge_succ_link_data)
                                        .active_count
                                        > 0
                                        && self.is_linked_individual_successor_node_merging_subset(
                                            indi_proc_sat_node,
                                            succ_link_data,
                                            merge_succ_link_data,
                                            creation_role,
                                            calc_alg_context,
                                        )
                                    {
                                        deactivate_link = true;
                                    }
                                }
                            }
                            if deactivate_link {
                                // KONCLUDE-PORT-NOTE[identity]: self-inclusive super-role list (see s02).
                                let creation_super_roles =
                                    Self::saturation_indirect_super_roles(
                                        creation_role,
                                        calc_alg_context,
                                    );
                                for creation_super_role_it in creation_super_roles {
                                    if !creation_super_role_it.negated {
                                        calc_alg_context
                                            .process_context_mut()
                                            .linked_role_successor_hash_deactivate_linked_successor(
                                                linked_succ_hash,
                                                creation_super_role_it.target,
                                                succ_node,
                                                creation_role,
                                            );
                                    }
                                }
                            }
                        }
                    }
                }

                if calc_alg_context
                    .process_context()
                    .sat_succ_data(succ_link_data)
                    .active_count
                    <= 0
                {
                    removed_succ_card_count += succ_card;
                }
            }
        }
        let _ = (role, removed_succ_card_count);
        links_deactivated
    }

    // =======================================================================
    // Mark-ancestors-as-insufficient (cpp 2824–2930).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::markNominalATMOSTRestrictedAncestorsAsInsufficient`.
    /// cpp 2824–2848.
    ///
    /// When a nominal-integrated node's ATMOST is restricted, marks every backward-
    /// propagation source ancestor (for the concept's role) as insufficient and
    /// records the critical predecessor-role cardinality. Returns whether any
    /// ancestor was restricted.
    pub fn mark_nominal_atmost_restricted_ancestors_as_insufficient(
        &mut self,
        // `CConceptSaturationDescriptor* conDes`
        con_des: ConceptSaturationDescriptorId,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut ancestors_restricted = false;
        let (concept, concept_negation) = {
            let con_des_ref = calc_alg_context.process_context().con_sat_desc(con_des);
            (con_des_ref.get_concept(), con_des_ref.get_negation())
        };
        let role = calc_alg_context.ontology_arenas().concept(concept).get_role();
        let backward_prop_hash = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .role_back_prop_hash;
        let is_abox = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .is_abox_individual_representation_node();
        if backward_prop_hash.is_some() && !is_abox {
            let link_linker = calc_alg_context
                .process_context()
                .role_backward_sat_prop_hash(backward_prop_hash)
                .get_role_backward_propagation_data_hash()
                .get(&role)
                .map(|data| data.link_linker)
                .unwrap_or(BackwardSaturationPropagationLinkId::NONE);
            let mut back_prop_link_it = link_linker;
            while back_prop_link_it.is_some() {
                let (source_indi, next_link) = {
                    let link = calc_alg_context
                        .process_context()
                        .backward_sat_prop_link(back_prop_link_it);
                    (link.source_individual, link.next)
                };
                self.update_direct_adding_individual_status_flags(
                    source_indi,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                    calc_alg_context,
                );
                self.set_insufficient_node_occured(calc_alg_context);
                ancestors_restricted = true;
                back_prop_link_it = next_link;
            }
        }
        let crit_pred_rol_card_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_critical_predecessor_role_cardinality_hash(*indi_proc_sat_node, true);
        calc_alg_context
            .process_context_mut()
            .critical_predecessor_role_cardinality_hash_add_cardinality(
                crit_pred_rol_card_hash,
                role,
                concept,
                !concept_negation,
            );
        ancestors_restricted
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::markATMOSTRestrictedAncestorsAsInsufficient`.
    /// cpp 2852–2930.
    ///
    /// The qualified analogue: for each backward-propagation source ancestor of the
    /// ATMOST concept's role, decides whether that ancestor is genuinely insufficient
    /// — it is NOT when (allowed cardinality 1, unqualified) the ancestor is the
    /// functionally-restricted successor, or its inverse-role successor toward
    /// `indiProcSatNode` is inactive, or the functionally-restricted successor has
    /// already merged all the creation roles as predecessor / their labels and
    /// creation-role sets are merging subsets. Insufficient ancestors get the
    /// INSUFFICIENT flag; the critical predecessor-role cardinality is recorded.
    /// Returns whether any ancestor was restricted.
    pub fn mark_atmost_restricted_ancestors_as_insufficient(
        &mut self,
        // `CConceptSaturationDescriptor* conDes`
        con_des: ConceptSaturationDescriptorId,
        // `CIndividualSaturationProcessNode* functionallyRestrictedSuccessorNode`
        functionally_restricted_successor_node: SatNodeId,
        // `CXNegLinker<CRole*>* functionallyRestrictedSuccessorCreationRoleLinker`
        functionally_restricted_successor_creation_role_linker: &[NegLink<RoleId>],
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut ancestors_restricted = false;
        let (concept, concept_negation) = {
            let con_des_ref = calc_alg_context.process_context().con_sat_desc(con_des);
            (con_des_ref.get_concept(), con_des_ref.get_negation())
        };
        let (role, allowed_cardinality, concept_has_operands) = {
            let concept_ref = calc_alg_context.ontology_arenas().concept(concept);
            (
                concept_ref.get_role(),
                concept_ref.get_parameter() - Cint64::from(concept_negation),
                !concept_ref.get_operand_list().is_empty(),
            )
        };
        let backward_prop_hash = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .role_back_prop_hash;
        let is_abox = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .is_abox_individual_representation_node();
        if backward_prop_hash.is_some() && !is_abox {
            let link_linker = calc_alg_context
                .process_context()
                .role_backward_sat_prop_hash(backward_prop_hash)
                .get_role_backward_propagation_data_hash()
                .get(&role)
                .map(|data| data.link_linker)
                .unwrap_or(BackwardSaturationPropagationLinkId::NONE);
            let mut back_prop_link_it = link_linker;
            while back_prop_link_it.is_some() {
                let (source_indi, next_link) = {
                    let link = calc_alg_context
                        .process_context()
                        .backward_sat_prop_link(back_prop_link_it);
                    (link.source_individual, link.next)
                };
                let mut ancestor_insufficient = true;
                let source_insufficient = calc_alg_context
                    .process_context()
                    .sat_node(source_indi)
                    .indirect_status_flags
                    .has_insufficient_flag();
                if !source_insufficient && allowed_cardinality == 1 && !concept_has_operands {
                    if source_indi == functionally_restricted_successor_node {
                        ancestor_insufficient = false;
                    } else {
                        let mut source_indi_mut = source_indi;
                        self.collect_linked_successor_nodes(
                            &mut source_indi_mut,
                            calc_alg_context,
                            INVALID,
                        );
                        let linked_succ_hash = calc_alg_context
                            .process_context_mut()
                            .sat_node_ext_linked_role_successor_hash(source_indi, false);
                        if linked_succ_hash.is_some() {
                            let inverse_role = self.get_inverse_role(role, calc_alg_context);
                            let succ_data = calc_alg_context
                                .process_context()
                                .linked_role_sat_succ_hash(linked_succ_hash)
                                .role_succ_data_hash
                                .get(&inverse_role)
                                .copied();
                            if let Some(succ_data) = succ_data.filter(|d| d.is_some()) {
                                let indi_id = calc_alg_context
                                    .process_context()
                                    .sat_node(*indi_proc_sat_node)
                                    .get_individual_id();
                                let succ_role_data = calc_alg_context
                                    .process_context()
                                    .linked_role_sat_succ_data(succ_data)
                                    .succ_node_data_map
                                    .get(&indi_id)
                                    .copied();
                                if let Some(succ_role_data) =
                                    succ_role_data.filter(|d| d.is_some())
                                {
                                    let (active_count, succ_creation_role_linker) = {
                                        let d = calc_alg_context
                                            .process_context()
                                            .sat_succ_data(succ_role_data);
                                        (d.active_count, d.creation_role_linker.clone())
                                    };
                                    if active_count <= 0 {
                                        ancestor_insufficient = false;
                                    } else {
                                        let mut func_succ_all_role_pred_merged = false;
                                        let func_con_ext_data = calc_alg_context
                                            .process_context_mut()
                                            .sat_node_functional_concepts_extension_data(
                                                functionally_restricted_successor_node,
                                                false,
                                            );
                                        if func_con_ext_data.is_some() {
                                            func_succ_all_role_pred_merged = true;
                                            for creation_role_it in
                                                functionally_restricted_successor_creation_role_linker
                                                    .iter()
                                                    .filter(|l| !l.negated)
                                            {
                                                if !calc_alg_context
                                                    .process_context()
                                                    .sat_indi_node_functional_concept_ext_data(
                                                        func_con_ext_data,
                                                    )
                                                    .has_individual_node_forwarding_predecessor_merged(
                                                        source_indi,
                                                        creation_role_it.target,
                                                    )
                                                {
                                                    func_succ_all_role_pred_merged = false;
                                                    break;
                                                }
                                            }
                                        }
                                        if func_succ_all_role_pred_merged
                                            || self.is_individual_node_label_merging_subset(
                                                functionally_restricted_successor_node,
                                                source_indi,
                                                true,
                                                calc_alg_context,
                                            )
                                        {
                                            if func_succ_all_role_pred_merged
                                                || self.is_successor_creation_role_merging_subset(
                                                    functionally_restricted_successor_creation_role_linker,
                                                    &succ_creation_role_linker,
                                                    calc_alg_context,
                                                )
                                            {
                                                ancestor_insufficient = false;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if ancestor_insufficient {
                    self.update_direct_adding_individual_status_flags(
                        source_indi,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                    self.set_insufficient_node_occured(calc_alg_context);
                    ancestors_restricted = true;
                }
                back_prop_link_it = next_link;
            }
        }
        let crit_pred_rol_card_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_critical_predecessor_role_cardinality_hash(*indi_proc_sat_node, true);
        calc_alg_context
            .process_context_mut()
            .critical_predecessor_role_cardinality_hash_add_cardinality(
                crit_pred_rol_card_hash,
                role,
                concept,
                !concept_negation,
            );
        ancestors_restricted
    }

    // =======================================================================
    // ATMOST relevant-successor collection (cpp 3779–3961).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::collectATMOSTConceptRelevantSuccessors`.
    /// cpp 3779–3961.
    ///
    /// Scans the role's successor-node data map for successors relevant to the ATMOST
    /// concept: a successor is relevant unless its label provably satisfies the
    /// qualification negatively (then it cannot count) — accounting for trivial vs
    /// choose-triggered qualification, VALUE-nominal connections (resolved through the
    /// det-cached completion graph), and qualification-representative successor
    /// individuals. Builds the `mergingSuccDataLinker` chain of countable successors,
    /// returns the summed found cardinality, sets `minCardinality` to the max single
    /// successor cardinality, records the last successor node / creation-role linker,
    /// and clashes the node when a single successor already exceeds the allowance.
    pub fn collect_atmost_concept_relevant_successors(
        &mut self,
        // `CConceptSaturationDescriptor* conDes`
        con_des: ConceptSaturationDescriptorId,
        indi_proc_sat_node: &mut SatNodeId,
        // `CLinkedRoleSaturationSuccessorData* succData`
        succ_data: LinkedRoleSaturationSuccessorDataId,
        // `CIndividualSaturationSuccessorLinkDataLinker*& mergingSuccDataLinker`
        merging_succ_data_linker: &mut IndividualSaturationSuccessorLinkDataLinkerId,
        last_successor_node: &mut SatNodeId,
        // `CXNegLinker<CRole*>*& lastSuccessorCreationRoleLinker`
        last_successor_creation_role_linker: &mut Vec<NegLink<RoleId>>,
        min_cardinality: &mut Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        let (concept, concept_negation) = {
            let con_des_ref = calc_alg_context.process_context().con_sat_desc(con_des);
            (con_des_ref.get_concept(), con_des_ref.get_negation())
        };
        let (role, allowed_cardinality, operands) = {
            let concept_ref = calc_alg_context.ontology_arenas().concept(concept);
            (
                concept_ref.get_role(),
                concept_ref.get_parameter() - Cint64::from(concept_negation),
                concept_ref.get_operand_list().to_vec(),
            )
        };

        let mut found_cardinality: Cint64 = 0;
        *min_cardinality = 0;

        let mut trivial_qualification = true;
        for op_linker in operands.iter() {
            let op_code = calc_alg_context
                .ontology_arenas()
                .concept(op_linker.target)
                .get_operator_code();
            if op_linker.negated || (op_code != CCATOM && op_code != CCSUB) {
                trivial_qualification = false;
                break;
            }
        }

        // Deferred[api]: CConceptProcessData::getConceptRoleBranchTrigger.
        // The current substrate has no CConceptRoleBranchingTrigger chain yet. The
        // C++ fallback when there is no choose-trigger linker is preserved below:
        // a missing non-trivial operand makes `operantsContained = false`.
        let choose_trigger_linker_available = false;

        let succ_role_data_ids: Vec<_> = calc_alg_context
            .process_context()
            .linked_role_sat_succ_data(succ_data)
            .get_successor_node_data_map()
            .values()
            .copied()
            .collect();

        for succ_role_data_id in succ_role_data_ids {
            let (
                active_count,
                succ_cardinality,
                value_nominal_connection,
                succ_node,
                creation_role_linker,
            ) = {
                let succ_role_data = calc_alg_context
                    .process_context()
                    .sat_succ_data(succ_role_data_id);
                (
                    succ_role_data.get_active_count(),
                    succ_role_data.get_successor_count(),
                    succ_role_data.value_nominal_connection,
                    succ_role_data.get_successor_individual_node(),
                    succ_role_data.creation_role_linker.clone(),
                )
            };
            if active_count < 1 {
                continue;
            }

            let mut operants_contained_negative = true;
            let mut operants_contained_positive = true;
            let mut operants_contained = true;
            let mut qualification_representitive_successor_indi = false;

            if value_nominal_connection {
                *last_successor_node = SatNodeId::NONE;
                last_successor_creation_role_linker.clear();
                // Deferred[api]: VALUE-nominal branch needs getCorrectedNode over
                // mDetCachedCGIndiVector and the completion-layer
                // CReapplyConceptLabelSet::containsConcept. Until that sibling
                // substrate exists, preserve the same no-label-set flag transition
                // used by the C++ body below the failed/absent reapply-label path.
                if trivial_qualification {
                    operants_contained_positive = false;
                } else if !choose_trigger_linker_available {
                    operants_contained = false;
                }
            } else {
                *last_successor_node = succ_node;
                *last_successor_creation_role_linker = creation_role_linker;

                let succ_con_set = calc_alg_context
                    .process_context_mut()
                    .sat_node_reapply_concept_saturation_label_set(succ_node, false);
                let concept_sat_item = {
                    let item = calc_alg_context
                        .process_context()
                        .sat_node(succ_node)
                        .get_saturation_concept_reference_linking();
                    if item.is_some()
                        && item.index()
                            < calc_alg_context
                                .process_context()
                                .extended_con_ref_linking_data_count()
                    {
                        item
                    } else {
                        Id::NONE
                    }
                };
                if succ_con_set.is_some() {
                    if !operands.is_empty() {
                        for op_linker in operands.iter() {
                            if concept_sat_item.is_some() {
                                let concept_sat_item_ref = calc_alg_context
                                    .process_context()
                                    .extended_con_ref_linking_data(concept_sat_item);
                                let indi_concept = concept_sat_item_ref.get_saturation_concept();
                                let indi_con_negation =
                                    concept_sat_item_ref.get_saturation_negation();
                                let indi_role = concept_sat_item_ref.get_saturation_role_ranges();
                                if op_linker.target == indi_concept
                                    && op_linker.negated == indi_con_negation
                                    && (indi_role.is_none() || indi_role == role)
                                {
                                    qualification_representitive_successor_indi = true;
                                    operants_contained_negative = false;
                                }
                            }
                            if !qualification_representitive_successor_indi {
                                if let Some(contained_negation) =
                                    Self::sat_label_set_contains_concept_get_negation(
                                        succ_con_set,
                                        op_linker.target,
                                        calc_alg_context,
                                    )
                                {
                                    if contained_negation == op_linker.negated {
                                        operants_contained_negative = false;
                                    } else {
                                        operants_contained_positive = false;
                                    }
                                } else if trivial_qualification {
                                    operants_contained_positive = false;
                                } else if !choose_trigger_linker_available {
                                    operants_contained = false;
                                }
                            }
                        }
                    } else {
                        if concept_sat_item.is_some() {
                            let concept_sat_item_ref = calc_alg_context
                                .process_context()
                                .extended_con_ref_linking_data(concept_sat_item);
                            let indi_concept = concept_sat_item_ref.get_saturation_concept();
                            let indi_con_negation = concept_sat_item_ref.get_saturation_negation();
                            let indi_role = concept_sat_item_ref.get_saturation_role_ranges();
                            let top_concept = calc_alg_context
                                .processing_data_box()
                                .ontology_top_concept();
                            if top_concept == indi_concept
                                && !indi_con_negation
                                && (indi_role.is_none() || indi_role == role)
                            {
                                qualification_representitive_successor_indi = true;
                            }
                        }
                        operants_contained_negative = false;
                    }
                } else if trivial_qualification {
                    operants_contained_positive = false;
                } else if !choose_trigger_linker_available {
                    operants_contained = false;
                }
            }
            let _ = operants_contained_negative;

            if operants_contained_positive || !operants_contained {
                *min_cardinality = (*min_cardinality).max(succ_cardinality);
                let nominal_individual = calc_alg_context
                    .process_context()
                    .sat_node(*indi_proc_sat_node)
                    .get_nominal_individual();
                if operants_contained
                    && operants_contained_positive
                    && nominal_individual.is_none()
                    && succ_cardinality > allowed_cardinality
                {
                    if super::sat_clash_trace_enabled() {
                        let indi = calc_alg_context
                            .process_context()
                            .sat_node(*indi_proc_sat_node)
                            .get_individual_id();
                        eprintln!(
                            "SAT-CLASH s08-atmost node={:?} indi={} succ_card={} allowed={}",
                            indi_proc_sat_node, indi, succ_cardinality, allowed_cardinality
                        );
                    }
                    self.update_direct_adding_individual_status_flags(
                        *indi_proc_sat_node,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                        calc_alg_context,
                    );
                }

                if !qualification_representitive_successor_indi {
                    found_cardinality += succ_cardinality;
                    let new_linker = self
                        .create_individual_saturation_successor_link_data_linker(calc_alg_context);
                    calc_alg_context
                        .process_context_mut()
                        .indi_sat_succ_link_data_linker_mut(new_linker)
                        .init_successor_link_data_linker(succ_role_data_id)
                        .set_next(*merging_succ_data_linker);
                    *merging_succ_data_linker = new_linker;
                }
            }
        }
        // W4-DEFER[api]: faithful C++ body —
        //   concept = conDes->getConcept(); conceptNegation = conDes->isNegated();
        //   role = concept->getRole(); allowedCardinality = concept->getParameter() - 1*conceptNegation;
        //   foundCardinality = 0; minCardinality = 0;
        //   // detect trivial (atomic/sub, non-negated) qualification; else pull the choose-trigger linker:
        //   trivialQualification = true;
        //   for (opLinkerIt in concept->getOperandList()) if (opNeg || (opCode != CCATOM && opCode != CCSUB)) trivialQualification = false;
        //   if (!trivialQualification) { conProData = (CConceptProcessData*)concept->getConceptData(); if (conProData) chooseTriggerLinker = conProData->getConceptRoleBranchTrigger(); }
        //   for ((id, succRoleData) in succData->mSuccNodeDataMap) if (succRoleData->mActiveCount >= 1) {
        //       succCardinality = succRoleData->mSuccCount;
        //       operantsContainedNegative = operantsContainedPositive = operantsContained = true;
        //       qualificationRepresentitiveSuccessorIndi = false;
        //       if (succRoleData->mVALUENominalConnection) {
        //           lastSuccessorNode = nullptr; lastSuccessorCreationRoleLinker = nullptr;
        //           indiProcNode = getCorrectedNode(succRoleData->mVALUENominalID, mDetCachedCGIndiVector, mCalcAlgContext);   // sibling
        //           if (indiProcNode) {
        //               reapplyConSet = indiProcNode->getReapplyConceptLabelSet(false);
        //               if (reapplyConSet) {
        //                   if (concept->getOperandList())
        //                       for (opLinkerIt in concept->getOperandList()) {
        //                           opConcept = opLinkerIt->getData(); opConceptNegation = opLinkerIt->isNegated(); containedNegation = false;
        //                           if (reapplyConSet->containsConcept(opConcept, &containedNegation)) { if (containedNegation == opConceptNegation) operantsContainedNegative = false; else operantsContainedPositive = false; }
        //                           else if (trivialQualification) operantsContainedPositive = false;
        //                           else { isChooseTriggered = false; for (chooseTriggerIt in chooseTriggerLinker) { if (conceptTrigger && contains+sameNeg) isChooseTriggered = true; else if (!conceptTrigger) isChooseTriggered = true; } if (!chooseTriggerLinker || isChooseTriggered) operantsContained = false; }
        //                       }
        //                   else operantsContainedNegative = false;
        //               } else if (trivialQualification) operantsContainedPositive = false; else operantsContained = false;
        //           }
        //       } else {
        //           succNode = succRoleData->mSuccIndiNode; lastSuccessorNode = succNode; lastSuccessorCreationRoleLinker = succRoleData->mCreationRoleLinker;
        //           succConSet = succNode->getReapplyConceptSaturationLabelSet(false);
        //           conceptSatItem = (CSaturationConceptDataItem*)succNode->getSaturationConceptReferenceLinking();
        //           if (succConSet) {
        //               if (concept->getOperandList())
        //                   for (opLinkerIt in concept->getOperandList()) {
        //                       opConcept = opLinkerIt->getData(); opConceptNegation = opLinkerIt->isNegated(); containedNegation = false;
        //                       if (conceptSatItem) { indiConcept = conceptSatItem->getSaturationConcept(); indiConNegation = conceptSatItem->getSaturationNegation(); indiRole = conceptSatItem->getSaturationRoleRanges();
        //                           if (opConcept == indiConcept && opConceptNegation == indiConNegation && (indiRole == null || indiRole == role)) { qualificationRepresentitiveSuccessorIndi = true; operantsContainedNegative = false; } }
        //                       if (!qualificationRepresentitiveSuccessorIndi) {
        //                           if (succConSet->containsConcept(opConcept, &containedNegation)) { if (containedNegation == opConceptNegation) operantsContainedNegative = false; else operantsContainedPositive = false; }
        //                           else if (trivialQualification) operantsContainedPositive = false;
        //                           else { isChooseTriggered = false; for (chooseTriggerIt in chooseTriggerLinker) {...as above over succConSet...} if (!chooseTriggerLinker || isChooseTriggered) operantsContained = false; }
        //                       }
        //                   }
        //               else {
        //                   if (conceptSatItem) { indiConcept = ...; topConcept = calcAlgContext->getUsedProcessingDataBox()->getOntologyTopConcept();
        //                       if (topConcept == indiConcept && !indiConNegation && (indiRole == null || indiRole == role)) qualificationRepresentitiveSuccessorIndi = true; }
        //                   operantsContainedNegative = false;
        //               }
        //           } else if (trivialQualification) operantsContainedPositive = false; else operantsContained = false;
        //       }
        //       if (operantsContainedPositive || !operantsContained) {
        //           minCardinality = qMax(minCardinality, succCardinality);
        //           if (operantsContained && operantsContainedPositive && !indiProcSatNode->getNominalIndividual() && succCardinality > allowedCardinality)
        //               updateDirectAddingIndividualStatusFlags(indiProcSatNode, INDSATFLAGCLASHED, ctx);
        //           if (!qualificationRepresentitiveSuccessorIndi) {
        //               foundCardinality += succCardinality;
        //               newMergingSuccDataLinker = createIndividualSaturationSuccessorLinkDataLinker(ctx);   // pool sibling
        //               newMergingSuccDataLinker->initSuccessorLinkDataLinker(succRoleData);
        //               mergingSuccDataLinker = newMergingSuccDataLinker->append(mergingSuccDataLinker);
        //           }
        //       }
        //   }
        //   return foundCardinality;
        // CLinkedRoleSaturationSuccessorData / CSaturationSuccessorData / label sets /
        // CSaturationConceptDataItem / CConceptRoleBranchingTrigger satellites + the
        // getCorrectedNode / status-flag / pool-linker siblings not yet ported.
        found_cardinality
    }

    pub(in crate::konclude_ht) fn sat_label_set_contains_concept_get_negation(
        label_set: ReapplyConceptSaturationLabelSetId,
        concept: ConceptId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Option<bool> {
        let con_tag = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_tag();
        let mut con_sat_des = ConceptSaturationDescriptorId::NONE;
        let mut imp_reapply_con_sat_des = ImplicationReapplyConceptSaturationDescriptorId::NONE;
        let contained = calc_alg_context
            .process_context()
            .reapply_con_sat_label_set(label_set)
            .get_concept_saturation_descriptor_by_tag(
                con_tag,
                &mut con_sat_des,
                &mut imp_reapply_con_sat_des,
            );
        if contained && con_sat_des.is_some() {
            Some(
                calc_alg_context
                    .process_context()
                    .con_sat_desc(con_sat_des)
                    .get_negation(),
            )
        } else {
            None
        }
    }

    // =======================================================================
    // ATMOST merging driver loop (cpp 3969–4027).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::tryATMOSTConceptSuccessorMerging`.
    /// cpp 3969–4027.
    ///
    /// Drains the databox's ATMOST-merging process-linker worklist. For each queued
    /// node not already insufficient/clashed, walks its ATMOST merging-concept linker
    /// and runs `tryIndividiualATMOSTConceptSuccessorMerging`; on a result that does
    /// not require node expansion, applies the insufficiency outcome (INSUFFICIENT
    /// flag + occurrence flag, or critical-concept propagation), marks nominal /
    /// general ATMOST-restricted ancestors, and flags cardinality-problematic when an
    /// ancestor may be critical. Returns whether a node-expansion saturation step is
    /// required (which suspends draining).
    pub fn try_atmost_concept_successor_merging(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut node_saturation = false;
        while !node_saturation
            && calc_alg_context
                .processing_data_box()
                .has_saturation_atmost_merging_process_linker()
        {
            let merging_process_linker = calc_alg_context
                .processing_data_box()
                .saturation_atmost_merging_process_linker();
            let mut indi_proc_sat_node = calc_alg_context
                .process_context()
                .indi_sat_process_node_linker(merging_process_linker)
                .get_processing_individual();

            let indirect_flags = calc_alg_context
                .process_context()
                .sat_node(indi_proc_sat_node)
                .indirect_status_flags;
            if !indirect_flags.has_insufficient_flag() && !indirect_flags.has_clashed_flag() {
                let atmost_succ_merging_data = calc_alg_context
                    .process_context_mut()
                    .sat_node_ext_atmost_successor_merging_data(indi_proc_sat_node, false);
                if atmost_succ_merging_data.is_some() {
                    let mut con_proc_linker = calc_alg_context
                        .process_context()
                        .sat_atmost_successor_merging_data(atmost_succ_merging_data)
                        .get_merging_concept_linker();
                    while !node_saturation && con_proc_linker.is_some() {
                        let con_des = calc_alg_context
                            .process_context()
                            .con_sat_proc_linker(con_proc_linker)
                            .get_concept_saturation_descriptor();

                        calc_alg_context
                            .process_context_mut()
                            .sat_atmost_successor_merging_data_atmost_concept_merging_data(
                                atmost_succ_merging_data,
                                con_des,
                            );

                        let mut node_insufficient = false;
                        let mut ancestor_possibly_insufficient = false;
                        let mut functionally_restricted_successor_node = SatNodeId::NONE;
                        let mut functionally_restricted_successor_creation_role_linker: Vec<
                            NegLink<RoleId>,
                        > = Vec::new();

                        node_saturation = self.try_individiual_atmost_concept_successor_merging(
                            con_des,
                            INVALID,
                            &mut node_insufficient,
                            &mut ancestor_possibly_insufficient,
                            &mut functionally_restricted_successor_node,
                            &mut functionally_restricted_successor_creation_role_linker,
                            &mut indi_proc_sat_node,
                            calc_alg_context,
                        );

                        if !node_saturation {
                            if node_insufficient {
                                self.insufficient_atmost_count += 1;
                                self.update_direct_adding_individual_status_flags(
                                    indi_proc_sat_node,
                                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                                    calc_alg_context,
                                );
                                self.set_insufficient_node_occured(calc_alg_context);
                            } else {
                                self.add_critical_concept_for_dependent_nodes(
                                    con_des,
                                    CCT_ATMOST,
                                    &mut indi_proc_sat_node,
                                    false,
                                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                                    calc_alg_context,
                                );
                            }
                            if calc_alg_context
                                .process_context()
                                .sat_node(indi_proc_sat_node)
                                .has_nominal_integrated()
                            {
                                self.mark_nominal_atmost_restricted_ancestors_as_insufficient(
                                    con_des,
                                    &mut indi_proc_sat_node,
                                    calc_alg_context,
                                );
                            }
                            if ancestor_possibly_insufficient {
                                self.mark_atmost_restricted_ancestors_as_insufficient(
                                    con_des,
                                    functionally_restricted_successor_node,
                                    &functionally_restricted_successor_creation_role_linker,
                                    &mut indi_proc_sat_node,
                                    calc_alg_context,
                                );
                                self.update_direct_adding_individual_status_flags(
                                    indi_proc_sat_node,
                                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCARDINALITYPROPLEMATIC,
                                    calc_alg_context,
                                );
                            }
                        }

                        if !node_saturation {
                            con_proc_linker = calc_alg_context
                                .process_context_mut()
                                .sat_atmost_successor_merging_data_take_next_merging_concept_linker(
                                    atmost_succ_merging_data,
                                );
                        }
                    }
                }
            }

            if !node_saturation {
                let ctx_base = &mut calc_alg_context.base;
                let merging_process_linker = ctx_base
                    .used_processing_data_box
                    .take_saturation_atmost_merging_process_linker(
                        &mut ctx_base.used_process_context,
                    );
                ctx_base
                    .used_process_context
                    .indi_sat_process_node_linker_mut(merging_process_linker)
                    .set_processing_queued(false);
            }
        }
        node_saturation
    }

    // =======================================================================
    // Merged-successor reconnection (cpp 4034–4131).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::reconnectMergedLinkedSuccessors`.
    /// cpp 4034–4131.
    ///
    /// After two successor links merge into `resolvedIndiProcSatNode`, rewires the
    /// linked-successor hash: for each non-coincident source link, deactivates its
    /// creation-super-role successors and adds the resolved successor (cardinality
    /// `newSuccCard`), then propagates the merge-distinctness relation onto the
    /// resolved data. When the resolved node already equals one source, increases that
    /// link's count by `incrSuccCard` and folds distinctness; otherwise returns a new
    /// merging link-data linker for the resolved successor (with its remaining
    /// mergeable cardinality recorded).
    pub fn reconnect_merged_linked_successors(
        &mut self,
        // `CSaturationSuccessorData* succLinkData`
        succ_link_data: Cint64,
        // `CSaturationSuccessorData* mergedSuccLinkData`
        merged_succ_link_data: Cint64,
        new_succ_card: Cint64,
        incr_succ_card: Cint64,
        // `CLinkedRoleSaturationSuccessorHash* linkedSuccHash`
        linked_succ_hash: Cint64,
        // `CLinkedRoleSaturationSuccessorData* succData`
        succ_data: Cint64,
        // `CPROCESSHASH<CSaturationSuccessorData*,CSaturationSuccessorData*>* mergeDistintHash`
        merge_distint_hash: Cint64,
        // `CPROCESSSET< QPair<CSaturationSuccessorData*,CSaturationSuccessorData*> >* mergeDistintSet`
        merge_distint_set: Cint64,
        // `CPROCESSHASH<CSaturationSuccessorData*,cint64>* remainMergeableCardHash`
        remain_mergeable_card_hash: Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        // `CIndividualSaturationProcessNode* resolvedIndiProcSatNode`
        resolved_indi_proc_sat_node: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        let merging_succ_data_linker: Cint64 = INVALID;
        // W4-DEFER[api]: faithful C++ body —
        //   resolvedSuccLinkData = nullptr;
        //   if (resolvedIndiProcSatNode != succLinkData->mSuccIndiNode) {
        //       for (creationRoleIt in succLinkData->mCreationRoleLinker) if (!negated) {
        //           creationRole = creationRoleIt->getData();
        //           for (superRoleIt in creationRole->getIndirectSuperRoleList()) if (!negated)
        //               linkedSuccHash->deactivateLinkedSuccessor(superRoleIt->getData(), succLinkData->mSuccIndiNode, creationRole);
        //           if (!linkedSuccHash->hasActiveLinkedSuccessor(creationRole, resolvedIndiProcSatNode, creationRole, newSuccCard))
        //               for (superRoleIt in creationRole->getIndirectSuperRoleList()) if (!negated)
        //                   linkedSuccHash->addExtensionSuccessor(superRoleIt->getData(), resolvedIndiProcSatNode, creationRole, newSuccCard);
        //       }
        //       resolvedSuccLinkData = succData->getSuccessorNodeDataMap()->value(resolvedIndiProcSatNode->getIndividualID());
        //       for (mDIt = mergeDistintHash->constFind(succLinkData); mDIt.key() == succLinkData; ++mDIt) {
        //           distSuccData = mDIt.value();
        //           mergeDistintHash->insertMulti(distSuccData, resolvedSuccLinkData); mergeDistintHash->insertMulti(resolvedSuccLinkData, distSuccData);
        //           mergeDistintSet->insert(QPair(qMin(resolvedSuccLinkData,distSuccData), qMax(resolvedSuccLinkData,distSuccData)));
        //       }
        //   }
        //   if (resolvedIndiProcSatNode != mergedSuccLinkData->mSuccIndiNode) { ...identical block for mergedSuccLinkData... }
        //   if (resolvedIndiProcSatNode == succLinkData->mSuccIndiNode || resolvedIndiProcSatNode == mergedSuccLinkData->mSuccIndiNode) {
        //       sameSuccLinkData = succLinkData; otherSuccLinkData = mergedSuccLinkData;
        //       if (resolvedIndiProcSatNode != mergedSuccLinkData->mSuccIndiNode) { sameSuccLinkData = mergedSuccLinkData; otherSuccLinkData = succLinkData; }
        //       if (incrSuccCard > 0)
        //           for (creationRoleIt in sameSuccLinkData->mCreationRoleLinker) if (!negated)
        //               for (superRoleIt in creationRole->getIndirectSuperRoleList()) if (!negated)
        //                   linkedSuccHash->increaseLinkedSuccessorCount(superRoleIt->getData(), sameSuccLinkData->mSuccIndiNode, creationRole, incrSuccCard);
        //       for (mDIt = mergeDistintHash->constFind(otherSuccLinkData); mDIt.key() == otherSuccLinkData; ++mDIt) {
        //           distSuccData = mDIt.value();
        //           mergeDistintHash->insertMulti(distSuccData, sameSuccLinkData); mergeDistintHash->insertMulti(sameSuccLinkData, distSuccData);
        //           mergeDistintSet->insert(QPair(qMin(sameSuccLinkData,distSuccData), qMax(sameSuccLinkData,distSuccData)));
        //       }
        //       remainMergeableCardHash->insert(sameSuccLinkData, newSuccCard);
        //   } else {
        //       newMergingSuccDataLinker = createIndividualSaturationSuccessorLinkDataLinker(ctx);   // pool sibling
        //       newMergingSuccDataLinker->initSuccessorLinkDataLinker(resolvedSuccLinkData);
        //       mergingSuccDataLinker = newMergingSuccDataLinker->append(mergingSuccDataLinker);
        //       remainMergeableCardHash->insert(resolvedSuccLinkData, newSuccCard);
        //   }
        //   return mergingSuccDataLinker;
        // CLinkedRoleSaturationSuccessorHash / CSaturationSuccessorData / the merge
        // distinct hash+set / remaining-mergeable hash satellites + the pool sibling
        // not yet ported.
        let _ = (
            succ_link_data,
            merged_succ_link_data,
            new_succ_card,
            incr_succ_card,
            linked_succ_hash,
            succ_data,
            merge_distint_hash,
            merge_distint_set,
            remain_mergeable_card_hash,
            indi_proc_sat_node,
            resolved_indi_proc_sat_node,
        );
        merging_succ_data_linker
    }

    // =======================================================================
    // Merged-successor problematic test (cpp 4136–4247).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::testMergedSuccessorLinkingProblematic`.
    /// cpp 4136–4247.
    ///
    /// Decides whether merging two successor links into `resolvedIndiProcSatNode`
    /// would be unsound: true if any backward-propagation reapply operand of a
    /// creation-super-role is absent from `indiProcSatNode`'s label, or if a concept
    /// newly contributed by the resolved (merged) node's label re-triggers a
    /// predecessor ATMOST/¬ATLEAST whose qualified successor count would then exceed
    /// its allowance. Returns whether merging is problematic.
    pub fn test_merged_successor_linking_problematic(
        &mut self,
        // `CConceptSaturationDescriptor* conDes`
        con_des: Cint64,
        // `CSaturationSuccessorData* succLinkData`
        succ_link_data: Cint64,
        // `CSaturationSuccessorData* mergedSuccLinkData`
        merged_succ_link_data: Cint64,
        // `CIndividualSaturationProcessNode* resolvedIndiProcSatNode`
        resolved_indi_proc_sat_node: SatNodeId,
        // `CLinkedRoleSaturationSuccessorData* succData`
        succ_data: Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   resolvedSuccLinkData = succData->getSuccessorNodeDataMap()->value(resolvedIndiProcSatNode->getIndividualID());
        //   propTestBackwardPropHash = resolvedIndiProcSatNode->getRoleBackwardPropagationHash(false);
        //   if (propTestBackwardPropHash) {
        //       indiConSet = indiProcSatNode->getReapplyConceptSaturationLabelSet(false);
        //       backwardPropDataHash = propTestBackwardPropHash->getRoleBackwardPropagationDataHash();
        //       // for both succLinkData and mergedSuccLinkData creation-role linkers:
        //       for (creationRoleIt in <link>->mCreationRoleLinker) if (!negated)
        //           for (superRoleIt in creationRole->getIndirectSuperRoleList()) if (!negated) {
        //               backwardPropData = backwardPropDataHash->valuePointer(superRole);
        //               if (backwardPropData && backwardPropData->mReapplyLinker)
        //                   for (backPropIt in backwardPropData->mReapplyLinker) {
        //                       backConDes = backPropIt->getReapplyConceptSaturationDescriptor(); concept = backConDes->getConcept(); negation = backConDes->isNegated();
        //                       for (opLinkerIt in concept->getOperandList()) { opConcept = opLinkerIt->getData(); opNegation = opLinkerIt->isNegated() ^ negation;
        //                           if (!indiConSet->containsConcept(opConcept, opNegation)) return true; }
        //                   }
        //           }
        //   }
        //   // newly-contributed concepts of the resolved label (up to either source's label head):
        //   lastConDesIt1 = succLinkData->mSuccIndiNode->getReapplyConceptSaturationLabelSet(false)->getConceptSaturationDescriptionLinker();
        //   lastConDesIt2 = mergedSuccLinkData->mSuccIndiNode->getReapplyConceptSaturationLabelSet(false)->getConceptSaturationDescriptionLinker();
        //   for (conDesIt = resolvedIndiProcSatNode->...->getConceptSaturationDescriptionLinker(); conDesIt && conDesIt != lastConDesIt1 && conDesIt != lastConDesIt2; conDesIt = conDesIt->getNextConceptDesciptor()) {
        //       concept = conDesIt->getConcept();
        //       for (predConDesIt in indiProcSatNode->...->getConceptSaturationDescriptionLinker()) {
        //           predConcept = predConDesIt->getConcept(); predConNegation = predConDesIt->isNegated(); predConOpCode = predConcept->getOperatorCode();
        //           if (predConNegation && predConOpCode == CCATLEAST || !predConNegation && predConOpCode == CCATMOST) {
        //               predOpCon = nullptr; if (predConcept->getOperandList()) predOpCon = predConcept = predConcept->getOperandList()->getData();
        //               if (!predOpCon || predOpCon == concept)
        //                   for (creationRoleLinkerIt in <both succLinkData & mergedSuccLinkData>->mCreationRoleLinker) if (!negated)
        //                       for (creationSuperRoleIt in creationRole->getIndirectSuperRoleList()) if (!negated)
        //                           if (creationSuperRole == predConcept->getRole()) {
        //                               allowedCardinality = predConcept->getParameter() - 1*predConNegation;
        //                               if (getIndividualNodeQualifiedSuccessorCount(indiProcSatNode, creationSuperRole, predConcept->getOperandList(), ctx) > allowedCardinality) return true;
        //                           }
        //           }
        //       }
        //   }
        //   return false;
        // CRoleBackwardSaturationPropagationHash / CSaturationSuccessorData / label
        // sets satellites + the getIndividualNodeQualifiedSuccessorCount sibling
        // (LIVE-deferred below) not yet ported.
        let _ = (
            con_des,
            succ_link_data,
            merged_succ_link_data,
            resolved_indi_proc_sat_node,
            succ_data,
            indi_proc_sat_node,
        );
        false
    }

    // =======================================================================
    // Per-individual ATMOST successor merging (cpp 4250–4453).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::tryIndividiualATMOSTConceptSuccessorMerging`.
    /// cpp 4250–4453. (C++ method-name typo `Individiual` preserved per PORT.md.)
    ///
    /// The cardinality core for one ATMOST descriptor on `indiProcSatNode`. With
    /// allowed cardinality < 0 the node is immediately insufficient. Otherwise it
    /// collects the role's relevant successors (once, cached on `mergingSuccData`),
    /// then tries to fold them: a simple subset-merge pass (when configured) and a
    /// detailed extended-merge pass that resolves merged successor nodes via
    /// node-extension and reconnects them, each reducing `mergeableCardinality`. A
    /// final greedy pairwise loop merges remaining mergeable successors that are not
    /// problematic, possibly signalling a node-expansion-required saturation step. If
    /// the residual count equals the allowance (or min cardinality already meets it),
    /// flags the ancestor possibly-critical (and, for allowance 1, records the
    /// functionally-restricted successor); if it exceeds the allowance, marks the node
    /// insufficient. Returns whether node expansion is required.
    #[allow(clippy::too_many_arguments)]
    pub fn try_individiual_atmost_concept_successor_merging(
        &mut self,
        // `CConceptSaturationDescriptor* conDes`
        con_des: ConceptSaturationDescriptorId,
        // `CSaturationATMOSTSuccessorMergingHashData* mergingSuccData`
        merging_succ_data: Cint64,
        node_insufficient: &mut bool,
        ancestor_possibly_critical_flag: &mut bool,
        functionally_restricted_successor_node: &mut SatNodeId,
        // `CXNegLinker<CRole*>*& functionallyRestrictedSuccessorCreationRoleLinker`
        functionally_restricted_successor_creation_role_linker: &mut Vec<NegLink<RoleId>>,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   concept = conDes->getConcept(); conceptNegation = conDes->isNegated(); role = concept->getRole();
        //   allowedCardinality = concept->getParameter() - 1*conceptNegation;
        //   if (allowedCardinality < 0) { nodeInsufficient = true; return false; }
        //   if (!indiProcSatNode->hasSubstituteIndividualNode()) {
        //       atmostSuccMergingData = indiProcSatNode->getATMOSTSuccessorMergingData();
        //       linkedSuccHash = atmostSuccMergingData->getMergedLinkedRoleSaturationSuccessorHash();
        //       collectLinkedSuccessorNodes(indiProcSatNode, ctx, linkedSuccHash);   // sibling
        //       if (linkedSuccHash) {
        //           foundCardinality = mergingSuccData->mFoundCardinality; mergeableCardinality = mergingSuccData->mMergeableCardinality; minCardinality = mergingSuccData->mMinCardinality;  // refs
        //           succHash = linkedSuccHash->getLinkedRoleSuccessorHash(); succData = succHash->value(role);
        //           if (succData && succData->mSuccCount >= allowedCardinality) {
        //               mergingSuccDataLinker = mergingSuccData->mSuccessorLinkMergingLinker;   // ref
        //               lastSuccessorNode = mergingSuccData->mLastSuccessorNode; lastSuccessorCreationRoleLinker = mergingSuccData->mLastSuccessorCreationRoleLinker;  // refs
        //               remainMergeableCardHash = atmostSuccMergingData->getRemainingMergeableCardinalityHash();
        //               mergeDistintHash = atmostSuccMergingData->getMergingDistintHash(); mergeDistintSet = atmostSuccMergingData->getMergingDistintSet();
        //               if (!mergingSuccData->mInitialized) {
        //                   mergingSuccData->mInitialized = true;
        //                   foundCardinality = collectATMOSTConceptRelevantSuccessors(conDes, indiProcSatNode, succData, mergingSuccDataLinker, lastSuccessorNode, lastSuccessorCreationRoleLinker, minCardinality, ctx);
        //                   if (foundCardinality >= allowedCardinality && foundCardinality > 1 && mergingSuccDataLinker) {
        //                       if (mConfSimpleMergingTestForATMOSTCriticalTesting)
        //                           for (it = mergingSuccDataLinker; it && foundCardinality-mergeableCardinality >= allowedCardinality; it = it->getNext()) {
        //                               succLinkData = it->getData();
        //                               if (succLinkData->mSuccCount >= 1) {
        //                                   maxRequiredMergingCardinality = foundCardinality-mergeableCardinality-(allowedCardinality-1);
        //                                   mergingCardinality = getSuccessorLinkSimplyMergeableCardinalityCount(indiProcSatNode, succLinkData, mergingSuccDataLinker, remainMergeableCardHash, role, maxRequiredMergingCardinality, mergeDistintHash, mergeDistintSet, ctx);
        //                                   remainingCardinality = succLinkData->mSuccCount-mergingCardinality;
        //                                   remainMergeableCardHash->insert(succLinkData, remainingCardinality);
        //                                   if (remainingCardinality <= 0)
        //                                       for (creationRoleIt in succLinkData->mCreationRoleLinker) if (!negated)
        //                                           for (superRoleIt in creationRole->getIndirectSuperRoleList()) if (!negated)
        //                                               linkedSuccHash->deactivateLinkedSuccessor(superRole, succLinkData->mSuccIndiNode, creationRole);
        //                                   mergeableCardinality += mergingCardinality;
        //                               }
        //                           }
        //                       if (mConfDetailedMergingTestForATMOSTCriticalTesting && foundCardinality-mergeableCardinality >= allowedCardinality && foundCardinality-mergeableCardinality <= allowedCardinality*2)
        //                           for (it = mergingSuccDataLinker; it && foundCardinality-mergeableCardinality >= allowedCardinality; it = it->getNext()) {
        //                               succLinkData = it->getData(); mergedSuccLinkData = nullptr;
        //                               if (succLinkData->mSuccCount >= 1) {
        //                                   succRemainingCardinality = remainMergeableCardHash->value(succLinkData, succLinkData->mSuccCount);
        //                                   if (succRemainingCardinality > 0) {
        //                                       maxRequiredMergingCardinality = foundCardinality-mergeableCardinality-(allowedCardinality-1);
        //                                       mergingCardinality = getSuccessorLinkExtendedMergeableCardinalityCount(indiProcSatNode, succLinkData, &mergedSuccLinkData, it->getNext(), remainMergeableCardHash, role, maxRequiredMergingCardinality, mergeDistintHash, mergeDistintSet, ctx);
        //                                       if (mergingCardinality > 0) {
        //                                           newSuccCard = qMax(succRemainingCardinality, mergingCardinality);
        //                                           copyIndiProcSatNode = succLinkData->mSuccIndiNode;
        //                                           resolveData = copyIndiProcSatNode->getSuccessorExtensionData(true)->getBaseExtensionResolveData(true);
        //                                           resolveData = getResolvedIndividualNodeExtension(resolveData, mergedSuccLinkData->mSuccIndiNode, copyIndiProcSatNode, ctx);  // sibling
        //                                           resolvedIndiProcSatNode = resolveData->getProcessingIndividualNode();
        //                                           incrSuccCard = qMax(mergingCardinality,succRemainingCardinality)-qMin(mergingCardinality,succRemainingCardinality);
        //                                           newMergingSuccDataLinker = reconnectMergedLinkedSuccessors(succLinkData, mergedSuccLinkData, newSuccCard, incrSuccCard, linkedSuccHash, succData, mergeDistintHash, mergeDistintSet, remainMergeableCardHash, indiProcSatNode, resolvedIndiProcSatNode, ctx);
        //                                           if (newMergingSuccDataLinker) mergingSuccDataLinker = newMergingSuccDataLinker->append(mergingSuccDataLinker);
        //                                           removedSuccCard = qMin(succRemainingCardinality, mergingCardinality); mergeableCardinality += removedSuccCard;
        //                                       }
        //                                   }
        //                               }
        //                           }
        //                   }
        //               }
        //               nodeExpansionRequired = false;
        //               while (mergingSuccDataLinker && foundCardinality-mergeableCardinality >= allowedCardinality && !nodeExpansionRequired) {
        //                   succLinkData = mergingSuccDataLinker->getData();
        //                   if (succLinkData->mSuccCount >= 1) {
        //                       succRemainingCardinality = remainMergeableCardHash->value(succLinkData, succLinkData->mSuccCount);
        //                       if (succRemainingCardinality > 0)
        //                           for (it = mergingSuccDataLinker->getNext(); it && foundCardinality-mergeableCardinality >= allowedCardinality && foundCardinality-mergeableCardinality > minCardinality; it = it->getNext()) {
        //                               mergeSuccLinkData = it->getData();
        //                               if (mergeSuccLinkData->mSuccCount >= 1 && !mergeDistintSet->contains(QPair(qMin(mergeSuccLinkData,succLinkData), qMax(mergeSuccLinkData,succLinkData)))) {
        //                                   mergingCardinality = remainMergeableCardHash->value(mergeSuccLinkData, mergeSuccLinkData->mSuccCount);
        //                                   if (mergingCardinality > 0) {
        //                                       newNodeExpansionCreated = false; copyIndiProcSatNode = succLinkData->mSuccIndiNode;
        //                                       resolveData = copyIndiProcSatNode->getSuccessorExtensionData(true)->getBaseExtensionResolveData(true);
        //                                       resolveData = getResolvedIndividualNodeExtension(resolveData, mergeSuccLinkData->mSuccIndiNode, copyIndiProcSatNode, &newNodeExpansionCreated, ctx);
        //                                       if (newNodeExpansionCreated) nodeExpansionRequired = true;
        //                                       else {
        //                                           resolvedIndiProcSatNode = resolveData->getProcessingIndividualNode();
        //                                           resolvedNodesFlags = resolvedIndiProcSatNode->getIndirectStatusFlags();
        //                                           if (!resolvedNodesFlags->hasClashedFlag() && !resolvedNodesFlags->hasInsufficientFlag()) {
        //                                               resolvedIndiProcSatNode = resolveData->getProcessingIndividualNode();
        //                                               if (!testMergedSuccessorLinkingProblematic(conDes, succLinkData, mergeSuccLinkData, resolvedIndiProcSatNode, succData, indiProcSatNode, ctx)) {
        //                                                   newSuccCard = qMax(mergingCardinality, succRemainingCardinality);
        //                                                   incrSuccCard = qMax(mergingCardinality,succRemainingCardinality)-qMin(mergingCardinality,succRemainingCardinality);
        //                                                   newMergingSuccDataLinker = reconnectMergedLinkedSuccessors(succLinkData, mergeSuccLinkData, newSuccCard, incrSuccCard, linkedSuccHash, succData, mergeDistintHash, mergeDistintSet, remainMergeableCardHash, indiProcSatNode, resolvedIndiProcSatNode, ctx);
        //                                                   if (newMergingSuccDataLinker) mergingSuccDataLinker = newMergingSuccDataLinker->append(mergingSuccDataLinker);
        //                                                   removedSuccCard = qMin(succRemainingCardinality, mergingCardinality); mergeableCardinality += removedSuccCard;
        //                                               }
        //                                           }
        //                                       }
        //                                   }
        //                               }
        //                           }
        //                   }
        //               }
        //               if (foundCardinality-mergeableCardinality == allowedCardinality || minCardinality >= allowedCardinality) {
        //                   ancestorPossiblyCriticalFlag = true;
        //                   if (allowedCardinality == 1) { functionallyRestrictedSuccessorNode = lastSuccessorNode; functionallyRestrictedSuccessorCreationRoleLinker = lastSuccessorCreationRoleLinker; }
        //               }
        //               if (foundCardinality-mergeableCardinality > allowedCardinality) nodeInsufficient = true;
        //               return nodeExpansionRequired;
        //           }
        //       }
        //   }
        //   return false;
        // CSaturationATMOSTSuccessorMergingData / ...HashData / CLinkedRoleSaturationSuccessorHash
        // / CSaturationSuccessorData / CSaturationIndividualNodeExtensionResolveData
        // satellites + the collect/getSimply/getExtended/reconnect/testProblematic
        // siblings (this unit) and getResolvedIndividualNodeExtension /
        // collectLinkedSuccessorNodes (other units) not yet ported.
        let _ = (
            con_des,
            merging_succ_data,
            node_insufficient,
            ancestor_possibly_critical_flag,
            functionally_restricted_successor_node,
            functionally_restricted_successor_creation_role_linker,
            indi_proc_sat_node,
        );
        false
    }

    // =======================================================================
    // Cardinality-mergeability predicates (cpp 4467–4493, 4599–4635).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isIndividualSuccessorLinkCardinalityMergeable`
    /// (the `CSaturationSuccessorData*`/`CSaturationSuccessorData*` dispatcher overload). cpp 4467–4471.
    ///
    /// Unwraps both successor data's `mSuccIndiNode` and delegates to `_for_nodes`.
    pub fn is_individual_successor_link_cardinality_mergeable(
        &mut self,
        // `CSaturationSuccessorData* subsetIndiSuccData`
        subset_indi_succ_data: SaturationSuccessorDataId,
        // `CSaturationSuccessorData* superIndiSuccData`
        super_indi_succ_data: SaturationSuccessorDataId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let subset_indi_succ_node = calc_alg_context
            .process_context()
            .sat_succ_data(subset_indi_succ_data)
            .get_successor_individual_node();
        let super_indi_succ_node = calc_alg_context
            .process_context()
            .sat_succ_data(super_indi_succ_data)
            .get_successor_individual_node();
        self.is_individual_successor_link_cardinality_mergeable_for_nodes(
            subset_indi_succ_node,
            subset_indi_succ_data,
            super_indi_succ_node,
            super_indi_succ_data,
            calc_alg_context,
        )
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isIndividualSuccessorLinkCardinalityMergeable`
    /// (the explicit-node worker overload). cpp 4473–4493. [overload] `_for_nodes` suffix.
    ///
    /// True when two role successors can be cardinality-merged: neither is a
    /// VALUE-nominal connection, neither node is nominal-integrated,
    /// ABox-representation, nor data-value-applied; the subset creation-role set is
    /// a merging subset of the super set; and the subset label is a merging subset
    /// (AND-concepts ignored).
    pub fn is_individual_successor_link_cardinality_mergeable_for_nodes(
        &mut self,
        // `CIndividualSaturationProcessNode* subsetIndiSuccNode`
        subset_indi_succ_node: SatNodeId,
        subset_indi_succ_data: SaturationSuccessorDataId,
        super_indi_succ_node: SatNodeId,
        super_indi_succ_data: SaturationSuccessorDataId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let (
            subset_value_nominal,
            subset_creation_roles,
            super_value_nominal,
            super_creation_roles,
        ) = {
            let process_context = calc_alg_context.process_context();
            let subset_data = process_context.sat_succ_data(subset_indi_succ_data);
            let super_data = process_context.sat_succ_data(super_indi_succ_data);
            (
                subset_data.value_nominal_connection,
                subset_data.creation_role_linker.clone(),
                super_data.value_nominal_connection,
                super_data.creation_role_linker.clone(),
            )
        };
        if subset_value_nominal || super_value_nominal {
            return false;
        }
        {
            let process_context = calc_alg_context.process_context();
            let subset_node = process_context.sat_node(subset_indi_succ_node);
            let super_node = process_context.sat_node(super_indi_succ_node);
            if subset_node.has_nominal_integrated() || super_node.has_nominal_integrated() {
                return false;
            }
            if subset_node.is_abox_individual_representation_node()
                || super_node.is_abox_individual_representation_node()
            {
                return false;
            }
            if subset_node.has_data_value_applied() || super_node.has_data_value_applied() {
                return false;
            }
        }
        if !self.is_successor_creation_role_merging_subset(
            &subset_creation_roles,
            &super_creation_roles,
            calc_alg_context,
        ) {
            return false;
        }
        if !self.is_individual_node_label_merging_subset(
            subset_indi_succ_node,
            super_indi_succ_node,
            true,
            calc_alg_context,
        ) {
            return false;
        }
        true
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isIndividualSuccessorLinkCardinalityExtendedMergeable`
    /// (the `CSaturationSuccessorData*`/`CSaturationSuccessorData*` dispatcher overload). cpp 4599–4603.
    ///
    /// Unwraps both successor data's `mSuccIndiNode` and delegates to `_for_nodes`.
    pub fn is_individual_successor_link_cardinality_extended_mergeable(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        // `CSaturationSuccessorData* indiSuccData1`
        indi_succ_data1: SaturationSuccessorDataId,
        // `CSaturationSuccessorData* indiSuccData2`
        indi_succ_data2: SaturationSuccessorDataId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let indi_succ_node1 = calc_alg_context
            .process_context()
            .sat_succ_data(indi_succ_data1)
            .get_successor_individual_node();
        let indi_succ_node2 = calc_alg_context
            .process_context()
            .sat_succ_data(indi_succ_data2)
            .get_successor_individual_node();
        self.is_individual_successor_link_cardinality_extended_mergeable_for_nodes(
            indi_proc_sat_node,
            indi_succ_node1,
            indi_succ_data1,
            indi_succ_node2,
            indi_succ_data2,
            calc_alg_context,
        )
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isIndividualSuccessorLinkCardinalityExtendedMergeable`
    /// (the explicit-node worker overload). cpp 4605–4635. [overload] `_for_nodes` suffix.
    ///
    /// The symmetric extended variant: neither VALUE-nominal, nominal-integrated,
    /// data-value-applied, nor ABox-representation; creation-role sets are merging
    /// subsets BOTH ways; and neither node's label merge is problematic for the other
    /// (via `isIndividualNodeLabelMergingProblematic` in both directions).
    pub fn is_individual_successor_link_cardinality_extended_mergeable_for_nodes(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        indi_succ_node1: SatNodeId,
        indi_succ_data1: SaturationSuccessorDataId,
        indi_succ_node2: SatNodeId,
        indi_succ_data2: SaturationSuccessorDataId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let (value_nominal1, creation_roles1, value_nominal2, creation_roles2) = {
            let process_context = calc_alg_context.process_context();
            let data1 = process_context.sat_succ_data(indi_succ_data1);
            let data2 = process_context.sat_succ_data(indi_succ_data2);
            (
                data1.value_nominal_connection,
                data1.creation_role_linker.clone(),
                data2.value_nominal_connection,
                data2.creation_role_linker.clone(),
            )
        };
        if value_nominal1 || value_nominal2 {
            return false;
        }
        {
            let process_context = calc_alg_context.process_context();
            let node1 = process_context.sat_node(indi_succ_node1);
            let node2 = process_context.sat_node(indi_succ_node2);
            if node1.has_nominal_integrated() || node2.has_nominal_integrated() {
                return false;
            }
            if node1.has_data_value_applied() || node2.has_data_value_applied() {
                return false;
            }
            if node1.is_abox_individual_representation_node()
                || node2.is_abox_individual_representation_node()
            {
                return false;
            }
        }
        if !self.is_successor_creation_role_merging_subset(
            &creation_roles1,
            &creation_roles2,
            calc_alg_context,
        ) {
            return false;
        }
        if !self.is_successor_creation_role_merging_subset(
            &creation_roles2,
            &creation_roles1,
            calc_alg_context,
        ) {
            return false;
        }
        if self.is_individual_node_label_merging_problematic(
            indi_proc_sat_node,
            indi_succ_node1,
            indi_succ_node2,
            creation_roles1,
            calc_alg_context,
        ) {
            return false;
        }
        if self.is_individual_node_label_merging_problematic(
            indi_proc_sat_node,
            indi_succ_node2,
            indi_succ_node1,
            creation_roles2,
            calc_alg_context,
        ) {
            return false;
        }
        true
    }

    // =======================================================================
    // Simply-mergeable cardinality count (cpp 4498–4580).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getSuccessorLinkSimplyMergeableCardinalityCount`.
    /// cpp 4498–4580.
    ///
    /// Computes how much of `succLinkData`'s cardinality can be folded into the other
    /// merging successors. If some other successor with cardinality ≥ `succLinkData`'s
    /// is (cardinality-)mergeable and distinct-compatible, the whole remaining
    /// cardinality merges. Otherwise greedily merges into smaller mergeable successors
    /// up to `maxRequiredMergingCardinality`, marking pairwise-distinct successors as
    /// mutually distinct when an "into-all-mergeable" test fails. Returns the merged
    /// cardinality.
    pub fn get_successor_link_simply_mergeable_cardinality_count(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        // `CSaturationSuccessorData* succLinkData`
        succ_link_data: SaturationSuccessorDataId,
        // `CIndividualSaturationSuccessorLinkDataLinker* mergingSuccDataLinker`
        merging_succ_data_linker: IndividualSaturationSuccessorLinkDataLinkerId,
        // `CPROCESSHASH<CSaturationSuccessorData*,cint64>* remainMergeableCardHash`
        remain_mergeable_card_hash: &mut std::collections::HashMap<
            SaturationSuccessorDataId,
            Cint64,
        >,
        role: RoleId,
        max_required_merging_cardinality: Cint64,
        // `CPROCESSHASH<CSaturationSuccessorData*,CSaturationSuccessorData*>* mergeDistintHash`
        merge_distint_hash: &mut std::collections::HashMap<
            SaturationSuccessorDataId,
            Vec<SaturationSuccessorDataId>,
        >,
        // `CPROCESSSET< QPair<...> >* mergeDistintSet`
        merge_distint_set: &mut std::collections::HashSet<(
            SaturationSuccessorDataId,
            SaturationSuccessorDataId,
        )>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        let succ_count = calc_alg_context
            .process_context()
            .sat_succ_data(succ_link_data)
            .get_successor_count();
        let mut remaining_cardinality = succ_count;
        let mut into_all_mergeable = false;
        let mut into_all_mergeable_checked = false;

        let mut merging_succ_data_linker_it = merging_succ_data_linker;
        while merging_succ_data_linker_it.is_some() {
            let (merge_succ_link_data, next_linker) = {
                let linker = calc_alg_context
                    .process_context()
                    .indi_sat_succ_link_data_linker(merging_succ_data_linker_it);
                (linker.get_data(), linker.get_next())
            };
            if merge_succ_link_data != succ_link_data {
                let default_mergeable_cardinality = calc_alg_context
                    .process_context()
                    .sat_succ_data(merge_succ_link_data)
                    .get_successor_count();
                let mergeable_cardinality = remain_mergeable_card_hash
                    .get(&merge_succ_link_data)
                    .copied()
                    .unwrap_or(default_mergeable_cardinality);
                if mergeable_cardinality >= succ_count {
                    if !merge_distint_set.contains(&Self::successor_data_pair(
                        merge_succ_link_data,
                        succ_link_data,
                    )) {
                        if self.is_individual_successor_link_cardinality_mergeable(
                            succ_link_data,
                            merge_succ_link_data,
                            calc_alg_context,
                        ) {
                            return remaining_cardinality;
                        }
                        into_all_mergeable_checked = true;
                    } else {
                        into_all_mergeable_checked = true;
                    }
                }
            }
            merging_succ_data_linker_it = next_linker;
        }

        let mut merged_cardinality: Cint64 = 0;
        merging_succ_data_linker_it = merging_succ_data_linker;
        while merging_succ_data_linker_it.is_some()
            && remaining_cardinality > 0
            && merged_cardinality < max_required_merging_cardinality
        {
            let (merge_succ_link_data, next_linker) = {
                let linker = calc_alg_context
                    .process_context()
                    .indi_sat_succ_link_data_linker(merging_succ_data_linker_it);
                (linker.get_data(), linker.get_next())
            };
            if merge_succ_link_data != succ_link_data {
                let default_mergeable_cardinality = calc_alg_context
                    .process_context()
                    .sat_succ_data(merge_succ_link_data)
                    .get_successor_count();
                let mergeable_cardinality = remain_mergeable_card_hash
                    .get(&merge_succ_link_data)
                    .copied()
                    .unwrap_or(default_mergeable_cardinality);
                if mergeable_cardinality > 0 && mergeable_cardinality < succ_count {
                    let merge_pair =
                        Self::successor_data_pair(merge_succ_link_data, succ_link_data);
                    if !merge_distint_set.contains(&merge_pair) {
                        if into_all_mergeable
                            || self.is_individual_successor_link_cardinality_mergeable(
                                succ_link_data,
                                merge_succ_link_data,
                                calc_alg_context,
                            )
                        {
                            if !into_all_mergeable_checked {
                                into_all_mergeable = true;
                                let mut rem_test_succ_data_linker_it = next_linker;
                                while rem_test_succ_data_linker_it.is_some() {
                                    let (rem_test_succ_link_data, rem_next_linker) = {
                                        let linker = calc_alg_context
                                            .process_context()
                                            .indi_sat_succ_link_data_linker(
                                                rem_test_succ_data_linker_it,
                                            );
                                        (linker.get_data(), linker.get_next())
                                    };
                                    if rem_test_succ_link_data != succ_link_data
                                        && rem_test_succ_link_data != merge_succ_link_data
                                    {
                                        let default_mergeable_cardinality = calc_alg_context
                                            .process_context()
                                            .sat_succ_data(rem_test_succ_link_data)
                                            .get_successor_count();
                                        let rem_mergeable_cardinality = remain_mergeable_card_hash
                                            .get(&rem_test_succ_link_data)
                                            .copied()
                                            .unwrap_or(default_mergeable_cardinality);
                                        if rem_mergeable_cardinality > 0
                                            && rem_mergeable_cardinality < succ_count
                                            && !merge_distint_set.contains(
                                                &Self::successor_data_pair(
                                                    rem_test_succ_link_data,
                                                    succ_link_data,
                                                ),
                                            )
                                            && !self
                                                .is_individual_successor_link_cardinality_mergeable(
                                                    succ_link_data,
                                                    merge_succ_link_data,
                                                    calc_alg_context,
                                                )
                                        {
                                            into_all_mergeable = false;
                                        }
                                    }
                                    rem_test_succ_data_linker_it = rem_next_linker;
                                }
                                into_all_mergeable_checked = true;
                            }

                            if !into_all_mergeable && succ_count > 1 {
                                merge_distint_set.insert(merge_pair);
                                let distinct_successors = merge_distint_hash
                                    .get(&succ_link_data)
                                    .cloned()
                                    .unwrap_or_default();
                                for dist_succ_data in distinct_successors {
                                    merge_distint_hash
                                        .entry(dist_succ_data)
                                        .or_default()
                                        .push(merge_succ_link_data);
                                    merge_distint_hash
                                        .entry(merge_succ_link_data)
                                        .or_default()
                                        .push(dist_succ_data);
                                    merge_distint_set.insert(Self::successor_data_pair(
                                        merge_succ_link_data,
                                        dist_succ_data,
                                    ));
                                }
                                merge_distint_hash
                                    .entry(succ_link_data)
                                    .or_default()
                                    .push(merge_succ_link_data);
                                merge_distint_hash
                                    .entry(merge_succ_link_data)
                                    .or_default()
                                    .push(succ_link_data);
                            }

                            let merging_cardinality =
                                remaining_cardinality.min(mergeable_cardinality);
                            remaining_cardinality -= merging_cardinality;
                            merged_cardinality += merging_cardinality;
                        } else {
                            into_all_mergeable_checked = true;
                        }
                    } else {
                        into_all_mergeable_checked = true;
                    }
                }
            }
            merging_succ_data_linker_it = next_linker;
        }
        merged_cardinality
    }

    // =======================================================================
    // Qualified-successor count (cpp 4637–4713).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getIndividualNodeQualifiedSuccessorCount`.
    /// cpp 4637–4713.
    ///
    /// Counts (by cardinality) `indiProcSatNode`'s role successors that are NOT
    /// provably outside the qualification `conQualificationLinker` — VALUE-nominal
    /// connections count; otherwise a successor counts unless its label contains every
    /// qualification operand with the opposite negation (or, with a non-trivial
    /// qualification, fails to contain a needed operand). Returns the summed matching
    /// successor cardinality.
    pub fn get_individual_node_qualified_successor_count(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        role: RoleId,
        // `CSortedNegLinker<CConcept*>* conQualificationLinker`
        con_qualification_linker: Option<&[NegLink<ConceptId>]>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        let mut matching_succ_count: Cint64 = 0;
        let linked_succ_hash = calc_alg_context
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(*indi_proc_sat_node, false);
        if linked_succ_hash.is_none() {
            return matching_succ_count;
        }

        let pred_succ_data = calc_alg_context
            .process_context_mut()
            .linked_role_successor_data(linked_succ_hash, role, false);
        if pred_succ_data.is_none() {
            return matching_succ_count;
        }

        let mut trivial_qualification = true;
        if let Some(con_qualification_linker) = con_qualification_linker {
            for op_linker_it in con_qualification_linker.iter() {
                let op_code = calc_alg_context
                    .ontology_arenas()
                    .concept(op_linker_it.target)
                    .get_operator_code();
                if op_linker_it.negated || (op_code != CCATOM && op_code != CCSUB) {
                    trivial_qualification = false;
                    break;
                }
            }
        }

        let succ_role_data_ids: Vec<_> = calc_alg_context
            .process_context()
            .linked_role_sat_succ_data(pred_succ_data)
            .get_successor_node_data_map()
            .values()
            .copied()
            .collect();

        for succ_role_data_id in succ_role_data_ids {
            let (active_count, succ_cardinality, value_nominal_connection, succ_node) = {
                let succ_role_data = calc_alg_context
                    .process_context()
                    .sat_succ_data(succ_role_data_id);
                (
                    succ_role_data.get_active_count(),
                    succ_role_data.get_successor_count(),
                    succ_role_data.value_nominal_connection,
                    succ_role_data.get_successor_individual_node(),
                )
            };
            if active_count < 1 {
                continue;
            }

            let mut operants_contained_negative = true;
            let mut operants_contained_positive = true;
            let mut operants_contained = true;
            if value_nominal_connection {
                operants_contained_positive = true;
            } else {
                let succ_con_set = calc_alg_context
                    .process_context_mut()
                    .sat_node_reapply_concept_saturation_label_set(succ_node, false);
                if succ_con_set.is_some() {
                    if let Some(con_qualification_linker) = con_qualification_linker {
                        for op_linker_it in con_qualification_linker.iter() {
                            if let Some(contained_negation) =
                                Self::sat_label_set_contains_concept_get_negation(
                                    succ_con_set,
                                    op_linker_it.target,
                                    calc_alg_context,
                                )
                            {
                                if contained_negation == op_linker_it.negated {
                                    operants_contained_negative = false;
                                } else {
                                    operants_contained_positive = false;
                                }
                            } else if trivial_qualification {
                                operants_contained_positive = false;
                            } else {
                                operants_contained = false;
                            }
                        }
                    } else {
                        operants_contained_negative = false;
                    }
                } else if trivial_qualification {
                    operants_contained_positive = false;
                } else {
                    operants_contained = false;
                }
            }
            let _ = operants_contained_negative;
            if operants_contained_positive || !operants_contained {
                matching_succ_count += succ_cardinality;
            }
        }
        matching_succ_count
    }

    // =======================================================================
    // Node-label merging problematic test (cpp 4716–4803).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isIndividualNodeLabelMergingProblematic`.
    /// cpp 4716–4803.
    ///
    /// For merging `mergingSuccNode` into `probTestingSuccNode`, true if any concept
    /// of the merging label conflicts in the prob-testing label (opposite negation, or
    /// an implication whose body operand is absent from both), or — for concepts not
    /// present in the prob-testing label — if the concept is "critical": it would
    /// re-trigger a predecessor ATMOST/¬ATLEAST over the allowance, or it is a
    /// propagation ∀/¬∃-family concept whose role already has a prob-testing linked
    /// successor, or a ∃/self/≥ (resp. ∀/≤) concept whose super-role has a pending
    /// backward-propagation reapply linker. Returns whether merging is problematic.
    pub fn is_individual_node_label_merging_problematic(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        // `CIndividualSaturationProcessNode* mergingSuccNode`
        merging_succ_node: SatNodeId,
        // `CIndividualSaturationProcessNode* probTestingSuccNode`
        prob_testing_succ_node: SatNodeId,
        // `CXNegLinker<CRole*>* creationRoleLinker`
        creation_role_linker: Vec<NegLink<RoleId>>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let merging_con_set = calc_alg_context
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(merging_succ_node, false);
        let prop_test_con_set = calc_alg_context
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(prob_testing_succ_node, false);
        if merging_con_set.is_none() || prop_test_con_set.is_none() {
            return false;
        }

        let mut merging_iterator = calc_alg_context
            .process_context()
            .reapply_con_sat_label_set(merging_con_set)
            .get_iterator(true, false);
        while merging_iterator.has_next() {
            let con_des = merging_iterator.get_concept_saturation_descriptor();
            if con_des.is_some() {
                let (concept, negation, con_tag) = {
                    let process_context = calc_alg_context.process_context();
                    let con_des_ref = process_context.con_sat_desc(con_des);
                    let concept = con_des_ref.get_concept();
                    let negation = con_des_ref.get_negation();
                    let con_tag = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_concept_tag();
                    (concept, negation, con_tag)
                };

                let mut prop_test_con_des = ConceptSaturationDescriptorId::NONE;
                let mut prop_test_imp_reap_des =
                    ImplicationReapplyConceptSaturationDescriptorId::NONE;
                let contained = calc_alg_context
                    .process_context()
                    .reapply_con_sat_label_set(prop_test_con_set)
                    .get_concept_descriptor_and_reapply_queue_by_tag(
                        con_tag,
                        &mut prop_test_con_des,
                        &mut prop_test_imp_reap_des,
                    );
                if contained {
                    if prop_test_con_des.is_some() {
                        if calc_alg_context
                            .process_context()
                            .con_sat_desc(prop_test_con_des)
                            .get_negation()
                            != negation
                        {
                            return true;
                        }
                    } else if !negation && prop_test_imp_reap_des.is_some() {
                        let prop_test_imp_con = calc_alg_context
                            .process_context()
                            .imp_reapply_con_sat_desc(prop_test_imp_reap_des)
                            .get_implication_concept();
                        let first_operand = calc_alg_context
                            .ontology_arenas()
                            .concept(prop_test_imp_con)
                            .get_operand_list()
                            .first()
                            .map(|link| link.target);
                        if let Some(first_operand) = first_operand {
                            let first_operand_tag = calc_alg_context
                                .ontology_arenas()
                                .concept(first_operand)
                                .get_concept_tag();
                            let prop_test_contains = calc_alg_context
                                .process_context()
                                .reapply_con_sat_label_set(prop_test_con_set)
                                .contains_concept_or_reaplly_queue(first_operand_tag);
                            let merging_contains = calc_alg_context
                                .process_context()
                                .reapply_con_sat_label_set(merging_con_set)
                                .contains_concept_or_reaplly_queue(first_operand_tag);
                            if !prop_test_contains && !merging_contains {
                                return true;
                            }
                        }
                    }
                } else {
                    // Concept absent in `propTestConSet` — "test whether concept is
                    // critical" (cpp 4736-4805). Any hit means merging COULD trip a
                    // cardinality/propagation interaction ⇒ problematic (true).

                    // (1) Predecessor-label ≤n / ¬≥n re-count: an ATMOST (or negated
                    // ATLEAST) on the merged-INTO predecessor whose role is reached by
                    // a creation super-role, re-counted against its bound.
                    let pred_con_set = calc_alg_context
                        .process_context_mut()
                        .sat_node_reapply_concept_saturation_label_set(*indi_proc_sat_node, false);
                    if pred_con_set.is_some() {
                        let mut pred_iterator = calc_alg_context
                            .process_context()
                            .reapply_con_sat_label_set(pred_con_set)
                            .get_iterator(true, false);
                        while pred_iterator.has_next() {
                            let pred_con_des = pred_iterator.get_concept_saturation_descriptor();
                            if pred_con_des.is_some() {
                                let (pred_concept_orig, pred_con_negation) = {
                                    let con_des_ref =
                                        calc_alg_context.process_context().con_sat_desc(pred_con_des);
                                    (con_des_ref.get_concept(), con_des_ref.get_negation())
                                };
                                let pred_con_op_code = calc_alg_context
                                    .ontology_arenas()
                                    .concept(pred_concept_orig)
                                    .get_operator_code();
                                if (pred_con_negation && pred_con_op_code == CCATLEAST)
                                    || (!pred_con_negation && pred_con_op_code == CCATMOST)
                                {
                                    // C++: `predOpCon = predConcept = predConcept->getOperandList()->getData();`
                                    // — the chained assignment REASSIGNS predConcept to the first
                                    // operand (ported faithfully: for a QUALIFIED at-most the
                                    // operand's role is a concept-role mismatch, so the re-count
                                    // below effectively fires for unqualified at-mosts only).
                                    let mut pred_concept = pred_concept_orig;
                                    let mut pred_op_con = ConceptId::NONE;
                                    if let Some(first_op) = calc_alg_context
                                        .ontology_arenas()
                                        .concept(pred_concept_orig)
                                        .get_operand_list()
                                        .first()
                                    {
                                        pred_op_con = first_op.target;
                                        pred_concept = first_op.target;
                                    }
                                    if pred_op_con.is_none() || pred_op_con == concept {
                                        let (pred_role, pred_parameter, pred_operands) = {
                                            let pred_concept_ref =
                                                calc_alg_context.ontology_arenas().concept(pred_concept);
                                            (
                                                pred_concept_ref.get_role(),
                                                pred_concept_ref.get_parameter(),
                                                pred_concept_ref.get_operand_list().to_vec(),
                                            )
                                        };
                                        for creation_role_it in
                                            creation_role_linker.iter().filter(|l| !l.negated)
                                        {
                                            // KONCLUDE-PORT-NOTE[identity]: saturation-side
                                            // super-role walk — self-inclusive helper.
                                            let creation_super_roles =
                                                Self::saturation_indirect_super_roles(
                                                    creation_role_it.target,
                                                    calc_alg_context,
                                                );
                                            for creation_super_role_it in
                                                creation_super_roles.iter().filter(|l| !l.negated)
                                            {
                                                let creation_super_role = creation_super_role_it.target;
                                                if creation_super_role == pred_role {
                                                    let allowed_cardinality = pred_parameter
                                                        - Cint64::from(pred_con_negation);
                                                    let qualification = if pred_operands.is_empty() {
                                                        None
                                                    } else {
                                                        Some(pred_operands.as_slice())
                                                    };
                                                    if self.get_individual_node_qualified_successor_count(
                                                        indi_proc_sat_node,
                                                        creation_super_role,
                                                        qualification,
                                                        calc_alg_context,
                                                    ) > allowed_cardinality
                                                    {
                                                        return true;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            pred_iterator.move_next();
                        }
                    }

                    let (op_code, con_op, con_role) = {
                        let concept_ref = calc_alg_context.ontology_arenas().concept(concept);
                        (
                            concept_ref.get_operator_code(),
                            concept_ref.get_concept_operator(),
                            concept_ref.get_role(),
                        )
                    };

                    // (2) ∀/¬∃/≤/¬≥ over a role the prob-testing successor already has
                    // linked successors for — merging would demand new propagation.
                    if (!negation && con_op.has_partial_operator_code_flag(CCFS_AQALL_TYPE))
                        || (negation && con_op.has_partial_operator_code_flag(CCFS_SOME_TYPE))
                        || (!negation && op_code == CCATMOST)
                        || (negation && op_code == CCATLEAST)
                    {
                        let mut prob_node = prob_testing_succ_node;
                        self.collect_linked_successor_nodes(&mut prob_node, calc_alg_context, INVALID);
                        let prop_test_linked_succ_hash = calc_alg_context
                            .process_context_mut()
                            .sat_node_ext_linked_role_successor_hash(prob_testing_succ_node, false);
                        if prop_test_linked_succ_hash.is_some() && con_role.is_some() {
                            // hasLinkedRoleSuccessorData(role): value(role) && mSuccCount > 0.
                            let role_succ_data = calc_alg_context
                                .process_context()
                                .linked_role_sat_succ_hash(prop_test_linked_succ_hash)
                                .role_succ_data_hash
                                .get(&con_role)
                                .copied();
                            if let Some(role_succ_data) = role_succ_data.filter(|d| d.is_some()) {
                                if calc_alg_context
                                    .process_context()
                                    .linked_role_sat_succ_data(role_succ_data)
                                    .succ_count
                                    > 0
                                {
                                    return true;
                                }
                            }
                        }
                    }

                    // (3) ∃/Self/≥ (or ¬∀/¬≤) whose role has backward-propagation
                    // reapply descriptors on the prob-testing successor.
                    if (!negation
                        && con_op.has_partial_operator_code_flag(
                            CCFS_SOME_TYPE | CCF_SELF | CCF_ATLEAST,
                        ))
                        || (negation
                            && con_op
                                .has_partial_operator_code_flag(CCFS_AQALL_TYPE | CCF_ATMOST))
                    {
                        let prop_test_backward_prop_hash = calc_alg_context
                            .process_context()
                            .sat_node(prob_testing_succ_node)
                            .role_back_prop_hash;
                        if prop_test_backward_prop_hash.is_some() && con_role.is_some() {
                            // KONCLUDE-PORT-NOTE[identity]: saturation-side super-role walk.
                            let super_roles =
                                Self::saturation_indirect_super_roles(con_role, calc_alg_context);
                            for super_role_it in super_roles.iter().filter(|l| !l.negated) {
                                let has_reapply = calc_alg_context
                                    .process_context()
                                    .role_backward_sat_prop_hash(prop_test_backward_prop_hash)
                                    .get_role_backward_propagation_data_hash()
                                    .get(&super_role_it.target)
                                    .map(|data| data.reapply_linker.is_some())
                                    .unwrap_or(false);
                                if has_reapply {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
            merging_iterator.move_next();
        }
        false
    }

    // =======================================================================
    // Extended-mergeable cardinality count (cpp 4808–4831).
    // =======================================================================

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getSuccessorLinkExtendedMergeableCardinalityCount`.
    /// cpp 4808–4831.
    ///
    /// Finds the first other merging successor that is extended-cardinality-mergeable
    /// with `succLinkData` and distinct-compatible; folds its remaining cardinality to
    /// zero, propagates the merge-distinctness relation, reports it through
    /// `mergedSuccLinkData`, and returns its mergeable cardinality (0 when none).
    pub fn get_successor_link_extended_mergeable_cardinality_count(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        // `CSaturationSuccessorData* succLinkData`
        succ_link_data: SaturationSuccessorDataId,
        // `CSaturationSuccessorData** mergedSuccLinkData` (out)
        merged_succ_link_data: Option<&mut SaturationSuccessorDataId>,
        // `CIndividualSaturationSuccessorLinkDataLinker* mergingSuccDataLinker`
        merging_succ_data_linker: IndividualSaturationSuccessorLinkDataLinkerId,
        // `CPROCESSHASH<CSaturationSuccessorData*,cint64>* remainMergeableCardHash`
        remain_mergeable_card_hash: &mut std::collections::HashMap<
            SaturationSuccessorDataId,
            Cint64,
        >,
        role: RoleId,
        max_required_merging_cardinality: Cint64,
        // `CPROCESSHASH<CSaturationSuccessorData*,CSaturationSuccessorData*>* mergeDistintHash`
        merge_distint_hash: &mut std::collections::HashMap<
            SaturationSuccessorDataId,
            Vec<SaturationSuccessorDataId>,
        >,
        // `CPROCESSSET< QPair<...> >* mergeDistintSet`
        merge_distint_set: &mut std::collections::HashSet<(
            SaturationSuccessorDataId,
            SaturationSuccessorDataId,
        )>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        let mut merged_succ_link_data = merged_succ_link_data;
        let mut merging_succ_data_linker_it = merging_succ_data_linker;
        while merging_succ_data_linker_it.is_some() {
            let (merge_succ_link_data, next_linker) = {
                let linker = calc_alg_context
                    .process_context()
                    .indi_sat_succ_link_data_linker(merging_succ_data_linker_it);
                (linker.get_data(), linker.get_next())
            };
            let default_mergeable_cardinality = calc_alg_context
                .process_context()
                .sat_succ_data(merge_succ_link_data)
                .get_successor_count();
            let mergeable_cardinality = remain_mergeable_card_hash
                .get(&merge_succ_link_data)
                .copied()
                .unwrap_or(default_mergeable_cardinality);
            if mergeable_cardinality > 0
                && !merge_distint_set.contains(&Self::successor_data_pair(
                    merge_succ_link_data,
                    succ_link_data,
                ))
                && self.is_individual_successor_link_cardinality_extended_mergeable(
                    indi_proc_sat_node,
                    succ_link_data,
                    merge_succ_link_data,
                    calc_alg_context,
                )
            {
                remain_mergeable_card_hash.insert(merge_succ_link_data, 0);
                let distinct_successors = merge_distint_hash
                    .get(&succ_link_data)
                    .cloned()
                    .unwrap_or_default();
                for dist_succ_data in distinct_successors {
                    merge_distint_hash
                        .entry(dist_succ_data)
                        .or_default()
                        .push(merge_succ_link_data);
                    merge_distint_hash
                        .entry(merge_succ_link_data)
                        .or_default()
                        .push(dist_succ_data);
                    merge_distint_set.insert(Self::successor_data_pair(
                        merge_succ_link_data,
                        dist_succ_data,
                    ));
                }
                if let Some(out_merged_succ_link_data) = merged_succ_link_data.as_deref_mut() {
                    *out_merged_succ_link_data = merge_succ_link_data;
                }
                return mergeable_cardinality;
            }
            merging_succ_data_linker_it = next_linker;
        }
        0
    }

    fn successor_data_pair(
        first: SaturationSuccessorDataId,
        second: SaturationSuccessorDataId,
    ) -> (SaturationSuccessorDataId, SaturationSuccessorDataId) {
        if first.raw <= second.raw {
            (first, second)
        } else {
            (second, first)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::completion::context::CalculationAlgorithmContextBase;
    use super::super::super::model::concept::Concept;
    use super::super::super::model::op::{CCATMOST, CCATOM, CCTOP};
    use super::super::super::model::role::Role;
    use super::super::super::process::sat_linker::IndividualSaturationProcessNodeLinker;
    use super::super::super::process::sat_node::IndividualSaturationProcessNode;
    use super::super::super::process::sat_ref::ExtendedConceptReferenceLinkingData;
    use super::super::super::saturation::satellites::{
        ConceptSaturationDescriptor, ConceptSaturationDescriptorReapplyData,
        ImplicationReapplyConceptSaturationDescriptor,
        ImplicationReapplyConceptSaturationDescriptorId,
        IndividualSaturationSuccessorLinkDataLinkerId, LinkedRoleSaturationSuccessorData,
        SaturationSuccessorData,
    };
    use super::super::algorithm::SaturationTaskHandleAlgorithm;
    use super::*;

    fn make_role(ctx: &mut CalculationAlgorithmContextBase, tag: Cint64) -> RoleId {
        let mut role = Role::new();
        role.set_role_tag(tag);
        ctx.ontology_arenas_mut().alloc_role(role)
    }

    fn atom(ctx: &mut CalculationAlgorithmContextBase, tag: Cint64) -> ConceptId {
        let mut concept = Concept::new();
        concept.set_operator_code(CCATOM).set_concept_tag(tag);
        ctx.ontology_arenas_mut().alloc_concept(concept)
    }

    fn insert_label(
        ctx: &mut CalculationAlgorithmContextBase,
        node: SatNodeId,
        concept: ConceptId,
        negated: bool,
    ) {
        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(node, true);
        let mut descriptor = ConceptSaturationDescriptor::new();
        descriptor.init_concept_saturation_descriptor(concept, negated);
        let descriptor = ctx.process_context_mut().alloc_con_sat_desc(descriptor);
        let con_tag = ctx.ontology_arenas().concept(concept).get_concept_tag();
        ctx.process_context_mut()
            .reapply_con_sat_label_set_insert_concept_return_clashed(
                label_set, descriptor, con_tag, None, None,
            );
    }

    #[test]
    fn s08_create_ancestor_successor_merging_extension_forwards_label_and_inverse_link() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role = make_role(&mut ctx, 7101);
        let inv_role = make_role(&mut ctx, 7103);
        let creation_role = make_role(&mut ctx, 7105);
        let inv_creation_role = make_role(&mut ctx, 7107);
        let creation_super_role = make_role(&mut ctx, 7109);
        ctx.ontology_arenas_mut()
            .role_mut(role)
            .set_inverse_role(inv_role);
        ctx.ontology_arenas_mut()
            .role_mut(creation_role)
            .set_inverse_role(inv_creation_role);
        ctx.ontology_arenas_mut()
            .role_mut(inv_creation_role)
            .add_indirect_super_role_linker(NegLink {
                target: creation_super_role,
                negated: false,
            });

        let mut indi = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(7201));
        let succ = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(7203));
        let anc = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(7205));
        ctx.process_context_mut()
            .sat_node_mut(indi)
            .init_individual_saturation_process_node(7201, Id::NONE, Id::NONE);
        ctx.process_context_mut()
            .sat_node_mut(succ)
            .init_individual_saturation_process_node(7203, Id::NONE, Id::NONE);
        ctx.process_context_mut()
            .sat_node_mut(anc)
            .init_individual_saturation_process_node(7205, Id::NONE, Id::NONE);
        let forwarded = atom(&mut ctx, 7211);
        insert_label(&mut ctx, succ, forwarded, false);
        ctx.process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(anc, true);

        let anc_linked_hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(anc, true);
        let anc_succ_data =
            ctx.process_context_mut()
                .linked_role_successor_data(anc_linked_hash, inv_role, true);
        let anc_succ_link = {
            let mut data = SaturationSuccessorData::new();
            data.set_successor_individual_node(indi)
                .set_successor_count(1)
                .set_active_count(1)
                .creation_role_linker
                .push(NegLink {
                    target: inv_role,
                    negated: false,
                });
            ctx.process_context_mut().alloc_sat_succ_data(data)
        };
        {
            let anc_succ_data_ref = ctx
                .process_context_mut()
                .linked_role_sat_succ_data_mut(anc_succ_data);
            anc_succ_data_ref.set_last_successor_link_data(anc_succ_link);
            anc_succ_data_ref
                .get_successor_node_data_map_mut()
                .insert(7201, anc_succ_link);
        }

        assert!(algo.create_ancestor_successor_merging_extension(
            &mut indi,
            role,
            succ,
            anc,
            vec![NegLink {
                target: creation_role,
                negated: false
            }],
            &mut ctx,
        ));

        let anc_label = ctx
            .process_context()
            .sat_node(anc)
            .reapply_con_sat_label_set;
        let mut con_des = ConceptSaturationDescriptorId::NONE;
        let mut imp_des = ImplicationReapplyConceptSaturationDescriptorId::NONE;
        let forwarded_tag = ctx.ontology_arenas().concept(forwarded).get_concept_tag();
        assert!(ctx
            .process_context()
            .reapply_con_sat_label_set(anc_label)
            .get_concept_saturation_descriptor_by_tag(forwarded_tag, &mut con_des, &mut imp_des,));
        assert!(ctx
            .process_context()
            .sat_node(succ)
            .get_copy_depending_individual_node_linker()
            .iter()
            .any(|link| link.target == anc && !link.negated));
        let func_ext = ctx
            .process_context_mut()
            .sat_node_functional_concepts_extension_data(succ, false);
        assert!(ctx
            .process_context()
            .sat_indi_node_functional_concept_ext_data(func_ext)
            .has_individual_node_forwarding_predecessor_merged(anc, creation_role));
        assert!(ctx
            .process_context()
            .linked_role_successor_hash_has_active_linked_successor(
                anc_linked_hash,
                creation_super_role,
                indi,
                Some(inv_creation_role),
                1,
            ));
        assert!(!algo.create_ancestor_successor_merging_extension(
            &mut indi,
            role,
            succ,
            anc,
            vec![NegLink {
                target: creation_role,
                negated: false
            }],
            &mut ctx,
        ));
    }

    #[test]
    fn s08_atmost_merging_driver_drains_empty_queued_node() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let mut linker = IndividualSaturationProcessNodeLinker::new();
        linker.init_process_node_linker(node, true);
        let linker = ctx
            .process_context_mut()
            .alloc_indi_sat_process_node_linker(linker);
        ctx.processing_data_box_mut()
            .set_saturation_atmost_merging_process_linker(linker);

        assert!(!algo.try_atmost_concept_successor_merging(&mut ctx));
        assert!(!ctx
            .processing_data_box()
            .has_saturation_atmost_merging_process_linker());
        assert!(!ctx
            .process_context()
            .indi_sat_process_node_linker(linker)
            .is_processing_queued());
    }

    #[test]
    fn s08_atmost_merging_driver_materializes_concept_data_and_takes_concepts() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let data = ctx
            .process_context_mut()
            .sat_node_ext_atmost_successor_merging_data(node, true);
        let con = ctx
            .process_context_mut()
            .alloc_con_sat_desc(ConceptSaturationDescriptor::new());
        ctx.process_context_mut()
            .sat_atmost_successor_merging_data_add_merging_processing_concept(data, con);

        let mut linker = IndividualSaturationProcessNodeLinker::new();
        linker.init_process_node_linker(node, true);
        let linker = ctx
            .process_context_mut()
            .alloc_indi_sat_process_node_linker(linker);
        ctx.processing_data_box_mut()
            .set_saturation_atmost_merging_process_linker(linker);

        assert!(!algo.try_atmost_concept_successor_merging(&mut ctx));
        assert_eq!(
            ctx.process_context()
                .sat_atmost_successor_merging_data(data)
                .get_merging_concept_linker(),
            Id::NONE
        );
        assert!(ctx
            .process_context_mut()
            .sat_atmost_successor_merging_data_concept_merging_hash(data, false)
            .is_some());
    }

    #[test]
    fn s08_collect_atmost_trivial_missing_operand_skips_successor_without_label_set() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let operand = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(11);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let atmost = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCATMOST)
                .set_parameter(1)
                .set_concept_tag(13)
                .add_operand_linker(operand, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let con_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(atmost, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let succ_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let succ_data = {
            let mut data = SaturationSuccessorData::new();
            data.set_successor_individual_node(succ_node)
                .set_successor_count(2)
                .set_active_count(1);
            ctx.process_context_mut().alloc_sat_succ_data(data)
        };
        let linked_data = {
            let mut data = LinkedRoleSaturationSuccessorData::new();
            data.get_successor_node_data_map_mut()
                .insert(succ_node.index() as Cint64, succ_data);
            ctx.process_context_mut()
                .alloc_linked_role_sat_succ_data(data)
        };

        let mut root_ref = root;
        let mut merging = IndividualSaturationSuccessorLinkDataLinkerId::NONE;
        let mut last_successor = SatNodeId::NONE;
        let mut last_roles = Vec::new();
        let mut min_cardinality = -1;

        let found = algo.collect_atmost_concept_relevant_successors(
            con_des,
            &mut root_ref,
            linked_data,
            &mut merging,
            &mut last_successor,
            &mut last_roles,
            &mut min_cardinality,
            &mut ctx,
        );

        assert_eq!(found, 0);
        assert_eq!(min_cardinality, 0);
        assert_eq!(merging, IndividualSaturationSuccessorLinkDataLinkerId::NONE);
        assert_eq!(last_successor, succ_node);
    }

    #[test]
    fn s08_collect_atmost_positive_operand_prepends_countable_successor() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let operand = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(21);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let atmost = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCATMOST)
                .set_parameter(1)
                .set_concept_tag(23)
                .add_operand_linker(operand, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let con_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(atmost, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let succ_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(succ_node, true);
        let operand_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(operand, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };
        let operand_tag = ctx.ontology_arenas().concept(operand).get_concept_tag();
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(label_set)
            .concept_des_dep_hash
            .insert(
                operand_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: operand_des,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );

        let succ_data = {
            let mut data = SaturationSuccessorData::new();
            data.set_successor_individual_node(succ_node)
                .set_successor_count(2)
                .set_active_count(1);
            ctx.process_context_mut().alloc_sat_succ_data(data)
        };
        let linked_data = {
            let mut data = LinkedRoleSaturationSuccessorData::new();
            data.get_successor_node_data_map_mut()
                .insert(succ_node.index() as Cint64, succ_data);
            ctx.process_context_mut()
                .alloc_linked_role_sat_succ_data(data)
        };

        let mut root_ref = root;
        let mut merging = IndividualSaturationSuccessorLinkDataLinkerId::NONE;
        let mut last_successor = SatNodeId::NONE;
        let mut last_roles = Vec::new();
        let mut min_cardinality = 0;

        let found = algo.collect_atmost_concept_relevant_successors(
            con_des,
            &mut root_ref,
            linked_data,
            &mut merging,
            &mut last_successor,
            &mut last_roles,
            &mut min_cardinality,
            &mut ctx,
        );

        assert_eq!(found, 2);
        assert_eq!(min_cardinality, 2);
        assert_eq!(last_successor, succ_node);
        let linker = ctx
            .process_context()
            .indi_sat_succ_link_data_linker(merging);
        assert_eq!(linker.get_data(), succ_data);
        assert_eq!(
            linker.get_next(),
            IndividualSaturationSuccessorLinkDataLinkerId::NONE
        );
        assert!(ctx
            .process_context()
            .sat_node(root)
            .direct_status_flags
            .has_clashed_flag());
    }

    #[test]
    fn s08_collect_atmost_operand_representative_updates_min_without_linking() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let operand = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(41);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let atmost = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCATMOST)
                .set_parameter(3)
                .set_concept_tag(43)
                .add_operand_linker(operand, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let con_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(atmost, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let succ_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(succ_node, true);
        let mut concept_sat_item = ExtendedConceptReferenceLinkingData::new();
        concept_sat_item.init_concept_saturation_testing_item(operand, false, RoleId::NONE);
        let concept_sat_item = ctx
            .process_context_mut()
            .alloc_extended_con_ref_linking_data(concept_sat_item);
        ctx.process_context_mut()
            .sat_node_mut(succ_node)
            .concept_saturation_link_ref_data = concept_sat_item;

        let succ_data = {
            let mut data = SaturationSuccessorData::new();
            data.set_successor_individual_node(succ_node)
                .set_successor_count(2)
                .set_active_count(1);
            ctx.process_context_mut().alloc_sat_succ_data(data)
        };
        let linked_data = {
            let mut data = LinkedRoleSaturationSuccessorData::new();
            data.get_successor_node_data_map_mut()
                .insert(succ_node.index() as Cint64, succ_data);
            ctx.process_context_mut()
                .alloc_linked_role_sat_succ_data(data)
        };

        let mut root_ref = root;
        let mut merging = IndividualSaturationSuccessorLinkDataLinkerId::NONE;
        let mut last_successor = SatNodeId::NONE;
        let mut last_roles = Vec::new();
        let mut min_cardinality = 0;

        let found = algo.collect_atmost_concept_relevant_successors(
            con_des,
            &mut root_ref,
            linked_data,
            &mut merging,
            &mut last_successor,
            &mut last_roles,
            &mut min_cardinality,
            &mut ctx,
        );

        assert_eq!(found, 0);
        assert_eq!(min_cardinality, 2);
        assert_eq!(merging, IndividualSaturationSuccessorLinkDataLinkerId::NONE);
        assert_eq!(last_successor, succ_node);
    }

    #[test]
    fn s08_collect_atmost_no_operand_existing_label_set_counts_successor() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let atmost = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCATMOST)
                .set_parameter(3)
                .set_concept_tag(31);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let con_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(atmost, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let succ_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(succ_node, true);
        let succ_data = {
            let mut data = SaturationSuccessorData::new();
            data.set_successor_individual_node(succ_node)
                .set_successor_count(1)
                .set_active_count(1);
            ctx.process_context_mut().alloc_sat_succ_data(data)
        };
        let linked_data = {
            let mut data = LinkedRoleSaturationSuccessorData::new();
            data.get_successor_node_data_map_mut()
                .insert(succ_node.index() as Cint64, succ_data);
            ctx.process_context_mut()
                .alloc_linked_role_sat_succ_data(data)
        };

        let mut root_ref = root;
        let mut merging = IndividualSaturationSuccessorLinkDataLinkerId::NONE;
        let mut last_successor = SatNodeId::NONE;
        let mut last_roles = Vec::new();
        let mut min_cardinality = 0;

        let found = algo.collect_atmost_concept_relevant_successors(
            con_des,
            &mut root_ref,
            linked_data,
            &mut merging,
            &mut last_successor,
            &mut last_roles,
            &mut min_cardinality,
            &mut ctx,
        );

        assert_eq!(found, 1);
        assert_eq!(min_cardinality, 1);
        assert_eq!(
            ctx.process_context()
                .indi_sat_succ_link_data_linker(merging)
                .get_data(),
            succ_data
        );
    }

    #[test]
    fn s08_collect_atmost_top_representative_updates_min_without_linking() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let top = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCTOP).set_concept_tag(51);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        ctx.processing_data_box_mut().ontology_top_concept = top;
        let atmost = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCATMOST)
                .set_parameter(3)
                .set_concept_tag(53);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let con_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(atmost, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let succ_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(succ_node, true);
        let mut concept_sat_item = ExtendedConceptReferenceLinkingData::new();
        concept_sat_item.init_concept_saturation_testing_item(top, false, RoleId::NONE);
        let concept_sat_item = ctx
            .process_context_mut()
            .alloc_extended_con_ref_linking_data(concept_sat_item);
        ctx.process_context_mut()
            .sat_node_mut(succ_node)
            .concept_saturation_link_ref_data = concept_sat_item;

        let succ_data = {
            let mut data = SaturationSuccessorData::new();
            data.set_successor_individual_node(succ_node)
                .set_successor_count(1)
                .set_active_count(1);
            ctx.process_context_mut().alloc_sat_succ_data(data)
        };
        let linked_data = {
            let mut data = LinkedRoleSaturationSuccessorData::new();
            data.get_successor_node_data_map_mut()
                .insert(succ_node.index() as Cint64, succ_data);
            ctx.process_context_mut()
                .alloc_linked_role_sat_succ_data(data)
        };

        let mut root_ref = root;
        let mut merging = IndividualSaturationSuccessorLinkDataLinkerId::NONE;
        let mut last_successor = SatNodeId::NONE;
        let mut last_roles = Vec::new();
        let mut min_cardinality = 0;

        let found = algo.collect_atmost_concept_relevant_successors(
            con_des,
            &mut root_ref,
            linked_data,
            &mut merging,
            &mut last_successor,
            &mut last_roles,
            &mut min_cardinality,
            &mut ctx,
        );

        assert_eq!(found, 0);
        assert_eq!(min_cardinality, 1);
        assert_eq!(merging, IndividualSaturationSuccessorLinkDataLinkerId::NONE);
        assert_eq!(last_successor, succ_node);
    }

    #[test]
    fn s08_successor_creation_role_subset_uses_non_negated_roles() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let role_a = RoleId::new(7);
        let role_b = RoleId::new(11);
        let subset = vec![NegLink {
            target: role_a,
            negated: false,
        }];
        let super_set = vec![
            NegLink {
                target: role_a,
                negated: false,
            },
            NegLink {
                target: role_b,
                negated: true,
            },
        ];

        assert!(algo.is_successor_creation_role_merging_subset(&subset, &super_set, &mut ctx));
        assert!(
            !algo.is_successor_creation_role_merging_subset_for_role(role_b, &super_set, &mut ctx)
        );
    }

    #[test]
    fn s08_label_merging_subset_checks_polarity_and_ignores_and_when_requested() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let atom = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(61);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let and_concept = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCAND).set_concept_tag(63);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let atom_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(atom, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };
        let and_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(and_concept, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };

        let subset = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let super_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let subset_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(subset, true);
        let super_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(super_node, true);
        let atom_tag = ctx.ontology_arenas().concept(atom).get_concept_tag();
        let and_tag = ctx.ontology_arenas().concept(and_concept).get_concept_tag();
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(subset_set)
            .concept_des_dep_hash
            .insert(
                atom_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: atom_des,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(subset_set)
            .concept_des_dep_hash
            .insert(
                and_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: and_des,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(subset_set)
            .concept_count = 2;
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(super_set)
            .concept_des_dep_hash
            .insert(
                atom_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: atom_des,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(super_set)
            .concept_count = 2;

        assert!(algo.is_individual_node_label_merging_subset(subset, super_node, true, &mut ctx));
        assert!(!algo.is_individual_node_label_merging_subset(subset, super_node, false, &mut ctx));
    }

    #[test]
    fn s08_cardinality_mergeable_uses_successor_data_and_node_guards() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let subset_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let super_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let subset_data = {
            let mut data = SaturationSuccessorData::new();
            data.set_successor_individual_node(subset_node)
                .set_successor_count(1)
                .set_active_count(1);
            ctx.process_context_mut().alloc_sat_succ_data(data)
        };
        let super_data = {
            let mut data = SaturationSuccessorData::new();
            data.set_successor_individual_node(super_node)
                .set_successor_count(1)
                .set_active_count(1);
            ctx.process_context_mut().alloc_sat_succ_data(data)
        };

        assert!(algo.is_individual_successor_link_cardinality_mergeable(
            subset_data,
            super_data,
            &mut ctx
        ));

        ctx.process_context_mut()
            .sat_node_mut(super_node)
            .set_data_value_applied(true);
        assert!(!algo.is_individual_successor_link_cardinality_mergeable(
            subset_data,
            super_data,
            &mut ctx
        ));
        ctx.process_context_mut()
            .sat_node_mut(super_node)
            .set_data_value_applied(false);
        ctx.process_context_mut()
            .sat_succ_data_mut(subset_data)
            .value_nominal_connection = true;
        assert!(!algo.is_individual_successor_link_cardinality_mergeable(
            subset_data,
            super_data,
            &mut ctx
        ));
    }

    #[test]
    fn s08_extended_cardinality_mergeable_requires_symmetric_role_sets() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let role_a = RoleId::new(17);
        let role_b = RoleId::new(19);
        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let node1 = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let node2 = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let data1 = {
            let mut data = SaturationSuccessorData::new();
            data.set_successor_individual_node(node1)
                .set_successor_count(1)
                .set_active_count(1);
            data.creation_role_linker.push(NegLink {
                target: role_a,
                negated: false,
            });
            ctx.process_context_mut().alloc_sat_succ_data(data)
        };
        let data2 = {
            let mut data = SaturationSuccessorData::new();
            data.set_successor_individual_node(node2)
                .set_successor_count(1)
                .set_active_count(1);
            data.creation_role_linker.push(NegLink {
                target: role_a,
                negated: false,
            });
            data.creation_role_linker.push(NegLink {
                target: role_b,
                negated: false,
            });
            ctx.process_context_mut().alloc_sat_succ_data(data)
        };

        let mut root_ref = root;
        assert!(
            !algo.is_individual_successor_link_cardinality_extended_mergeable(
                &mut root_ref,
                data1,
                data2,
                &mut ctx
            )
        );

        ctx.process_context_mut()
            .sat_succ_data_mut(data1)
            .creation_role_linker
            .push(NegLink {
                target: role_b,
                negated: false,
            });
        assert!(
            algo.is_individual_successor_link_cardinality_extended_mergeable(
                &mut root_ref,
                data1,
                data2,
                &mut ctx
            )
        );
    }

    #[test]
    fn s08_qualified_successor_count_checks_label_polarity_and_value_nominals() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let role = RoleId::new(23);
        let operand = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(101);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let operand_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(operand, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };
        let neg_operand_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(operand, true);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let matching_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let opposite_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let missing_label_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let value_nominal_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());

        let operand_tag = ctx.ontology_arenas().concept(operand).get_concept_tag();
        let matching_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(matching_node, true);
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(matching_set)
            .concept_des_dep_hash
            .insert(
                operand_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: operand_des,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(matching_set)
            .concept_count = 1;

        let opposite_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(opposite_node, true);
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(opposite_set)
            .concept_des_dep_hash
            .insert(
                operand_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: neg_operand_des,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(opposite_set)
            .concept_count = 1;

        let hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(root, true);
        let role_data = ctx
            .process_context_mut()
            .linked_role_successor_data(hash, role, true);
        for (node, count, value_nominal) in [
            (matching_node, 2, false),
            (opposite_node, 3, false),
            (missing_label_node, 5, false),
            (value_nominal_node, 7, true),
        ] {
            let succ_data = {
                let mut data = SaturationSuccessorData::new();
                data.set_successor_individual_node(node)
                    .set_successor_count(count)
                    .set_active_count(1);
                data.value_nominal_connection = value_nominal;
                ctx.process_context_mut().alloc_sat_succ_data(data)
            };
            ctx.process_context_mut()
                .linked_role_sat_succ_data_mut(role_data)
                .get_successor_node_data_map_mut()
                .insert(node.index() as Cint64, succ_data);
        }

        let mut root_ref = root;
        let qualification = [NegLink {
            target: operand,
            negated: false,
        }];
        assert_eq!(
            algo.get_individual_node_qualified_successor_count(
                &mut root_ref,
                role,
                Some(&qualification),
                &mut ctx,
            ),
            9
        );
    }

    #[test]
    fn s08_qualified_successor_count_preserves_null_and_nontrivial_branches() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let role = RoleId::new(29);
        let and_operand = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCAND).set_concept_tag(111);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let labelled_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let unlabelled_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(labelled_node, true);

        let hash = ctx
            .process_context_mut()
            .sat_node_ext_linked_role_successor_hash(root, true);
        let role_data = ctx
            .process_context_mut()
            .linked_role_successor_data(hash, role, true);
        for (node, count) in [(labelled_node, 4), (unlabelled_node, 6)] {
            let succ_data = {
                let mut data = SaturationSuccessorData::new();
                data.set_successor_individual_node(node)
                    .set_successor_count(count)
                    .set_active_count(1);
                ctx.process_context_mut().alloc_sat_succ_data(data)
            };
            ctx.process_context_mut()
                .linked_role_sat_succ_data_mut(role_data)
                .get_successor_node_data_map_mut()
                .insert(node.index() as Cint64, succ_data);
        }

        let mut root_ref = root;
        assert_eq!(
            algo.get_individual_node_qualified_successor_count(
                &mut root_ref,
                role,
                None,
                &mut ctx,
            ),
            4
        );

        let nontrivial_qualification = [NegLink {
            target: and_operand,
            negated: false,
        }];
        assert_eq!(
            algo.get_individual_node_qualified_successor_count(
                &mut root_ref,
                role,
                Some(&nontrivial_qualification),
                &mut ctx,
            ),
            10
        );
    }

    #[test]
    fn s08_label_merging_problematic_detects_opposite_polarity() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let concept = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(121);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let merging_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(concept, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };
        let prop_test_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(concept, true);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let merging_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let prop_test_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let merging_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(merging_node, true);
        let prop_test_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(prop_test_node, true);
        let tag = ctx.ontology_arenas().concept(concept).get_concept_tag();
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(merging_set)
            .concept_des_dep_hash
            .insert(
                tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: merging_des,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(prop_test_set)
            .concept_des_dep_hash
            .insert(
                tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: prop_test_des,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );

        let mut root_ref = root;
        assert!(algo.is_individual_node_label_merging_problematic(
            &mut root_ref,
            merging_node,
            prop_test_node,
            Vec::new(),
            &mut ctx,
        ));
    }

    #[test]
    fn s08_label_merging_problematic_accepts_same_polarity_prefix() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let concept = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(131);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let merging_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(concept, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };
        let prop_test_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(concept, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let merging_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let prop_test_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let merging_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(merging_node, true);
        let prop_test_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(prop_test_node, true);
        let tag = ctx.ontology_arenas().concept(concept).get_concept_tag();
        for (set, descriptor) in [(merging_set, merging_des), (prop_test_set, prop_test_des)] {
            ctx.process_context_mut()
                .reapply_con_sat_label_set_mut(set)
                .concept_des_dep_hash
                .insert(
                    tag,
                    ConceptSaturationDescriptorReapplyData {
                        con_sat_des: descriptor,
                        imp_reapply_con_sat_des:
                            ImplicationReapplyConceptSaturationDescriptorId::NONE,
                    },
                );
        }

        let mut root_ref = root;
        assert!(!algo.is_individual_node_label_merging_problematic(
            &mut root_ref,
            merging_node,
            prop_test_node,
            Vec::new(),
            &mut ctx,
        ));
    }

    #[test]
    fn s08_label_merging_problematic_detects_missing_implication_operand() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let trigger = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(141);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let implication_operand = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(143);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let implication = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCATOM)
                .set_concept_tag(145)
                .add_operand_linker(implication_operand, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let merging_des = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(trigger, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };
        let imp_reapply_des = {
            let mut descriptor = ImplicationReapplyConceptSaturationDescriptor::new();
            descriptor.init_implication_reaplly_concept_saturation_descriptor(implication, None);
            ctx.process_context_mut()
                .alloc_imp_reapply_con_sat_desc(descriptor)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let merging_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let prop_test_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let merging_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(merging_node, true);
        let prop_test_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(prop_test_node, true);
        let trigger_tag = ctx.ontology_arenas().concept(trigger).get_concept_tag();
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(merging_set)
            .concept_des_dep_hash
            .insert(
                trigger_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: merging_des,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(prop_test_set)
            .concept_des_dep_hash
            .insert(
                trigger_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: ConceptSaturationDescriptorId::NONE,
                    imp_reapply_con_sat_des: imp_reapply_des,
                },
            );

        let mut root_ref = root;
        assert!(algo.is_individual_node_label_merging_problematic(
            &mut root_ref,
            merging_node,
            prop_test_node,
            Vec::new(),
            &mut ctx,
        ));
    }
}
