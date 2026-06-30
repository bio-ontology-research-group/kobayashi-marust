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
//! a `CSaturationSuccessorData**` out-pointer becomes `&mut Cint64`.
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
//!   * the **mutating** `CLinkedRoleSaturationSuccessorHash` surface
//!     (`getLinkedRoleSuccessorData(role,create)` / `deactivateLinkedSuccessor`) and
//!     `CSaturationSuccessorData` THREADING — the struct is now ported, but these
//!     methods still take it as opaque `Cint64`; a reconcile should re-type those
//!     params to `SaturationSuccessorDataId` once a producer (the successor-hash read
//!     path) exists. RECONCILE-NEED: successor-data param re-typing + the
//!     `getLinkedRoleSuccessorData` read accessor (process + satellites).
//!   * the **FUNCTIONAL/ALL successor-extension data** + `getRoleBackwardPropagationHash`
//!     + `CCriticalPredecessorRoleCardinalityHash` (all still opaque `Cint64` in sat1);
//!   * the **deep** `CReapplyConceptSaturationLabelSet` bodies (`containsConcept`,
//!     `getConceptDescriptorAndReapplyQueue`) — only simple accessors are ported;
//!   * the **status-flag masks** `INDSATFLAGINSUFFICIENT` / `hasInsufficientFlag` /
//!     `hasClashedFlag`. RECONCILE-NEED: saturation status-flag masks (process/sat1.rs).
//! No live (non-deferred) site calls these group-G methods, so the signatures stay
//! as-is until that coordinated reconcile.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::substrate::{Cint64, INVALID};
use super::super::model::RoleId;
use super::super::process::SatNodeId;

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
        let mut inv_role: RoleId =
            calc_alg_context.ontology_arenas().role(role).get_inverse_role();
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
            let super_role_list = calc_alg_context
                .ontology_arenas()
                .role(role)
                .get_indirect_super_role_list()
                .to_vec();
            for inv_super_role_linker_it in &super_role_list {
                if inv_role.is_some() {
                    break;
                }
                if inv_super_role_linker_it.negated {
                    let inv_super_role = inv_super_role_linker_it.target;
                    let super_super_role_list = calc_alg_context
                        .ontology_arenas()
                        .role(inv_super_role)
                        .get_indirect_super_role_list()
                        .to_vec();
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
        creation_role_linker: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   ancSuccLinkData = nullptr;
        //   collectLinkedSuccessorNodes(ancSatNode, ctx);                       // sibling
        //   invRole = getInverseRole(role, ctx);                                // LIVE sibling
        //   ancLinkedSuccHash = ancSatNode->getLinkedRoleSuccessorHash(true);
        //   if (ancLinkedSuccHash) {
        //       ancSuccData = ancLinkedSuccHash->getLinkedRoleSuccessorData(invRole, false);
        //       if (ancSuccData)
        //           ancSuccLinkData = ancSuccData->mSuccNodeDataMap.value(indiProcSatNode->getIndividualID());
        //   }
        //   if (ancSuccLinkData && ancSuccLinkData->mActiveCount >= 1) {
        //       ancSuccCreationRoleLinker = ancSuccLinkData->mCreationRoleLinker;
        //       updated = false;
        //       funcConExtData = succSatNode->getSuccessorExtensionData(true)->getFUNCTIONALConceptsExtensionData(true);
        //       if (!funcConExtData->hasIndividualNodeForwardingPredecessorMerged(ancSatNode)) {
        //           succConSet = succSatNode->getReapplyConceptSaturationLabelSet(false);
        //           if (succConSet)
        //               for (conSatDesIt in succConSet->getConceptSaturationDescriptionLinker())
        //                   addConceptFilteredToIndividual(conSatDesIt->getConcept(), conSatDesIt->isNegated(), ancSatNode, ctx);  // sibling
        //           depCopyLinker = new CXNegLinker<...>; depCopyLinker->initNegLinker(ancSatNode, false);
        //           succSatNode->addCopyDependingIndividualNodeLinker(depCopyLinker);
        //           preprocessResolvedIndividualNode(ancSatNode, ctx);          // sibling
        //       }
        //       for (creationRoleLinkerIt in creationRoleLinker) if (!negated) {
        //           creationRole = creationRoleLinkerIt->getData();
        //           if (!funcConExtData->hasIndividualNodeForwardingPredecessorMerged(ancSatNode, creationRole)) {
        //               updated = true;
        //               funcConExtData->setIndividualNodeForwardingPredecessorMerged(ancSatNode, creationRole);
        //               invCreationRole = getInverseRole(creationRole, ctx);
        //               if (invCreationRole && !ancLinkedSuccHash->hasActiveLinkedSuccessor(invCreationRole, indiProcSatNode)) {
        //                   for (invCreationSuperRoleIt in invCreationRole->getIndirectSuperRoleList()) {
        //                       creationSuperRole = invCreationSuperRoleIt->getData();
        //                       if (!negated) {
        //                           ancLinkedSuccHash->addExtensionSuccessor(creationSuperRole, indiProcSatNode, invCreationRole, 1);
        //                           addNewLinkedExtensionProcessingRole(creationSuperRole, ancSatNode, true, true, ctx);  // sibling
        //                       } else {
        //                           backPropLink = new CBackwardSaturationPropagationLink;
        //                           backPropLink->initBackwardPropagationLink(ancSatNode, creationSuperRole);
        //                           installBackwardPropagationLink(ancSatNode, indiProcSatNode, creationSuperRole, backPropLink, true, false, ctx);  // s06 sibling
        //                       }
        //                   }
        //               }
        //           }
        //       }
        //       return updated;
        //   }
        //   return false;
        // CLinkedRoleSaturationSuccessorHash / CSaturationSuccessorData /
        // CSaturationIndividualNodeFUNCTIONALConceptsExtensionData satellites + the
        // listed siblings are not yet ported.
        let _ = (
            indi_proc_sat_node,
            role,
            succ_sat_node,
            anc_sat_node,
            creation_role_linker,
        );
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
        subset_indi_succ_data: Cint64,
        // `CSaturationSuccessorData* superIndiSuccData`
        super_indi_succ_data: Cint64,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   subsetIndiSuccNode = subsetIndiSuccData->mSuccIndiNode;
        //   superIndiSuccNode  = superIndiSuccData->mSuccIndiNode;
        //   return isLinkedIndividualSuccessorNodeMergingSubset(indiProcSatNode,
        //       subsetIndiSuccNode, subsetIndiSuccData, superIndiSuccNode, superIndiSuccData, role, ctx);  // → _for_nodes
        // CSaturationSuccessorData satellite not yet ported.
        let _ = (
            indi_proc_sat_node,
            subset_indi_succ_data,
            super_indi_succ_data,
            role,
        );
        false
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
        subset_indi_succ_data: Cint64,
        super_indi_succ_node: SatNodeId,
        super_indi_succ_data: Cint64,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   if (subsetIndiSuccData->mVALUENominalConnection || superIndiSuccData->mVALUENominalConnection) return false;
        //   if (subsetIndiSuccNode->hasNominalIntegrated()) return false;
        //   if (subsetIndiSuccNode->hasDataValueApplied()) return false;
        //   if (superIndiSuccData->mActiveCount <= 0) return false;
        //   if (subsetIndiSuccData->mSuccCount > superIndiSuccData->mSuccCount) return false;
        //   if (!isSuccessorCreationRoleMergingSubset(role, superIndiSuccData->mCreationRoleLinker, ctx)) return false;  // _for_role
        //   if (!isIndividualNodeLabelMergingSubset(subsetIndiSuccNode, superIndiSuccNode, false, ctx)) return false;
        //   return true;
        // CSaturationSuccessorData + node nominal/data-value flags not yet ported.
        let _ = (
            indi_proc_sat_node,
            subset_indi_succ_node,
            subset_indi_succ_data,
            super_indi_succ_node,
            super_indi_succ_data,
            role,
        );
        false
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isSuccessorCreationRoleMergingSubset`
    /// (the `CXNegLinker<CRole*>*`/`CXNegLinker<CRole*>*` overload). cpp 1370–1380.
    ///
    /// True when every non-negated creation-role of `superCreationRoleLinker` is
    /// itself contained (subset) in `superCreationRoleLinker` (per the `_for_role`
    /// worker). (C++ iterates `superCreationRoleLinker` and tests each via the
    /// single-role worker; `subCreationRoleLinker` is unused in the body.)
    pub fn is_successor_creation_role_merging_subset(
        &mut self,
        // `CXNegLinker<CRole*>* subCreationRoleLinker`
        sub_creation_role_linker: Cint64,
        // `CXNegLinker<CRole*>* superCreationRoleLinker`
        super_creation_role_linker: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   for (subCreationRoleLinkerIt = superCreationRoleLinker; subCreationRoleLinkerIt; ++) {
        //       if (!subCreationRoleLinkerIt->isNegated()) {
        //           subCreationRole = subCreationRoleLinkerIt->getData();
        //           if (!isSuccessorCreationRoleMergingSubset(subCreationRole, superCreationRoleLinker, ctx))  // _for_role
        //               return false;
        //       }
        //   }
        //   return true;
        // The CXNegLinker<CRole*> chains come from CSaturationSuccessorData
        // (`mCreationRoleLinker`), a not-yet-ported satellite.
        let _ = (sub_creation_role_linker, super_creation_role_linker);
        false
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isSuccessorCreationRoleMergingSubset`
    /// (the single-role worker overload). cpp 1382–1391. [overload] `_for_role` suffix.
    ///
    /// True when `subCreationRole` occurs non-negated in `superCreationRoleLinker`.
    pub fn is_successor_creation_role_merging_subset_for_role(
        &mut self,
        sub_creation_role: RoleId,
        // `CXNegLinker<CRole*>* superCreationRoleLinker`
        super_creation_role_linker: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   for (superCreationRoleLinkerIt = superCreationRoleLinker; superCreationRoleLinkerIt; ++)
        //       if (!superCreationRoleLinkerIt->isNegated() && superCreationRoleLinkerIt->getData() == subCreationRole)
        //           return true;
        //   return false;
        // The CXNegLinker<CRole*> chain comes from a not-yet-ported CSaturationSuccessorData satellite.
        let _ = (sub_creation_role, super_creation_role_linker);
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
        // W4-DEFER[api]: faithful C++ body —
        //   subsetConSet = subsetIndiSuccNode->getReapplyConceptSaturationLabelSet(false);
        //   superConSet  = superIndiSuccNode->getReapplyConceptSaturationLabelSet(false);
        //   if (!superConSet && subsetConSet) return false;
        //   if (subsetConSet && superConSet) {
        //       if (subsetConSet->getConceptCount() <= superConSet->getConceptCount()) {
        //           for (conDesIt in subsetConSet->getConceptSaturationDescriptionLinker()) {
        //               concept = conDesIt->getConcept(); negation = conDesIt->isNegated();
        //               conCode = concept->getOperatorCode();
        //               if (!ignoreANDConcepts
        //                   || (!negation && conCode != CCAND && conCode != CCAQAND && conCode != CCIMPLAQAND && conCode != CCBRANCHAQAND)
        //                   || (negation && conCode != CCOR)) {
        //                   if (!superConSet->containsConcept(concept, negation)) return false;
        //               }
        //           }
        //       } else return false;
        //   }
        //   return true;
        // CReapplyConceptSaturationLabelSet satellite not yet ported.
        let _ = (
            subset_indi_succ_node,
            super_indi_succ_node,
            ignore_and_concepts,
        );
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
        linked_succ_hash: Cint64,
        // `CPROCESSMAP<cint64,CSaturationSuccessorData*>* succDataMap`
        succ_data_map: Cint64,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let links_deactivated = false;
        // W4-DEFER[api]: faithful C++ body —
        //   removedSuccCardCount = 0;
        //   for ((indiID, succLinkData) in succDataMap) {
        //       if (succLinkData->mActiveCount > 0) {
        //           succCard = succLinkData->mSuccCount;
        //           nodeMergeable = true;
        //           if (succLinkData->mSuccIndiNode && (succLinkData->mSuccIndiNode->hasDataValueApplied() || succLinkData->mSuccIndiNode->hasNominalIntegrated())) nodeMergeable = false;
        //           if (succLinkData->mVALUENominalConnection) nodeMergeable = false;
        //           if (nodeMergeable) {
        //               for (creationRoleLinkerIt in succLinkData->mCreationRoleLinker) if (!negated) {
        //                   creationRole = creationRoleLinkerIt->getData();
        //                   deactivateLink = false;
        //                   for ((mergeIndiID, mergeSuccLinkData) in succDataMap) if (!deactivateLink && indiID != mergeIndiID && mergeSuccLinkData->mActiveCount > 0)
        //                       if (isLinkedIndividualSuccessorNodeMergingSubset(indiProcSatNode, succLinkData, mergeSuccLinkData, creationRole, ctx))
        //                           deactivateLink = true;
        //                   if (deactivateLink)
        //                       for (creationSuperRoleIt in creationRole->getIndirectSuperRoleList()) if (!negated)
        //                           linkedSuccHash->deactivateLinkedSuccessor(creationSuperRoleIt->getData(), succLinkData->mSuccIndiNode, creationRole);
        //               }
        //           }
        //           if (succLinkData->mActiveCount <= 0) removedSuccCardCount += succCard;
        //       }
        //   }
        //   return linksDeactivated;   // never assigned true in C++
        // CLinkedRoleSaturationSuccessorHash / CSaturationSuccessorData satellites not yet ported.
        let _ = (indi_proc_sat_node, linked_succ_hash, succ_data_map, role);
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
        con_des: Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut ancestors_restricted = false;
        // W4-DEFER[api]: faithful C++ body —
        //   backwardPropHash = indiProcSatNode->getRoleBackwardPropagationHash(false);
        //   concept = conDes->getConcept(); conceptNegation = conDes->isNegated();
        //   role = concept->getRole();
        //   if (backwardPropHash && !indiProcSatNode->isABoxIndividualRepresentationNode()) {
        //       backPropDataHash = backwardPropHash->getRoleBackwardPropagationDataHash();
        //       if (backPropDataHash)
        //           for (it = backPropDataHash->constFind(role); it != end && it.key() == role; ++it)
        //               for (backPropLinkIt in it.value().mLinkLinker) {
        //                   sourceIndi = backPropLinkIt->getSourceIndividual();
        //                   updateDirectAddingIndividualStatusFlags(sourceIndi, INDSATFLAGINSUFFICIENT, ctx);  // sibling
        //                   setInsufficientNodeOccured(mCalcAlgContext);                                       // sibling
        //                   ancestorsRestricted = true;
        //               }
        //   }
        //   critPredRolCardHash = indiProcSatNode->getCriticalPredecessorRoleCardinalityHash(true);
        //   critPredRolCardHash->addCriticalPredecessorRoleCardinality(role, concept, !conceptNegation);
        //   return ancestorsRestricted;
        // CRoleBackwardSaturationPropagationHash / CCriticalPredecessorRoleCardinalityHash
        // satellites + the status-flag siblings not yet ported.
        let _ = (con_des, indi_proc_sat_node);
        ancestors_restricted = false;
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
        con_des: Cint64,
        // `CIndividualSaturationProcessNode* functionallyRestrictedSuccessorNode`
        functionally_restricted_successor_node: SatNodeId,
        // `CXNegLinker<CRole*>* functionallyRestrictedSuccessorCreationRoleLinker`
        functionally_restricted_successor_creation_role_linker: Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut ancestors_restricted = false;
        // W4-DEFER[api]: faithful C++ body —
        //   backwardPropHash = indiProcSatNode->getRoleBackwardPropagationHash(false);
        //   concept = conDes->getConcept(); conceptNegation = conDes->isNegated(); role = concept->getRole();
        //   if (backwardPropHash && !indiProcSatNode->isABoxIndividualRepresentationNode()) {
        //       backPropDataHash = backwardPropHash->getRoleBackwardPropagationDataHash();
        //       if (backPropDataHash)
        //           for (it = backPropDataHash->constFind(role); it != end && it.key() == role; ++it)
        //               for (backPropLinkIt in it.value().mLinkLinker) {
        //                   sourceIndi = backPropLinkIt->getSourceIndividual();
        //                   ancestorInsufficient = true;
        //                   allowedCardinality = concept->getParameter() - 1*conceptNegation;
        //                   if (!sourceIndi->getIndirectStatusFlags()->hasInsufficientFlag()) {
        //                       if (allowedCardinality == 1 && !concept->getOperandList()) {
        //                           if (sourceIndi == functionallyRestrictedSuccessorNode) ancestorInsufficient = false;
        //                           else {
        //                               collectLinkedSuccessorNodes(sourceIndi, ctx);   // sibling
        //                               linkedSuccHash = sourceIndi->getLinkedRoleSuccessorHash(false);
        //                               if (linkedSuccHash) {
        //                                   succHash = linkedSuccHash->getLinkedRoleSuccessorHash();
        //                                   inverseRole = getInverseRole(role, ctx);     // LIVE sibling
        //                                   succData = succHash->value(inverseRole);
        //                                   if (succData) {
        //                                       succRoleData = succData->mSuccNodeDataMap.value(indiProcSatNode->getIndividualID());
        //                                       if (succRoleData) {
        //                                           if (succRoleData->mActiveCount <= 0) ancestorInsufficient = false;
        //                                           else {
        //                                               funcSuccAllRolePredMerged = false;
        //                                               succExtData = functionallyRestrictedSuccessorNode->getSuccessorExtensionData(false);
        //                                               if (succExtData) {
        //                                                   funcConExtData = succExtData->getFUNCTIONALConceptsExtensionData(false);
        //                                                   if (funcConExtData) {
        //                                                       funcSuccAllRolePredMerged = true;
        //                                                       for (it2 in functionallyRestrictedSuccessorCreationRoleLinker) if (!negated)
        //                                                           if (!funcConExtData->hasIndividualNodeForwardingPredecessorMerged(sourceIndi, it2->getData()))
        //                                                               funcSuccAllRolePredMerged = false;
        //                                                   }
        //                                               }
        //                                               if (funcSuccAllRolePredMerged || isIndividualNodeLabelMergingSubset(functionallyRestrictedSuccessorNode, sourceIndi, true, ctx))
        //                                                   if (funcSuccAllRolePredMerged || isSuccessorCreationRoleMergingSubset(functionallyRestrictedSuccessorCreationRoleLinker, succRoleData->mCreationRoleLinker, ctx))
        //                                                       ancestorInsufficient = false;
        //                                           }
        //                                       }
        //                                   }
        //                               }
        //                           }
        //                       }
        //                   }
        //                   if (ancestorInsufficient) {
        //                       updateDirectAddingIndividualStatusFlags(sourceIndi, INDSATFLAGINSUFFICIENT, ctx);
        //                       setInsufficientNodeOccured(mCalcAlgContext);
        //                       ancestorsRestricted = true;
        //                   }
        //               }
        //   }
        //   critPredRolCardHash = indiProcSatNode->getCriticalPredecessorRoleCardinalityHash(true);
        //   critPredRolCardHash->addCriticalPredecessorRoleCardinality(role, concept, !conceptNegation);
        //   return ancestorsRestricted;
        // Same backward-propagation / linked-successor / FUNCTIONAL-extension satellite
        // tower + status-flag siblings as the nominal variant, not yet ported.
        let _ = (
            con_des,
            functionally_restricted_successor_node,
            functionally_restricted_successor_creation_role_linker,
            indi_proc_sat_node,
        );
        ancestors_restricted = false;
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
        con_des: Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        // `CLinkedRoleSaturationSuccessorData* succData`
        succ_data: Cint64,
        // `CIndividualSaturationSuccessorLinkDataLinker*& mergingSuccDataLinker`
        merging_succ_data_linker: &mut Cint64,
        last_successor_node: &mut SatNodeId,
        // `CXNegLinker<CRole*>*& lastSuccessorCreationRoleLinker`
        last_successor_creation_role_linker: &mut Cint64,
        min_cardinality: &mut Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        let found_cardinality: Cint64 = 0;
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
        let _ = (
            con_des,
            indi_proc_sat_node,
            succ_data,
            merging_succ_data_linker,
            last_successor_node,
            last_successor_creation_role_linker,
            min_cardinality,
        );
        found_cardinality
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
        let node_saturation = false;
        // W4-DEFER[api]: faithful C++ body —
        //   processingDataBox = calcAlgContext->getUsedProcessingDataBox();
        //   while (!nodeSaturation && processingDataBox->hasSaturationATMOSTMergingProcessLinker()) {
        //       mergingProcessLinker = processingDataBox->getSaturationATMOSTMergingProcessLinker();
        //       indiProcSatNode = mergingProcessLinker->getData();
        //       indirectFlags = indiProcSatNode->getIndirectStatusFlags();
        //       if (!indirectFlags->hasInsufficientFlag() && !indirectFlags->hasClashedFlag()) {
        //           atmostSuccMergingData = indiProcSatNode->getATMOSTSuccessorMergingData(false);
        //           if (atmostSuccMergingData) {
        //               conProcLinker = atmostSuccMergingData->getMergingConceptLinker();
        //               while (!nodeSaturation && conProcLinker) {
        //                   conDes = conProcLinker->getConceptSaturationDescriptor();
        //                   mergingSuccData = atmostSuccMergingData->getATMOSTConceptMergingData(conDes);
        //                   nodeInsufficient = false; ancestorPossiblyInsufficient = false;
        //                   functionallyRestrictedSuccessorNode = nullptr; functionallyRestrictedSuccessorCreationRoleLinker = nullptr;
        //                   nodeSaturation = tryIndividiualATMOSTConceptSuccessorMerging(conDes, &mergingSuccData, nodeInsufficient, ancestorPossiblyInsufficient,
        //                       functionallyRestrictedSuccessorNode, functionallyRestrictedSuccessorCreationRoleLinker, indiProcSatNode, ctx);
        //                   if (!nodeSaturation) {
        //                       if (nodeInsufficient) { ++mInsufficientATMOSTCount; updateDirectAddingIndividualStatusFlags(indiProcSatNode, INDSATFLAGINSUFFICIENT, ctx); setInsufficientNodeOccured(ctx); }
        //                       else addCriticalConceptForDependentNodes(conDes, CCT_ATMOST, indiProcSatNode, false, INDSATFLAGINSUFFICIENT, ctx);   // sibling
        //                       if (indiProcSatNode->hasNominalIntegrated()) markNominalATMOSTRestrictedAncestorsAsInsufficient(conDes, indiProcSatNode, ctx);
        //                       if (ancestorPossiblyInsufficient) { markATMOSTRestrictedAncestorsAsInsufficient(conDes, functionallyRestrictedSuccessorNode, functionallyRestrictedSuccessorCreationRoleLinker, indiProcSatNode, ctx);
        //                           updateDirectAddingIndividualStatusFlags(indiProcSatNode, INDSATFLAGCARDINALITYPROPLEMATIC, ctx); }
        //                   }
        //                   if (!nodeSaturation) conProcLinker = atmostSuccMergingData->takeNextMergingConceptLinker();
        //               }
        //           }
        //       }
        //       if (!nodeSaturation) { mergingProcessLinker = processingDataBox->takeSaturationATMOSTMergingProcessLinker(); mergingProcessLinker->setProcessingQueued(false); }
        //   }
        //   return nodeSaturation;
        // The databox ATMOST-merging queue + CSaturationATMOSTSuccessorMergingData
        // satellite + the addCriticalConceptForDependentNodes / status-flag siblings
        // not yet ported.
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
        con_des: Cint64,
        // `CSaturationATMOSTSuccessorMergingHashData* mergingSuccData`
        merging_succ_data: Cint64,
        node_insufficient: &mut bool,
        ancestor_possibly_critical_flag: &mut bool,
        functionally_restricted_successor_node: &mut SatNodeId,
        // `CXNegLinker<CRole*>*& functionallyRestrictedSuccessorCreationRoleLinker`
        functionally_restricted_successor_creation_role_linker: &mut Cint64,
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
        subset_indi_succ_data: Cint64,
        // `CSaturationSuccessorData* superIndiSuccData`
        super_indi_succ_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   subsetIndiSuccNode = subsetIndiSuccData->mSuccIndiNode;
        //   superIndiSuccNode  = superIndiSuccData->mSuccIndiNode;
        //   return isIndividualSuccessorLinkCardinalityMergeable(subsetIndiSuccNode, subsetIndiSuccData, superIndiSuccNode, superIndiSuccData, ctx);  // → _for_nodes
        // CSaturationSuccessorData satellite not yet ported.
        let _ = (subset_indi_succ_data, super_indi_succ_data);
        false
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isIndividualSuccessorLinkCardinalityMergeable`
    /// (the explicit-node worker overload). cpp 4473–4493. [overload] `_for_nodes` suffix.
    ///
    /// True when two role successors can be cardinality-merged: neither a
    /// VALUE-nominal connection, neither node nominal-integrated, an ABox-individual
    /// representation, nor data-value-applied; their creation-role sets are merging
    /// subsets of each other (via the subset-only direction in C++); and the subset
    /// label is a merging subset (AND-concepts ignored).
    pub fn is_individual_successor_link_cardinality_mergeable_for_nodes(
        &mut self,
        // `CIndividualSaturationProcessNode* subsetIndiSuccNode`
        subset_indi_succ_node: SatNodeId,
        subset_indi_succ_data: Cint64,
        super_indi_succ_node: SatNodeId,
        super_indi_succ_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   if (subsetIndiSuccData->mVALUENominalConnection || superIndiSuccData->mVALUENominalConnection) return false;
        //   if (subsetIndiSuccNode->hasNominalIntegrated() || superIndiSuccNode->hasNominalIntegrated()) return false;
        //   if (subsetIndiSuccNode->isABoxIndividualRepresentationNode() || superIndiSuccNode->isABoxIndividualRepresentationNode()) return false;
        //   if (subsetIndiSuccNode->hasDataValueApplied() || superIndiSuccNode->hasDataValueApplied()) return false;
        //   if (!isSuccessorCreationRoleMergingSubset(subsetIndiSuccData->mCreationRoleLinker, superIndiSuccData->mCreationRoleLinker, ctx)) return false;
        //   if (!isIndividualNodeLabelMergingSubset(subsetIndiSuccNode, superIndiSuccNode, true, ctx)) return false;
        //   return true;
        // CSaturationSuccessorData + node flags satellites not yet ported.
        let _ = (
            subset_indi_succ_node,
            subset_indi_succ_data,
            super_indi_succ_node,
            super_indi_succ_data,
        );
        false
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::isIndividualSuccessorLinkCardinalityExtendedMergeable`
    /// (the `CSaturationSuccessorData*`/`CSaturationSuccessorData*` dispatcher overload). cpp 4599–4603.
    ///
    /// Unwraps both successor data's `mSuccIndiNode` and delegates to `_for_nodes`.
    pub fn is_individual_successor_link_cardinality_extended_mergeable(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        // `CSaturationSuccessorData* indiSuccData1`
        indi_succ_data1: Cint64,
        // `CSaturationSuccessorData* indiSuccData2`
        indi_succ_data2: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   indiSuccNode1 = indiSuccData1->mSuccIndiNode; indiSuccNode2 = indiSuccData2->mSuccIndiNode;
        //   return isIndividualSuccessorLinkCardinalityExtendedMergeable(indiProcSatNode, indiSuccNode1, indiSuccData1, indiSuccNode2, indiSuccData2, ctx);  // → _for_nodes
        // CSaturationSuccessorData satellite not yet ported.
        let _ = (indi_proc_sat_node, indi_succ_data1, indi_succ_data2);
        false
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
        indi_succ_data1: Cint64,
        indi_succ_node2: SatNodeId,
        indi_succ_data2: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   if (indiSuccData1->mVALUENominalConnection || indiSuccData2->mVALUENominalConnection) return false;
        //   if (indiSuccNode1->hasNominalIntegrated() || indiSuccNode2->hasNominalIntegrated()) return false;
        //   if (indiSuccNode1->hasDataValueApplied() || indiSuccNode2->hasDataValueApplied()) return false;
        //   if (indiSuccNode1->isABoxIndividualRepresentationNode() || indiSuccNode2->isABoxIndividualRepresentationNode()) return false;
        //   if (!isSuccessorCreationRoleMergingSubset(indiSuccData1->mCreationRoleLinker, indiSuccData2->mCreationRoleLinker, ctx)) return false;
        //   if (!isSuccessorCreationRoleMergingSubset(indiSuccData2->mCreationRoleLinker, indiSuccData1->mCreationRoleLinker, ctx)) return false;
        //   if (isIndividualNodeLabelMergingProblematic(indiProcSatNode, indiSuccNode1, indiSuccNode2, indiSuccData1->mCreationRoleLinker, ctx)) return false;
        //   if (isIndividualNodeLabelMergingProblematic(indiProcSatNode, indiSuccNode2, indiSuccNode1, indiSuccData2->mCreationRoleLinker, ctx)) return false;
        //   return true;
        // CSaturationSuccessorData + node flags satellites not yet ported.
        let _ = (
            indi_proc_sat_node,
            indi_succ_node1,
            indi_succ_data1,
            indi_succ_node2,
            indi_succ_data2,
        );
        false
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
        succ_link_data: Cint64,
        // `CIndividualSaturationSuccessorLinkDataLinker* mergingSuccDataLinker`
        merging_succ_data_linker: Cint64,
        // `CPROCESSHASH<CSaturationSuccessorData*,cint64>* remainMergeableCardHash`
        remain_mergeable_card_hash: Cint64,
        role: RoleId,
        max_required_merging_cardinality: Cint64,
        // `CPROCESSHASH<CSaturationSuccessorData*,CSaturationSuccessorData*>* mergeDistintHash`
        merge_distint_hash: Cint64,
        // `CPROCESSSET< QPair<...> >* mergeDistintSet`
        merge_distint_set: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        let merged_cardinality: Cint64 = 0;
        // W4-DEFER[api]: faithful C++ body —
        //   remainingCardinality = succLinkData->mSuccCount; intoAllMergeable = false; intoAllMergeableChecked = false;
        //   // fast path: some other successor with capacity >= succLinkData->mSuccCount that is mergeable+distinct-clear:
        //   for (it in mergingSuccDataLinker) if (mergeSuccLinkData != succLinkData) {
        //       mergeableCardinality = remainMergeableCardHash->value(mergeSuccLinkData, mergeSuccLinkData->mSuccCount);
        //       if (mergeableCardinality >= succLinkData->mSuccCount) {
        //           if (!mergeDistintSet->contains(QPair(qMin,qMax))) { if (isIndividualSuccessorLinkCardinalityMergeable(succLinkData, mergeSuccLinkData, ctx)) return remainingCardinality; else intoAllMergeableChecked = true; }
        //           else intoAllMergeableChecked = true;
        //       }
        //   }
        //   mergedCardinality = 0;
        //   for (it in mergingSuccDataLinker; remainingCardinality > 0 && mergedCardinality < maxRequiredMergingCardinality; ) if (mergeSuccLinkData != succLinkData) {
        //       mergeableCardinality = remainMergeableCardHash->value(mergeSuccLinkData, mergeSuccLinkData->mSuccCount);
        //       if (mergeableCardinality > 0 && mergeableCardinality < succLinkData->mSuccCount) {
        //           if (!mergeDistintSet->contains(QPair(qMin,qMax))) {
        //               if (intoAllMergeable || isIndividualSuccessorLinkCardinalityMergeable(succLinkData, mergeSuccLinkData, ctx)) {
        //                   if (!intoAllMergeableChecked) {
        //                       intoAllMergeable = true;
        //                       for (remTestIt = it->getNext(); remTestIt; remTestIt = remTestIt->getNext()) if (remTestSuccLinkData != succLinkData && remTestSuccLinkData != mergeSuccLinkData) {
        //                           c = remainMergeableCardHash->value(remTestSuccLinkData, remTestSuccLinkData->mSuccCount);
        //                           if (c > 0 && c < succLinkData->mSuccCount && !mergeDistintSet->contains(QPair(qMin(remTest,succ),qMax(...))))
        //                               if (!isIndividualSuccessorLinkCardinalityMergeable(succLinkData, mergeSuccLinkData, ctx)) intoAllMergeable = false;
        //                       }
        //                       intoAllMergeableChecked = true;
        //                   }
        //                   if (!intoAllMergeable && succLinkData->mSuccCount > 1) {
        //                       mergeDistintSet->insert(QPair(qMin(mergeSucc,succ),qMax(...)));
        //                       for (mDIt = mergeDistintHash->constFind(succLinkData); mDIt.key() == succLinkData; ++mDIt) { distSuccData = mDIt.value(); mergeDistintHash->insertMulti(distSuccData,mergeSuccLinkData); mergeDistintHash->insertMulti(mergeSuccLinkData,distSuccData); mergeDistintSet->insert(QPair(qMin(mergeSucc,dist),qMax(...))); }
        //                       mergeDistintHash->insertMulti(succLinkData,mergeSuccLinkData); mergeDistintHash->insertMulti(mergeSuccLinkData,succLinkData);
        //                   }
        //                   mergingCardinality = qMin(remainingCardinality, mergeableCardinality); remainingCardinality -= mergingCardinality; mergedCardinality += mergingCardinality;
        //               } else intoAllMergeableChecked = true;
        //           } else intoAllMergeableChecked = true;
        //       }
        //   }
        //   return mergedCardinality;
        // CSaturationSuccessorData / merge distinct hash+set / remaining-mergeable hash
        // satellites + the cardinality-mergeable sibling (this unit) not yet ported.
        let _ = (
            indi_proc_sat_node,
            succ_link_data,
            merging_succ_data_linker,
            remain_mergeable_card_hash,
            role,
            max_required_merging_cardinality,
            merge_distint_hash,
            merge_distint_set,
        );
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
        con_qualification_linker: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        let matching_succ_count: Cint64 = 0;
        // W4-DEFER[api]: faithful C++ body —
        //   linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //   if (linkedSuccHash) {
        //       succHash = linkedSuccHash->getLinkedRoleSuccessorHash(); predSuccData = succHash->value(role);
        //       if (predSuccData) {
        //           trivialQualification = true;
        //           for (opLinkerIt in conQualificationLinker) if (opNeg || (opCode != CCATOM && opCode != CCSUB)) trivialQualification = false;
        //           for ((id, succRoleData) in predSuccData->mSuccNodeDataMap) if (succRoleData->mActiveCount >= 1) {
        //               succCardinality = succRoleData->mSuccCount;
        //               operantsContainedNegative = operantsContainedPositive = operantsContained = true;
        //               if (succRoleData->mVALUENominalConnection) operantsContainedPositive = true;
        //               else {
        //                   succNode = succRoleData->mSuccIndiNode; lastSuccessorNode = succNode; lastSuccessorCreationRoleLinker = succRoleData->mCreationRoleLinker;
        //                   succConSet = succNode->getReapplyConceptSaturationLabelSet(false);
        //                   if (succConSet) {
        //                       if (conQualificationLinker)
        //                           for (opLinkerIt in conQualificationLinker) { opConcept = opLinkerIt->getData(); opConceptNegation = opLinkerIt->isNegated(); containedNegation = false;
        //                               if (succConSet->containsConcept(opConcept, &containedNegation)) { if (containedNegation == opConceptNegation) operantsContainedNegative = false; else operantsContainedPositive = false; }
        //                               else if (trivialQualification) operantsContainedPositive = false; else operantsContained = false; }
        //                       else operantsContainedNegative = false;
        //                   } else if (trivialQualification) operantsContainedPositive = false; else operantsContained = false;
        //               }
        //               if (operantsContainedPositive || !operantsContained) matchingSuccCount += succCardinality;
        //           }
        //       }
        //   }
        //   return matchingSuccCount;
        // CLinkedRoleSaturationSuccessorHash / CSaturationSuccessorData / label-set
        // satellites not yet ported.
        let _ = (indi_proc_sat_node, role, con_qualification_linker);
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
        creation_role_linker: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W4-DEFER[api]: faithful C++ body —
        //   mergingConSet = mergingSuccNode->getReapplyConceptSaturationLabelSet(false);
        //   propTestConSet = probTestingSuccNode->getReapplyConceptSaturationLabelSet(false);
        //   for (conDesIt in mergingConSet->getConceptSaturationDescriptionLinker()) {
        //       concept = conDesIt->getConcept(); negation = conDesIt->isNegated(); propTestConDes = nullptr; propTestImpReapDes = nullptr;
        //       if (propTestConSet->getConceptDescriptorAndReapplyQueue(concept, propTestConDes, propTestImpReapDes)) {
        //           if (propTestConDes) { if (propTestConDes->isNegated() != negation) return true; }
        //           else if (!negation && propTestImpReapDes) { propTestImpCon = propTestImpReapDes->getImplicationConcept();
        //               if (!propTestConSet->containsConcept(propTestImpCon->getOperandList()->getData()) && !mergingConSet->containsConcept(propTestImpCon->getOperandList()->getData())) return true; }
        //       } else {
        //           // concept not present in prob-testing label -> test whether critical:
        //           for (predConDesIt in indiProcSatNode->getReapplyConceptSaturationLabelSet(false)->getConceptSaturationDescriptionLinker()) {
        //               predConcept = predConDesIt->getConcept(); predConNegation = predConDesIt->isNegated(); predConOpCode = predConcept->getOperatorCode();
        //               if (predConNegation && predConOpCode == CCATLEAST || !predConNegation && predConOpCode == CCATMOST) {
        //                   predOpCon = nullptr; if (predConcept->getOperandList()) predOpCon = predConcept = predConcept->getOperandList()->getData();
        //                   if (!predOpCon || predOpCon == concept)
        //                       for (creationRoleLinkerIt in creationRoleLinker) if (!negated)
        //                           for (creationSuperRoleIt in creationRole->getIndirectSuperRoleList()) if (!negated)
        //                               if (creationSuperRole == predConcept->getRole()) { allowedCardinality = predConcept->getParameter() - 1*predConNegation;
        //                                   if (getIndividualNodeQualifiedSuccessorCount(indiProcSatNode, creationSuperRole, predConcept->getOperandList(), ctx) > allowedCardinality) return true; }
        //               }
        //           }
        //           opCode = concept->getOperatorCode(); conOp = concept->getConceptOperator();
        //           if (!negation && conOp->hasPartialOperatorCodeFlag(CCFS_AQALL_TYPE) || negation && conOp->hasPartialOperatorCodeFlag(CCFS_SOME_TYPE) || !negation && opCode == CCATMOST || negation && opCode == CCATLEAST) {
        //               collectLinkedSuccessorNodes(probTestingSuccNode, ctx);   // sibling
        //               propTestLinkedSuccHash = probTestingSuccNode->getLinkedRoleSuccessorHash(false);
        //               if (propTestLinkedSuccHash && propTestLinkedSuccHash->hasLinkedRoleSuccessorData(concept->getRole())) return true;
        //           }
        //           if (!negation && conOp->hasPartialOperatorCodeFlag(CCFS_SOME_TYPE | CCF_SELF | CCF_ATLEAST) || negation && conOp->hasPartialOperatorCodeFlag(CCFS_AQALL_TYPE | CCF_ATMOST)) {
        //               propTestBackwardPropHash = probTestingSuccNode->getRoleBackwardPropagationHash(false);
        //               if (propTestBackwardPropHash) { backwardPropDataHash = propTestBackwardPropHash->getRoleBackwardPropagationDataHash();
        //                   for (superRoleIt in concept->getRole()->getIndirectSuperRoleList()) if (!negated) {
        //                       backwardPropData = backwardPropDataHash->valuePointer(superRole);
        //                       if (backwardPropData && backwardPropData->mReapplyLinker) return true; } }
        //           }
        //       }
        //   }
        //   return false;
        // CReapplyConceptSaturationLabelSet / CLinkedRoleSaturationSuccessorHash /
        // CRoleBackwardSaturationPropagationHash satellites + the
        // getIndividualNodeQualifiedSuccessorCount (this unit) / collectLinkedSuccessorNodes
        // siblings not yet ported.
        let _ = (
            indi_proc_sat_node,
            merging_succ_node,
            prob_testing_succ_node,
            creation_role_linker,
        );
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
        succ_link_data: Cint64,
        // `CSaturationSuccessorData** mergedSuccLinkData` (out)
        merged_succ_link_data: &mut Cint64,
        // `CIndividualSaturationSuccessorLinkDataLinker* mergingSuccDataLinker`
        merging_succ_data_linker: Cint64,
        // `CPROCESSHASH<CSaturationSuccessorData*,cint64>* remainMergeableCardHash`
        remain_mergeable_card_hash: Cint64,
        role: RoleId,
        max_required_merging_cardinality: Cint64,
        // `CPROCESSHASH<CSaturationSuccessorData*,CSaturationSuccessorData*>* mergeDistintHash`
        merge_distint_hash: Cint64,
        // `CPROCESSSET< QPair<...> >* mergeDistintSet`
        merge_distint_set: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // W4-DEFER[api]: faithful C++ body —
        //   for (it in mergingSuccDataLinker) {
        //       mergeSuccLinkData = it->getData();
        //       mergeableCardinality = remainMergeableCardHash->value(mergeSuccLinkData, mergeSuccLinkData->mSuccCount);
        //       if (mergeableCardinality > 0 && !mergeDistintSet->contains(QPair(qMin(mergeSucc,succ),qMax(...)))) {
        //           if (isIndividualSuccessorLinkCardinalityExtendedMergeable(indiProcSatNode, succLinkData, mergeSuccLinkData, ctx)) {
        //               remainMergeableCardHash->insert(mergeSuccLinkData, 0);
        //               for (mDIt = mergeDistintHash->constFind(succLinkData); mDIt.key() == succLinkData; ++mDIt) { distSuccData = mDIt.value(); mergeDistintHash->insertMulti(distSuccData,mergeSuccLinkData); mergeDistintHash->insertMulti(mergeSuccLinkData,distSuccData); mergeDistintSet->insert(QPair(qMin(mergeSucc,dist),qMax(...))); }
        //               if (mergedSuccLinkData) *mergedSuccLinkData = mergeSuccLinkData;
        //               return mergeableCardinality;
        //           }
        //       }
        //   }
        //   return 0;
        // CSaturationSuccessorData / merge distinct hash+set / remaining-mergeable hash
        // satellites + the extended-mergeable sibling (this unit) not yet ported.
        let _ = (
            indi_proc_sat_node,
            succ_link_data,
            merged_succ_link_data,
            merging_succ_data_linker,
            remain_mergeable_card_hash,
            role,
            max_required_merging_cardinality,
            merge_distint_hash,
            merge_distint_set,
        );
        0
    }
}
