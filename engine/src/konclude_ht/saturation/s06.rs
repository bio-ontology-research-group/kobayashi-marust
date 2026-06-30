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
//! No method here is substrate-portable today (unlike u17's three exceptions):
//! all 13 immediately deref the not-yet-ported satellite tower.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, INVALID};
use super::super::model::RoleId;
use super::super::process::SatNodeId;
use super::super::completion::context::CalculationAlgorithmContextBase;

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
        // `CLinkedRoleSaturationSuccessorData* succData` — unported satellite.
        succ_data: Cint64,
        create: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // W6-DEFER[api]: faithful C++ body —
        //   CSaturationSuccessorExtensionData*& succExtData = succData->mExtensionData;
        //   if (!succExtData && create) {
        //       succExtData = CObjectParameterizingAllocator<CSaturationSuccessorExtensionData,
        //           CProcessContext*>::allocateAndConstructAndParameterize(
        //               calcAlgContext->getUsedProcessTaskMemoryAllocationManager(),
        //               calcAlgContext->getProcessContext());
        //       succExtData->initSuccessorExtensionData();
        //   }
        //   return succExtData;
        // CLinkedRoleSaturationSuccessorData / CSaturationSuccessorExtensionData are
        // not yet ported (no Rust struct + no per-test arena for them), so the
        // lazy alloc + the `mExtensionData` slot cannot be resolved.
        let _ = (succ_data, create);
        INVALID
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
        // W6-DEFER[api]: faithful C++ body —
        //   indiProcSatNodeSuccExt = indiProcSatNode->getSuccessorExtensionData();
        //   indiProcSatNodeALLConSuccExt = indiProcSatNodeSuccExt->getALLConceptsExtensionData(true);
        //   linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //   if (linkedSuccHash) {
        //       succHash = linkedSuccHash->getLinkedRoleSuccessorHash();
        //       backwardPropHash = indiProcSatNode->getRoleBackwardPropagationHash(false);
        //       if (backwardPropHash) {
        //           backwardPropDataHash = backwardPropHash->getRoleBackwardPropagationDataHash();
        //           for (role, succData) in succHash {
        //               backwardPropData = backwardPropDataHash->valuePointer(role);
        //               if (backwardPropData && backwardPropData->mReapplyLinker) {
        //                   backwardPropData->mRoleALLConceptsProcessingQueued = false;
        //                   updateSuccessorRoleALLConceptsExtensions(
        //                       indiProcSatNode, role, succData, *backwardPropData, ctx);   // → _for_succ_data
        //               }
        //           }
        //       }
        //   }
        // The successor-extension-data + linked-role-successor-hash + role-backward-
        // propagation-hash satellites are not yet ported.
        let _ = indi_proc_sat_node;
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
        // `CLinkedRoleSaturationSuccessorData* succData`
        succ_data: Cint64,
        // `const CRoleBackwardSaturationPropagationHashData& backwardPropData`
        backward_prop_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W6-DEFER[api]: faithful C++ body —
        //   indiProcSatNodeALLConSuccExt = indiProcSatNode->getSuccessorExtensionData()
        //                                     ->getALLConceptsExtensionData(true);
        //   if (succData && backwardPropData.mReapplyLinker) {
        //       satSuccExtData = getSucessorExtensionData(succData, true, ctx);
        //       lastExaminedLinkLinker      = satSuccExtData->getLastExaminedLinkLinker();
        //       lastExaminedALLConReaDes    = satSuccExtData->getLastExaminedALLConceptReapplyDescriptor();
        //       // decide iteration scope from watermark deltas:
        //       continueIterateLinks   = (lastExaminedALLConReaDes != backwardPropData.mReapplyLinker)
        //                              || (lastExaminedLinkLinker  != succData->mLastLink);
        //       allConUpdated          = (lastExaminedALLConReaDes != backwardPropData.mReapplyLinker);
        //       iterateFullAllConReaDes= (lastExaminedLinkLinker  != succData->mLastLink);
        //       for (linkLinkerIt = succData->mLastLink; linkLinkerIt && continueIterateLinks; ) {
        //           if (!linkLinkerIt->mVALUENominalConnection) {
        //               succIndiNode = linkLinkerIt->mSuccIndiNode;
        //               for (creationRoleLinkerIt in linkLinkerIt->mCreationRoleLinker) {
        //                   creationRole = creationRoleLinkerIt->getData();
        //                   allConSuccExtData = indiProcSatNodeALLConSuccExt
        //                       ->getALLConceptsExtensionData(succIndiNode)
        //                       ->getRoleSuccessorALLConceptExtensionData(creationRole);
        //                   modified  = allConSuccExtData->addRequiredSuccessorCardinality(linkLinkerIt->mSuccCount);
        //                   for (backReapplyIt = backwardPropData.mReapplyLinker;
        //                        backReapplyIt && continueIterateALLReapConDes; ) {
        //                       reapplyConDes = backReapplyIt->getReapplyConceptSaturationDescriptor();
        //                       modified |= addSuccessorExtensionsALLConcept(
        //                           indiProcSatNode, reapplyConDes->getConcept(),
        //                           reapplyConDes->getNegation(), allConSuccExtData, ctx);   // PU-SAT-7 sibling
        //                       backReapplyIt = backReapplyIt->getNext();
        //                       if (backReapplyIt == lastExaminedALLConReaDes && !iterateFullAllConReaDes)
        //                           continueIterateALLReapConDes = false;
        //                   }
        //                   if (modified && !allConSuccExtData->isExtensionProcessingQueued()) {
        //                       allConSuccExtData->setExtensionProcessingQueued(true);
        //                       indiProcSatNodeALLConSuccExt->addExtensionProcessData(allConSuccExtData);
        //                   }
        //               }
        //           }
        //           linkLinkerIt = linkLinkerIt->mNextLink;
        //           if (linkLinkerIt == lastExaminedLinkLinker) {
        //               if (!allConUpdated) continueIterateLinks = false;
        //               else iterateFullAllConReaDes = false;
        //           }
        //       }
        //       satSuccExtData->setLastExaminedLinkLinker(succData->mLastLink);
        //       satSuccExtData->setLastExaminedALLConceptReapplyDescriptor(backwardPropData.mReapplyLinker);
        //   }
        // `addSuccessorExtensionsALLConcept` is a PU-SAT-7 sibling; the ALL-concept
        // extension-data + linked-successor + backward-propagation satellites are
        // not yet ported.
        let _ = (indi_proc_sat_node, role, succ_data, backward_prop_data);
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
        // W6-DEFER[api]: faithful C++ body —
        //   linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //   if (linkedSuccHash) {
        //       succData = linkedSuccHash->getLinkedRoleSuccessorHash()->value(role, nullptr);
        //       if (succData) {
        //           succData->mRoleALLConceptsProcessingQueued = false;
        //           backwardPropHash = indiProcSatNode->getRoleBackwardPropagationHash(false);
        //           if (backwardPropHash) {
        //               backwardPropData = backwardPropHash->getRoleBackwardPropagationDataHash()->valuePointer(role);
        //               if (backwardPropData && backwardPropData->mReapplyLinker) {
        //                   backwardPropData->mRoleALLConceptsProcessingQueued = false;
        //                   updateSuccessorRoleALLConceptsExtensions(
        //                       indiProcSatNode, role, succData, *backwardPropData, ctx);   // → _for_succ_data
        //               }
        //           }
        //       }
        //   }
        // Linked-role-successor-hash + role-backward-propagation-hash satellites not
        // yet ported.
        let _ = (indi_proc_sat_node, role);
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
        // W6-DEFER[api]: faithful C++ body —
        //   linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //   if (linkedSuccHash) {
        //       indiProcSatNodeSuccExt = indiProcSatNode->getSuccessorExtensionData(false);
        //       if (indiProcSatNodeSuccExt) {
        //           indiProcSatNodeALLConSuccExt = indiProcSatNodeSuccExt->getALLConceptsExtensionData(false);
        //           if (indiProcSatNodeALLConSuccExt) {
        //               while (indiProcSatNodeALLConSuccExt->hasExtensionProcessData()) {
        //                   satSucALLConExtData = indiProcSatNodeALLConSuccExt->takeNextExtensionProcessData();
        //                   satSucALLConExtData->setExtensionProcessingQueued(false);
        //                   satSucConExtMap     = satSucALLConExtData->getSuccessorConceptExtensionMap();
        //                   indiNode            = satSucALLConExtData->getIndividualNode();
        //                   role                = satSucALLConExtData->getRole();
        //                   lastResolvedIndiNode= satSucALLConExtData->getLastResolvedIndividualNode() ?? indiNode;
        //                   lastSuccCard        = satSucALLConExtData->getLastConnectedSuccessorCardinality();
        //                   requiredSuccCard    = satSucALLConExtData->getRequiredSuccessorCardinality();
        //                   onlySuccessorCardinalityUpdated = true;
        //                   resolvedIndiNode = lastResolvedIndiNode;
        //                   if (satSucALLConExtData->hasConceptsUpdatedFlag()) {
        //                       resolvedIndiNode = getResolvedIndividualNodeExtensionSuccessor(    // PU-SAT-10 sibling
        //                           indiNode, satSucConExtMap, ctx);
        //                       if (lastResolvedIndiNode != resolvedIndiNode)
        //                           onlySuccessorCardinalityUpdated = false;
        //                   }
        //                   if (lastResolvedIndiNode != resolvedIndiNode || lastSuccCard != requiredSuccCard) {
        //                       updated = true;
        //                       backwardLinkConnected = false;
        //                       if (lastResolvedIndiNode)
        //                           for (superRoleIt in role->getIndirectSuperRoleList()) if (!negated)
        //                               linkedSuccHash->deactivateLinkedSuccessor(superRole, lastResolvedIndiNode, role);
        //                       for (superRoleIt in role->getIndirectSuperRoleList()) {
        //                           if (!negated) {
        //                               linkedSuccHash->addExtensionSuccessor(superRole, resolvedIndiNode, role, requiredSuccCard);
        //                               addNewLinkedExtensionProcessingRole(superRole, indiProcSatNode, false, true, ctx); // PU-SAT-7
        //                           } else if (!onlySuccessorCardinalityUpdated) {
        //                               backwardLinkConnected = true;
        //                               backPropLink = new CBackwardSaturationPropagationLink;
        //                               backPropLink->initBackwardPropagationLink(indiProcSatNode, superRole);
        //                               installBackwardPropagationLink(indiProcSatNode, resolvedIndiNode, superRole,
        //                                   backPropLink, true, true, ctx);
        //                           }
        //                       }
        //                       updateIndirectAddingIndividualStatusFlags(indiProcSatNode, resolvedIndiNode->getIndirectStatusFlags(), mCalcAlgContext);
        //                       updateAddingSuccessorConnectedNominal(indiProcSatNode, resolvedIndiNode->getSuccessorConnectedNominalSet(false), mCalcAlgContext);
        //                       updateMaxCardinalityCandidates(indiProcSatNode, resolvedIndiNode->getMaxAtleastCardinalityCandidate(),
        //                           resolvedIndiNode->getMaxAtmostCardinalityCandidate(), mCalcAlgContext);
        //                       if (!onlySuccessorCardinalityUpdated && !backwardLinkConnected) {
        //                           nonInvConnectedIndiNodeLinker = new CXLinker<...>; nonInvConnectedIndiNodeLinker->initLinker(indiProcSatNode);
        //                           resolvedIndiNode->addNonInverseConnectedIndividualNodeLinker(nonInvConnectedIndiNodeLinker);
        //                       }
        //                       satSucALLConExtData->setLastResolvedIndividualNode(resolvedIndiNode);
        //                       satSucALLConExtData->setLastConnectedSuccessorCardinality(requiredSuccCard);
        //                   }
        //               }
        //           }
        //       }
        //   }
        // `getResolvedIndividualNodeExtensionSuccessor` (PU-SAT-10),
        // `addNewLinkedExtensionProcessingRole` (PU-SAT-7), the status/nominal/
        // cardinality propagators (PU-SAT-11) and the ALL-concept extension-data +
        // linked-successor + backward-propagation satellites are not yet ported.
        let _ = indi_proc_sat_node;
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
        // W6-DEFER[api]: faithful C++ body —
        //   linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //   if (linkedSuccHash) {
        //       succData = linkedSuccHash->getLinkedRoleSuccessorData(role, true);
        //       if (succData && !succData->mRoleFUNCTIONALConceptsQueuingRequired) {
        //           succData->mRoleFUNCTIONALConceptsQueuingRequired = true;
        //           installed = true;
        //       }
        //   }
        //   backwardPropHash = indiProcSatNode->getRoleBackwardPropagationHash(true);
        //   if (backwardPropHash) {
        //       backwardPropDataHash = backwardPropHash->getRoleBackwardPropagationDataHash();
        //       if (backwardPropDataHash) {
        //           backPropData = (*backwardPropDataHash)[role];
        //           if (!backPropData.mRolePredecessorMergingQueuingRequired) {
        //               backPropData.mRolePredecessorMergingQueuingRequired = true;
        //               installed = true;
        //           }
        //       }
        //   }
        //   return installed;
        // Linked-role-successor-hash + role-backward-propagation-hash satellites not
        // yet ported.
        let _ = (indi_proc_sat_node, role);
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
        // W6-DEFER[api]: faithful C++ body —
        //   linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //   if (linkedSuccHash) {
        //       succData = linkedSuccHash->getLinkedRoleSuccessorData(role, false);
        //       if (succData && succData->mRoleFUNCTIONALConceptsQueuingRequired) {
        //           succData->mRoleFUNCTIONALConceptsProcessingQueued = false;
        //           if (succData->mSuccCount > 1)
        //               updated |= updateSuccessorRoleFUNCTIONALConceptsExtensions(    // → _for_succ_data
        //                   indiProcSatNode, role, succData, ctx);
        //       }
        //   }
        //   return updated;
        // Linked-role-successor-hash satellite not yet ported.
        let _ = (indi_proc_sat_node, role);
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
        // `CLinkedRoleSaturationSuccessorData* succData`
        succ_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated = false;
        // W6-DEFER[api]: faithful C++ body —
        //   linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //   indiProcSatNodeFunctionalConSuccExt =
        //       indiProcSatNode->getSuccessorExtensionData()->getFUNCTIONALConceptsExtensionData(true);
        //   if (succData) {
        //       roleFuncConExtData = indiProcSatNodeFunctionalConSuccExt
        //           ->getSuccessorFUNCTIONALConceptsExtensionData(role, true);
        //       lastExaminedLinkedSucc = roleFuncConExtData->getLastExaminedLinkedSuccessorData();
        //       lastLinkedSucc         = succData->getLastSuccessorLinkData();
        //       if (lastLinkedSucc != lastExaminedLinkedSucc) {
        //           succDataMap = succData->getSuccessorNodeDataMap(false);
        //           deactivateSubsetMergeableSuccessorLinks(indiProcSatNode, linkedSuccHash,    // PU-SAT-8 sibling
        //               succDataMap, role, ctx);
        //           // count active non-nominal successors + their max cardinality:
        //           succCount = 0; maxSuccCardinality = CINT64_MIN;
        //           for (it = lastLinkedSucc; it; it = it->mNextLink)
        //               if (it->mActiveCount >= 1 && !it->mVALUENominalConnection) {
        //                   succCount++; maxSuccCardinality = qMax(maxSuccCardinality, it->mSuccCount); }
        //           if (succCount > 1 && maxSuccCardinality <= 1) {
        //               // build merge link-data list + pick the max-label-concept successor as copy base:
        //               mergingSuccDataLinker = nullptr; maxLabelResolveIndiLinkedSuccData = nullptr; maxLabelResolveIndiConceptCount = 0;
        //               for ((succID, linkedSuccData) in succDataMap)
        //                   if (active && !nominal) {
        //                       succLabelConCount = linkedSuccData->mSuccIndiNode->getReapplyConceptSaturationLabelSet(false)->getConceptCount();
        //                       if (!maxLabelResolveIndiLinkedSuccData && succLabelConCount > maxLabelResolveIndiConceptCount) {
        //                           maxLabelResolveIndiConceptCount = succLabelConCount; maxLabelResolveIndiLinkedSuccData = linkedSuccData; }
        //                       tmp = createIndividualSaturationSuccessorLinkDataLinker(ctx);   // PU-SAT-11 pool helper
        //                       tmp->initSuccessorLinkDataLinker(linkedSuccData);
        //                       mergingSuccDataLinker = tmp->append(mergingSuccDataLinker);
        //                   }
        //               conExtMap = nullptr;
        //               resolveLinkedSuccData = maxLabelResolveIndiLinkedSuccData;
        //               copyIndiProcSatNode   = resolveLinkedSuccData->mSuccIndiNode;
        //               for (it in mergingSuccDataLinker)
        //                   if (it->getData() != resolveLinkedSuccData)
        //                       collectResolveIndividualExtendableConceptMap(copyIndiProcSatNode,           // PU-SAT-10 sibling
        //                           it->getData()->mSuccIndiNode, conExtMap, ctx);
        //               releaseIndividualSaturationSuccessorLinkDataLinker(mergingSuccDataLinker, ctx);     // PU-SAT-11
        //               resolveData = copyIndiProcSatNode->getSuccessorExtensionData(true)->getBaseExtensionResolveData(true);
        //               resolveData = getResolvedIndividualNodeExtension(resolveData, conExtMap, copyIndiProcSatNode, ctx); // PU-SAT-10
        //               resolvedIndiNode = resolveData->getProcessingIndividualNode();
        //               roleFuncConExtData->setLastResolvedIndividualNode(resolvedIndiNode);
        //               backwardLinkConnected = false; connectionAlreadyExist = false;
        //               for ((succID, linkedSuccData) in succDataMap) if (active && !nominal)
        //                   for (creationRoleLinkerIt in linkedSuccData->mCreationRoleLinker) if (!negated) {
        //                       creationRole = creationRoleLinkerIt->getData();
        //                       makeNewSuccessorConnections = true; removePreviousSuccessorConnections = true;
        //                       if (linkedSuccHash->hasActiveLinkedSuccessor(creationRole, resolvedIndiNode)) {
        //                           connectionAlreadyExist = true; makeNewSuccessorConnections = false;
        //                           if (succNode == resolvedIndiNode) removePreviousSuccessorConnections = false;
        //                       }
        //                       for (creationSuperRoleIt in creationRole->getIndirectSuperRoleList()) {
        //                           creationSuperRole = creationSuperRoleIt->getData();
        //                           if (!negated) {
        //                               if (removePreviousSuccessorConnections)
        //                                   linkedSuccHash->deactivateLinkedSuccessor(creationSuperRole, succNode, creationRole);
        //                               if (makeNewSuccessorConnections)
        //                                   linkedSuccHash->addExtensionSuccessor(creationSuperRole, resolvedIndiNode, creationRole, 1);
        //                           } else if (makeNewSuccessorConnections) {
        //                               backwardLinkConnected = true;
        //                               backPropLink = new CBackwardSaturationPropagationLink;
        //                               backPropLink->initBackwardPropagationLink(indiProcSatNode, creationSuperRole);
        //                               installBackwardPropagationLink(indiProcSatNode, resolvedIndiNode, creationSuperRole, backPropLink, true, true, ctx);
        //                           }
        //                       }
        //                   }
        //               updateIndirectAddingIndividualStatusFlags(indiProcSatNode, resolvedIndiNode->getIndirectStatusFlags(), mCalcAlgContext);
        //               updateAddingSuccessorConnectedNominal(indiProcSatNode, resolvedIndiNode->getSuccessorConnectedNominalSet(false), mCalcAlgContext);
        //               updateMaxCardinalityCandidates(indiProcSatNode, resolvedIndiNode->getMaxAtleastCardinalityCandidate(),
        //                   resolvedIndiNode->getMaxAtmostCardinalityCandidate(), mCalcAlgContext);
        //               if (!connectionAlreadyExist && !backwardLinkConnected) {
        //                   nonInvConnectedIndiNodeLinker = new CXLinker<...>; nonInvConnectedIndiNodeLinker->initLinker(indiProcSatNode);
        //                   resolvedIndiNode->addNonInverseConnectedIndividualNodeLinker(nonInvConnectedIndiNodeLinker);
        //               }
        //               updated = true;
        //           }
        //       }
        //   }
        //   return updated;
        // Driven start-to-finish by the FUNCTIONAL-concept extension-data + linked-
        // successor + backward-propagation satellites and by PU-SAT-8/10/11 siblings,
        // none yet ported.
        let _ = (indi_proc_sat_node, role, succ_data);
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
        // W6-DEFER[api]: faithful C++ body —
        //   linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //   if (linkedSuccHash) {
        //       succData = linkedSuccHash->getLinkedRoleSuccessorData(role, false);
        //       if (succData && succData->mSuccCount > 1)
        //           updated |= updateSuccessorRoleQualifiedFUNCTIONALConceptsExtensions(   // → _for_succ_data
        //               indiProcSatNode, role, qualifiyConLinker, succData, ctx);
        //   }
        //   return updated;
        // Linked-role-successor-hash satellite not yet ported.
        let _ = (indi_proc_sat_node, role, qualifiy_con_linker);
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
        succ_data: Cint64,
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
        // W6-DEFER[api]: faithful C++ body —
        //   backwardPropHash = indiProcSatNode->getRoleBackwardPropagationHash(true);
        //   if (backwardPropHash) {
        //       backwardPropDataHash = backwardPropHash->getRoleBackwardPropagationDataHash();
        //       if (backwardPropDataHash) {
        //           backPropData = (*backwardPropDataHash)[role];
        //           if (backPropData.mRolePredecessorMergingQueuingRequired) {
        //               backPropData.mRolePredecessorMergingProcessingQueued = false;
        //               if (backPropData.mLinkLinker) {
        //                   backPropLinkLinker = backPropData.mLinkLinker;
        //                   linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //                   if (linkedSuccHash) {
        //                       succData = linkedSuccHash->getLinkedRoleSuccessorData(role, false);
        //                       if (succData->mSuccCount >= 1)
        //                           updated |= updatePredecessorRoleFUNCTIONALConceptsExtensions(   // → _for_succ_data
        //                               indiProcSatNode, role, succData, backPropLinkLinker, ctx);
        //                   }
        //               }
        //           }
        //       }
        //   }
        //   return updated;
        // Role-backward-propagation-hash + linked-role-successor-hash satellites not
        // yet ported.
        let _ = (indi_proc_sat_node, role);
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
        succ_data: Cint64,
        // `CBackwardSaturationPropagationLink* backPropLinkLinker`
        back_prop_link_linker: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut updated = false;
        // W6-DEFER[api]: faithful C++ body —
        //   linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //   indiProcSatNodeFunctionalConSuccExt =
        //       indiProcSatNode->getSuccessorExtensionData()->getFUNCTIONALConceptsExtensionData(true);
        //   if (succData) {
        //       predRoleFuncConExtData = indiProcSatNodeFunctionalConSuccExt
        //           ->getPredecessorFUNCTIONALConceptsExtensionData(role, true);
        //       lastLinkedSucc = succData->getLastSuccessorLinkData();
        //       activeLinkedSucc = first linkedSuccIt from lastLinkedSucc with mActiveCount >= 1;
        //       if (activeLinkedSucc) {
        //           succIndiNode = activeLinkedSucc->mSuccIndiNode;
        //           if (succIndiNode)
        //               for (backPropLinkLinkerIt = backPropLinkLinker; backPropLinkLinkerIt; backPropLinkLinkerIt = backPropLinkLinkerIt->getNext()) {
        //                   predAncIndiNode = backPropLinkLinkerIt->getSourceIndividual();
        //                   if (succIndiNode != predAncIndiNode)
        //                       updated |= createAncestorSuccessorMergingExtension(            // PU-SAT-8 sibling
        //                           indiProcSatNode, role, succIndiNode, predAncIndiNode,
        //                           activeLinkedSucc->mCreationRoleLinker, ctx);
        //               }
        //       }
        //   }
        //   return updated;
        // `createAncestorSuccessorMergingExtension` is a PU-SAT-8 sibling; the
        // FUNCTIONAL-concept extension-data + linked-successor + backward-propagation
        // satellites are not yet ported.
        let _ = (indi_proc_sat_node, role, succ_data, back_prop_link_linker);
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
        // `CBackwardSaturationPropagationLink* link`
        link: Cint64,
        apply_back_prop_des: bool,
        queue_functional_processing: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut link_installed = false;
        // W6-DEFER[api]: faithful C++ body —
        //   resolvedIndiBackPropHash = destIndiProcSatNode->getRoleBackwardPropagationHash(true);
        //   backPropDataHash = resolvedIndiBackPropHash->getRoleBackwardPropagationDataHash();
        //   backPropData = (*backPropDataHash)[role];
        //   installLink = true;
        //   if (backPropData.mLinkLinker
        //       && backPropData.mLinkLinker->getSourceIndividual() == link->getSourceIndividual())
        //       installLink = false;
        //   if (installLink) {
        //       linkInstalled = true;
        //       backPropData.mLinkLinker = link->append(backPropData.mLinkLinker);   // head-front splice
        //       backPropReapplyDes = backPropData.mReapplyLinker;
        //       if (backPropReapplyDes && applyBackPropDes)
        //           applyBackwardPropagationConcepts(sourceIndiProcSatNode, backPropReapplyDes, ctx); // PU-SAT-3 sibling
        //   }
        //   if (backPropData.mRolePredecessorMergingQueuingRequired && queueFunctionalProcessing) {
        //       if (!backPropData.mRolePredecessorMergingProcessingQueued) {
        //           backPropData.mRolePredecessorMergingProcessingQueued = true;
        //           addSuccessorExtensionToProcessingQueue(destIndiProcSatNode, ctx);            // PU-SAT-7 sibling
        //           succExtData = destIndiProcSatNode->getSuccessorExtensionData(false);
        //           if (succExtData) {
        //               succIndiFUNCTIONALConExtData = succExtData->getFUNCTIONALConceptsExtensionData(false);
        //               if (succIndiFUNCTIONALConExtData && succIndiFUNCTIONALConExtData->isSuccessorExtensionInitialized()
        //                   && !succIndiFUNCTIONALConExtData->hasLinkedPredecessorAddedProcessLinkerForRole(role)) {
        //                   roleProcessLinker = createRoleSaturationProcessLinker(ctx);            // PU-SAT-11 pool helper
        //                   roleProcessLinker->initRoleProcessLinker(role);
        //                   succIndiFUNCTIONALConExtData->addLinkedPredecessorAddedRoleProcessLinker(roleProcessLinker);
        //               }
        //           }
        //       }
        //   }
        //   return linkInstalled;
        // `applyBackwardPropagationConcepts` (PU-SAT-3), `addSuccessorExtensionToProcessingQueue`
        // + `createRoleSaturationProcessLinker` (PU-SAT-7/11) siblings, and the
        // role-backward-propagation-hash + FUNCTIONAL-concept extension-data
        // satellites are not yet ported.
        let _ = (
            source_indi_proc_sat_node,
            dest_indi_proc_sat_node,
            role,
            link,
            apply_back_prop_des,
            queue_functional_processing,
        );
        link_installed
    }
}
