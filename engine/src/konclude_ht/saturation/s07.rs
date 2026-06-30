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
//!     extension-processing queue);
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
//! the C++ `nullptr`). Logic is documented, never silently dropped. No method here
//! is substrate-portable today: every one immediately dereferences the not-yet-ported
//! successor-extension / linked-successor / backward-propagation satellite tower.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::substrate::Cint64;
use super::super::model::{ConceptId, RoleId};
use super::super::process::stubs::ConceptSaturationDescriptorId;
use super::super::process::SatNodeId;

impl super::algorithm::SaturationTaskHandleAlgorithm {
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
        // `CSaturationSuccessorALLConceptExtensionData* allConSuccExtData` — satellite.
        all_con_succ_ext_data: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut new_concept_added = false;
        // W4-DEFER[api]: faithful C++ body —
        //   addOperandConcepts = false; useNegatedOperandConcepts = false;
        //   conOp = concept->getConceptOperator();
        //   if (!conceptNegation && conOp->hasPartialOperatorCodeFlag(CCFS_ALL_AQALL_TYPE)) {
        //       addOperandConcepts = true; useNegatedOperandConcepts = false;
        //   }
        //   if (conceptNegation && conOp->hasPartialOperatorCodeFlag(CCFS_SOME_TYPE)) {
        //       addOperandConcepts = true; useNegatedOperandConcepts = true;
        //   }
        //   if (addOperandConcepts) {
        //       for (opLinkerIt in concept->getOperandList()) {
        //           opConcept = opLinkerIt->getData();
        //           opConceptNegation = opLinkerIt->isNegated() ^ useNegatedOperandConcepts;
        //           newConceptAdded |= allConSuccExtData->addExtensionConcept(opConcept, opConceptNegation);
        //       }
        //   }
        //   return newConceptAdded;
        // `concept->getConceptOperator()` / `getOperandList()` are portable (ConceptId),
        // but the sink `CSaturationSuccessorALLConceptExtensionData::addExtensionConcept`
        // is the not-yet-ported ALL-concept successor-extension satellite.
        let _ = (
            indi_proc_sat_node,
            concept,
            concept_negation,
            all_con_succ_ext_data,
        );
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
        // W4-DEFER[api]: faithful C++ body —
        //   succExtensionData = indiProcSatNode->getSuccessorExtensionData();
        //   functionalConceptsExtension = succExtensionData->getFUNCTIONALConceptsExtensionData();
        //   collectLinkedSuccessorNodes(indiProcSatNode, calcAlgContext);            // self, this unit
        //   if (!functionalConceptsExtension->isSuccessorExtensionInitialized())
        //       functionalConceptsExtension->setSuccessorExtensionInitialized(true);
        //   for (functionalityRoleSatProcLinker = functionalConceptsExtension->takeFunctionalityAddedRoleProcessLinker();
        //        functionalityRoleSatProcLinker; ) {
        //       role = functionalityRoleSatProcLinker->getRole();
        //       tmp = functionalityRoleSatProcLinker; functionalityRoleSatProcLinker = functionalityRoleSatProcLinker->getNext(); tmp->clearNext();
        //       if (installSuccessorPredecessorRoleFunctionalityConceptsExtension(indiProcSatNode, role, ctx)) {  // PU-SAT-6
        //           functionalConceptsExtension->addLinkedSuccessorAddedRoleProcessLinker(tmp);
        //           addFUNCTIONALProcessRoleExtensionFunctionalityAddedToDependentIndividuals(indiProcSatNode, role, ctx); // self
        //           predFuncRoleProcLinker = createRoleSaturationProcessLinker(ctx); predFuncRoleProcLinker->initRoleProcessLinker(role); // PU-SAT-11
        //           functionalConceptsExtension->addLinkedPredecessorAddedRoleProcessLinker(predFuncRoleProcLinker);
        //           copyInitRoleLinker = createRoleSaturationProcessLinker(ctx); copyInitRoleLinker->initRoleProcessLinker(role);
        //           functionalConceptsExtension->addCopyingInitializingRoleProcessLinker(copyInitRoleLinker);
        //       }
        //   }
        //   if (!updated)
        //       for (succLinkedAddedRoleSatProcLinker = functionalConceptsExtension->takeLinkedSuccessorAddedRoleProcessLinker();
        //            succLinkedAddedRoleSatProcLinker; ) {
        //           role = ...->getRole(); tmp = ...; advance; tmp->clearNext();
        //           updated |= updateSuccessorRoleFUNCTIONALConceptsExtensions(indiProcSatNode, role, ctx);   // PU-SAT-6
        //           releaseRoleSaturationProcessLinker(tmp, ctx);                                              // PU-SAT-11
        //       }
        //   if (!updated)
        //       for (predLinkedAddedRoleSatProcLinker = functionalConceptsExtension->takeLinkedPredecessorAddedRoleProcessLinker();
        //            predLinkedAddedRoleSatProcLinker; ) {
        //           role = ...->getRole(); tmp = ...; advance; tmp->clearNext();
        //           updated |= updatePredecessorRoleFUNCTIONALConceptsExtensions(indiProcSatNode, role, ctx);  // PU-SAT-6
        //           releaseRoleSaturationProcessLinker(tmp, ctx);
        //       }
        //   if (!updated)
        //       for (funcQualAtmostConSatProcLinker = functionalConceptsExtension->takeQualifiedFunctionalAtmostConceptProcessLinker();
        //            funcQualAtmostConSatProcLinker; ) {
        //           conDes = ...->getConceptSaturationDescriptor(); tmp = ...; advance; tmp->clearNext();
        //           funcQualAtleastConcept = conDes->getConcept();
        //           updated |= updateSuccessorRoleQualifiedFUNCTIONALConceptsExtensions(                       // PU-SAT-6
        //               indiProcSatNode, funcQualAtleastConcept->getRole(), funcQualAtleastConcept->getOperandList(), ctx);
        //           releaseConceptSaturationProcessLinker(tmp, ctx);                                           // PU-SAT-11
        //           addFUNCTIONALQualifiedProcessAtmostConceptExtensionToDependentIndividuals(indiProcSatNode, conDes, ctx); // self
        //       }
        //   if (succExtensionData->isExtensionProcessingQueued())
        //       succExtensionData->setExtensionProcessingQueued(false);
        //   return updated;
        // Drained start-to-finish through the FUNCTIONAL-concepts successor-extension
        // satellite + the PU-SAT-11 pool helpers, none yet ported.
        let _ = indi_proc_sat_node;
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
        // W4-DEFER[api]: faithful C++ body —
        //   indiProcSatNode = nullptr;
        //   extProIndiQueue = mProcessingDataBox->getSaturationSucessorExtensionIndividualNodeProcessingQueue(false);
        //   while (!extensionProcessed && extProIndiQueue && !extProIndiQueue->isEmpty()) {
        //       indiProcSatNode = extProIndiQueue->takeNextToCurrentProcessIndividual();
        //       if (indiProcSatNode && !indiProcSatNode->isSeparated()) {
        //           if (!extensionProcessed && mConfALLConceptsExtensionProcessing)
        //               extensionProcessed |= processSuccessorALLConceptsExtensions(indiProcSatNode, calcAlgContext);        // self
        //           if (!extensionProcessed && mConfFUNCTIONALConceptsExtensionProcessing)
        //               extensionProcessed |= processSuccessorFUNCTIONALConceptsExtensions(indiProcSatNode, calcAlgContext); // self
        //       }
        //       if (!extensionProcessed)
        //           extProIndiQueue->clearCurrentProcessIndividual();
        //   }
        //   return extensionProcessed;
        // `CSaturationSuccessorExtensionIndividualNodeProcessingQueue` (the databox
        // extension-processing queue) is not yet ported.
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
        let mut updated = false;
        // W4-DEFER[api]: faithful C++ body —
        //   succExtensionData = indiProcSatNode->getSuccessorExtensionData();
        //   allConceptsExtension = succExtensionData->getALLConceptsExtensionData();
        //   collectLinkedSuccessorNodes(indiProcSatNode, calcAlgContext);            // self, this unit
        //   if (!allConceptsExtension->isSuccessorExtensionInitialized()) {
        //       allConceptsExtension->setSuccessorExtensionInitialized(true);
        //       initializeSuccessorALLConceptsExtensions(indiProcSatNode, calcAlgContext);   // PU-SAT-6
        //       addProcessExtensionToDependentIndividuals(indiProcSatNode, calcAlgContext);   // self
        //       initialized = true; mALLSuccExtInitializedCount++;
        //   }
        //   for (roleSatProcLinker = allConceptsExtension->takeRoleProcessLinker(); roleSatProcLinker; ) {
        //       role = roleSatProcLinker->getRole(); tmp = roleSatProcLinker; roleSatProcLinker = roleSatProcLinker->getNext(); tmp->clearNext();
        //       updateSuccessorRoleALLConceptsExtensions(indiProcSatNode, role, calcAlgContext);   // PU-SAT-6
        //       releaseRoleSaturationProcessLinker(tmp, calcAlgContext);                            // PU-SAT-11
        //   }
        //   if (allConceptsExtension->isExtensionProcessingQueued())
        //       allConceptsExtension->setExtensionProcessingQueued(false);
        //   if (succExtensionData->isExtensionProcessingQueued())
        //       succExtensionData->setExtensionProcessingQueued(false);
        //   updated = updateSuccessorALLConceptsExtensions(indiProcSatNode, calcAlgContext);        // PU-SAT-6
        //   return updated;
        // The ALL-concepts successor-extension satellite + the PU-SAT-6/11 siblings
        // are not yet ported.
        let _ = indi_proc_sat_node;
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
        // W4-DEFER[api]: faithful C++ body —
        //   succExtData = indiProcSatNode->getSuccessorExtensionData(true);
        //   succIndiALLConExtData = succExtData->getALLConceptsExtensionData(true);
        //   if (!succExtData->isExtensionProcessingQueued()) {
        //       succExtData->setExtensionProcessingQueued(true);
        //       calcAlgContext->getUsedProcessingDataBox()
        //           ->getSaturationSucessorExtensionIndividualNodeProcessingQueue(true)
        //           ->insertProcessIndiviudal(indiProcSatNode);
        //       return true;
        //   }
        //   return false;
        // The successor-extension data satellite + the databox extension-processing
        // queue are not yet ported.
        let _ = indi_proc_sat_node;
        false
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
        // PARTIAL port of the C++ body (cpp 2738–2754). The copy-depending fan-out +
        // the unconditional `addSuccessorExtensionToProcessingQueue` enqueue resolve
        // (copy-depending linker = SAT-1 slice, now ported). The per-dependent
        // ALL-concept process-linker registration is LEFT DEFERRED: its guard
        // (`isSuccessorExtensionInitialized` / `hasProcessLinkerForRole`) and sink
        // (`addRoleProcessLinker`) live on `CSaturationSuccessorALLConceptExtensionData`,
        // the still-missing successor-extension satellite tower.
        //   for (depIndiLinkerIt in ...getCopyDependingIndividualNodeLinker()) {
        //       depIndi = depIndiLinkerIt->getData();
        //       if (depIndi) {
        //           succExtData = depIndi->getSuccessorExtensionData(true);                // W4-DEFER: opaque tower
        //           succIndiALLConExtData = succExtData->getALLConceptsExtensionData(true); // W4-DEFER: opaque tower
        //           addSuccessorExtensionToProcessingQueue(depIndi, calcAlgContext);
        //           if (succIndiALLConExtData->isSuccessorExtensionInitialized()           // W4-DEFER: opaque tower
        //               && !succIndiALLConExtData->hasProcessLinkerForRole(role)) {
        //               roleProcLinker = createRoleSaturationProcessLinker(calcAlgContext); // PU-SAT-11 (available)
        //               roleProcLinker->initRoleProcessLinker(role);
        //               succIndiALLConExtData->addRoleProcessLinker(roleProcLinker);        // W4-DEFER: opaque sink
        //           }
        //       }
        //   }
        let _ = role;
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
            // W4-DEFER[api]: the conditional ALL-concept role-process-linker
            // registration above needs the CSaturationSuccessorALLConceptExtensionData
            // tower (isSuccessorExtensionInitialized/hasProcessLinkerForRole/addRoleProcessLinker).
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
        // PARTIAL port of the C++ body (cpp 2757–2773). Copy-depending fan-out + the
        // unconditional enqueue resolve (copy-depending linker = SAT-1 slice). The
        // per-dependent FUNCTIONAL linked-successor-added process-linker registration
        // is LEFT DEFERRED on the still-missing
        // `CSaturationSuccessorFUNCTIONALConceptExtensionData` tower.
        //   for (depIndi in ...getCopyDependingIndividualNodeLinker()) if (depIndi) {
        //       succExtData = depIndi->getSuccessorExtensionData(true);                 // W4-DEFER: opaque tower
        //       succIndiFunctionalConExtData = succExtData->getFUNCTIONALConceptsExtensionData(true);
        //       addSuccessorExtensionToProcessingQueue(depIndi, calcAlgContext);
        //       if (succIndiFunctionalConExtData->isSuccessorExtensionInitialized()     // W4-DEFER: opaque tower
        //           && !...->hasLinkedSuccessorAddedProcessLinkerForRole(role)) {
        //           roleProcLinker = createRoleSaturationProcessLinker(calcAlgContext); // PU-SAT-11 (available)
        //           roleProcLinker->initRoleProcessLinker(role);
        //           succIndiFunctionalConExtData->addLinkedSuccessorAddedRoleProcessLinker(roleProcLinker); // W4-DEFER: opaque sink
        //       }
        //   }
        let _ = role;
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
            // W4-DEFER[api]: the conditional FUNCTIONAL linked-successor-added
            // role-process-linker registration needs the
            // CSaturationSuccessorFUNCTIONALConceptExtensionData tower.
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
        // W4-DEFER[api]: faithful C++ body —
        //   for (depIndiLinkerIt in indiProcSatNode->getCopyDependingIndividualNodeLinker()) {
        //       depIndi = depIndiLinkerIt->getData();
        //       if (depIndi) {
        //           succExtData = depIndi->getSuccessorExtensionData(true);
        //           succIndiFunctionalConExtData = succExtData->getFUNCTIONALConceptsExtensionData(true);
        //           if (succIndiFunctionalConExtData->isSuccessorExtensionInitialized()) {
        //               addSuccessorExtensionToProcessingQueue(depIndi, calcAlgContext);   // self
        //               if (!succIndiFunctionalConExtData->hasLinkedPredecessorAddedProcessLinkerForRole(role)) {
        //                   roleProcLinker = createRoleSaturationProcessLinker(calcAlgContext);   // PU-SAT-11
        //                   roleProcLinker->initRoleProcessLinker(role);
        //                   succIndiFunctionalConExtData->addLinkedPredecessorAddedRoleProcessLinker(roleProcLinker);
        //               }
        //           }
        //       }
        //   }
        // The copy-depending linker + FUNCTIONAL-concepts successor-extension
        // satellites + the PU-SAT-11 pool helper are not yet ported.
        let _ = (indi_proc_sat_node, role);
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
        // W4-DEFER[api]: faithful C++ body —
        //   for (depIndiLinkerIt in indiProcSatNode->getCopyDependingIndividualNodeLinker()) {
        //       depIndi = depIndiLinkerIt->getData();
        //       if (depIndi) {
        //           succExtData = depIndi->getSuccessorExtensionData(true);
        //           succIndiFunctionalConExtData = succExtData->getFUNCTIONALConceptsExtensionData(true);
        //           addSuccessorExtensionToProcessingQueue(depIndi, calcAlgContext);   // self
        //           if (!succIndiFunctionalConExtData->hasFunctionalityAddedProcessLinkerForRole(role)) {
        //               roleProcLinker = createRoleSaturationProcessLinker(calcAlgContext);   // PU-SAT-11
        //               roleProcLinker->initRoleProcessLinker(role);
        //               succIndiFunctionalConExtData->addFunctionalityAddedRoleProcessLinker(roleProcLinker);
        //           }
        //       }
        //   }
        // The copy-depending linker + FUNCTIONAL-concepts successor-extension
        // satellites + the PU-SAT-11 pool helper are not yet ported.
        let _ = (indi_proc_sat_node, role);
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
        // W4-DEFER[api]: faithful C++ body —
        //   if (!linkedRoleSuccHash)
        //       linkedRoleSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(true);
        //   lastExaminedConDes = linkedRoleSuccHash->getLastExaminedConceptDescriptor();
        //   conSet = indiProcSatNode->getReapplyConceptSaturationLabelSet(true);
        //   conDesLinker = conSet->getConceptSaturationDescriptionLinker();
        //   for (conDesIt = conDesLinker; conDesIt && conDesIt != lastExaminedConDes; conDesIt = conDesIt->getNext()) {
        //       concept = conDesIt->getConcept(); conNegation = conDesIt->isNegated();
        //       conCode = concept->getOperatorCode();
        //       if (!conNegation && (conCode == CCSOME || conCode == CCAQSOME) || conNegation && (conCode == CCALL))
        //           addLinkedSuccessorNodeForConcept(conDesIt, linkedRoleSuccHash, indiProcSatNode, calcAlgContext);   // self
        //       if (!conNegation && conCode == CCATLEAST || conNegation && conCode == CCATMOST)
        //           addLinkedSuccessorNodeForConcept(conDesIt, linkedRoleSuccHash, indiProcSatNode, calcAlgContext);   // self
        //       if (!conNegation && conCode == CCVALUE)
        //           addLinkedSuccessorNodeForConcept(conDesIt, linkedRoleSuccHash, indiProcSatNode, calcAlgContext);   // self
        //   }
        //   lastSatSuccRoleAssLinker = linkedRoleSuccHash->getLastExaminedRoleAssertionLinker();
        //   satSuccRoleAssLinker = indiProcSatNode->getRoleAssertionLinker();
        //   for (it = satSuccRoleAssLinker; it && it != lastSatSuccRoleAssLinker; it = it->getNext()) {
        //       role = it->getAssertionRole(); roleNegation = it->getAssertionRoleNegation();
        //       destNode = it->getAssertionDestinationNode();
        //       addLinkedSuccessorNodeForRoleAssertion(destNode, role, roleNegation, linkedRoleSuccHash, indiProcSatNode, calcAlgContext); // self
        //   }
        //   linkedRoleSuccHash->setLastExaminedRoleAssertionLinker(satSuccRoleAssLinker);
        //   linkedRoleSuccHash->setLastExaminedConceptDescriptor(conDesLinker);
        // The `CLinkedRoleSaturationSuccessorHash` + `CReapplyConceptSaturationLabelSet`
        // + `CConceptSaturationDescriptor` + `CSaturationSuccessorRoleAssertionLinker`
        // satellites are not yet ported.
        let _ = (indi_proc_sat_node, linked_role_succ_hash);
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
        // `CLinkedRoleSaturationSuccessorHash* linkedRoleSuccHash` — satellite.
        linked_role_succ_hash: Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: faithful C++ body —
        //   for (superRoleIt in role->getIndirectSuperRoleList()) {
        //       superRole = superRoleIt->getData();
        //       if (!superRoleIt->isNegated() ^ roleInversion)
        //           linkedRoleSuccHash->addLinkedSuccessor(superRole, destNode, role, 1, true);
        //       superRoleIt = superRoleIt->getNext();
        //   }
        // `role->getIndirectSuperRoleList()` is portable (RoleId), but the sink
        // `CLinkedRoleSaturationSuccessorHash::addLinkedSuccessor` is the not-yet-
        // ported linked-role-successor-hash satellite.
        let _ = (dest_node, role, role_inversion, linked_role_succ_hash, indi_proc_sat_node);
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
        // `CLinkedRoleSaturationSuccessorHash* linkedRoleSuccHash` — satellite.
        linked_role_succ_hash: Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: faithful C++ body —
        //   concept = conDes->getConcept(); conNegation = conDes->isNegated();
        //   role = concept->getRole(); param = concept->getParameter();
        //   cardinality = param + 1*conNegation; conCode = concept->getOperatorCode();
        //   addSuccessor = false; nominalSuccessor = false; successorCount = 0; nominalID = 0;
        //   if (!conNegation && conCode == CCVALUE) {
        //       addSuccessor = true; successorCount = 1; nominalSuccessor = true;
        //       nominalID = concept->getNominalIndividual()->getIndividualID();
        //   }
        //   if (!conNegation && (conCode == CCSOME || conCode == CCAQSOME) || conNegation && conCode == CCALL) {
        //       addSuccessor = true; successorCount = 1; nominalSuccessor = false;
        //   }
        //   if (cardinality >= 1 && (!conNegation && conCode == CCATLEAST || conNegation && conCode == CCATMOST)) {
        //       addSuccessor = true; successorCount = cardinality; nominalSuccessor = false;
        //   }
        //   if (addSuccessor) {
        //       foundSpecialIndiNode = false; foundOperandIndiNode = false;
        //       // (1) existential-successor reference linking on the concept itself:
        //       conProcData = (CConceptProcessData*)concept->getConceptData();
        //       confSatRefLinkingData = (CConceptSaturationReferenceLinkingData*)conProcData->getConceptReferenceLinking();
        //       extSatCalcRefLinkData = confSatRefLinkingData->getExistentialSuccessorConceptSaturationReferenceLinkingData();
        //       existIndiNode = (CIndividualSaturationProcessNode*)extSatCalcRefLinkData->getIndividualProcessNodeForConcept();
        //       if (existIndiNode) {
        //           foundSpecialIndiNode = true;
        //           for (superRoleIt in role->getIndirectSuperRoleList()) if (!negated)
        //               nominalSuccessor ? linkedRoleSuccHash->addLinkedVALUESuccessor(superRole, nominalID, role)
        //                                : linkedRoleSuccHash->addLinkedSuccessor(superRole, existIndiNode, role, successorCount, false);
        //       }
        //       // (2) else first operand concept's reference linking (negation-folded):
        //       if (!foundSpecialIndiNode)
        //           for (conceptOpLinkerIt in concept->getOperandList()) {
        //               foundOperandIndiNode = true;
        //               opConcept = conceptOpLinkerIt->getData(); opConNegation = conceptOpLinkerIt->isNegated() ^ conNegation;
        //               satCalcRefLinkData = ((CConceptSaturationReferenceLinkingData*)
        //                   ((CConceptProcessData*)opConcept->getConceptData())->getConceptReferenceLinking())
        //                   ->getConceptSaturationReferenceLinkingData(opConNegation);
        //               existIndiNode = (CIndividualSaturationProcessNode*)satCalcRefLinkData->getIndividualProcessNodeForConcept();
        //               if (existIndiNode)
        //                   for (superRoleIt in role->getIndirectSuperRoleList()) if (!negated)
        //                       nominalSuccessor ? addLinkedVALUESuccessor(superRole, nominalID, role)
        //                                        : addLinkedSuccessor(superRole, existIndiNode, role, successorCount, false);
        //           }
        //       // (3) else the (data-)top concept's reference linking:
        //       if (!foundSpecialIndiNode && !foundOperandIndiNode) {
        //           baseTopConcept = role->isDataRole()
        //               ? calcAlgContext->getUsedProcessingDataBox()->getOntologyTopDataRangeConcept()
        //               : calcAlgContext->getUsedProcessingDataBox()->getOntologyTopConcept();
        //           satCalcRefLinkData = ((CConceptSaturationReferenceLinkingData*)
        //               ((CConceptProcessData*)baseTopConcept->getConceptData())->getConceptReferenceLinking())
        //               ->getConceptSaturationReferenceLinkingData(false);
        //           existIndiNode = (CIndividualSaturationProcessNode*)satCalcRefLinkData->getIndividualProcessNodeForConcept();
        //           if (existIndiNode)
        //               for (superRoleIt in role->getIndirectSuperRoleList()) if (!negated)
        //                   nominalSuccessor ? addLinkedVALUESuccessor(superRole, nominalID, role)
        //                                    : addLinkedSuccessor(superRole, existIndiNode, role, successorCount, false);
        //       }
        //   }
        // The concept/role/operand traversal is portable (ConceptId/RoleId), but the
        // resolution bottoms out in `CConceptSaturationReferenceLinkingData` /
        // `CSaturationConceptReferenceLinking::getIndividualProcessNodeForConcept`
        // (the concept→saturation-node reference linking) and the
        // `CLinkedRoleSaturationSuccessorHash` add-successor sinks, none yet ported.
        let _ = (con_des, linked_role_succ_hash, indi_proc_sat_node);
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
        // `CRoleBackwardSaturationPropagationHashData& backPropHashData` — satellite (in/out).
        back_prop_hash_data: Cint64,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: faithful C++ body —
        //   if (mConfALLConceptsExtensionProcessing) {
        //       if (!backPropHashData.mRoleALLConceptsProcessingQueued) {
        //           backPropHashData.mRoleALLConceptsProcessingQueued = true;
        //           succExtData = indiProcSatNode->getSuccessorExtensionData(true);
        //           succIndiALLConExtData = succExtData->getALLConceptsExtensionData(true);
        //           addSuccessorExtensionToProcessingQueue(indiProcSatNode, calcAlgContext);   // self
        //           if (succIndiALLConExtData->isSuccessorExtensionInitialized()
        //               && !succIndiALLConExtData->hasProcessLinkerForRole(role)) {
        //               roleProcessLinker = createRoleSaturationProcessLinker(calcAlgContext);  // PU-SAT-11
        //               roleProcessLinker->initRoleProcessLinker(role);
        //               succIndiALLConExtData->addRoleProcessLinker(roleProcessLinker);
        //           }
        //       }
        //   }
        // The role-backward-propagation hash-data + ALL-concepts successor-extension
        // satellites + the PU-SAT-11 pool helper are not yet ported.
        let _ = (role, back_prop_hash_data, indi_proc_sat_node);
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
        // W4-DEFER[api]: faithful C++ body —
        //   if (mConfFUNCTIONALConceptsExtensionProcessing) {
        //       succExtData = indiProcSatNode->getSuccessorExtensionData(true);
        //       succIndiFUNCTIONALConExtData = succExtData->getFUNCTIONALConceptsExtensionData(true);
        //       addSuccessorExtensionToProcessingQueue(indiProcSatNode, calcAlgContext);   // self
        //       if (!succIndiFUNCTIONALConExtData->hasFunctionalityAddedProcessLinkerForRole(role)) {
        //           roleProcessLinker = createRoleSaturationProcessLinker(calcAlgContext);  // PU-SAT-11
        //           roleProcessLinker->initRoleProcessLinker(role);
        //           succIndiFUNCTIONALConExtData->addFunctionalityAddedRoleProcessLinker(roleProcessLinker);
        //       }
        //   }
        // The FUNCTIONAL-concepts successor-extension satellite + the PU-SAT-11 pool
        // helper are not yet ported.
        let _ = (role, indi_proc_sat_node);
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
        // W4-DEFER[api]: faithful C++ body —
        //   if (mConfFUNCTIONALConceptsExtensionProcessing) {
        //       succExtData = indiProcSatNode->getSuccessorExtensionData(true);
        //       succIndiFUNCTIONALConExtData = succExtData->getFUNCTIONALConceptsExtensionData(true);
        //       addSuccessorExtensionToProcessingQueue(indiProcSatNode, calcAlgContext);   // self
        //       if (!succIndiFUNCTIONALConExtData->hasQualifiedFunctionalAtmostConceptProcessLinkerForConcept(conDes)) {
        //           conProcessLinker = createConceptSaturationProcessLinker(calcAlgContext);  // PU-SAT-11
        //           conProcessLinker->initConceptSaturationProcessLinker(conDes);
        //           succIndiFUNCTIONALConExtData->addQualifiedFunctionalAtmostConceptProcessLinker(conProcessLinker);
        //       }
        //   }
        // The FUNCTIONAL-concepts successor-extension satellite + the PU-SAT-11 pool
        // helper are not yet ported.
        let _ = (con_des, indi_proc_sat_node);
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
        // W4-DEFER[api]: faithful C++ body —
        //   if (mConfConceptsExtensionProcessing) {
        //       succExtData = indiProcSatNode->getSuccessorExtensionData(false);
        //       if (succExtData) {
        //           succIndiALLConExtData = succExtData->getALLConceptsExtensionData(false);
        //           succIndiFUNCTIONALConExtData = succExtData->getFUNCTIONALConceptsExtensionData(false);
        //           succExtensionInitialized = false; succALLExtensionInitialized = false; succFUNCTIONALExtensionInitialized = false;
        //           if (succIndiALLConExtData && succIndiALLConExtData->isSuccessorExtensionInitialized()) { succExtensionInitialized = true; succALLExtensionInitialized = true; }
        //           if (succIndiFUNCTIONALConExtData && succIndiFUNCTIONALConExtData->isSuccessorExtensionInitialized()) { succExtensionInitialized = true; succFUNCTIONALExtensionInitialized = true; }
        //           if (succExtensionInitialized) {
        //               linkedSuccHash = indiProcSatNode->getLinkedRoleSuccessorHash(false);
        //               if (linkedSuccHash) {
        //                   succData = linkedSuccHash->getLinkedRoleSuccessorData(role, true);
        //                   if (succData) {
        //                       queueProcessing = false;
        //                       // --- ALL face ---
        //                       if (succALLExtensionInitialized && !succData->mRoleALLConceptsProcessingQueued && queueALLExtension) {
        //                           allQueueingRequired = succData->mRoleALLConceptsQueuingRequired;
        //                           if (!allQueueingRequired) {
        //                               backwardPropHash = indiProcSatNode->getRoleBackwardPropagationHash(false);
        //                               if (backwardPropHash) {
        //                                   backwardPropData = backwardPropHash->getRoleBackwardPropagationDataHash()->valuePointer(role);
        //                                   if (backwardPropData && backwardPropData->mReapplyLinker) { allQueueingRequired = true; succData->mRoleALLConceptsQueuingRequired = true; }
        //                               }
        //                           }
        //                           if (allQueueingRequired) {
        //                               succData->mRoleALLConceptsProcessingQueued = true; queueProcessing = true;
        //                               if (succIndiALLConExtData->isSuccessorExtensionInitialized() && !succIndiALLConExtData->hasProcessLinkerForRole(role)) {
        //                                   roleProcessLinker = createRoleSaturationProcessLinker(calcAlgContext); roleProcessLinker->initRoleProcessLinker(role); // PU-SAT-11
        //                                   succIndiALLConExtData->addRoleProcessLinker(roleProcessLinker);
        //                               }
        //                           }
        //                       }
        //                       // --- FUNCTIONAL face ---
        //                       if (succFUNCTIONALExtensionInitialized && !succData->mRoleFUNCTIONALConceptsProcessingQueued
        //                           && succData->mRoleFUNCTIONALConceptsQueuingRequired && queueFUNCTIONALExtension) {
        //                           succData->mRoleFUNCTIONALConceptsProcessingQueued = true; queueProcessing = true;
        //                           if (succIndiFUNCTIONALConExtData->isSuccessorExtensionInitialized()) {
        //                               if (!succIndiFUNCTIONALConExtData->hasLinkedSuccessorAddedProcessLinkerForRole(role)) {
        //                                   roleProcessLinker = createRoleSaturationProcessLinker(calcAlgContext); roleProcessLinker->initRoleProcessLinker(role);
        //                                   succIndiFUNCTIONALConExtData->addLinkedSuccessorAddedRoleProcessLinker(roleProcessLinker);
        //                               }
        //                               if (!succIndiFUNCTIONALConExtData->hasLinkedPredecessorAddedProcessLinkerForRole(role)) {
        //                                   roleProcessLinker = createRoleSaturationProcessLinker(calcAlgContext); roleProcessLinker->initRoleProcessLinker(role);
        //                                   succIndiFUNCTIONALConExtData->addLinkedPredecessorAddedRoleProcessLinker(roleProcessLinker);
        //                               }
        //                           }
        //                       }
        //                       if (queueProcessing)
        //                           addSuccessorExtensionToProcessingQueue(indiProcSatNode, calcAlgContext);   // self
        //                   }
        //               }
        //           }
        //       }
        //   }
        // The successor-extension data + linked-role-successor-hash + role-backward-
        // propagation-hash satellites + the PU-SAT-11 pool helper are not yet ported.
        let _ = (role, indi_proc_sat_node, queue_all_extension, queue_functional_extension);
    }
}
