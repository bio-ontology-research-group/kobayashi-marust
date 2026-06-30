//! `completion::u08` — Expansion-rule family, batch 4 (port unit #8 of 36).
//!
//! Faithful port of 10 expansion-rule methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (manifest `01-completion-methods.md`, "Unit 8", cpp ranges 14102–16259):
//!
//!   * `applyDATATYPEIMPLICATIONRule` / `applyDATARESTRICTIONIMPLICATIONRule`
//!     (datatype value-space trigger implication),
//!   * `applyBOTTOMRule` / `applyANDRule` (the conjunction calculus),
//!   * `applySOMERule` / `applyVALUERule` (existential + value generation),
//!   * `applyFUNCTIONALRule` / `applyATMOSTRule` (functional + at-most merging),
//!   * `applyATLEASTRule` (at-least distinct-successor generation),
//!   * `applyNOMINALRule` (nominal merging / distinctness).
//!
//! KONCLUDE-PORT-NOTE[ownership]: a rule method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase` (the C++ `CCalculationAlgorithmContextBase*`).
//! The C++ `CIndividualProcessNode*&` / `CConceptProcessDescriptor*&` out/in-out
//! pointer-references become `&mut NodeId` / `&mut ConProcDescId` (arena ids); a
//! `CConcept*`/`CConceptDescriptor*`/`CDependencyTrackPoint*` field load becomes a
//! `ConceptId`/`ConDescId`/`TrackPointId` resolved through the per-test
//! `ProcessContext` (nodes/descriptors/dependencies) or the static
//! `OntologyArenas` (concepts/roles), per the W3.5 accessor convention:
//!   * `conProDes->getConceptDescriptor()` →
//!     `calc_alg_context.process_context().con_proc_desc(*con_pro_des).get_concept_descriptor()`
//!   * `conDes->getConcept()` →
//!     `calc_alg_context.process_context().con_desc(con_des).get_concept()`
//!   * `concept->getRole()` →
//!     `calc_alg_context.ontology_arenas().concept(concept).get_role()`
//!   * `getProcessingDataBox()->getOntologyTopConcept()` →
//!     `calc_alg_context.processing_data_box().ontology_top_concept()`
//! Sibling rule/queue/dependency methods are `self.<snake_case>(...)` (they land in
//! their own units; the call convention is fixed now).
//!
//! ## Status of the ten methods
//!
//! Four port with FULL faithful bodies — the conjunction + datatype-implication
//! rules, whose only out-of-unit dependencies are sibling factory/queue helpers
//! (`create_and_dependency`, `add_concept_to_individual`,
//! `add_concepts_to_individual`, `addtriggered_value_space_concepts`) and the
//! datatype handler (W6 Cache/handler layer, flagged inline).
//!
//! The other six — SOME / VALUE / FUNCTIONAL / ATMOST / ATLEAST / NOMINAL — are
//! kept `// PORT-PENDING` with a full structural transcription and the exact
//! signature. They are dominated by facilities that have no port yet and cannot be
//! faithfully written without inventing their interfaces:
//!   * the satellite lazy getters `getReapplyConceptLabelSet` /
//!     `getReapplyRoleSuccessorHash` and their iterators (W2-DEFER stubs on
//!     `IndividualProcessNode`),
//!   * the entire merge subsystem (`initializeMergingIndividualNodes`,
//!     `qualifyMergingIndividualNodes`, `mergeMergingIndividualNodes*`,
//!     `getMergedIndividualNodes`, `isIndividualNodesMergeable` — units 12–15),
//!   * the successor-generation / functional-extension machinery
//!     (`createSuccessorIndividual`, `tryExtendFunctionalSuccessorIndividual`,
//!     `createDistinctSuccessorIndividuals`, `createNominalsSuccessorIndividuals` —
//!     units 26/27),
//!   * the backend-cache handler neighbour-visit (`mBackendCacheHandler` — W6
//!     Cache) and the unsatisfiable-cache retrieval strategy (W6 Strategy),
//!   * the clash-exception channel (C++ `throw CCalculationClashProcessingException`
//!     — the rule-layer `[exceptions]` propagation model is not yet established;
//!     `handleTask` in u01 catches one only at the top frame).
//! No logic is dropped: every branch is transcribed in the doc comment so a later
//! reconcile wave fills the body without re-reading the source.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::ConceptId;
use super::super::process::node::IndividualProcessNode;
use super::super::process::{ConDescId, ConProcDescId, NodeId, RestrictionSpecId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Datatype value-space implication rules (cpp 14102–14135).
    //
    // Both forward to the datatype handler (W6 Cache/handler layer) and, if it
    // produced triggered value-space concepts, hand them to
    // `addtriggered_value_space_concepts`. Ported faithfully; the handler call
    // itself is the only `// W6-DEFER[api]` site.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyDATATYPEIMPLICATIONRule`.
    pub fn apply_datatype_implication_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        let datatype: Cint64 = calc_alg_context.ontology_arenas().concept(concept).get_datatype();
        if datatype != INVALID {
            let dep_track_point: TrackPointId = calc_alg_context
                .process_context()
                .con_proc_desc(*con_pro_des)
                .get_dependency_track_point();
            // triggerConcept = concept->getOperandList()->getData() (head operand).
            let trigger_concept: ConceptId =
                calc_alg_context.ontology_arenas().concept(concept).get_operand_list()[0].target;
            let mut triggered_concepts: ConDescId = Id::NONE;
            if self.datatype_handler != Id::NONE && self.conf_datatype_reasoning {
                // W6-DEFER[api]: mDatatypeHandler->triggerDatatypeConcept(processIndi, datatype,
                // negate, depTrackPoint, triggerConcept, triggeredConcepts, calcAlgContext)
                // — CDatatypeIndividualProcessNodeHandler is the W6 datatype/value-space
                // subsystem; `triggered_concepts` stays NONE until it is ported.
                let _ = (datatype, negate, dep_track_point, trigger_concept);
                if triggered_concepts != Id::NONE {
                    self.addtriggered_value_space_concepts(
                        *process_indi,
                        triggered_concepts,
                        calc_alg_context,
                    );
                }
            }
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyDATARESTRICTIONIMPLICATIONRule`.
    pub fn apply_data_restriction_implication_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        // triggerConcept = concept->getOperandList()->getData() (head operand).
        let trigger_concept: ConceptId =
            calc_alg_context.ontology_arenas().concept(concept).get_operand_list()[0].target;
        let mut triggered_concepts: ConDescId = Id::NONE;
        if self.datatype_handler != Id::NONE && self.conf_datatype_reasoning {
            // W6-DEFER[api]: mDatatypeHandler->triggerDataRestrictionConcept(processIndi, concept,
            // negate, depTrackPoint, triggerConcept, triggeredConcepts, calcAlgContext)
            // — W6 datatype/value-space subsystem; `triggered_concepts` stays NONE.
            let _ = (concept, negate, dep_track_point, trigger_concept);
            if triggered_concepts != Id::NONE {
                self.addtriggered_value_space_concepts(
                    *process_indi,
                    triggered_concepts,
                    calc_alg_context,
                );
            }
        }
    }

    // =======================================================================
    // Conjunction calculus (cpp 14138–14171).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyBOTTOMRule`.
    ///
    /// Adds the NEGATED top concept (⊤ negated ≡ ⊥) under a fresh AND dependency:
    /// the bottom rule fires when a node carries ⊥, forcing the (negated) top.
    pub fn apply_bottom_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.applied_and_rule_count += 1;
        // W3-DEFER[macro]: STATINC(ANDRULEAPPLICATIONCOUNT, calc_alg_context)
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();

        let top_concept: ConceptId =
            calc_alg_context.processing_data_box().ontology_top_concept();

        // create dependency
        let mut next_dep_track_point: TrackPointId = Id::NONE;
        let _and_dep_node = self.create_and_dependency(
            &mut next_dep_track_point,
            process_indi,
            con_des,
            dep_track_point,
            calc_alg_context,
        );

        self.add_concept_to_individual(
            top_concept,
            true,
            process_indi,
            next_dep_track_point,
            true,
            false,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyANDRule`.
    pub fn apply_and_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.applied_and_rule_count += 1;
        // W3-DEFER[macro]: STATINC(ANDRULEAPPLICATIONCOUNT, calc_alg_context)
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId = calc_alg_context.process_context().con_desc(con_des).get_concept();
        let concept_negation: bool = negate;
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();

        // create dependency
        let mut next_dep_track_point: TrackPointId = Id::NONE;
        let _and_dep_node = self.create_and_dependency(
            &mut next_dep_track_point,
            process_indi,
            con_des,
            dep_track_point,
            calc_alg_context,
        );

        // KONCLUDE-PORT-NOTE[ownership]: C++ passes the operand `CSortedNegLinker*`
        // directly; the operand list lives in the (ctx-owned) concept arena, so the
        // borrow is collected to an owned `Vec<NegLink<ConceptId>>` before the
        // `&mut self`/`&mut ctx` call. Contents and order are identical.
        let op_con_linker_it: Vec<NegLink<ConceptId>> =
            calc_alg_context.ontology_arenas().concept(concept).get_operand_list().to_vec();

        self.add_concepts_to_individual(
            &op_con_linker_it,
            concept_negation,
            process_indi,
            next_dep_track_point,
            true,
            false,
            None,
            calc_alg_context,
        );
    }

    // =======================================================================
    // Existential / value generation (cpp 14215–14685).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applySOMERule`.
    ///
    /// PORT-PENDING: the ∃-rule. Faithful structure (cpp 14215–14402):
    /// ```text
    /// conDes=conProDes->getConceptDescriptor(); concept=conDes->getConcept(); role=concept->getRole()
    /// depTrackPoint=conProDes->getDependencyTrackPoint(); conceptOpLinker=concept->getOperandList()
    /// saturationNode = getCreationSuccessorSaturationNode(processIndi, conDes, ...)
    /// // (1) BACKEND-CACHE neighbour reuse:
    /// backendSyncData = processIndi->getIndividualBackendCacheSynchronisationData(false)
    /// if backendSyncData && backendSyncData->getAssocitaionData():
    ///   neighbourVisitLimit = (saturationNode incomplete/insufficient) ? 5 : 1
    ///   mBackendCacheHandler->visitNeighbourIndividualIdsForRole(assoc, role, lambda{
    ///       if !nondeterministic: neighbourAssData=getIndividualAssociationData(id);
    ///         contained = all opConcepts present in neighbour FULL_CONCEPT_SET_LABEL;
    ///         if contained: hasAppropriateNeighbourIndividual=true }, true, ...)
    ///   if hasAppropriateNeighbourIndividual:
    ///       markIndividualNodeBackendNonConceptSetRelatedProcessing(processIndi);
    ///       markIndividualNodeBackendNonConceptSetNeighbourLabelRelatedProcessingForDisjointRoles(processIndi, role);
    ///       return
    /// // (2) VALUE shortcut for a single nominal operand:
    /// if !conceptOpLinker->hasNext():
    ///   if (!conceptOpLinker->isNegated()^negate) || (saturationNode && saturationNode->hasNominalIntegrated()):
    ///     nominalConcept=conceptOpLinker->getData()
    ///     if nominalConcept->getOperatorCode()==CCNOMINAL || saturationNode->hasNominalIntegrated():
    ///       indi=nominalConcept->getNominalIndividual(); saturationIntegrateNominal=false
    ///       if !CCNOMINAL && saturationNode->hasNominalIntegrated(): indi=saturationNode->getIntegratedNominalIndividual(); saturationIntegrateNominal=true
    ///       mark…NonConceptSetRelatedProcessing(processIndi)
    ///       locNominalIndi=getLocalizedForcedBackendInitializedNominalIndividualNode(indi->getIndividualID())
    ///       mark…NonConceptSetRelatedAndNeighbourLabelRelatedProcessing(locNominalIndi); mark…ForDisjointRoles(processIndi, role)
    ///       locNominalNodeConSet=locNominalIndi->getReapplyConceptLabelSet(true); nominalConcept=indi->getIndividualNominalConcept()
    ///       if indi->getIndividualID()!=locNominalIndi->getIndividualNodeID(): locNominalNodeConSet->getConceptDescriptor(nominalConcept, nominalConDes, nominalConDepTrackPoint)
    ///       if !hasIndividualsLink(processIndi, locNominalIndi, role, true):
    ///         hasAppropriateNominalConnection = checkBackendCachedNominalConnection(processIndi, role, indi->getIndividualID(), depTrackPoint)
    ///         if !hasAppropriateNominalConnection:
    ///           valueDepNode=createVALUEDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, nominalConDepTrackPoint)
    ///           if saturationIntegrateNominal && !locNominalIndi->getReapplyConceptLabelSet(false)->containsConcept(opData, opNeg^negate): addConceptsToIndividual(conceptOpLinker, negate, locNominalIndi, nextDepTrackPoint, true, true, null)
    ///           createNewIndividualsLinksReapplyed(processIndi, locNominalIndi, role->getIndirectSuperRoleList(), role, nextDepTrackPoint, true)
    ///           if !processIndi->isNominalIndividualNode(): propagateIndividualNodeNominalConnectionStatusToAncestors(processIndi, locNominalIndi)
    ///           propagateIndividualNodeModified(locNominalIndi); addIndividualToProcessingQueue(locNominalIndi)
    ///       else if saturationIntegrateNominal && !contains: createVALUEDependency(...); addConceptsToIndividual(conceptOpLinker, negate, locNominalIndi, nextDepTrackPoint, true, true, null)
    ///       return
    /// // (3) general ∃ successor:
    /// alreadyExistSuitableSuccessor = getRoleSuccessorWithConcepts(processIndi, role, conceptOpLinker, negate)
    /// if !alreadyExistSuitableSuccessor:
    ///   if mConfSatExpCachedSuccAbsorp && processIndi->hasPartialProcessingRestrictionFlags(PRFSATISFIABLECACHED|PRFSIGNATUREBLOCKINGCACHED|PRFCOMPLETIONGRAPHCACHED|PRFSATURATIONSUCCESSORCREATIONBLOCKINGCACHED):
    ///     if isGeneratingConceptSatisfiableCachedAbsorpable(processIndi, conDes): return addSatisfiableCachedAbsorbedGeneratingConcept(conDes, processIndi, depTrackPoint)
    ///   ++mAppliedSOMERuleCount
    ///   if getUsedUnsatisfiableCacheRetrievalStrategy()->testUnsatisfiableCacheForSuccessorGeneration(conProDes, processIndi): testIndividualNodeUnsatisfiableCached(processIndi)
    ///   succIndi = tryExtendFunctionalSuccessorIndividual(processIndi, conDes, role->getIndirectSuperRoleList(), role, conceptOpLinker, negate, depTrackPoint, saturationNode)
    ///   if !succIndi: succIndi = createSuccessorIndividual(...); if processIndi nominal && level<=0: succIndi->setExtendedQueueProcessing(true)
    ///   if processIndi->isIndividualAncestor(succIndi):   // backward dependency
    ///     if mConfSatExpCachedSuccAbsorp && flags: reapplySatisfiableCachedAbsorbedGeneratingConcepts(processIndi)
    ///     newBackwardDepLinker=CXLinker(processIndi); succIndi->addSuccessorIndividualNodeBackwardDependencyLinker(...); processIndi->setBackwardDependencyToAncestorIndividualNode(true)
    ///     if succIndi->hasPartialProcessingRestrictionFlags(PRFSUCCESSORNOMINALCONNECTION) && !processIndi nominal: propagateIndividualNodeNominalConnectionStatusToAncestors(processIndi, succIndi)
    ///   addIndividualToProcessingQueue(succIndi)
    ///   if mConfAnywhereBlockingSomeInitializationHashing: addIndividualNodeCandidateForConcept(succIndi, conceptOpLinker, negate)
    /// else:   // suitable successor already exists — backward dependency only
    ///   if processIndi->isIndividualAncestor(alreadyExistSuitableSuccessor):
    ///     locAncestorIndiNode=getLocalizedIndividual(alreadyExistSuitableSuccessor, false); newBackwardDepLinker=CXLinker(processIndi)
    ///     locAncestorIndiNode->addSuccessorIndividualNodeBackwardDependencyLinker(...); processIndi->setBackwardDependencyToAncestorIndividualNode(true)
    ///     if locAncestorIndiNode->hasPartialProcessingRestrictionFlags(PRFSUCCESSORNOMINALCONNECTION) && !processIndi nominal: propagateIndividualNodeNominalConnectionStatusToAncestors(processIndi, locAncestorIndiNode)
    /// ```
    pub fn apply_some_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // Prelude (cpp 14215–14219), all deps available: the rule's first unported
        // dependency is `getCreationSuccessorSaturationNode` (saturation, unit 27).
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId =
            calc_alg_context.process_context().con_desc(con_des).get_concept();
        let role = calc_alg_context.ontology_arenas().concept(concept).get_role();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        // conceptOpLinker = concept->getOperandList()  (the ∃ qualifier operands)
        let _ = (process_indi, negate, role, dep_track_point);
        // PORT-PENDING: see structural transcription above. Past the prelude the rule
        // needs `getCreationSuccessorSaturationNode` (saturation, unit 27), the
        // backend-cache handler neighbour-visit (W6 Cache), the successor-generation /
        // functional-extension machinery (`createSuccessorIndividual`,
        // `tryExtendFunctionalSuccessorIndividual`, units 26/27), the label-set lazy
        // getter (`getReapplyConceptLabelSet`, W2-DEFER) and the unsatisfiable-cache
        // retrieval strategy (W6 Strategy) — none ported.
        todo!("W3-DEFER: applySOMERule — saturation-node creation / backend-cache / successor-generation / unsat-cache unported");
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyVALUERule`.
    ///
    /// PORT-PENDING: ∀-value to a named nominal. Faithful structure (cpp 14608–14685):
    /// ```text
    /// STATINC(VALUERULEAPPLICATIONCOUNT)
    /// conDes=conProDes->getConceptDescriptor(); concept=conDes->getConcept(); role=concept->getRole()
    /// indi=concept->getNominalIndividual(); depTrackPoint=conProDes->getDependencyTrackPoint()
    /// if indi:
    ///   hasAppropriateNominalConnection = checkBackendCachedNominalConnection(processIndi, role, indi->getIndividualID(), depTrackPoint)
    ///   if hasAppropriateNominalConnection && !negate:
    ///       markIndividualNodeBackendNonConceptSetRelatedProcessing(processIndi); mark…ForDisjointRoles(processIndi, role); return
    /// if indi:
    ///   markIndividualNodeBackendNonConceptSetRelatedProcessing(processIndi)
    ///   locNominalIndi = getLocalizedForcedBackendInitializedNominalIndividualNode(indi->getIndividualID())
    ///   mark…NonConceptSetRelatedAndNeighbourLabelRelatedProcessing(locNominalIndi); mark…ForDisjointRoles(processIndi, role)
    ///   nominalConDepTrackPoint=null
    ///   if -indi->getIndividualID()!=locNominalIndi->getIndividualNodeID() && locNominalIndi->getIndividualMergingHash(false):
    ///       nominalConDepTrackPoint = locNominalIndi->getIndividualMergingHash(false)->value(indi->getIndividualID()).getDependencyTrackPoint()
    ///   if !negate:
    ///     if !hasIndividualsLink(processIndi, locNominalIndi, role, true):
    ///       valueDepNode=createVALUEDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, nominalConDepTrackPoint)
    ///       createNewIndividualsLinksReapplyed(processIndi, locNominalIndi, role->getIndirectSuperRoleList(), role, nextDepTrackPoint, true)
    ///       if !processIndi nominal: propagateIndividualNodeNominalConnectionStatusToAncestors(processIndi, locNominalIndi)
    ///       propagateIndividualNodeModified(locNominalIndi); addIndividualToProcessingQueue(locNominalIndi)
    ///   else:
    ///     negValueDepNode=createNEGVALUEDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, nominalConDepTrackPoint)
    ///     createIndividualNodeNegationLink(processIndi, locNominalIndi, role, nextDepTrackPoint)
    ///     if !processIndi nominal: propagateIndividualNodeNominalConnectionStatusToAncestors(processIndi, locNominalIndi)
    ///     addIndividualToProcessingQueue(locNominalIndi)
    /// ```
    pub fn apply_value_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(VALUERULEAPPLICATIONCOUNT, calc_alg_context)
        // Prelude (cpp 14608–14612), all deps available: the rule's first unported
        // dependency is `checkBackendCachedNominalConnection`.
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId =
            calc_alg_context.process_context().con_desc(con_des).get_concept();
        let role = calc_alg_context.ontology_arenas().concept(concept).get_role();
        let indi = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_nominal_individual();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        let _ = (process_indi, negate, role, indi, dep_track_point);
        // PORT-PENDING: past the prelude the rule needs
        // `checkBackendCachedNominalConnection` /
        // `getLocalizedForcedBackendInitializedNominalIndividualNode` (backend-cache
        // nominal subsystem, units 16/17 + W6 Cache), the individual-merging-hash
        // satellite (W2-DEFER) and the VALUE/NEGVALUE dependency creators + link
        // creators (units 28/29) — none ported.
        todo!("W3-DEFER: applyVALUERule — backend-cache nominal connection / merging-hash / link creators unported");
    }

    // =======================================================================
    // Functional / cardinality merging (cpp 14689–15006).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyFUNCTIONALRule`.
    ///
    /// PORT-PENDING: merges all role successors into one. Faithful structure
    /// (cpp 14689–14820):
    /// ```text
    /// STATINC(FUNCTIONALRULEAPPLICATIONCOUNT); conDes/concept/role/depTrackPoint/conceptOpLinkerIt; reapplied=conProDes->isConceptReapplied()
    /// baseRoleSuccIt = processIndi->getRoleSuccessorLinkIterator(role); roleSuccIt=baseRoleSuccIt
    /// firstSuccNode=null; firstLink=null; nominalNode=processIndi->isNominalIndividualNode()
    /// requiresNNRule=false; hasAlreadyMergingNominal=false
    /// if nominalNode && roleSuccIt.hasNext():   // NN-rule pre-scan
    ///   while !hasAlreadyMergingNominal && checkNNRoleSuccIt.hasNext():
    ///     link=checkNNRoleSuccIt.next()
    ///     if !requiresNNRule && link->getCreatorIndividualID()!=processIndi->getIndividualNodeID(): requiresNNRule=true; nnRequireDepTrackPoint=link->getDependencyTrackPoint()
    ///     succIndi=getSuccessorIndividual(processIndi, link); if succIndi nominal: hasAlreadyMergingNominal=true; firstSuccNode=succIndi; firstLink=link
    /// if !hasAlreadyMergingNominal:
    ///   if requiresNNRule: createNominalsSuccessorIndividuals(processIndi, role->getIndirectSuperRoleList(), role, conceptOpLinkerIt, false, nnRequireDepTrackPoint, 1); lastRoleSuccIt=processIndi->getRoleSuccessorHistoryLinkIterator(role,null); if hasNext: firstSuccNode/firstLink = that successor
    ///   else: while !firstSuccNode && roleSuccIt.hasNext(): firstLink=roleSuccIt.next(); if roleSuccIt.hasNext(): firstSuccNode=getSuccessorIndividual(processIndi, firstLink)
    /// if firstSuccNode:
    ///   // pick minimum-id successor as merge target
    ///   minIndiId=firstSuccNode->getIndividualNodeID(); search roleSuccIt for the smallest (signed, nominal-aware) id → update firstSuccNode/firstLink; if changed: roleSuccIt=baseRoleSuccIt
    ///   locFirstSuccNode=null
    ///   while roleSuccIt.hasNext() && !processIndi->hasPurgedBlockedProcessingRestrictionFlags():
    ///     link=roleSuccIt.next()
    ///     if link!=firstLink && processIndi->hasRoleSuccessorToIndividual(role, link->getOppositeIndividual(processIndi), true):
    ///       succIndi=getSuccessorIndividual(processIndi, link); clashDescriptors=null
    ///       if isIndividualNodesMergeable(firstSuccNode, succIndi, clashDescriptors):
    ///         setIndividualNodeConceptLabelSetModified(processIndi)
    ///         if !locFirstSuccNode: locFirstSuccNode=getLocalizedIndividual(firstSuccNode, link); firstSuccNode=locFirstSuccNode
    ///         locSuccIndiNode=getLocalizedIndividual(succIndi, false)
    ///         funcDepNode=createFUNCTIONALDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, firstLink->getDependencyTrackPoint(), link->getDependencyTrackPoint())
    ///         locFirstSuccNode=getMergedIndividualNodes(locFirstSuccNode, locSuccIndiNode, nextDepTrackPoint); firstSuccNode=locFirstSuccNode; if locFirstSuccNode==locSuccIndiNode: firstLink=link
    ///         roleSuccIt=processIndi->getRoleSuccessorLinkIterator(role)
    ///         if mConfSatExpCachedSuccAbsorp && flags && locFirstSuccNode==getAncestorIndividual(processIndi): reapplySatisfiableCachedAbsorbedGeneratingConcepts(processIndi)
    ///       else: // clash
    ///         clashDescriptors=createClashedConceptDescriptor(clashDescriptors, processIndi, conDes, depTrackPoint)
    ///         clashDescriptors=createIndividualMergeCausingDescriptors(clashDescriptors, firstSuccNode, firstLink, null)
    ///         clashDescriptors=createIndividualMergeCausingDescriptors(clashDescriptors, succIndi, link, null)
    ///         throw CCalculationClashProcessingException(clashDescriptors)
    /// if !reapplied: addConceptToReapplyQueue(conDes, role, processIndi, true, depTrackPoint)
    /// ```
    pub fn apply_functional_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(FUNCTIONALRULEAPPLICATIONCOUNT, calc_alg_context)
        // W3-DEFER[memory-pool]: taskMemMan / processContext
        // Prelude (cpp 14689–14694), all deps available: the rule's first unported
        // dependency is `processIndi->getRoleSuccessorLinkIterator(role)`.
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId =
            calc_alg_context.process_context().con_desc(con_des).get_concept();
        let role = calc_alg_context.ontology_arenas().concept(concept).get_role();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        let reapplied: bool = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .is_concept_reapplied();
        let _ = (process_indi, negate, role, dep_track_point, reapplied);
        // PORT-PENDING: past the prelude the rule needs the role-successor link
        // iterators (`getRoleSuccessorLinkIterator` / `…HistoryLinkIterator`, W2-DEFER
        // satellite), the merge subsystem (`isIndividualNodesMergeable`,
        // `getMergedIndividualNodes`, units 14/15), the NN-rule successor creator
        // (`createNominalsSuccessorIndividuals`, unit 27), the FUNCTIONAL dependency
        // creator + clash-descriptor factory (units 28–30), the `[exceptions]` clash
        // channel and the trailing `if !reapplied: addConceptToReapplyQueue(conDes,
        // role, processIndi, true, depTrackPoint)` — none ported.
        todo!("W3-DEFER: applyFUNCTIONALRule — role-successor iterators / merge subsystem / NN creator / clash channel unported");
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyATMOSTRule`.
    ///
    /// PORT-PENDING: at-most-`n` qualified merging. Faithful structure
    /// (cpp 14861–15006):
    /// ```text
    /// STATINC(ATMOSTRULEAPPLICATIONCOUNT); taskMemMan/processContext; conDes/concept/role/depTrackPoint/conceptOpLinkerIt
    /// procRest=conProDes->getProcessingRestrictionSpecification(); cardinality=concept->getParameter() - 1*negate
    /// if cardinality<0: clash → createClashedConceptDescriptor; throw
    /// if cardinality==1 && !conceptOpLinkerIt: return applyFUNCTIONALRule(processIndi, conProDes, negate)
    /// if mConfSatExpCachedMergAbsorp && processIndi->hasPartialProcessingRestrictionFlags(PRFSATISFIABLECACHED|PRFCOMPLETIONGRAPHCACHED): return addSatisfiableCachedAbsorbedDisjunctionConcept(conDes, processIndi, procRest, depTrackPoint)
    /// roleSuccHash=processIndi->getReapplyRoleSuccessorHash(false); branchingMergingProcRest=null; roleSuccIt; usingLastLink=null; linkCount=0
    /// if !procRest:
    ///   if roleSuccHash: roleSuccIt=roleSuccHash->getRoleSuccessorLinkIterator(role,&linkCount,usingLastLink)
    ///   if !roleSuccIt.hasNext(): // no merging
    ///   else if cardinality<=0 && !conceptOpLinkerIt: clash (concept + link descriptor); throw
    ///   if mConfAtleastAtmostFastClashCheck: walk label set for a conflicting CCATLEAST whose role is a super-role → clash; throw
    ///   atMostDepNode=createATMOSTDependency(processIndi, conDes, depTrackPoint); atMostNonDetDepTrackPoint=createNonDeterministicDependencyTrackPointBranch(atMostDepNode, true)
    ///   branchingMergingProcRest = new CBranchingMergingProcessingRestrictionSpecification(); init…(); initDependencyTracker(atMostNonDetDepTrackPoint); initMergingDependencyNode(atMostDepNode)
    ///   if getUsedUnsatisfiableCacheRetrievalStrategy()->testUnsatisfiableCacheForMergingInitialization(conProDes, processIndi): testIndividualNodeUnsatisfiableCached(processIndi)
    /// else:
    ///   prevBranchingMergingProcRest=(…)procRest; roleSuccIt=roleSuccHash->getRoleSuccessorHistoryLinkIterator(role, prevBranchingMergingProcRest->getLastIndividualLink(), &linkCount)
    ///   if cardinality<=0 && linkCount>0 && !conceptOpLinkerIt: clash; throw
    ///   newBranchingMergingProcRest = new CBranchingMergingProcessingRestrictionSpecification(prevBranchingMergingProcRest); branchingMergingProcRest=newBranchingMergingProcRest
    /// initializeMergingIndividualNodes(processIndi, conProDes, &roleSuccIt, usingLastLink, conceptOpLinkerIt, branchingMergingProcRest)
    /// qualifyMergingIndividualNodes(processIndi, conProDes, branchingMergingProcRest)
    /// if mConfPairwiseMerging: mergeMergingIndividualNodesPairwise(processIndi, conProDes, linkCount, cardinality, branchingMergingProcRest)
    /// else: mergeMergingIndividualNodes(processIndi, conProDes, linkCount, cardinality, branchingMergingProcRest)
    /// addConceptToReapplyQueue(conDes, role, processIndi, branchingMergingProcRest, depTrackPoint)
    /// ```
    pub fn apply_atmost_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(ATMOSTRULEAPPLICATIONCOUNT, calc_alg_context)
        // W3-DEFER[memory-pool]: taskMemMan / processContext
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId =
            calc_alg_context.process_context().con_desc(con_des).get_concept();
        let role = calc_alg_context.ontology_arenas().concept(concept).get_role();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        // conceptOpLinkerIt = concept->getOperandList(); `!conceptOpLinkerIt` ≡ unqualified.
        let has_operands: bool = !calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .is_empty();
        let proc_rest: RestrictionSpecId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_processing_restriction_specification();
        let mut cardinality: Cint64 =
            calc_alg_context.ontology_arenas().concept(concept).get_parameter();
        if negate {
            cardinality -= 1;
        }
        if cardinality < 0 {
            // clash: createClashedConceptDescriptor + throw CCalculationClashProcessingException
            let clash = self.create_clashed_concept_descriptor(
                Id::NONE,
                process_indi,
                con_des,
                dep_track_point,
                calc_alg_context,
            );
            calc_alg_context.raise_clash(clash);
            return;
        } else if cardinality == 1 && !has_operands {
            // unqualified at-most-1 ≡ functional.
            self.apply_functional_rule(process_indi, con_pro_des, negate, calc_alg_context);
            return;
        }
        if self.conf_sat_exp_cached_merg_absorp
            && calc_alg_context
                .process_context()
                .node(*process_indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SATISFIABLECACHED
                        | IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
                )
        {
            // W3-DEFER[macro]: STATINC(SATCACHEDABSORBEDMERGINGCONCEPTSCOUNT, calc_alg_context)
            self.add_satisfiable_cached_absorbed_disjunction_concept(
                con_des,
                *process_indi,
                proc_rest,
                dep_track_point,
                calc_alg_context,
            );
            return;
        }
        let _ = role;
        // PORT-PENDING (remainder): the role-successor-hash satellite + its iterators
        // (`getReapplyRoleSuccessorHash` / `getRoleSuccessorLinkIterator` /
        // `getRoleSuccessorHistoryLinkIterator`, W2-DEFER), the at-most fast-clash
        // label walk (`mConfAtleastAtmostFastClashCheck`), the ATMOST /
        // non-deterministic dependency creators (units 28/29), the branching-merging
        // restriction-spec allocation, the merge subsystem
        // (`initializeMergingIndividualNodes`, `qualifyMergingIndividualNodes`,
        // `mergeMergingIndividualNodes[Pairwise]`, units 12–15), the
        // unsatisfiable-cache retrieval strategy (W6 Strategy) and the trailing
        // `addConceptToReapplyQueue` — none ported.
        todo!("W3-DEFER: applyATMOSTRule remainder — role-succ-hash iterators / merge subsystem / restriction-spec alloc / unsat-cache unported");
    }

    // =======================================================================
    // At-least / nominal generation (cpp 16068–16259).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyATLEASTRule`.
    ///
    /// PORT-PENDING: at-least-`n` distinct-successor generation. Faithful structure
    /// (cpp 16068–16153):
    /// ```text
    /// STATINC(ATLEASTRULEAPPLICATIONCOUNT); conDes/concept/role/depTrackPoint/conceptOpLinkerIt
    /// cardinality = concept->getParameter() + 1*negate
    /// if cardinality<=0: return
    /// else if cardinality==1: applySOMERule(processIndi, conProDes, false)
    /// if mConfSatExpCachedSuccAbsorp && processIndi->hasPartialProcessingRestrictionFlags(PRFSATISFIABLECACHED|PRFSIGNATUREBLOCKINGCACHED|PRFCOMPLETIONGRAPHCACHED|PRFSATURATIONSUCCESSORCREATIONBLOCKINGCACHED): return addSatisfiableCachedAbsorbedGeneratingConcept(conDes, processIndi, depTrackPoint)
    /// alreadyExistSuitableSuccessors = hasDistinctRoleSuccessorConcepts(processIndi, role, conceptOpLinkerIt, false, cardinality)
    /// if !alreadyExistSuitableSuccessors:
    ///   if mConfAtleastAtmostFastClashCheck: walk label set for a conflicting CCATMOST whose role is a super-role of this role → clash; throw
    ///   if getUsedUnsatisfiableCacheRetrievalStrategy()->testUnsatisfiableCacheForSuccessorGeneration(conProDes, processIndi): testIndividualNodeUnsatisfiableCached(processIndi)
    ///   ++mAppliedATLEASTRuleCount
    ///   atleastDepNode=createATLEASTDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint)
    ///   indiList=PROCESSINGLIST; createDistinctSuccessorIndividuals(processIndi, conDes, indiList, role->getIndirectSuperRoleList(), role, conceptOpLinkerIt, false, nextDepTrackPoint, cardinality)
    ///   for succIndi in indiList: STATINC(DISTINCTSUCCESSORINDINODECREATIONCOUNT); if processIndi nominal && level<=0: succIndi->setExtendedQueueProcessing(true); addIndividualToProcessingQueue(succIndi)
    /// ```
    pub fn apply_atleast_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(ATLEASTRULEAPPLICATIONCOUNT, calc_alg_context)
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId =
            calc_alg_context.process_context().con_desc(con_des).get_concept();
        let role = calc_alg_context.ontology_arenas().concept(concept).get_role();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        let mut cardinality: Cint64 =
            calc_alg_context.ontology_arenas().concept(concept).get_parameter();
        if negate {
            cardinality += 1;
        }
        if cardinality <= 0 {
            return;
        } else if cardinality == 1 {
            // at-least-1 ≡ ∃.
            self.apply_some_rule(process_indi, con_pro_des, false, calc_alg_context);
        } else {
            if self.conf_sat_exp_cached_succ_absorp
                && calc_alg_context
                    .process_context()
                    .node(*process_indi)
                    .has_partial_processing_restriction_flags(
                        IndividualProcessNode::PRF_SATISFIABLECACHED
                            | IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED
                            | IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED
                            | IndividualProcessNode::PRF_SATURATIONSUCCESSORCREATIONBLOCKINGCACHED,
                    )
            {
                self.add_satisfiable_cached_absorbed_generating_concept(
                    con_des,
                    *process_indi,
                    dep_track_point,
                    calc_alg_context,
                );
                return;
            }
            let _ = role;
            // PORT-PENDING (cardinality>=2 remainder): the at-least fast-clash label
            // walk (`mConfAtleastAtmostFastClashCheck`), the unsatisfiable-cache
            // retrieval strategy (W6 Strategy), `++mAppliedATLEASTRuleCount`,
            // `createATLEASTDependency`, `hasDistinctRoleSuccessorConcepts` +
            // `createDistinctSuccessorIndividuals` (distinct-successor generation,
            // unit 27) and the per-successor processing-queue insertion — none ported.
            todo!("W3-DEFER: applyATLEASTRule cardinality>=2 — distinct-successor generation / fast-clash label set / unsat-cache unported");
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyNOMINALRule`.
    ///
    /// PORT-PENDING: nominal merging (positive) / distinctness (negated). Faithful
    /// structure (cpp 16162–16259):
    /// ```text
    /// STATINC(NOMINALRULEAPPLICATIONCOUNT); conDes/concept; indi=concept->getNominalIndividual(); depTrackPoint
    /// nominalNode = getCorrectedNominalIndividualNode(-indi->getIndividualID())
    /// if !negate:
    ///   if nominalNode->getIndividualNodeID()!=processIndi->getIndividualNodeID():
    ///     locNominalNode=getLocalizedForcedBackendInitializedNominalIndividualNode(nominalNode); mark…NonConceptSetRelatedAndNeighbourLabelRelatedProcessing(locNominalNode)
    ///     locNominalNodeConSet=locNominalNode->getReapplyConceptLabelSet(true); nominalConcept=indi->getIndividualNominalConcept(); nominalConDes=null; nominalConDepTrackPoint=null
    ///     if -indi->getIndividualID()!=locNominalNode->getIndividualNodeID(): locNominalNodeConSet->getConceptDescriptor(nominalConcept, nominalConDes, nominalConDepTrackPoint)
    ///     STATINC(INDINODENOMINALMERGECOUNT); clashDescriptors=null
    ///     if isIndividualNodesMergeable(processIndi, locNominalNode, clashDescriptors):
    ///       propagateIndividualNodeNominalConnectionStatusToAncestors(processIndi, locNominalNode)
    ///       nominalDepNode=createNOMINALDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, nominalConDepTrackPoint)
    ///       mergedNode=getMergedIndividualNodes(processIndi, locNominalNode, nextDepTrackPoint)
    ///     else: clashDescriptors=createClashedConceptDescriptor(…, processIndi, conDes, depTrackPoint); if nominalConDes: createClashedConceptDescriptor(…, locNominalNode, nominalConDes, nominalConDepTrackPoint); throw
    /// else:  // negated: enforce distinctness, detect identity clash
    ///   clashed=false; clashDescriptors=null
    ///   if processIndi->getNominalIndividual() && processIndi->getNominalIndividual()->getIndividualID()==indi->getIndividualID(): clashed=true; descriptors=conDes + nominalNode->getDependencyTrackPoint()
    ///   indiMergingHash=processIndi->getIndividualMergingHash(false); if indiMergingHash && indiMergingHash->hasMergedIndividual(indi->getIndividualID()): clashed=true; descriptors=conDes + mergingData.getDependencyTrackPoint()
    ///   if clashed: throw CCalculationClashProcessingException(clashDescriptors)
    ///   locNominalNode=getLocalizedIndividual(nominalNode, false); nominalConDepTrackPoint = (-indi id != loc id) ? locNominalNode->getIndividualMergingHash(true)->value(indi id).getDependencyTrackPoint() : null
    ///   nominalDepNode=createNOMINALDependency(nextDepTrackPoint, processIndi, conDes, depTrackPoint, nominalConDepTrackPoint)
    ///   disEdge = new CDistinctEdge(); disEdge->initDistinctEdge(processIndi, locNominalNode, nextDepTrackPoint)
    ///   processIndi->getDistinctHash(true)->insertDistinctIndividual(locNominalNode->getIndividualNodeID(), disEdge)
    ///   locNominalNode->getDistinctHash(true)->insertDistinctIndividual(processIndi->getIndividualNodeID(), disEdge)
    /// ```
    pub fn apply_nominal_rule(
        &mut self,
        process_indi: &mut NodeId,
        con_pro_des: &mut ConProcDescId,
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[macro]: STATINC(NOMINALRULEAPPLICATIONCOUNT, calc_alg_context)
        // Prelude (cpp 16162–16166), all deps available: the rule's first unported
        // dependency is `getCorrectedNominalIndividualNode`.
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_concept_descriptor();
        let concept: ConceptId =
            calc_alg_context.process_context().con_desc(con_des).get_concept();
        let indi = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_nominal_individual();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        let _ = (process_indi, negate, indi, dep_track_point);
        // PORT-PENDING: past the prelude the rule needs the nominal-node
        // correction/localization helpers (`getCorrectedNominalIndividualNode`,
        // `getLocalizedForcedBackendInitializedNominalIndividualNode`, units 16/17),
        // the merge subsystem (`isIndividualNodesMergeable`,
        // `getMergedIndividualNodes`, units 14/15), the NOMINAL dependency creator +
        // clash-descriptor factory (units 28–30), the individual-merging-hash and
        // distinct-hash satellites (W2-DEFER), the `CDistinctEdge` allocation and the
        // `[exceptions]` clash channel — none ported.
        todo!("W3-DEFER: applyNOMINALRule — nominal correction / merge subsystem / distinct edges / clash channel unported");
    }
}
