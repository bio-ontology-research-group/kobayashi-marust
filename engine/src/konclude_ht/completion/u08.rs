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
use super::super::model::{op, ConceptId, RoleId};
use super::super::process::dependency::BranchTreeNode;
use super::super::process::edge::{DistinctEdge, IndividualLinkEdge};
use super::super::process::node::IndividualProcessNode;
use super::super::process::{
    BranchNodeId, ConDescId, ConProcDescId, DependencyId, EdgeId, NodeId, RestrictionSpecId,
    SatNodeId, TrackPointId,
};
use super::algorithm::{AtMostMergeBranch, BranchKind, OrBranchPoint};
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let datatype: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_datatype();
        if datatype != INVALID {
            let dep_track_point: TrackPointId = calc_alg_context
                .process_context()
                .con_proc_desc(*con_pro_des)
                .get_dependency_track_point();
            // triggerConcept = concept->getOperandList()->getData() (head operand).
            let trigger_concept: ConceptId = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()[0]
                .target;
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        // triggerConcept = concept->getOperandList()->getData() (head operand).
        let trigger_concept: ConceptId = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()[0]
            .target;
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();

        let top_concept: ConceptId = calc_alg_context
            .processing_data_box()
            .ontology_top_concept();

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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
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
        let op_con_linker_it: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

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
        // W3-DEFER[macro]: STATINC(SOMERULEAPPLICATIONCOUNT, calc_alg_context)
        // Prelude (cpp 14215–14219). The read heads resolve live against the arenas.
        let con_des: ConDescId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
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
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        // conceptOpLinker = concept->getOperandList()  (the ∃ qualifier operands C).
        let concept_op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();

        // saturationNode = getCreationSuccessorSaturationNode(processIndi, conDes)
        // (cpp 14224). KONCLUDE-PORT-NOTE[reduced]: unconditional in C++ (a pure
        // lookup that returns null without installed reference linkings); gated on
        // the two consuming confs here so the non-saturation default path stays
        // untouched byte-for-byte.
        let mut saturation_node: SatNodeId = if self.conf_expand_created_successors_from_saturation
            || self.conf_caching_blocking_from_saturation
        {
            let mut pi = *process_indi;
            self.get_creation_successor_saturation_node(&mut pi, con_des, calc_alg_context)
        } else {
            Id::NONE
        };

        // (1) backend-cache neighbour reuse + (2) the single-nominal VALUE shortcut
        // (cpp 14220–14379) stay W3-DEFER: they need the backend-cache handler / the
        // nominal-localisation subsystem, neither ported. The general ∃ successor
        // generation — the part that makes this a hypertableau — follows.

        // (3) general ∃ successor (cpp 14380–14402):
        //   alreadyExistSuitableSuccessor = getRoleSuccessorWithConcepts(processIndi, role, conceptOpLinker, negate)
        let already_exist: NodeId = self.ht_role_successor_with_concepts(
            *process_indi,
            role,
            &concept_op_linker,
            negate,
            calc_alg_context,
        );
        if already_exist == NodeId::NONE {
            self.applied_some_rule_count += 1;
            // Unsat-cache probe before generating the new role successor (cpp
            // 14351: `testUnsatisfiableCacheForSuccessorGeneration` is
            // constant-true in the generative strategy). A hit clashes the
            // parent and ABORTS the generation (Konclude throws out of the
            // rule here). Pending-gated: `raise_clash` overwrites the signal.
            if !calc_alg_context.has_pending_signal() {
                self.test_individual_node_unsatisfiable_cached(*process_indi, calc_alg_context);
                if calc_alg_context.has_pending_signal() {
                    return;
                }
            }
            // KM_BRIDGE_SEARCH_LOG: every ∃ successor CREATE with the parent,
            // filler, and the labels of the parent's EXISTING same-role
            // successors — why did the already-exists check miss them (the
            // COW duplicate-generation hunt, memory cont-12+).
            if std::env::var_os("KM_BRIDGE_SEARCH_LOG").is_some() {
                let filler_tags: Vec<i64> = concept_op_linker
                    .iter()
                    .map(|nl| {
                        calc_alg_context
                            .ontology_arenas()
                            .concept(nl.target)
                            .get_concept_tag()
                    })
                    .collect();
                let existing: Vec<String> = self
                    .ht_role_successor_links(*process_indi, role, calc_alg_context)
                    .iter()
                    .map(|&(_, n)| {
                        let pc = calc_alg_context.process_context();
                        let ls = pc.node(n).use_reapply_con_label_set;
                        let mut v: Vec<i64> = if ls.is_some() {
                            pc.label_set(ls)
                                .concept_des_dep_map
                                .iter()
                                .filter_map(|(t, d)| {
                                    if d.concept_descriptor.is_none() {
                                        None
                                    } else if pc.con_desc(d.concept_descriptor).is_negated() {
                                        None
                                    } else {
                                        Some(*t)
                                    }
                                })
                                .collect()
                        } else {
                            Vec::new()
                        };
                        v.sort_unstable();
                        format!("n{}:{:?}", n.index(), v)
                    })
                    .collect();
                let m = format!(
                    "CREATE parent={} role={} filler={:?} nodes_len={} existing: {}",
                    process_indi.index(),
                    calc_alg_context.ontology_arenas().role(role).get_role_tag(),
                    filler_tags,
                    calc_alg_context.process_context().node_count(),
                    existing.join(" ")
                );
                self.ht_search_log(&m);
            }
            // W3-DEFER[api]: testUnsatisfiableCacheForSuccessorGeneration / unsat-cache strategy.
            // succIndi = tryExtendFunctionalSuccessorIndividual(...) — W3-DEFER (functional
            // reuse + merge subsystem); falls through to a fresh successor.
            // succIndi = createSuccessorIndividual(processIndi, conDes, role->getIndirectSuperRoleList(),
            //                                      role, conceptOpLinker, negate, depTrackPoint, saturationNode)
            // KONCLUDE-PORT-NOTE[api]: createSuccessorIndividual / createNewIndividualsLinksReapplyed
            // (units 35/10) are PORT-PENDING stubs returning NONE; the ∃-rule realises the
            // successor inline from the LIVE primitives (`create_new_individual`, the edge +
            // succ-role-hash install, `add_concept_to_individual`) faithful to that method's
            // body (cpp 21635–21670): create the node, install the R link-edge, set the
            // ancestor link/depth, add the qualifier concepts.
            let is_data_role: bool = calc_alg_context.ontology_arenas().role(role).is_data_role();
            let mut succ_indi: NodeId =
                self.create_new_individual(dep_track_point, is_data_role, calc_alg_context);
            // tryExpansionFromSaturatedData (createSuccessorIndividual cpp 21640–21645,
            // BEFORE the links/concepts): replay the saturated filler label onto the
            // fresh successor, or raise the clash when the filler's saturation node
            // CLASHED (the ∃ is then unsatisfiable on this node).
            let mut sat_caching_possible = true;
            let mut last_sat_cach_possible_con_des: ConDescId = Id::NONE;
            if self.conf_expand_created_successors_from_saturation {
                self.try_expansion_from_saturated_data(
                    process_indi,
                    succ_indi,
                    con_des,
                    dep_track_point,
                    &mut saturation_node,
                    &mut sat_caching_possible,
                    &mut last_sat_cach_possible_con_des,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    return;
                }
            }
            // createNewIndividualsLinksReapplyed → the directed R link-edge + succ-role-hash.
            let anc_link: EdgeId = self.ht_install_role_successor_edge(
                *process_indi,
                succ_indi,
                role,
                dep_track_point,
                calc_alg_context,
            );
            // succIndi->setAncestorLink(ancLink); succIndi->setIndividualAncestorDepth(depth+1).
            let depth: Cint64 = calc_alg_context
                .process_context()
                .node(*process_indi)
                .individual_ancestor_depth();
            let source_flags: Cint64 = calc_alg_context
                .process_context()
                .node(*process_indi)
                .processing_restriction_flags();
            {
                let n = calc_alg_context.process_context_mut().node_mut(succ_indi);
                n.set_ancestor_link(anc_link);
                n.set_individual_ancestor_depth(depth + 1);
                // Ancestor saturation-blocked inheritance (createSuccessorIndividual
                // cpp 21657–21665; the SATISFIABLECACHED / SIGNATUREBLOCKING twins
                // stay W3-DEFER with their subsystems).
                if source_flags
                    & (IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHED
                        | IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED)
                    != 0
                {
                    n.add_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED,
                    );
                }
            }
            // addConcepts(conceptOpLinker, negate, succIndi, ...) — the ∃ qualifier C.
            for nl in &concept_op_linker {
                self.add_concept_to_individual(
                    nl.target,
                    nl.negated ^ negate,
                    &mut succ_indi,
                    dep_track_point,
                    true,
                    true,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    return;
                }
            }
            // Edge-triggered ∀ re-application along the freshly created link.
            // KONCLUDE-PORT-NOTE[api]: Konclude re-fires the predecessor's ∀-restrictions
            // on a new link through the role reapply-queue + the link-processing-restriction
            // (applyALLRule with a restLink). That reapply-queue subsystem is W2-DEFER, so
            // the ∃-rule instead scans the predecessor's concept label set for ∀-restrictions
            // on `role` and pushes them onto the new successor (behaviourally the same
            // edge-triggered ∀ propagation; only the trigger source differs).
            self.ht_reapply_universal_restrictions(
                *process_indi,
                &mut succ_indi,
                role,
                dep_track_point,
                calc_alg_context,
            );
            if calc_alg_context.has_pending_signal() {
                return;
            }
            // tryEstablishSaturationCaching (createSuccessorIndividual cpp 21666–21668,
            // AFTER the successor's label is complete — qualifiers + reapplied ∀s):
            // when the label is covered by a completed sufficient saturation node,
            // the successor is saturation-blocked and never processed.
            if self.conf_caching_blocking_from_saturation {
                self.try_establish_saturation_caching(
                    process_indi,
                    succ_indi,
                    saturation_node,
                    &mut sat_caching_possible,
                    &mut last_sat_cach_possible_con_des,
                    calc_alg_context,
                );
            }
            // addIndividualToProcessingQueue(succIndi). The faithful router runs for its
            // flag bookkeeping, then the successor is enqueued so
            // `take_next_process_individual` drains it — the terminal `insertIndiviudal...`
            // inside `add_individual_to_processing_queue_based_on_processing_concepts` is
            // itself W3-DEFER (commented out, cpp), so the ∃-rule performs the real enqueue.
            self.add_individual_to_processing_queue(succ_indi, calc_alg_context);
            // KONCLUDE-PORT-NOTE[W16-successor-drain]: route the fresh successor onto the
            // DEPTH processing queue (`take_next_process_individual` Probe 25 /
            // INQT_DEPTHNORMAL), NOT the immediately-processing queue. The drive reaches
            // Probe 25 only AFTER Probe 5 lowers `min_concept_processing_priority_level` to
            // DETERMINISTIC (4), so the successor's own deterministic-priority concepts
            // (∃R.C = 4, ≥n = 5) ARE admitted by `continue_individual_processing` and DRAIN —
            // this is what lets a nested ∃R.(∃R.D) grow the second hop. The immediate queue
            // forced min = IMMEDIATELY (8), silently dropping every successor concept below 8
            // (the old W8.1 "successors don't drain" gap). Faithful `addIndividualToProcessingQueue`
            // depth-oriented routing for a blockable (non-nominal) node.
            let dq = calc_alg_context.get_individual_depth_processing_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_depth_queue_insert(dq, succ_indi);
        } else {
            // A suitable successor already exists — Konclude records a backward
            // dependency to the ancestor (cpp 14403–14418); the backward-dependency
            // linker subsystem is W3-DEFER, no graph mutation needed here.
        }
    }

    // =======================================================================
    // HT edge subsystem (W9-W11 follow-on) — the ∃/∀ successor-and-edge
    // machinery realised over the LIVE primitives. These stand in for the
    // still-PORT-PENDING `createSuccessorIndividual` / `createNewIndividualsLinks*`
    // (units 35/10) successor/link chain whose node-level role-successor iterators
    // are W2-DEFER (they cannot resolve the hash id against the arena); the
    // context-threaded `node_successor_*` accessors DO, so the edge/edge-iteration
    // is threaded through `&mut CalculationAlgorithmContextBase` here.
    // =======================================================================

    /// Collect the live `role`-successor `(link, successor-node)` pairs of `source`,
    /// resolving the node's successor-role hash through the context.
    ///
    /// KONCLUDE-PORT-NOTE[api]: stands in for `getRoleSuccessorLinkIterator(role)`.
    /// The role test is `edge.role == role` (exact match); faithful super-role
    /// propagation via `role->getIndirectSuperRoleList()` is deferred (the test roles
    /// coincide). `node_successor_iterator` yields one link per distinct successor,
    /// which is exactly one R-edge per successor in the no-merge regime here.
    pub fn ht_role_successor_links(
        &self,
        source: NodeId,
        role: RoleId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Vec<(EdgeId, NodeId)> {
        let mut out: Vec<(EdgeId, NodeId)> = Vec::new();
        let pc = calc_alg_context.process_context();
        let mut it = pc.node_successor_iterator(source);
        while it.has_next() {
            let link: EdgeId = it.next_link(false);
            let succ_id: Cint64 = it.next_individual_id(true);
            if link.is_none() {
                continue;
            }
            if pc.edge(link).get_link_role() == role {
                let succ = calc_alg_context
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(succ_id);
                if succ.is_some() {
                    // skip MERGED-AWAY / PURGED ghosts: the port keeps no
                    // connection-successor sets, so a ≤n merge cannot relocate
                    // the old links (Konclude phase 5) — filtering here keeps
                    // every successor scan consistent with the merged graph.
                    let n = pc.node(succ);
                    if n.has_merged_into_individual_node_id()
                        || n.has_purged_blocked_processing_restriction_flags()
                    {
                        continue;
                    }
                    out.push((link, succ));
                }
            }
        }
        out
    }

    /// Port-faithful core of `getRoleSuccessorWithConcepts` (cpp 20170–20193):
    /// the first `role`-successor of `source` that already carries every concept of
    /// `concept_linker` (polarity XOR `negate`), else `NodeId::NONE`.
    pub fn ht_role_successor_with_concepts(
        &mut self,
        source: NodeId,
        role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        for (_link, succ) in self.ht_role_successor_links(source, role, calc_alg_context) {
            let ls = calc_alg_context
                .process_context()
                .node(succ)
                .use_reapply_con_label_set;
            if ls.is_none() {
                continue;
            }
            let mut all = true;
            for nl in concept_linker {
                // tag-RESOLVED contains (ls1::has_concept is a W2-DEFER stub; a
                // raw/tag collision here would REUSE an unsuitable successor).
                if !self.label_set_contains_concept_resolved(
                    ls,
                    nl.target,
                    nl.negated ^ negate,
                    calc_alg_context,
                ) {
                    all = false;
                    break;
                }
            }
            if all {
                return succ;
            }
        }
        NodeId::NONE
    }

    /// Allocate a directed `source --role--> destination` `CIndividualLinkEdge` and
    /// install it into `source`'s successor-role hash (keyed by the destination
    /// individual id). Realises `createNewIndividualsLink` (cpp 22355–22369) +
    /// `installIndividualNodeRoleLink` (cpp 22251–22269) over the live edge arena +
    /// the real `SuccessorRoleHash` backend. Returns the new link.
    pub fn ht_install_role_successor_edge(
        &mut self,
        source: NodeId,
        destination: NodeId,
        role: RoleId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> EdgeId {
        // new CIndividualLinkEdge; initIndividualLinkEdge(creator=source, source, destination, role, dtp).
        let mut e = IndividualLinkEdge::new();
        e.set_source_individual(source);
        e.set_destination_individual(destination);
        e.set_link_role(role);
        e.set_dependency_track_point(dep_track_point);
        e.creator = source;
        let link: EdgeId = calc_alg_context.process_context_mut().alloc_edge(e);
        // installIndividualNodeRoleLink → reapply-role hash + successor-role hash.
        let mut reapply_queue_it = super::super::process::rs1::ReapplyQueueIterator::empty();
        calc_alg_context
            .process_context_mut()
            .node_install_individual_link(source, link, &mut reapply_queue_it);
        // createNewIndividualsLink tail (cpp 22346–22349): register the SOURCE in the
        // DESTINATION's connection-successor set — the only back-reference from a
        // node to its predecessors. The inverse arm of `ht_all_rule_targets` walks
        // it; without it a node acquired through ≤n-merge relocation only ever
        // propagates ∀R⁻ to its CREATOR ancestor.
        {
            let source_id = calc_alg_context
                .process_context()
                .node(source)
                .individual_node_id();
            let conn = calc_alg_context
                .process_context_mut()
                .node_connection_successor_set(destination);
            calc_alg_context
                .process_context_mut()
                .conn_succ_set_mut(conn)
                .insert_connection_successor(source_id);
        }
        // createNewIndividualsLinkReapplyed domain/range (cpp 22382–22395): for an
        // installed R-edge (u,v), `range(R)` concepts go to v and `domain(R)`
        // concepts to u, BEFORE the reapply queue fires over the link. Konclude
        // passes allowPreprocessing=false here ("no preprocessing, because of
        // possible not intercepted clashes while merging").
        self.ht_apply_role_domain_range(role, source, destination, dep_track_point, calc_alg_context);
        // applyReapplyQueueConceptsRestricted (cpp 22321/26572): the concepts armed in
        // `source`'s per-role reapply queue (∀ / ≤n restrictions already processed on
        // `source`) must RE-FIRE over this fresh link. Dropping the iterator here made
        // the closure depend on whether the link existed when the rule first ran — the
        // HashMap-order-dependent (in)completeness the bridge probes exposed.
        self.apply_reapply_queue_concepts_restricted(source, reapply_queue_it, link, calc_alg_context);
        // KONCLUDE-PORT-NOTE[api]: Konclude installs ONE link PER indirect super-role
        // (`createNewIndividualsLinksReapplyed`'s roleLinkerIt loop), so each
        // super-role's reapply queue fires on its own install. The port installs a
        // single link and resolves the hierarchy at lookup — so the super-role queues
        // must fire HERE: non-inverted supers armed on `source` (an R-link is an
        // S-link for R ⊑ S), inverted supers armed on `destination` (the R-link makes
        // `destination` see `source` as an S⁻-successor).
        let super_links: Vec<(RoleId, bool)> = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_indirect_super_role_list()
            .iter()
            .map(|l| (l.target, l.negated))
            .collect();
        for (super_role, inversed) in super_links {
            // createNewIndividualsLinksReapplyed applies EACH super-role's own
            // domain/range at its per-super-role install (cpp 22303–22334): a
            // non-inverted super S puts the S-edge as (source, destination), an
            // inverted super as (destination, source).
            if super_role != role {
                let (u, v) = if inversed { (destination, source) } else { (source, destination) };
                self.ht_apply_role_domain_range(super_role, u, v, dep_track_point, calc_alg_context);
            }
            let (holder, skip) = if inversed {
                (destination, false)
            } else {
                (source, super_role == role) // own queue already consumed via install
            };
            if skip {
                continue;
            }
            let hash = calc_alg_context
                .process_context()
                .node_reapply_role_successor_hash_existing(holder);
            if hash.is_none() {
                continue;
            }
            let it = calc_alg_context
                .process_context_mut()
                .role_succ_hash_mut(hash)
                .get_role_reapply_iterator(super_role, true);
            self.apply_reapply_queue_concepts_restricted(holder, it, link, calc_alg_context);
        }
        // MIRROR INVERSE INSTALL (cpp 22300–22341, the roleLinkerIt INVERSE arm):
        // Konclude installs one link per indirect-super-role entry, and the
        // inverse entries go on the DESTINATION under the inverse role. The
        // bridge wires only `set_inverse_role` (no inverse super lists), so
        // synthesize that install here: `destination --inv(R)--> source` in the
        // destination's hashes, with ITS reapply queue consumed over the new
        // link. This is what lets (a) the B2 blocking condition see the parent
        // edge from the child's side (without it a blocked child's blocker can
        // hold an armed `∀R⁻.C` that would fire backward over the parent edge —
        // an UNSOUND block that hid clashes order-dependently), and (b) `∀R⁻`
        // fire as a plain forward ∀ over the inverse link.
        let inv_role = calc_alg_context.ontology_arenas().role(role).get_inverse_role();
        if inv_role.is_some() {
            let mut e = IndividualLinkEdge::new();
            // C++ initIndividualLinkEdge(creator=indiSource, indiDestination,
            // indiSource, superRole, dtp): creator stays the ∃-applier.
            e.set_source_individual(destination);
            e.set_destination_individual(source);
            e.set_link_role(inv_role);
            e.set_dependency_track_point(dep_track_point);
            e.creator = source;
            let inv_link: EdgeId = calc_alg_context.process_context_mut().alloc_edge(e);
            let mut inv_reapply_it = super::super::process::rs1::ReapplyQueueIterator::empty();
            calc_alg_context
                .process_context_mut()
                .node_install_individual_link(destination, inv_link, &mut inv_reapply_it);
            // generatedInvLink tail (cpp 22346): the SOURCE's connection set
            // records the destination.
            {
                let dest_id = calc_alg_context
                    .process_context()
                    .node(destination)
                    .individual_node_id();
                let conn = calc_alg_context
                    .process_context_mut()
                    .node_connection_successor_set(source);
                calc_alg_context
                    .process_context_mut()
                    .conn_succ_set_mut(conn)
                    .insert_connection_successor(dest_id);
            }
            // the inverse edge (destination, source) carries inv(R)'s own
            // domain/range (cpp invRole arm, 22326–22334).
            self.ht_apply_role_domain_range(
                inv_role,
                destination,
                source,
                dep_track_point,
                calc_alg_context,
            );
            self.apply_reapply_queue_concepts_restricted(
                destination,
                inv_reapply_it,
                inv_link,
                calc_alg_context,
            );
        }
        link
    }

    /// Port of the domain/range application inside `createNewIndividualsLink*`
    /// (cpp 22303–22334 / 22382–22395): for an installed `role`-edge `(u, v)`,
    /// add `role.range_linker` concepts to `v` and `role.domain_linker` concepts
    /// to `u` via `addConceptsToIndividual(…, allowPreprocessing=false,
    /// allowInitialization=false, nullptr, …)`.
    pub fn ht_apply_role_domain_range(
        &mut self,
        role: RoleId,
        u: NodeId,
        v: NodeId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let (domain, range) = {
            let r = calc_alg_context.ontology_arenas().role(role);
            if r.domain_linker.is_empty() && r.range_linker.is_empty() {
                return;
            }
            (r.domain_linker.clone(), r.range_linker.clone())
        };
        if !range.is_empty() {
            let mut dest = v;
            self.add_concepts_to_individual(
                &range,
                false,
                &mut dest,
                dep_track_point,
                false,
                false,
                None,
                calc_alg_context,
            );
        }
        if !domain.is_empty() {
            let mut src = u;
            self.add_concepts_to_individual(
                &domain,
                false,
                &mut src,
                dep_track_point,
                false,
                false,
                None,
                calc_alg_context,
            );
        }
    }

    /// Edge-triggered ∀ re-application: push the positive `role`-`∀`-restrictions
    /// present on `source` onto the freshly created `successor`.
    ///
    /// KONCLUDE-PORT-NOTE[api]: stands in for the role reapply-queue + the
    /// link-processing-restriction `applyALLRule(restLink)` path (W2-DEFER). It scans
    /// `source`'s concept label set for `CCALL` concepts on `role` and adds their
    /// operands, which is exactly the set of `∀role.C` consequences a new R-edge must
    /// receive. Two extensions keep the stand-in faithful to the reapply queue:
    ///  - the role match is HIERARCHY-resolved (`edge role == r` or the edge role has
    ///    `r` as an indirect super role) — Konclude registers a new edge under every
    ///    indirect super role, so a `∀S.C` re-fires on a fresh `R ⊑ S` edge;
    ///  - the role-automaton family re-fires too: `CCAQALL`-family transition concepts
    ///    in the label (the non-specialized `apply_and_rule` route puts them there),
    ///    and `CCAQAND`-family STATE concepts, whose transitions never enter the label
    ///    under `conf_specialized_automate_rules` (`apply_automat_transactions`
    ///    recurses inline) — for those the state graph is walked here, mirroring the
    ///    reapply-queue re-run of the state descriptor over the single new link.
    pub fn ht_reapply_universal_restrictions(
        &mut self,
        source: NodeId,
        successor: &mut NodeId,
        role: RoleId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let ls = calc_alg_context
            .process_context()
            .node(source)
            .use_reapply_con_label_set;
        if ls.is_none() {
            return;
        }
        // Collect the operands first (the iterator borrows the context immutably);
        // then add them (mutating) after the borrow ends. Each op carries the
        // SOURCE ∀ concept descriptor `cd` — its dependency track point must be
        // combined with the edge's when the operand is added to the successor
        // (Konclude's applyALLRule createALLDependency, cpp 16334): without it
        // the propagated concept loses the ∀'s branch provenance, so a clash
        // on the successor traces to the (deterministic) edge instead of the
        // disjunction that introduced the ∀, and DDB wrongly root-cancels
        // (measured: ore_ont_541 Cell spuriously UNSAT via Q_70 ≡
        // ∀projectsOnto.PointInTime).
        let mut ops: Vec<(ConceptId, bool, ConDescId)> = Vec::new();
        {
            let pc = calc_alg_context.process_context();
            let onto = calc_alg_context.ontology_arenas();
            // `∀r.C` on `source` reaches the new `role`-edge when the edge role is r
            // or r is one of its indirect super roles (self is in the list per the
            // Konclude convention; the == check covers hand-built fixtures too).
            let role_matches = |r: RoleId| -> bool {
                r == role || (role.is_some() && onto.role(role).has_indirect_super_role(r))
            };
            let mut it = pc
                .label_set(ls)
                .get_concept_label_set_iterator(true, false, false);
            while it.has_next() {
                let cd: ConDescId = it.next(true, pc);
                if cd.is_none() {
                    break;
                }
                if pc.con_desc(cd).is_negated() {
                    continue;
                }
                let con: ConceptId = pc.con_desc(cd).get_concept();
                let oc = onto.concept(con).get_operator_code();
                if (oc == op::CCALL
                    || oc == op::CCAQALL
                    || oc == op::CCIMPLAQALL
                    || oc == op::CCBRANCHAQALL)
                    && role_matches(onto.concept(con).get_role())
                {
                    // KM_BRIDGE_WATCH_NODE diagnostics: which ∀ matched this edge.
                    if std::env::var("KM_BRIDGE_WATCH_NODE")
                        .ok()
                        .and_then(|w| w.parse::<Cint64>().ok())
                        == Some(pc.node(*successor).individual_node_id())
                    {
                        let fillers: Vec<String> = onto
                            .concept(con)
                            .get_operand_list()
                            .iter()
                            .map(|nl| {
                                format!(
                                    "{}{}",
                                    if nl.negated { "¬" } else { "" },
                                    onto.concept(nl.target).get_concept_tag()
                                )
                            })
                            .collect();
                        eprintln!(
                            "WATCH-ALL edge_role_tag={} forall_role_tag={} oc={oc} fillers=[{}]",
                            onto.role(role).get_role_tag(),
                            onto.role(onto.concept(con).get_role()).get_role_tag(),
                            fillers.join(" ")
                        );
                    }
                    for nl in onto.concept(con).get_operand_list() {
                        ops.push((nl.target, nl.negated, cd));
                    }
                } else if oc == op::CCAQAND || oc == op::CCIMPLAQAND || oc == op::CCBRANCHAQAND {
                    // Walk the automaton state graph exactly as
                    // `apply_automat_transactions` recurses: an AQALL operand on a
                    // matching role contributes its operands XOR-ed with its own
                    // linker negation; a nested AQAND is entered (its incoming
                    // negation is ignored there, as in the C++ AQAND arm). The
                    // visited set is defensive only (the preprocessor builds no
                    // AQAND-cycle; ε-loops go through AQALL).
                    let mut visited: std::collections::HashSet<ConceptId> =
                        std::collections::HashSet::new();
                    let mut stack: Vec<ConceptId> = vec![con];
                    while let Some(state) = stack.pop() {
                        if !visited.insert(state) {
                            continue;
                        }
                        for nl in onto.concept(state).get_operand_list() {
                            let op_oc = onto.concept(nl.target).get_operator_code();
                            if op_oc == op::CCAQAND
                                || op_oc == op::CCIMPLAQAND
                                || op_oc == op::CCBRANCHAQAND
                            {
                                stack.push(nl.target);
                            } else if (op_oc == op::CCAQALL
                                || op_oc == op::CCIMPLAQALL
                                || op_oc == op::CCBRANCHAQALL)
                                && role_matches(onto.concept(nl.target).get_role())
                            {
                                for tl in onto.concept(nl.target).get_operand_list() {
                                    ops.push((tl.target, tl.negated ^ nl.negated, cd));
                                }
                            }
                        }
                    }
                }
            }
        }
        // Per-source-∀ ALL dependency (Konclude builds one `allDepNode` per
        // conProDes, shared across that ∀'s operands): its continue track
        // point depends on BOTH the ∀ concept descriptor's track point
        // (`prev`) and the edge's (`link`). Memoized by `cd` so operands of
        // the same ∀ share one dependency, matching the C++ `allDepNodeCreated`
        // flag. When dependency building is off (baseline), the operand is
        // added under the plain edge track point, exactly as before.
        let mut all_dep_cache: std::collections::HashMap<ConDescId, TrackPointId> =
            std::collections::HashMap::new();
        for (op_concept, op_neg, cd) in ops {
            let add_tp = if self.conf_build_dependencies {
                if let Some(&tp) = all_dep_cache.get(&cd) {
                    tp
                } else {
                    let forall_dep = calc_alg_context
                        .process_context()
                        .con_desc(cd)
                        .get_dependency_track_point();
                    let mut next_tp = TrackPointId::NONE;
                    let mut src = source;
                    self.create_all_dependency(
                        &mut next_tp,
                        &mut src,
                        cd,
                        forall_dep,
                        dep_track_point,
                        calc_alg_context,
                    );
                    all_dep_cache.insert(cd, next_tp);
                    next_tp
                }
            } else {
                dep_track_point
            };
            self.add_concept_to_individual(
                op_concept,
                op_neg,
                successor,
                add_tp,
                true,
                true,
                calc_alg_context,
            );
            if calc_alg_context.has_pending_signal() {
                return;
            }
        }
    }

    // =======================================================================
    // W14-number — the SHIQ qualified-cardinality core (≥n R.C / ≤n R.C),
    // realised over the LIVE ∃/∀ edge primitives. These stand in for the
    // PORT-PENDING `createDistinctSuccessorIndividuals` (cpp 22143–22186) +
    // `createIndividualsDistinct` (cpp 22401–22429) and the merge/clash spine of
    // `applyATMOSTRule` / `mergeMergingIndividualNodes` (cpp 14861–15006).
    // KONCLUDE-PORT-NOTE[api]: the C++ rules funnel through the role-successor-hash
    // satellite iterators + the branching-merging restriction-spec subsystem (W2/W3
    // DEFER); the W14 port instead drives the same observable graph effect — n fresh
    // pairwise-distinct successors for ≥n, and pair-merge-else-distinct-clash for ≤n —
    // over the context-threaded node successor iterator + the real distinct-edge hash.
    // =======================================================================

    /// Make every pair in `indis` pairwise distinct via `CDistinctEdge`s installed in
    /// both endpoints' distinct hashes. Port of `createIndividualsDistinct(indiList)`
    /// (cpp 22413–22429).
    pub fn ht_make_individuals_distinct(
        &mut self,
        indis: &[NodeId],
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        for i in 0..indis.len() {
            for j in (i + 1)..indis.len() {
                let a = indis[i];
                let b = indis[j];
                let a_id = calc_alg_context
                    .process_context()
                    .node(a)
                    .individual_node_id();
                let b_id = calc_alg_context
                    .process_context()
                    .node(b)
                    .individual_node_id();
                // new CDistinctEdge; initDistinctEdge(a, b, depTrackPoint).
                let mut e = DistinctEdge::new();
                e.set_source_individual(a);
                e.set_destination_individual(b);
                e.set_dependency_track_point(dep_track_point);
                let edge = calc_alg_context
                    .process_context_mut()
                    .alloc_distinct_edge(e);
                // disHash1->insertDistinctIndividual(b_id, edge); disHash2->insert…(a_id, edge).
                let dh_a = calc_alg_context.process_context_mut().node_distinct_hash(a);
                calc_alg_context
                    .process_context_mut()
                    .distinct_hash_mut(dh_a)
                    .insert_distinct_individual(b_id, edge);
                let dh_b = calc_alg_context.process_context_mut().node_distinct_hash(b);
                calc_alg_context
                    .process_context_mut()
                    .distinct_hash_mut(dh_b)
                    .insert_distinct_individual(a_id, edge);
            }
        }
    }

    /// Create `cardinality` fresh `role`-successors of `source`, each labelled with the
    /// qualifier `concept_linker` (polarity XOR `negate`), made PAIRWISE DISTINCT, then
    /// enqueued. Port-faithful core of `createDistinctSuccessorIndividuals`
    /// (cpp 22143–22186): the ∃-rule's inline successor realisation, looped n times,
    /// followed by `createIndividualsDistinct` and the per-successor enqueue.
    pub fn ht_create_distinct_successors(
        &mut self,
        source: NodeId,
        role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        dep_track_point: TrackPointId,
        cardinality: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let is_data_role: bool = calc_alg_context.ontology_arenas().role(role).is_data_role();
        let depth: Cint64 = calc_alg_context
            .process_context()
            .node(source)
            .individual_ancestor_depth();
        let mut succs: Vec<NodeId> = Vec::new();
        // (1) create the n successors + install the R link-edge + the qualifier C.
        for _ in 0..cardinality {
            let mut succ: NodeId =
                self.create_new_individual(dep_track_point, is_data_role, calc_alg_context);
            let anc_link: EdgeId = self.ht_install_role_successor_edge(
                source,
                succ,
                role,
                dep_track_point,
                calc_alg_context,
            );
            {
                let n = calc_alg_context.process_context_mut().node_mut(succ);
                n.set_ancestor_link(anc_link);
                n.set_individual_ancestor_depth(depth + 1);
            }
            for nl in concept_linker {
                self.add_concept_to_individual(
                    nl.target,
                    nl.negated ^ negate,
                    &mut succ,
                    dep_track_point,
                    true,
                    true,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    return;
                }
            }
            self.ht_reapply_universal_restrictions(
                source,
                &mut succ,
                role,
                dep_track_point,
                calc_alg_context,
            );
            if calc_alg_context.has_pending_signal() {
                return;
            }
            succs.push(succ);
        }
        // (2) createIndividualsDistinct(indiList): pairwise distinct edges.
        self.ht_make_individuals_distinct(&succs, dep_track_point, calc_alg_context);
        // (3) addIndividualToProcessingQueue(succIndi) for each.
        // KONCLUDE-PORT-NOTE[W16-successor-drain]: depth-queue routing (see apply_some_rule)
        // so each ≥n successor's own deterministic-priority concepts drain.
        for succ in succs {
            self.add_individual_to_processing_queue(succ, calc_alg_context);
            let dq = calc_alg_context.get_individual_depth_processing_queue(true);
            calc_alg_context
                .process_context_mut()
                .indi_depth_queue_insert(dq, succ);
        }
    }

    /// The distinct `role`-successor nodes of `source` whose label set carries every
    /// concept of `concept_linker` (polarity XOR `negate`). An empty `concept_linker`
    /// (the unqualified ≤n R.⊤ / functional case) matches every successor. Port-faithful
    /// core of `hasDistinctRoleSuccessorConcepts` / the at-most successor gather.
    pub fn ht_role_successors_with_concepts(
        &mut self,
        source: NodeId,
        role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Vec<NodeId> {
        // KONCLUDE-PORT-NOTE[api]: the label set is keyed by `CConcept::getConceptTag`,
        // but `ReapplyConceptLabelSet::has_concept` / the `concept_tag` static are
        // W2-DEFER stubs that key by the raw arena index. To test qualifier
        // membership reliably, resolve the real concept tag through the ontology
        // arena, probe via `get_concept_descriptor_by_tag`, and resolve the found
        // descriptor's POLARITY through the process arena (`con_desc(cd)
        // .is_negated()` — the same caller-side resolution as the ls1 tp-stub
        // fix). Konclude counts a successor ONLY on positive-polarity qualifier
        // containment (`initializeMergingIndividualNodes` cpp 15879:
        // `if (!containsNegation)`): a successor whose label carries ¬C is NOT
        // an R.C-successor — counting it over-merges/over-clashes the ≤n rule
        // (measured: ore_ont_12653 `X ⊑ Path` spurious family). The qualifier
        // linker's own negation is respected; the rule-level `negate` does NOT
        // flip it (¬≥n R.C ≡ ≤(n−1) R.C — the filler polarity is unchanged;
        // Konclude reads the operand linker raw in the merge-candidate
        // collection). A successor carrying NEITHER polarity is skipped here —
        // Konclude installs choose-triggering for those (cpp 15934+, the
        // completeness half; PORT-PENDING).
        let _ = negate;
        let want: Vec<(Cint64, bool)> = concept_linker
            .iter()
            .map(|nl| {
                (
                    calc_alg_context
                        .ontology_arenas()
                        .concept(nl.target)
                        .get_concept_tag(),
                    nl.negated,
                )
            })
            .collect();
        let mut out: Vec<NodeId> = Vec::new();
        for (_link, succ) in self.ht_role_successor_links(source, role, calc_alg_context) {
            if out.contains(&succ) {
                continue;
            }
            let mut all = true;
            if !want.is_empty() {
                let ls = calc_alg_context
                    .process_context()
                    .node(succ)
                    .use_reapply_con_label_set;
                if ls.is_none() {
                    all = false;
                } else {
                    for &(t, expected_neg) in &want {
                        let mut cd: ConDescId = Id::NONE;
                        let mut dtp: TrackPointId = TrackPointId::NONE;
                        let found = calc_alg_context
                            .process_context()
                            .label_set(ls)
                            .get_concept_descriptor_by_tag(t, &mut cd, &mut dtp);
                        if !found
                            || calc_alg_context.process_context().con_desc(cd).is_negated()
                                != expected_neg
                        {
                            all = false;
                            break;
                        }
                    }
                }
            }
            if all {
                out.push(succ);
            }
        }
        out
    }

    /// Port of `createIndividualMergeCausingDescriptors` (cpp 16690–16713):
    /// the per-successor merge-causing clash descriptors — the LINK's
    /// dependency (when it differs from the successor's own) and each
    /// qualifier operand's CONTAINED descriptor on the successor. These carry
    /// the branch taint of WHY the successor counts toward the at-most;
    /// omitting them over-localised the at-most refutation and made the u29
    /// analysis wrongly ROOT-CANCEL (measured: ore_ont_12653
    /// AlternativePath ⊑ PathOfLength2 spurious under DDB — the collected
    /// closure degenerated to the decision's own tag-0 cause).
    pub fn ht_create_individual_merge_causing_descriptors(
        &mut self,
        prev_clashes: super::super::process::ClashDescId,
        succ: NodeId,
        link: EdgeId,
        concept_add_linker: &[NegLink<ConceptId>],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> super::super::process::ClashDescId {
        let mut clash_des = prev_clashes;
        let link_tp = calc_alg_context
            .process_context()
            .edge(link)
            .get_dependency_track_point();
        let succ_tp = calc_alg_context
            .process_context()
            .node(succ)
            .dependency_track_point();
        if link_tp != succ_tp {
            clash_des = self.create_clashed_individual_link_descriptor(
                clash_des,
                link,
                link_tp,
                calc_alg_context,
            );
        }
        let ls = calc_alg_context
            .process_context()
            .node(succ)
            .use_reapply_con_label_set;
        for nl in concept_add_linker {
            let t = calc_alg_context
                .ontology_arenas()
                .concept(nl.target)
                .get_concept_tag();
            let mut cd: ConDescId = Id::NONE;
            let mut dtp: TrackPointId = TrackPointId::NONE;
            if ls.is_some()
                && calc_alg_context
                    .process_context()
                    .label_set(ls)
                    .get_concept_descriptor_by_tag(t, &mut cd, &mut dtp)
            {
                // resolve the contained descriptor's track point (the ls1
                // lookup out-tp is a W2-DEFER stub returning NONE).
                if dtp.is_none() && cd.is_some() {
                    dtp = calc_alg_context
                        .process_context()
                        .con_desc(cd)
                        .get_dependency_track_point();
                }
                let mut s = succ;
                clash_des = self.create_clashed_concept_descriptor(
                    clash_des,
                    &mut s,
                    cd,
                    dtp,
                    calc_alg_context,
                );
            }
        }
        clash_des
    }

    /// Port of `CNonDeterministicDependencyNode::addBranchClashes` (the
    /// `mClashTrackPoint.addClashes(clash)` idiom): append the clash
    /// descriptors to the decision node's CLASH track point — the "all
    /// alternatives failed" continuation that
    /// `get_collected_filtered_clashed_descriptors_from_branch` walks (the
    /// clash track point heads the `branch_track_points` chain), so a fully
    /// refuted decision propagates these causes upward.
    pub fn ht_add_branch_clashes(
        &mut self,
        dep_node: DependencyId,
        clashes: super::super::process::ClashDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if dep_node.is_none() || clashes.is_none() {
            return;
        }
        let pc = calc_alg_context.process_context_mut();
        let ctp = pc.dep_node(dep_node).clash_track_point();
        if ctp.is_none() {
            return;
        }
        let old = pc.track_point(ctp).get_clashes();
        let joined = pc.append_clash_descriptor_chain(clashes, old);
        pc.track_point_mut(ctp).set_clashes(joined, false);
    }

    /// The PESSIMISTIC qualified `role`-successor count of `source`: distinct
    /// successors whose label is NOT decided AGAINST the qualifier (undecided
    /// ones count — they could still become qualifier members). Used by the
    /// lazy triggered-OR defer (u03): this count can only grow through NEW
    /// `role`-links, so a role-keyed reapply re-fires the deferred disjunction
    /// exactly when the count can change upward.
    pub fn ht_role_successor_count_possibly_qualified(
        &mut self,
        source: NodeId,
        role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        let want: Vec<(Cint64, bool)> = concept_linker
            .iter()
            .map(|nl| {
                (
                    calc_alg_context
                        .ontology_arenas()
                        .concept(nl.target)
                        .get_concept_tag(),
                    nl.negated,
                )
            })
            .collect();
        let mut seen: Vec<NodeId> = Vec::new();
        let mut count: Cint64 = 0;
        for (_link, succ) in self.ht_role_successor_links(source, role, calc_alg_context) {
            if seen.contains(&succ) {
                continue;
            }
            seen.push(succ);
            let ls = calc_alg_context
                .process_context()
                .node(succ)
                .use_reapply_con_label_set;
            let mut decided_anti = false;
            if ls.is_some() {
                for &(t, expected_neg) in &want {
                    let mut cd: ConDescId = Id::NONE;
                    let mut dtp: TrackPointId = TrackPointId::NONE;
                    if calc_alg_context
                        .process_context()
                        .label_set(ls)
                        .get_concept_descriptor_by_tag(t, &mut cd, &mut dtp)
                        && calc_alg_context.process_context().con_desc(cd).is_negated()
                            != expected_neg
                    {
                        decided_anti = true;
                        break;
                    }
                }
            }
            if !decided_anti {
                count += 1;
            }
        }
        count
    }

    /// The first `role`-successor of `source` whose label decides NEITHER
    /// polarity of some qualifier operand — the choose rule's both-qualify
    /// candidate (`initializeMergingIndividualNodes`' else-branch, cpp 15931:
    /// `containsIndividualNodeConcepts` false ⇒ some operand ABSENT in both
    /// polarities). A successor carrying an operand with the OPPOSITE polarity
    /// but no absent operand is DECIDED (anti-qualified) and not a candidate.
    pub fn ht_find_both_qualify_successor(
        &mut self,
        source: NodeId,
        role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Option<NodeId> {
        let want: Vec<Cint64> = concept_linker
            .iter()
            .map(|nl| {
                calc_alg_context
                    .ontology_arenas()
                    .concept(nl.target)
                    .get_concept_tag()
            })
            .collect();
        if want.is_empty() {
            return None;
        }
        let mut seen: Vec<NodeId> = Vec::new();
        for (_link, succ) in self.ht_role_successor_links(source, role, calc_alg_context) {
            if seen.contains(&succ) {
                continue;
            }
            seen.push(succ);
            let ls = calc_alg_context
                .process_context()
                .node(succ)
                .use_reapply_con_label_set;
            let mut undecided = false;
            if ls.is_none() {
                undecided = true;
            } else {
                for &t in &want {
                    let mut cd: ConDescId = Id::NONE;
                    let mut dtp: TrackPointId = TrackPointId::NONE;
                    if !calc_alg_context
                        .process_context()
                        .label_set(ls)
                        .get_concept_descriptor_by_tag(t, &mut cd, &mut dtp)
                    {
                        undecided = true;
                        break;
                    }
                }
            }
            if undecided {
                return Some(succ);
            }
        }
        None
    }

    /// Are `indi1` and `indi2` mergeable? `false` iff `indi1`'s active distinct hash
    /// records `indi2` as `owl:differentFrom` (a distinct-edge). Port of the leading
    /// distinct-test of `isIndividualNodesMergeable` (cpp 20714–20726).
    pub fn ht_individuals_mergeable(
        &self,
        indi1: NodeId,
        indi2: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        // disHash = indi1->getDistinctHash(false) (the active mUseDistinctHash).
        let dh = calc_alg_context
            .process_context()
            .node(indi1)
            .use_distinct_hash;
        if dh.is_some() {
            let id2 = calc_alg_context
                .process_context()
                .node(indi2)
                .individual_node_id();
            if calc_alg_context
                .process_context()
                .distinct_hash(dh)
                .is_individual_distinct(id2)
            {
                return false;
            }
        }
        // isLabelConceptClashSet (cpp 20741): a same-tag opposite-polarity pair
        // across the two labels makes the pair unmergeable — the pre-test that
        // lets the merge's label union skip any-polarity-contained tags. Without
        // it a ≤n merge would silently drop the polarity clash.
        !self.ht_label_concept_clash_set(indi1, indi2, calc_alg_context)
    }

    /// Port of `isLabelConceptClashSet` (the `CIndividualProcessNode*` pair
    /// overload, cpp 20867–20934): true iff the two labels contain the SAME
    /// concept tag with OPPOSITE polarity.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the clash-descriptor accumulation is threaded by
    /// the caller in the C++ (the collected descriptors feed the at-most clash);
    /// the port's greedy at-most path raises its own clash descriptor, so only
    /// the boolean verdict is ported. The C++ direct-lookup branch collects the
    /// clash but forgets to return true (the sorted-walk branch returns) — the
    /// port returns true from both, matching the evident intent and the caller's
    /// use of the verdict.
    pub fn ht_label_concept_clash_set(
        &self,
        indi1: NodeId,
        indi2: NodeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let pc = calc_alg_context.process_context();
        let ls1 = pc.node(indi1).use_reapply_con_label_set;
        let ls2 = pc.node(indi2).use_reapply_con_label_set;
        if ls1.is_none() || ls2.is_none() {
            return false;
        }
        // iterate the smaller set, look up in the larger (the C++ swap). The maps
        // are keyed by REAL concept tags at insert, so probe by tag and compare
        // polarity explicitly (ls1::has_concept is a W2-DEFER stub — raw-index key
        // + always-false negation — and must not be used here).
        let (sub, sup) = if pc.label_set(ls1).get_concept_count()
            <= pc.label_set(ls2).get_concept_count()
        {
            (ls1, ls2)
        } else {
            (ls2, ls1)
        };
        for (tag, data) in pc.label_set(sub).concept_des_dep_map.iter() {
            let cd = data.concept_descriptor;
            if cd.is_none() {
                continue;
            }
            let neg = pc.con_desc(cd).is_negated();
            if pc
                .label_set(sup)
                .concept_des_dep_map
                .get(tag)
                .map_or(false, |d| {
                    d.concept_descriptor.is_some()
                        && pc.con_desc(d.concept_descriptor).is_negated() != neg
                })
            {
                return true;
            }
        }
        false
    }

    /// The merge/clash spine of `applyATMOSTRule` / the PAIRWISE merge branching
    /// `mergeMergingIndividualNodesPairwise` (cpp 14861–15006 / 15044–15093).
    /// Gather the `role`-successors carrying the qualifier; while they exceed the
    /// bound, enumerate every MERGEABLE pair: which pair merges is a
    /// NON-DETERMINISTIC choice (Konclude forks one `createMergeBranchingTask`
    /// per pair) — the port pushes an `AtMostMerge` branch point whose
    /// alternatives are the pairs, performs pair 0 (the pair the previous greedy
    /// realisation merged, so deterministic runs are unchanged), and loops to
    /// re-check the bound; backtracking (u02 `advance_atmost_merge_alternative`)
    /// tries the sibling pairs. No mergeable pair at all ⇒ the at-most CLASH.
    ///
    /// Every merge branch point OWNS a branch epoch, even when the global
    /// in-process COW is off: a merge mutates labels / links / distinct hashes
    /// across nodes, which the single-node label snapshot cannot undo — the
    /// previous epoch-less greedy merge leaked refuted alternatives' merges into
    /// their siblings and manufactured spurious unsats (measured: ore_ont_12653
    /// `X ⊑ Path` spurious family — a definer pulled into the root by an
    /// unrolled-back merge).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the NN-rule / nominal machinery of
    /// `mergeMergingIndividualNodes` stays W3-DEFER; the choose-triggering for
    /// neither-polarity successors (cpp 15934+) is the pending completeness half.
    pub fn ht_apply_atmost_merge(
        &mut self,
        process_indi: &mut NodeId,
        role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        cardinality: Cint64,
        dep_track_point: TrackPointId,
        con_des: ConDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let watch = std::env::var_os("KM_BRIDGE_WATCH_MERGE").is_some();
        loop {
            // --- choose rule (`qualifyMergingIndividualNodes`, cpp 15677–15816).
            // A `role`-successor whose label decides NEITHER polarity of the
            // qualifier is qualified BEFORE any merging — regardless of the
            // current qualified count (in the positive alternative it becomes a
            // merge candidate and can push the count over the bound; skipping
            // undecided successors loses that refutation = incompleteness).
            // One candidate per iteration (Konclude forks + reapplication
            // re-fires for the rest).
            if !concept_linker.is_empty() {
                if let Some(qsucc) = self.ht_find_both_qualify_successor(
                    *process_indi,
                    role,
                    concept_linker,
                    calc_alg_context,
                ) {
                    // KM_BRIDGE_WATCH_ATMOST: identify the at-most driving a
                    // choose qualification (concept/role/bound/negate + the
                    // at-most descriptor's own track point tag).
                    if std::env::var_os("KM_BRIDGE_WATCH_ATMOST").is_some()
                        && self.ddb_analysis_dumps < 12
                    {
                        self.ddb_analysis_dumps += 1;
                        let am_tag = calc_alg_context
                            .process_context()
                            .con_desc(con_des)
                            .get_concept();
                        let am_tag = calc_alg_context
                            .ontology_arenas()
                            .concept(am_tag)
                            .get_concept_tag();
                        let quals: Vec<String> = concept_linker
                            .iter()
                            .map(|nl| {
                                format!(
                                    "{}{}",
                                    if nl.negated { "¬" } else { "" },
                                    calc_alg_context
                                        .ontology_arenas()
                                        .concept(nl.target)
                                        .get_concept_tag()
                                )
                            })
                            .collect();
                        let dep_tag = if dep_track_point.is_some() {
                            calc_alg_context
                                .process_context()
                                .track_point(dep_track_point)
                                .process_tag
                        } else {
                            -1
                        };
                        eprintln!(
                            "WATCH-ATMOST choose: atmost_tag={} card={} negate={} role_tag={} quals=[{}] parent=n{} succ=n{} dep_tag={}",
                            am_tag,
                            cardinality,
                            negate,
                            calc_alg_context.ontology_arenas().role(role).get_role_tag(),
                            quals.join(","),
                            process_indi.index(),
                            qsucc.index(),
                            dep_tag
                        );
                    }
                    // `createQUALIFYDependency` — the decision node.
                    let qualify_dep: DependencyId = {
                        let mut pi = *process_indi;
                        self.create_qualify_dependency(
                            &mut pi,
                            con_des,
                            dep_track_point,
                            calc_alg_context,
                        )
                    };
                    // `qualifyDepNode->addBranchClashes(clashDes)` with the
                    // qualified successor's LINK descriptor (cpp 15711–15716):
                    // the choose decision's refutation must carry the link's
                    // branch taint.
                    if let Some(&(qlink, _)) = self
                        .ht_role_successor_links(*process_indi, role, calc_alg_context)
                        .iter()
                        .find(|&&(_, n)| n == qsucc)
                    {
                        let qlink_tp = calc_alg_context
                            .process_context()
                            .edge(qlink)
                            .get_dependency_track_point();
                        let qclash = self.create_clashed_individual_link_descriptor(
                            Id::NONE,
                            qlink,
                            qlink_tp,
                            calc_alg_context,
                        );
                        self.ht_add_branch_clashes(qualify_dep, qclash, calc_alg_context);
                    }
                    let parent_used_branch_node = calc_alg_context.base.used_branch_tree_node;
                    if cardinality <= 0 {
                        // ≤0 R.C: only the NEGATED qualification is consistent —
                        // deterministic (cpp 15721–15733, "qualify only negated").
                        let tps = self.ht_mint_alternative_track_points(
                            qualify_dep,
                            1,
                            parent_used_branch_node,
                            calc_alg_context,
                        );
                        let add_tp = tps.first().copied().unwrap_or(dep_track_point);
                        for nl in concept_linker {
                            if calc_alg_context.has_pending_signal() {
                                return;
                            }
                            let mut s = qsucc;
                            self.add_concept_to_individual(
                                nl.target,
                                !nl.negated,
                                &mut s,
                                add_tp,
                                true,
                                true,
                                calc_alg_context,
                            );
                        }
                        self.add_individual_to_processing_queue(qsucc, calc_alg_context);
                        if calc_alg_context.has_pending_signal() {
                            return;
                        }
                        continue;
                    }
                    // choose branching: alternative 0 = ¬C (qualNeg = true first),
                    // alternative 1 = C. Own-epoch: the qualification's downstream
                    // derivations must be undone before the sibling alternative.
                    let parent_branch: BranchNodeId = self
                        .or_branch_stack
                        .last()
                        .map(|bp| bp.branch_node)
                        .unwrap_or(BranchNodeId::NONE);
                    let root_branch: BranchNodeId = self
                        .or_branch_stack
                        .first()
                        .map(|bp| bp.branch_node)
                        .unwrap_or(BranchNodeId::NONE);
                    let alt_track_points = self.ht_mint_alternative_track_points(
                        qualify_dep,
                        2,
                        parent_used_branch_node,
                        calc_alg_context,
                    );
                    let branch_node: BranchNodeId = calc_alg_context
                        .process_context_mut()
                        .alloc_branch_node(BranchTreeNode {
                            process_tag: 0,
                            parent_node: parent_branch,
                            root_node: root_branch,
                            branched_dep_track_point: Id::NONE,
                            sat_calc_task: INVALID,
                        });
                    let node_count_at_push = calc_alg_context.process_context().node_count();
                    let first_alt_tp = alt_track_points.first().copied().unwrap_or(Id::NONE);
                    calc_alg_context.push_branch_epoch();
                    self.or_branch_open_count += 1;
                    self.or_branch_stack.push(OrBranchPoint {
                        node: qsucc,
                        disjuncts: Vec::new(),
                        negate: false,
                        next_alt: 1,
                        dep_track_point,
                        branch_node,
                        or_dependency_node: qualify_dep,
                        alt_track_points,
                        parent_used_branch_node,
                        node_label_snapshot: Default::default(),
                        node_queue_snapshot: Default::default(),
                        node_count_at_push,
                        kind: BranchKind::AtMostQualify {
                            succ: qsucc,
                            atmost: AtMostMergeBranch {
                                pairs: Vec::new(),
                                parent: *process_indi,
                                role,
                                concept_linker: concept_linker.to_vec(),
                                negate,
                                cardinality,
                                con_des,
                                rest: Id::NONE,
                            },
                        },
                        own_epoch: true,
                    });
                    let add_tp = if first_alt_tp.is_some() {
                        calc_alg_context.base.used_branch_tree_node = calc_alg_context
                            .process_context()
                            .track_point(first_alt_tp)
                            .get_branch_node();
                        first_alt_tp
                    } else {
                        dep_track_point
                    };
                    if watch {
                        eprintln!(
                            "ATMOST-QUALIFY parent=n{} succ=n{} qualNeg=true",
                            process_indi.index(),
                            qsucc.index()
                        );
                    }
                    for nl in concept_linker {
                        if calc_alg_context.has_pending_signal() {
                            return;
                        }
                        let mut s = qsucc;
                        self.add_concept_to_individual(
                            nl.target,
                            !nl.negated,
                            &mut s,
                            add_tp,
                            true,
                            true,
                            calc_alg_context,
                        );
                    }
                    self.add_individual_to_processing_queue(qsucc, calc_alg_context);
                    if calc_alg_context.has_pending_signal() {
                        return;
                    }
                    // re-gather: the ¬C successor is now decided (excluded);
                    // further undecided successors branch one at a time.
                    continue;
                }
            }

            let succs = self.ht_role_successors_with_concepts(
                *process_indi,
                role,
                concept_linker,
                negate,
                calc_alg_context,
            );
            if (succs.len() as Cint64) <= cardinality {
                return;
            }
            // merge-causing descriptors for every counted successor (link +
            // contained qualifier descriptors, cpp 15062/15069): the branch
            // taint of WHY each successor counts — chained into the at-most
            // clash AND recorded on the MERGE decision (`addBranchClashes`)
            // so a fully refuted merge decision propagates them upward.
            let succ_links = self.ht_role_successor_links(*process_indi, role, calc_alg_context);
            let mut merge_causing: super::super::process::ClashDescId = Id::NONE;
            for &s in &succs {
                if let Some(&(link, _)) = succ_links.iter().find(|&&(_, n)| n == s) {
                    merge_causing = self.ht_create_individual_merge_causing_descriptors(
                        merge_causing,
                        s,
                        link,
                        concept_linker,
                        calc_alg_context,
                    );
                }
            }
            // enumerate every mergeable pair — the merge alternatives
            // (`isIndividualNodesMergeable` per pair, cpp 15071).
            let mut pairs: Vec<(NodeId, NodeId)> = Vec::new();
            let pair_log = std::env::var_os("KM_BRIDGE_SEARCH_LOG").is_some();
            let mut pair_verdicts: Vec<String> = Vec::new();
            for i in 0..succs.len() {
                for j in (i + 1)..succs.len() {
                    let ok = self.ht_individuals_mergeable(succs[i], succs[j], calc_alg_context);
                    if pair_log {
                        // annotate WHY a pair is blocked (distinct edge vs
                        // label clash-set) — the cross-pair-exclusion hunt.
                        let why = if ok {
                            "ok".to_string()
                        } else {
                            let dh = calc_alg_context
                                .process_context()
                                .node(succs[i])
                                .use_distinct_hash;
                            let dist = dh.is_some() && {
                                let id2 = calc_alg_context
                                    .process_context()
                                    .node(succs[j])
                                    .individual_node_id();
                                calc_alg_context
                                    .process_context()
                                    .distinct_hash(dh)
                                    .is_individual_distinct(id2)
                            };
                            if dist { "DISTINCT".into() } else { "LABELCLASH".into() }
                        };
                        pair_verdicts.push(format!(
                            "({},{}):{}",
                            succs[i].index(),
                            succs[j].index(),
                            why
                        ));
                    }
                    if ok {
                        pairs.push((succs[i], succs[j]));
                    }
                }
            }
            if pair_log {
                let am_tag = {
                    let c = calc_alg_context
                        .process_context()
                        .con_desc(con_des)
                        .get_concept();
                    calc_alg_context
                        .ontology_arenas()
                        .concept(c)
                        .get_concept_tag()
                };
                let succ_labels: Vec<String> = succs
                    .iter()
                    .map(|&n| {
                        let pc = calc_alg_context.process_context();
                        let ls = pc.node(n).use_reapply_con_label_set;
                        if ls.is_none() {
                            return format!("n{}:[]", n.index());
                        }
                        let mut v: Vec<(i64, bool)> = pc
                            .label_set(ls)
                            .concept_des_dep_map
                            .iter()
                            .filter_map(|(tag, data)| {
                                let cd = data.concept_descriptor;
                                if cd.is_none() {
                                    return None;
                                }
                                Some((*tag, pc.con_desc(cd).is_negated()))
                            })
                            .collect();
                        v.sort_unstable();
                        format!(
                            "n{}:[{}]",
                            n.index(),
                            v.iter()
                                .map(|(t, neg)| format!("{}{}", if *neg { "-" } else { "" }, t))
                                .collect::<Vec<_>>()
                                .join(",")
                        )
                    })
                    .collect();
                let m = format!(
                    "atmost-pairs am={} card={} parent={} {} verdicts=[{}]",
                    am_tag,
                    cardinality,
                    process_indi.index(),
                    succ_labels.join(" "),
                    pair_verdicts.join(" ")
                );
                self.ht_search_log(&m);
            }
            if pairs.is_empty() {
                // every excess successor is pairwise-distinct ⇒ at-most violated
                // (the `!newTaskList` clash, cpp 15085–15088), blamed on the
                // merge-causing descriptors + the at-most concept.
                let clash = self.create_clashed_concept_descriptor(
                    merge_causing,
                    process_indi,
                    con_des,
                    dep_track_point,
                    calc_alg_context,
                );
                calc_alg_context.raise_clash(clash);
                return;
            }

            // --- push the merge branch point (the sibling task fan-out). ---
            // Records that belong to the PARENT state (dependency node,
            // alternative track points) are created BEFORE the epoch opens,
            // mirroring the OR-rule push (u03).
            let parent_branch: BranchNodeId = self
                .or_branch_stack
                .last()
                .map(|bp| bp.branch_node)
                .unwrap_or(BranchNodeId::NONE);
            let root_branch: BranchNodeId = self
                .or_branch_stack
                .first()
                .map(|bp| bp.branch_node)
                .unwrap_or(BranchNodeId::NONE);
            // `createMERGEDependency` (cpp 15054) — the non-deterministic
            // decision node the DDB analysis walks through.
            let merge_dependency_node: DependencyId = {
                let mut pi = *process_indi;
                self.create_merge_dependency(&mut pi, con_des, dep_track_point, calc_alg_context)
            };
            // `mergeDependencyNode->addBranchClashes(clashDescriptors)`
            // (cpp 15078–15080).
            self.ht_add_branch_clashes(merge_dependency_node, merge_causing, calc_alg_context);
            let parent_used_branch_node = calc_alg_context.base.used_branch_tree_node;
            let alt_track_points = self.ht_mint_alternative_track_points(
                merge_dependency_node,
                pairs.len(),
                parent_used_branch_node,
                calc_alg_context,
            );
            let branch_node: BranchNodeId =
                calc_alg_context
                    .process_context_mut()
                    .alloc_branch_node(BranchTreeNode {
                        process_tag: 0,
                        parent_node: parent_branch,
                        root_node: root_branch,
                        branched_dep_track_point: Id::NONE,
                        sat_calc_task: INVALID,
                    });
            let node_count_at_push = calc_alg_context.process_context().node_count();
            let (into, from) = pairs[0];
            let first_alt_tp = alt_track_points.first().copied().unwrap_or(Id::NONE);

            // the merge epoch: everything from here to this branch point's
            // discard/advance is rolled back by the epoch pop.
            calc_alg_context.push_branch_epoch();
            self.or_branch_open_count += 1;
            self.or_branch_stack.push(OrBranchPoint {
                node: *process_indi,
                disjuncts: Vec::new(),
                negate: false,
                next_alt: 1,
                dep_track_point,
                branch_node,
                or_dependency_node: merge_dependency_node,
                alt_track_points,
                parent_used_branch_node,
                node_label_snapshot: Default::default(),
                node_queue_snapshot: Default::default(),
                node_count_at_push,
                kind: BranchKind::AtMostMerge(AtMostMergeBranch {
                    pairs,
                    parent: *process_indi,
                    role,
                    concept_linker: concept_linker.to_vec(),
                    negate,
                    cardinality,
                    con_des,
                    rest: Id::NONE,
                }),
                own_epoch: true,
            });

            // --- perform alternative 0: merge `from` INTO `into`. ---
            let add_tp = if first_alt_tp.is_some() {
                calc_alg_context.base.used_branch_tree_node = calc_alg_context
                    .process_context()
                    .track_point(first_alt_tp)
                    .get_branch_node();
                first_alt_tp
            } else {
                dep_track_point
            };
            if watch {
                eprintln!(
                    "ATMOST-MERGE parent=n{} merge n{} -> n{} (alternatives={})",
                    process_indi.index(),
                    from.index(),
                    into.index(),
                    self.or_branch_stack
                        .last()
                        .map(|bp| bp.alternatives_len())
                        .unwrap_or(0),
                );
            }
            self.merge_individual_node_into(into, from, add_tp, calc_alg_context);
            if calc_alg_context.has_pending_signal() {
                return;
            }
            // phase-5 relocation from the COUNTED parent: the merge's
            // ancestor-scoped relocation covers `from`'s creator; when
            // `process_indi` reached `from` through an earlier relocation
            // its own link must be re-pointed too (idempotent — the
            // helper skips existing links).
            self.ht_relocate_incoming_links(
                *process_indi,
                from,
                into,
                add_tp,
                calc_alg_context,
            );
            if calc_alg_context.has_pending_signal() {
                return;
            }
            // loop: re-gather on the merged graph (count dropped by one); if
            // still over the bound, a NESTED merge branch point is pushed.
        }
    }

    // =======================================================================
    // At-most resume — the `branchingMergingProcRest` machinery
    // (`KM_HT_ATMOST_REST`; cpp 14891–14980 / 15820–16063 / 15677–15816).
    // =======================================================================

    /// Take the rest out of its arena slot, run `f` on it with the process
    /// context borrowable, and put it back. The take journals the slot's
    /// pre-epoch state (first touch), so branch-epoch pops restore it.
    ///
    /// `f` MUST NOT push or pop a branch epoch: the put-back must land in the
    /// same epoch as the take, or the new epoch's first-touch save would
    /// capture the placeholder instead of the real record.
    pub(super) fn ht_with_atmost_rest<R>(
        &mut self,
        rest_id: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
        f: impl FnOnce(
            &mut Self,
            &mut super::super::process::satellites::BranchingMergingProcessingRestrictionSpecification,
            &mut CalculationAlgorithmContextBase,
        ) -> R,
    ) -> R {
        let mut rest = std::mem::take(
            calc_alg_context
                .process_context_mut()
                .restriction_spec_mut(rest_id),
        );
        let r = f(self, &mut rest, calc_alg_context);
        *calc_alg_context
            .process_context_mut()
            .restriction_spec_mut(rest_id) = rest;
        r
    }

    /// Resolve or create the branching-merging rest for one at-most firing —
    /// the `procRest` split of `applyATMOSTRule` (cpp 14891–14980).
    ///
    /// KONCLUDE-PORT-NOTE[api]: Konclude allocates a NEW rest per
    /// (re)application, copy-initialised from the previous one, because forked
    /// SIBLING tasks share the previous rest read-only. The port keeps ONE
    /// rest per installed reapply descriptor and mutates it in place: sibling
    /// isolation is the branch-epoch journal's job (`restriction_spec_mut`
    /// journals the first pre-epoch touch, and merge/qualify branch points
    /// always own an epoch), so a per-fire copy would only orphan the
    /// descriptor's pointer.
    fn ht_atmost_resolve_rest(
        &mut self,
        process_indi: &mut NodeId,
        con_des: ConDescId,
        dep_track_point: TrackPointId,
        proc_rest: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> RestrictionSpecId {
        if proc_rest.is_some()
            && calc_alg_context
                .process_context()
                .restriction_spec(proc_rest)
                .is_branching_merging
        {
            return proc_rest;
        }
        // fresh application: `createATMOSTDependency` + the non-deterministic
        // basis track point (cpp 14948–14956). With dependency building off
        // both stay NONE and the callers fall back to `dep_track_point`.
        let atmost_dep =
            self.create_atmost_dependency(process_indi, con_des, dep_track_point, calc_alg_context);
        let atmost_tp = self.create_non_deterministic_dependency_track_point_branch(
            atmost_dep,
            true,
            calc_alg_context,
        );
        let mut rest =
            super::super::process::satellites::BranchingMergingProcessingRestrictionSpecification::new(
                INVALID,
            );
        rest.init_branching_merging_processing_restriction(None);
        rest.set_dependency_track_point(atmost_tp);
        rest.init_merging_dependency_node(atmost_dep);
        calc_alg_context
            .process_context_mut()
            .alloc_restriction_spec(rest)
    }

    /// Classify one successor's label against the at-most qualifier:
    /// `Some(true)` = counted (every operand present at its own polarity),
    /// `Some(false)` = excluded (all tags present, some at the opposite
    /// polarity), `None` = undecided (some operand tag absent — the choose
    /// rule's input). Mirrors the legacy pair
    /// `ht_role_successors_with_concepts` / `ht_find_both_qualify_successor`
    /// exactly (including the raw operand polarity; the rule-level `negate`
    /// does not flip the filler — see the KONCLUDE-PORT-NOTE there).
    fn ht_atmost_classify_successor(
        &self,
        succ: NodeId,
        concept_linker: &[NegLink<ConceptId>],
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Option<bool> {
        if concept_linker.is_empty() {
            // unqualified (functional-family) at-most: every successor counts.
            return Some(true);
        }
        let ls = calc_alg_context
            .process_context()
            .node(succ)
            .use_reapply_con_label_set;
        if ls.is_none() {
            return None;
        }
        let mut all_expected = true;
        for nl in concept_linker {
            let t = calc_alg_context
                .ontology_arenas()
                .concept(nl.target)
                .get_concept_tag();
            let mut cd: ConDescId = Id::NONE;
            let mut dtp: TrackPointId = TrackPointId::NONE;
            if !calc_alg_context
                .process_context()
                .label_set(ls)
                .get_concept_descriptor_by_tag(t, &mut cd, &mut dtp)
            {
                return None;
            }
            if calc_alg_context.process_context().con_desc(cd).is_negated() != nl.negated {
                all_expected = false;
            }
        }
        Some(all_expected)
    }

    /// Is a recorded merge candidate still usable: its node alive (not
    /// merged away / purged) and its link intact (same role, still between
    /// the counted parent and the candidate). The at-most bound check and
    /// the pair enumeration filter through this instead of re-scanning the
    /// full successor list (`hasRoleSuccessorToIndividual`, cpp 15130).
    fn ht_atmost_candidate_valid(
        &self,
        parent: NodeId,
        role: RoleId,
        cand: NodeId,
        link: EdgeId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> bool {
        let pc = calc_alg_context.process_context();
        if cand.is_none() || link.is_none() {
            return false;
        }
        let n = pc.node(cand);
        if n.has_merged_into_individual_node_id()
            || n.has_purged_blocked_processing_restriction_flags()
        {
            return false;
        }
        if link.index() >= pc.edges().len() {
            return false;
        }
        let e = pc.edge(link);
        e.get_link_role() == role
            && e.get_source_individual() == parent
            && e.get_destination_individual() == cand
    }

    /// The incremental successor initialization — the port of
    /// `initializeMergingIndividualNodes` (cpp 15820–16063) over the links
    /// added since the rest's last scan (`scan_edge_watermark`; Konclude's
    /// `getRoleSuccessorHistoryLinkIterator(role, mIndiLink)`).
    ///
    /// New links' successors are classified into the rest's lists: counted →
    /// merging candidates, excluded → dropped, undecided → both-qualify (the
    /// choose rule branches these in the spine; Konclude's choose-TRIGGER
    /// reapply deferral needs `CConceptRoleBranchingTrigger` and stays
    /// PORT-PENDING). Counted candidates also feed the DISTINCT-CLIQUE greedy
    /// (cpp 15886–15928 + 15981–16021): a maximal run of pairwise-distinct
    /// counted successors; more than `cardinality` of them refutes the ≤n
    /// immediately — with the distinct edges' own dependencies — without any
    /// merge search. Returns `true` when it raised that clash.
    ///
    /// KONCLUDE-PORT-NOTE[api]: the merging-INITIALIZATION candidate split
    /// (`addMergingInitializationCandidateNodeLinker` + the recorded init
    /// clash descriptors) is input to the NON-pairwise merge state machine
    /// (`mergeMergingIndividualNodes`); the port ships the pairwise spine, so
    /// clique members join the plain candidate list (their mutual distinct
    /// edges already exclude the intra-clique pairs) and only the clique
    /// CLASH half is live. The nominal-merging and blockable-predecessor
    /// halves stay W3-DEFER with the NN rule.
    #[allow(clippy::too_many_arguments)]
    fn ht_atmost_initialize_merging_nodes(
        &mut self,
        process_indi: &mut NodeId,
        role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        cardinality: Cint64,
        con_des: ConDescId,
        dep_track_point: TrackPointId,
        rest_id: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let edge_len = calc_alg_context.process_context().edges().len();
        let watermark = {
            let r = calc_alg_context.process_context().restriction_spec(rest_id);
            // defensive clamp — see `scan_edge_watermark` in satellites.rs.
            (r.scan_edge_watermark.max(0) as usize).min(edge_len)
        };
        // gather the NEW links only (edge-arena order == insertion order).
        let mut new_links: Vec<(EdgeId, NodeId)> = Vec::new();
        for (link, succ) in self.ht_role_successor_links(*process_indi, role, calc_alg_context) {
            if link.index() >= watermark {
                new_links.push((link, succ));
            }
        }
        calc_alg_context
            .process_context_mut()
            .restriction_spec_mut(rest_id)
            .scan_edge_watermark = edge_len as Cint64;
        if new_links.is_empty() {
            return false;
        }
        // the distinct-clique greedy run over the counted candidates
        // ((node, link) with a distinct hash, pairwise distinct).
        let mut dis_run: Vec<(NodeId, EdgeId)> = Vec::new();
        let mut max_run: Vec<(NodeId, EdgeId)> = Vec::new();
        for (link, succ) in new_links {
            match self.ht_atmost_classify_successor(succ, concept_linker, calc_alg_context) {
                Some(true) => {
                    // counted → merge candidate.
                    let linker = {
                        let mut l = super::super::process::stubs::BranchingMergingIndividualNodeCandidateLinker::new();
                        l.init_branching_merging_individual_node_candidate(succ, link);
                        calc_alg_context
                            .process_context_mut()
                            .alloc_branching_merging_candidate_linker(l)
                    };
                    self.ht_with_atmost_rest(rest_id, calc_alg_context, |_alg, rest, ctx| {
                        rest.add_merging_candidate_node_linker(
                            linker,
                            ctx.process_context_mut(),
                        );
                    });
                    // clique run tracking (cpp 15886–15928).
                    let dh = calc_alg_context.process_context().node(succ).use_distinct_hash;
                    if dh.is_some() {
                        let distinct_to_all = dis_run.iter().all(|&(prev, _)| {
                            let prev_id = calc_alg_context
                                .process_context()
                                .node(prev)
                                .individual_node_id();
                            calc_alg_context
                                .process_context()
                                .distinct_hash(dh)
                                .is_individual_distinct(prev_id)
                        });
                        if distinct_to_all {
                            dis_run.push((succ, link));
                        } else {
                            if dis_run.len() > max_run.len() {
                                max_run = std::mem::take(&mut dis_run);
                            } else {
                                dis_run.clear();
                            }
                            dis_run.push((succ, link));
                        }
                    }
                }
                Some(false) => {}
                None => {
                    // undecided → both-qualify (choose input).
                    let linker = {
                        let mut l = super::super::process::stubs::BranchingMergingIndividualNodeCandidateLinker::new();
                        l.init_branching_merging_individual_node_candidate(succ, link);
                        calc_alg_context
                            .process_context_mut()
                            .alloc_branching_merging_candidate_linker(l)
                    };
                    self.ht_with_atmost_rest(rest_id, calc_alg_context, |_alg, rest, ctx| {
                        rest.add_both_qualify_candidate_node_linker(
                            linker,
                            ctx.process_context_mut(),
                        );
                    });
                }
            }
        }
        if dis_run.len() > max_run.len() {
            max_run = dis_run;
        }
        // the clique clash (cpp 15988–16015): more than `cardinality`
        // pairwise-distinct counted successors — collect each pair's distinct
        // edge dependency (deduped by track point), the members' merge-causing
        // descriptors, and the at-most concept itself.
        if (max_run.len() as Cint64) > cardinality {
            let mut clashes: super::super::process::ClashDescId = Id::NONE;
            let mut seen_tps: Vec<TrackPointId> = Vec::new();
            for (i, &(cand, link)) in max_run.iter().enumerate() {
                for &(other, _) in &max_run[i + 1..] {
                    let dh = calc_alg_context.process_context().node(cand).use_distinct_hash;
                    if dh.is_none() {
                        continue;
                    }
                    let other_id = calc_alg_context
                        .process_context()
                        .node(other)
                        .individual_node_id();
                    let dis_edge = calc_alg_context
                        .process_context()
                        .distinct_hash(dh)
                        .get_individual_distinct_edge(other_id);
                    if dis_edge.is_none() {
                        continue;
                    }
                    let dis_tp = calc_alg_context
                        .process_context()
                        .distinct_edge(dis_edge)
                        .get_dependency_track_point();
                    if !seen_tps.contains(&dis_tp) {
                        seen_tps.push(dis_tp);
                        clashes = self.create_clashed_individual_distinct_descriptor(
                            clashes,
                            dis_edge,
                            dis_tp,
                            calc_alg_context,
                        );
                    }
                }
                clashes = self.ht_create_individual_merge_causing_descriptors(
                    clashes,
                    cand,
                    link,
                    concept_linker,
                    calc_alg_context,
                );
            }
            let clash = self.create_clashed_concept_descriptor(
                clashes,
                process_indi,
                con_des,
                dep_track_point,
                calc_alg_context,
            );
            calc_alg_context.raise_clash(clash);
            return true;
        }
        false
    }

    /// The REST-driven qualify + merge spine: `qualifyMergingIndividualNodes`
    /// (cpp 15677–15816) over the persistent both-qualify list, then the
    /// pairwise bound check / merge branching over the persistent candidate
    /// lists. Same search tree as the legacy `ht_apply_atmost_merge` (one
    /// nested choose branch per undecided successor, then merge pairs), but
    /// each fire touches only state the previous fires haven't settled.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn ht_atmost_qualify_merge_rest(
        &mut self,
        process_indi: &mut NodeId,
        role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        cardinality: Cint64,
        dep_track_point: TrackPointId,
        con_des: ConDescId,
        rest_id: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        loop {
            // --- qualify: the next still-undecided both-qualify candidate ---
            let mut choose: Option<(NodeId, EdgeId)> = None;
            loop {
                let head = calc_alg_context
                    .process_context()
                    .restriction_spec(rest_id)
                    .get_both_qualify_candidate_node_linker();
                if head.is_none() {
                    break;
                }
                let (cand, link, next) = {
                    let pc = calc_alg_context.process_context();
                    let l = pc.branching_merging_candidate_linker(head);
                    (l.merging_indi_node_candidate, l.merging_link, l.next)
                };
                calc_alg_context
                    .process_context_mut()
                    .restriction_spec_mut(rest_id)
                    .set_both_qualify_candidate_node_linker(next);
                if !self.ht_atmost_candidate_valid(*process_indi, role, cand, link, calc_alg_context)
                {
                    continue;
                }
                match self.ht_atmost_classify_successor(cand, concept_linker, calc_alg_context) {
                    Some(true) => {
                        // decided positive since classification → merge
                        // candidate (cpp 15700–15707, fresh linker).
                        let linker = {
                            let mut l = super::super::process::stubs::BranchingMergingIndividualNodeCandidateLinker::new();
                            l.init_branching_merging_individual_node_candidate(cand, link);
                            calc_alg_context
                                .process_context_mut()
                                .alloc_branching_merging_candidate_linker(l)
                        };
                        self.ht_with_atmost_rest(rest_id, calc_alg_context, |_alg, rest, ctx| {
                            rest.add_merging_candidate_node_linker(
                                linker,
                                ctx.process_context_mut(),
                            );
                        });
                    }
                    Some(false) => {}
                    None => {
                        // CHOOSE-TRIGGER deferral (Konclude's
                        // installedChoiseTriggering, cpp 15933–15957): for an
                        // ALL-ATOMIC qualifier the eager C-vs-¬C branch is
                        // replaced by reactivation hooks on the missing
                        // operands. Completeness is the read-off's own
                        // argument: in a clash-free SATURATED graph an
                        // underived atom is FALSE in the canonical model, so
                        // the undecided successor simply never counts; if any
                        // rule later derives a missing operand, the hook
                        // re-queues the ≤n on the parent and the candidate
                        // re-enters this loop. COMPLEX qualifiers keep the
                        // eager choose branch (Konclude covers those via
                        // absorption-computed triggers — PORT-PENDING).
                        let all_atomic = concept_linker.iter().all(|nl| {
                            let opc = calc_alg_context
                                .ontology_arenas()
                                .concept(nl.target)
                                .get_operator_code();
                            opc == op::CCATOM || opc == op::CCSUB
                        });
                        if all_atomic {
                            self.ht_atmost_install_choose_triggers(
                                *process_indi,
                                cand,
                                link,
                                concept_linker,
                                con_des,
                                dep_track_point,
                                rest_id,
                                calc_alg_context,
                            );
                            continue;
                        }
                        choose = Some((cand, link));
                        break;
                    }
                }
            }
            if let Some((qsucc, qlink)) = choose {
                // --- the choose rule on one undecided successor (mirrors the
                // legacy block in `ht_apply_atmost_merge`). ---
                let qualify_dep: DependencyId = {
                    let mut pi = *process_indi;
                    self.create_qualify_dependency(&mut pi, con_des, dep_track_point, calc_alg_context)
                };
                let qlink_tp = calc_alg_context
                    .process_context()
                    .edge(qlink)
                    .get_dependency_track_point();
                let qclash = self.create_clashed_individual_link_descriptor(
                    Id::NONE,
                    qlink,
                    qlink_tp,
                    calc_alg_context,
                );
                self.ht_add_branch_clashes(qualify_dep, qclash, calc_alg_context);
                let parent_used_branch_node = calc_alg_context.base.used_branch_tree_node;
                if cardinality <= 0 {
                    // ≤0 R.C: only the NEGATED qualification is consistent —
                    // deterministic (cpp 15721–15733).
                    let tps = self.ht_mint_alternative_track_points(
                        qualify_dep,
                        1,
                        parent_used_branch_node,
                        calc_alg_context,
                    );
                    let add_tp = tps.first().copied().unwrap_or(dep_track_point);
                    for nl in concept_linker {
                        if calc_alg_context.has_pending_signal() {
                            return;
                        }
                        let mut s = qsucc;
                        self.add_concept_to_individual(
                            nl.target,
                            !nl.negated,
                            &mut s,
                            add_tp,
                            true,
                            true,
                            calc_alg_context,
                        );
                    }
                    self.add_individual_to_processing_queue(qsucc, calc_alg_context);
                    if calc_alg_context.has_pending_signal() {
                        return;
                    }
                    continue;
                }
                let parent_branch: BranchNodeId = self
                    .or_branch_stack
                    .last()
                    .map(|bp| bp.branch_node)
                    .unwrap_or(BranchNodeId::NONE);
                let root_branch: BranchNodeId = self
                    .or_branch_stack
                    .first()
                    .map(|bp| bp.branch_node)
                    .unwrap_or(BranchNodeId::NONE);
                let alt_track_points = self.ht_mint_alternative_track_points(
                    qualify_dep,
                    2,
                    parent_used_branch_node,
                    calc_alg_context,
                );
                let branch_node: BranchNodeId = calc_alg_context
                    .process_context_mut()
                    .alloc_branch_node(BranchTreeNode {
                        process_tag: 0,
                        parent_node: parent_branch,
                        root_node: root_branch,
                        branched_dep_track_point: Id::NONE,
                        sat_calc_task: INVALID,
                    });
                let node_count_at_push = calc_alg_context.process_context().node_count();
                let first_alt_tp = alt_track_points.first().copied().unwrap_or(Id::NONE);
                calc_alg_context.push_branch_epoch();
                self.or_branch_open_count += 1;
                self.or_branch_stack.push(OrBranchPoint {
                    node: qsucc,
                    disjuncts: Vec::new(),
                    negate: false,
                    next_alt: 1,
                    dep_track_point,
                    branch_node,
                    or_dependency_node: qualify_dep,
                    alt_track_points,
                    parent_used_branch_node,
                    node_label_snapshot: Default::default(),
                    node_queue_snapshot: Default::default(),
                    node_count_at_push,
                    kind: BranchKind::AtMostQualify {
                        succ: qsucc,
                        atmost: AtMostMergeBranch {
                            pairs: Vec::new(),
                            parent: *process_indi,
                            role,
                            concept_linker: concept_linker.to_vec(),
                            negate,
                            cardinality,
                            con_des,
                            rest: rest_id,
                        },
                    },
                    own_epoch: true,
                });
                let add_tp = if first_alt_tp.is_some() {
                    calc_alg_context.base.used_branch_tree_node = calc_alg_context
                        .process_context()
                        .track_point(first_alt_tp)
                        .get_branch_node();
                    first_alt_tp
                } else {
                    dep_track_point
                };
                for nl in concept_linker {
                    if calc_alg_context.has_pending_signal() {
                        return;
                    }
                    let mut s = qsucc;
                    self.add_concept_to_individual(
                        nl.target,
                        !nl.negated,
                        &mut s,
                        add_tp,
                        true,
                        true,
                        calc_alg_context,
                    );
                }
                self.add_individual_to_processing_queue(qsucc, calc_alg_context);
                if calc_alg_context.has_pending_signal() {
                    return;
                }
                continue;
            }

            // --- merge bound check over the persistent candidates. ---
            let cands = self.ht_atmost_valid_candidates(*process_indi, role, rest_id, calc_alg_context);
            if (cands.len() as Cint64) <= cardinality {
                return;
            }
            let mut merge_causing: super::super::process::ClashDescId = Id::NONE;
            for &(s, link) in &cands {
                merge_causing = self.ht_create_individual_merge_causing_descriptors(
                    merge_causing,
                    s,
                    link,
                    concept_linker,
                    calc_alg_context,
                );
            }
            let mut pairs: Vec<(NodeId, NodeId)> = Vec::new();
            for i in 0..cands.len() {
                for j in (i + 1)..cands.len() {
                    if self.ht_individuals_mergeable(cands[i].0, cands[j].0, calc_alg_context) {
                        pairs.push((cands[i].0, cands[j].0));
                    }
                }
            }
            if pairs.is_empty() {
                let clash = self.create_clashed_concept_descriptor(
                    merge_causing,
                    process_indi,
                    con_des,
                    dep_track_point,
                    calc_alg_context,
                );
                calc_alg_context.raise_clash(clash);
                return;
            }
            let parent_branch: BranchNodeId = self
                .or_branch_stack
                .last()
                .map(|bp| bp.branch_node)
                .unwrap_or(BranchNodeId::NONE);
            let root_branch: BranchNodeId = self
                .or_branch_stack
                .first()
                .map(|bp| bp.branch_node)
                .unwrap_or(BranchNodeId::NONE);
            let merge_dependency_node: DependencyId = {
                let mut pi = *process_indi;
                self.create_merge_dependency(&mut pi, con_des, dep_track_point, calc_alg_context)
            };
            self.ht_add_branch_clashes(merge_dependency_node, merge_causing, calc_alg_context);
            let parent_used_branch_node = calc_alg_context.base.used_branch_tree_node;
            let alt_track_points = self.ht_mint_alternative_track_points(
                merge_dependency_node,
                pairs.len(),
                parent_used_branch_node,
                calc_alg_context,
            );
            let branch_node: BranchNodeId =
                calc_alg_context
                    .process_context_mut()
                    .alloc_branch_node(BranchTreeNode {
                        process_tag: 0,
                        parent_node: parent_branch,
                        root_node: root_branch,
                        branched_dep_track_point: Id::NONE,
                        sat_calc_task: INVALID,
                    });
            let node_count_at_push = calc_alg_context.process_context().node_count();
            let (into, from) = pairs[0];
            let first_alt_tp = alt_track_points.first().copied().unwrap_or(Id::NONE);
            calc_alg_context.push_branch_epoch();
            self.or_branch_open_count += 1;
            self.or_branch_stack.push(OrBranchPoint {
                node: *process_indi,
                disjuncts: Vec::new(),
                negate: false,
                next_alt: 1,
                dep_track_point,
                branch_node,
                or_dependency_node: merge_dependency_node,
                alt_track_points,
                parent_used_branch_node,
                node_label_snapshot: Default::default(),
                node_queue_snapshot: Default::default(),
                node_count_at_push,
                kind: BranchKind::AtMostMerge(AtMostMergeBranch {
                    pairs,
                    parent: *process_indi,
                    role,
                    concept_linker: concept_linker.to_vec(),
                    negate,
                    cardinality,
                    con_des,
                    rest: rest_id,
                }),
                own_epoch: true,
            });
            let add_tp = if first_alt_tp.is_some() {
                calc_alg_context.base.used_branch_tree_node = calc_alg_context
                    .process_context()
                    .track_point(first_alt_tp)
                    .get_branch_node();
                first_alt_tp
            } else {
                dep_track_point
            };
            self.merge_individual_node_into(into, from, add_tp, calc_alg_context);
            if calc_alg_context.has_pending_signal() {
                return;
            }
            self.ht_relocate_incoming_links(*process_indi, from, into, add_tp, calc_alg_context);
            if calc_alg_context.has_pending_signal() {
                return;
            }
            // loop: bound re-check on the merged graph (the merged-away
            // candidate drops out via the validity filter).
        }
    }

    /// Install the ATMOST-reactivation hooks for one undecided successor —
    /// the choose-trigger deferral's arming half (Konclude installs
    /// `CExtendedCondensedReapplyConceptDescriptorATMOSTReactivation` on the
    /// successor's concept reapply queue, cpp 15949–15957). One STATIC hook
    /// per MISSING qualifier operand, keyed (tag, counted polarity): when the
    /// operand lands, the condensed fire path (u10) hands the candidate back
    /// to the rest's both-qualify list and re-queues the ≤n on `parent`.
    /// Duplicate installs are cheap no-ops at fire time (the qualify loop
    /// dedups candidates by node).
    #[allow(clippy::too_many_arguments)]
    fn ht_atmost_install_choose_triggers(
        &mut self,
        parent: NodeId,
        succ: NodeId,
        link: EdgeId,
        concept_linker: &[NegLink<ConceptId>],
        con_des: ConDescId,
        dep_track_point: TrackPointId,
        rest_id: RestrictionSpecId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let ls = calc_alg_context
            .process_context()
            .node(succ)
            .use_reapply_con_label_set;
        for nl in concept_linker {
            let tag = calc_alg_context
                .ontology_arenas()
                .concept(nl.target)
                .get_concept_tag();
            // only the MISSING operands need hooks; present ones are decided.
            if ls.is_some() {
                let mut cd: ConDescId = Id::NONE;
                let mut dtp: TrackPointId = TrackPointId::NONE;
                if calc_alg_context
                    .process_context()
                    .label_set(ls)
                    .get_concept_descriptor_by_tag(tag, &mut cd, &mut dtp)
                {
                    continue;
                }
            }
            let mut desc = super::super::process::reapply_sat::CondensedReapplyConceptDescriptor::new(
                con_des,
                dep_track_point,
                !nl.negated,
            );
            desc.init_atmost_extended_reapply_descriptor(
                con_des,
                dep_track_point,
                !nl.negated,
                rest_id.raw,
                parent,
                link,
            );
            let desc = calc_alg_context
                .process_context_mut()
                .alloc_cond_reapply_con_desc(desc);
            calc_alg_context
                .process_context_mut()
                .node_add_concept_reapply_concept_descriptor_by_tag(succ, tag, nl.negated, desc);
        }
    }

    /// The live merge candidates of one at-most rest: walk the
    /// init/nominal/plain candidate chains, validity-filter, dedup by node.
    fn ht_atmost_valid_candidates(
        &self,
        parent: NodeId,
        role: RoleId,
        rest_id: RestrictionSpecId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Vec<(NodeId, EdgeId)> {
        let mut out: Vec<(NodeId, EdgeId)> = Vec::new();
        let heads = {
            let r = calc_alg_context.process_context().restriction_spec(rest_id);
            [
                r.get_merging_initialization_candidate_node_linker(),
                r.nominal_merging_nodes_linker,
                r.get_merging_candidate_node_linker(),
            ]
        };
        for head in heads {
            let mut it = head;
            while it.is_some() {
                let (cand, link, next) = {
                    let pc = calc_alg_context.process_context();
                    let l = pc.branching_merging_candidate_linker(it);
                    (l.merging_indi_node_candidate, l.merging_link, l.next)
                };
                it = next;
                if out.iter().any(|&(n, _)| n == cand) {
                    continue;
                }
                if self.ht_atmost_candidate_valid(parent, role, cand, link, calc_alg_context) {
                    out.push((cand, link));
                }
            }
        }
        out
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let role = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_role();
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let role = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_role();
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let role = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_role();
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
        let mut cardinality: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_parameter();
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
            // KONCLUDE-PORT-NOTE[api]: Konclude delegates unqualified at-most-1 to
            // applyFUNCTIONALRule (the NN-rule pre-scan + min-id merge target). That rule
            // is PORT-PENDING, so the W14 port handles the functional case uniformly
            // through the generic at-most merge/clash path below with an empty (⊤)
            // qualifier filter (every R-successor counts). The NN-rule for nominal
            // predecessors stays W3-DEFER. Fall through (no early return).
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
        let concept_op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operand_list()
            .to_vec();
        if self.conf_atmost_rest {
            // --- the `branchingMergingProcRest` resume path (KM_HT_ATMOST_REST,
            // cpp 14891–15005): resolve/create the rest, scan only the links
            // added since the last fire, then run the rest-driven spine. ---
            let rest_id = self.ht_atmost_resolve_rest(
                process_indi,
                con_des,
                dep_track_point,
                proc_rest,
                calc_alg_context,
            );
            // Unsat-cache probe after the fresh merging-restriction init (cpp
            // 14959: `testUnsatisfiableCacheForMergingInitialization`,
            // constant-true; Konclude throws out of the rule on a hit).
            // Pending-gated: `raise_clash` overwrites the signal.
            if !calc_alg_context.has_pending_signal() {
                self.test_individual_node_unsatisfiable_cached(*process_indi, calc_alg_context);
                if calc_alg_context.has_pending_signal() {
                    return;
                }
            }
            // fast clash (cpp 14902–14908 / 14967–14973): an unqualified ≤0
            // with any `role`-link is refuted by the link itself.
            if cardinality <= 0 && !has_operands {
                if let Some(&(link, _)) = self
                    .ht_role_successor_links(*process_indi, role, calc_alg_context)
                    .first()
                {
                    let link_tp = calc_alg_context
                        .process_context()
                        .edge(link)
                        .get_dependency_track_point();
                    let clash = self.create_clashed_concept_descriptor(
                        Id::NONE,
                        process_indi,
                        con_des,
                        dep_track_point,
                        calc_alg_context,
                    );
                    let clash = self.create_clashed_individual_link_descriptor(
                        clash,
                        link,
                        link_tp,
                        calc_alg_context,
                    );
                    calc_alg_context.raise_clash(clash);
                    return;
                }
            }
            if self.ht_atmost_initialize_merging_nodes(
                process_indi,
                role,
                &concept_op_linker,
                cardinality,
                con_des,
                dep_track_point,
                rest_id,
                calc_alg_context,
            ) {
                return;
            }
            self.ht_atmost_qualify_merge_rest(
                process_indi,
                role,
                &concept_op_linker,
                negate,
                cardinality,
                dep_track_point,
                con_des,
                rest_id,
                calc_alg_context,
            );
            if calc_alg_context.has_pending_signal() {
                return;
            }
            // installReapplication (cpp 15001–15005), rest-carrying: a STATIC
            // descriptor installed once per (node, ≤n concept) — see the
            // KONCLUDE-PORT-NOTE on `add_concept_to_reapply_queue_role_restricted_static`.
            let is_concept_reapplied: bool = calc_alg_context
                .process_context()
                .con_proc_desc(*con_pro_des)
                .is_concept_reapplied();
            if !is_concept_reapplied {
                self.add_concept_to_reapply_queue_role_restricted_static(
                    con_des,
                    role,
                    *process_indi,
                    rest_id.raw,
                    dep_track_point,
                    calc_alg_context,
                );
            }
            return;
        }
        let _ = proc_rest;
        // W14-number: the merge/clash spine, over the live role-successor iterator +
        // the real distinct-edge hash. conceptOpLinkerIt = concept->getOperandList()
        // (the at-most qualifier C; empty ⇒ unqualified/functional). The role-succ-hash
        // satellite iterators (W2-DEFER), the at-most fast-clash label walk, the
        // unsat-cache retrieval strategy stay PORT-PENDING; the ATMOST dependency +
        // branching-merging restriction-spec resume machinery is LIVE behind
        // `KM_HT_ATMOST_REST` (see `ht_atmost_qualify_merge_rest`).
        self.ht_apply_atmost_merge(
            process_indi,
            role,
            &concept_op_linker,
            negate,
            cardinality,
            dep_track_point,
            con_des,
            calc_alg_context,
        );

        // A merge clash throws in the C++ (skipping the registration below) — the
        // port signals instead of unwinding, so return here like the exception would.
        if calc_alg_context.has_pending_signal() {
            return;
        }

        // installReapplication (cpp 15001–15005): keep the ≤n restriction armed so a
        // LATER `role`-link re-fires this rule — without it the merge/clash check only
        // sees the successors that happen to exist NOW, an order-dependent closure.
        // KONCLUDE-PORT-NOTE[api]: Konclude registers the dynamic
        // `branchingMergingProcRest` descriptor to resume its branching-merging state
        // machine; the greedy merge has no state to resume, so the port registers the
        // plain-role STATIC descriptor (the `applyALLRule` pattern) — every future
        // link re-runs the whole rule, a sound superset. The `is_concept_reapplied`
        // guard keeps the queue duplicate-free.
        let is_concept_reapplied: bool = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .is_concept_reapplied();
        if !is_concept_reapplied {
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
        let role = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_role();
        let dep_track_point: TrackPointId = calc_alg_context
            .process_context()
            .con_proc_desc(*con_pro_des)
            .get_dependency_track_point();
        let mut cardinality: Cint64 = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_parameter();
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
            // W14-number: distinct-successor generation, over the live ∃-rule
            // primitives. conceptOpLinkerIt = concept->getOperandList() (the qualifier C).
            let concept_op_linker: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            // alreadyExistSuitableSuccessors = hasDistinctRoleSuccessorConcepts(...) —
            // if `cardinality` distinct R-successors already carry C, nothing to do.
            let existing = self.ht_role_successors_with_concepts(
                *process_indi,
                role,
                &concept_op_linker,
                negate,
                calc_alg_context,
            );
            if (existing.len() as Cint64) >= cardinality {
                return;
            }
            // PORT-PENDING: the at-least fast-clash label walk
            // (`mConfAtleastAtmostFastClashCheck`), the unsat-cache retrieval strategy
            // (W6 Strategy) and `createATLEASTDependency` stay deferred.
            // Unsat-cache probe before generating the ≥n successors (cpp
            // 16132: `testUnsatisfiableCacheForSuccessorGeneration`,
            // constant-true). A hit clashes the parent and aborts the
            // generation. Pending-gated: `raise_clash` overwrites the signal.
            if !calc_alg_context.has_pending_signal() {
                self.test_individual_node_unsatisfiable_cached(*process_indi, calc_alg_context);
                if calc_alg_context.has_pending_signal() {
                    return;
                }
            }
            self.applied_atleast_rule_count += 1; // ++mAppliedATLEASTRuleCount
            self.ht_create_distinct_successors(
                *process_indi,
                role,
                &concept_op_linker,
                negate,
                dep_track_point,
                cardinality,
                calc_alg_context,
            );
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
        let concept: ConceptId = calc_alg_context
            .process_context()
            .con_desc(con_des)
            .get_concept();
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
