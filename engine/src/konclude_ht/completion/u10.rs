//! `completion::u10` — Reapply-queue management family (port unit #10 of 36).
//!
//! Faithful port of the 27-method "Reapply-queue management" unit of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
//! (manifest `01-completion-methods.md`, "Unit 10", cpp ranges 6252–27676):
//!
//!   * `reapplySatisfiableCachedAbsorbed{Disjunction,Generating}Concepts`
//!     (6252 / 6275) — flush a node's cached-absorbed reapply linker into its
//!     concept-processing queue,
//!   * the two `reapplyConceptUpdatedRepresentative` overloads (11236 / 11248),
//!   * the `applyReapplyQueueConcepts` family — the propagation-binding linker
//!     (13876), the concept+negation / role / restricted / condensed-iterator
//!     overloads (26523 / 26549 / 26572 / 26602),
//!   * `applyExtendedReapplyConceptDescriptor` (26492, the ATMOST reactivation),
//!   * `collectReapplyAutomatTransactionsRestrictions` (22019, the qualified-∀
//!     automaton restriction collector),
//!   * `createNewIndividualsLink{s,}Reapplyed` (22295 / 22372, link creation that
//!     re-fires the role-keyed reapply queue),
//!   * the five `addConceptToReapplyQueue` overloads (26625..26671) and the two
//!     `isConceptInReapplyQueue` overloads (26674 / 26682).
//!
//! The 7 rule-counter getters that the manifest also lists in this unit
//! (`getAppliedANDRuleCount`..`getAppliedTotalRuleCount`, cpp 27650–27676) are
//! ALREADY ported as inline accessors in `completion/algorithm.rs`
//! (`applied_and_rule_count()`..`applied_total_rule_count()`); they are NOT
//! re-defined here, to avoid a duplicate-method definition on the same impl.
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase` (the C++ `CCalculationAlgorithmContextBase*`).
//! A `CIndividualProcessNode*` becomes a `NodeId`, a `CConceptDescriptor*` a
//! `ConDescId`, a `CDependencyTrackPoint*` a `TrackPointId`, an
//! `CIndividualLinkEdge*` an `EdgeId`; the static `CConcept*`/`CRole*` become
//! `ConceptId`/`RoleId` (resolved against `ctx.ontology_arenas()`).
//!
//! KONCLUDE-PORT-NOTE[overload]: Rust has no function overloading, so the C++
//! same-name overloads get a disambiguating suffix preserving their distinguishing
//! parameter (`_role` / `_concept` / `_restricted` / `_condensed_iterator` /
//! `_propagation_binding` / `_binding_count`). The original C++ name is kept in
//! each item's doc-comment as the port anchor.
//!
//! KONCLUDE-PORT-NOTE[api]: the reapply machinery hangs off three not-yet-ported
//! subsystems — (1) the per-node intrusive reapply containers and their iterators
//! (`CReapplyQueue` / `CCondensedReapplyQueue` / `CReapplyQueueIterator` /
//! `CCondensedReapplyQueueIterator` / the `CReapplyConceptDescriptor` /
//! `CCondensedReapplyConceptDescriptor` / `CPropagationBindingReapplyConceptDescriptor`
//! linker payloads), reached via node getters (`getConceptProcessingQueue`,
//! `getRoleReapplyQueue`, `getConceptReapplyQueue`, `getRoleReapplyIterator`,
//! `getConceptReapplyIterator`, `getReapplyConceptLabelSet`,
//! `getSatisfiableCachedAbsorbed*Linker`, `getSuccessorIndividualATMOSTReactivationData`)
//! that `process/node.rs` has not yet surfaced; (2) the link-installation helpers
//! (`getLocalizedIndividual`, `hasIndividualsLink`, `installIndividualNodeRoleLinkReapplied`,
//! `createIndividualNodeDisjointRolesLinks`, `addConceptsToIndividual`,
//! `linkCreationDirectlyChangedNeighbourConnectionUpdate`,
//! `setIndividualNodeConceptLabelSetModified`), all siblings in later units; and
//! (3) the per-test memory pool (`getUsedProcessTaskMemoryAllocationManager`) /
//! the STATINC counters. Every such site is transcribed in place and flagged
//! `// W3-DEFER[api]` / `// W3-DEFER[memory-pool]`; control flow is ported in full
//! (loops, polarity XORs, the `if (conProQueue) addIndividualToProcessingQueue`
//! tail), with linker-chain traversals modelled as an (empty until wired) `Vec`
//! and the "was anything queued" sentinel kept as an explicit bool because the
//! `conProQueue` pointer is a stubbed `Id::NONE`. Sibling queue-adders
//! (`addConceptRestrictedToProcessingQueue`, `addConceptToProcessingQueue`,
//! `addConceptPreprocessedToProcessingQueue`, `addIndividualToProcessingQueue`)
//! ARE the ported unit-4 methods and are called for real.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(unused_mut)]

use std::collections::HashMap;

use super::super::model::op;
use super::super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::super::model::{ConceptId, RoleId};
use super::super::process::node::IndividualProcessNode;
use super::super::process::stubs::ConceptProcessingQueueId;
use super::super::process::{ConDescId, EdgeId, LabelSetId, NodeId, TrackPointId};
use super::context::CalculationAlgorithmContextBase;

/// KONCLUDE-PORT-NOTE[api]: `CProcessingRestrictionSpecification*` is not yet
/// ported; an opaque handle (`INVALID` == `nullptr`), matching `u04`.
type ProcRestrictionHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CCondensedReapplyQueue*` — not yet ported.
type CondensedReapplyQueueHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CReapplyQueue*` — not yet ported.
type ReapplyQueueHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CCondensedReapplyQueueIterator` (by-value iterator) —
/// not yet ported; an opaque cursor handle.
type CondensedReapplyQueueIteratorHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CReapplyQueueIterator` (by-value iterator).
type ReapplyQueueIteratorHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CReapplyConceptDescriptor*` linker payload.
type ReapplyConDescHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CCondensedReapplyConceptDescriptor*` linker payload.
type CondensedReapplyConDescHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CPropagationBindingReapplyConceptDescriptor*` linker.
type PropagationBindingReapplyConDescHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CReapplyConceptSaturationLabelSet*` — saturation
/// label-set satellite, not yet ported.
type ReapplyConceptSaturationLabelSetHandle = Cint64;
/// KONCLUDE-PORT-NOTE[api]: `CSortedNegLinker<CRole*>*` — the (inverse-tagged)
/// role linker chain a link-creation iterates; head handle of the chain.
type RoleLinkerHandle = Cint64;

/// Port of `CConceptNegationPair` (the `<CConcept*, bool>` pair the automaton
/// restriction collector accumulates). KONCLUDE-PORT-NOTE[overload]: a small local
/// struct; the C++ class also lives elsewhere but only its (concept, negation)
/// payload is used here.
#[derive(Copy, Clone, Debug)]
pub struct ConceptNegationPair {
    pub concept: ConceptId,
    pub negated: bool,
}

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Satisfiable-cached-absorbed flush (cpp 6252 / 6275).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reapplySatisfiableCachedAbsorbedDisjunctionConcepts`.
    pub fn reapply_satisfiable_cached_absorbed_disjunction_concepts(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut concepts_reapplyed = false;

        // W3-DEFER[api]: conProQueue = individualNode->getConceptProcessingQueue(true);
        let con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        // W3-DEFER[api]: absorbedReapplyConDesLinker = individualNode->getSatisfiableCachedAbsorbedDisjunctionsLinker();
        //               (intrusive CReapplyConceptDescriptor chain; modelled as a Vec until node getter is surfaced).
        let absorbed_reapply_con_des_linker: Vec<ReapplyConDescHandle> = Vec::new();
        for absorbed_reapply_con_des in absorbed_reapply_con_des_linker {
            concepts_reapplyed = true;

            // W3-DEFER[api]: conDes = absorbedReapplyConDesLinker->getConceptDescriptor();
            let con_des: ConDescId = Id::NONE;
            // W3-DEFER[api]: depTrackPoint = absorbedReapplyConDesLinker->getDependencyTrackPoint();
            let dep_track_point: TrackPointId = Id::NONE;
            // W3-DEFER[api]: procRest = absorbedReapplyConDesLinker->getReapplyProcessingRestriction();
            let proc_rest: ProcRestrictionHandle = INVALID;
            // W3-DEFER[api]: absorbedReapplyConDesLinker->isStaticDescriptor()
            let is_static_descriptor = false;

            self.add_concept_restricted_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                individual_node,
                is_static_descriptor,
                proc_rest,
                calc_alg_context,
            );
            let _ = absorbed_reapply_con_des;
        }
        // W3-DEFER[api]: individualNode->clearSatisfiableCachedAbsorbedDisjunctionsLinker();

        concepts_reapplyed
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reapplySatisfiableCachedAbsorbedGeneratingConcepts`.
    pub fn reapply_satisfiable_cached_absorbed_generating_concepts(
        &mut self,
        individual_node: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut concepts_reapplyed = false;

        // W3-DEFER[api]: conProQueue = individualNode->getConceptProcessingQueue(true);
        let con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        // W3-DEFER[api]: absorbedReapplyConDesLinker = individualNode->getSatisfiableCachedAbsorbedGeneratingLinker();
        let absorbed_reapply_con_des_linker: Vec<ReapplyConDescHandle> = Vec::new();
        for absorbed_reapply_con_des in absorbed_reapply_con_des_linker {
            concepts_reapplyed = true;

            // W3-DEFER[api]: conDes = absorbedReapplyConDesLinker->getConceptDescriptor();
            let con_des: ConDescId = Id::NONE;
            // W3-DEFER[api]: depTrackPoint = absorbedReapplyConDesLinker->getDependencyTrackPoint();
            let dep_track_point: TrackPointId = Id::NONE;

            self.add_concept_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                individual_node,
                false,
                calc_alg_context,
            );
            let _ = absorbed_reapply_con_des;
        }
        // W3-DEFER[api]: individualNode->clearSatisfiableCachedAbsorbedGeneratingLinker();

        concepts_reapplyed
    }

    // =======================================================================
    // reapplyConceptUpdatedRepresentative — representative re-fire (cpp 11236 / 11248).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reapplyConceptUpdatedRepresentative`
    /// (the `CReapplyConceptLabelSet*`/no-binding-count overload).
    pub fn reapply_concept_updated_representative(
        &mut self,
        process_indi: NodeId,
        binding_con_des: ConDescId,
        binding_dep_track_point: TrackPointId,
        mut con_set: LabelSetId,
        reapply_queue: CondensedReapplyQueueHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi,calcAlgContext); — helper, later unit.
        // W3-DEFER[api]: conProQueue = processIndi->getConceptProcessingQueue(true);
        let con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        // addConceptPreprocessedToProcessingQueue(bindingConDes,bindingDepTrackPoint,conProQueue,processIndi,true,calcAlgContext);
        // (the `allowPreprocessing` overload — skipFunction defaults to nullptr == INVALID).
        self.add_concept_preprocessed_to_processing_queue_skip(
            binding_con_des,
            binding_dep_track_point,
            con_pro_queue,
            process_indi,
            true,
            calc_alg_context,
            INVALID,
        );
        // W3-DEFER[api]: reapplyQueue->isEmpty()
        let reapply_queue_empty = true;
        let _ = reapply_queue;
        if !reapply_queue_empty {
            // W3-DEFER[api]: conSet = processIndi->getReapplyConceptLabelSet(true);
            con_set = Id::NONE;
            // W3-DEFER[api]: CCondensedReapplyQueueIterator reapplyQueueIt(conSet->getConceptReapplyIterator(bindingConDes));
            let reapply_queue_it: CondensedReapplyQueueIteratorHandle = INVALID;
            self.apply_reapply_queue_concepts_condensed_iterator(
                process_indi,
                reapply_queue_it,
                calc_alg_context,
            );
            let _ = con_set;
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::reapplyConceptUpdatedRepresentative`
    /// (the `bindingCount` overload).
    pub fn reapply_concept_updated_representative_binding_count(
        &mut self,
        process_indi: NodeId,
        binding_con_des: ConDescId,
        binding_dep_track_point: TrackPointId,
        binding_count: Cint64,
        mut con_set: LabelSetId,
        reapply_queue: CondensedReapplyQueueHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: setIndividualNodeConceptLabelSetModified(processIndi,calcAlgContext);
        // W3-DEFER[api]: conProQueue = processIndi->getConceptProcessingQueue(true);
        let con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        // addConceptPreprocessedToProcessingQueue(bindingConDes,bindingDepTrackPoint,conProQueue,processIndi,bindingCount,calcAlgContext);
        self.add_concept_preprocessed_to_processing_queue(
            binding_con_des,
            binding_dep_track_point,
            con_pro_queue,
            process_indi,
            binding_count,
            calc_alg_context,
        );
        // W3-DEFER[api]: reapplyQueue->isEmpty()
        let reapply_queue_empty = true;
        let _ = reapply_queue;
        if !reapply_queue_empty {
            // W3-DEFER[api]: conSet = processIndi->getReapplyConceptLabelSet(true);
            con_set = Id::NONE;
            // W3-DEFER[api]: CCondensedReapplyQueueIterator reapplyQueueIt(conSet->getConceptReapplyIterator(bindingConDes));
            let reapply_queue_it: CondensedReapplyQueueIteratorHandle = INVALID;
            self.apply_reapply_queue_concepts_condensed_iterator(
                process_indi,
                reapply_queue_it,
                calc_alg_context,
            );
            let _ = con_set;
        }
    }

    // =======================================================================
    // applyReapplyQueueConcepts family (cpp 13876 / 26523 / 26549 / 26572 / 26602).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyReapplyQueueConcepts`
    /// (the `CPropagationBindingReapplyConceptDescriptor*` linker overload, cpp 13876).
    pub fn apply_reapply_queue_concepts_propagation_binding(
        &mut self,
        process_indi: NodeId,
        reapply_des_linker: PropagationBindingReapplyConDescHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // CProcessingRestrictionSpecification* procRest = nullptr;
        // for (reapplyDesLinkerIt = reapplyDesLinker; it; it = it->getNext()) { ... }
        // W3-DEFER[api]: linker-chain traversal (CPropagationBindingReapplyConceptDescriptor not ported).
        let _ = reapply_des_linker;
        let reapply_des_chain: Vec<PropagationBindingReapplyConDescHandle> = Vec::new();
        // process_indi node id (real accessor) is the localisation discriminator below.
        let process_indi_id = calc_alg_context
            .process_context()
            .node(process_indi)
            .individual_node_id();
        for reapply_des in reapply_des_chain {
            // W3-DEFER[api]: STATINC(PBINDREAPPLICATIONCOUNT,calcAlgContext);
            // W3-DEFER[api]: conDes = reapplyDes->getConceptDescriptor();
            let con_des: ConDescId = Id::NONE;
            // W3-DEFER[api]: depTrackPoint = conDes->getDependencyTrackPoint();
            let dep_track_point: TrackPointId = Id::NONE;
            // W3-DEFER[api]: indiNode = reapplyDes->getReapllyIndividualNode();
            let indi_node: NodeId = Id::NONE;
            let mut loc_indi_node = indi_node;

            // W3-DEFER[api]: indiNode->getIndividualNodeID()
            let indi_node_id: Cint64 = INVALID;
            if process_indi_id != indi_node_id {
                // locIndiNode = getLocalizedIndividual(indiNode,true,calcAlgContext);
                loc_indi_node = self.get_localized_individual(indi_node, true, calc_alg_context);
            }

            // W3-DEFER[api]: conProQueue = locIndiNode->getConceptProcessingQueue(true);
            let con_pro_queue: ConceptProcessingQueueId = Id::NONE;
            self.add_concept_restricted_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                loc_indi_node,
                false,
                INVALID,
                calc_alg_context,
            );

            if process_indi_id != indi_node_id {
                self.add_individual_to_processing_queue(loc_indi_node, calc_alg_context);
            }
            let _ = reapply_des;
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyReapplyQueueConcepts`
    /// (the `CConcept*` + `negation` overload, cpp 26523).
    pub fn apply_reapply_queue_concepts_concept(
        &mut self,
        process_indi: NodeId,
        concept: ConceptId,
        negation: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // W3-DEFER[api]: reapplyQueueIt = processIndi->getConceptReapplyIterator(concept,negation,true);
        let reapply_queue_chain: Vec<CondensedReapplyConDescHandle> = Vec::new();
        let mut con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        let mut con_pro_queue_set = false;
        for reapply_concept_des in reapply_queue_chain {
            // W3-DEFER[api]: STATINC(REAPPLIEDCONCEPTSCOUNT,calcAlgContext);
            // W3-DEFER[api]: conDes = reapplyConceptDes->getConceptDescriptor();
            let con_des: ConDescId = Id::NONE;
            // W3-DEFER[api]: depTrackPoint = reapplyConceptDes->getDependencyTrackPoint();
            let dep_track_point: TrackPointId = Id::NONE;
            // W3-DEFER[api]: procRest = reapplyConceptDes->getReapplyProcessingRestriction();
            let proc_rest: ProcRestrictionHandle = INVALID;
            // W3-DEFER[api]: reapplyConceptDes->isExtended()
            let is_extended = false;
            if is_extended {
                self.apply_extended_reapply_concept_descriptor(
                    process_indi,
                    concept,
                    negation,
                    reapply_concept_des,
                    calc_alg_context,
                );
            } else {
                if !con_pro_queue_set {
                    // W3-DEFER[api]: conProQueue = processIndi->getConceptProcessingQueue(true);
                    con_pro_queue = Id::NONE;
                    con_pro_queue_set = true;
                }
                // W3-DEFER[api]: reapplyConceptDes->isStaticDescriptor()
                let is_static_descriptor = false;
                self.add_concept_restricted_to_processing_queue(
                    con_des,
                    dep_track_point,
                    con_pro_queue,
                    process_indi,
                    is_static_descriptor,
                    proc_rest,
                    calc_alg_context,
                );
            }
        }
        if con_pro_queue_set {
            self.add_individual_to_processing_queue(process_indi, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyReapplyQueueConcepts`
    /// (the `CRole*` overload, cpp 26549).
    pub fn apply_reapply_queue_concepts_role(
        &mut self,
        process_indi: NodeId,
        role: RoleId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // W3-DEFER[api]: reapplyQueueIt = processIndi->getRoleReapplyIterator(role,true);
        let _ = role;
        let reapply_queue_chain: Vec<ReapplyConDescHandle> = Vec::new();
        let mut con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        let mut con_pro_queue_set = false;
        for reapply_concept_des in reapply_queue_chain {
            // W3-DEFER[api]: STATINC(REAPPLIEDCONCEPTSCOUNT,calcAlgContext);
            // W3-DEFER[api]: conDes = reapplyConceptDes->getConceptDescriptor();
            let con_des: ConDescId = Id::NONE;
            // W3-DEFER[api]: depTrackPoint = reapplyConceptDes->getDependencyTrackPoint();
            let dep_track_point: TrackPointId = Id::NONE;
            // W3-DEFER[api]: procRest = reapplyConceptDes->getReapplyProcessingRestriction();
            let proc_rest: ProcRestrictionHandle = INVALID;
            if !con_pro_queue_set {
                // W3-DEFER[api]: conProQueue = processIndi->getConceptProcessingQueue(true);
                con_pro_queue = Id::NONE;
                con_pro_queue_set = true;
            }
            // W3-DEFER[api]: reapplyConceptDes->isStaticDescriptor()
            let is_static_descriptor = false;
            self.add_concept_restricted_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                process_indi,
                is_static_descriptor,
                proc_rest,
                calc_alg_context,
            );
            let _ = reapply_concept_des;
        }
        if con_pro_queue_set {
            self.add_individual_to_processing_queue(process_indi, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyReapplyQueueConceptsRestricted`
    /// (the `CReapplyQueueIterator*` + `restrictedLink` overload, cpp 26572).
    pub fn apply_reapply_queue_concepts_restricted(
        &mut self,
        process_indi: NodeId,
        reapply_queue_it: ReapplyQueueIteratorHandle,
        restricted_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let _ = (reapply_queue_it, restricted_link);
        let mut con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        let mut con_pro_queue_set = false;
        // CLinkProcessingRestrictionSpecification* linkProcRest = nullptr;
        let mut link_proc_rest: ProcRestrictionHandle = INVALID;
        // W3-DEFER[api]: iterate reapplyQueueIt->hasNext()/next() (CReapplyQueueIterator not ported).
        let reapply_queue_chain: Vec<ReapplyConDescHandle> = Vec::new();
        for reapply_concept_des in reapply_queue_chain {
            // W3-DEFER[api]: STATINC(REAPPLIEDCONCEPTSCOUNT,calcAlgContext);
            // W3-DEFER[api]: conDes = reapplyConceptDes->getConceptDescriptor();
            let con_des: ConDescId = Id::NONE;
            // W3-DEFER[api]: depTrackPoint = reapplyConceptDes->getDependencyTrackPoint();
            let dep_track_point: TrackPointId = Id::NONE;
            // W3-DEFER[api]: procRest = reapplyConceptDes->getReapplyProcessingRestriction();
            let mut proc_rest: ProcRestrictionHandle = INVALID;
            if !con_pro_queue_set {
                // W3-DEFER[api]: conProQueue = processIndi->getConceptProcessingQueue(true);
                con_pro_queue = Id::NONE;
                con_pro_queue_set = true;
            }
            if proc_rest == INVALID {
                if link_proc_rest == INVALID {
                    // W3-DEFER[memory-pool/api]: linkProcRest = allocateAndConstruct(taskMemMan);
                    //                            linkProcRest->initLinkRestriction(restrictedLink);
                    link_proc_rest = INVALID;
                }
                proc_rest = link_proc_rest;
            }
            // W3-DEFER[api]: reapplyConceptDes->isStaticDescriptor()
            let is_static_descriptor = false;
            self.add_concept_restricted_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                process_indi,
                is_static_descriptor,
                proc_rest,
                calc_alg_context,
            );
            let _ = reapply_concept_des;
        }
        if con_pro_queue_set {
            self.add_individual_to_processing_queue(process_indi, calc_alg_context);
        }
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyReapplyQueueConcepts`
    /// (the `CCondensedReapplyQueueIterator*` overload, cpp 26602).
    pub fn apply_reapply_queue_concepts_condensed_iterator(
        &mut self,
        process_indi: NodeId,
        reapply_queue_it: CondensedReapplyQueueIteratorHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let _ = reapply_queue_it;
        let mut con_pro_queue: ConceptProcessingQueueId = Id::NONE;
        let mut con_pro_queue_set = false;
        // W3-DEFER[api]: iterate reapplyQueueIt->hasNext()/next() (CCondensedReapplyQueueIterator not ported).
        let reapply_queue_chain: Vec<CondensedReapplyConDescHandle> = Vec::new();
        for reapply_concept_des in reapply_queue_chain {
            // W3-DEFER[api]: STATINC(REAPPLIEDCONCEPTSCOUNT,calcAlgContext);
            // W3-DEFER[api]: conDes = reapplyConceptDes->getConceptDescriptor();
            let con_des: ConDescId = Id::NONE;
            // W3-DEFER[api]: depTrackPoint = reapplyConceptDes->getDependencyTrackPoint();
            let dep_track_point: TrackPointId = Id::NONE;
            // W3-DEFER[api]: procRest = reapplyConceptDes->getReapplyProcessingRestriction();
            let proc_rest: ProcRestrictionHandle = INVALID;
            if !con_pro_queue_set {
                // W3-DEFER[api]: conProQueue = processIndi->getConceptProcessingQueue(true);
                con_pro_queue = Id::NONE;
                con_pro_queue_set = true;
            }
            // W3-DEFER[api]: reapplyConceptDes->isStaticDescriptor()
            let is_static_descriptor = false;
            self.add_concept_restricted_to_processing_queue(
                con_des,
                dep_track_point,
                con_pro_queue,
                process_indi,
                is_static_descriptor,
                proc_rest,
                calc_alg_context,
            );
            let _ = reapply_concept_des;
        }
        if con_pro_queue_set {
            self.add_individual_to_processing_queue(process_indi, calc_alg_context);
        }
    }

    // =======================================================================
    // applyExtendedReapplyConceptDescriptor — ATMOST reactivation (cpp 26492).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::applyExtendedReapplyConceptDescriptor`.
    pub fn apply_extended_reapply_concept_descriptor(
        &mut self,
        process_indi: NodeId,
        concept: ConceptId,
        negation: bool,
        reapply_concept_des: CondensedReapplyConDescHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = (process_indi, concept, negation, reapply_concept_des);
        // CExtendedCondensedReapplyConceptDescriptor* extendedReapplyConceptDes = (cast)reapplyConceptDes;
        // W3-DEFER[api]: extendedReapplyConceptDes->getExtentionType() == REAPPLYCONCEPTDESCRIPTOREXTENSIONTYPEATMOST
        let extention_type_is_atmost = false;
        if extention_type_is_atmost {
            // CExtendedCondensedReapplyConceptDescriptorATMOSTReactivation* atmostReapplyConDes = (cast)extendedReapplyConceptDes;
            // W3-DEFER[api]: reapplicationIndiNode = atmostReapplyConDes->getReapplicationIndividualNode();
            let reapplication_indi_node: NodeId = Id::NONE;
            // W3-DEFER[api]: indiLinkEdge = atmostReapplyConDes->getIndividualLink();
            let indi_link_edge: EdgeId = Id::NONE;
            // locReapplicationIndiNode = getLocalizedIndividual(reapplicationIndiNode,true,calcAlgContext);
            let loc_reapplication_indi_node: NodeId =
                self.get_localized_individual(reapplication_indi_node, true, calc_alg_context);

            // W3-DEFER[api]: !locReapplicationIndiNode->hasProcessingRestrictionFlags(PRFPURGEDBLOCKED)
            let _ = IndividualProcessNode::PRF_PURGEDBLOCKED;
            let has_purged_blocked = false;
            if !has_purged_blocked {
                // W3-DEFER[api]: succIndiATMOSTReactivationData = locReapplicationIndiNode->getSuccessorIndividualATMOSTReactivationData(true);
                // W3-DEFER[api]: atmostConDes = atmostReapplyConDes->getConceptDescriptor();
                let atmost_con_des: ConDescId = Id::NONE;
                // W3-DEFER[api]: succIndiATMOSTReactivationData->addReactivationSuccessorIndividualLink(atmostConDes,indiLinkEdge);
                let _ = indi_link_edge;

                // W3-DEFER[api]: role = atmostConDes->getConcept()->getRole();
                let role: RoleId = Id::NONE;
                // W3-DEFER[api]: roleReapplyQueueIt = locReapplicationIndiNode->getRoleReapplyIterator(role,false);
                let role_reapply_queue_chain: Vec<ReapplyConDescHandle> = Vec::new();
                let mut role_queue_reapplied = false;
                let mut role_reapply_iter = role_reapply_queue_chain.into_iter();
                while !role_queue_reapplied {
                    let role_reapply_concept_des = match role_reapply_iter.next() {
                        Some(v) => v,
                        None => break,
                    };
                    // W3-DEFER[api]: roleReapplyConceptDes->getConceptDescriptor() == atmostConDes
                    let role_reapply_con_des: ConDescId = Id::NONE;
                    if role_reapply_con_des == atmost_con_des {
                        self.apply_reapply_queue_concepts_role(
                            loc_reapplication_indi_node,
                            role,
                            calc_alg_context,
                        );
                        role_queue_reapplied = true;
                    }
                    let _ = role_reapply_concept_des;
                }
            }
        }
    }

    // =======================================================================
    // collectReapplyAutomatTransactionsRestrictions — qualified-∀ automaton
    // restriction collector (cpp 22019). Ported against the real ontology arenas.
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::collectReapplyAutomatTransactionsRestrictions`.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `CPROCESSINGHASH<cint64,
    /// CConceptNegationPair>*& conExtensionMap` is a pointer-reference allocated on
    /// first use (`if (!conExtensionMap) conExtensionMap = …`); ported as a
    /// `&mut Option<HashMap<…>>` so the lazy "allocate if null then insert"
    /// semantics survive (`get_or_insert_with(HashMap::new)`).
    pub fn collect_reapply_automat_transactions_restrictions(
        &mut self,
        process_indi: NodeId,
        collecting_role: RoleId,
        concept: ConceptId,
        negated: bool,
        con_extension_map: &mut Option<HashMap<Cint64, ConceptNegationPair>>,
        con_set: ReapplyConceptSaturationLabelSetHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // cint64 opCode = concept->getOperatorCode();
        let _op_code = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        let concept_operator = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_concept_operator();
        let has_aqand = concept_operator.has_partial_operator_code_flag(op::CCFS_AQAND_TYPE);
        let has_all_aqall = concept_operator.has_partial_operator_code_flag(op::CCFS_ALL_AQALL_TYPE);
        let has_some = concept_operator.has_partial_operator_code_flag(op::CCFS_SOME_TYPE);

        if self.conf_specialized_automate_rules && !negated && has_aqand {
            // recurse over operands
            let op_concepts: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            for op_concept in op_concepts {
                self.collect_reapply_automat_transactions_restrictions(
                    process_indi,
                    collecting_role,
                    op_concept.target,
                    op_concept.negated,
                    con_extension_map,
                    con_set,
                    calc_alg_context,
                );
            }
        } else if (!negated && has_all_aqall) || (negated && has_some) {
            // CRole* role = concept->getRole();
            let role = calc_alg_context.ontology_arenas().concept(concept).get_role();
            if role == collecting_role {
                if (!negated && has_all_aqall) || (negated && has_some) {
                    let rea_op_concepts: Vec<NegLink<ConceptId>> = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_operand_list()
                        .to_vec();
                    for rea_op_concept in rea_op_concepts {
                        let rea_op_con_negation = rea_op_concept.negated ^ negated;

                        // W3-DEFER[api]: conSet->containsConcept(reaOpConceptIt->getData(), reaOpConNegation)
                        //   (CReapplyConceptSaturationLabelSet not ported); null conSet => always collect.
                        let con_set_contains_concept = false;
                        if con_set == INVALID || !con_set_contains_concept {
                            // W3-DEFER[api]: STATINC(NODESUCCESSOREXPANSIONSATURATIONRESOLVINGCONCEPTCANDIDATECOUNT,calcAlgContext);
                            // conExtensionMap->insert(reaOp->getConceptTag(), CConceptNegationPair(reaOp, reaOpConNegation));
                            let con_tag = calc_alg_context
                                .ontology_arenas()
                                .concept(rea_op_concept.target)
                                .get_concept_tag();
                            con_extension_map
                                .get_or_insert_with(HashMap::new)
                                .insert(
                                    con_tag,
                                    ConceptNegationPair {
                                        concept: rea_op_concept.target,
                                        negated: rea_op_con_negation,
                                    },
                                );
                        }
                    }
                }
            }
        }
        let _ = process_indi;
    }

    // =======================================================================
    // createNewIndividualsLink{s,}Reapplyed — link creation that re-fires the
    // role-keyed reapply queue (cpp 22295 / 22372).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createNewIndividualsLinksReapplyed`
    /// (the `CSortedNegLinker<CRole*>*` multi-role overload, cpp 22295).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `indiSource`/`indiDestination` are C++
    /// `CIndividualProcessNode*&` (not reassigned here) → `NodeId`. Returns the
    /// created edge for `ancRole` (or `Id::NONE` == `nullptr`).
    pub fn create_new_individuals_links_reapplyed(
        &mut self,
        indi_source: NodeId,
        indi_destination: NodeId,
        role_linker_it: &[NegLink<RoleId>],
        anc_role: RoleId,
        dep_track_point: TrackPointId,
        check_role_existing: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> EdgeId {
        let mut anc_role_link: EdgeId = Id::NONE;
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let mut generated_inv_link = false;

        // W3-DEFER[api]: iterate roleLinkerIt (CSortedNegLinker<CRole*> chain; not ported).
        let _ = role_linker_it;
        let role_chain: Vec<NegLink<RoleId>> = Vec::new();
        for role_link in role_chain {
            let role = role_link.target;
            let inv_role = role_link.negated;
            // W3-DEFER[api]: rangeConLinkerIt = role->getRangeConceptList();
            // W3-DEFER[api]: STATINC(LINKSCREATIONCOUNT,calcAlgContext);
            // W3-DEFER[memory-pool]: individualLink = allocateAndConstructAndParameterize(taskMemMan, getUsedProcessContext());
            let individual_link: EdgeId = Id::NONE;
            if !inv_role {
                // W3-DEFER[api]: !checkRoleExisting || !hasIndividualsLink(indiSource,indiDestination,role,true,calcAlgContext)
                let has_individuals_link = false;
                if !check_role_existing || !has_individuals_link {
                    // W3-DEFER[api]: createIndividualNodeDisjointRolesLinks(indiSource,indiDestination,role->getDisjointRoleList(),depTrackPoint,calcAlgContext);
                    // W3-DEFER[api]: individualLink->initIndividualLinkEdge(indiSource,indiSource,indiDestination,role,depTrackPoint);
                    // W3-DEFER[api]: reapplyIterator = installIndividualNodeRoleLinkReapplied(indiSource,indiDestination,individualLink,calcAlgContext);
                    let reapply_iterator: ReapplyQueueIteratorHandle = INVALID;
                    // W3-DEFER[api]: if (rangeConLinkerIt) addConceptsToIndividual(rangeConLinkerIt,false,indiDestination,depTrackPoint,true,false,nullptr,calcAlgContext);
                    // W3-DEFER[api]: domainConLinkerIt = role->getDomainConceptList(); if (domainConLinkerIt) addConceptsToIndividual(domainConLinkerIt,false,indiSource,...);
                    self.apply_reapply_queue_concepts_restricted(
                        indi_source,
                        reapply_iterator,
                        individual_link,
                        calc_alg_context,
                    );
                }
            } else {
                // W3-DEFER[api]: !checkRoleExisting || !hasIndividualsLink(indiDestination,indiSource,role,true,calcAlgContext)
                let has_individuals_link = false;
                if !check_role_existing || !has_individuals_link {
                    generated_inv_link = true;
                    // W3-DEFER[api]: createIndividualNodeDisjointRolesLinks(indiDestination,indiSource,role->getDisjointRoleList(),depTrackPoint,calcAlgContext);
                    // W3-DEFER[api]: individualLink->initIndividualLinkEdge(indiSource,indiDestination,indiSource,role,depTrackPoint);
                    // W3-DEFER[api]: reapplyIterator = installIndividualNodeRoleLinkReapplied(indiDestination,indiSource,individualLink,calcAlgContext);
                    let reapply_iterator: ReapplyQueueIteratorHandle = INVALID;
                    // W3-DEFER[api]: if (rangeConLinkerIt) addConceptsToIndividual(rangeConLinkerIt,false,indiSource,...);
                    // W3-DEFER[api]: domainConLinkerIt; if present addConceptsToIndividual(domainConLinkerIt,false,indiDestination,...);
                    self.apply_reapply_queue_concepts_restricted(
                        indi_destination,
                        reapply_iterator,
                        individual_link,
                        calc_alg_context,
                    );
                }
            }
            if anc_role == role {
                anc_role_link = individual_link;
            }
        }

        // indiDestination->isNominalIndividualNode() — real accessor.
        let indi_destination_is_nominal = calc_alg_context
            .process_context()
            .node(indi_destination)
            .is_nominal_individual_node();
        // Individual-node ids for the connection-successor inserts (read before the
        // &mut process-context borrow of the lazy connection-successor-set getter).
        let indi_source_id = calc_alg_context
            .process_context()
            .node(indi_source)
            .individual_node_id();
        let indi_destination_id = calc_alg_context
            .process_context()
            .node(indi_destination)
            .individual_node_id();
        if generated_inv_link || indi_destination_is_nominal {
            // indiSource->getConnectionSuccessorSet(true)->insertConnectionSuccessor(indiDestination->getIndividualNodeID());
            let conn_succ_set = calc_alg_context
                .process_context_mut()
                .node_connection_successor_set(indi_source);
            calc_alg_context
                .process_context_mut()
                .conn_succ_set_mut(conn_succ_set)
                .insert_connection_successor(indi_destination_id);
        }
        // indiDestination->getConnectionSuccessorSet(true)->insertConnectionSuccessor(indiSource->getIndividualNodeID());
        let conn_succ_set = calc_alg_context
            .process_context_mut()
            .node_connection_successor_set(indi_destination);
        calc_alg_context
            .process_context_mut()
            .conn_succ_set_mut(conn_succ_set)
            .insert_connection_successor(indi_source_id);
        if self.opt_incremental_compatible_expansion {
            // W3-DEFER[api]: linkCreationDirectlyChangedNeighbourConnectionUpdate(indiDestination,indiSource,true,calcAlgContext);
        }
        anc_role_link
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::createNewIndividualsLinkReapplyed`
    /// (the single-`CRole*` overload, cpp 22372).
    pub fn create_new_individuals_link_reapplyed(
        &mut self,
        indi_creator: NodeId,
        indi_source: NodeId,
        indi_destination: NodeId,
        role: RoleId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> EdgeId {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        let _ = (indi_creator, role, dep_track_point);
        // W3-DEFER[api]: createIndividualNodeDisjointRolesLinks(indiSource,indiDestination,role->getDisjointRoleList(),depTrackPoint,calcAlgContext);
        // CReapplyQueueIterator reapplyIterator;
        // W3-DEFER[api]: STATINC(LINKSCREATIONCOUNT,calcAlgContext);
        // W3-DEFER[memory-pool]: individualLink = allocateAndConstructAndParameterize(taskMemMan, getUsedProcessContext());
        let individual_link: EdgeId = Id::NONE;
        // W3-DEFER[api]: individualLink->initIndividualLinkEdge(indiCreator,indiSource,indiDestination,role,depTrackPoint);
        // W3-DEFER[api]: reapplyIterator = installIndividualNodeRoleLinkReapplied(indiSource,indiDestination,individualLink,calcAlgContext);
        let reapply_iterator: ReapplyQueueIteratorHandle = INVALID;
        // W3-DEFER[api]: rangeConLinkerIt = role->getRangeConceptList();
        //   if (rangeConLinkerIt) addConceptsToIndividual(rangeConLinkerIt,false,indiDestination,depTrackPoint,false,false,nullptr,calcAlgContext);
        // W3-DEFER[api]: domainConLinkerIt = role->getDomainConceptList();
        //   if (domainConLinkerIt) addConceptsToIndividual(domainConLinkerIt,false,indiSource,depTrackPoint,false,false,nullptr,calcAlgContext);
        self.apply_reapply_queue_concepts_restricted(
            indi_source,
            reapply_iterator,
            individual_link,
            calc_alg_context,
        );
        // indiDestination->getConnectionSuccessorSet(true)->insertConnectionSuccessor(indiSource->getIndividualNodeID());
        let indi_source_id = calc_alg_context
            .process_context()
            .node(indi_source)
            .individual_node_id();
        let conn_succ_set = calc_alg_context
            .process_context_mut()
            .node_connection_successor_set(indi_destination);
        calc_alg_context
            .process_context_mut()
            .conn_succ_set_mut(conn_succ_set)
            .insert_connection_successor(indi_source_id);
        if self.opt_incremental_compatible_expansion {
            // W3-DEFER[api]: linkCreationDirectlyChangedNeighbourConnectionUpdate(indiDestination,indiSource,true,calcAlgContext);
        }
        individual_link
    }

    // =======================================================================
    // addConceptToReapplyQueue overloads (cpp 26625 / 26632 / 26642 / 26653 / 26671).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToReapplyQueue`
    /// (the 3-arg dispatcher that derives the role from the concept, cpp 26625).
    pub fn add_concept_to_reapply_queue(
        &mut self,
        concept_descriptor: ConDescId,
        process_indi: NodeId,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[api]: concept = conceptDescriptor->getConcept();
        let concept: ConceptId = Id::NONE;
        // role = concept->getRole();  (resolved against the ontology arenas once conceptDescriptor->getConcept() is surfaced)
        // W3-DEFER[api]: role = concept->getRole();
        let role: RoleId = Id::NONE;
        let _ = concept;
        self.add_concept_to_reapply_queue_role(
            concept_descriptor,
            role,
            process_indi,
            true,
            dependency_track_point,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToReapplyQueue`
    /// (the `CRole*` + `isStaticDes` overload, cpp 26632).
    pub fn add_concept_to_reapply_queue_role(
        &mut self,
        concept_descriptor: ConDescId,
        role: RoleId,
        process_indi: NodeId,
        is_static_des: bool,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // W3-DEFER[api]: STATINC(INSERTCONCEPTREAPPLICATIONSCOUNT,calcAlgContext);
        // W3-DEFER[api]: reapplyQueue = processIndi->getRoleReapplyQueue(role,true);
        let reapply_queue: ReapplyQueueHandle = INVALID;
        // W3-DEFER[memory-pool/api]: reapplyConDes = allocateAndConstruct(taskMemMan);
        //                            reapplyConDes->initReapllyDescriptor(conceptDescriptor,dependencyTrackPoint,isStaticDes);
        //                            reapplyQueue->addReapplyConceptDescriptor(reapplyConDes);
        let _ = (
            concept_descriptor,
            role,
            process_indi,
            is_static_des,
            dependency_track_point,
            reapply_queue,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToReapplyQueue`
    /// (the `CConcept*` + `negation` + `isStaticDes` overload, cpp 26642).
    pub fn add_concept_to_reapply_queue_concept(
        &mut self,
        concept_descriptor: ConDescId,
        concept: ConceptId,
        negation: bool,
        process_indi: NodeId,
        is_static_des: bool,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // W3-DEFER[api]: STATINC(INSERTCONCEPTREAPPLICATIONSCOUNT,calcAlgContext);
        // W3-DEFER[api]: reapplyQueue = processIndi->getConceptReapplyQueue(concept,negation,true);
        let reapply_queue: CondensedReapplyQueueHandle = INVALID;
        // W3-DEFER[memory-pool/api]: reapplyConDes = allocateAndConstruct(taskMemMan);
        //                            reapplyConDes->initReapllyDescriptor(conceptDescriptor,dependencyTrackPoint,!negation);
        //                            reapplyQueue->addReapplyConceptDescriptor(reapplyConDes);
        let _ = (
            concept_descriptor,
            concept,
            negation,
            process_indi,
            is_static_des,
            dependency_track_point,
            reapply_queue,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToReapplyQueue`
    /// (the `CRole*` + `CProcessingRestrictionSpecification*` overload, cpp 26653).
    pub fn add_concept_to_reapply_queue_role_restricted(
        &mut self,
        concept_descriptor: ConDescId,
        role: RoleId,
        process_indi: NodeId,
        proc_rest: ProcRestrictionHandle,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // W3-DEFER[api]: STATINC(INSERTCONCEPTREAPPLICATIONSCOUNT,calcAlgContext);
        // W3-DEFER[api]: reapplyQueue = processIndi->getRoleReapplyQueue(role,true);
        let reapply_queue: ReapplyQueueHandle = INVALID;
        // W3-DEFER[memory-pool/api]: reapplyConDes = allocateAndConstruct(taskMemMan);
        //                            reapplyConDes->initReapllyDescriptor(conceptDescriptor,dependencyTrackPoint,procRest);
        //                            reapplyQueue->addReapplyConceptDescriptor(reapplyConDes);
        let _ = (
            concept_descriptor,
            role,
            process_indi,
            proc_rest,
            dependency_track_point,
            reapply_queue,
            calc_alg_context,
        );
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::addConceptToReapplyQueue`
    /// (the `CConcept*` + `negation` + `CProcessingRestrictionSpecification*` overload, cpp 26671).
    pub fn add_concept_to_reapply_queue_concept_restricted(
        &mut self,
        concept_descriptor: ConDescId,
        concept: ConceptId,
        negation: bool,
        process_indi: NodeId,
        proc_rest: ProcRestrictionHandle,
        dependency_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager();
        // W3-DEFER[api]: STATINC(INSERTCONCEPTREAPPLICATIONSCOUNT,calcAlgContext);
        // W3-DEFER[api]: reapplyQueue = processIndi->getConceptReapplyQueue(concept,negation,true);
        let reapply_queue: CondensedReapplyQueueHandle = INVALID;
        // W3-DEFER[memory-pool/api]: reapplyConDes = allocateAndConstruct(taskMemMan);
        //                            reapplyConDes->initReapllyDescriptor(conceptDescriptor,dependencyTrackPoint,!negation,procRest);
        //                            reapplyQueue->addReapplyConceptDescriptor(reapplyConDes);
        let _ = (
            concept_descriptor,
            concept,
            negation,
            process_indi,
            proc_rest,
            dependency_track_point,
            reapply_queue,
            calc_alg_context,
        );
    }

    // =======================================================================
    // isConceptInReapplyQueue overloads (cpp 26674 / 26682).
    // =======================================================================

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isConceptInReapplyQueue`
    /// (the `CConcept*` + `negation` overload, cpp 26674).
    pub fn is_concept_in_reapply_queue_concept(
        &mut self,
        concept_descriptor: ConDescId,
        concept: ConceptId,
        negation: bool,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[api]: reapplyQueue = processIndi->getConceptReapplyQueue(concept,negation,false);
        let reapply_queue: CondensedReapplyQueueHandle = INVALID;
        let _ = (concept_descriptor, concept, negation, process_indi, calc_alg_context);
        if reapply_queue != INVALID {
            // W3-DEFER[api]: return reapplyQueue->hasConceptDescriptor(conceptDescriptor);
            return false;
        }
        false
    }

    /// Port of `CCalculationTableauCompletionTaskHandleAlgorithm::isConceptInReapplyQueue`
    /// (the `CRole*` overload, cpp 26682).
    pub fn is_concept_in_reapply_queue_role(
        &mut self,
        concept_descriptor: ConDescId,
        role: RoleId,
        process_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // W3-DEFER[api]: reapplyQueue = processIndi->getRoleReapplyQueue(role,false);
        let reapply_queue: ReapplyQueueHandle = INVALID;
        let _ = (concept_descriptor, role, process_indi, calc_alg_context);
        if reapply_queue != INVALID {
            // W3-DEFER[api]: return reapplyQueue->hasConceptDescriptor(conceptDescriptor);
            return false;
        }
        false
    }

    // =======================================================================
    // Rule-counter getters (cpp 27650–27676): ALREADY ported as inline accessors
    // in `completion/algorithm.rs` (`applied_and_rule_count()` ..
    // `applied_total_rule_count()`); not re-defined here to avoid a duplicate
    // method definition on the shared impl.
    // =======================================================================
}
