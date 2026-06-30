//! `completion::u35` — Generic helpers / accessors / label tests, batch
//! (port unit #35 of 36).
//!
//! Faithful port of the 35 methods the manifest (`01-completion-methods.md`,
//! "Unit 35") groups under the node-construction + label-test helpers of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`.
//! cpp source line ranges (1-based) are noted on each item.
//!
//! Methods (cpp order):
//!   * `generateDebugIndividualNodeAssociatedConceptsString`              [18390–18409]
//!   * `generateDebugIndividualNodeAssociatedConceptsSetString`          [18414–18425]
//!   * `generateDebugIndividualNodesListAssociatedConceptsSetString`     [18430–18462]
//!   * `containsIndividualNodeConcept` ×2                                 [18786–18805]
//!   * `containsIndividualNodeConcepts` ×5                               [18808–18879]
//!   * `addIndividualNodeCandidateForConcept` ×2                          [19543–19568]
//!   * `propagateIndividualNodeModified`                                  [19634–19688]
//!   * `pruneSuccessors`                                                  [19699–19758]
//!   * `hasAncestorIndividualNode`                                        [20117–20122]
//!   * `hasRoleSuccessorConcept`                                          [20125–20140]
//!   * `hasRoleSuccessorConcepts`                                         [20142–20167]
//!   * `getRoleSuccessorWithConcepts`                                     [20170–20193]
//!   * `hasDistinctRoleSuccessorConcepts`                                 [20198–20238]
//!   * `createIndividualNodeDisjointRolesLinks`                           [20241–20270]
//!   * `createIndividualNodeNegationLink`                                 [20274–20295]
//!   * `tryExtendFunctionalSuccessorIndividual`                           [21565–21632]
//!   * `createSuccessorIndividual`                                        [21635–21670]
//!   * `createDistinctSuccessorIndividuals`                               [22143–22186]
//!   * `createNewIndividualsLinks`                                        [22212–22247]
//!   * `installIndividualNodeRoleLink`                                    [22251–22269]
//!   * `installIndividualNodeRoleLinkReapplied`                           [22272–22292]
//!   * `createNewIndividualsLink`                                         [22355–22369]
//!   * `createIndividualsDistinct` ×2                                     [22401–22430]
//!   * `hasIndividualsLink`                                               [22433–22435]
//!   * `createNewEmptyIndividual`                                         [22439–22458]
//!   * `createNewIndividual`                                              [22462–22475]
//!   * `getAvailableUpToDateIndividual`                                   [22477–22482]
//!   * `getUpToDateIndividual(CIndividualProcessNode*)`                   [22485–22493]
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauCompletionTaskHandleAlgorithm`, so it becomes `&mut self`
//! plus the threaded per-thread context `calc_alg_context: &mut
//! CalculationAlgorithmContextBase`. C++ `CIndividualProcessNode*&` in/out
//! pointer-references become `&mut NodeId`; a plain value `CIndividualProcessNode*`
//! → `NodeId`; `CConcept*` → `ConceptId`; `CRole*` → `RoleId`;
//! `CSortedNegLinker<CConcept*>*` / `CSortedNegLinker<CRole*>*` → the read-only
//! ontology operand slices `&[NegLink<ConceptId>]` / `&[NegLink<RoleId>]` (the
//! C++ intrusive linker over the static terminology — `model/concept.rs`'s
//! `get_operand_list`, `model/role.rs`'s `get_disjoint_role_list` etc. already
//! return these slices); `CConceptDescriptor*` → `ConDescId`;
//! `CDependencyTrackPoint*` → `TrackPointId`; `CIndividualLinkEdge*` → `EdgeId`;
//! `CIndividualSaturationProcessNode*` → `SatNodeId`; an out `bool*` →
//! `Option<&mut bool>`; `CPROCESSINGLIST<CIndividualProcessNode*>&` →
//! `&mut Vec<NodeId>`. The per-test arenas resolve through the context
//! (`calc_alg_context.process_context()` / `_mut()`), the databox as
//! `calc_alg_context.processing_data_box{,_mut}()`, the static terminology as
//! `calc_alg_context.ontology_arenas()`.
//!
//! KONCLUDE-PORT-NOTE[overload]: the 9 overloaded C++ names (`containsIndividualNode-
//! Concept(s)`, `addIndividualNodeCandidateForConcept`, `createIndividualsDistinct`)
//! get distinct Rust names with a parameter-describing suffix; each keeps its
//! `/// Port of …` anchor so the method-by-method diff is preserved.
//!
//! Deferral landscape. The label/predicate tests
//! (`containsIndividualNodeConcept(s)`, `hasAncestorIndividualNode`,
//! `hasIndividualsLink`) are FULLY PORTED — they bottom out in the ported
//! `CReapplyConceptLabelSet` (`contains_concept{,_get_negated}`) + node accessors
//! (`get_reapply_concept_label_set`, `get_ancestor_link`,
//! `has_role_successor_to_individual_id`). The node/edge GENERATORS
//! (`create*Individual*`, `installIndividualNodeRoleLink*`, the disjoint/negation
//! edges, `propagateIndividualNodeModified`, `pruneSuccessors`, the role-successor
//! concept scanners) are driven by not-yet-ported subsystems: the per-test edge
//! allocators (`CIndividualLinkEdge`/`CNegationDisjointEdge`/`CDistinctEdge`
//! `init*` — though `alloc_edge`/`alloc_distinct_edge`/`alloc_disjoint_edge` exist,
//! their `init*` bodies are W2-DEFER), the clash-descriptor factory + the
//! `CCalculationClashProcessingException` throw (Unit 30, `[exceptions]`), the
//! reapply-queue iterator (`CReapplyQueueIterator`), the saturation-caching
//! expansion helpers (`tryExpansionFromSaturatedData`/`tryEstablishSaturationCaching`/
//! `getCreationSuccessorSaturationNode`), the SOME/ALL dependency creators (Unit 29),
//! the cross-unit siblings (`addConceptToIndividual(s)` Unit 36,
//! `getSuccessorIndividual`/`getLocalizedIndividual`/`getLocalizedSuccessorIndividual`
//! Unit 36, `isNominalIndividualNodeAvailable` Unit 36, the queue-add /
//! processing-restriction-propagation helpers Unit 1/3, `eliminiateBlockedIndividuals`),
//! and the blocking-candidate hash. Following the porting convention each such
//! method keeps its faithful signature + a structural transcription of the C++ so a
//! later wave fills it without re-reading the source; logic is documented, never
//! silently dropped.

#![allow(dead_code)]
#![allow(unused_variables)]

use super::super::model::substrate::{Id, NegLink};
use super::super::model::{Cint64, ConceptId, RoleId, INVALID};
use super::super::process::node::IndividualProcessNode;
use super::super::process::{
    ConDescId, EdgeId, LabelSetId, NodeId, SatNodeId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;

/// `CReapplyQueueIterator` — the reapply-queue cursor `installIndividualNodeRole-
/// LinkReapplied` returns. KONCLUDE-PORT-NOTE[api]: the iterator value type is not
/// yet ported; kept as an opaque `Cint64` handle (`INVALID` == default-constructed).
type ReapplyQueueIterator = Cint64;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Debug associated-concepts string builders (cpp 18390–18462).
    //
    // PORT-PENDING: pure Qt-string instrumentation over `QSet<CConcept*>` /
    // `QMap<cint64,QString>` / `QSet<QList<QSet<CConcept*>>>` aggregates that are
    // not represented in the port (the associated-concept sets are debug-only,
    // never threaded through an arena id). Each reads `concept->getConceptTag()`
    // (`ctx.ontology_arenas().concept(id).get_concept_tag()`) and joins per the
    // C++; held PORT-PENDING until the debug aggregate types land.
    // =======================================================================

    /// Port of `generateDebugIndividualNodeAssociatedConceptsString`. cpp 18390–18409.
    ///
    /// C++: builds a `QMap<cint64,QString>` keyed by `concept->getConceptTag()`
    /// (value = the tag rendered as text), joins the values with ", ", returns
    /// `"<indiNodeId> : {<joined>}"`.
    pub fn generate_debug_individual_node_associated_concepts_string(
        &mut self,
        indi_node_id: Cint64,
        associated_concepts: &[ConceptId],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // PORT-PENDING: faithful transcription of cpp 18390–18409.
        //   conTagConceptStringMap: BTreeMap<Cint64,String> (QMap = ordered);
        //   for concept in associated_concepts:
        //       tag = ctx.ontology_arenas().concept(concept).get_concept_tag();
        //       conTagConceptStringMap.insert(tag, tag.to_string());
        //   conceptsString = conTagConceptStringMap.values().join(", ");
        //   return format!("{} : {{{}}}", indi_node_id, conceptsString);
        let _ = (indi_node_id, associated_concepts);
        String::new()
    }

    /// Port of `generateDebugIndividualNodeAssociatedConceptsSetString`. cpp 18414–18425.
    ///
    /// C++: for each `QSet<CConcept*>` in the all-variable-mappings set, renders it
    /// via `generateDebugIndividualNodeAssociatedConceptsString(individualNode->
    /// getIndividualNodeID(), …)`, joins the lines with "<br>\n".
    pub fn generate_debug_individual_node_associated_concepts_set_string(
        &mut self,
        individual_node: &mut NodeId,
        all_variable_mappings_associated_concepts_set: &[Vec<ConceptId>],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // PORT-PENDING: faithful transcription of cpp 18414–18425.
        //   indiNodeId = ctx.process_context().node(*individual_node).individual_node_id();
        //   for set in all_variable_mappings_associated_concepts_set:
        //       lines.push(self.generate_debug_individual_node_associated_concepts_string(indiNodeId, set, ctx));
        //   return lines.join("<br>\n");
        let _ = (individual_node, all_variable_mappings_associated_concepts_set);
        String::new()
    }

    /// Port of `generateDebugIndividualNodesListAssociatedConceptsSetString`. cpp 18430–18462.
    ///
    /// C++: for each node-list in the over-nodes-list set, emits the node line, the
    /// predecessor (ancestor) line, then one "nominal node …" line per dependent
    /// nominal id; joins each list with "  |||  " and the lists with "<br>\n".
    pub fn generate_debug_individual_nodes_list_associated_concepts_set_string(
        &mut self,
        individual_node: &mut NodeId,
        ancestor_individual_node: &mut NodeId,
        dependent_nominal_id_list: &[Cint64],
        all_variable_mappings_associated_concepts_over_nodes_list_set: &[Vec<Vec<ConceptId>>],
        node_naming: &str,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> String {
        // PORT-PENDING: faithful transcription of cpp 18430–18462 (the three-part
        // per-node-list rendering: "<naming> node …", "<naming> predecessor …",
        // then "nominal node …" per dependent nominal id). Held PORT-PENDING with
        // the debug aggregate types.
        let _ = (
            individual_node,
            ancestor_individual_node,
            dependent_nominal_id_list,
            all_variable_mappings_associated_concepts_over_nodes_list_set,
            node_naming,
        );
        String::new()
    }

    // =======================================================================
    // Label-set concept-containment tests (cpp 18786–18879). FULLY PORTED.
    // =======================================================================

    /// Port of `containsIndividualNodeConcept(CIndividualProcessNode*&, CConcept*,
    /// bool*)`. cpp 18786–18789.
    pub fn contains_individual_node_concept(
        &mut self,
        test_indi: &mut NodeId,
        con_test: ConceptId,
        contains_negation: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*test_indi)
            .get_reapply_concept_label_set(false);
        self.contains_individual_node_concept_label(con_label_set, con_test, contains_negation, calc_alg_context)
    }

    /// Port of `containsIndividualNodeConcept(CReapplyConceptLabelSet*, CConcept*,
    /// bool*)`. cpp 18792–18805.
    pub fn contains_individual_node_concept_label(
        &mut self,
        con_label_set: LabelSetId,
        con_test: ConceptId,
        contains_negation: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut contains_neg = false;
        if !calc_alg_context
            .process_context()
            .label_set(con_label_set)
            .contains_concept_get_negated(con_test, Some(&mut contains_neg))
        {
            return false;
        }
        if let Some(out) = contains_negation {
            *out = contains_neg;
        }
        true
    }

    /// Port of `containsIndividualNodeConcepts(CReapplyConceptLabelSet*,
    /// CSortedNegLinker<CConcept*>*, bool* containsNegation)`. cpp 18808–18849.
    pub fn contains_individual_node_concepts_label_get_negated(
        &mut self,
        con_label_set: LabelSetId,
        con_test_linker: &[NegLink<ConceptId>],
        contains_negation: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut contains_negation = contains_negation;
        let mut contains_all_negated = true;
        let mut contains_all_non_negated = true;
        if con_test_linker.is_empty() {
            // interpret as top
            if let Some(out) = contains_negation.as_deref_mut() {
                *out = false;
            }
            contains_all_negated = false;
        }
        let mut idx = 0usize;
        while idx < con_test_linker.len() && (contains_all_negated || contains_all_non_negated) {
            let concept = con_test_linker[idx].target;
            let con_neg = con_test_linker[idx].negated;
            let mut contains_neg = false;
            if !calc_alg_context
                .process_context()
                .label_set(con_label_set)
                .contains_concept_get_negated(concept, Some(&mut contains_neg))
            {
                return false;
            }
            if contains_neg == con_neg {
                contains_all_negated = false;
            } else {
                contains_all_non_negated = false;
            }
            idx += 1;
        }
        if let Some(out) = contains_negation.as_deref_mut() {
            if contains_all_negated {
                *out = true;
                return true;
            }
            if contains_all_non_negated {
                *out = false;
                return true;
            }
        }
        if contains_all_non_negated {
            return true;
        }
        if contains_all_negated {
            return true;
        }
        false
    }

    /// Port of `containsIndividualNodeConcepts(CReapplyConceptLabelSet*,
    /// CSortedNegLinker<CConcept*>*, bool negated)`. cpp 18852–18862.
    pub fn contains_individual_node_concepts_label_negated(
        &mut self,
        con_label_set: LabelSetId,
        con_test_linker: &[NegLink<ConceptId>],
        negated: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        for nl in con_test_linker {
            let concept = nl.target;
            let con_neg = nl.negated ^ negated;
            if !calc_alg_context
                .process_context()
                .label_set(con_label_set)
                .contains_concept(concept, con_neg)
            {
                return false;
            }
        }
        true
    }

    /// Port of `containsIndividualNodeConcepts(CIndividualProcessNode*&,
    /// CSortedNegLinker<CConcept*>*, bool negated)`. cpp 18865–18868.
    pub fn contains_individual_node_concepts_negated(
        &mut self,
        test_indi: &mut NodeId,
        con_test_linker: &[NegLink<ConceptId>],
        negated: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*test_indi)
            .get_reapply_concept_label_set(false);
        self.contains_individual_node_concepts_label_negated(con_label_set, con_test_linker, negated, calc_alg_context)
    }

    /// Port of `containsIndividualNodeConcepts(CIndividualProcessNode*&,
    /// CSortedNegLinker<CConcept*>*, bool* containsNegation)`. cpp 18870–18873.
    pub fn contains_individual_node_concepts_get_negated(
        &mut self,
        test_indi: &mut NodeId,
        con_test_linker: &[NegLink<ConceptId>],
        contains_negation: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*test_indi)
            .get_reapply_concept_label_set(false);
        self.contains_individual_node_concepts_label_get_negated(con_label_set, con_test_linker, contains_negation, calc_alg_context)
    }

    /// Port of `containsIndividualNodeConcepts(CIndividualProcessNode*&,
    /// CSortedNegLinker<CConcept*>*)`. cpp 18876–18879.
    pub fn contains_individual_node_concepts(
        &mut self,
        test_indi: &mut NodeId,
        con_test_linker: &[NegLink<ConceptId>],
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let con_label_set = calc_alg_context
            .process_context_mut()
            .node_mut(*test_indi)
            .get_reapply_concept_label_set(false);
        // C++ passes (bool*)nullptr.
        self.contains_individual_node_concepts_label_get_negated(con_label_set, con_test_linker, None, calc_alg_context)
    }

    // =======================================================================
    // Anywhere-blocking candidate-hash registration (cpp 19543–19568).
    // =======================================================================

    /// Port of `addIndividualNodeCandidateForConcept(CIndividualProcessNode*&,
    /// CConceptDescriptor*)`. cpp 19543–19549.
    ///
    /// C++: fetches the databox blocking-candidate hash, gets/creates the
    /// `CBlockingIndividualNodeCandidateData` for `conDes`, and inserts `indi`.
    pub fn add_individual_node_candidate_for_concept_descriptor(
        &mut self,
        indi: &mut NodeId,
        con_des: ConDescId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 19543–19549.
        //   procDataBox = calc_alg_context.processing_data_box_mut();
        //   blockingCandHash = procDataBox.get_blocking_individual_node_candidate_hash(true);
        //   blockingCandData = blockingCandHash.get_blocking_individual_candidate_data(con_des, true);
        //   STATINC(ANYWHEREBLOCKINGCANDIDATEHASHUDATEADDCOUNT);
        //   blockingCandData.insert_blocking_candidate_individual_node(*indi);
        //
        // Held PORT-PENDING: `CBlockingIndividualNodeCandidateHash` /
        // `CBlockingIndividualNodeCandidateData` accessors are not yet ported (the
        // databox exposes the hash field but not the candidate-data get/insert API).
        let _ = (indi, con_des);
    }

    /// Port of `addIndividualNodeCandidateForConcept(CIndividualProcessNode*&,
    /// CSortedNegLinker<CConcept*>*, bool negated)`. cpp 19552–19568.
    ///
    /// C++: per concept in the linker (negation XOR `negated`), inserts `indi` into
    /// the concept's candidate-data; for a non-negated `CCAND` / negated `CCOR`
    /// operand it recurses into the operand list (same polarity).
    pub fn add_individual_node_candidate_for_concept(
        &mut self,
        indi: &mut NodeId,
        concepts: &[NegLink<ConceptId>],
        negated: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 19552–19568.
        //   blockingCandHash = calc_alg_context.processing_data_box_mut().get_blocking_individual_node_candidate_hash(true);
        //   for nl in concepts:
        //       concept = nl.target; conceptNeg = nl.negated ^ negated;
        //       data = blockingCandHash.get_blocking_individual_candidate_data(concept, conceptNeg, true);
        //       STATINC(ANYWHEREBLOCKINGCANDIDATEHASHUDATEADDCOUNT);
        //       data.insert_blocking_candidate_individual_node(*indi);
        //       opCode = ctx.ontology_arenas().concept(concept).get_operator_code();
        //       if (!conceptNeg && opCode == CCAND) || (conceptNeg && opCode == CCOR):
        //           self.add_individual_node_candidate_for_concept(indi, ctx.ontology_arenas().concept(concept).get_operand_list(), conceptNeg, ctx);
        //
        // Held PORT-PENDING with the blocking-candidate hash/data API (as above);
        // the concept-arena reads (`get_operator_code`/`get_operand_list`, CCAND/CCOR)
        // become live on the reconcile pass.
        let _ = (indi, concepts, negated);
    }

    // =======================================================================
    // Modification propagation + successor pruning (cpp 19634–19758).
    // =======================================================================

    /// Port of `propagateIndividualNodeModified`. cpp 19634–19688.
    ///
    /// Marks `indi` for the full battery of retest-due-to-direct-modification
    /// processing-restriction flags (saturation-blocking-cache retest, direct
    /// blocking retest + successor propagation, satisfiable / signature-blocking /
    /// completion-graph / saturation-blocking cache retests, backend-synchronisation
    /// retest, incremental-compatibility retest), queues it onto the matching review
    /// queue, and re-queues a delayed nominal node.
    pub fn propagate_individual_node_modified(
        &mut self,
        indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 19634–19688.
        // The node processing-restriction-flag reads/writes are substrate-resolvable
        // (`has_partial_processing_restriction_flags`/`add_processing_restriction_flags`
        // + the `PRF_*` consts on `IndividualProcessNode`); the structure is:
        //
        //   addIndividualToProcessingQueueDueToModification = false;
        //   if !indi.has_partial(PRF_SATURATIONBLOCKINGCACHEDRETESTDUETOMODIFICATION):
        //       indi.add(PRF_SATURATIONBLOCKINGCACHEDRETESTDUETOMODIFICATION);
        //   if !indi.has_partial(PRF_BLOCKINGRETESTDUEDIRECTMODIFIED) && !indi.nominal_individual():
        //       indi.add(PRF_BLOCKINGRETESTDUEDIRECTMODIFIED);
        //       self.propagate_processing_restriction_to_successors(indi, PRF_BLOCKINGRETESTDUEANCESTORMODIFIED, true,
        //           PRF_DIRECTBLOCKED | PRF_INDIRECTBLOCKED | PRF_PROCESSINGBLOCKED, ctx);   // Unit 1
        //       addIndividualToProcessingQueueDueToModification = true;
        //   self.eliminiate_blocked_individuals(indi, ctx);                                  // Unit 3
        //   if indi.has_partial(PRF_SATISFIABLECACHED) && !indi.has_partial(PRF_RETESTSATISFIABLECACHEDDUEDIRECTMODIFIED):
        //       indi.add(PRF_RETESTSATISFIABLECACHEDDUEDIRECTMODIFIED); addIndividualToProcessingQueueDueToModification = true;
        //   if indi.has_partial(PRF_SIGNATUREBLOCKINGCACHED) && !indi.has_partial(PRF_RETESTSIGNATUREBLOCKINGCACHEDDUEDIRECTMODIFIED):
        //       indi.add(PRF_RETESTSIGNATUREBLOCKINGCACHEDDUEDIRECTMODIFIED); addIndividualToProcessingQueueDueToModification = true;
        //   if indi.has_partial(PRF_COMPLETIONGRAPHCACHED) && !indi.has_partial(PRF_RETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED):
        //       indi.add(PRF_RETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED); addIndividualToProcessingQueueDueToModification = true;
        //   if indi.has_partial(PRF_SATURATIONBLOCKINGCACHED) && !indi.has_partial(PRF_RETESTSATURATIONBLOCKINGCACHEDDUEDIRECTMODIFIED):
        //       indi.add(PRF_RETESTSATURATIONBLOCKINGCACHEDDUEDIRECTMODIFIED); addIndividualToProcessingQueueDueToModification = true;
        //   if addIndividualToProcessingQueueDueToModification:
        //       self.add_individual_to_blocking_update_review_processing_queue(indi, ctx);   // Unit 3
        //   if indi.has_partial(PRF_SYNCHRONIZEDBACKEND | …SUCCESSOREXPANSIONBLOCKED | …NEIGHBOUREXPANSIONBLOCKED |
        //         PRF_SYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION | …INDIRECTNOMINALEXPANSIONBLOCKED)
        //         && !indi.has_partial(PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED):
        //       indi.add(PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED);
        //       if !addIndividualToProcessingQueueDueToModification: self.add_individual_to_backend_synchronisation_retest_queue(indi, ctx);  // Unit 3
        //   if indi.has_partial(PRF_SYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION) && !indi.has_partial(PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED)
        //         && !indi.has_partial(PRF_SYNCHRONIZEDBACKENNEIGHBOURDFULLEXPANSION):
        //       indi.add(PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED);
        //       if !addIndividualToProcessingQueueDueToModification: self.add_individual_to_backend_direct_influence_expansion_queue(indi, ctx);  // Unit 3
        //   if self.opt_incremental_compatible_expansion && indi.has_partial(PRF_INCREMENTALEXPANDING) && !indi.has_partial(PRF_INCREMENTALEXPANSIONRETESTDUEDIRECTMODIFIED):
        //       indi.add(PRF_INCREMENTALEXPANSIONRETESTDUEDIRECTMODIFIED);
        //       self.add_individual_to_incremental_compatibility_checking_queue(indi, ctx);  // Unit 26
        //   if indi.is_nominal_individual_node() && indi.nominal_individual() && indi.is_delayed_nominal_processing_queued():
        //       indi.set_delayed_nominal_processing_queued(false);
        //       self.add_individual_to_processing_queue(indi, ctx);                          // Unit 1
        //
        // Held PORT-PENDING: the queue-add + processing-restriction-propagation
        // siblings (`propagate_processing_restriction_to_successors`,
        // `eliminiate_blocked_individuals`, `add_individual_to_*_queue`, Units 1/3/26)
        // are not yet ported; the node flag ops + `self.opt_incremental_compatible_expansion`
        // become live on the reconcile pass. NOTE `mOptIncrementalCompatibleExpansion`
        // is `self.opt_incremental_compatible_expansion`.
        let _ = indi;
    }

    /// Port of `pruneSuccessors`. cpp 19699–19758.
    ///
    /// Marks `indi` purge-blocked + eliminates its blocked individuals; when
    /// `remove_nominal_links` removes every (non-ancestor) nominal connection in
    /// both the connection-successor set and the successor iterator; then recurses
    /// into each strictly-deeper blockable, not-already-purged successor it created.
    pub fn prune_successors(
        &mut self,
        indi: &mut NodeId,
        ancestor_indi: NodeId,
        remove_nominal_links: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 19699–19758.
        //   indi.add(PRF_PURGEDBLOCKED);
        //   self.eliminiate_blocked_individuals(indi, ctx);                                  // Unit 3
        //   if remove_nominal_links && ancestor_indi.is_some():
        //       ancIndiID = ctx...node(ancestor_indi).individual_node_id();
        //       connSuccSet = node_mut(*indi).get_connection_successor_set(false);
        //       if connSuccSet && connSuccSet.get_connection_successor_count() > 0:
        //           for connID in connSuccSet.iterator():
        //               if ancIndiID != connID:
        //                   nomIndi = self.get_up_to_date_individual_by_id(connID, ctx);      // Unit 36
        //                   if nomIndi.is_nominal_individual_node():
        //                       locNomIndi = self.get_localized_individual(nomIndi, false, ctx);  // Unit 36
        //                       for link in locNomIndi.successor_role_iterator(*indi): locNomIndi.remove_individual_link(link);
        //                       locNomIndi.remove_individual_connection(*indi);
        //       for succLink in node(*indi).successor_iterator():
        //           succIndi = self.get_successor_individual(indi, succLink, ctx);            // Unit 36
        //           if succIndi.is_nominal_individual_node() && succIndi.id() != ancIndiID:
        //               locNomIndi = self.get_localized_individual(succIndi, false, ctx);
        //               for link in locNomIndi.successor_role_iterator(*indi): locNomIndi.remove_individual_link(link);
        //               locNomIndi.remove_individual_connection(*indi);
        //   ancDepth = node(*indi).individual_ancestor_depth();
        //   for succLink in node(*indi).successor_iterator():
        //       if edge(succLink).get_creator_individual().id() == node(*indi).id():
        //           succIndi = self.get_successor_individual(indi, succLink, ctx);
        //           if succIndi.individual_ancestor_depth() > ancDepth:
        //               if succIndi.is_blockable_individual() && !succIndi.has_purged_blocked_processing_restriction_flags():
        //                   locSuccIndi = self.get_localized_individual(succIndi, false, ctx);
        //                   self.prune_successors(locSuccIndi, *indi, true, ctx);             // recurse
        //
        // Held PORT-PENDING: the successor/connection/successor-role iterators
        // (`CSuccessorIterator`/`CConnectionSuccessorSetIterator`/`CSuccessorRoleIterator`),
        // `eliminiate_blocked_individuals` (Unit 3), and the cross-unit individual
        // resolvers `get_up_to_date_individual_by_id`/`get_localized_individual`/
        // `get_successor_individual` (Unit 36). The node flag op + ancestor-depth
        // reads are substrate-resolvable on the reconcile pass.
        let _ = (indi, ancestor_indi, remove_nominal_links);
    }

    // =======================================================================
    // Ancestor + role-successor concept scanners (cpp 20117–20238).
    // =======================================================================

    /// Port of `hasAncestorIndividualNode`. cpp 20117–20122. FULLY PORTED.
    pub fn has_ancestor_individual_node(
        &mut self,
        process_indi: &mut NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let anc_link = calc_alg_context
            .process_context()
            .node(*process_indi)
            .get_ancestor_link();
        anc_link.is_some()
    }

    /// Port of `hasRoleSuccessorConcept`. cpp 20125–20140.
    ///
    /// True iff some `role`-successor of `process_indi` has `concept` (with
    /// `concept_negation`) in its label set.
    pub fn has_role_successor_concept(
        &mut self,
        process_indi: &mut NodeId,
        role: RoleId,
        concept: ConceptId,
        concept_negation: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 20125–20140.
        //   roleSuccHash = node_mut(*process_indi).get_reapply_role_successor_hash(false);
        //   if roleSuccHash.is_some():
        //       for link in role_succ_hash(roleSuccHash).get_role_successor_link_iterator(role):
        //           succIndi = self.get_successor_individual(process_indi, link, ctx);        // Unit 36
        //           conLabelSet = node_mut(succIndi).get_reapply_concept_label_set(false);
        //           if label_set(conLabelSet).has_concept(concept, concept_negation): return true;
        //   return false;
        //
        // Held PORT-PENDING: the `CRoleSuccessorLinkIterator` (role-succ-hash
        // iterator) + `get_successor_individual` (Unit 36); the label-set
        // `has_concept` is ported.
        let _ = (process_indi, role, concept, concept_negation);
        false
    }

    /// Port of `hasRoleSuccessorConcepts`. cpp 20142–20167.
    ///
    /// True iff some `role`-successor of `process_indi` contains every concept of
    /// `concept_linker` (each polarity XOR `negate`) in its label set.
    pub fn has_role_successor_concepts(
        &mut self,
        process_indi: &mut NodeId,
        role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 20142–20167.
        //   roleSuccHash = node_mut(*process_indi).get_reapply_role_successor_hash(false);
        //   if roleSuccHash.is_some():
        //       for link in role_succ_hash(roleSuccHash).get_role_successor_link_iterator(role):
        //           succIndi = self.get_successor_individual(process_indi, link, ctx);        // Unit 36
        //           conLabelSet = node_mut(succIndi).get_reapply_concept_label_set(false);
        //           allContained = true;
        //           for nl in concept_linker:
        //               if !label_set(conLabelSet).has_concept(nl.target, nl.negated ^ negate): allContained = false; break;
        //           if allContained:
        //               // C++ `if (process_indi.is_individual_ancestor(succIndi)) {}` is an empty no-op
        //               return true;
        //   return false;
        //
        // Held PORT-PENDING: the role-succ-hash iterator + `get_successor_individual`
        // (Unit 36); the label-set test is ported.
        let _ = (process_indi, role, concept_linker, negate);
        false
    }

    /// Port of `getRoleSuccessorWithConcepts`. cpp 20170–20193.
    ///
    /// Returns the first `role`-successor of `process_indi` containing every concept
    /// of `concept_linker` (each polarity XOR `negate`), else `NodeId::NONE`.
    pub fn get_role_successor_with_concepts(
        &mut self,
        process_indi: &mut NodeId,
        role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 20170–20193 (identical scan to
        // `has_role_successor_concepts`, returning `succIndi` instead of `true` and
        // `NodeId::NONE` (`nullptr`) instead of `false`).
        // Held PORT-PENDING: the role-succ-hash iterator + `get_successor_individual`
        // (Unit 36); the label-set test is ported.
        let _ = (process_indi, role, concept_linker, negate);
        NodeId::NONE
    }

    /// Port of `hasDistinctRoleSuccessorConcepts`. cpp 20198–20238.
    ///
    /// True iff `process_indi` has at least `distinct_count` pairwise-distinct
    /// `role`-successors that each contain every concept of `concept_linker`
    /// (polarity XOR `negate`). For each candidate successor it walks the
    /// successor's distinct hash, counting distinct individuals that are also
    /// `role`-successors and carry the required concepts, with the symmetric
    /// `disIndiID < succIndiID` pruning of already-checked pairs.
    pub fn has_distinct_role_successor_concepts(
        &mut self,
        process_indi: &mut NodeId,
        role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        distinct_count: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // PORT-PENDING: faithful transcription of cpp 20198–20238.
        //   roleSuccHash = node_mut(*process_indi).get_reapply_role_successor_hash(false);
        //   if roleSuccHash.is_some():
        //       for link in role_succ_hash(roleSuccHash).get_role_successor_link_iterator(role):
        //           succIndi = self.get_successor_individual(process_indi, link, ctx);        // Unit 36
        //           succIndiID = node(succIndi).individual_node_id();
        //           disHash = node_mut(succIndi).get_distinct_hash(false);
        //           if disHash.is_some():
        //               maxSuccDisCount = distinct_hash(disHash).get_distinct_count() + 1;
        //               if maxSuccDisCount >= distinct_count
        //                  && self.contains_individual_node_concepts_negated(succIndi, concept_linker, negate, ctx):  // ported (this unit)
        //                   succDisCount = 1; failDisCount = 0;
        //                   for disIndiID in distinct_hash(disHash).iterator():
        //                       (while maxSuccDisCount - failDisCount >= distinct_count && succDisCount < distinct_count)
        //                       if disIndiID != succIndiID && node(*process_indi).has_role_successor_to_individual_id(role, disIndiID, true):
        //                           if disIndiID < succIndiID: break;  // pair already checked w/ smaller-id successor
        //                           disIndi = self.get_up_to_date_individual_by_id(disIndiID, ctx);   // Unit 36
        //                           if self.contains_individual_node_concepts_negated(disIndi, concept_linker, negate, ctx): succDisCount += 1; else failDisCount += 1;
        //                   if succDisCount >= distinct_count: return true;
        //   return false;
        //
        // Held PORT-PENDING: the role-succ-hash + distinct-hash iterators,
        // `get_successor_individual`/`get_up_to_date_individual_by_id` (Unit 36).
        // The `contains_individual_node_concepts_negated` test +
        // `has_role_successor_to_individual_id` node accessor are ported; they become
        // live on the reconcile pass.
        let _ = (process_indi, role, concept_linker, negate, distinct_count);
        false
    }

    // =======================================================================
    // Disjoint-role / negation edges (cpp 20241–20295).
    //
    // KONCLUDE-PORT-NOTE[exceptions]: an existing role link against a disjoint /
    // negation role is a clash — Konclude throws `CCalculationClashProcessingException`
    // carrying the clash-descriptor chain. The port (Unit 30 clash processing) will
    // surface this as an early-return / `Result`; here the throw site is flagged
    // `[exceptions]` and the descriptor-chain construction is documented.
    // =======================================================================

    /// Port of `createIndividualNodeDisjointRolesLinks`. cpp 20241–20270.
    ///
    /// For each role in `disjoint_role_linker`, installs a `CNegationDisjointEdge`
    /// from `source_indi` to `destination_indi`; if a matching role-successor link
    /// already exists it is a clash (throw), else the disjoint edge is installed and
    /// both nodes flagged as having disjoint-role connections.
    pub fn create_individual_node_disjoint_roles_links(
        &mut self,
        source_indi: &mut NodeId,
        destination_indi: &mut NodeId,
        disjoint_role_linker: &[NegLink<RoleId>],
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 20241–20270.
        //   if disjoint_role_linker not empty:
        //       for nl in disjoint_role_linker:
        //           disjointRole = nl.target;
        //           negDisEdge = ctx.process_context_mut().alloc_disjoint_edge(DisjointEdge::new(...));
        //           disjoint_edge_mut(negDisEdge).init_negation_disjoint_edge(*source_indi, *destination_indi, disjointRole, dep_track_point);
        //           linkIndi = node(*source_indi).get_role_successor_to_individual_link_id(disjointRole, node(*destination_indi).id(), true);
        //           if linkIndi.is_some():
        //               // [exceptions]: clash — throw CCalculationClashProcessingException(clashDes)
        //               //   clashDes = self.create_clashed_individual_link_descriptor(NONE, linkIndi, edge(linkIndi).get_dependency_track_point(), ctx);   // Unit 30
        //               //   clashDes = self.create_clashed_negation_disjoint_descriptor(clashDes, negDisEdge, dep_track_point, ctx);                        // Unit 30
        //               return; // early-return placeholder for the throw
        //           else:
        //               node_mut(*source_indi).set_disjoint_role_connections(true);
        //               node_mut(*destination_indi).set_disjoint_role_connections(true);
        //               node_mut(*source_indi).install_disjoint_link(negDisEdge);
        //       // destination need not install the connection — the disjoint roles already carry a role link.
        //
        // Held PORT-PENDING: the `CNegationDisjointEdge::init_negation_disjoint_edge`
        // body (W2-DEFER) + the clash-descriptor factory/throw (Unit 30, [exceptions]).
        // The role/role-list iteration + node flag/install ops are substrate-resolvable.
        let _ = (source_indi, destination_indi, disjoint_role_linker, dep_track_point);
    }

    /// Port of `createIndividualNodeNegationLink`. cpp 20274–20295.
    ///
    /// Installs a single `CNegationDisjointEdge` for `negation_role`; clash (throw)
    /// when the role-successor link already exists, else installs the edge, flags
    /// both nodes, and registers the connection successor on the destination.
    pub fn create_individual_node_negation_link(
        &mut self,
        source_indi: &mut NodeId,
        destination_indi: &mut NodeId,
        negation_role: RoleId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 20274–20295.
        //   negDisEdge = ctx.process_context_mut().alloc_disjoint_edge(DisjointEdge::new(...));
        //   disjoint_edge_mut(negDisEdge).init_negation_disjoint_edge(*source_indi, *destination_indi, negation_role, dep_track_point);
        //   linkIndi = node(*source_indi).get_role_successor_to_individual_link_id(negation_role, node(*destination_indi).id(), true);
        //   if linkIndi.is_some():
        //       // [exceptions]: clash — throw CCalculationClashProcessingException(clashDes) (same two-descriptor chain as above, Unit 30)
        //       return;
        //   else:
        //       node_mut(*source_indi).install_disjoint_link(negDisEdge);
        //       node_mut(*source_indi).set_disjoint_role_connections(true);
        //       node_mut(*destination_indi).set_disjoint_role_connections(true);
        //       destId = node(*source_indi).individual_node_id();
        //       connSet = node_mut(*destination_indi).get_connection_successor_set(true);
        //       conn_succ_set_mut(connSet).insert_connection_successor(destId);
        //
        // Held PORT-PENDING: the disjoint-edge `init` body (W2-DEFER) + clash
        // factory/throw (Unit 30, [exceptions]); the node ops are substrate-resolvable.
        let _ = (source_indi, destination_indi, negation_role, dep_track_point);
    }

    // =======================================================================
    // Successor-individual generation (cpp 21565–22186).
    //
    // These build new role-successor nodes (functional reuse, fresh SOME successor,
    // distinct cardinality successors). They thread the SOME/ALL dependency creators
    // (Unit 29), the saturation-caching expansion helpers, `addConceptsToIndividual`
    // (Unit 36), and the link/distinct creators of this unit. Held PORT-PENDING with
    // faithful transcriptions.
    // =======================================================================

    /// Port of `tryExtendFunctionalSuccessorIndividual`. cpp 21565–21632.
    ///
    /// If a functional role in `role_linker` already has a successor, reuses it:
    /// creates the ALL dependency, optionally expands it from saturated data, adds
    /// the missing successor links (reapplied) for every role in `role_linker`
    /// (inverse roles linked the other way), propagates modification, and adds the
    /// concepts. Returns the reused successor node (or `NodeId::NONE`).
    pub fn try_extend_functional_successor_individual(
        &mut self,
        indi: &mut NodeId,
        con_des: ConDescId,
        role_linker: &[NegLink<RoleId>],
        anc_role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        dep_track_point: TrackPointId,
        saturation_indi_node: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 21565–21632.
        //   succIndi = NONE; mergeLink = NONE;
        //   roleSucc = node_mut(*indi).get_reapply_role_successor_hash(false);
        //   if roleSucc.is_some():
        //       for nl in role_linker (until succIndi found):
        //           role = nl.target; invRole = nl.negated;
        //           if !invRole && ctx.ontology_arenas().role(role).is_functional():
        //               it = role_succ_hash(roleSucc).get_role_successor_link_iterator(role);
        //               if it.has_next(): link = it.next(false); succIndi = self.get_localized_successor_individual(indi, link, ctx); mergeLink = link;  // Unit 36
        //   if succIndi.is_some():
        //       nextAllDepTrackPoint = NONE;
        //       allDepNode = self.create_all_dependency(&mut nextAllDepTrackPoint, indi, con_des, dep_track_point, edge(mergeLink).get_dependency_track_point(), ctx);  // Unit 29
        //       satCachingPossible; lastSatCachPossibleConDes = NONE;
        //       if self.conf_expand_created_successors_from_saturation:
        //           self.try_expansion_from_saturated_data(indi, succIndi, con_des, nextAllDepTrackPoint, saturation_indi_node, &mut satCachingPossible, &mut lastSatCachPossibleConDes, ctx);
        //       newLinksAdded = false;
        //       for nl in role_linker:
        //           role = nl.target; invRole = nl.negated;
        //           if !invRole:
        //               if !self.has_individuals_link(indi, succIndi, role, true, ctx):       // ported (this unit)
        //                   self.create_new_individuals_link_reapplyed(indi, indi, succIndi, role, nextAllDepTrackPoint, ctx);  // this unit
        //                   newLinksAdded = true;
        //           else:
        //               if !self.has_individuals_link(succIndi, indi, role, true, ctx):
        //                   self.create_new_individuals_link_reapplyed(indi, succIndi, indi, role, nextAllDepTrackPoint, ctx);
        //                   newLinksAdded = true;
        //       if newLinksAdded: self.propagate_individual_node_modified(succIndi, ctx);     // this unit
        //       self.add_concepts_to_individual(concept_linker, negate, succIndi, nextAllDepTrackPoint, true, true, NONE, ctx);  // Unit 36
        //       if self.conf_caching_blocking_from_saturation:
        //           self.try_establish_saturation_caching(indi, succIndi, saturation_indi_node, &mut satCachingPossible, &mut lastSatCachPossibleConDes, ctx);
        //   return succIndi;
        //
        // Held PORT-PENDING: the role-succ-hash iterator, `create_all_dependency`
        // (Unit 29), the saturation-caching expansion helpers, `add_concepts_to_individual`
        // (Unit 36), `get_localized_successor_individual` (Unit 36). The
        // `is_functional` read + `has_individuals_link` + `create_new_individuals_link_reapplyed`
        // + `propagate_individual_node_modified` are ported (this unit).
        let _ = (
            indi, con_des, role_linker, anc_role, concept_linker, negate, dep_track_point,
            saturation_indi_node,
        );
        NodeId::NONE
    }

    /// Port of `createSuccessorIndividual`. cpp 21635–21670.
    ///
    /// Creates a fresh SOME successor: SOME dependency, new individual, optional
    /// saturated-data expansion, the ancestor links (reapplied) + ancestor-depth +
    /// inherited ancestor-cache flags, and the concepts. Returns the new node.
    pub fn create_successor_individual(
        &mut self,
        indi: &mut NodeId,
        con_des: ConDescId,
        role_linker: &[NegLink<RoleId>],
        anc_role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        dep_track_point: TrackPointId,
        saturation_indi_node: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 21635–21670.
        //   nextDepTrackPoint = NONE;
        //   someDepNode = self.create_some_dependency(&mut nextDepTrackPoint, indi, con_des, dep_track_point, ctx);   // Unit 29
        //   succIndi = self.create_new_individual(nextDepTrackPoint, ctx.ontology_arenas().role(anc_role).is_data_role(), ctx);  // this unit
        //   satCachingPossible = true; lastSatCachPossibleConDes = NONE;
        //   if self.conf_expand_created_successors_from_saturation:
        //       self.try_expansion_from_saturated_data(indi, succIndi, con_des, nextDepTrackPoint, saturation_indi_node, &mut satCachingPossible, &mut lastSatCachPossibleConDes, ctx);
        //   ancLink = self.create_new_individuals_links_reapplyed(indi, succIndi, role_linker, anc_role, nextDepTrackPoint, false, ctx);  // Unit 10
        //   node_mut(succIndi).set_ancestor_link(ancLink);
        //   node_mut(succIndi).set_individual_ancestor_depth(node(*indi).individual_ancestor_depth() + 1);
        //   if node(*indi).has_partial(PRF_SATISFIABLECACHED | PRF_ANCESTORSATISFIABLECACHED): node_mut(succIndi).add(PRF_ANCESTORSATISFIABLECACHED);
        //   if node(*indi).has_partial(PRF_SIGNATUREBLOCKINGCACHED | PRF_ANCESTORSIGNATUREBLOCKINGCACHED): node_mut(succIndi).add(PRF_ANCESTORSIGNATUREBLOCKINGCACHED);
        //   if node(*indi).has_partial(PRF_SATURATIONBLOCKINGCACHED | PRF_ANCESTORSATURATIONBLOCKINGCACHED): node_mut(succIndi).add(PRF_ANCESTORSATURATIONBLOCKINGCACHED);
        //   self.add_concepts_to_individual(concept_linker, negate, succIndi, nextDepTrackPoint, true, true, NONE, ctx);  // Unit 36
        //   if self.conf_caching_blocking_from_saturation:
        //       self.try_establish_saturation_caching(indi, succIndi, saturation_indi_node, &mut satCachingPossible, &mut lastSatCachPossibleConDes, ctx);
        //   return succIndi;
        //
        // Held PORT-PENDING: `create_some_dependency` (Unit 29),
        // `create_new_individuals_links_reapplyed` (Unit 10), the saturation-caching
        // helpers, `add_concepts_to_individual` (Unit 36). `create_new_individual` +
        // the node-flag inheritance are ported (this unit) / substrate-resolvable.
        let _ = (
            indi, con_des, role_linker, anc_role, concept_linker, negate, dep_track_point,
            saturation_indi_node,
        );
        NodeId::NONE
    }

    /// Port of `createDistinctSuccessorIndividuals`. cpp 22143–22186.
    ///
    /// Creates `succ_card_count` fresh successors into `indi_list`, makes them
    /// pairwise distinct, then for each: optional saturated-data expansion, the
    /// ancestor links (reapplied) + depth + inherited ancestor-cache flags, and the
    /// concepts.
    pub fn create_distinct_successor_individuals(
        &mut self,
        indi: &mut NodeId,
        con_des: ConDescId,
        indi_list: &mut Vec<NodeId>,
        role_linker: &[NegLink<RoleId>],
        anc_role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        dep_track_point: TrackPointId,
        succ_card_count: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 22143–22186.
        //   for _ in 0..succ_card_count:
        //       succIndi = self.create_new_individual(dep_track_point, ctx.ontology_arenas().role(anc_role).is_data_role(), ctx);  // this unit
        //       indi_list.push(succIndi);
        //   saturationIndiNode = self.get_creation_successor_saturation_node(indi, con_des, ctx);   // saturation helper (unported)
        //   self.create_individuals_distinct(indi_list, dep_track_point, ctx);                      // this unit
        //   for succIndi in indi_list:
        //       satCachingPossible = true; lastSatCachPossibleConDes = NONE;
        //       if self.conf_expand_created_successors_from_saturation && saturationIndiNode.is_some():
        //           self.try_expansion_from_saturated_data(indi, succIndi, con_des, dep_track_point, saturationIndiNode, &mut satCachingPossible, &mut lastSatCachPossibleConDes, ctx);
        //       ancLink = self.create_new_individuals_links_reapplyed(indi, succIndi, role_linker, anc_role, dep_track_point, false, ctx);  // Unit 10
        //       node_mut(succIndi).set_ancestor_link(ancLink);
        //       node_mut(succIndi).set_individual_ancestor_depth(node(*indi).individual_ancestor_depth() + 1);
        //       <inherit PRF_ANCESTOR{SATISFIABLE,SIGNATUREBLOCKING,SATURATIONBLOCKING}CACHED as in create_successor_individual>
        //       self.add_concepts_to_individual(concept_linker, negate, succIndi, dep_track_point, true, true, NONE, ctx);  // Unit 36
        //       if self.conf_caching_blocking_from_saturation && saturationIndiNode.is_some():
        //           self.try_establish_saturation_caching(indi, succIndi, saturationIndiNode, &mut satCachingPossible, &mut lastSatCachPossibleConDes, ctx);
        //
        // Held PORT-PENDING: `get_creation_successor_saturation_node` + the
        // saturation-caching helpers, `create_new_individuals_links_reapplyed`
        // (Unit 10), `add_concepts_to_individual` (Unit 36). `create_new_individual`
        // + `create_individuals_distinct` are ported (this unit).
        let _ = (
            indi, con_des, indi_list, role_linker, anc_role, concept_linker, negate,
            dep_track_point, succ_card_count,
        );
    }

    // =======================================================================
    // Role-link creation + installation (cpp 22212–22369).
    //
    // KONCLUDE-PORT-NOTE[exceptions]: installing a role link that coincides with an
    // existing disjoint/negation edge is a clash (throw, Unit 30); flagged
    // `[exceptions]` at the throw site.
    // =======================================================================

    /// Port of `createNewIndividualsLinks`. cpp 22212–22247.
    ///
    /// Creates one `CIndividualLinkEdge` per role in `role_linker` (inverse roles
    /// from destination to source), installing each (with disjoint-role-link clash
    /// checks), recording the ancestor-role link, registering connection successors,
    /// and (when inverse links were generated or the destination is nominal) the
    /// reverse connection. Returns the ancestor-role link.
    pub fn create_new_individuals_links(
        &mut self,
        indi_source: &mut NodeId,
        indi_destination: &mut NodeId,
        role_linker: &[NegLink<RoleId>],
        anc_role: RoleId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> EdgeId {
        // PORT-PENDING: faithful transcription of cpp 22212–22247.
        //   ancRoleLink = NONE; generatedInvLink = false;
        //   for nl in role_linker:
        //       role = nl.target; invRole = nl.negated; STATINC(LINKSCREATIONCOUNT);
        //       individualLink = ctx.process_context_mut().alloc_edge(IndividualLinkEdge::new(...));
        //       if !invRole:
        //           self.create_individual_node_disjoint_roles_links(indi_source, indi_destination, ctx.ontology_arenas().role(role).get_disjoint_role_list(), dep_track_point, ctx);  // this unit
        //           edge_mut(individualLink).init_individual_link_edge(*indi_source, *indi_source, *indi_destination, role, dep_track_point);
        //           self.install_individual_node_role_link(indi_source, indi_destination, individualLink, ctx);  // this unit
        //       else:
        //           generatedInvLink = true;
        //           self.create_individual_node_disjoint_roles_links(indi_destination, indi_source, ctx.ontology_arenas().role(role).get_disjoint_role_list(), dep_track_point, ctx);
        //           edge_mut(individualLink).init_individual_link_edge(*indi_source, *indi_destination, *indi_source, role, dep_track_point);
        //           self.install_individual_node_role_link(indi_destination, indi_source, individualLink, ctx);
        //       if anc_role == role: ancRoleLink = individualLink;
        //   if generatedInvLink || node(*indi_destination).is_nominal_individual_node():
        //       destId = node(*indi_destination).individual_node_id();
        //       conn_succ_set_mut(node_mut(*indi_source).get_connection_successor_set(true)).insert_connection_successor(destId);
        //   srcId = node(*indi_source).individual_node_id();
        //   conn_succ_set_mut(node_mut(*indi_destination).get_connection_successor_set(true)).insert_connection_successor(srcId);
        //   if self.opt_incremental_compatible_expansion:
        //       self.link_creation_directly_changed_neighbour_connection_update(indi_destination, indi_source, true, ctx);  // Unit 26
        //   return ancRoleLink;
        //
        // Held PORT-PENDING: the `CIndividualLinkEdge::init_individual_link_edge` body
        // (W2-DEFER), the connection-successor-set insert API, and
        // `link_creation_directly_changed_neighbour_connection_update` (Unit 26). The
        // role-list reads, `alloc_edge`, and `install_individual_node_role_link` +
        // `create_individual_node_disjoint_roles_links` (this unit) are resolvable.
        let _ = (indi_source, indi_destination, role_linker, anc_role, dep_track_point);
        EdgeId::NONE
    }

    /// Port of `installIndividualNodeRoleLink`. cpp 22251–22269.
    ///
    /// Installs `individual_link` on `source_indi`; clash (throw) if a disjoint
    /// successor-role edge to the destination on the same role already exists; on a
    /// fresh first link, updates the role-instance occurrence statistics.
    pub fn install_individual_node_role_link(
        &mut self,
        source_indi: &mut NodeId,
        destination_indi: &mut NodeId,
        individual_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 22251–22269.
        //   disSuccRoleHash = node_mut(*source_indi).get_disjoint_successor_role_hash(false);
        //   if disSuccRoleHash.is_some():
        //       destId = node(*destination_indi).individual_node_id(); linkRole = edge(individual_link).get_link_role();
        //       negDisEdge = ...get_disjoint_successor_role_link(destId, linkRole);
        //       if negDisEdge.is_some():
        //           // [exceptions]: clash — throw (Unit 30) with createClashedIndividualLinkDescriptor + createClashedNegationDisjointDescriptor
        //           return;
        //   succLinkCount = node_mut(*source_indi).install_individual_link(individual_link);
        //   if self.conf_occurrence_statistics_collecting && self.opt_collect_occurrence_statistics:
        //       nondeterministically = self.has_nondeterministic_dependency(edge(individual_link).get_dependency_track_point(), ctx);  // Unit 29
        //       occ_stats_cache_handler(self.occ_stats_cache_handler).inc_role_instance_occurrencce_statistics(edge(individual_link).get_link_role(), nondeterministically, !node(*source_indi).nominal_individual(), succLinkCount <= 1);
        //
        // Held PORT-PENDING: the disjoint-successor-role hash lookup + clash/throw
        // (Unit 30, [exceptions]) + the occurrence-statistics cache handler. The
        // `install_individual_link` node accessor + `has_nondeterministic_dependency`
        // (Unit 29) are ported.
        let _ = (source_indi, destination_indi, individual_link);
    }

    /// Port of `installIndividualNodeRoleLinkReapplied`. cpp 22272–22292.
    ///
    /// As `install_individual_node_role_link`, but installs with a reapply-queue
    /// iterator (returned to the caller for restricted reapplication).
    pub fn install_individual_node_role_link_reapplied(
        &mut self,
        source_indi: &mut NodeId,
        destination_indi: &mut NodeId,
        individual_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ReapplyQueueIterator {
        // PORT-PENDING: faithful transcription of cpp 22272–22292 (identical clash
        // check to `install_individual_node_role_link`, but the install variant
        // `node_mut(*source_indi).install_individual_link(individual_link, &mut reapplyIterator)`
        // fills + returns the `CReapplyQueueIterator`).
        // Held PORT-PENDING: same as `install_individual_node_role_link`, plus the
        // reapply-queue iterator value type (opaque `Cint64` here, [api]).
        let _ = (source_indi, destination_indi, individual_link);
        INVALID
    }

    /// Port of `createNewIndividualsLink`. cpp 22355–22369.
    ///
    /// Creates and installs a single `CIndividualLinkEdge` (`indi_creator` as
    /// creator) from `indi_source` to `indi_destination` on `role`, with the
    /// disjoint-role-link clash check + connection-successor registration. Returns
    /// the link.
    pub fn create_new_individuals_link(
        &mut self,
        indi_creator: &mut NodeId,
        indi_source: &mut NodeId,
        indi_destination: &mut NodeId,
        role: RoleId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> EdgeId {
        // PORT-PENDING: faithful transcription of cpp 22355–22369.
        //   STATINC(LINKSCREATIONCOUNT);
        //   self.create_individual_node_disjoint_roles_links(indi_source, indi_destination, ctx.ontology_arenas().role(role).get_disjoint_role_list(), dep_track_point, ctx);  // this unit
        //   individualLink = ctx.process_context_mut().alloc_edge(IndividualLinkEdge::new(...));
        //   edge_mut(individualLink).init_individual_link_edge(*indi_creator, *indi_source, *indi_destination, role, dep_track_point);
        //   self.install_individual_node_role_link(indi_source, indi_destination, individualLink, ctx);  // this unit
        //   srcId = node(*indi_source).individual_node_id();
        //   conn_succ_set_mut(node_mut(*indi_destination).get_connection_successor_set(true)).insert_connection_successor(srcId);
        //   if self.opt_incremental_compatible_expansion:
        //       self.link_creation_directly_changed_neighbour_connection_update(indi_destination, indi_source, true, ctx);  // Unit 26
        //   return individualLink;
        //
        // Held PORT-PENDING: the edge `init` body (W2-DEFER), the connection-set
        // insert API, and the incremental neighbour-update sibling (Unit 26).
        let _ = (indi_creator, indi_source, indi_destination, role, dep_track_point);
        EdgeId::NONE
    }

    // NOTE: `createNewIndividualsLinkReapplyed` (cpp 22372–22398) and
    // `createNewIndividualsLinksReapplyed` (cpp 22295–22352) belong to the
    // reapply-queue family (manifest Unit 10), not this unit.

    // =======================================================================
    // Distinct edges + link predicate (cpp 22401–22435).
    // =======================================================================

    /// Port of `createIndividualsDistinct(CIndividualProcessNode*&,
    /// CIndividualProcessNode*&, CDependencyTrackPoint*)`. cpp 22401–22409.
    ///
    /// Installs one `CDistinctEdge` symmetrically into both nodes' distinct hashes.
    pub fn create_individuals_distinct_pair(
        &mut self,
        indi_source: &mut NodeId,
        indi_destination: &mut NodeId,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 22401–22409.
        //   STATINC(DISTINCTCREATIONCOUNT);
        //   disEdge = ctx.process_context_mut().alloc_distinct_edge(DistinctEdge::new(...));
        //   distinct_edge_mut(disEdge).init_distinct_edge(*indi_source, *indi_destination, dep_track_point);
        //   srcId = node(*indi_source).individual_node_id(); destId = node(*indi_destination).individual_node_id();
        //   distinct_hash_mut(node_mut(*indi_source).get_distinct_hash(true)).insert_distinct_individual(destId, disEdge);
        //   distinct_hash_mut(node_mut(*indi_destination).get_distinct_hash(true)).insert_distinct_individual(srcId, disEdge);
        //
        // Held PORT-PENDING: the `CDistinctEdge::init_distinct_edge` body (W2-DEFER)
        // + the distinct-hash insert API; `alloc_distinct_edge` + `get_distinct_hash`
        // are resolvable.
        let _ = (indi_source, indi_destination, dep_track_point);
    }

    /// Port of `createIndividualsDistinct(CPROCESSINGLIST<CIndividualProcessNode*>&,
    /// CDependencyTrackPoint*)`. cpp 22413–22430.
    ///
    /// Makes every pair in `indi_list` distinct (one `CDistinctEdge` per unordered
    /// pair, inserted into both nodes' distinct hashes).
    pub fn create_individuals_distinct(
        &mut self,
        indi_list: &mut Vec<NodeId>,
        dep_track_point: TrackPointId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // PORT-PENDING: faithful transcription of cpp 22413–22430.
        //   for i in 0..indi_list.len():
        //       indi1 = indi_list[i];
        //       for j in (i+1)..indi_list.len():
        //           indi2 = indi_list[j]; STATINC(DISTINCTCREATIONCOUNT);
        //           disEdge = ctx.process_context_mut().alloc_distinct_edge(DistinctEdge::new(...));
        //           distinct_edge_mut(disEdge).init_distinct_edge(indi1, indi2, dep_track_point);
        //           id1 = node(indi1).individual_node_id(); id2 = node(indi2).individual_node_id();
        //           distinct_hash_mut(node_mut(indi1).get_distinct_hash(true)).insert_distinct_individual(id2, disEdge);
        //           distinct_hash_mut(node_mut(indi2).get_distinct_hash(true)).insert_distinct_individual(id1, disEdge);
        //
        // Held PORT-PENDING: same as `create_individuals_distinct_pair`. (The C++
        // caches each node's distinct hash once per outer/inner iteration; the port
        // re-fetches per insert — behaviour identical.)
        let _ = (indi_list, dep_track_point);
    }

    /// Port of `hasIndividualsLink`. cpp 22433–22435. FULLY PORTED.
    pub fn has_individuals_link(
        &mut self,
        indi_source: &mut NodeId,
        indi_destination: &mut NodeId,
        role: RoleId,
        locateable: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let dest_id = calc_alg_context
            .process_context()
            .node(*indi_destination)
            .individual_node_id();
        calc_alg_context
            .process_context()
            .node(*indi_source)
            .has_role_successor_to_individual_id(role, dest_id, locateable)
    }

    // =======================================================================
    // Fresh-individual construction (cpp 22439–22493).
    // =======================================================================

    /// Port of `createNewEmptyIndividual`. cpp 22439–22458.
    ///
    /// Bump-allocates a fresh `CIndividualProcessNode`, assigns it the next free node
    /// id (≥ the node vector's max index + 1), registers it in the node vector, and
    /// applies the consistence-node-preparation / incremental-expansion flags.
    pub fn create_new_empty_individual(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 22439–22458.
        //   STATINC(SUCCESSORINDINODECREATIONCOUNT);
        //   newIndividual = ctx.process_context_mut().alloc_node(IndividualProcessNode::new(...));
        //   indiProcNodeVec = ctx.processing_data_box().individual_process_node_vector();
        //   newIndividualID = ctx.processing_data_box_mut().next_individual_node_id();
        //   newIndividualID = max(indiProcNodeVec.get_item_max_index() + 1, newIndividualID);
        //   node_mut(newIndividual).set_individual_node_id(newIndividualID);
        //   indiProcNodeVec.set_local_data(newIndividualID, newIndividual);
        //   if self.opt_consistence_node_marking: node_mut(newIndividual).add_processing_restriction_flags(PRF_CONSNODEPREPARATIONINDINODE);
        //   if self.opt_incremental_compatible_expansion:
        //       node_mut(newIndividual).add_processing_restriction_flags(PRF_INCREMENTALEXPANDING);
        //       node_mut(newIndividual).set_incremental_expansion_id(ctx.processing_data_box().incremental_expansion_id());
        //   return newIndividual;
        //
        // NOW LIVE. The node-vector get-max-index / set-data API is wired
        // (`process/node_resolution.rs` `IndividualProcessNodeVector`), `alloc_node`,
        // `next_individual_node_id`, `set_individual_node_id`, the flag adds, and
        // `incremental_expansion_id` are all available.
        //
        // W3-DEFER[macro]: STATINC(SUCCESSORINDINODECREATIONCOUNT, ctx).
        let new_individual = calc_alg_context
            .process_context_mut()
            .alloc_node(IndividualProcessNode::new(Id::NONE));
        let max_index = calc_alg_context
            .processing_data_box()
            .individual_process_node_vector()
            .get_item_max_index();
        // `getNextIndividualNodeID()` is a non-incrementing floor read; the node-vector
        // growth (setData below) drives id uniqueness, matching Konclude.
        let floor_id = calc_alg_context
            .processing_data_box_mut()
            .next_individual_node_id(false);
        let new_individual_id = (max_index + 1).max(floor_id);
        calc_alg_context
            .process_context_mut()
            .node_mut(new_individual)
            .set_individual_node_id(new_individual_id);
        calc_alg_context
            .processing_data_box_mut()
            .individual_process_node_vector_mut()
            .set_data(new_individual_id, new_individual);
        if self.opt_consistence_node_marking {
            calc_alg_context
                .process_context_mut()
                .node_mut(new_individual)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_CONSNODEPREPARATIONINDINODE,
                );
        }
        if self.opt_incremental_compatible_expansion {
            calc_alg_context
                .process_context_mut()
                .node_mut(new_individual)
                .add_processing_restriction_flags(IndividualProcessNode::PRF_INCREMENTALEXPANDING);
            let inc_exp_id = calc_alg_context
                .processing_data_box()
                .incremental_expansion_id();
            calc_alg_context
                .process_context_mut()
                .node_mut(new_individual)
                .set_incremental_expansion_id(inc_exp_id);
        }
        new_individual
    }

    /// Port of `createNewIndividual`. cpp 22462–22475.
    ///
    /// Creates an empty individual, inits its dependency tracker, and seeds it with
    /// the ontology top concept (object node) or top-data-range concept (data node,
    /// also flagged concrete-data + extended-queue).
    pub fn create_new_individual(
        &mut self,
        dep_track_point: TrackPointId,
        data_node: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 22462–22475.
        //   newIndividual = self.create_new_empty_individual(ctx);                            // this unit
        //   node_mut(newIndividual).init_dependency_tracker(dep_track_point);
        //   if !data_node:
        //       topConcept = ctx.processing_data_box().ontology_top_concept();
        //       self.add_concept_to_individual(topConcept, false, newIndividual, dep_track_point, true, false, ctx);  // Unit 36
        //   else:
        //       node_mut(newIndividual).set_extended_queue_processing(true);
        //       topDataRangeConcept = ctx.processing_data_box().ontology_top_data_range_concept();
        //       self.add_concept_to_individual(topDataRangeConcept, false, newIndividual, dep_track_point, true, false, ctx);  // Unit 36
        //       node_mut(newIndividual).add_processing_restriction_flags(PRF_CONCRETEDATAINDINODE);
        //   return newIndividual;
        //
        // NOW LIVE. `add_concept_to_individual` (Unit 36) is wired; the node
        // `initDependencyTracker(depTrackPoint)` derived init stays W2-deferred, so the
        // field is set directly via `set_dependency_track_point` (the descriptor-init
        // convention u36 uses for `init_concept_descriptor_fields`).
        let mut new_individual = self.create_new_empty_individual(calc_alg_context);
        calc_alg_context
            .process_context_mut()
            .node_mut(new_individual)
            .set_dependency_track_point(dep_track_point);
        if !data_node {
            let top_concept = calc_alg_context.processing_data_box().ontology_top_concept();
            self.add_concept_to_individual(
                top_concept,
                false,
                &mut new_individual,
                dep_track_point,
                true,
                false,
                calc_alg_context,
            );
        } else {
            calc_alg_context
                .process_context_mut()
                .node_mut(new_individual)
                .set_extended_queue_processing(true);
            let top_data_range_concept = calc_alg_context
                .processing_data_box()
                .ontology_top_data_range_concept();
            self.add_concept_to_individual(
                top_data_range_concept,
                false,
                &mut new_individual,
                dep_track_point,
                true,
                false,
                calc_alg_context,
            );
            calc_alg_context
                .process_context_mut()
                .node_mut(new_individual)
                .add_processing_restriction_flags(IndividualProcessNode::PRF_CONCRETEDATAINDINODE);
        }
        new_individual
    }

    /// Port of `getAvailableUpToDateIndividual`. cpp 22477–22482.
    ///
    /// Returns the up-to-date node for `indi_id` if the nominal node is available,
    /// else `NodeId::NONE`.
    pub fn get_available_up_to_date_individual(
        &mut self,
        indi_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 22477–22482.
        //   if self.is_nominal_individual_node_available(indi_id, ctx):       // Unit 36
        //       return self.get_up_to_date_individual_by_id(indi_id, ctx);    // Unit 36
        //   return NONE;
        //
        // NOW LIVE: superseded by `ctx.get_available_up_to_date_individual`
        // (node-resolution keystone) — `is_nominal_individual_node_available` +
        // `get_up_to_date_individual_by_id` are wired there.
        calc_alg_context.get_available_up_to_date_individual(indi_id)
    }

    /// Port of `getUpToDateIndividual(CIndividualProcessNode*)`. cpp 22485–22493.
    ///
    /// If `indi`'s localization tag is stale and it has been relocalized, reloads the
    /// current node from the node vector; otherwise returns `indi` unchanged.
    pub fn get_up_to_date_individual(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        // PORT-PENDING: faithful transcription of cpp 22485–22493.
        //   currentTag = ctx...used_process_tagger().current_localization_tag();   // process-tagger (opaque [api])
        //   if !node(indi).is_localization_tag_up_to_date(currentTag) && node(indi).is_relocalized():
        //       STATINC(INDINODEUPDATELOADCOUNT);
        //       indiProcNodeVec = ctx.processing_data_box().individual_process_node_vector();
        //       return indiProcNodeVec.get_data(node(indi).individual_node_id());   // vector get-data (unported)
        //   return indi;
        //
        // NOW LIVE: superseded by `ctx.get_up_to_date_individual` (node-resolution
        // keystone) — the tagger + `is_localization_tag_up_to_date` + the databox
        // node-vector `get_data` are wired there.
        calc_alg_context.get_up_to_date_individual(indi)
    }
}
