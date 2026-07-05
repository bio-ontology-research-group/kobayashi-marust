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
//! allocators (`CIndividualLinkEdge`/`CNegationDisjointEdge`/`CDistinctEdge`),
//! the clash-descriptor factory + the
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

use super::super::model::op;
use super::super::model::substrate::{Id, NegLink, INVALID};
use super::super::model::{Cint64, ConceptId, RoleId};
use super::super::process::blocking_hash::{
    BlockingIndividualNodeCandidateHash, BlockingIndividualNodeCandidateHashId,
};
use super::super::process::edge::{DisjointEdge, DistinctEdge, IndividualLinkEdge};
use super::super::process::node::IndividualProcessNode;
use super::super::process::rs1::ReapplyQueueIterator;
use super::super::process::{
    ClashDescId, ConDescId, EdgeId, LabelSetId, NodeId, SatNodeId, TrackPointId,
};
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // =======================================================================
    // Debug associated-concepts string builders (cpp 18390–18462).
    //
    // KONCLUDE-PORT-NOTE[ownership]: Qt `QSet<CConcept*>` /
    // `QSet<QList<QSet<CConcept*>>>` debug-only aggregate inputs are represented
    // by slices/Vectors of `ConceptId` groups. The per-node concept rendering
    // still reproduces the ordered `QMap<cint64,QString>` tag join.
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
        let mut con_tag_concept_string_map = std::collections::BTreeMap::new();
        for concept in associated_concepts.iter().copied() {
            let concept_tag = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_concept_tag();
            con_tag_concept_string_map.insert(concept_tag, concept_tag.to_string());
        }
        let concepts_string = con_tag_concept_string_map
            .values()
            .cloned()
            .collect::<Vec<_>>()
            .join(", ");
        format!("{} : {{{}}}", indi_node_id, concepts_string)
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
        let individual_node_id = calc_alg_context
            .process_context()
            .node(*individual_node)
            .individual_node_id();
        let mut all_node_list_associated_concepts_string_list = Vec::new();
        for associated_concepts in all_variable_mappings_associated_concepts_set.iter() {
            let associated_concepts_string = self
                .generate_debug_individual_node_associated_concepts_string(
                    individual_node_id,
                    associated_concepts,
                    calc_alg_context,
                );
            all_node_list_associated_concepts_string_list.push(associated_concepts_string);
        }
        all_node_list_associated_concepts_string_list.join("<br>\n")
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
        let individual_node_id = calc_alg_context
            .process_context()
            .node(*individual_node)
            .individual_node_id();
        let ancestor_individual_node_id = calc_alg_context
            .process_context()
            .node(*ancestor_individual_node)
            .individual_node_id();
        let mut all_node_list_associated_concepts_string_list = Vec::new();

        for node_list_associated_concepts in
            all_variable_mappings_associated_concepts_over_nodes_list_set.iter()
        {
            let mut node_list_associated_concepts_string_list = Vec::new();
            let mut list_iter = node_list_associated_concepts.iter();
            if let Some(test_indi_associated_concepts) = list_iter.next() {
                let test_indi_associated_concepts_string = self
                    .generate_debug_individual_node_associated_concepts_string(
                        individual_node_id,
                        test_indi_associated_concepts,
                        calc_alg_context,
                    );
                node_list_associated_concepts_string_list.push(format!(
                    "{} node {}",
                    node_naming, test_indi_associated_concepts_string
                ));
            }
            if let Some(ancestor_test_indi_associated_concepts) = list_iter.next() {
                let ancestor_test_indi_associated_concepts_string = self
                    .generate_debug_individual_node_associated_concepts_string(
                        ancestor_individual_node_id,
                        ancestor_test_indi_associated_concepts,
                        calc_alg_context,
                    );
                node_list_associated_concepts_string_list.push(format!(
                    "{} predecessor {}",
                    node_naming, ancestor_test_indi_associated_concepts_string
                ));
            }

            let mut dependent_nominal_id_iter = dependent_nominal_id_list.iter();
            for nominal_indi_associated_concepts in list_iter {
                let dependent_nominal_id = dependent_nominal_id_iter
                    .next()
                    .copied()
                    .unwrap_or_default();
                let nominal_indi_associated_concepts_string = self
                    .generate_debug_individual_node_associated_concepts_string(
                        dependent_nominal_id,
                        nominal_indi_associated_concepts,
                        calc_alg_context,
                    );
                node_list_associated_concepts_string_list.push(format!(
                    "nominal node {}",
                    nominal_indi_associated_concepts_string
                ));
            }
            all_node_list_associated_concepts_string_list
                .push(node_list_associated_concepts_string_list.join("  |||  "));
        }

        all_node_list_associated_concepts_string_list.join("<br>\n")
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
            .node_reapply_concept_label_set(*test_indi);
        self.contains_individual_node_concept_label(
            con_label_set,
            con_test,
            contains_negation,
            calc_alg_context,
        )
    }

    /// Context-resolved concept containment for live label-set callers.
    ///
    /// `CReapplyConceptLabelSet` still has legacy `ConceptId -> tag` shims from the
    /// structural wave. Completion code must use ontology concept tags and descriptor
    /// negation from the process arena, matching the C++ pointer-based lookup.
    pub fn label_set_contains_concept_get_negated_resolved(
        &mut self,
        con_label_set: LabelSetId,
        con_test: ConceptId,
        contains_negation: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let con_tag = calc_alg_context
            .ontology_arenas()
            .concept(con_test)
            .get_concept_tag();
        let mut con_des: ConDescId = Id::NONE;
        let mut dep_track_point = TrackPointId::NONE;
        if !calc_alg_context
            .process_context()
            .label_set(con_label_set)
            .get_concept_descriptor_by_tag(con_tag, &mut con_des, &mut dep_track_point)
        {
            if let Some(data) = calc_alg_context
                .process_context()
                .label_set_additional_get_cloned(con_label_set, con_tag)
            {
                con_des = data.concept_descriptor;
            }
            if con_des.is_none() {
                return false;
            }
        }
        if let Some(out) = contains_negation {
            *out = calc_alg_context
                .process_context()
                .con_desc(con_des)
                .is_negated();
        }
        true
    }

    pub fn label_set_contains_concept_resolved(
        &mut self,
        con_label_set: LabelSetId,
        con_test: ConceptId,
        negated: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut contains_negated = false;
        self.label_set_contains_concept_get_negated_resolved(
            con_label_set,
            con_test,
            Some(&mut contains_negated),
            calc_alg_context,
        ) && contains_negated == negated
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
        if !self.label_set_contains_concept_get_negated_resolved(
            con_label_set,
            con_test,
            Some(&mut contains_neg),
            calc_alg_context,
        ) {
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
            if !self.label_set_contains_concept_get_negated_resolved(
                con_label_set,
                concept,
                Some(&mut contains_neg),
                calc_alg_context,
            ) {
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
            if !self.label_set_contains_concept_resolved(
                con_label_set,
                concept,
                con_neg,
                calc_alg_context,
            ) {
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
            .node_reapply_concept_label_set(*test_indi);
        self.contains_individual_node_concepts_label_negated(
            con_label_set,
            con_test_linker,
            negated,
            calc_alg_context,
        )
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
            .node_reapply_concept_label_set(*test_indi);
        self.contains_individual_node_concepts_label_get_negated(
            con_label_set,
            con_test_linker,
            contains_negation,
            calc_alg_context,
        )
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
            .node_reapply_concept_label_set(*test_indi);
        // C++ passes (bool*)nullptr.
        self.contains_individual_node_concepts_label_get_negated(
            con_label_set,
            con_test_linker,
            None,
            calc_alg_context,
        )
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
        let blocking_cand_hash =
            self.get_or_create_blocking_individual_node_candidate_hash(calc_alg_context);
        let blocking_cand_data =
            BlockingIndividualNodeCandidateHash::get_blocking_individual_candidate_data_for_concept_descriptor(
                calc_alg_context.process_context_mut(),
                blocking_cand_hash,
                con_des,
                true,
            );
        // W3-DEFER[macro]: STATINC(ANYWHEREBLOCKINGCANDIDATEHASHUDATEADDCOUNT, calcAlgContext).
        calc_alg_context
            .process_context_mut()
            .blocking_indi_node_cand_data_insert_blocking_candidate_individual_node(
                blocking_cand_data,
                *indi,
            );
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
        let blocking_cand_hash =
            self.get_or_create_blocking_individual_node_candidate_hash(calc_alg_context);
        for concept_link in concepts.iter() {
            let concept = concept_link.target;
            let concept_negation = concept_link.negated ^ negated;
            let blocking_cand_data =
                BlockingIndividualNodeCandidateHash::get_blocking_individual_candidate_data(
                    calc_alg_context.process_context_mut(),
                    blocking_cand_hash,
                    concept,
                    concept_negation,
                    true,
                );
            // W3-DEFER[macro]: STATINC(ANYWHEREBLOCKINGCANDIDATEHASHUDATEADDCOUNT, calcAlgContext).
            calc_alg_context
                .process_context_mut()
                .blocking_indi_node_cand_data_insert_blocking_candidate_individual_node(
                    blocking_cand_data,
                    *indi,
                );
            let op_code = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operator_code();
            if (!concept_negation && op_code == op::CCAND)
                || (concept_negation && op_code == op::CCOR)
            {
                let operands = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_operand_list()
                    .to_vec();
                self.add_individual_node_candidate_for_concept(
                    indi,
                    &operands,
                    concept_negation,
                    calc_alg_context,
                );
            }
        }
    }

    /// Localized equivalent of
    /// `processingDataBox->getBlockingIndividualNodeCandidateHash(true)`.
    fn get_or_create_blocking_individual_node_candidate_hash(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> BlockingIndividualNodeCandidateHashId {
        calc_alg_context.blocking_individual_node_candidate_hash(true)
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
        let mut add_individual_to_processing_queue_due_to_modification = false;
        if !calc_alg_context
            .process_context()
            .node(*indi)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHEDRETESTDUETOMODIFICATION,
            )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(*indi)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHEDRETESTDUETOMODIFICATION,
                );
        }
        if !calc_alg_context
            .process_context()
            .node(*indi)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED,
            )
            && calc_alg_context
                .process_context()
                .node(*indi)
                .nominal_individual()
                .is_none()
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(*indi)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_BLOCKINGRETESTDUEDIRECTMODIFIED,
                );
            self.propagate_processing_restriction_to_successors(
                *indi,
                IndividualProcessNode::PRF_BLOCKINGRETESTDUEANCESTORMODIFIED,
                true,
                IndividualProcessNode::PRF_DIRECTBLOCKED
                    | IndividualProcessNode::PRF_INDIRECTBLOCKED
                    | IndividualProcessNode::PRF_PROCESSINGBLOCKED,
                calc_alg_context,
            );
            add_individual_to_processing_queue_due_to_modification = true;
        }
        self.eliminiate_blocked_individuals(*indi, calc_alg_context);
        if calc_alg_context
            .process_context()
            .node(*indi)
            .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_SATISFIABLECACHED)
            && !calc_alg_context
                .process_context()
                .node(*indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTSATISFIABLECACHEDDUEDIRECTMODIFIED,
                )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(*indi)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTSATISFIABLECACHEDDUEDIRECTMODIFIED,
                );
            add_individual_to_processing_queue_due_to_modification = true;
        }
        if calc_alg_context
            .process_context()
            .node(*indi)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED,
            )
            && !calc_alg_context
                .process_context()
                .node(*indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTSIGNATUREBLOCKINGCACHEDDUEDIRECTMODIFIED,
                )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(*indi)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTSIGNATUREBLOCKINGCACHEDDUEDIRECTMODIFIED,
                );
            add_individual_to_processing_queue_due_to_modification = true;
        }
        if calc_alg_context
            .process_context()
            .node(*indi)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_COMPLETIONGRAPHCACHED,
            )
            && !calc_alg_context
                .process_context()
                .node(*indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED,
                )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(*indi)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTCOMPLETIONGRAPHCACHEDDUEDIRECTMODIFIED,
                );
            add_individual_to_processing_queue_due_to_modification = true;
        }
        if calc_alg_context
            .process_context()
            .node(*indi)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHED,
            )
            && !calc_alg_context
                .process_context()
                .node(*indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTSATURATIONBLOCKINGCACHEDDUEDIRECTMODIFIED,
                )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(*indi)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTSATURATIONBLOCKINGCACHEDDUEDIRECTMODIFIED,
                );
            add_individual_to_processing_queue_due_to_modification = true;
        }
        if add_individual_to_processing_queue_due_to_modification {
            self.add_individual_to_blocking_update_review_processing_queue(*indi, calc_alg_context);
        }
        if calc_alg_context
            .process_context()
            .node(*indi)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKEND
                    | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDSUCCESSOREXPANSIONBLOCKED
                    | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDNEIGHBOUREXPANSIONBLOCKED
                    | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION
                    | IndividualProcessNode::PRF_SYNCHRONIZEDBACKENDINDIRECTNOMINALEXPANSIONBLOCKED,
            )
            && !calc_alg_context
                .process_context()
                .node(*indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
                )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(*indi)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
                );
            if !add_individual_to_processing_queue_due_to_modification {
                self.add_individual_to_backend_synchronisation_retest_queue(
                    *indi,
                    calc_alg_context,
                );
            }
        }
        if calc_alg_context
            .process_context()
            .node(*indi)
            .has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDPARTIALEXPANSION,
            )
            && !calc_alg_context
                .process_context()
                .node(*indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
                )
            && !calc_alg_context
                .process_context()
                .node(*indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_SYNCHRONIZEDBACKENNEIGHBOURDFULLEXPANSION,
                )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(*indi)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_RETESTBACKENDSYNCHRONIZATIONDUEDIRECTMODIFIED,
                );
            if !add_individual_to_processing_queue_due_to_modification {
                self.add_individual_to_backend_direct_influence_expansion_queue(
                    *indi,
                    calc_alg_context,
                );
            }
        }
        if self.opt_incremental_compatible_expansion
            && calc_alg_context
                .process_context()
                .node(*indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_INCREMENTALEXPANDING,
                )
            && !calc_alg_context
                .process_context()
                .node(*indi)
                .has_partial_processing_restriction_flags(
                    IndividualProcessNode::PRF_INCREMENTALEXPANSIONRETESTDUEDIRECTMODIFIED,
                )
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(*indi)
                .add_processing_restriction_flags(
                    IndividualProcessNode::PRF_INCREMENTALEXPANSIONRETESTDUEDIRECTMODIFIED,
                );
            self.add_individual_to_incremental_compatibility_checking_queue(
                *indi,
                calc_alg_context,
            );
        }
        if calc_alg_context
            .process_context()
            .node(*indi)
            .is_nominal_individual_node()
            && calc_alg_context
                .process_context()
                .node(*indi)
                .nominal_individual()
                .is_some()
            && calc_alg_context
                .process_context()
                .node(*indi)
                .is_delayed_nominal_processing_queued()
        {
            calc_alg_context
                .process_context_mut()
                .node_mut(*indi)
                .set_delayed_nominal_processing_queued(false);
            self.add_individual_to_processing_queue(*indi, calc_alg_context);
        }
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
        calc_alg_context
            .process_context_mut()
            .node_mut(*indi)
            .add_processing_restriction_flags(IndividualProcessNode::PRF_PURGEDBLOCKED);
        self.eliminiate_blocked_individuals(*indi, calc_alg_context);

        if remove_nominal_links && ancestor_indi.is_some() {
            let ancestor_indi_id = calc_alg_context
                .process_context()
                .node(ancestor_indi)
                .individual_node_id();
            let pruned_indi_id = calc_alg_context
                .process_context()
                .node(*indi)
                .individual_node_id();

            let conn_ids: Vec<Cint64> = {
                let conn_set = calc_alg_context
                    .process_context()
                    .node_connection_successor_set_existing(*indi);
                if conn_set.is_some()
                    && calc_alg_context
                        .process_context()
                        .conn_succ_set(conn_set)
                        .get_connection_successor_count()
                        > 0
                {
                    let mut iterator = calc_alg_context
                        .process_context()
                        .conn_succ_set(conn_set)
                        .get_connection_successor_iterator();
                    let mut ids = Vec::new();
                    while iterator.has_next() {
                        ids.push(iterator.next(true));
                    }
                    ids
                } else {
                    Vec::new()
                }
            };

            for conn_id in conn_ids {
                if ancestor_indi_id != conn_id {
                    let nom_indi = self.get_up_to_date_individual_by_id(conn_id, calc_alg_context);
                    if nom_indi.is_some()
                        && calc_alg_context
                            .process_context()
                            .node(nom_indi)
                            .is_nominal_individual_node()
                    {
                        let loc_nom_indi =
                            self.get_localized_individual(nom_indi, false, calc_alg_context);
                        self.remove_nominal_pruned_links(
                            loc_nom_indi,
                            pruned_indi_id,
                            *indi,
                            calc_alg_context,
                        );
                    }
                }
            }

            let succ_links = self.snapshot_successor_links(*indi, calc_alg_context);
            for succ_link in succ_links {
                let succ_indi = self.get_successor_individual(indi, succ_link, calc_alg_context);
                if calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .is_nominal_individual_node()
                    && calc_alg_context
                        .process_context()
                        .node(succ_indi)
                        .individual_node_id()
                        != ancestor_indi_id
                {
                    let loc_nom_indi =
                        self.get_localized_individual(succ_indi, false, calc_alg_context);
                    self.remove_nominal_pruned_links(
                        loc_nom_indi,
                        pruned_indi_id,
                        *indi,
                        calc_alg_context,
                    );
                }
            }
        }

        let ancestor_depth = calc_alg_context
            .process_context()
            .node(*indi)
            .individual_ancestor_depth();
        let source_indi_id = calc_alg_context
            .process_context()
            .node(*indi)
            .individual_node_id();
        let succ_links = self.snapshot_successor_links(*indi, calc_alg_context);
        for succ_link in succ_links {
            let creator_indi = calc_alg_context
                .process_context()
                .edge(succ_link)
                .get_creator_individual();
            let creator_indi_id = calc_alg_context
                .process_context()
                .node(creator_indi)
                .individual_node_id();
            if creator_indi_id == source_indi_id {
                let succ_indi = self.get_successor_individual(indi, succ_link, calc_alg_context);
                let prune_succ = {
                    let succ_node = calc_alg_context.process_context().node(succ_indi);
                    succ_node.individual_ancestor_depth() > ancestor_depth
                        && succ_node.is_blockable_individual()
                        && !succ_node.has_purged_blocked_processing_restriction_flags()
                };
                if prune_succ {
                    let mut loc_succ_indi =
                        self.get_localized_individual(succ_indi, false, calc_alg_context);
                    self.prune_successors(&mut loc_succ_indi, *indi, true, calc_alg_context);
                }
            }
        }
    }

    fn snapshot_successor_links(
        &mut self,
        indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Vec<EdgeId> {
        let mut iterator = calc_alg_context
            .process_context()
            .node_successor_iterator(indi);
        let mut links = Vec::new();
        while iterator.has_next() {
            links.push(iterator.next_link(true));
        }
        links
    }

    fn remove_nominal_pruned_links(
        &mut self,
        loc_nom_indi: NodeId,
        pruned_indi_id: Cint64,
        pruned_indi: NodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let links = {
            let mut iterator = calc_alg_context
                .process_context()
                .node_successor_role_iterator(loc_nom_indi, pruned_indi_id);
            let mut links = Vec::new();
            while iterator.has_next() {
                links.push(iterator.next(true));
            }
            links
        };
        for link in links {
            calc_alg_context
                .process_context_mut()
                .node_remove_individual_link(loc_nom_indi, link);
        }
        calc_alg_context
            .process_context_mut()
            .node_remove_individual_connection(loc_nom_indi, pruned_indi);
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
        let role_succ_hash = calc_alg_context
            .process_context()
            .node_reapply_role_successor_hash_existing(*process_indi);
        if role_succ_hash.is_some() {
            let mut role_succ_it = calc_alg_context
                .process_context()
                .role_succ_hash(role_succ_hash)
                .get_role_successor_link_iterator(calc_alg_context.process_context().edges(), role);
            while role_succ_it.has_next() {
                let link = role_succ_it.next(true);
                let succ_indi = self.get_successor_individual(process_indi, link, calc_alg_context);
                let con_label_set = calc_alg_context
                    .process_context_mut()
                    .node_reapply_concept_label_set(succ_indi);
                if self.label_set_contains_concept_resolved(
                    con_label_set,
                    concept,
                    concept_negation,
                    calc_alg_context,
                ) {
                    return true;
                }
            }
        }
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
        let role_succ_hash = calc_alg_context
            .process_context()
            .node_reapply_role_successor_hash_existing(*process_indi);
        if role_succ_hash.is_some() {
            let mut role_succ_it = calc_alg_context
                .process_context()
                .role_succ_hash(role_succ_hash)
                .get_role_successor_link_iterator(calc_alg_context.process_context().edges(), role);
            while role_succ_it.has_next() {
                let link = role_succ_it.next(true);
                let mut succ_indi =
                    self.get_successor_individual(process_indi, link, calc_alg_context);
                if self.contains_individual_node_concepts_negated(
                    &mut succ_indi,
                    concept_linker,
                    negate,
                    calc_alg_context,
                ) {
                    return true;
                }
            }
        }
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
        let role_succ_hash = calc_alg_context
            .process_context()
            .node_reapply_role_successor_hash_existing(*process_indi);
        if role_succ_hash.is_some() {
            let mut role_succ_it = calc_alg_context
                .process_context()
                .role_succ_hash(role_succ_hash)
                .get_role_successor_link_iterator(calc_alg_context.process_context().edges(), role);
            while role_succ_it.has_next() {
                let link = role_succ_it.next(true);
                let mut succ_indi =
                    self.get_successor_individual(process_indi, link, calc_alg_context);
                if self.contains_individual_node_concepts_negated(
                    &mut succ_indi,
                    concept_linker,
                    negate,
                    calc_alg_context,
                ) {
                    return succ_indi;
                }
            }
        }
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
        let role_succ_hash = calc_alg_context
            .process_context()
            .node_reapply_role_successor_hash_existing(*process_indi);
        if role_succ_hash.is_some() {
            let mut role_succ_it = calc_alg_context
                .process_context()
                .role_succ_hash(role_succ_hash)
                .get_role_successor_link_iterator(calc_alg_context.process_context().edges(), role);
            while role_succ_it.has_next() {
                let link = role_succ_it.next(true);
                let mut succ_indi =
                    self.get_successor_individual(process_indi, link, calc_alg_context);
                let succ_indi_id = calc_alg_context
                    .process_context()
                    .node(succ_indi)
                    .individual_node_id();
                let dis_hash = calc_alg_context
                    .process_context()
                    .node_distinct_hash_existing(succ_indi);
                if dis_hash.is_some() {
                    let max_succ_dis_count = calc_alg_context
                        .process_context()
                        .distinct_hash(dis_hash)
                        .get_distinct_count()
                        + 1;
                    if max_succ_dis_count >= distinct_count
                        && self.contains_individual_node_concepts_negated(
                            &mut succ_indi,
                            concept_linker,
                            negate,
                            calc_alg_context,
                        )
                    {
                        let mut succ_dis_count = 1;
                        let mut fail_dis_count = 0;
                        let mut dis_it = calc_alg_context
                            .process_context()
                            .distinct_hash(dis_hash)
                            .get_distinct_iterator();
                        while dis_it.has_next()
                            && max_succ_dis_count - fail_dis_count >= distinct_count
                            && succ_dis_count < distinct_count
                        {
                            let dis_indi_id = dis_it.next_distinct_individual_id(true);
                            if dis_indi_id != succ_indi_id
                                && calc_alg_context
                                    .process_context_mut()
                                    .node_has_role_successor_to_individual_id(
                                        *process_indi,
                                        role,
                                        dis_indi_id,
                                        true,
                                    )
                            {
                                if dis_indi_id < succ_indi_id {
                                    break;
                                }
                                let mut dis_indi = self
                                    .get_up_to_date_individual_by_id(dis_indi_id, calc_alg_context);
                                if dis_indi.is_some()
                                    && self.contains_individual_node_concepts_negated(
                                        &mut dis_indi,
                                        concept_linker,
                                        negate,
                                        calc_alg_context,
                                    )
                                {
                                    succ_dis_count += 1;
                                } else {
                                    fail_dis_count += 1;
                                }
                            }
                        }
                        if succ_dis_count >= distinct_count {
                            return true;
                        }
                    }
                }
            }
        }
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
        for nl in disjoint_role_linker {
            let disjoint_role = nl.target;
            let mut edge = DisjointEdge::new();
            edge.init_negation_disjoint_edge(
                *source_indi,
                *destination_indi,
                disjoint_role,
                dep_track_point,
            );
            let neg_dis_edge = calc_alg_context
                .process_context_mut()
                .alloc_disjoint_edge(edge);

            let link_indi = self.get_individual_node_link(
                source_indi,
                destination_indi,
                disjoint_role,
                calc_alg_context,
            );
            if link_indi.is_some() {
                let link_dep_track_point = calc_alg_context
                    .process_context()
                    .edge(link_indi)
                    .get_dependency_track_point();
                let mut clash_des: ClashDescId = Id::NONE;
                clash_des = self.create_clashed_individual_link_descriptor(
                    clash_des,
                    link_indi,
                    link_dep_track_point,
                    calc_alg_context,
                );
                clash_des = self.create_clashed_negation_disjoint_descriptor(
                    clash_des,
                    neg_dis_edge,
                    dep_track_point,
                    calc_alg_context,
                );
                calc_alg_context.raise_clash(clash_des);
                return;
            }

            calc_alg_context
                .process_context_mut()
                .node_mut(*source_indi)
                .set_disjoint_role_connections(true);
            calc_alg_context
                .process_context_mut()
                .node_mut(*destination_indi)
                .set_disjoint_role_connections(true);
            calc_alg_context
                .process_context_mut()
                .node_install_disjoint_link(*source_indi, neg_dis_edge);
        }
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
        let mut edge = DisjointEdge::new();
        edge.init_negation_disjoint_edge(
            *source_indi,
            *destination_indi,
            negation_role,
            dep_track_point,
        );
        let neg_dis_edge = calc_alg_context
            .process_context_mut()
            .alloc_disjoint_edge(edge);

        let link_indi = self.get_individual_node_link(
            source_indi,
            destination_indi,
            negation_role,
            calc_alg_context,
        );
        if link_indi.is_some() {
            let link_dep_track_point = calc_alg_context
                .process_context()
                .edge(link_indi)
                .get_dependency_track_point();
            let mut clash_des: ClashDescId = Id::NONE;
            clash_des = self.create_clashed_individual_link_descriptor(
                clash_des,
                link_indi,
                link_dep_track_point,
                calc_alg_context,
            );
            clash_des = self.create_clashed_negation_disjoint_descriptor(
                clash_des,
                neg_dis_edge,
                dep_track_point,
                calc_alg_context,
            );
            calc_alg_context.raise_clash(clash_des);
            return;
        }

        calc_alg_context
            .process_context_mut()
            .node_install_disjoint_link(*source_indi, neg_dis_edge);
        calc_alg_context
            .process_context_mut()
            .node_mut(*source_indi)
            .set_disjoint_role_connections(true);
        calc_alg_context
            .process_context_mut()
            .node_mut(*destination_indi)
            .set_disjoint_role_connections(true);
        let source_id = calc_alg_context
            .process_context()
            .node(*source_indi)
            .individual_node_id();
        let conn_set = calc_alg_context
            .process_context_mut()
            .node_connection_successor_set(*destination_indi);
        calc_alg_context
            .process_context_mut()
            .conn_succ_set_mut(conn_set)
            .insert_connection_successor(source_id);
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
        _anc_role: RoleId,
        concept_linker: &[NegLink<ConceptId>],
        negate: bool,
        dep_track_point: TrackPointId,
        saturation_indi_node: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let mut succ_indi = NodeId::NONE;
        let mut merge_link = EdgeId::NONE;
        let role_succ_hash = calc_alg_context
            .process_context()
            .node_reapply_role_successor_hash_existing(*indi);
        if role_succ_hash.is_some() {
            for role_link in role_linker {
                if succ_indi.is_some() {
                    break;
                }
                let role = role_link.target;
                let inv_role = role_link.negated;
                if !inv_role
                    && calc_alg_context
                        .ontology_arenas()
                        .role(role)
                        .is_functional()
                {
                    let mut role_succ_it = calc_alg_context
                        .process_context()
                        .role_succ_hash(role_succ_hash)
                        .get_role_successor_link_iterator(
                            calc_alg_context.process_context().edges(),
                            role,
                        );
                    if role_succ_it.has_next() {
                        let link = role_succ_it.next(false);
                        succ_indi =
                            self.get_localized_successor_individual(indi, link, calc_alg_context);
                        merge_link = link;
                    }
                }
            }
        }

        if succ_indi.is_some() {
            let mut next_all_dep_track_point = TrackPointId::NONE;
            let link_dep_track_point = calc_alg_context
                .process_context()
                .edge(merge_link)
                .get_dependency_track_point();
            let _all_dep_node = self.create_all_dependency(
                &mut next_all_dep_track_point,
                indi,
                con_des,
                dep_track_point,
                link_dep_track_point,
                calc_alg_context,
            );
            let mut sat_caching_possible = true;
            let mut last_sat_cach_possible_con_des = ConDescId::NONE;
            let mut saturation_indi_node = saturation_indi_node;
            if self.conf_expand_created_successors_from_saturation {
                self.try_expansion_from_saturated_data(
                    indi,
                    succ_indi,
                    con_des,
                    next_all_dep_track_point,
                    &mut saturation_indi_node,
                    &mut sat_caching_possible,
                    &mut last_sat_cach_possible_con_des,
                    calc_alg_context,
                );
            }

            let mut new_links_added = false;
            for role_link in role_linker {
                let role = role_link.target;
                let inv_role = role_link.negated;
                if !inv_role {
                    let mut target = succ_indi;
                    if !self.has_individuals_link(indi, &mut target, role, true, calc_alg_context) {
                        self.create_new_individuals_link_reapplyed(
                            *indi,
                            *indi,
                            succ_indi,
                            role,
                            next_all_dep_track_point,
                            calc_alg_context,
                        );
                        new_links_added = true;
                    }
                } else {
                    let mut source = succ_indi;
                    let mut target = *indi;
                    if !self.has_individuals_link(
                        &mut source,
                        &mut target,
                        role,
                        true,
                        calc_alg_context,
                    ) {
                        self.create_new_individuals_link_reapplyed(
                            *indi,
                            succ_indi,
                            *indi,
                            role,
                            next_all_dep_track_point,
                            calc_alg_context,
                        );
                        new_links_added = true;
                    }
                }
            }
            if new_links_added {
                let mut modified = succ_indi;
                self.propagate_individual_node_modified(&mut modified, calc_alg_context);
            }
            let mut target = succ_indi;
            self.add_concepts_to_individual(
                concept_linker,
                negate,
                &mut target,
                next_all_dep_track_point,
                true,
                true,
                None,
                calc_alg_context,
            );
            if self.conf_caching_blocking_from_saturation {
                self.try_establish_saturation_caching(
                    indi,
                    succ_indi,
                    saturation_indi_node,
                    &mut sat_caching_possible,
                    &mut last_sat_cach_possible_con_des,
                    calc_alg_context,
                );
            }
        }
        succ_indi
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
        let mut next_dep_track_point = TrackPointId::NONE;
        let _some_dep_node = self.create_some_dependency(
            &mut next_dep_track_point,
            indi,
            con_des,
            dep_track_point,
            calc_alg_context,
        );
        let is_data_role = calc_alg_context
            .ontology_arenas()
            .role(anc_role)
            .is_data_role();
        let mut succ_indi =
            self.create_new_individual(next_dep_track_point, is_data_role, calc_alg_context);
        let mut sat_caching_possible = true;
        let mut last_sat_cach_possible_con_des = ConDescId::NONE;
        let mut saturation_indi_node = saturation_indi_node;
        if self.conf_expand_created_successors_from_saturation {
            self.try_expansion_from_saturated_data(
                indi,
                succ_indi,
                con_des,
                next_dep_track_point,
                &mut saturation_indi_node,
                &mut sat_caching_possible,
                &mut last_sat_cach_possible_con_des,
                calc_alg_context,
            );
        }
        let anc_link = self.create_new_individuals_links_reapplyed(
            *indi,
            succ_indi,
            role_linker,
            anc_role,
            next_dep_track_point,
            false,
            calc_alg_context,
        );
        let ancestor_depth = calc_alg_context
            .process_context()
            .node(*indi)
            .individual_ancestor_depth();
        let source_flags = calc_alg_context
            .process_context()
            .node(*indi)
            .processing_restriction_flags();
        {
            let succ_node = calc_alg_context.process_context_mut().node_mut(succ_indi);
            succ_node.set_ancestor_link(anc_link);
            succ_node.set_individual_ancestor_depth(ancestor_depth + 1);
            if source_flags
                & (IndividualProcessNode::PRF_SATISFIABLECACHED
                    | IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED)
                != 0
            {
                succ_node.add_processing_restriction_flags(
                    IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED,
                );
            }
            if source_flags
                & (IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED
                    | IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED)
                != 0
            {
                succ_node.add_processing_restriction_flags(
                    IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
                );
            }
            if source_flags
                & (IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHED
                    | IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED)
                != 0
            {
                succ_node.add_processing_restriction_flags(
                    IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED,
                );
            }
        }
        self.add_concepts_to_individual(
            concept_linker,
            negate,
            &mut succ_indi,
            next_dep_track_point,
            true,
            true,
            None,
            calc_alg_context,
        );
        if self.conf_caching_blocking_from_saturation {
            self.try_establish_saturation_caching(
                indi,
                succ_indi,
                saturation_indi_node,
                &mut sat_caching_possible,
                &mut last_sat_cach_possible_con_des,
                calc_alg_context,
            );
        }
        succ_indi
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
        let is_data_role = calc_alg_context
            .ontology_arenas()
            .role(anc_role)
            .is_data_role();
        for _ in 0..succ_card_count {
            let succ_indi =
                self.create_new_individual(dep_track_point, is_data_role, calc_alg_context);
            indi_list.push(succ_indi);
        }
        let mut saturation_indi_node =
            self.get_creation_successor_saturation_node(indi, con_des, calc_alg_context);
        self.create_individuals_distinct(indi_list, dep_track_point, calc_alg_context);

        let ancestor_depth = calc_alg_context
            .process_context()
            .node(*indi)
            .individual_ancestor_depth();
        let source_flags = calc_alg_context
            .process_context()
            .node(*indi)
            .processing_restriction_flags();
        let created_successors = indi_list.clone();
        for mut succ_indi in created_successors {
            let mut sat_caching_possible = true;
            let mut last_sat_cach_possible_con_des = ConDescId::NONE;
            if self.conf_expand_created_successors_from_saturation && saturation_indi_node.is_some()
            {
                self.try_expansion_from_saturated_data(
                    indi,
                    succ_indi,
                    con_des,
                    dep_track_point,
                    &mut saturation_indi_node,
                    &mut sat_caching_possible,
                    &mut last_sat_cach_possible_con_des,
                    calc_alg_context,
                );
            }
            let anc_link = self.create_new_individuals_links_reapplyed(
                *indi,
                succ_indi,
                role_linker,
                anc_role,
                dep_track_point,
                false,
                calc_alg_context,
            );
            {
                let succ_node = calc_alg_context.process_context_mut().node_mut(succ_indi);
                succ_node.set_ancestor_link(anc_link);
                succ_node.set_individual_ancestor_depth(ancestor_depth + 1);
                if source_flags
                    & (IndividualProcessNode::PRF_SATISFIABLECACHED
                        | IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED)
                    != 0
                {
                    succ_node.add_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED,
                    );
                }
                if source_flags
                    & (IndividualProcessNode::PRF_SIGNATUREBLOCKINGCACHED
                        | IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED)
                    != 0
                {
                    succ_node.add_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED,
                    );
                }
                if source_flags
                    & (IndividualProcessNode::PRF_SATURATIONBLOCKINGCACHED
                        | IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED)
                    != 0
                {
                    succ_node.add_processing_restriction_flags(
                        IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED,
                    );
                }
            }
            self.add_concepts_to_individual(
                concept_linker,
                negate,
                &mut succ_indi,
                dep_track_point,
                true,
                true,
                None,
                calc_alg_context,
            );
            if self.conf_caching_blocking_from_saturation && saturation_indi_node.is_some() {
                self.try_establish_saturation_caching(
                    indi,
                    succ_indi,
                    saturation_indi_node,
                    &mut sat_caching_possible,
                    &mut last_sat_cach_possible_con_des,
                    calc_alg_context,
                );
            }
        }
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
        let mut anc_role_link = EdgeId::NONE;
        // W3-DEFER[api]: STATINC(LINKSCREATIONCOUNT, calcAlgContext).
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager().
        let mut generated_inv_link = false;
        let role_chain = role_linker.to_vec();
        for nl in role_chain {
            let role = nl.target;
            let inv_role = nl.negated;
            let disjoint_role_linker = calc_alg_context
                .ontology_arenas()
                .role(role)
                .get_disjoint_role_list()
                .to_vec();

            let mut edge = IndividualLinkEdge::new();
            if !inv_role {
                self.create_individual_node_disjoint_roles_links(
                    indi_source,
                    indi_destination,
                    &disjoint_role_linker,
                    dep_track_point,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    return anc_role_link;
                }
                edge.init_individual_link_edge(
                    *indi_source,
                    *indi_source,
                    *indi_destination,
                    role,
                    dep_track_point,
                );
                let individual_link = calc_alg_context.process_context_mut().alloc_edge(edge);
                self.install_individual_node_role_link(
                    indi_source,
                    indi_destination,
                    individual_link,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    return anc_role_link;
                }
                if anc_role == role {
                    anc_role_link = individual_link;
                }
            } else {
                generated_inv_link = true;
                self.create_individual_node_disjoint_roles_links(
                    indi_destination,
                    indi_source,
                    &disjoint_role_linker,
                    dep_track_point,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    return anc_role_link;
                }
                edge.init_individual_link_edge(
                    *indi_source,
                    *indi_destination,
                    *indi_source,
                    role,
                    dep_track_point,
                );
                let individual_link = calc_alg_context.process_context_mut().alloc_edge(edge);
                self.install_individual_node_role_link(
                    indi_destination,
                    indi_source,
                    individual_link,
                    calc_alg_context,
                );
                if calc_alg_context.has_pending_signal() {
                    return anc_role_link;
                }
                if anc_role == role {
                    anc_role_link = individual_link;
                }
            }
        }

        let indi_source_id = calc_alg_context
            .process_context()
            .node(*indi_source)
            .individual_node_id();
        let indi_destination_id = calc_alg_context
            .process_context()
            .node(*indi_destination)
            .individual_node_id();
        let indi_destination_is_nominal = calc_alg_context
            .process_context()
            .node(*indi_destination)
            .is_nominal_individual_node();
        if generated_inv_link || indi_destination_is_nominal {
            let conn_succ_set = calc_alg_context
                .process_context_mut()
                .node_connection_successor_set(*indi_source);
            calc_alg_context
                .process_context_mut()
                .conn_succ_set_mut(conn_succ_set)
                .insert_connection_successor(indi_destination_id);
        }
        let conn_succ_set = calc_alg_context
            .process_context_mut()
            .node_connection_successor_set(*indi_destination);
        calc_alg_context
            .process_context_mut()
            .conn_succ_set_mut(conn_succ_set)
            .insert_connection_successor(indi_source_id);
        if self.opt_incremental_compatible_expansion {
            self.link_creation_directly_changed_neighbour_connection_update(
                *indi_destination,
                *indi_source,
                true,
                calc_alg_context,
            );
        }
        anc_role_link
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
        if self.raise_role_link_disjoint_clash_if_needed(
            *source_indi,
            *destination_indi,
            individual_link,
            calc_alg_context,
        ) {
            return;
        }

        let mut reapply_iterator = ReapplyQueueIterator::empty();
        let succ_link_count = calc_alg_context
            .process_context_mut()
            .node_install_individual_link(*source_indi, individual_link, &mut reapply_iterator);
        self.update_role_link_occurrence_statistics(
            *source_indi,
            *destination_indi,
            individual_link,
            succ_link_count,
            calc_alg_context,
        );
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
        if self.raise_role_link_disjoint_clash_if_needed(
            *source_indi,
            *destination_indi,
            individual_link,
            calc_alg_context,
        ) {
            return ReapplyQueueIterator::empty();
        }

        let mut reapply_iterator = ReapplyQueueIterator::empty();
        let succ_link_count = calc_alg_context
            .process_context_mut()
            .node_install_individual_link(*source_indi, individual_link, &mut reapply_iterator);
        self.update_role_link_occurrence_statistics(
            *source_indi,
            *destination_indi,
            individual_link,
            succ_link_count,
            calc_alg_context,
        );
        reapply_iterator
    }

    fn update_role_link_occurrence_statistics(
        &mut self,
        source_indi: NodeId,
        destination_indi: NodeId,
        individual_link: EdgeId,
        succ_link_count: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if !self.conf_occurrence_statistics_collecting
            || !self.opt_collect_occurrence_statistics
            || succ_link_count != 1
        {
            return;
        }

        let role = calc_alg_context
            .process_context()
            .edge(individual_link)
            .get_link_role();
        let dep_track_point = calc_alg_context
            .process_context()
            .edge(individual_link)
            .get_dependency_track_point();
        let role_id = calc_alg_context.ontology_arenas().role(role).get_role_tag();
        let concept_count = calc_alg_context.ontology_arenas().concept_count();
        let role_count = calc_alg_context.ontology_arenas().role_count();
        let nondeterministic =
            self.has_nondeterministic_dependency(dep_track_point, calc_alg_context);
        let deterministic_count = if nondeterministic { 0 } else { 1 };
        let nondeterministic_count = if nondeterministic { 1 } else { 0 };
        let source_nominal = calc_alg_context
            .process_context()
            .node(source_indi)
            .nominal_individual()
            .is_some();
        let destination_nominal = calc_alg_context
            .process_context()
            .node(destination_indi)
            .nominal_individual()
            .is_some();
        let individual_count = if source_nominal || destination_nominal {
            1
        } else {
            0
        };
        let existential_count = if source_nominal || destination_nominal {
            0
        } else {
            1
        };

        calc_alg_context
            .occurrence_statistics_cache_handler_mut()
            .inc_role_instance_occurrencce_statistics(
                role_id,
                concept_count,
                role_count,
                deterministic_count,
                nondeterministic_count,
                individual_count,
                existential_count,
                1,
                1,
            );
    }

    fn raise_role_link_disjoint_clash_if_needed(
        &mut self,
        source_indi: NodeId,
        destination_indi: NodeId,
        individual_link: EdgeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let disjoint_hash = calc_alg_context
            .process_context()
            .node(source_indi)
            .use_disjoint_succ_role_hash;
        if disjoint_hash.is_none() {
            return false;
        }
        let dest_id = calc_alg_context
            .process_context()
            .node(destination_indi)
            .individual_node_id();
        let link_role = calc_alg_context
            .process_context()
            .edge(individual_link)
            .get_link_role();
        let neg_dis_edge = calc_alg_context
            .process_context()
            .disjoint_succ_role_hash(disjoint_hash)
            .get_disjoint_successor_role_link(dest_id, link_role);
        if neg_dis_edge.is_none() {
            return false;
        }

        let link_dep_track_point = calc_alg_context
            .process_context()
            .edge(individual_link)
            .get_dependency_track_point();
        let neg_dis_dep_track_point = calc_alg_context
            .process_context()
            .disjoint_edge(neg_dis_edge)
            .get_dependency_track_point();
        let mut clash_des: ClashDescId = Id::NONE;
        clash_des = self.create_clashed_individual_link_descriptor(
            clash_des,
            individual_link,
            link_dep_track_point,
            calc_alg_context,
        );
        clash_des = self.create_clashed_negation_disjoint_descriptor(
            clash_des,
            neg_dis_edge,
            neg_dis_dep_track_point,
            calc_alg_context,
        );
        calc_alg_context.raise_clash(clash_des);
        true
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
        // W3-DEFER[api]: STATINC(LINKSCREATIONCOUNT, calcAlgContext).
        // W3-DEFER[memory-pool]: taskMemMan = calcAlgContext->getUsedProcessTaskMemoryAllocationManager().
        let disjoint_role_linker = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_disjoint_role_list()
            .to_vec();
        self.create_individual_node_disjoint_roles_links(
            indi_source,
            indi_destination,
            &disjoint_role_linker,
            dep_track_point,
            calc_alg_context,
        );
        if calc_alg_context.has_pending_signal() {
            return EdgeId::NONE;
        }
        let mut edge = IndividualLinkEdge::new();
        edge.init_individual_link_edge(
            *indi_creator,
            *indi_source,
            *indi_destination,
            role,
            dep_track_point,
        );
        let individual_link = calc_alg_context.process_context_mut().alloc_edge(edge);
        self.install_individual_node_role_link(
            indi_source,
            indi_destination,
            individual_link,
            calc_alg_context,
        );
        if calc_alg_context.has_pending_signal() {
            return individual_link;
        }
        let indi_source_id = calc_alg_context
            .process_context()
            .node(*indi_source)
            .individual_node_id();
        let conn_succ_set = calc_alg_context
            .process_context_mut()
            .node_connection_successor_set(*indi_destination);
        calc_alg_context
            .process_context_mut()
            .conn_succ_set_mut(conn_succ_set)
            .insert_connection_successor(indi_source_id);
        if self.opt_incremental_compatible_expansion {
            self.link_creation_directly_changed_neighbour_connection_update(
                *indi_destination,
                *indi_source,
                true,
                calc_alg_context,
            );
        }
        individual_link
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
        let dis_edge = calc_alg_context
            .process_context_mut()
            .alloc_distinct_edge(DistinctEdge::new());
        calc_alg_context
            .process_context_mut()
            .distinct_edge_mut(dis_edge)
            .init_distinct_edge(*indi_source, *indi_destination, dep_track_point);

        let source_id = calc_alg_context
            .process_context()
            .node(*indi_source)
            .individual_node_id();
        let destination_id = calc_alg_context
            .process_context()
            .node(*indi_destination)
            .individual_node_id();

        let source_distinct_hash = calc_alg_context
            .process_context_mut()
            .node_distinct_hash(*indi_source);
        calc_alg_context
            .process_context_mut()
            .distinct_hash_mut(source_distinct_hash)
            .insert_distinct_individual(destination_id, dis_edge);

        let destination_distinct_hash = calc_alg_context
            .process_context_mut()
            .node_distinct_hash(*indi_destination);
        calc_alg_context
            .process_context_mut()
            .distinct_hash_mut(destination_distinct_hash)
            .insert_distinct_individual(source_id, dis_edge);
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
        for source_index in 0..indi_list.len() {
            let indi_source = indi_list[source_index];
            for indi_destination in indi_list.iter().skip(source_index + 1).copied() {
                let mut source = indi_source;
                let mut destination = indi_destination;
                self.create_individuals_distinct_pair(
                    &mut source,
                    &mut destination,
                    dep_track_point,
                    calc_alg_context,
                );
            }
        }
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
            .process_context_mut()
            .node_has_role_successor_to_individual_id(*indi_source, role, dest_id, locateable)
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
        // KONCLUDE-PORT-NOTE[api]: the node `initDependencyTracker(depTrackPoint)`
        // derived initializer is represented by the live dependency-track-point setter,
        // matching the descriptor-init convention used elsewhere in the port.
        let mut new_individual = self.create_new_empty_individual(calc_alg_context);
        calc_alg_context
            .process_context_mut()
            .node_mut(new_individual)
            .set_dependency_track_point(dep_track_point);
        if !data_node {
            let top_concept = calc_alg_context
                .processing_data_box()
                .ontology_top_concept();
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
        calc_alg_context.get_up_to_date_individual(indi)
    }
}
