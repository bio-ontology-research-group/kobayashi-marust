//! `saturation::s10` — Node-extension resolve / copy-on-write (port unit #10 of 12).
//!
//! Faithful port of the "group J" node-extension substitution / resolve machinery
//! of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
//! (manifest `03-saturation-calc.md`, PU-SAT-10). Two cpp ranges:
//!
//! Block 1 (cpp 2070–2530):
//!   * `preprocessResolvedIndividualNode`                       (cpp 2070–2083),
//!   * `getResolvedIndividualNodeRepresentativeRangeAssertion`  (cpp 2088–2180),
//!   * `getResolvedIndividualNodeRepresentativeAssertion`       (cpp 2186–2254),
//!   * `getResolvedIndividualNodeAssertion`                     (cpp 2258–2291),
//!   * `getResolvedIndividualNodeExtensionSuccessor`            (cpp 2297–2338),
//!   * `createResolvedIndividualNode`                           (cpp 2342–2363),
//!   * `collectResolveIndividualExtendableConceptMap`           (cpp 2371–2398),
//!   * `getResolvedIndividualNodeExtension` (5 overloads)       (cpp 2401/2405/2443/2449/2512),
//!   * `getResolvedNeighbourIndividualNodeExtension`            (cpp 2497–2508).
//!
//! Block 2 (cpp 5270–5365):
//!   * `getSeparatedSaturationConceptAssertionResolveNode`      (cpp 5270–5298),
//!   * `getIndividualNodeForConcept`                            (cpp 5301–5316),
//!   * `getSaturationIDForIndividualNode`                       (cpp 5319–5333),
//!   * `getIndividualNodeForIndividual`                         (cpp 5336–5365).
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauApproximationSaturationTaskHandleAlgorithm` → `&mut self`.
//! The shared `CCalculationAlgorithmContextBase*` is threaded explicitly as the
//! trailing `calc_alg_context: &mut CalculationAlgorithmContextBase` (the struct
//! wave aliased the `mCalcAlgContext` member to an opaque `Cint64`, so the context
//! is passed by argument per the port-wide convention). The C++
//! `CIndividualSaturationProcessNode*` becomes `SatNodeId` (an id into the per-test
//! `sat_nodes` pool); a `CIndividualSaturationProcessNode*&` in/out reference
//! becomes `&mut SatNodeId`. `CConcept*`/`CRole*`/`CIndividual*` are the static
//! read-shared terminology, ported as `ConceptId`/`RoleId`/`IndividualId` and read
//! through `calc_alg_context.ontology_arenas()`.
//!
//! KONCLUDE-PORT-NOTE[api]: this group's central data structure is
//! `CSaturationIndividualNodeExtensionResolveData` (the per-substitution resolve
//! record, reached via `node->getSuccessorExtensionData(true)->getBaseExtensionResolveData(true)`
//! and threaded through every `getResolved*` method), together with its
//! `CSaturationIndividualNodeExtensionResolveHash`, the
//! `CSaturationSuccessorConceptExtensionMap`, and the
//! `CPROCESSINGHASH<cint64,CConceptNegationPair>` extension maps. These
//! satellites are ported in bounded form as typed arena ids, and the remaining
//! unported dereferences are still flagged `// W4-DEFER[api]` with the C++
//! transcribed verbatim above them. The PORTABLE leaves ARE emitted as real code: node pool-allocation + init in
//! `createResolvedIndividualNode`, the databox resolved-node id counter, label-set
//! creation, the completion-queue add, the model reads (assertion linkers, super
//! roles, range concepts, operator codes, nominal individuals), and the sibling
//! `addConceptFilteredToIndividual` / `preprocessResolvedIndividualNode` /
//! `initializeIndividualNodeByCoping` / `addIndividualToCompletionQueue` calls
//! (these land in other `s01..s12` units and are invoked as `self.x(...)`). No
//! logic is dropped.
//!
//! KONCLUDE-PORT-NOTE[overload]: Rust cannot overload, so the five C++
//! `getResolvedIndividualNodeExtension` overloads get distinct names by their
//! discriminating argument: `..._for_con_map` / `..._for_con_map_created`
//! (the `CPROCESSINGHASH` map), `..._for_node` / `..._for_node_created`
//! (the extension `CIndividualSaturationProcessNode*`), and the bare
//! `get_resolved_individual_node_extension` (the `(concept, negation)` leaf — the
//! one the representative/assertion methods call). The 6-arg label-set
//! `addConceptFilteredToIndividual` overload is called as
//! `add_concept_filtered_to_individual_for_label_set` (group K, other s-unit).
//! `bool* newNodeExpansionCreated` → `Option<&mut bool>`.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::op::CCNOMINAL;
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, IndividualId, RoleId};
use super::super::process::sat_node::IndividualSaturationProcessNode;
use super::super::process::SatNodeId;
use super::satellites::{
    ConceptNegationPair, ConceptSaturationDescriptorId,
    ImplicationReapplyConceptSaturationDescriptorId, SaturationConceptExtensionMap,
    SaturationConceptExtensionMapId, SaturationIndividualNodeExtensionResolveData,
    SaturationIndividualNodeExtensionResolveDataId, SaturationSuccessorConceptExtensionMapId,
};

impl super::algorithm::SaturationTaskHandleAlgorithm {
    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::preprocessResolvedIndividualNode`
    /// (cpp 2070–2083).
    ///
    /// Drains the resolved node's pending concept-saturation linker chain, applying
    /// each as a tableau saturation rule. Fully portable: the linker take/apply/
    /// release leaves all have ported siblings.
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ `CIndividualSaturationProcessNode*
    /// resolvedIndiProcSatNode` is taken by value but handed to
    /// `applyTableauSaturationRule(...&...)` by reference, so a substituting rule
    /// can rebind it; ported as `mut resolved_indi_proc_sat_node: SatNodeId` passed
    /// `&mut` so the subsequent `take` sees the (possibly rebound) node.
    pub fn preprocess_resolved_individual_node(
        &mut self,
        mut resolved_indi_proc_sat_node: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut processed = false;
        let mut concept_saturation_process_linker = calc_alg_context
            .process_context_mut()
            .sat_node_take_concept_saturation_process_linker(resolved_indi_proc_sat_node);
        while concept_saturation_process_linker.is_some() {
            // STATINC(RULEAPPLICATIONCOUNT, calcAlgContext); — W4-DEFER[macro]
            // KONCLUCE_..._SATURATION_MODEL_STRING_INSTRUCTION(mRuleBeginDebugIndiModelString = ...) — W4-DEFER[macro]
            self.apply_tableau_saturation_rule(
                &mut resolved_indi_proc_sat_node,
                concept_saturation_process_linker,
                calc_alg_context,
            );
            // KONCLUCE_..._SATURATION_MODEL_STRING_INSTRUCTION(mRuleEndDebugIndiModelString = ...) — W4-DEFER[macro]
            self.release_concept_saturation_process_linker(
                concept_saturation_process_linker,
                calc_alg_context,
            );
            concept_saturation_process_linker = calc_alg_context
                .process_context_mut()
                .sat_node_take_concept_saturation_process_linker(resolved_indi_proc_sat_node);
            processed = true;
        }
        processed
    }

    fn base_extension_resolve_data_for_node(
        &mut self,
        indi_proc_sat_node: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SaturationIndividualNodeExtensionResolveDataId {
        let succ_ext = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(indi_proc_sat_node, true);
        calc_alg_context
            .process_context_mut()
            .sat_successor_extension_base_extension_resolve_data(succ_ext, true)
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeRepresentativeRangeAssertion`
    /// (cpp 2088–2180).
    pub fn get_resolved_individual_node_representative_range_assertion(
        &mut self,
        indi_proc_sat_node: SatNodeId,
        nominal_indi: IndividualId,
        role: RoleId,
        inversed_role: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let mut resolved_node = SatNodeId::NONE;
        let mut resolve_data =
            self.base_extension_resolve_data_for_node(indi_proc_sat_node, calc_alg_context);
        let mut copy_indi_proc_sat_node = indi_proc_sat_node;
        // CConceptAssertionLinker* conAssLinker = nominalIndi->getAssertionConceptLinker();
        // KONCLUDE-PORT-NOTE[ownership]: snapshot the assertion-concept chain before the
        //   `&mut calc_alg_context` resolve calls (the iteration re-reads it twice).
        let con_ass_linker: Vec<(ConceptId, bool)> = calc_alg_context
            .ontology_arenas()
            .individual(nominal_indi)
            .get_assertion_concept_linker()
            .iter()
            .map(|a| (a.target, a.negated))
            .collect();
        let top_concept = calc_alg_context
            .processing_data_box()
            .ontology_top_concept();
        let nominal_concept = calc_alg_context
            .ontology_arenas()
            .individual(nominal_indi)
            .get_individual_nominal_concept();

        // resolve individual
        for &(concept, negated) in &con_ass_linker {
            if concept == nominal_concept {
                if negated {
                    resolve_data = self.get_resolved_individual_node_extension(
                        resolve_data,
                        top_concept,
                        true,
                        &mut copy_indi_proc_sat_node,
                        calc_alg_context,
                    );
                }
            } else {
                let op_code = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_operator_code();
                if op_code == CCNOMINAL {
                    let nominal_individual = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_nominal_individual();
                    if nominal_individual == nominal_indi {
                        if negated {
                            resolve_data = self.get_resolved_individual_node_extension(
                                resolve_data,
                                top_concept,
                                true,
                                &mut copy_indi_proc_sat_node,
                                calc_alg_context,
                            );
                        }
                    } else if !negated {
                        resolve_data = self.get_resolved_individual_node_extension(
                            resolve_data,
                            concept,
                            negated,
                            &mut copy_indi_proc_sat_node,
                            calc_alg_context,
                        );
                    }
                } else {
                    resolve_data = self.get_resolved_individual_node_extension(
                        resolve_data,
                        concept,
                        negated,
                        &mut copy_indi_proc_sat_node,
                        calc_alg_context,
                    );
                }
            }
        }

        // Snapshot the (superRole, rangeConcept-list) structure once for the resolve pass.
        // KONCLUDE-PORT-NOTE[identity]: self-inclusive super-role list (see s02).
        let super_role_list: Vec<(RoleId, bool)> =
            Self::saturation_indirect_super_roles(role, calc_alg_context)
                .iter()
                .map(|r| (r.target, r.negated))
                .collect();
        for &(super_role, super_role_negated) in &super_role_list {
            let range_con_linker: Vec<(ConceptId, bool)> = calc_alg_context
                .ontology_arenas()
                .role(super_role)
                .get_relative_range_concept_list(super_role_negated ^ inversed_role)
                .iter()
                .map(|c| (c.target, c.negated))
                .collect();
            for &(range_concept, range_concept_negation) in &range_con_linker {
                resolve_data = self.get_resolved_individual_node_extension(
                    resolve_data,
                    range_concept,
                    range_concept_negation,
                    &mut copy_indi_proc_sat_node,
                    calc_alg_context,
                );
            }
        }

        resolve_data = self.get_resolved_neighbour_individual_node_extension(
            resolve_data,
            &mut copy_indi_proc_sat_node,
            calc_alg_context,
        );

        if !calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(resolve_data)
            .has_processing_individual_node()
        {
            // create individual
            resolved_node = self.create_resolved_individual_node(
                resolve_data,
                &mut copy_indi_proc_sat_node,
                true,
                calc_alg_context,
            );
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .set_abox_individual_representation_node(true);
            let separated = calc_alg_context
                .process_context()
                .sat_node(indi_proc_sat_node)
                .is_separated();
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .set_separated(separated);
            // CReapplyConceptSaturationLabelSet* conSet = resolvedNode->getReapplyConceptSaturationLabelSet(true);
            //   (dead local in C++ — created for side-effect only)
            let _con_set = calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .get_reapply_concept_saturation_label_set(true);

            // add all concepts to individual
            for &(concept, negated) in &con_ass_linker {
                if concept == nominal_concept {
                    if negated {
                        self.add_concept_filtered_to_individual(
                            top_concept,
                            true,
                            &mut resolved_node,
                            calc_alg_context,
                        );
                    }
                } else {
                    let op_code = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_operator_code();
                    if op_code == CCNOMINAL {
                        let nominal_individual = calc_alg_context
                            .ontology_arenas()
                            .concept(concept)
                            .get_nominal_individual();
                        if nominal_individual == nominal_indi {
                            if negated {
                                self.add_concept_filtered_to_individual(
                                    top_concept,
                                    true,
                                    &mut resolved_node,
                                    calc_alg_context,
                                );
                            }
                        } else if !negated {
                            self.add_concept_filtered_to_individual(
                                concept,
                                negated,
                                &mut resolved_node,
                                calc_alg_context,
                            );
                        }
                    } else {
                        self.add_concept_filtered_to_individual(
                            concept,
                            negated,
                            &mut resolved_node,
                            calc_alg_context,
                        );
                    }
                }
            }

            for &(super_role, super_role_negated) in &super_role_list {
                let range_con_linker: Vec<(ConceptId, bool)> = calc_alg_context
                    .ontology_arenas()
                    .role(super_role)
                    .get_relative_range_concept_list(super_role_negated ^ inversed_role)
                    .iter()
                    .map(|c| (c.target, c.negated))
                    .collect();
                for &(range_concept, range_concept_negation) in &range_con_linker {
                    self.add_concept_filtered_to_individual(
                        range_concept,
                        range_concept_negation,
                        &mut resolved_node,
                        calc_alg_context,
                    );
                }
            }

            self.preprocess_resolved_individual_node(resolved_node, calc_alg_context);
        }
        calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(resolve_data)
            .get_processing_individual_node()
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeRepresentativeAssertion`
    /// (cpp 2186–2254).
    pub fn get_resolved_individual_node_representative_assertion(
        &mut self,
        indi_proc_sat_node: SatNodeId,
        nominal_indi: IndividualId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let mut resolved_node = SatNodeId::NONE;
        let mut resolve_data =
            self.base_extension_resolve_data_for_node(indi_proc_sat_node, calc_alg_context);
        let mut copy_indi_proc_sat_node = indi_proc_sat_node;
        let con_ass_linker: Vec<(ConceptId, bool)> = calc_alg_context
            .ontology_arenas()
            .individual(nominal_indi)
            .get_assertion_concept_linker()
            .iter()
            .map(|a| (a.target, a.negated))
            .collect();
        let top_concept = calc_alg_context
            .processing_data_box()
            .ontology_top_concept();
        let nominal_concept = calc_alg_context
            .ontology_arenas()
            .individual(nominal_indi)
            .get_individual_nominal_concept();

        // resolve individual
        for &(concept, negated) in &con_ass_linker {
            if concept == nominal_concept {
                if negated {
                    resolve_data = self.get_resolved_individual_node_extension(
                        resolve_data,
                        top_concept,
                        true,
                        &mut copy_indi_proc_sat_node,
                        calc_alg_context,
                    );
                }
            } else {
                let op_code = calc_alg_context
                    .ontology_arenas()
                    .concept(concept)
                    .get_operator_code();
                if op_code == CCNOMINAL {
                    let nominal_individual = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_nominal_individual();
                    if nominal_individual == nominal_indi {
                        if negated {
                            resolve_data = self.get_resolved_individual_node_extension(
                                resolve_data,
                                top_concept,
                                true,
                                &mut copy_indi_proc_sat_node,
                                calc_alg_context,
                            );
                        }
                    } else {
                        resolve_data = self.get_resolved_individual_node_extension(
                            resolve_data,
                            concept,
                            negated,
                            &mut copy_indi_proc_sat_node,
                            calc_alg_context,
                        );
                    }
                } else {
                    resolve_data = self.get_resolved_individual_node_extension(
                        resolve_data,
                        concept,
                        negated,
                        &mut copy_indi_proc_sat_node,
                        calc_alg_context,
                    );
                }
            }
        }

        resolve_data = self.get_resolved_neighbour_individual_node_extension(
            resolve_data,
            &mut copy_indi_proc_sat_node,
            calc_alg_context,
        );

        if !calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(resolve_data)
            .has_processing_individual_node()
        {
            // create individual
            resolved_node = self.create_resolved_individual_node(
                resolve_data,
                &mut copy_indi_proc_sat_node,
                true,
                calc_alg_context,
            );
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .set_abox_individual_representation_node(true);
            let separated = calc_alg_context
                .process_context()
                .sat_node(indi_proc_sat_node)
                .is_separated();
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .set_separated(separated);
            let _con_set = calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .get_reapply_concept_saturation_label_set(true);

            // add all concepts to individual
            for &(concept, negated) in &con_ass_linker {
                if concept == nominal_concept {
                    if negated {
                        self.add_concept_filtered_to_individual(
                            top_concept,
                            true,
                            &mut resolved_node,
                            calc_alg_context,
                        );
                    }
                } else {
                    let op_code = calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_operator_code();
                    if op_code == CCNOMINAL {
                        let nominal_individual = calc_alg_context
                            .ontology_arenas()
                            .concept(concept)
                            .get_nominal_individual();
                        if nominal_individual == nominal_indi {
                            if negated {
                                self.add_concept_filtered_to_individual(
                                    top_concept,
                                    true,
                                    &mut resolved_node,
                                    calc_alg_context,
                                );
                            }
                        } else {
                            self.add_concept_filtered_to_individual(
                                concept,
                                negated,
                                &mut resolved_node,
                                calc_alg_context,
                            );
                        }
                    } else {
                        self.add_concept_filtered_to_individual(
                            concept,
                            negated,
                            &mut resolved_node,
                            calc_alg_context,
                        );
                    }
                }
            }

            self.preprocess_resolved_individual_node(resolved_node, calc_alg_context);
        }
        calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(resolve_data)
            .get_processing_individual_node()
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeAssertion`
    /// (cpp 2258–2291).
    pub fn get_resolved_individual_node_assertion(
        &mut self,
        indi_proc_sat_node: SatNodeId,
        nominal_indi: IndividualId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let mut resolved_node = SatNodeId::NONE;
        let mut resolve_data =
            self.base_extension_resolve_data_for_node(indi_proc_sat_node, calc_alg_context);
        let mut copy_indi_proc_sat_node = indi_proc_sat_node;
        let con_ass_linker: Vec<(ConceptId, bool)> = calc_alg_context
            .ontology_arenas()
            .individual(nominal_indi)
            .get_assertion_concept_linker()
            .iter()
            .map(|a| (a.target, a.negated))
            .collect();
        let nominal_concept = calc_alg_context
            .ontology_arenas()
            .individual(nominal_indi)
            .get_individual_nominal_concept();

        // resolve individual
        for &(concept, negated) in &con_ass_linker {
            if negated || concept != nominal_concept {
                resolve_data = self.get_resolved_individual_node_extension(
                    resolve_data,
                    concept,
                    negated,
                    &mut copy_indi_proc_sat_node,
                    calc_alg_context,
                );
            }
        }

        if !calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(resolve_data)
            .has_processing_individual_node()
        {
            // create individual
            resolved_node = self.create_resolved_individual_node(
                resolve_data,
                &mut copy_indi_proc_sat_node,
                true,
                calc_alg_context,
            );
            let separated = calc_alg_context
                .process_context()
                .sat_node(indi_proc_sat_node)
                .is_separated();
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .set_separated(separated);
            let _con_set = calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .get_reapply_concept_saturation_label_set(true);

            // add all concepts to individual
            for &(concept, negated) in &con_ass_linker {
                if negated || concept != nominal_concept {
                    self.add_concept_filtered_to_individual(
                        concept,
                        negated,
                        &mut resolved_node,
                        calc_alg_context,
                    );
                }
            }

            self.preprocess_resolved_individual_node(resolved_node, calc_alg_context);
        }
        calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(resolve_data)
            .get_processing_individual_node()
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeExtensionSuccessor`
    /// (cpp 2297–2338).
    ///
    pub fn get_resolved_individual_node_extension_successor(
        &mut self,
        indi_proc_sat_node: SatNodeId,
        succ_con_ext_map: SaturationSuccessorConceptExtensionMapId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let mut resolve_data =
            self.base_extension_resolve_data_for_node(indi_proc_sat_node, calc_alg_context);
        let mut copy_indi_proc_sat_node = indi_proc_sat_node;

        // resolve individual
        // Konclude's process hash has one deterministic hash function for every
        // map. Rust's `HashMap` randomizes each map independently, which would
        // send identical extension sets down different resolve-cache paths.
        let mut extension_data: Vec<_> = calc_alg_context
            .process_context()
            .sat_successor_concept_extension_map(succ_con_ext_map)
            .iter()
            .map(|(&tag, data)| (tag, *data))
            .collect();
        extension_data.sort_unstable_by_key(|(tag, _)| *tag);
        for (_, con_ext_dat) in &extension_data {
            let concept = con_ext_dat.concept;
            let add_positive = con_ext_dat.positive;
            let add_negative = con_ext_dat.negative;
            if add_positive {
                resolve_data = self.get_resolved_individual_node_extension(
                    resolve_data,
                    concept,
                    false,
                    &mut copy_indi_proc_sat_node,
                    calc_alg_context,
                );
            }
            if add_negative {
                resolve_data = self.get_resolved_individual_node_extension(
                    resolve_data,
                    concept,
                    true,
                    &mut copy_indi_proc_sat_node,
                    calc_alg_context,
                );
            }
        }

        if !calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(resolve_data)
            .has_processing_individual_node()
        {
            // create individual
            let mut resolved_node = self.create_resolved_individual_node(
                resolve_data,
                &mut copy_indi_proc_sat_node,
                true,
                calc_alg_context,
            );
            let con_set = calc_alg_context
                .process_context_mut()
                .sat_node_reapply_concept_saturation_label_set(resolved_node, true);

            // add all concepts to individual
            for (_, con_ext_dat) in &extension_data {
                let concept = con_ext_dat.concept;
                let add_positive = con_ext_dat.positive;
                let add_negative = con_ext_dat.negative;
                if add_positive {
                    let mut resolved_node_ref = resolved_node;
                    self.add_concept_filtered_to_individual_label_set(
                        concept,
                        false,
                        &mut resolved_node_ref,
                        con_set,
                        true,
                        calc_alg_context,
                    );
                }
                if add_negative {
                    let mut resolved_node_ref = resolved_node;
                    self.add_concept_filtered_to_individual_label_set(
                        concept,
                        true,
                        &mut resolved_node_ref,
                        con_set,
                        true,
                        calc_alg_context,
                    );
                }
            }

            self.preprocess_resolved_individual_node(resolved_node, calc_alg_context);
        }
        calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(resolve_data)
            .get_processing_individual_node()
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::createResolvedIndividualNode`
    /// (cpp 2342–2363).
    ///
    /// Pool-allocates a fresh resolved saturation node, copies the base node's
    /// label into it, registers it with the resolve record, queues it for
    /// completion + (optionally) processing, and tracks it in the saturation node
    /// vector.
    ///
    /// KONCLUDE-PORT-NOTE[memory-pool]: the C++ `CObjectParameterizingAllocator<
    /// CIndividualSaturationProcessNode,CProcessContext*>::allocateAndConstructAndParameterize(
    /// memMan, processContext)` becomes `ctx.process_context_mut().alloc_sat_node(
    /// IndividualSaturationProcessNode::new(INVALID))` (the typed arena replaces the
    /// pool; the `CProcessContext*` ctor arg is the opaque `Cint64` the node carries).
    pub fn create_resolved_individual_node(
        &mut self,
        resolve_data: SaturationIndividualNodeExtensionResolveDataId,
        copy_indi_proc_sat_node: &mut SatNodeId,
        queue_processing: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let mut resolved_node = calc_alg_context
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
        let processing_individual_node_id = calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(resolve_data)
            .get_processing_individual_node_id();
        calc_alg_context
            .process_context_mut()
            .sat_node_mut(resolved_node)
            .init_individual_saturation_process_node(
                processing_individual_node_id,
                Id::NONE,
                Id::NONE,
            );
        // `initializeIndividualNodeByCoping` performs the copy initialization
        // itself (C++ 2346 -> 2022). Calling the raw node initializer first
        // duplicates the copy setup and its dependent-link registration.
        self.initialize_individual_node_by_coping(
            resolved_node,
            *copy_indi_proc_sat_node,
            false,
            calc_alg_context,
        );

        calc_alg_context
            .process_context_mut()
            .sat_indi_node_ext_resolve_data_mut(resolve_data)
            .set_processing_individual_node(resolved_node);
        let resolved_succ_ext = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(resolved_node, true);
        calc_alg_context
            .process_context_mut()
            .sat_indi_node_succ_ext_data_mut(resolved_succ_ext)
            .set_extension_resolve_data(resolve_data);
        calc_alg_context
            .process_context_mut()
            .sat_node_mut(resolved_node)
            .set_initialized(true);
        calc_alg_context
            .process_context_mut()
            .sat_node_mut(resolved_node)
            .set_required_backward_propagation(true);
        self.add_individual_to_completion_queue(&mut resolved_node, calc_alg_context);

        // CIndividualSaturationProcessNodeLinker* resolveNodeProcessLiner =
        //   CObjectAllocator<CIndividualSaturationProcessNodeLinker>::allocateAndConstruct(memMan);
        // resolveNodeProcessLiner->initProcessNodeLinker(resolvedNode, queueProcessing);
        let resolve_node_process_liner = calc_alg_context
            .process_context_mut()
            .sat_node_individual_saturation_process_node_linker(resolved_node, true);
        calc_alg_context
            .process_context_mut()
            .indi_sat_process_node_linker_mut(resolve_node_process_liner)
            .set_processing_queued(queue_processing);
        if queue_processing {
            calc_alg_context
                .processing_data_box_mut()
                .add_individual_saturation_process_node_linker(resolve_node_process_liner);
        }
        // indiVec = ctx->getUsedProcessingDataBox()->getIndividualSaturationProcessNodeVector(true);
        let resolved_node_individual_id = calc_alg_context
            .process_context()
            .sat_node(resolved_node)
            .get_individual_id();
        calc_alg_context
            .processing_data_box_mut()
            .individual_saturation_process_node_vector(true)
            .expect("create=true yields CIndividualSaturationProcessNodeVector")
            .set_data(resolved_node_individual_id, resolved_node);
        resolved_node
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::collectResolveIndividualExtendableConceptMap`
    /// (cpp 2371–2398).
    ///
    /// KONCLUDE-PORT-NOTE[api]: both label sets (`CReapplyConceptSaturationLabelSet`)
    /// and the descriptor chain (`CConceptSaturationDescriptor`) plus the extension
    /// map (`CPROCESSINGHASH<cint64,CConceptNegationPair>`) is represented as a
    /// typed temporary arena id. `conExtMap` is an in/out pointer reference.
    pub fn collect_resolve_individual_extendable_concept_map(
        &mut self,
        base_indi_node: SatNodeId,
        extension_indi_node: SatNodeId,
        con_ext_map: &mut SaturationConceptExtensionMapId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let ext_con_set = calc_alg_context
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(extension_indi_node, false);
        let mut extension_required = false;
        if ext_con_set.is_none() {
            return false;
        }
        let mut con_it = calc_alg_context
            .process_context()
            .reapply_con_sat_label_set(ext_con_set)
            .get_concept_saturation_description_linker();
        while con_it.is_some() {
            let (concept, negation, con_tag, next_con_it) = {
                let con_ref = calc_alg_context.process_context().con_sat_desc(con_it);
                (
                    con_ref.get_concept(),
                    con_ref.get_negation(),
                    con_ref.get_concept_tag(calc_alg_context.ontology_arenas()),
                    con_ref.get_next_concept_desciptor(),
                )
            };
            let mut insertion_required = false;
            let base_con_set = calc_alg_context
                .process_context_mut()
                .sat_node_reapply_concept_saturation_label_set(base_indi_node, false);
            if base_con_set.is_some() {
                let mut contained_con_des = ConceptSaturationDescriptorId::NONE;
                let mut contained_imp_rea_des =
                    ImplicationReapplyConceptSaturationDescriptorId::NONE;
                if calc_alg_context
                    .process_context()
                    .reapply_con_sat_label_set(base_con_set)
                    .get_concept_saturation_descriptor_by_tag(
                        con_tag,
                        &mut contained_con_des,
                        &mut contained_imp_rea_des,
                    )
                {
                    if contained_con_des.is_none()
                        || calc_alg_context
                            .process_context()
                            .con_sat_desc(contained_con_des)
                            .get_negation()
                            != negation
                    {
                        insertion_required = true;
                    }
                } else {
                    insertion_required = true;
                }
            } else {
                insertion_required = true;
            }

            if insertion_required {
                extension_required = true;
                if con_ext_map.is_none() {
                    *con_ext_map = calc_alg_context
                        .process_context_mut()
                        .alloc_sat_concept_extension_map(SaturationConceptExtensionMap::new());
                }
                calc_alg_context
                    .process_context_mut()
                    .sat_concept_extension_map_mut(*con_ext_map)
                    .insert(con_tag, ConceptNegationPair::new(concept, negation));
            }
            con_it = next_con_it;
        }
        extension_required
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeExtension`
    /// (cpp 2401–2403; the `CPROCESSINGHASH` overload, forwarding wrapper).
    ///
    /// KONCLUDE-PORT-NOTE[overload]: C++ overload distinguished by the
    /// `CPROCESSINGHASH<cint64,CConceptNegationPair>* conExtensionMap` arg.
    /// Forwards to `..._for_con_map_created` with `newNodeExpansionCreated == nullptr`.
    pub fn get_resolved_individual_node_extension_for_con_map(
        &mut self,
        resolve_data: SaturationIndividualNodeExtensionResolveDataId,
        con_extension_map: SaturationConceptExtensionMapId,
        copy_indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SaturationIndividualNodeExtensionResolveDataId {
        self.get_resolved_individual_node_extension_for_con_map_created(
            resolve_data,
            con_extension_map,
            copy_indi_proc_sat_node,
            None,
            calc_alg_context,
        )
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeExtension`
    /// (cpp 2405–2438; the `CPROCESSINGHASH` + `bool* newNodeExpansionCreated` overload).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: `conExtensionMap`
    /// (`CPROCESSINGHASH<cint64,CConceptNegationPair>*`) is represented as a typed
    /// temporary arena id; when non-null, Konclude iterates it twice (resolve pass,
    /// then — if no processing node yet — create + add pass).
    /// `bool* newNodeExpansionCreated` → `Option<&mut bool>`.
    pub fn get_resolved_individual_node_extension_for_con_map_created(
        &mut self,
        mut resolve_data: SaturationIndividualNodeExtensionResolveDataId,
        con_extension_map: SaturationConceptExtensionMapId,
        copy_indi_proc_sat_node: &mut SatNodeId,
        new_node_expansion_created: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SaturationIndividualNodeExtensionResolveDataId {
        if con_extension_map.is_some() {
            let mut extension_pairs: Vec<(Cint64, ConceptNegationPair)> = calc_alg_context
                .process_context()
                .sat_concept_extension_map(con_extension_map)
                .iter()
                .map(|(&tag, pair)| (tag, *pair))
                .collect();
            extension_pairs.sort_unstable_by_key(|(tag, _)| *tag);

            for (_, con_ext_dat) in &extension_pairs {
                resolve_data = self.get_resolved_individual_node_extension(
                    resolve_data,
                    con_ext_dat.concept,
                    con_ext_dat.negation,
                    copy_indi_proc_sat_node,
                    calc_alg_context,
                );
            }

            if !calc_alg_context
                .process_context()
                .sat_indi_node_ext_resolve_data(resolve_data)
                .has_processing_individual_node()
            {
                let resolved_node = self.create_resolved_individual_node(
                    resolve_data,
                    copy_indi_proc_sat_node,
                    true,
                    calc_alg_context,
                );

                let mut resolved_node_ref = resolved_node;
                for (_, con_ext_dat) in &extension_pairs {
                    self.add_concept_filtered_to_individual(
                        con_ext_dat.concept,
                        con_ext_dat.negation,
                        &mut resolved_node_ref,
                        calc_alg_context,
                    );
                }
                self.preprocess_resolved_individual_node(resolved_node, calc_alg_context);

                if let Some(flag) = new_node_expansion_created {
                    *flag = true;
                }
            }

            *copy_indi_proc_sat_node = calc_alg_context
                .process_context()
                .sat_indi_node_ext_resolve_data(resolve_data)
                .get_processing_individual_node();
        }
        resolve_data
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeExtension`
    /// (cpp 2443–2445; the extension-`CIndividualSaturationProcessNode*` overload, forwarding wrapper).
    pub fn get_resolved_individual_node_extension_for_node(
        &mut self,
        resolve_data: SaturationIndividualNodeExtensionResolveDataId,
        extension_node: SatNodeId,
        copy_indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SaturationIndividualNodeExtensionResolveDataId {
        self.get_resolved_individual_node_extension_for_node_created(
            resolve_data,
            extension_node,
            copy_indi_proc_sat_node,
            None,
            calc_alg_context,
        )
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeExtension`
    /// (cpp 2449–2487; the extension-node + `bool* newNodeExpansionCreated` overload).
    ///
    /// KONCLUDE-PORT-NOTE[api]: caches the result keyed by `extensionNode` in
    /// `resolveData`'s `CSaturationIndividualNodeExtensionResolveHash`; on a miss,
    /// builds the concept-extension map by diffing the extension node's label
    /// against the copy node's label, then delegates to the `..._for_con_map`
    /// overload.
    pub fn get_resolved_individual_node_extension_for_node_created(
        &mut self,
        mut resolve_data: SaturationIndividualNodeExtensionResolveDataId,
        extension_node: SatNodeId,
        copy_indi_proc_sat_node: &mut SatNodeId,
        new_node_expansion_created: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SaturationIndividualNodeExtensionResolveDataId {
        let hash = calc_alg_context
            .process_context_mut()
            .sat_extension_resolve_hash(resolve_data, true);
        let mut child_resolve_data = calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_hash(hash)
            .get_non_creating_resolved_individual_node_extension_data_for_node(extension_node)
            .resolve_data;
        if child_resolve_data.is_none() {
            // CReapplyConceptSaturationLabelSet* extConSet = extensionNode->getReapplyConceptSaturationLabelSet(false);
            let _ext_con_set = calc_alg_context
                .process_context_mut()
                .sat_node_mut(extension_node)
                .get_reapply_concept_saturation_label_set(false);

            // CPROCESSINGHASH<cint64,CConceptNegationPair>* conExtensionMap = nullptr;
            let mut con_extension_map = SaturationConceptExtensionMapId::NONE;
            self.collect_resolve_individual_extendable_concept_map(
                *copy_indi_proc_sat_node,
                extension_node,
                &mut con_extension_map,
                calc_alg_context,
            );

            resolve_data = self.get_resolved_individual_node_extension_for_con_map_created(
                resolve_data,
                con_extension_map,
                copy_indi_proc_sat_node,
                new_node_expansion_created,
                calc_alg_context,
            );

            child_resolve_data = resolve_data;
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_ext_resolve_hash_mut(hash)
                .get_resolved_individual_node_extension_data_for_node(extension_node)
                .resolve_data = child_resolve_data;
        }
        if calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(child_resolve_data)
            .has_processing_individual_node()
        {
            *copy_indi_proc_sat_node = calc_alg_context
                .process_context()
                .sat_indi_node_ext_resolve_data(child_resolve_data)
                .get_processing_individual_node();
        }
        child_resolve_data
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedNeighbourIndividualNodeExtension`
    /// (cpp 2497–2508).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the neighbour slot of `resolveData`'s resolve hash
    /// (`getResolvedNeighbourIndividualNodeExtensionData()`) is unported; on a miss
    /// it pool-allocates a fresh `CSaturationIndividualNodeExtensionResolveData` and
    /// inits it with the next resolved-successor-extension node id. The PORTABLE
    /// leaf is the databox id counter, emitted as real code.
    pub fn get_resolved_neighbour_individual_node_extension(
        &mut self,
        resolve_data: SaturationIndividualNodeExtensionResolveDataId,
        copy_indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SaturationIndividualNodeExtensionResolveDataId {
        let hash = calc_alg_context
            .process_context_mut()
            .sat_extension_resolve_hash(resolve_data, true);
        let mut neighbour_data = calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_hash(hash)
            .neighbour_resolve_data
            .resolve_data;
        if neighbour_data.is_none() {
            let next_resolve_indi_id = calc_alg_context
                .next_saturation_resolved_successor_extension_individual_node_id(true);
            let mut data = SaturationIndividualNodeExtensionResolveData::new();
            data.init_extension_resolve_data_for_id(next_resolve_indi_id);
            neighbour_data = calc_alg_context
                .process_context_mut()
                .alloc_sat_indi_node_ext_resolve_data(data);
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_ext_resolve_hash_mut(hash)
                .neighbour_resolve_data
                .resolve_data = neighbour_data;
        }
        if calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(neighbour_data)
            .has_processing_individual_node()
        {
            *copy_indi_proc_sat_node = calc_alg_context
                .process_context()
                .sat_indi_node_ext_resolve_data(neighbour_data)
                .get_processing_individual_node();
        }
        neighbour_data
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeExtension`
    /// (cpp 2512–2528; the `(concept, negation)` leaf overload — the one the
    /// representative / assertion methods call).
    ///
    /// KONCLUDE-PORT-NOTE[api]: short-circuits when the copy node's label already
    /// contains `(concept, negation)` (`CReapplyConceptSaturationLabelSet::containsConcept`,
    /// unported); otherwise caches a fresh resolve record keyed by `(concept,
    /// negation)` in `resolveData`'s resolve hash (unported). PORTABLE leaf: the
    /// databox resolved-node id counter on a miss.
    pub fn get_resolved_individual_node_extension(
        &mut self,
        resolve_data: SaturationIndividualNodeExtensionResolveDataId,
        concept: ConceptId,
        negation: bool,
        copy_indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SaturationIndividualNodeExtensionResolveDataId {
        let con_set = calc_alg_context
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(*copy_indi_proc_sat_node, false);
        if con_set.is_some() {
            let con_tag = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_concept_tag();
            let mut contained_con_des = ConceptSaturationDescriptorId::NONE;
            let mut contained_imp_rea_des = ImplicationReapplyConceptSaturationDescriptorId::NONE;
            if calc_alg_context
                .process_context()
                .reapply_con_sat_label_set(con_set)
                .get_concept_saturation_descriptor_by_tag(
                    con_tag,
                    &mut contained_con_des,
                    &mut contained_imp_rea_des,
                )
                && contained_con_des.is_some()
                && calc_alg_context
                    .process_context()
                    .con_sat_desc(contained_con_des)
                    .get_negation()
                    == negation
            {
                return resolve_data;
            }
        }

        let hash = calc_alg_context
            .process_context_mut()
            .sat_extension_resolve_hash(resolve_data, true);
        let mut child_resolve_data = calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_hash(hash)
            .get_non_creating_resolved_individual_node_extension_data(concept, negation)
            .resolve_data;
        if child_resolve_data.is_none() {
            let next_resolve_indi_id = calc_alg_context
                .next_saturation_resolved_successor_extension_individual_node_id(true);
            let mut data = SaturationIndividualNodeExtensionResolveData::new();
            data.init_extension_resolve_data_for_id(next_resolve_indi_id);
            child_resolve_data = calc_alg_context
                .process_context_mut()
                .alloc_sat_indi_node_ext_resolve_data(data);
            calc_alg_context
                .process_context_mut()
                .sat_indi_node_ext_resolve_hash_mut(hash)
                .get_resolved_individual_node_extension_data(concept, negation)
                .resolve_data = child_resolve_data;
        }
        if calc_alg_context
            .process_context()
            .sat_indi_node_ext_resolve_data(child_resolve_data)
            .has_processing_individual_node()
        {
            *copy_indi_proc_sat_node = calc_alg_context
                .process_context()
                .sat_indi_node_ext_resolve_data(child_resolve_data)
                .get_processing_individual_node();
        }
        child_resolve_data
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getSeparatedSaturationConceptAssertionResolveNode`
    /// (cpp 5270–5298).
    ///
    /// Lazily builds (once, cached on the databox) the shared "separated" resolve
    /// node seeded with just the top concept. Almost fully portable.
    pub fn get_separated_saturation_concept_assertion_resolve_node(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let top_concept = calc_alg_context
            .processing_data_box()
            .ontology_top_concept();
        let mut resolve_node = calc_alg_context
            .processing_data_box()
            .separated_saturation_concept_assertion_resolve_node();
        if resolve_node.is_none() {
            resolve_node = calc_alg_context
                .process_context_mut()
                .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
            let next_resolve_indi_id = calc_alg_context
                .next_saturation_resolved_successor_extension_individual_node_id(true);

            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolve_node)
                .init_individual_saturation_process_node(next_resolve_indi_id, Id::NONE, Id::NONE);
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolve_node)
                .set_initialized(true);
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolve_node)
                .set_separated(true);
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolve_node)
                .set_required_backward_propagation(true);

            self.add_individual_to_completion_queue(&mut resolve_node, calc_alg_context);

            // resolveNodeProcessLiner =
            //   CObjectAllocator<CIndividualSaturationProcessNodeLinker>::allocateAndConstruct(memMan);
            // resolveNodeProcessLiner->initProcessNodeLinker(resolveNode, true);
            let resolve_node_process_liner = calc_alg_context
                .process_context_mut()
                .sat_node_individual_saturation_process_node_linker(resolve_node, true);
            calc_alg_context
                .process_context_mut()
                .indi_sat_process_node_linker_mut(resolve_node_process_liner)
                .set_processing_queued(true);
            calc_alg_context
                .processing_data_box_mut()
                .add_individual_saturation_process_node_linker(resolve_node_process_liner);
            let resolve_node_individual_id = calc_alg_context
                .process_context()
                .sat_node(resolve_node)
                .get_individual_id();
            calc_alg_context
                .processing_data_box_mut()
                .individual_saturation_process_node_vector(true)
                .expect("create=true yields CIndividualSaturationProcessNodeVector")
                .set_data(resolve_node_individual_id, resolve_node);

            // CReapplyConceptSaturationLabelSet* resolveConSet = resolveNode->getReapplyConceptSaturationLabelSet(true);
            let resolve_con_set = calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolve_node)
                .get_reapply_concept_saturation_label_set(true);
            self.add_concept_filtered_to_individual_label_set(
                top_concept,
                false,
                &mut resolve_node,
                resolve_con_set,
                false,
                calc_alg_context,
            );

            calc_alg_context
                .processing_data_box_mut()
                .set_separated_saturation_concept_assertion_resolve_node(resolve_node);
        }
        resolve_node
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getIndividualNodeForConcept`
    /// (cpp 5301–5316).
    ///
    /// KONCLUDE-PORT-NOTE[api]: walks the concept's process-side reference linking
    /// (`CConceptData` → `CConceptProcessData` → `CConceptReferenceLinking` →
    /// `CConceptSaturationReferenceLinkingData` → `CSaturationConceptReferenceLinking`)
    /// to the cached individual node for `(concept, negated)`. The concept process
    /// data + reference-linking chain is unported (the C++ `getConceptData()` returns
    /// the opaque `Cint64` process-data handle); the whole `dynamic_cast` ladder is
    /// deferred. Returns `SatNodeId::NONE` until it lands.
    pub fn get_individual_node_for_concept(
        &mut self,
        concept: ConceptId,
        negated: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        // The dynamic_cast ladder (CConceptData → CConceptProcessData →
        // CConceptReferenceLinking → CConceptSaturationReferenceLinkingData →
        // CSaturationConceptReferenceLinking → node) is the shared s07 resolver.
        Self::s07_concept_reference_node(concept, negated, calc_alg_context)
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getSaturationIDForIndividualNode`
    /// (cpp 5319–5333).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the individual's saturation reference linking
    /// (`CIndividualProcessData` → `getSaturationReferenceLinkingData()` →
    /// `CIndividualSaturationReferenceLinkingData::getSaturationID()`) is unported;
    /// the C++ `getIndividualData()` returns the opaque `Cint64` process-data handle.
    /// Returns `-1` (the C++ "no linking" sentinel) until it lands.
    pub fn get_saturation_id_for_individual_node(
        &mut self,
        individual: IndividualId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // CIndividualProcessData* indiProcData = (CIndividualProcessData*)individual->getIndividualData();
        let indi_proc_data = calc_alg_context
            .ontology_arenas()
            .individual(individual)
            .get_individual_data();
        let mut has_ref_linking = false;
        if indi_proc_data != INVALID {
            // W4-DEFER[api]: refLinking = indiProcData->getSaturationReferenceLinkingData();
            //   if (refLinking) { satCalcRefLinkData = (CIndividualSaturationReferenceLinkingData*)refLinking;
            //     if (satCalcRefLinkData) { hasRefLinking = true; return satCalcRefLinkData->getSaturationID(); } }
            //   — CIndividualProcessData / CIndividualSaturationReferenceLinkingData unported.
            let _ = &mut has_ref_linking;
        }
        -1
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getIndividualNodeForIndividual`
    /// (cpp 5336–5365).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the nominal short-circuit (the passed node's
    /// `getNominalIndividual() == individual`) is PORTABLE and emitted; the fallback
    /// reference-linking lookup (same `CIndividualSaturationReferenceLinkingData`
    /// chain as `getSaturationIDForIndividualNode`, guarded by the saturation id
    /// match + a nominal re-check on the cached node) is unported and deferred.
    pub fn get_individual_node_for_individual(
        &mut self,
        indi_proc_sat_node: SatNodeId,
        individual: IndividualId,
        saturation_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let mut node = SatNodeId::NONE;
        let nominal_individual = calc_alg_context
            .process_context()
            .sat_node(indi_proc_sat_node)
            .get_nominal_individual();
        if nominal_individual == individual {
            node = indi_proc_sat_node;
        } else {
            // CIndividualProcessData* indiProcData = (CIndividualProcessData*)individual->getIndividualData();
            let indi_proc_data = calc_alg_context
                .ontology_arenas()
                .individual(individual)
                .get_individual_data();
            let mut has_ref_linking = false;
            if indi_proc_data != INVALID {
                // W4-DEFER[api]: refLinking = indiProcData->getSaturationReferenceLinkingData();
                //   if (refLinking) { satCalcRefLinkData = (CIndividualSaturationReferenceLinkingData*)refLinking;
                //     if (satCalcRefLinkData) { hasRefLinking = true;
                //       if (satCalcRefLinkData->getSaturationID() == saturationID) {
                //         node = (CIndividualSaturationProcessNode*)satCalcRefLinkData->getIndividualProcessNodeForConcept();
                //         if (node->getNominalIndividual() != individual) node = nullptr;
                //       }
                //     }
                //   }
                //   — CIndividualProcessData / CIndividualSaturationReferenceLinkingData unported;
                //   the saturation-id-matched cached node lookup resolves when they land.
                let _ = (&mut has_ref_linking, saturation_id);
            }
        }
        // C++ trailing commented-out fallback (the indiNodeVec lookup) is intentionally
        // disabled in the source; preserved as a comment for fidelity:
        //   //if (!hasRefLinking) { node = ctx->getProcessingDataBox()
        //   //    ->getIndividualSaturationProcessNodeVector(false)->getData(individual->getIndividualID()); }
        node
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::concept::Concept;
    use super::super::super::model::op::CCATOM;
    use super::super::satellites::{
        ConceptSaturationDescriptor, SaturationSuccessorConceptExtensionMap,
    };
    use super::*;

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
    fn s10_collect_resolve_extendable_concept_map_diffs_extension_label_set() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let base_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let extension_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_mut(base_node)
            .init_individual_saturation_process_node(701, Id::NONE, Id::NONE);
        ctx.process_context_mut()
            .sat_node_mut(extension_node)
            .init_individual_saturation_process_node(703, Id::NONE, Id::NONE);
        let same = atom(&mut ctx, 9101);
        let opposite = atom(&mut ctx, 9103);
        let missing = atom(&mut ctx, 9105);

        insert_label(&mut ctx, base_node, same, false);
        insert_label(&mut ctx, base_node, opposite, false);
        insert_label(&mut ctx, extension_node, same, false);
        insert_label(&mut ctx, extension_node, opposite, true);
        insert_label(&mut ctx, extension_node, missing, false);

        let mut algo = super::super::algorithm::SaturationTaskHandleAlgorithm::new();
        let mut con_ext_map = SaturationConceptExtensionMapId::NONE;
        assert!(algo.collect_resolve_individual_extendable_concept_map(
            base_node,
            extension_node,
            &mut con_ext_map,
            &mut ctx,
        ));
        assert!(con_ext_map.is_some());

        let map = ctx.process_context().sat_concept_extension_map(con_ext_map);
        assert_eq!(map.iter().count(), 2);
        assert_eq!(
            map.concept_extension_map.get(&9103).copied(),
            Some(ConceptNegationPair::new(opposite, true))
        );
        assert_eq!(
            map.concept_extension_map.get(&9105).copied(),
            Some(ConceptNegationPair::new(missing, false))
        );
        assert!(map.concept_extension_map.get(&9101).is_none());
    }

    #[test]
    fn s10_concept_leaf_resolve_allocates_caches_and_short_circuits_existing_label() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let base_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let concept = atom(&mut ctx, 9201);
        let other = atom(&mut ctx, 9203);
        let resolve_data = {
            let mut data = SaturationIndividualNodeExtensionResolveData::new();
            data.init_extension_resolve_data_for_node(base_node, 700);
            ctx.process_context_mut()
                .alloc_sat_indi_node_ext_resolve_data(data)
        };

        let mut algo = super::super::algorithm::SaturationTaskHandleAlgorithm::new();
        let mut copy_node = base_node;
        let child = algo.get_resolved_individual_node_extension(
            resolve_data,
            concept,
            false,
            &mut copy_node,
            &mut ctx,
        );
        assert!(child.is_some());
        assert_ne!(child, resolve_data);
        assert_eq!(copy_node, base_node);
        assert_eq!(
            ctx.process_context()
                .sat_indi_node_ext_resolve_data(child)
                .get_processing_individual_node_id(),
            0
        );

        let child_again = algo.get_resolved_individual_node_extension(
            resolve_data,
            concept,
            false,
            &mut copy_node,
            &mut ctx,
        );
        assert_eq!(child_again, child);

        insert_label(&mut ctx, base_node, other, true);
        let short_circuit = algo.get_resolved_individual_node_extension(
            resolve_data,
            other,
            true,
            &mut copy_node,
            &mut ctx,
        );
        assert_eq!(short_circuit, resolve_data);
    }

    #[test]
    fn s10_extension_node_resolve_uses_individual_hash_cache() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let base_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let extension_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let base_concept = atom(&mut ctx, 9301);
        let extension_concept = atom(&mut ctx, 9303);
        insert_label(&mut ctx, base_node, base_concept, false);
        insert_label(&mut ctx, extension_node, base_concept, false);
        insert_label(&mut ctx, extension_node, extension_concept, false);
        let resolve_data = {
            let mut data = SaturationIndividualNodeExtensionResolveData::new();
            data.init_extension_resolve_data_for_node(base_node, 701);
            ctx.process_context_mut()
                .alloc_sat_indi_node_ext_resolve_data(data)
        };

        let mut algo = super::super::algorithm::SaturationTaskHandleAlgorithm::new();
        let mut copy_node = base_node;
        let mut created = false;
        let child = algo.get_resolved_individual_node_extension_for_node_created(
            resolve_data,
            extension_node,
            &mut copy_node,
            Some(&mut created),
            &mut ctx,
        );
        assert!(created);
        assert!(child.is_some());
        assert_ne!(child, resolve_data);
        let resolved_node = ctx
            .process_context()
            .sat_indi_node_ext_resolve_data(child)
            .get_processing_individual_node();
        assert!(resolved_node.is_some());
        assert_eq!(copy_node, resolved_node);

        let resolve_data_count = ctx.process_context().sat_indi_node_ext_resolve_data_count();
        let sat_node_count = ctx.process_context().sat_node_count();
        copy_node = base_node;
        let mut created_again = false;
        let child_again = algo.get_resolved_individual_node_extension_for_node_created(
            resolve_data,
            extension_node,
            &mut copy_node,
            Some(&mut created_again),
            &mut ctx,
        );
        assert!(!created_again);
        assert_eq!(child_again, child);
        assert_eq!(copy_node, resolved_node);
        assert_eq!(
            ctx.process_context().sat_indi_node_ext_resolve_data_count(),
            resolve_data_count
        );
        assert_eq!(ctx.process_context().sat_node_count(), sat_node_count);

        let hash = ctx
            .process_context_mut()
            .sat_extension_resolve_hash(resolve_data, false);
        assert_eq!(
            ctx.process_context()
                .sat_indi_node_ext_resolve_hash(hash)
                .get_non_creating_resolved_individual_node_extension_data_for_node(extension_node)
                .resolve_data,
            child
        );
    }

    #[test]
    fn s10_successor_concept_extension_map_tracks_polarity_by_concept_tag() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let concept = atom(&mut ctx, 9401);
        let other = atom(&mut ctx, 9403);
        let mut map = SaturationSuccessorConceptExtensionMap::new();

        assert!(map.add_extension_concept(concept, false, 9401));
        assert!(!map.add_extension_concept(concept, false, 9401));
        assert!(map.add_extension_concept(concept, true, 9401));
        assert!(map.add_extension_concept(other, true, 9403));

        let first = map.concept_extension_map.get(&9401).unwrap();
        assert_eq!(first.concept, concept);
        assert!(first.positive);
        assert!(first.negative);
        let second = map.concept_extension_map.get(&9403).unwrap();
        assert_eq!(second.concept, other);
        assert!(!second.positive);
        assert!(second.negative);

        map.init_successor_concept_extension_map();
        assert!(map.is_empty());
    }

    #[test]
    fn s10_successor_extension_resolver_walks_positive_and_negative_entries() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let base_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_mut(base_node)
            .init_individual_saturation_process_node(9500, Id::NONE, Id::NONE);
        ctx.process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(base_node, true);
        let positive = atom(&mut ctx, 9501);
        let negative = atom(&mut ctx, 9503);

        let succ_map = {
            let mut map = SaturationSuccessorConceptExtensionMap::new();
            assert!(map.add_extension_concept(positive, false, 9501));
            assert!(map.add_extension_concept(negative, true, 9503));
            ctx.process_context_mut()
                .alloc_sat_successor_concept_extension_map(map)
        };

        let mut algo = super::super::algorithm::SaturationTaskHandleAlgorithm::new();
        let resolved_node =
            algo.get_resolved_individual_node_extension_successor(base_node, succ_map, &mut ctx);
        assert!(resolved_node.is_some());
        assert_ne!(resolved_node, base_node);

        let label_set = ctx
            .process_context()
            .sat_node(resolved_node)
            .reapply_con_sat_label_set;
        let label_set = ctx.process_context().reapply_con_sat_label_set(label_set);
        assert!(label_set.contains_concept_or_reaplly_queue(9501));
        assert!(label_set.contains_concept_or_reaplly_queue(9503));
    }

    #[test]
    fn s10_successor_extension_resolver_reuses_cache_for_equal_maps() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let base_node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_mut(base_node)
            .init_individual_saturation_process_node(9600, Id::NONE, Id::NONE);
        ctx.process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(base_node, true);

        let concepts: Vec<_> = (0..16)
            .map(|offset| atom(&mut ctx, 9601 + offset * 2))
            .collect();
        let first_map = {
            let mut map = SaturationSuccessorConceptExtensionMap::new();
            for (offset, &concept) in concepts.iter().enumerate() {
                assert!(map.add_extension_concept(concept, false, 9601 + offset as i64 * 2));
            }
            ctx.process_context_mut()
                .alloc_sat_successor_concept_extension_map(map)
        };
        let second_map = {
            let mut map = SaturationSuccessorConceptExtensionMap::new();
            for (offset, &concept) in concepts.iter().enumerate().rev() {
                assert!(map.add_extension_concept(concept, false, 9601 + offset as i64 * 2));
            }
            ctx.process_context_mut()
                .alloc_sat_successor_concept_extension_map(map)
        };

        let mut algo = super::super::algorithm::SaturationTaskHandleAlgorithm::new();
        let first =
            algo.get_resolved_individual_node_extension_successor(base_node, first_map, &mut ctx);
        let node_count = ctx.process_context().sat_node_count();
        let resolve_count = ctx.process_context().sat_indi_node_ext_resolve_data_count();
        let second =
            algo.get_resolved_individual_node_extension_successor(base_node, second_map, &mut ctx);

        assert_eq!(second, first);
        assert_eq!(ctx.process_context().sat_node_count(), node_count);
        assert_eq!(
            ctx.process_context().sat_indi_node_ext_resolve_data_count(),
            resolve_count
        );
    }
}
