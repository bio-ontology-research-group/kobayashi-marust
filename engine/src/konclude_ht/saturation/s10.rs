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
//! `CPROCESSINGHASH<cint64,CConceptNegationPair>` extension maps. NONE of these
//! saturation satellites is ported (they have no `process::stubs` marker), so —
//! matching `s06`'s handling of the sibling successor-extension satellites — each
//! is carried as an opaque `Cint64` (`INVALID` == `nullptr`), and every
//! `resolveData->...` / `resolveHash->...` / `extensionMap->...` dereference is
//! flagged `// W4-DEFER[api]` with the C++ transcribed verbatim above it. The
//! PORTABLE leaves ARE emitted as real code: node pool-allocation + init in
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
use super::super::process::stubs::IndividualSaturationProcessNodeLinkerId;
use super::super::process::SatNodeId;

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
            .sat_node_mut(resolved_indi_proc_sat_node)
            .take_concept_saturation_process_linker();
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
                .sat_node_mut(resolved_indi_proc_sat_node)
                .take_concept_saturation_process_linker();
            processed = true;
        }
        processed
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
        // W4-DEFER[api]: resolveData = indiProcSatNode->getSuccessorExtensionData(true)
        //   ->getBaseExtensionResolveData(true) — CSaturationIndividualNodeExtensionResolveData
        //   not ported (opaque Cint64).
        let mut resolve_data: Cint64 = INVALID;
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
        let top_concept = calc_alg_context.processing_data_box().ontology_top_concept();
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
                let op_code = calc_alg_context.ontology_arenas().concept(concept).get_operator_code();
                if op_code == CCNOMINAL {
                    let nominal_individual =
                        calc_alg_context.ontology_arenas().concept(concept).get_nominal_individual();
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
        let super_role_list: Vec<(RoleId, bool)> = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_indirect_super_role_list()
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

        // W4-DEFER[api]: if (!resolveData->hasProcessingIndividualNode()) — resolveData satellite.
        let has_processing_individual_node: bool = false;
        if !has_processing_individual_node {
            // create individual
            resolved_node =
                self.create_resolved_individual_node(resolve_data, &mut copy_indi_proc_sat_node, true, calc_alg_context);
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .set_abox_individual_representation_node(true);
            let separated = calc_alg_context.process_context().sat_node(indi_proc_sat_node).is_separated();
            calc_alg_context.process_context_mut().sat_node_mut(resolved_node).set_separated(separated);
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
                        self.add_concept_filtered_to_individual(top_concept, true, &mut resolved_node, calc_alg_context);
                    }
                } else {
                    let op_code =
                        calc_alg_context.ontology_arenas().concept(concept).get_operator_code();
                    if op_code == CCNOMINAL {
                        let nominal_individual =
                            calc_alg_context.ontology_arenas().concept(concept).get_nominal_individual();
                        if nominal_individual == nominal_indi {
                            if negated {
                                self.add_concept_filtered_to_individual(top_concept, true, &mut resolved_node, calc_alg_context);
                            }
                        } else if !negated {
                            self.add_concept_filtered_to_individual(concept, negated, &mut resolved_node, calc_alg_context);
                        }
                    } else {
                        self.add_concept_filtered_to_individual(concept, negated, &mut resolved_node, calc_alg_context);
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
                    self.add_concept_filtered_to_individual(range_concept, range_concept_negation, &mut resolved_node, calc_alg_context);
                }
            }

            self.preprocess_resolved_individual_node(resolved_node, calc_alg_context);
        }
        // W4-DEFER[api]: resolvedNode = resolveData->getProcessingIndividualNode();
        //   (resolveData satellite) — returns the freshly created node when the
        //   create-branch ran, else the cached processing node.
        resolved_node
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
        // W4-DEFER[api]: resolveData = indiProcSatNode->getSuccessorExtensionData(true)->getBaseExtensionResolveData(true)
        let mut resolve_data: Cint64 = INVALID;
        let mut copy_indi_proc_sat_node = indi_proc_sat_node;
        let con_ass_linker: Vec<(ConceptId, bool)> = calc_alg_context
            .ontology_arenas()
            .individual(nominal_indi)
            .get_assertion_concept_linker()
            .iter()
            .map(|a| (a.target, a.negated))
            .collect();
        let top_concept = calc_alg_context.processing_data_box().ontology_top_concept();
        let nominal_concept = calc_alg_context
            .ontology_arenas()
            .individual(nominal_indi)
            .get_individual_nominal_concept();

        // resolve individual
        for &(concept, negated) in &con_ass_linker {
            if concept == nominal_concept {
                if negated {
                    resolve_data = self.get_resolved_individual_node_extension(
                        resolve_data, top_concept, true, &mut copy_indi_proc_sat_node, calc_alg_context,
                    );
                }
            } else {
                let op_code = calc_alg_context.ontology_arenas().concept(concept).get_operator_code();
                if op_code == CCNOMINAL {
                    let nominal_individual =
                        calc_alg_context.ontology_arenas().concept(concept).get_nominal_individual();
                    if nominal_individual == nominal_indi {
                        if negated {
                            resolve_data = self.get_resolved_individual_node_extension(
                                resolve_data, top_concept, true, &mut copy_indi_proc_sat_node, calc_alg_context,
                            );
                        }
                    } else {
                        resolve_data = self.get_resolved_individual_node_extension(
                            resolve_data, concept, negated, &mut copy_indi_proc_sat_node, calc_alg_context,
                        );
                    }
                } else {
                    resolve_data = self.get_resolved_individual_node_extension(
                        resolve_data, concept, negated, &mut copy_indi_proc_sat_node, calc_alg_context,
                    );
                }
            }
        }

        resolve_data = self.get_resolved_neighbour_individual_node_extension(
            resolve_data, &mut copy_indi_proc_sat_node, calc_alg_context,
        );

        // W4-DEFER[api]: if (!resolveData->hasProcessingIndividualNode())
        let has_processing_individual_node: bool = false;
        if !has_processing_individual_node {
            // create individual
            resolved_node =
                self.create_resolved_individual_node(resolve_data, &mut copy_indi_proc_sat_node, true, calc_alg_context);
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .set_abox_individual_representation_node(true);
            let separated = calc_alg_context.process_context().sat_node(indi_proc_sat_node).is_separated();
            calc_alg_context.process_context_mut().sat_node_mut(resolved_node).set_separated(separated);
            let _con_set = calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .get_reapply_concept_saturation_label_set(true);

            // add all concepts to individual
            for &(concept, negated) in &con_ass_linker {
                if concept == nominal_concept {
                    if negated {
                        self.add_concept_filtered_to_individual(top_concept, true, &mut resolved_node, calc_alg_context);
                    }
                } else {
                    let op_code =
                        calc_alg_context.ontology_arenas().concept(concept).get_operator_code();
                    if op_code == CCNOMINAL {
                        let nominal_individual =
                            calc_alg_context.ontology_arenas().concept(concept).get_nominal_individual();
                        if nominal_individual == nominal_indi {
                            if negated {
                                self.add_concept_filtered_to_individual(top_concept, true, &mut resolved_node, calc_alg_context);
                            }
                        } else {
                            self.add_concept_filtered_to_individual(concept, negated, &mut resolved_node, calc_alg_context);
                        }
                    } else {
                        self.add_concept_filtered_to_individual(concept, negated, &mut resolved_node, calc_alg_context);
                    }
                }
            }

            self.preprocess_resolved_individual_node(resolved_node, calc_alg_context);
        }
        // W4-DEFER[api]: resolvedNode = resolveData->getProcessingIndividualNode();
        resolved_node
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
        // W4-DEFER[api]: resolveData = indiProcSatNode->getSuccessorExtensionData(true)->getBaseExtensionResolveData(true)
        let mut resolve_data: Cint64 = INVALID;
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
                    resolve_data, concept, negated, &mut copy_indi_proc_sat_node, calc_alg_context,
                );
            }
        }

        // W4-DEFER[api]: if (!resolveData->hasProcessingIndividualNode())
        let has_processing_individual_node: bool = false;
        if !has_processing_individual_node {
            // create individual
            resolved_node =
                self.create_resolved_individual_node(resolve_data, &mut copy_indi_proc_sat_node, true, calc_alg_context);
            let separated = calc_alg_context.process_context().sat_node(indi_proc_sat_node).is_separated();
            calc_alg_context.process_context_mut().sat_node_mut(resolved_node).set_separated(separated);
            let _con_set = calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .get_reapply_concept_saturation_label_set(true);

            // add all concepts to individual
            for &(concept, negated) in &con_ass_linker {
                if negated || concept != nominal_concept {
                    self.add_concept_filtered_to_individual(concept, negated, &mut resolved_node, calc_alg_context);
                }
            }

            self.preprocess_resolved_individual_node(resolved_node, calc_alg_context);
        }
        // W4-DEFER[api]: resolvedNode = resolveData->getProcessingIndividualNode();
        resolved_node
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeExtensionSuccessor`
    /// (cpp 2297–2338).
    ///
    /// KONCLUDE-PORT-NOTE[api]: `succConExtMap`
    /// (`CSaturationSuccessorConceptExtensionMap*`) and its
    /// `getSuccessorConceptExtensionMap()` value-hash are unported satellites
    /// (opaque `Cint64`); the two iterations over the map (resolve pass + add pass)
    /// resolve when that satellite lands.
    pub fn get_resolved_individual_node_extension_successor(
        &mut self,
        indi_proc_sat_node: SatNodeId,
        succ_con_ext_map: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let mut resolved_node = SatNodeId::NONE;
        // W4-DEFER[api]: resolveData = indiProcSatNode->getSuccessorExtensionData(true)->getBaseExtensionResolveData(true)
        let mut resolve_data: Cint64 = INVALID;
        // W4-DEFER[api]: succConExtDataMap = succConExtMap->getSuccessorConceptExtensionMap()
        //   — CSaturationSuccessorConceptExtensionMap / CSaturationSuccessorConceptExtensionMapData unported.
        let mut copy_indi_proc_sat_node = indi_proc_sat_node;

        // resolve individual
        // W4-DEFER[api]: for (it : succConExtDataMap) { conExtDat = it.value();
        //   concept = conExtDat.mConcept; addPositive = conExtDat.mPositive; addNegative = conExtDat.mNegative;
        //   if (addPositive) resolveData = getResolvedIndividualNodeExtension(resolveData, concept, false, copyIndiProcSatNode, ...);
        //   if (addNegative) resolveData = getResolvedIndividualNodeExtension(resolveData, concept, true,  copyIndiProcSatNode, ...); }
        //   — the resolve pass over the (unported) successor-concept-extension map; each leaf is the
        //   ported `self.get_resolved_individual_node_extension(...)`.

        // W4-DEFER[api]: if (!resolveData->hasProcessingIndividualNode())
        let has_processing_individual_node: bool = false;
        if !has_processing_individual_node {
            // create individual
            resolved_node =
                self.create_resolved_individual_node(resolve_data, &mut copy_indi_proc_sat_node, true, calc_alg_context);
            let _con_set = calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolved_node)
                .get_reapply_concept_saturation_label_set(true);

            // add all concepts to individual
            // W4-DEFER[api]: for (it : succConExtDataMap) {
            //   if (addPositive) addConceptFilteredToIndividual(concept, false, resolvedNode, ...);
            //   if (addNegative) addConceptFilteredToIndividual(concept, true,  resolvedNode, ...); }
            //   — the add pass; each leaf is the ported `self.add_concept_filtered_to_individual(...)`.

            self.preprocess_resolved_individual_node(resolved_node, calc_alg_context);
        }
        // W4-DEFER[api]: resolvedNode = resolveData->getProcessingIndividualNode();
        resolved_node
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
        resolve_data: Cint64,
        copy_indi_proc_sat_node: &mut SatNodeId,
        queue_processing: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let mut resolved_node = calc_alg_context
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
        // W4-DEFER[api]: resolveData->getProcessingIndividualNodeID() — resolveData satellite;
        //   the resolved-node individual id is taken from the resolve record. Carried as the
        //   deferred init id below (INVALID until the satellite lands).
        let processing_individual_node_id: Cint64 = INVALID;
        calc_alg_context
            .process_context_mut()
            .sat_node_mut(resolved_node)
            .init_individual_saturation_process_node(processing_individual_node_id, Id::NONE, Id::NONE);
        self.initialize_individual_node_by_coping(resolved_node, *copy_indi_proc_sat_node, false, calc_alg_context);

        // W4-DEFER[api]: resolveData->setProcessingIndividualNode(resolvedNode); — resolveData satellite.
        // W4-DEFER[api]: resolvedNode->getSuccessorExtensionData(true)->setExtensionResolveData(resolveData);
        //   — CSaturationIndividualNodeSuccessorExtensionData::setExtensionResolveData not ported.
        calc_alg_context.process_context_mut().sat_node_mut(resolved_node).set_initialized(true);
        calc_alg_context.process_context_mut().sat_node_mut(resolved_node).set_required_backward_propagation(true);
        self.add_individual_to_completion_queue(&mut resolved_node, calc_alg_context);

        // CIndividualSaturationProcessNodeLinker* resolveNodeProcessLiner =
        //   CObjectAllocator<CIndividualSaturationProcessNodeLinker>::allocateAndConstruct(memMan);
        // resolveNodeProcessLiner->initProcessNodeLinker(resolvedNode, queueProcessing);
        // W4-DEFER[api]: CIndividualSaturationProcessNodeLinker (process::stubs marker, no arena);
        //   the linker alloc + initProcessNodeLinker resolve when that linker chain is ported.
        let resolve_node_process_liner: IndividualSaturationProcessNodeLinkerId = Id::NONE;
        calc_alg_context
            .process_context_mut()
            .sat_node_mut(resolved_node)
            .set_individual_saturation_process_node_linker(resolve_node_process_liner);
        if queue_processing {
            // KONCLUDE-PORT-NOTE[api]: the C++ adds the linker; the ported databox chain tracks
            //   by node id, so the resolved node is added.
            calc_alg_context
                .processing_data_box_mut()
                .add_individual_saturation_process_node_linker(resolved_node);
        }
        // indiVec = ctx->getUsedProcessingDataBox()->getIndividualSaturationProcessNodeVector(true);
        let _indi_vec = calc_alg_context
            .processing_data_box_mut()
            .individual_saturation_process_node_vector(true);
        // W4-DEFER[api]: indiVec->setData(resolvedNode->getIndividualID(), resolvedNode);
        //   — CIndividualSaturationProcessNodeVector (process::stubs marker) has no setData yet.
        resolved_node
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::collectResolveIndividualExtendableConceptMap`
    /// (cpp 2371–2398).
    ///
    /// KONCLUDE-PORT-NOTE[api]: both label sets (`CReapplyConceptSaturationLabelSet`)
    /// and the descriptor chain (`CConceptSaturationDescriptor`) plus the extension
    /// map (`CPROCESSINGHASH<cint64,CConceptNegationPair>`) are unported satellites
    /// (opaque `Cint64`); the whole "for each base-not-containing descriptor, insert
    /// into the extension map" body is transcribed and deferred. `conExtMap` is an
    /// in/out opaque-pointer reference (`&mut Cint64`).
    pub fn collect_resolve_individual_extendable_concept_map(
        &mut self,
        base_indi_node: SatNodeId,
        extension_indi_node: SatNodeId,
        con_ext_map: &mut Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // CReapplyConceptSaturationLabelSet* extConSet = extensionIndiNode->getReapplyConceptSaturationLabelSet(false);
        let _ext_con_set = calc_alg_context
            .process_context_mut()
            .sat_node_mut(extension_indi_node)
            .get_reapply_concept_saturation_label_set(false);
        let mut extension_required = false;
        // W4-DEFER[api]: for (conIt = extConSet->getConceptSaturationDescriptionLinker(); conIt; conIt = conIt->getNextConceptDesciptor()) {
        //   containedConDes / containedImpReaDes = nullptr; insertionRequired = false;
        //   baseConSet = baseIndiNode->getReapplyConceptSaturationLabelSet(false);
        //   if (baseConSet->getConceptSaturationDescriptor(conIt->getConcept(), containedConDes, containedImpReaDes)) {
        //     if (!containedConDes) insertionRequired = true;
        //     else if (containedConDes->isNegated() != conIt->isNegated()) insertionRequired = true;
        //   } else insertionRequired = true;
        //   if (insertionRequired) {
        //     extensionRequired = true;
        //     if (!conExtMap) conExtMap = new CPROCESSINGHASH<cint64,CConceptNegationPair>(...);  // [memory-pool] temp-arena alloc
        //     conExtMap->insert(conIt->getConceptTag(), CConceptNegationPair(conIt->getConcept(), conIt->isNegated()));
        //   }
        // }
        //   — CReapplyConceptSaturationLabelSet (descriptor-linker iteration + getConceptSaturationDescriptor)
        //   and the CPROCESSINGHASH extension map are unported; resolves when they land. No logic dropped.
        let _ = (base_indi_node, con_ext_map);
        extension_required
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeExtension`
    /// (cpp 2401–2403; the `CPROCESSINGHASH` overload, forwarding wrapper).
    ///
    /// KONCLUDE-PORT-NOTE[overload]: C++ overload distinguished by the
    /// `CPROCESSINGHASH<cint64,CConceptNegationPair>* conExtensionMap` arg (opaque
    /// `Cint64`). Forwards to `..._for_con_map_created` with `newNodeExpansionCreated == nullptr`.
    pub fn get_resolved_individual_node_extension_for_con_map(
        &mut self,
        resolve_data: Cint64,
        con_extension_map: Cint64,
        copy_indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
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
    /// KONCLUDE-PORT-NOTE[api]: `conExtensionMap`
    /// (`CPROCESSINGHASH<cint64,CConceptNegationPair>*`) is an unported temp-hash
    /// (opaque `Cint64`); when non-null, iterates it twice (resolve pass, then —
    /// if no processing node yet — create + add pass). `bool* newNodeExpansionCreated`
    /// → `Option<&mut bool>`.
    pub fn get_resolved_individual_node_extension_for_con_map_created(
        &mut self,
        mut resolve_data: Cint64,
        con_extension_map: Cint64,
        copy_indi_proc_sat_node: &mut SatNodeId,
        new_node_expansion_created: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        if con_extension_map != INVALID {
            // W4-DEFER[api]: for (it : conExtensionMap) { conExtDat = it.value();
            //   concept = conExtDat.first; negation = conExtDat.second;
            //   resolveData = getResolvedIndividualNodeExtension(resolveData, concept, negation, copyIndiProcSatNode, ...); }
            //   — resolve pass over the (unported) CPROCESSINGHASH; each leaf is the ported
            //   `self.get_resolved_individual_node_extension(...)`.

            // W4-DEFER[api]: if (!resolveData->getProcessingIndividualNode()) — resolveData satellite.
            let has_processing_individual_node: bool = false;
            if !has_processing_individual_node {
                let resolved_node =
                    self.create_resolved_individual_node(resolve_data, copy_indi_proc_sat_node, true, calc_alg_context);
                // W4-DEFER[api]: resolveData->setProcessingIndividualNode(resolvedNode);

                // W4-DEFER[api]: for (it : conExtensionMap) {
                //   addConceptFilteredToIndividual(it.value().first, it.value().second, resolvedNode, ...); }
                //   — add pass; each leaf is the ported `self.add_concept_filtered_to_individual(...)`.
                self.preprocess_resolved_individual_node(resolved_node, calc_alg_context);

                if let Some(flag) = new_node_expansion_created {
                    *flag = true;
                }
            }

            // W4-DEFER[api]: copyIndiProcSatNode = resolveData->getProcessingIndividualNode();
            //   — rebinds the copy node to the resolve record's processing node.
        }
        resolve_data
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::getResolvedIndividualNodeExtension`
    /// (cpp 2443–2445; the extension-`CIndividualSaturationProcessNode*` overload, forwarding wrapper).
    pub fn get_resolved_individual_node_extension_for_node(
        &mut self,
        resolve_data: Cint64,
        extension_node: SatNodeId,
        copy_indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
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
    /// `resolveData`'s `CSaturationIndividualNodeExtensionResolveHash` (opaque); on a
    /// miss, builds the concept-extension map by diffing the extension node's label
    /// against the copy node's label, then delegates to the `..._for_con_map`
    /// overload. The resolve-hash + the label-set descriptor diff are unported.
    pub fn get_resolved_individual_node_extension_for_node_created(
        &mut self,
        mut resolve_data: Cint64,
        extension_node: SatNodeId,
        copy_indi_proc_sat_node: &mut SatNodeId,
        new_node_expansion_created: Option<&mut bool>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // W4-DEFER[api]: resolveHashData = resolveData->getIndividualNodeExtensionResolveHash(true)
        //   ->getResolvedIndividualNodeExtensionData(extensionNode);
        //   — CSaturationIndividualNodeExtensionResolveHash / ...ResolveHashData unported (opaque).
        let resolve_hash_data_present: bool = false; // resolveHashData.mResolveData != nullptr
        if !resolve_hash_data_present {
            // CReapplyConceptSaturationLabelSet* extConSet = extensionNode->getReapplyConceptSaturationLabelSet(false);
            let _ext_con_set = calc_alg_context
                .process_context_mut()
                .sat_node_mut(extension_node)
                .get_reapply_concept_saturation_label_set(false);

            // CPROCESSINGHASH<cint64,CConceptNegationPair>* conExtensionMap = nullptr;
            let mut con_extension_map: Cint64 = INVALID;

            // W4-DEFER[api]: for (conIt = extConSet->getConceptSaturationDescriptionLinker(); conIt; conIt = conIt->getNextConceptDesciptor()) {
            //   containedConDes / containedImpReaDes = nullptr; insertionRequired = false;
            //   baseConSet = copyIndiProcSatNode->getReapplyConceptSaturationLabelSet(false);
            //   if (baseConSet->getConceptSaturationDescriptor(conIt->getConcept(), containedConDes, containedImpReaDes)) {
            //     if (!containedConDes) insertionRequired = true;
            //     else if (containedConDes->isNegated() != conIt->isNegated()) insertionRequired = true;
            //   } else insertionRequired = true;
            //   if (insertionRequired) {
            //     if (!conExtensionMap) conExtensionMap = new CPROCESSINGHASH<...>(...);   // [memory-pool] temp-arena alloc
            //     conExtensionMap->insert(conIt->getConceptTag(), CConceptNegationPair(conIt->getConcept(), conIt->isNegated()));
            //   }
            // }
            //   — same descriptor diff as collectResolveIndividualExtendableConceptMap, here against the copy node;
            //   resolves with CReapplyConceptSaturationLabelSet + the CPROCESSINGHASH temp map.

            resolve_data = self.get_resolved_individual_node_extension_for_con_map_created(
                resolve_data,
                con_extension_map,
                copy_indi_proc_sat_node,
                new_node_expansion_created,
                calc_alg_context,
            );

            // W4-DEFER[api]: resolveHashData.mResolveData = resolveData;
        }
        // W4-DEFER[api]: return resolveHashData.mResolveData;  — cached resolve record.
        resolve_data
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
        resolve_data: Cint64,
        copy_indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // W4-DEFER[api]: resolveHashData = resolveData->getIndividualNodeExtensionResolveHash(true)
        //   ->getResolvedNeighbourIndividualNodeExtensionData();
        let resolve_hash_data_present: bool = false; // resolveHashData.mResolveData != nullptr
        if !resolve_hash_data_present {
            // W4-DEFER[api/memory-pool]: resolveHashData.mResolveData = new CSaturationIndividualNodeExtensionResolveData(...);
            // PORTABLE: nextResolveIndiID = ctx->getUsedProcessingDataBox()->getNextSaturationResolvedSuccessorExtensionIndividualNodeID();
            let _next_resolve_indi_id = calc_alg_context
                .processing_data_box_mut()
                .next_saturation_resolved_successor_extension_individual_node_id(true);
            // W4-DEFER[api]: resolveHashData.mResolveData->initExtensionResolveData(nextResolveIndiID);
        }
        // W4-DEFER[api]: if (resolveHashData.mResolveData->hasProcessingIndividualNode())
        //   copyIndiProcSatNode = resolveHashData.mResolveData->getProcessingIndividualNode();
        let _ = copy_indi_proc_sat_node;
        // W4-DEFER[api]: return resolveHashData.mResolveData;
        resolve_data
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
        resolve_data: Cint64,
        concept: ConceptId,
        negation: bool,
        copy_indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // CReapplyConceptSaturationLabelSet* conSet = copyIndiProcSatNode->getReapplyConceptSaturationLabelSet(false);
        let con_set = calc_alg_context
            .process_context_mut()
            .sat_node_mut(*copy_indi_proc_sat_node)
            .get_reapply_concept_saturation_label_set(false);
        // W4-DEFER[api]: if (conSet && conSet->containsConcept(concept, negation)) return resolveData;
        //   — CReapplyConceptSaturationLabelSet::containsConcept not ported; the early-return
        //   on an already-contained concept resolves when the label set lands.
        let con_set_contains_concept: bool = false;
        if con_set.is_some() && con_set_contains_concept {
            return resolve_data;
        }

        // W4-DEFER[api]: resolveHashData = resolveData->getIndividualNodeExtensionResolveHash(true)
        //   ->getResolvedIndividualNodeExtensionData(concept, negation);
        let resolve_hash_data_present: bool = false; // resolveHashData.mResolveData != nullptr
        if !resolve_hash_data_present {
            // W4-DEFER[api/memory-pool]: resolveHashData.mResolveData = new CSaturationIndividualNodeExtensionResolveData(...);
            // PORTABLE: nextResolveIndiID = ctx->getUsedProcessingDataBox()->getNextSaturationResolvedSuccessorExtensionIndividualNodeID();
            let _next_resolve_indi_id = calc_alg_context
                .processing_data_box_mut()
                .next_saturation_resolved_successor_extension_individual_node_id(true);
            // W4-DEFER[api]: resolveHashData.mResolveData->initExtensionResolveData(nextResolveIndiID);
        }
        // W4-DEFER[api]: if (resolveHashData.mResolveData->hasProcessingIndividualNode())
        //   copyIndiProcSatNode = resolveHashData.mResolveData->getProcessingIndividualNode();
        // W4-DEFER[api]: return resolveHashData.mResolveData;
        let _ = (concept, negation);
        resolve_data
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
        let top_concept = calc_alg_context.processing_data_box().ontology_top_concept();
        let mut resolve_node = calc_alg_context
            .processing_data_box()
            .separated_saturation_concept_assertion_resolve_node();
        if resolve_node.is_none() {
            resolve_node = calc_alg_context
                .process_context_mut()
                .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
            let next_resolve_indi_id = calc_alg_context
                .processing_data_box_mut()
                .next_saturation_resolved_successor_extension_individual_node_id(true);

            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolve_node)
                .init_individual_saturation_process_node(next_resolve_indi_id, Id::NONE, Id::NONE);
            calc_alg_context.process_context_mut().sat_node_mut(resolve_node).set_initialized(true);
            calc_alg_context.process_context_mut().sat_node_mut(resolve_node).set_separated(true);
            calc_alg_context.process_context_mut().sat_node_mut(resolve_node).set_required_backward_propagation(true);

            self.add_individual_to_completion_queue(&mut resolve_node, calc_alg_context);

            // W4-DEFER[api]: resolveNodeProcessLiner = CObjectAllocator<CIndividualSaturationProcessNodeLinker>::...(memMan);
            //   resolveNodeProcessLiner->initProcessNodeLinker(resolveNode, true);
            //   — CIndividualSaturationProcessNodeLinker (process::stubs marker, no arena).
            let resolve_node_process_liner: IndividualSaturationProcessNodeLinkerId = Id::NONE;
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(resolve_node)
                .set_individual_saturation_process_node_linker(resolve_node_process_liner);
            calc_alg_context
                .processing_data_box_mut()
                .add_individual_saturation_process_node_linker(resolve_node);
            let _indi_vec = calc_alg_context
                .processing_data_box_mut()
                .individual_saturation_process_node_vector(true);
            // W4-DEFER[api]: indiVec->setData(resolveNode->getIndividualID(), resolveNode);

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
        let node = SatNodeId::NONE;
        // CConceptData* conceptData = concept->getConceptData();
        let concept_data = calc_alg_context.ontology_arenas().concept(concept).get_concept_data();
        if concept_data != INVALID {
            // W4-DEFER[api]: conProcData = (CConceptProcessData*)conceptData;
            //   conRefLinking = conProcData->getConceptReferenceLinking();
            //   if (conRefLinking) {
            //     confSatRefLinkingData = (CConceptSaturationReferenceLinkingData*)conRefLinking;
            //     satCalcRefLinkData = confSatRefLinkingData->getConceptSaturationReferenceLinkingData(negated);
            //     if (satCalcRefLinkData) node = (CIndividualSaturationProcessNode*)satCalcRefLinkData->getIndividualProcessNodeForConcept();
            //   }
            //   — CConceptProcessData / CConceptReferenceLinking / CConceptSaturationReferenceLinkingData /
            //   CSaturationConceptReferenceLinking unported; the cached-node lookup resolves when they land.
            let _ = negated;
        }
        node
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
        let indi_proc_data = calc_alg_context.ontology_arenas().individual(individual).get_individual_data();
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
            let indi_proc_data = calc_alg_context.ontology_arenas().individual(individual).get_individual_data();
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
