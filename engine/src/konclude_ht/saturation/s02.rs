//! `saturation::s02` — port unit #2 of 12 of the approximate-saturation
//! task-handle algorithm (Node-initialization family, group C of
//! `manifest/03-saturation-calc.md`).
//!
//! Ports the group-C methods of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`:
//!   - `individualNodeInitializing`              (.cpp 796–835)
//!   - `initializeIndividualNodeByCoping`        (.cpp 2022–2065)
//!   - `createRoleAssertionLink`                 (.cpp 5024–5076)
//!   - `initializeRoleAssertions`                (.cpp 5079–5140)
//!   - `initializeDataAssertions`                (.cpp 5145–5167)
//!   - `createSuccessorForDataLiteral`           (.cpp 5174–5265)
//!   - `countConceptsOfReferredNodes`            (.cpp 5369–5400)
//!   - `isProcessingCritical`                    (.cpp 5403–5420)
//!   - `resolveSpecialInitializationIndividualNode` (.cpp 5424–5460)
//!   - `initializeInitializationConcepts`        (.cpp 5464–5706)
//!   - `individualNodeConclusion`                (.cpp 5709–5714)
//!   - `getCorrectedNode`                        (.cpp 6461–6470)
//!   - `createSuccessorForConcept`               (.cpp 6931–7100)
//!
//! ## Context convention
//!
//! The saturation algorithm's `.h` declares every method with the SHARED
//! `CCalculationAlgorithmContextBase* calcAlgContext` (NOT a distinct saturation
//! context), so per `PORT.md` the port threads
//! `calc_alg_context: &mut super::super::completion::context::CalculationAlgorithmContextBase`.
//! Saturation nodes resolve through `ctx.process_context().sat_node(id)` /
//! `_mut(id)` / `alloc_sat_node(…)`; the databox through
//! `ctx.processing_data_box()` / `_mut()`; the static TBox/RBox concepts and roles
//! through `ctx.ontology_arenas()`. `CIndividualSaturationProcessNode*&` →
//! `&mut SatNodeId` (node-advancing ref); `CIndividualSaturationProcessNode*` (by
//! value) → `SatNodeId`. The C++ member back-handle `mCalcAlgContext` aliases the
//! passed `calcAlgContext` (same object); the port routes ALL access through the
//! `calc_alg_context` parameter.
//!
//! ## Deferral note (why the bodies are PORT-PENDING skeletons)
//!
//! KONCLUDE-PORT-NOTE[api]: group C is the saturation *node initialization* layer.
//! Almost every statement dereferences a saturation satellite class that is NOT
//! yet ported — `CReapplyConceptSaturationLabelSet`, `CConceptSaturationProcessLinker`,
//! `CSaturationConceptDataItem` / `CSaturationConceptReferenceLinking`,
//! `CBackwardSaturationPropagationLink`, `CIndividualSaturationProcessNodeExtensionData`,
//! `CLinkedNeighbourRoleAssertionSaturationHash`, `CLinkedDataValueAssertionSaturationData`,
//! `CSaturationIndividualNodeSuccessorExtensionData`, the saturation status-flag
//! masks, and the `CIndividualSaturationProcessNode` `init*`/`get…(create)` lazy
//! sub-struct getters (deferred to process unit SAT-1) — and it calls dozens of
//! sibling saturation methods that land in the OTHER s01..s12 units
//! (`addConceptFilteredToIndividual`, `updateDirect/IndirectAddingIndividualStatusFlags`,
//! `installBackwardPropagationLink`, `addNewLinkedExtensionProcessingRole`,
//! `getIndividualNodeForConcept`, `getSaturationIDForIndividualNode`,
//! `addIndividualToCompletionQueue`, `getResolvedIndividualNodeRepresentative*`, …).
//! Following the established `completion/u01..u06` precedent for the same class
//! family, each method below keeps its FAITHFUL signature and records the exact
//! C++ control flow as a structured PORT-PENDING transcription (no logic dropped),
//! with a minimal compiling body. They reconcile to live `ctx.…` / `self.…` calls
//! once SAT-1 and the sibling s-units land — see the per-method `W6-DEFER[api]`
//! markers and `manifest/03-saturation-calc.md` unit #2.

#![allow(dead_code, unused_variables, unused_mut)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::model::substrate::Cint64;
use super::super::model::Id;
use super::super::model::{ConceptId, NegLink, RoleId};
use super::super::process::node_resolution::IndividualProcessNodeVector;
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::stubs::ConceptSaturationProcessLinkerId;
use super::super::process::{NodeId, SatNodeId};
use super::algorithm::SaturationTaskHandleAlgorithm;

// ---------------------------------------------------------------------------
// Opaque saturation-satellite param aliases (W6-DEFER[api]).
// These C++ pointer parameter types belong to not-yet-ported saturation satellite
// classes; until those land they are opaque `Cint64` handles (`INVALID` ==
// `nullptr`), exactly like the saturation rule-function jump slots. When the real
// class is ported these aliases relocate to an `Id<T>` into its arena.
// ---------------------------------------------------------------------------

/// `CSaturationConceptDataItem*` — the per-node initialization-concept item.
type SaturationConceptDataItemHandle = Cint64;
/// `CConceptSaturationProcessLinker*` — a queued concept-application linker.
type ConceptSaturationProcessLinkerHandle = Cint64;
/// `CDataLiteral*` — a concrete data literal (opaque, shared read-only).
type DataLiteralHandle = Cint64;

impl SaturationTaskHandleAlgorithm {
    /// The saturation view of `role->getIndirectSuperRoleList()`.
    ///
    /// KONCLUDE-PORT-NOTE[identity]: Konclude's indirect super-role list STARTS
    /// with the role itself (`CSubroleTransformationPreProcess` cpp 221–224:
    /// `superRoleLinker->init(role,false); role->setIndirectSuperRoleLinker(...)`),
    /// but the bridge builds STRICT lists (its DFS skips `s == sub`) and the
    /// validated completion consumers depend on that shape. The saturation rules
    /// (successor creation, init-role ranges, the propagation-into-creation
    /// preprocess) semantically need the reflexive entry — restore it LOCALLY
    /// here instead of mutating the shared arenas.
    pub(in crate::konclude_ht) fn saturation_indirect_super_roles(
        role: RoleId,
        calc_alg_context: &CalculationAlgorithmContextBase,
    ) -> Vec<NegLink<RoleId>> {
        let list = calc_alg_context
            .ontology_arenas()
            .role(role)
            .get_indirect_super_role_list();
        let mut out = Vec::with_capacity(list.len() + 1);
        out.push(NegLink {
            target: role,
            negated: false,
        });
        for link in list {
            if !(link.target == role && !link.negated) {
                out.push(*link);
            }
        }
        out
    }

    /// Port of `CCalculationTableauApproximationSaturationTaskHandleAlgorithm::individualNodeInitializing`
    /// (.cpp 796–835).
    ///
    /// Initializes a fresh saturation node: lazily loads nominal triple assertions
    /// (via the ontology triples accessor + `CIndexedIndividualAssertionConvertionVisitor`),
    /// seeds the initialization concepts, then the role + data assertions, marks the
    /// node initialized, and — when the node is a nominal AND the task carries a
    /// saturation-individuals analysation observer — registers it on the databox's
    /// saturation-analysation node linker.
    ///
    /// PORT-PENDING (faithful C++ control flow; each `W6-DEFER[api]` resolves once
    /// the named subsystem lands):
    /// ```text
    /// if (!indiProcSatNode->isInitialized()) {                              // sat_node SAT-1
    ///   if (indiProcSatNode->hasNominalIndividualTriplesAssertions()        // sat_node SAT-1
    ///       && !indiProcSatNode->areNominalIndividualTriplesAssertionsLoaded()) {
    ///     ontology = ctx.processing_data_box().getOntology();               // databox
    ///     ontologyTriplesData = ontology->getOntologyTriplesData();         // ontology (unported)
    ///     if (ontologyTriplesData) {
    ///       triplesAssertionAccessor = ontologyTriplesData->getTripleAssertionAccessor();
    ///       if (triplesAssertionAccessor) {
    ///         // CIndexedIndividualAssertionConvertionVisitor over indiID (W6-DEFER[api])
    ///         //   seed = indiProcSatNode->getNominalIndividual() ? that : indiID
    ///         //   visitIndividualAssertions(indiID, &visitor)
    ///         indiProcSatNode->setNominalIndividual(visitor.getRetrievalIndividual());
    ///       }
    ///     }
    ///     indiProcSatNode->setNominalIndividualTriplesAssertionsLoaded(true);
    ///   }
    ///   self.initialize_initialization_concepts(indiProcSatNode, ctx);
    ///   self.initialize_role_assertions(indiProcSatNode, ctx);
    ///   self.initialize_data_assertions(indiProcSatNode, ctx);
    ///   indiProcSatNode->setInitialized(true);                              // sat_node SAT-1
    ///   if (indiProcSatNode->getNominalIndividual()
    ///       && ctx.getSatisfiableCalculationTask()->getSaturationIndividualsAnalysationObserver()) {
    ///     // alloc CIndividualSaturationProcessNodeLinker, initProcessNodeLinker(node,true)
    ///     ctx.processing_data_box_mut().addIndividualSaturationAnalysationNodeLinker(linker);
    ///   }
    /// }
    /// return true;
    /// ```
    pub fn individual_node_initializing(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if !calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .is_initialized()
        {
            // Nominal triples-assertion loading (cpp 799–819):
            // `hasNominalIndividualTriplesAssertions && !areLoaded` → visit the
            // ontology triples accessor. KONCLUDE-PORT-NOTE[api]: the ontology
            // triples subsystem is unported and the port's node construction
            // (`CSatisfiableCalculationTaskFromCalculationJobGenerator` analogue in
            // bridge.rs) never sets the triples-assertion flag, so the guard is
            // statically false here.

            self.initialize_initialization_concepts(indi_proc_sat_node, calc_alg_context); // 821
            self.initialize_role_assertions(indi_proc_sat_node, calc_alg_context); // 822
            self.initialize_data_assertions(indi_proc_sat_node, calc_alg_context); // 823

            calc_alg_context
                .process_context_mut()
                .sat_node_mut(*indi_proc_sat_node)
                .set_initialized(true); // 825

            // cpp 827–833: nominal + saturation-individuals analysation observer →
            // addIndividualSaturationAnalysationNodeLinker. KONCLUDE-PORT-NOTE[api]:
            // the Task subsystem's analysation observer is never installed in the
            // port, so the guard is statically false.
        }
        true // 835
    }

    /// Port of `initializeInitializationConcepts` (.cpp 5464–5706) — the 245-line
    /// seeder that establishes the start label of a saturation node.
    ///
    /// Resolves the node's `CSaturationConceptDataItem` (init concept / negation /
    /// role-ranges / data-range flag / potentially-existential back-prop hint),
    /// picks the special-reference node + mode (COPY vs SUBSTITUTE), then:
    ///  - substitute-mode: chase the substitute chain to the block node; if the init
    ///    concept is not already in its label, install a substituting node (mode 1),
    ///    propagate direct/indirect status + successor-connected nominals, and skip
    ///    adding init concepts; otherwise fall back to copy-mode.
    ///  - nominal node with a name: resolve the representative-assertion node, copy +
    ///    try-flat-label-copy; nominal node without a name: add its asserted concepts
    ///    directly.
    ///  - `mConfCopyNodeFromTopIndividualForManyConcepts`: if ⊤'s saturation node has
    ///    > 10 concepts, copy from it.
    ///  - copy-mode: if `isProcessingCritical` → mark UNPROCESSED|INSUFFICIENT and set
    ///    insufficient-node-occured + skip init concepts; else chase substitute chain
    ///    and `initializeIndividualNodeByCoping`.
    ///  - not-initialized fallback: `initRootIndividualSaturationProcessNode`, mode 4,
    ///    add base ⊤ (or ⊤-data-range) + the universal-connection-nominal-value concept.
    ///  - `addIndividualToCompletionQueue`.
    ///  - if `addInitializationConcepts`: add the init concept (filtered); when special
    ///    + the init concept is a disjunction already in the special node's label,
    ///    queue a `CConceptSaturationProcessLinker` for it; add init-role range
    ///    concepts of every indirect super-role.
    ///  - drain the node's initializing backward-propagation links: install each, then
    ///    propagate indirect status + successor-connected nominals back to the source.
    ///
    /// W6-DEFER[api]: every line dereferences SAT-1 sat_node getters / the
    /// `CReapplyConceptSaturationLabelSet` + `CSaturationConceptDataItem` satellites /
    /// `CConceptSaturationProcessLinker` + `CBackwardSaturationPropagationLink`, and
    /// calls sibling s-unit methods (`addConceptFilteredToIndividual`,
    /// `updateDirect/IndirectAddingIndividualStatusFlags`, `updateAddingSuccessorConnectedNominal`,
    /// `updateMaxCardinalityCandidates`, `getSeparatedSaturationConceptAssertionResolveNode`,
    /// `getIndividualNodeForConcept`, `getResolvedIndividualNodeRepresentativeAssertion`,
    /// `isProcessingCritical`, `setInsufficientNodeOccured`, `initializeIndividualNodeByCoping`,
    /// `addIndividualToCompletionQueue`, `createConceptSaturationProcessLinker`,
    /// `installBackwardPropagationLink`). The config flags it reads
    /// (`mConfForceAllConceptInsertion`, `mConfForceAllCopyInsteadOfSubstituition`,
    /// `mConfCopyNodeFromTopIndividualForManyConcepts`) and the counter it bumps
    /// (`mSubstituitedIndiNodeCount`) ARE present on `self` (see `algorithm.rs`).
    /// Full body lands when SAT-1 + the sibling s-units are ported.
    pub fn initialize_initialization_concepts(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        use super::super::model::concept_process::{
            SaturationConceptReferenceLinkingId, SATURATION_COPY_MODE, SATURATION_SUBSTITUTE_MODE,
        };
        use super::super::model::op::{CCAND, CCEQ, CCOR};

        let mut required_back_prop = true; // 5466
        let mut special_indi_node = SatNodeId::NONE; // 5468
        let mut copy_individual_node = false; // 5472
        let mut substituite_individual_node = false; // 5473

        // conceptSatItem = node->getSaturationConceptReferenceLinking() (5475–5476).
        // KONCLUDE-PORT-NOTE[api]: the single C++ CSaturationConceptDataItem is split
        // across two arenas in the port — the process-side
        // ExtendedConceptReferenceLinkingData (concept/negation/role-ranges) whose
        // `concept_reference_linking` raw handle points at the ontology-side
        // SaturationConceptReferenceLinking (exist-init/data-range flags, special
        // reference + mode, node pointer).
        let concept_sat_item = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_saturation_concept_reference_linking();

        let mut init_concept = ConceptId::NONE; // 5478
        let mut init_negated = false; // 5479
        let mut data_range_concept = false; // 5480
        let mut init_role = RoleId::NONE; // 5481
        let mut onto_item = SaturationConceptReferenceLinkingId::NONE;

        if concept_sat_item.is_some() {
            let (concept, negated, role, onto_ref) = {
                let item = calc_alg_context
                    .process_context()
                    .extended_con_ref_linking_data(concept_sat_item);
                (
                    item.get_saturation_concept(),
                    item.get_saturation_negation(),
                    item.get_saturation_role_ranges(),
                    item.get_concept_reference_linking(),
                )
            };
            init_concept = concept; // 5484
            init_negated = negated; // 5485
            init_role = role; // 5486
            onto_item = SaturationConceptReferenceLinkingId::new(onto_ref);
            if onto_item.is_some() {
                let onto = calc_alg_context
                    .ontology_arenas()
                    .saturation_concept_reference_linking(onto_item);
                if !self.conf_force_all_concept_insertion {
                    required_back_prop = onto.is_potentially_exist_initialization_concept();
                    // 5489
                }
                data_range_concept = onto.is_data_range_concept(); // 5491
            }
        }

        // specialRefItem → specialIndiNode (5494–5499).
        if onto_item.is_some() {
            let special_ref_item = calc_alg_context
                .ontology_arenas()
                .saturation_concept_reference_linking(onto_item)
                .get_special_item_reference();
            if special_ref_item.is_some() {
                special_indi_node = calc_alg_context
                    .ontology_arenas()
                    .saturation_concept_reference_linking(special_ref_item)
                    .get_individual_process_node_for_concept();
            }
        }

        // mode → copy / substitute (5501–5509).
        if onto_item.is_some() {
            let mode = calc_alg_context
                .ontology_arenas()
                .saturation_concept_reference_linking(onto_item)
                .get_special_reference_mode();
            if mode == SATURATION_COPY_MODE {
                copy_individual_node = true;
            } else if mode == SATURATION_SUBSTITUTE_MODE {
                substituite_individual_node = true;
            }
        }
        let init_debug = init_concept.is_some()
            && super::sat_init_debug_tag()
                == Some(
                    calc_alg_context
                        .ontology_arenas()
                        .concept(init_concept)
                        .get_concept_tag(),
                );
        if init_debug {
            let special_tag = if special_indi_node.is_some() {
                let special_item = calc_alg_context
                    .process_context()
                    .sat_node(special_indi_node)
                    .get_saturation_concept_reference_linking();
                if special_item.is_some() {
                    let special_concept = calc_alg_context
                        .process_context()
                        .extended_con_ref_linking_data(special_item)
                        .get_saturation_concept();
                    calc_alg_context
                        .ontology_arenas()
                        .concept(special_concept)
                        .get_concept_tag()
                } else {
                    -1
                }
            } else {
                -1
            };
            eprintln!(
                "SAT-INIT-SELECT node={} init-tag={} special={} special-tag={} copy={} substitute={}",
                indi_proc_sat_node.raw,
                calc_alg_context
                    .ontology_arenas()
                    .concept(init_concept)
                    .get_concept_tag(),
                special_indi_node.raw,
                special_tag,
                copy_individual_node,
                substituite_individual_node,
            );
        }

        let mut add_initialization_concepts = true; // 5511
        let mut initialized = false; // 5512
        if special_indi_node.is_some()
            && !calc_alg_context
                .process_context()
                .sat_node(special_indi_node)
                .is_initialized()
        {
            special_indi_node = SatNodeId::NONE; // 5514
        }
        if special_indi_node.is_some() {
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(*indi_proc_sat_node)
                .set_reference_individual_saturation_process_node(special_indi_node);
            // 5517
        }
        if special_indi_node.is_some()
            && substituite_individual_node
            && (self.conf_force_all_copy_instead_of_substituition || init_role.is_some())
        {
            substituite_individual_node = false; // 5520
            copy_individual_node = true; // 5521
        }
        if special_indi_node.is_some() && substituite_individual_node {
            // Chase the substitute chain to the block node (5524–5527).
            let mut blocked_indi_node = special_indi_node;
            while calc_alg_context
                .process_context()
                .sat_node(blocked_indi_node)
                .has_substitute_individual_node()
            {
                blocked_indi_node = calc_alg_context
                    .process_context()
                    .sat_node(blocked_indi_node)
                    .get_substitute_individual_node();
            }
            // contained = blockConSet->getConceptDescriptorAndReapplyQueue(initConcept, …) (5528–5534).
            let block_con_set = calc_alg_context
                .process_context()
                .sat_node(blocked_indi_node)
                .reapply_con_sat_label_set;
            let mut contained = false;
            if block_con_set.is_some() {
                let init_con_tag = calc_alg_context
                    .ontology_arenas()
                    .concept(init_concept)
                    .get_concept_tag();
                let mut con_sat_des = super::satellites::ConceptSaturationDescriptorId::NONE;
                let mut imp_reapply =
                    super::satellites::ImplicationReapplyConceptSaturationDescriptorId::NONE;
                contained = calc_alg_context
                    .process_context()
                    .reapply_con_sat_label_set(block_con_set)
                    .get_concept_descriptor_and_reapply_queue_by_tag(
                        init_con_tag,
                        &mut con_sat_des,
                        &mut imp_reapply,
                    );
            }
            if !contained {
                self.substituited_indi_node_count += 1; // 5537
                                                        // initSubstituitingIndividualSaturationProcessNode(blocked) copies the
                                                        // blocked node's flag words (5538).
                let (blocked_direct, blocked_indirect) = {
                    let blocked = calc_alg_context
                        .process_context()
                        .sat_node(blocked_indi_node);
                    (blocked.direct_status_flags, blocked.indirect_status_flags)
                };
                {
                    let node = calc_alg_context
                        .process_context_mut()
                        .sat_node_mut(*indi_proc_sat_node);
                    node.direct_status_flags = blocked_direct;
                    node.indirect_status_flags = blocked_indirect;
                    node.set_substitute_individual_node(special_indi_node); // 5539
                    node.set_reference_mode(1); // 5540
                    node.clear_concept_saturation_process_linker(); // 5541
                }
                add_initialization_concepts = false; // 5542
                initialized = true; // 5543
                self.update_direct_adding_individual_status_flags_with_flags(
                    *indi_proc_sat_node,
                    &blocked_direct,
                    calc_alg_context,
                ); // 5545
                self.update_indirect_adding_individual_status_flags(
                    *indi_proc_sat_node,
                    &blocked_indirect,
                    calc_alg_context,
                ); // 5546
                let blocked_nominal_set = calc_alg_context
                    .process_context_mut()
                    .sat_node_successor_connected_nominal_set(blocked_indi_node, false);
                self.update_adding_successor_connected_nominal_set(
                    *indi_proc_sat_node,
                    blocked_nominal_set,
                    calc_alg_context,
                ); // 5547
            } else {
                copy_individual_node = true; // 5550
            }
        }

        let mut try_flat_label_copy = false; // 5554
        calc_alg_context
            .process_context_mut()
            .sat_node_mut(*indi_proc_sat_node)
            .set_required_backward_propagation(required_back_prop); // 5555

        if special_indi_node.is_none() {
            let nominal_indi = calc_alg_context
                .process_context()
                .sat_node(*indi_proc_sat_node)
                .get_nominal_individual();
            if nominal_indi.is_some() {
                if nominal_indi.index()
                    < calc_alg_context.ontology_arenas().individual_count() as usize
                {
                    // Exact named-ABox path (C++ 5659–5674): resolve the
                    // individual's assertion set against the shared separated
                    // TOP node, saturate that reusable assertion-resolved node,
                    // then flat-copy its resolved label. In particular, do not
                    // seed the raw assertions directly on the named node: that
                    // loses Konclude's assertion-set disjunction resolution and
                    // makes globally absorbed ORs spuriously insufficient.
                    calc_alg_context
                        .process_context_mut()
                        .sat_node_mut(*indi_proc_sat_node)
                        .set_abox_individual_representation_node(true);
                    let has_individual_name = calc_alg_context
                        .ontology_arenas()
                        .individual(nominal_indi)
                        .has_individual_name();
                    if has_individual_name {
                        let resolve_node = if calc_alg_context
                            .process_context()
                            .sat_node(*indi_proc_sat_node)
                            .is_separated()
                        {
                            self.get_separated_saturation_concept_assertion_resolve_node(
                                calc_alg_context,
                            )
                        } else {
                            let top_concept = calc_alg_context
                                .processing_data_box()
                                .ontology_top_concept();
                            self.get_individual_node_for_concept(
                                top_concept,
                                false,
                                calc_alg_context,
                            )
                        };
                        if resolve_node.is_some() {
                            let assertion_resolved_node = self
                                .get_resolved_individual_node_representative_assertion(
                                    resolve_node,
                                    nominal_indi,
                                    calc_alg_context,
                                );
                            if assertion_resolved_node.is_some() {
                                special_indi_node = assertion_resolved_node;
                                copy_individual_node = true;
                                try_flat_label_copy = true;
                            } else {
                                self.update_direct_adding_individual_status_flags(
                                    *indi_proc_sat_node,
                                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNPROCESSED
                                        | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                                    calc_alg_context,
                                );
                                self.set_insufficient_node_occured(calc_alg_context);
                            }
                        } else {
                            // Konclude's generator guarantees a resolve base.
                            // A missing base in the typed port is an incomplete
                            // job, never permission to reinterpret a named ABox
                            // individual as an anonymous direct seed.
                            self.update_direct_adding_individual_status_flags(
                                *indi_proc_sat_node,
                                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNPROCESSED
                                    | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                                calc_alg_context,
                            );
                            self.set_insufficient_node_occured(calc_alg_context);
                        }
                    } else {
                        // Exact anonymous-individual branch (C++ 5675–5685):
                        // add only the assertion linker entries. The own
                        // nominal concept is not synthesized into that list.
                        let assertions = calc_alg_context
                            .ontology_arenas()
                            .individual(nominal_indi)
                            .get_assertion_concept_linker()
                            .to_vec();
                        for assertion in assertions {
                            self.add_concept_filtered_to_individual(
                                assertion.target,
                                assertion.negated,
                                indi_proc_sat_node,
                                calc_alg_context,
                            );
                        }
                    }
                } else {
                    // A dangling typed individual id is an incomplete
                    // saturation job, never an empty ABox.
                    self.update_direct_adding_individual_status_flags(
                        *indi_proc_sat_node,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNPROCESSED
                            | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    );
                    self.set_insufficient_node_occured(calc_alg_context);
                }
            }
        }

        // ⊤-copy heuristic (5594–5620): copy from ⊤'s node when it carries > 10
        // concepts.
        if special_indi_node.is_none()
            && !data_range_concept
            && self.conf_copy_node_from_top_individual_for_many_concepts
        {
            let top_concept = calc_alg_context.processing_data_box().ontology_top_concept;
            special_indi_node =
                Self::s07_concept_reference_node(top_concept, false, calc_alg_context);
            if special_indi_node.is_some()
                && calc_alg_context
                    .process_context()
                    .sat_node(special_indi_node)
                    .is_initialized()
            {
                let top_con_set = calc_alg_context
                    .process_context()
                    .sat_node(special_indi_node)
                    .reapply_con_sat_label_set;
                let mut many = false;
                if top_con_set.is_some() {
                    many = calc_alg_context
                        .process_context()
                        .reapply_con_sat_label_set(top_con_set)
                        .get_concept_count()
                        > 10;
                }
                if many {
                    copy_individual_node = true; // 5613
                }
            } else {
                special_indi_node = SatNodeId::NONE; // 5617
            }
        }

        if special_indi_node.is_some() && copy_individual_node {
            // 5622–5638
            let concept_sat_item_handle: Cint64 = concept_sat_item.raw;
            if self.is_processing_critical(
                *indi_proc_sat_node,
                concept_sat_item_handle,
                special_indi_node,
                calc_alg_context,
            ) {
                self.update_direct_adding_individual_status_flags(
                    *indi_proc_sat_node,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNPROCESSED
                        | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                    calc_alg_context,
                ); // 5625
                self.set_insufficient_node_occured(calc_alg_context); // 5626
                add_initialization_concepts = false; // 5627
                calc_alg_context
                    .process_context_mut()
                    .sat_node_mut(*indi_proc_sat_node)
                    .clear_concept_saturation_process_linker(); // 5628
            } else {
                let mut blocked_indi_node = special_indi_node;
                while calc_alg_context
                    .process_context()
                    .sat_node(blocked_indi_node)
                    .has_substitute_individual_node()
                {
                    blocked_indi_node = calc_alg_context
                        .process_context()
                        .sat_node(blocked_indi_node)
                        .get_substitute_individual_node();
                } // 5630–5633
                self.initialize_individual_node_by_coping(
                    *indi_proc_sat_node,
                    blocked_indi_node,
                    try_flat_label_copy,
                    calc_alg_context,
                ); // 5634
            }
            initialized = true; // 5636
        }

        if !initialized {
            // 5638–5660: root initialization.
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(*indi_proc_sat_node)
                .init_root_individual_saturation_process_node(); // 5640
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(*indi_proc_sat_node)
                .set_reference_mode(4); // 5641
            let base_top_concept = if !data_range_concept {
                calc_alg_context.processing_data_box().ontology_top_concept
            } else {
                calc_alg_context
                    .processing_data_box()
                    .ontology_top_data_range_concept
            }; // 5642–5647
            if base_top_concept.is_some() {
                self.add_concept_filtered_to_individual(
                    base_top_concept,
                    false,
                    indi_proc_sat_node,
                    calc_alg_context,
                ); // 5649
            }
            // univConnNomValueConcept (5651–5654): the TBox
            // universal-connection-nominal-value concept.
            // KONCLUDE-PORT-NOTE[api]: not modeled in the port's databox and never
            // built by the bridge (nominal-free fragment); statically absent.
        }

        self.add_individual_to_completion_queue(indi_proc_sat_node, calc_alg_context); // 5662

        if add_initialization_concepts {
            // 5667–5697
            if init_concept.is_some() {
                let label_set = calc_alg_context
                    .process_context_mut()
                    .sat_node_reapply_concept_saturation_label_set(*indi_proc_sat_node, true);
                self.add_concept_filtered_to_individual_label_set(
                    init_concept,
                    init_negated,
                    indi_proc_sat_node,
                    label_set,
                    false,
                    calc_alg_context,
                ); // 5669
                if special_indi_node.is_some() {
                    // Disjunction already present in the special node's label →
                    // requeue a process linker for it (5670–5688).
                    let init_con_op_code = calc_alg_context
                        .ontology_arenas()
                        .concept(init_concept)
                        .get_operator_code();
                    let init_concept_disjunction = (init_negated
                        && (init_con_op_code == CCAND || init_con_op_code == CCEQ))
                        || (!init_negated && init_con_op_code == CCOR);
                    if init_concept_disjunction {
                        let spec_con_set = calc_alg_context
                            .process_context()
                            .sat_node(special_indi_node)
                            .reapply_con_sat_label_set;
                        if spec_con_set.is_some() {
                            let init_con_tag = calc_alg_context
                                .ontology_arenas()
                                .concept(init_concept)
                                .get_concept_tag();
                            let mut init_con_sat_des =
                                super::satellites::ConceptSaturationDescriptorId::NONE;
                            let mut init_con_imp_des =
                                super::satellites::ImplicationReapplyConceptSaturationDescriptorId::NONE;
                            let found = calc_alg_context
                                .process_context()
                                .reapply_con_sat_label_set(spec_con_set)
                                .get_concept_saturation_descriptor_by_tag(
                                    init_con_tag,
                                    &mut init_con_sat_des,
                                    &mut init_con_imp_des,
                                );
                            if found
                                && calc_alg_context
                                    .process_context()
                                    .con_sat_desc(init_con_sat_des)
                                    .get_negation()
                                    == init_negated
                            {
                                let linker_payload =
                                    self.create_concept_saturation_process_linker(calc_alg_context);
                                let linker =
                                    ConceptSaturationProcessLinkerId::new(linker_payload.raw);
                                calc_alg_context
                                    .process_context_mut()
                                    .con_sat_proc_linker_mut(linker)
                                    .init_concept_saturation_process_linker(init_con_sat_des);
                                calc_alg_context
                                    .process_context_mut()
                                    .sat_node_add_concept_saturation_process_linker(
                                        *indi_proc_sat_node,
                                        linker,
                                    );
                            }
                        }
                    }
                }
            }
            if init_role.is_some() {
                // Init-role RANGE concepts of every indirect super-role (5689–5697).
                let super_roles: Vec<NegLink<RoleId>> =
                    Self::saturation_indirect_super_roles(init_role, calc_alg_context); // ([identity])
                for super_role_link in super_roles {
                    let range_concepts: Vec<NegLink<ConceptId>> = calc_alg_context
                        .ontology_arenas()
                        .role(super_role_link.target)
                        .get_domain_range_concept_list(!super_role_link.negated)
                        .to_vec();
                    for range_link in range_concepts {
                        self.add_concept_filtered_to_individual(
                            range_link.target,
                            range_link.negated,
                            indi_proc_sat_node,
                            calc_alg_context,
                        );
                    }
                }
            }
        }

        // Drain the node's initializing backward-propagation links (5699–5705):
        // install each and propagate the node's indirect status + nominal set back
        // to the source.
        let mut back_sat_prop_link_it = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_initializing_backward_propagation_links();
        while back_sat_prop_link_it.is_some() {
            let back_prop_link = back_sat_prop_link_it;
            back_sat_prop_link_it = calc_alg_context
                .process_context()
                .backward_sat_prop_link(back_prop_link)
                .get_next();
            calc_alg_context
                .process_context_mut()
                .backward_sat_prop_link_mut(back_prop_link)
                .set_next(super::satellites::BackwardSaturationPropagationLinkId::NONE); // clearNext()
            let (source, link_role) = {
                let link = calc_alg_context
                    .process_context()
                    .backward_sat_prop_link(back_prop_link);
                (link.get_source_individual(), link.get_link_role())
            };
            self.install_backward_propagation_link(
                source,
                *indi_proc_sat_node,
                link_role,
                back_prop_link,
                true,
                true,
                calc_alg_context,
            );
            let node_indirect_flags = calc_alg_context
                .process_context()
                .sat_node(*indi_proc_sat_node)
                .indirect_status_flags;
            self.update_indirect_adding_individual_status_flags(
                source,
                &node_indirect_flags,
                calc_alg_context,
            );
            let node_nominal_set = calc_alg_context
                .process_context_mut()
                .sat_node_successor_connected_nominal_set(*indi_proc_sat_node, false);
            self.update_adding_successor_connected_nominal_set(
                source,
                node_nominal_set,
                calc_alg_context,
            );
        }
    }

    /// Port of `individualNodeConclusion` (.cpp 5709–5714).
    ///
    /// If the node still has a queued concept-saturation process linker, re-enqueue it
    /// for processing.
    ///
    /// ```text
    /// conSatProLinker = indiProcSatNode->getConceptSaturationProcessLinker();  // sat_node SAT-1
    /// if (conSatProLinker) { self.add_individual_to_processing_queue(indiProcSatNode, ctx); }
    /// ```
    pub fn individual_node_conclusion(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let con_sat_pro_linker = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_concept_saturation_process_linker();
        if con_sat_pro_linker.is_some() {
            self.add_individual_to_processing_queue(indi_proc_sat_node, calc_alg_context);
        }
    }

    /// Port of `countConceptsOfReferredNodes` (.cpp 5369–5400).
    ///
    /// Recursively walks the operand tree of `concept` (only through SUB/EQ/AND under
    /// no-negation and EQ/OR under negation), counting, over the saturation nodes
    /// referenced by each operand concept: unprocessed referred nodes, total referred
    /// concepts, and "many-concept" referred nodes (label size ≥
    /// `mConfReferredNodeManyConceptCount`). Operand nodes that are not yet initialized
    /// recurse one level deeper (bounded by `depth`). Always returns `false`.
    ///
    /// ```text
    /// if (depth <= 0) return false;
    /// if (concept) {
    ///   initConCode = concept->getOperatorCode();                            // model::Concept
    ///   if (!negation && (CCSUB||CCEQ||CCAND)) || (negation && (CCEQ||CCOR)) {
    ///     for opConLinkerIt in concept->getOperandList() {                   // model::Concept
    ///       opConcept = opConLinkerIt->getData();
    ///       opNegation = opConLinkerIt->isNegated() ^ negation;
    ///       opIndiNode = self.get_individual_node_for_concept(opConcept, opNegation, ctx); // sibling
    ///       if (opIndiNode && opIndiNode->isInitialized()) {                 // sat_node SAT-1
    ///         if (opIndiNode->getDirectStatusFlags()->hasUnprocessedFlag()) ++unprocessedRefCount;
    ///         opConSet = opIndiNode->getReapplyConceptSaturationLabelSet(false);
    ///         if (opConSet) {
    ///           opConCount = opConSet->getConceptCount();
    ///           totalRefConceptCount += opConCount;
    ///           if (opConCount >= mConfReferredNodeManyConceptCount) ++manyConceptRefIndiNodeCount;
    ///         }
    ///       } else {
    ///         self.count_concepts_of_referred_nodes(opConcept, opNegation, depth-1,
    ///             manyConceptRefIndiNodeCount, totalRefConceptCount, unprocessedRefCount, ctx);
    ///       }
    ///     }
    ///   }
    /// }
    /// return false;
    /// ```
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: C++ passes the three accumulators by reference
    /// (`cint64&`); the port takes `&mut Cint64` to mirror it.
    pub fn count_concepts_of_referred_nodes(
        &mut self,
        concept: ConceptId,
        negation: bool,
        depth: Cint64,
        many_concept_ref_indi_node_count: &mut Cint64,
        total_ref_concept_count: &mut Cint64,
        unprocessed_ref_count: &mut Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (
            concept,
            negation,
            &many_concept_ref_indi_node_count,
            &total_ref_concept_count,
            &unprocessed_ref_count,
            &calc_alg_context,
        );
        if depth <= 0 {
            return false;
        }
        // W6-DEFER[api]: the operand walk needs model::Concept operator-code /
        // operand-list accessors, the sibling `get_individual_node_for_concept`, and
        // SAT-1 sat_node label-set/status-flag getters. `self.conf_referred_node_many_concept_count`
        // (the `mConfReferredNodeManyConceptCount` threshold) already resolves.
        let _many_threshold = self.conf_referred_node_many_concept_count;
        false
    }

    /// Port of `isProcessingCritical` (.cpp 5403–5420).
    ///
    /// When `mConfForceManyConceptSaturation` is set and a special-reference node +
    /// concept item are present, tallies the referred-node concept counts via
    /// `countConceptsOfReferredNodes` and returns `true` if any of the three limits
    /// is reached.
    ///
    /// ```text
    /// if (mConfForceManyConceptSaturation && specRefIndiProcSatNode && conceptSatItem) {
    ///   initConcept = conceptSatItem->getSaturationConcept();               // satellite (W6-DEFER)
    ///   initNegated = conceptSatItem->getSaturationNegation();
    ///   manyRefIndiConCount = totalRefConCount = unprocessedRefCount = 0;
    ///   self.count_concepts_of_referred_nodes(initConcept, initNegated,
    ///       mConfReferredNodeCheckingDepth, manyRefIndiConCount, totalRefConCount,
    ///       unprocessedRefCount, ctx);
    ///   if (manyRefIndiConCount >= mConfManyConceptReferredNodeCountProcessLimit
    ///       || totalRefConCount >= mConfReferredNodeConceptCountProcessLimit
    ///       || unprocessedRefCount >= mConfReferredNodeUnprocessedCountProcessLimit) return true;
    /// }
    /// return false;
    /// ```
    pub fn is_processing_critical(
        &mut self,
        indi_proc_sat_node: SatNodeId,
        concept_sat_item: SaturationConceptDataItemHandle,
        spec_ref_indi_proc_sat_node: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let _ = (indi_proc_sat_node, &calc_alg_context);
        // `mConfForceManyConceptSaturation` resolves on `self`; the rest needs the
        // `CSaturationConceptDataItem` satellite getters (W6-DEFER[api]).
        if self.conf_force_many_concept_saturation != 0
            && spec_ref_indi_proc_sat_node != Id::NONE
            && concept_sat_item != super::super::model::substrate::INVALID
        {
            // W6-DEFER[api]: PORT-PENDING — conceptSatItem->getSaturationConcept()/Negation,
            // self.count_concepts_of_referred_nodes(...) over mConfReferredNodeCheckingDepth,
            // then the three `mConf*ProcessLimit` comparisons (all present on `self`).
        }
        false
    }

    /// Port of `resolveSpecialInitializationIndividualNode` (.cpp 5424–5460).
    ///
    /// Among the operand concepts of the (non-negated SUB/EQ/AND or negated EQ/OR)
    /// init concept, picks the already-initialized saturation node with the LARGEST
    /// label and returns it as the special-reference node (else the original one).
    ///
    /// ```text
    /// if (specRefIndiProcSatNode && conceptSatItem) {
    ///   initConcept = conceptSatItem->getSaturationConcept();               // satellite
    ///   initNegated = conceptSatItem->getSaturationNegation();
    ///   maxConCountSpecRefIndiNode = nullptr; maxConCount = 0;
    ///   if (initConcept) {
    ///     initConCode = initConcept->getOperatorCode();
    ///     if (!initNegated && (CCSUB||CCEQ||CCAND)) || (initNegated && (CCEQ||CCOR)) {
    ///       for opConLinkerIt in initConcept->getOperandList() {
    ///         opConcept = opConLinkerIt->getData();
    ///         opNegation = opConLinkerIt->isNegated() ^ initNegated;
    ///         opIndiNode = self.get_individual_node_for_concept(opConcept, opNegation, ctx);
    ///         if (opIndiNode && opIndiNode->isInitialized()) {
    ///           opConSet = opIndiNode->getReapplyConceptSaturationLabelSet(false);
    ///           if (opConSet) {
    ///             opConCount = opConSet->getConceptCount();
    ///             if (!maxConCountSpecRefIndiNode || opConCount > maxConCount) {
    ///               maxConCount = opConCount; maxConCountSpecRefIndiNode = opIndiNode;
    ///             }
    ///           }
    ///         }
    ///       }
    ///     }
    ///   }
    ///   if (maxConCountSpecRefIndiNode) specRefIndiProcSatNode = maxConCountSpecRefIndiNode;
    /// }
    /// return specRefIndiProcSatNode;
    /// ```
    pub fn resolve_special_initialization_individual_node(
        &mut self,
        indi_proc_sat_node: SatNodeId,
        concept_sat_item: SaturationConceptDataItemHandle,
        spec_ref_indi_proc_sat_node: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let _ = (indi_proc_sat_node, concept_sat_item, &calc_alg_context);
        // W6-DEFER[api]: PORT-PENDING — see the transcription above (satellite item
        // getters + model::Concept operand walk + sibling get_individual_node_for_concept
        // + SAT-1 label-set getters). C++ returns the original node when no larger one
        // is found, so the faithful default is the passed-through node.
        spec_ref_indi_proc_sat_node
    }

    /// Port of `initializeRoleAssertions` (.cpp 5079–5140).
    ///
    /// For a nominal node, walks the nominal individual's assertion- and
    /// reverse-assertion role linkers; for each `(role, otherIndi)` resolves the peer
    /// saturation node (by saturation id), installs the bidirectional role-assertion
    /// links (`createRoleAssertionLink` + `addRoleAssertion`), falling back to a
    /// resolved representative-range-assertion node when the peer is absent, and
    /// records every neighbour role assertion in the node's neighbour-role-assertion
    /// hash.
    ///
    /// W6-DEFER[api]: PORT-PENDING — needs sat_node `getNominalIndividual`/`isSeparated`/
    /// `isInitialized`/`getIndividualExtensionData(true)`/`addRoleAssertion` (SAT-1),
    /// the `CLinkedNeighbourRoleAssertionSaturationHash` satellite, model::Individual
    /// assertion/reverse-assertion role linkers + role accessors, and the sibling
    /// s-unit methods `getSaturationIDForIndividualNode`,
    /// `getSeparatedSaturationConceptAssertionResolveNode`, `getIndividualNodeForConcept`,
    /// `getIndividualNodeForIndividual`, `getResolvedIndividualNodeRepresentativeRangeAssertion`,
    /// and the in-unit `create_role_assertion_link`. The full assertion/reverse-assertion
    /// double loop is preserved in the C++ (see .cpp 5101–5138).
    pub fn initialize_role_assertions(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let nominal_indi = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_nominal_individual();
        if nominal_indi.is_none() {
            return;
        }
        if nominal_indi.index() >= calc_alg_context.ontology_arenas().individual_count() as usize {
            self.update_direct_adding_individual_status_flags(
                *indi_proc_sat_node,
                super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNPROCESSED
                    | super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                calc_alg_context,
            );
            self.set_insufficient_node_occured(calc_alg_context);
            return;
        }

        // Exact C++ 5084–5134 endpoint handshake, over the port's value-backed
        // saturation assertion journal. Each model assertion is present on both
        // endpoints, once as its forward face and once as its reverse face.
        // Konclude skips the face while the peer node is still uninitialized.
        // Whichever endpoint initializes second then installs both semantic
        // directions. In particular, this prevents an early reverse face from
        // queuing an initializing backward link whose later status propagation
        // would incorrectly make the already-finished ABox peer insufficient.
        // Record the exact deterministic base-assertion journal while
        // replaying it.  The ontology model retains the same forward and
        // reverse linkers, so their mere presence cannot mean that an
        // assertion was omitted.  Konclude's two loops below are the
        // authoritative coverage contract: forward and reverse faces have
        // distinct orientation bits and every asserted endpoint/role must
        // occur in the staged journal.
        let mut covered_model_assertions = Vec::new();
        let mut role_assertion_linker = calc_alg_context
            .process_context()
            .sat_node_ext_role_assertion_linker(*indi_proc_sat_node);
        while role_assertion_linker.is_some() {
            if role_assertion_linker.index()
                >= calc_alg_context
                    .process_context()
                    .sat_succ_role_assertion_linker_count()
            {
                self.update_direct_adding_individual_status_flags(
                    *indi_proc_sat_node,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNPROCESSED
                        | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                    calc_alg_context,
                );
                self.set_insufficient_node_occured(calc_alg_context);
                return;
            }
            let (mut destination, role, role_inversed, next) = {
                let linker = calc_alg_context
                    .process_context()
                    .sat_succ_role_assertion_linker(role_assertion_linker);
                (
                    linker.get_assertion_destination_node(),
                    linker.get_assertion_role(),
                    linker.get_assertion_role_negation(),
                    linker.get_next(),
                )
            };
            if destination.is_none()
                || destination.index() >= calc_alg_context.process_context().sat_node_count()
                || role.is_none()
                || role.index() >= calc_alg_context.ontology_arenas().role_count() as usize
            {
                self.update_direct_adding_individual_status_flags(
                    *indi_proc_sat_node,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNPROCESSED
                        | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                    calc_alg_context,
                );
                self.set_insufficient_node_occured(calc_alg_context);
                return;
            }
            let destination_individual = calc_alg_context
                .process_context()
                .sat_node(destination)
                .get_nominal_individual();
            if destination_individual.is_none()
                || destination_individual.index()
                    >= calc_alg_context.ontology_arenas().individual_count() as usize
            {
                self.update_direct_adding_individual_status_flags(
                    *indi_proc_sat_node,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNPROCESSED
                        | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                    calc_alg_context,
                );
                self.set_insufficient_node_occured(calc_alg_context);
                return;
            }
            covered_model_assertions.push((destination_individual, role, role_inversed));
            let peer_initialized = destination == *indi_proc_sat_node
                || calc_alg_context
                    .process_context()
                    .sat_node(destination)
                    .is_initialized();
            if peer_initialized {
                self.create_role_assertion_link(
                    indi_proc_sat_node,
                    &mut destination,
                    role,
                    role_inversed,
                    calc_alg_context,
                );
                let mut reciprocal_source = destination;
                let mut reciprocal_destination = *indi_proc_sat_node;
                self.create_role_assertion_link(
                    &mut reciprocal_source,
                    &mut reciprocal_destination,
                    role,
                    !role_inversed,
                    calc_alg_context,
                );
            }
            role_assertion_linker = next;
        }

        // The native bridge translates model-level role assertions into the
        // value-backed journal above before initialization. Other callers may
        // still populate only the model linkers. Until their object-backed
        // neighbour resolution path is ported, fail closed instead of silently
        // classifying without those assertions.
        let has_unmaterialized_model_role_assertions = {
            let individual = calc_alg_context.ontology_arenas().individual(nominal_indi);
            individual.get_assertion_role_linker().iter().any(|assertion| {
                !covered_model_assertions.contains(&(
                    assertion.individual,
                    assertion.role,
                    false,
                ))
            }) || individual
                .get_reverse_assertion_role_linker()
                .iter()
                .any(|assertion| {
                    !covered_model_assertions.contains(&(
                        assertion.individual,
                        assertion.role,
                        true,
                    ))
                })
        };
        if has_unmaterialized_model_role_assertions {
            self.update_direct_adding_individual_status_flags(
                *indi_proc_sat_node,
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNPROCESSED
                    | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                calc_alg_context,
            );
            self.set_insufficient_node_occured(calc_alg_context);
        }
    }

    /// Port of `initializeDataAssertions` (.cpp 5145–5167).
    ///
    /// For a nominal node, resolves the assertion-resolve node (separated or ⊤), then
    /// for each data assertion `(role, dataLiteral)` of the nominal individual creates
    /// a data-literal successor.
    ///
    /// ```text
    /// nominalIndi = indiProcSatNode->getNominalIndividual();                  // sat_node SAT-1
    /// if (nominalIndi) {
    ///   saturationID = self.get_saturation_id_for_individual_node(nominalIndi, ctx); // sibling
    ///   resolveNode = indiProcSatNode->isSeparated()
    ///       ? self.get_separated_saturation_concept_assertion_resolve_node(ctx)      // sibling
    ///       : self.get_individual_node_for_concept(ctx.processing_data_box().getOntologyTopConcept(), false, ctx);
    ///   for assDataLinkerIt in nominalIndi->getAssertionDataLinker() {        // model::Individual
    ///     role = assDataLinkerIt->getRole(); dataLiteral = assDataLinkerIt->getDataLiteral();
    ///     self.create_successor_for_data_literal(indiProcSatNode, role, dataLiteral, ctx);
    ///   }
    /// }
    /// ```
    ///
    /// KONCLUDE-PORT-NOTE[unclear]: C++ computes `saturationID` and `resolveNode` but
    /// the visible loop only uses `create_successor_for_data_literal`; both are kept
    /// for fidelity (they guard the resolve path in `create_successor_for_data_literal`).
    pub fn initialize_data_assertions(
        &mut self,
        indi_proc_sat_node: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // C++ 5147–5148: guarded by `getNominalIndividual() != nullptr` — an exact
        // no-op for concept-seeded nodes (the only kind the bridge pre-build
        // creates). FAIL-SAFE for nominal nodes, mirroring
        // `initialize_role_assertions`.
        let nominal_indi = calc_alg_context
            .process_context()
            .sat_node(*indi_proc_sat_node)
            .get_nominal_individual();
        let has_unmaterialized_data_assertions = nominal_indi.is_some()
            && nominal_indi.index()
                < calc_alg_context.ontology_arenas().individual_count() as usize
            && !calc_alg_context
                .ontology_arenas()
                .individual(nominal_indi)
                .get_assertion_data_linker()
                .is_empty();
        if has_unmaterialized_data_assertions {
            self.update_direct_adding_individual_status_flags(
                *indi_proc_sat_node,
                super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNPROCESSED
                    | super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                calc_alg_context,
            );
            self.set_insufficient_node_occured(calc_alg_context);
        }
    }

    /// Port of `createRoleAssertionLink` (.cpp 5024–5076).
    ///
    /// Walks the role's indirect super-role list; for each super-role:
    ///  - if it has a disjoint-role list, mark the source INSUFFICIENT + set the
    ///    insufficient-node-occured flag;
    ///  - add every domain/range concept (filtered) of the (negated^inversed) side to
    ///    the source node's label;
    ///  - on the inverse side (negated^inversed): build a `CBackwardSaturationPropagationLink`
    ///    and either queue it on the destination's initializing links (peer not yet
    ///    initialized) or install it immediately;
    ///  - on the forward side: `addNewLinkedExtensionProcessingRole`, and if the role's
    ///    process data wants propagation/creation concepts, mark UNMARKEDROLEASSERTION.
    /// If no inverse super-role connected the nodes, record a non-inverse-connected
    /// individual-node linker on the destination.
    ///
    /// W6-DEFER[api]: PORT-PENDING — needs model::Role `getIndirectSuperRoleList` /
    /// `getDisjointRoleList` / `getDomainRangeConceptList` / `getRoleData`, sat_node
    /// SAT-1 `isInitialized`/`getReapplyConceptSaturationLabelSet(true)`/
    /// `addInitializingBackwardPropagationLinks`/`addNonInverseConnectedIndividualNodeLinker`,
    /// the `CBackwardSaturationPropagationLink` + `CReapplyConceptSaturationLabelSet`
    /// satellites, and the sibling s-unit methods `addConceptFilteredToIndividual`,
    /// `updateDirectAddingIndividualStatusFlags`, `setInsufficientNodeOccured`,
    /// `installBackwardPropagationLink`, `addNewLinkedExtensionProcessingRole`. The
    /// super-role loop + `connected` flag are preserved in the C++ (see .cpp 5031–5075).
    pub fn create_role_assertion_link(
        &mut self,
        source_node: &mut SatNodeId,
        destination_node: &mut SatNodeId,
        role: RoleId,
        role_inversed: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if source_node.is_none()
            || destination_node.is_none()
            || role.is_none()
            || source_node.index() >= calc_alg_context.process_context().sat_node_count()
            || destination_node.index() >= calc_alg_context.process_context().sat_node_count()
            || role.index() >= calc_alg_context.ontology_arenas().role_count() as usize
        {
            return;
        }
        let destination_initialized = *destination_node == *source_node
            || calc_alg_context
                .process_context()
                .sat_node(*destination_node)
                .is_initialized();
        let super_roles = Self::saturation_indirect_super_roles(role, calc_alg_context);
        let mut connected = false;
        for super_role_link in super_roles {
            let super_role = super_role_link.target;
            let super_role_inversed = super_role_link.negated ^ role_inversed;
            let (has_disjoint_roles, domain_concepts, role_data_missing) = {
                let role_ref = calc_alg_context.ontology_arenas().role(super_role);
                (
                    !role_ref.disjoint_roles.is_empty(),
                    role_ref
                        .get_domain_range_concept_list(super_role_inversed)
                        .to_vec(),
                    role_ref.get_role_data().is_none(),
                )
            };
            if has_disjoint_roles {
                self.update_direct_adding_individual_status_flags(
                    *source_node,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                    calc_alg_context,
                );
                self.set_insufficient_node_occured(calc_alg_context);
            }
            for domain in domain_concepts {
                self.add_concept_filtered_to_individual_update_copy(
                    domain.target,
                    domain.negated,
                    source_node,
                    false,
                    calc_alg_context,
                );
            }

            if super_role_inversed {
                connected = true;
                let mut back_prop_link =
                    super::satellites::BackwardSaturationPropagationLink::new();
                back_prop_link.init_backward_propagation_link(*source_node, super_role);
                let back_prop_link = calc_alg_context
                    .process_context_mut()
                    .alloc_backward_sat_prop_link(back_prop_link);
                if !destination_initialized {
                    let old_head = calc_alg_context
                        .process_context()
                        .sat_node(*destination_node)
                        .get_initializing_backward_propagation_links();
                    calc_alg_context
                        .process_context_mut()
                        .backward_sat_prop_link_mut(back_prop_link)
                        .set_next(old_head);
                    calc_alg_context
                        .process_context_mut()
                        .sat_node_mut(*destination_node)
                        .set_initializing_backward_propagation_links(back_prop_link);
                } else {
                    self.install_backward_propagation_link(
                        *source_node,
                        *destination_node,
                        super_role,
                        back_prop_link,
                        true,
                        true,
                        calc_alg_context,
                    );
                }
            } else {
                self.add_new_linked_extension_processing_role(
                    super_role,
                    source_node,
                    true,
                    true,
                    calc_alg_context,
                );
                if role_data_missing {
                    self.update_direct_adding_individual_status_flags(
                        *source_node,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNMARKEDROLEASSERTION,
                        calc_alg_context,
                    );
                }
            }
        }
        if !connected {
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(*destination_node)
                .add_non_inverse_connected_individual_node_linker(*source_node);
        }
    }

    /// Port of `createSuccessorForDataLiteral` (.cpp 5174–5265).
    ///
    /// Allocates a fresh root saturation node (reference mode 4) for the data literal,
    /// queues it for processing + completion, records the data-value assertion, seeds
    /// its label with the base ⊤-data-range concept and the literal's datatype concept,
    /// preprocesses + associates the literal with the node, propagates status /
    /// successor-connected-nominal / max-cardinality candidates to the process node,
    /// then walks the role's indirect super-roles adding domain concepts to the source
    /// and range concepts to the data node, installing the backward-prop link on the
    /// inverse side (or `addNewLinkedExtensionProcessingRole` on the forward side), and
    /// records a non-inverse-connected linker when nothing connected on the inverse side.
    ///
    /// W6-DEFER[api]: PORT-PENDING — the full body (92 lines) allocates a
    /// `CIndividualSaturationProcessNode` (`ctx.process_context_mut().alloc_sat_node(…)`)
    /// + a `CIndividualSaturationProcessNodeLinker`, drives the databox queues
    /// (`getNextSaturationResolvedSuccessorExtensionIndividualNodeID`,
    /// `addIndividualSaturationProcessNodeLinker`, `getIndividualSaturationProcessNodeVector`),
    /// and calls the sibling s-unit methods `addConceptFilteredToIndividual`,
    /// `addIndividualToCompletionQueue`, `preprocessResolvedIndividualNode`,
    /// `associateDataLiteralWithNode`, `updateIndirect/DirectAddingIndividualStatusFlags`,
    /// `updateAddingSuccessorConnectedNominal`, `updateMaxCardinalityCandidates`,
    /// `setInsufficientNodeOccured`, `installBackwardPropagationLink`,
    /// `addNewLinkedExtensionProcessingRole`. All depend on SAT-1 + unported saturation
    /// satellites + model::Role/Datatype accessors; see .cpp 5174–5265 for the exact
    /// statement order.
    pub fn create_successor_for_data_literal(
        &mut self,
        process_indi: &mut SatNodeId,
        role: RoleId,
        data_literal: DataLiteralHandle,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = (&process_indi, role, data_literal, &calc_alg_context);
        // W6-DEFER[api]: PORT-PENDING — see the structured transcription above.
    }

    /// Port of `createSuccessorForConcept` (.cpp 6931–7100) — the SOME-rule successor
    /// creator (170 lines).
    ///
    /// Resolves the existential successor's pre-built saturation node from the concept's
    /// saturation reference linking (existential-successor link → per-operand link →
    /// base-⊤ fallback). Then, for the resolved `existIndiNode`:
    ///  - non-separated mode: enqueue it uninitialized;
    ///  - propagate indirect status / successor-connected nominals / max-cardinality
    ///    candidates from the existential node to the process node;
    ///  - cardinality > 1: if the existential node has an integrated nominal, mark the
    ///    process node CLASHED; else record a multiple-cardinality-ancestor linker;
    ///  - the remainder (.cpp 7028+) handles separated-mode completion, backward-prop
    ///    link installation, and the role-extension wiring for the new edge.
    ///
    /// W6-DEFER[api]: PORT-PENDING — needs model::Concept `getRole`/`getConceptData`/
    /// `getOperandList`, the `CSaturationConceptReferenceLinking` satellite chain, the
    /// `CConceptSaturationProcessLinker`/`CConceptSaturationDescriptor` accessors, SAT-1
    /// sat_node getters (`isSeparated`/`isInitialized`/`isCompleted`/`hasNominalIntegrated`/
    /// `addMultipleCardinalityAncestorNodesLinker`/the status + nominal + cardinality
    /// candidate getters), and the sibling s-unit methods
    /// `addUninitializedIndividualToProcessingQueue`, `updateIndirect/DirectAddingIndividualStatusFlags`,
    /// `updateAddingSuccessorConnectedNominal`, `updateMaxCardinalityCandidates`,
    /// `installBackwardPropagationLink`. The `existIndiNode` resolution cascade
    /// (existential-successor → operand → base-⊤) is preserved in the C++ (see
    /// .cpp 6939–7000); the KONCLUDE_ASSERT_X guards map to debug asserts.
    pub fn create_successor_for_concept(
        &mut self,
        process_indi: &mut SatNodeId,
        con_pro_linker: ConceptSaturationProcessLinkerId,
        cardinality: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.diagnostic_counters_enabled {
            self.diagnostic_successor_create_count += 1;
        }
        let con_des = calc_alg_context
            .process_context()
            .con_sat_proc_linker(con_pro_linker)
            .get_concept_saturation_descriptor();
        let con_negation = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_negation();
        let concept = calc_alg_context
            .process_context()
            .con_sat_desc(con_des)
            .get_concept();
        let role = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_role();

        // --- existIndiNode resolution cascade (cpp 6939–7005) ---
        // 1. the concept's existential-successor reference linking;
        let mut exist_indi_node =
            Self::s07_existential_successor_reference_node(concept, calc_alg_context);
        // 2. per-operand reference linking under (opNegated ^ conNegation);
        if exist_indi_node.is_none() {
            let operands: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            for op_link in operands {
                if exist_indi_node.is_some() {
                    break;
                }
                let op_con_negation = op_link.negated ^ con_negation;
                exist_indi_node = Self::s07_concept_reference_node(
                    op_link.target,
                    op_con_negation,
                    calc_alg_context,
                );
            }
        }
        // 3. base-⊤ fallback (data roles use the ⊤-data-range concept; the bridge
        //    routes data-range-free input, matched by the plain ⊤ read).
        if exist_indi_node.is_none() {
            let is_data_role = calc_alg_context.ontology_arenas().role(role).is_data_role();
            let base_top_concept = if !is_data_role {
                calc_alg_context.processing_data_box().ontology_top_concept
            } else {
                calc_alg_context
                    .processing_data_box()
                    .ontology_top_data_range_concept
            };
            exist_indi_node =
                Self::s07_concept_reference_node(base_top_concept, false, calc_alg_context);
        }

        // KONCLUDE_ASSERT_X(existIndiNode, "SOME saturation rule", …): a missing
        // reference node means the pre-build pass did not cover this filler.
        // FAIL-SAFE (never silently approximate): mark the node insufficiently
        // saturated so the verdict defers to the completion tableau.
        if exist_indi_node.is_none() {
            self.update_direct_adding_individual_status_flags(
                *process_indi,
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGUNPROCESSED
                    | IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                calc_alg_context,
            );
            self.set_insufficient_node_occured(calc_alg_context);
            return;
        }

        // --- cpp 7009–7099 ---
        let separated_mode = calc_alg_context
            .process_context()
            .sat_node(*process_indi)
            .is_separated()
            && !calc_alg_context
                .process_context()
                .sat_node(exist_indi_node)
                .is_separated(); // 7010
        if !separated_mode {
            let mut exist_node = exist_indi_node;
            self.add_uninitialized_individual_to_processing_queue(
                &mut exist_node,
                calc_alg_context,
            ); // 7012
        }

        let exist_indirect_flags = *calc_alg_context
            .process_context_mut()
            .sat_node_mut(exist_indi_node)
            .get_indirect_status_flags();
        self.update_indirect_adding_individual_status_flags(
            *process_indi,
            &exist_indirect_flags,
            calc_alg_context,
        ); // 7015
        let exist_nominal_set = calc_alg_context
            .process_context_mut()
            .sat_node_successor_connected_nominal_set(exist_indi_node, false);
        self.update_adding_successor_connected_nominal_set(
            *process_indi,
            exist_nominal_set,
            calc_alg_context,
        ); // 7016
        let (exist_atleast, exist_atmost) = {
            let exist_node = calc_alg_context.process_context().sat_node(exist_indi_node);
            (
                exist_node.get_max_atleast_cardinality_candidate(),
                exist_node.get_max_atmost_cardinality_candidate(),
            )
        };
        self.update_max_cardinality_candidates(
            *process_indi,
            exist_atleast,
            exist_atmost,
            calc_alg_context,
        ); // 7017

        if cardinality > 1 {
            if calc_alg_context
                .process_context()
                .sat_node(exist_indi_node)
                .has_nominal_integrated()
            {
                if super::sat_clash_trace_enabled() {
                    let indi = calc_alg_context
                        .process_context()
                        .sat_node(*process_indi)
                        .get_individual_id();
                    eprintln!(
                        "SAT-CLASH s02-nominal-card node={:?} indi={} exist_node={:?}",
                        process_indi, indi, exist_indi_node
                    );
                }
                self.update_direct_adding_individual_status_flags(
                    *process_indi,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                    calc_alg_context,
                ); // 7022
            } else {
                calc_alg_context
                    .process_context_mut()
                    .sat_node_mut(exist_indi_node)
                    .add_multiple_cardinality_ancestor_nodes_linker(*process_indi);
                // 7024–7026
            }
        }

        let exist_indi_initialized = calc_alg_context
            .process_context()
            .sat_node(exist_indi_node)
            .is_initialized(); // 7030
        let exist_indi_completed = calc_alg_context
            .process_context()
            .sat_node(exist_indi_node)
            .is_completed(); // 7031
        if separated_mode && !exist_indi_completed {
            self.update_direct_adding_individual_status_flags(
                *process_indi,
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                calc_alg_context,
            ); // 7033
            self.set_insufficient_node_occured(calc_alg_context); // 7034
        } else {
            let mut con_set = super::satellites::ReapplyConceptSaturationLabelSetId::NONE; // 7037
            let super_roles: Vec<NegLink<RoleId>> =
                Self::saturation_indirect_super_roles(role, calc_alg_context); // 7038 ([identity])
            let mut connected = false; // 7039
            for super_role_link in super_roles {
                let super_role = super_role_link.target;
                let super_role_inversed = super_role_link.negated;
                if !calc_alg_context
                    .ontology_arenas()
                    .role(super_role)
                    .disjoint_roles
                    .is_empty()
                {
                    self.update_direct_adding_individual_status_flags(
                        *process_indi,
                        IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                        calc_alg_context,
                    ); // 7043
                    self.set_insufficient_node_occured(calc_alg_context); // 7044
                }
                let domain_concepts: Vec<NegLink<ConceptId>> = calc_alg_context
                    .ontology_arenas()
                    .role(super_role)
                    .get_domain_range_concept_list(super_role_inversed)
                    .to_vec(); // 7046
                for domain_link in domain_concepts {
                    if con_set.is_none() {
                        con_set = calc_alg_context
                            .process_context_mut()
                            .sat_node_reapply_concept_saturation_label_set(*process_indi, true);
                        // 7051
                    }
                    self.add_concept_filtered_to_individual_label_set(
                        domain_link.target,
                        domain_link.negated,
                        process_indi,
                        con_set,
                        false,
                        calc_alg_context,
                    ); // 7053
                }

                if super_role_inversed {
                    connected = true; // 7058
                    if !separated_mode {
                        let mut back_prop_link =
                            super::satellites::BackwardSaturationPropagationLink::new();
                        back_prop_link.init_backward_propagation_link(*process_indi, super_role); // 7062
                        let back_prop_link = calc_alg_context
                            .process_context_mut()
                            .alloc_backward_sat_prop_link(back_prop_link);
                        if !exist_indi_initialized {
                            // existIndiNode->addInitializingBackwardPropagationLinks(backPropLink)
                            // — prepend onto the node's initializing-links chain. // 7064
                            let pc = calc_alg_context.process_context_mut();
                            let old_head = pc
                                .sat_node(exist_indi_node)
                                .get_initializing_backward_propagation_links();
                            pc.backward_sat_prop_link_mut(back_prop_link)
                                .set_next(old_head);
                            pc.sat_node_mut(exist_indi_node)
                                .set_initializing_backward_propagation_links(back_prop_link);
                        } else {
                            self.install_backward_propagation_link(
                                *process_indi,
                                exist_indi_node,
                                super_role,
                                back_prop_link,
                                true,
                                true,
                                calc_alg_context,
                            ); // 7066
                        }
                    } else {
                        // separated mode (cpp 7069–7086): replay the existing reapply
                        // descriptors of the (completed) successor node, and detect a
                        // critical predecessor role cardinality.
                        let back_prop_hash = calc_alg_context
                            .process_context()
                            .sat_node(exist_indi_node)
                            .role_back_prop_hash;
                        if back_prop_hash.is_some() {
                            let back_prop_reapply_des = calc_alg_context
                                .process_context()
                                .role_backward_sat_prop_hash(back_prop_hash)
                                .get_backward_propagation_backward_propagation_concept_descriptor(
                                    super_role,
                                );
                            if back_prop_reapply_des.is_some() {
                                self.apply_backward_propagation_concepts(
                                    *process_indi,
                                    back_prop_reapply_des,
                                    calc_alg_context,
                                ); // 7075
                            }
                        }
                        let critical_pred_role_card_hash = calc_alg_context
                            .process_context_mut()
                            .sat_node_ext_critical_predecessor_role_cardinality_hash(
                                exist_indi_node,
                                false,
                            );
                        if critical_pred_role_card_hash.is_some() {
                            let has_critical_data = calc_alg_context
                                .process_context_mut()
                                .critical_predecessor_role_cardinality_hash_data(
                                    critical_pred_role_card_hash,
                                    role,
                                    false,
                                )
                                .is_some();
                            if has_critical_data {
                                self.update_direct_adding_individual_status_flags(
                                    *process_indi,
                                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                                    calc_alg_context,
                                ); // 7082
                                self.set_insufficient_node_occured(calc_alg_context);
                                // 7083
                            }
                        }
                    }
                } else {
                    self.add_new_linked_extension_processing_role(
                        super_role,
                        process_indi,
                        true,
                        true,
                        calc_alg_context,
                    ); // 7089
                }
            }
            if !connected && !separated_mode {
                calc_alg_context
                    .process_context_mut()
                    .sat_node_mut(exist_indi_node)
                    .add_non_inverse_connected_individual_node_linker(*process_indi);
                // 7094–7096
            }
        }
    }

    /// Port of `initializeIndividualNodeByCoping` (.cpp 2022–2065).
    ///
    /// Copies a saturation node from a source node (flat-label-copy hint), sets
    /// reference mode 2 + the copy/reference back-pointers, propagates direct/indirect
    /// status + successor-connected nominals + max-cardinality candidates, clones every
    /// queued concept-saturation process linker, and — when the source's successor
    /// extension data has an initialized ALL- or FUNCTIONAL-concepts extension —
    /// re-queues the successor extension (and for FUNCTIONAL, clones its
    /// copying-initializing role linkers as functionality-added role linkers).
    ///
    /// ```text
    /// self.copied_indi_node_count += 1;                                        // present on self
    /// indiProcSatNode->initCopingIndividualSaturationProcessNode(copyFrom, tryFlatLabelCopy); // SAT-1
    /// indiProcSatNode->setReferenceMode(2);                                    // SAT-1 (exists)
    /// indiProcSatNode->setCopyIndividualNode(copyFrom);                        // SAT-1
    /// indiProcSatNode->setReferenceIndividualSaturationProcessNode(copyFrom);  // SAT-1
    /// self.update_direct_adding_individual_status_flags(node, copyFrom->getDirectStatusFlags(), ctx);
    /// self.update_indirect_adding_individual_status_flags(node, copyFrom->getIndirectStatusFlags(), ctx);
    /// self.update_adding_successor_connected_nominal(node, copyFrom->getSuccessorConnectedNominalSet(false), ctx);
    /// self.update_max_cardinality_candidates(node, copyFrom->getMaxAtleastCardinalityCandidate(),
    ///                                        copyFrom->getMaxAtmostCardinalityCandidate(), ctx);
    /// for conSatProLinkerIt in copyFrom->getConceptSaturationProcessLinker() {  // SAT-1
    ///   l = self.create_concept_saturation_process_linker(ctx);                // sibling (pool)
    ///   l->initLinker(conSatProLinkerIt->getConceptSaturationDescriptor());
    ///   node->addConceptSaturationProcessLinker(l);
    /// }
    /// copySuccExtensionData = copyFrom->getSuccessorExtensionData(false);      // satellite
    /// if (copySuccExtensionData) {
    ///   if (copyALL = copySuccExtensionData->getALLConceptsExtensionData(false); copyALL && copyALL->isSuccessorExtensionInitialized())
    ///     self.add_successor_extension_to_processing_queue(node, ctx);
    ///   if (copyFUNC = copySuccExtensionData->getFUNCTIONALConceptsExtensionData(false); copyFUNC && copyFUNC->isSuccessorExtensionInitialized()) {
    ///     funcExt = node->getSuccessorExtensionData(true)->getFUNCTIONALConceptsExtensionData(true);
    ///     self.add_successor_extension_to_processing_queue(node, ctx);
    ///     for roleLinkerIt in copyFUNC->getCopyingInitializingRoleProcessLinker() {
    ///       tmp = self.create_role_saturation_process_linker(ctx);             // sibling (pool)
    ///       tmp->initRoleProcessLinker(roleLinkerIt->getRole());
    ///       funcExt->addFunctionalityAddedRoleProcessLinker(tmp);
    ///     }
    ///   }
    /// }
    /// ```
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the header declares the first two params by
    /// value (`CIndividualSaturationProcessNode*`, NOT `*&`), so they port as
    /// `SatNodeId` by value.
    pub fn initialize_individual_node_by_coping(
        &mut self,
        indi_proc_sat_node: SatNodeId,
        copy_from_indi_proc_sat_node: SatNodeId,
        try_flat_label_copy: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.copied_indi_node_count += 1; // 2023
        calc_alg_context
            .process_context_mut()
            .sat_node_init_coping_individual_saturation_process_node(
                indi_proc_sat_node,
                copy_from_indi_proc_sat_node,
                try_flat_label_copy,
            ); // 2024
        if let Some(watched_tag) = super::sat_add_trace_tag() {
            let source_label = calc_alg_context
                .process_context()
                .sat_node(copy_from_indi_proc_sat_node)
                .reapply_con_sat_label_set;
            let mut descriptor = super::satellites::ConceptSaturationDescriptorId::NONE;
            let mut reapply =
                super::satellites::ImplicationReapplyConceptSaturationDescriptorId::NONE;
            let source_contains = source_label.is_some()
                && calc_alg_context
                    .process_context()
                    .reapply_con_sat_label_set(source_label)
                    .get_concept_descriptor_and_reapply_queue_by_tag(
                        watched_tag,
                        &mut descriptor,
                        &mut reapply,
                    )
                && descriptor.is_some();
            if source_contains {
                let node_tag = |node: SatNodeId, context: &CalculationAlgorithmContextBase| {
                    let reference = context
                        .process_context()
                        .sat_node(node)
                        .get_saturation_concept_reference_linking();
                    if reference.is_some() {
                        let concept = context
                            .process_context()
                            .extended_con_ref_linking_data(reference)
                            .get_saturation_concept();
                        context.ontology_arenas().concept(concept).get_concept_tag()
                    } else {
                        -1
                    }
                };
                eprintln!(
                    "SAT-COPY-TAG-TRACE watched-tag={} source-tag={} target-tag={}",
                    watched_tag,
                    node_tag(copy_from_indi_proc_sat_node, calc_alg_context),
                    node_tag(indi_proc_sat_node, calc_alg_context),
                );
            }
        }
        calc_alg_context
            .process_context_mut()
            .sat_node_mut(indi_proc_sat_node)
            .set_reference_mode(2); // 2025
        calc_alg_context
            .process_context_mut()
            .sat_node_mut(indi_proc_sat_node)
            .set_copy_individual_node(copy_from_indi_proc_sat_node); // 2026
        calc_alg_context
            .process_context_mut()
            .sat_node_mut(indi_proc_sat_node)
            .set_reference_individual_saturation_process_node(copy_from_indi_proc_sat_node); // 2027

        let copy_direct_flags = *calc_alg_context
            .process_context_mut()
            .sat_node_mut(copy_from_indi_proc_sat_node)
            .get_direct_status_flags();
        let copy_indirect_flags = *calc_alg_context
            .process_context_mut()
            .sat_node_mut(copy_from_indi_proc_sat_node)
            .get_indirect_status_flags();
        self.update_direct_adding_individual_status_flags_with_flags(
            indi_proc_sat_node,
            &copy_direct_flags,
            calc_alg_context,
        ); // 2029
        self.update_indirect_adding_individual_status_flags(
            indi_proc_sat_node,
            &copy_indirect_flags,
            calc_alg_context,
        ); // 2030
        let copy_nominal_set = calc_alg_context
            .process_context_mut()
            .sat_node_successor_connected_nominal_set(copy_from_indi_proc_sat_node, false);
        self.update_adding_successor_connected_nominal_set(
            indi_proc_sat_node,
            copy_nominal_set,
            calc_alg_context,
        ); // 2031
        let (copy_atleast, copy_atmost) = {
            let copy_node = calc_alg_context
                .process_context()
                .sat_node(copy_from_indi_proc_sat_node);
            (
                copy_node.get_max_atleast_cardinality_candidate(),
                copy_node.get_max_atmost_cardinality_candidate(),
            )
        };
        self.update_max_cardinality_candidates(
            indi_proc_sat_node,
            copy_atleast,
            copy_atmost,
            calc_alg_context,
        ); // 2032

        // Clone every queued concept-saturation process linker (2035–2039).
        let mut con_sat_pro_linker_it = calc_alg_context
            .process_context()
            .sat_node(copy_from_indi_proc_sat_node)
            .get_concept_saturation_process_linker();
        let copy_debug = super::sat_link_debug_tag().is_some_and(|target_tag| {
            let reference = calc_alg_context
                .process_context()
                .sat_node(indi_proc_sat_node)
                .get_saturation_concept_reference_linking();
            reference.is_some()
                && calc_alg_context
                    .ontology_arenas()
                    .concept(
                        calc_alg_context
                            .process_context()
                            .extended_con_ref_linking_data(reference)
                            .get_saturation_concept(),
                    )
                    .get_concept_tag()
                    == target_tag
        });
        if copy_debug {
            let mut queued = Vec::new();
            let mut linker = con_sat_pro_linker_it;
            while linker.is_some() {
                let descriptor = calc_alg_context
                    .process_context()
                    .con_sat_proc_linker(linker)
                    .get_concept_saturation_descriptor();
                let concept = calc_alg_context
                    .process_context()
                    .con_sat_desc(descriptor)
                    .get_concept();
                queued.push(
                    calc_alg_context
                        .ontology_arenas()
                        .concept(concept)
                        .get_concept_tag(),
                );
                linker = calc_alg_context
                    .process_context()
                    .con_sat_proc_linker(linker)
                    .get_next();
            }
            eprintln!(
                "SAT-COPY target={indi_proc_sat_node:?} source={copy_from_indi_proc_sat_node:?} queued={queued:?}"
            );
        }
        while con_sat_pro_linker_it.is_some() {
            let con_des = calc_alg_context
                .process_context()
                .con_sat_proc_linker(con_sat_pro_linker_it)
                .get_concept_saturation_descriptor();
            let new_linker_payload =
                self.create_concept_saturation_process_linker(calc_alg_context);
            let new_linker = ConceptSaturationProcessLinkerId::new(new_linker_payload.raw);
            calc_alg_context
                .process_context_mut()
                .con_sat_proc_linker_mut(new_linker)
                .init_concept_saturation_process_linker(con_des);
            calc_alg_context
                .process_context_mut()
                .sat_node_add_concept_saturation_process_linker(indi_proc_sat_node, new_linker);
            con_sat_pro_linker_it = calc_alg_context
                .process_context()
                .con_sat_proc_linker(con_sat_pro_linker_it)
                .get_next();
        }

        // Successor-extension re-queueing (2041–2064).
        let copy_succ_extension_data = calc_alg_context
            .process_context_mut()
            .sat_node_ext_successor_extension_data(copy_from_indi_proc_sat_node, false);
        if copy_succ_extension_data.is_some() {
            let copy_all_ext = calc_alg_context
                .process_context_mut()
                .sat_successor_extension_all_concepts_extension_data(
                    copy_succ_extension_data,
                    false,
                );
            if copy_all_ext.is_some()
                && calc_alg_context
                    .process_context()
                    .sat_indi_node_all_concept_ext_data(copy_all_ext)
                    .is_successor_extension_initialized()
            {
                let mut node = indi_proc_sat_node;
                self.add_successor_extension_to_processing_queue(&mut node, calc_alg_context);
            }
            let copy_functional_ext = calc_alg_context
                .process_context_mut()
                .sat_successor_extension_functional_concepts_extension_data(
                    copy_succ_extension_data,
                    false,
                );
            if copy_functional_ext.is_some()
                && calc_alg_context
                    .process_context()
                    .sat_indi_node_functional_concept_ext_data(copy_functional_ext)
                    .is_successor_extension_initialized()
            {
                let succ_ext_data = calc_alg_context
                    .process_context_mut()
                    .sat_node_ext_successor_extension_data(indi_proc_sat_node, true);
                let functional_concepts_extension = calc_alg_context
                    .process_context_mut()
                    .sat_successor_extension_functional_concepts_extension_data(
                        succ_ext_data,
                        true,
                    );
                let mut node = indi_proc_sat_node;
                self.add_successor_extension_to_processing_queue(&mut node, calc_alg_context);
                let mut role_linker_it = calc_alg_context
                    .process_context()
                    .sat_indi_node_functional_concept_ext_data(copy_functional_ext)
                    .copying_initializing_role_process_linker;
                while role_linker_it.is_some() {
                    let role = calc_alg_context
                        .process_context()
                        .role_sat_proc_linker(role_linker_it)
                        .get_role();
                    let tmp_role_linker_payload =
                        self.create_role_saturation_process_linker(calc_alg_context);
                    let tmp_role_linker = super::satellites::RoleSaturationProcessLinkerId::new(
                        tmp_role_linker_payload.raw,
                    );
                    calc_alg_context
                        .process_context_mut()
                        .role_sat_proc_linker_mut(tmp_role_linker)
                        .init_role_process_linker(role);
                    let old_head = calc_alg_context
                        .process_context()
                        .sat_indi_node_functional_concept_ext_data(functional_concepts_extension)
                        .functionality_added_role_process_linker;
                    calc_alg_context
                        .process_context_mut()
                        .role_sat_proc_linker_mut(tmp_role_linker)
                        .set_next(old_head);
                    calc_alg_context
                        .process_context_mut()
                        .sat_indi_node_functional_concept_ext_data_mut(
                            functional_concepts_extension,
                        )
                        .functionality_added_role_process_linker = tmp_role_linker;
                    role_linker_it = calc_alg_context
                        .process_context()
                        .role_sat_proc_linker(role_linker_it)
                        .get_next();
                }
            }
        }
    }

    /// Port of `getCorrectedNode` (.cpp 6461–6470).
    ///
    /// Looks up the (full, non-saturation) process node for `-individualID` in the
    /// node vector, chasing one merge-redirect if the node has been merged into
    /// another.
    ///
    /// ```text
    /// indiNode = nullptr;
    /// if (indiVec) {
    ///   indiNode = indiVec->getData(-individualID);                           // node vector (process::stubs)
    ///   if (indiNode && indiNode->getMergedIntoIndividualNodeID() != indiNode->getIndividualNodeID())
    ///     indiNode = indiVec->getData(indiNode->getMergedIntoIndividualNodeID());
    /// }
    /// return indiNode;
    /// ```
    ///
    /// KONCLUDE-PORT-NOTE[int-width]: the C++ index is `-individualID` (negated id);
    /// preserved literally in the eventual body.
    pub fn get_corrected_node(
        &mut self,
        individual_id: Cint64,
        indi_vec: Id<IndividualProcessNodeVector>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> NodeId {
        let _ = (individual_id, indi_vec, &calc_alg_context);
        // W6-DEFER[api]: `CIndividualProcessNodeVector::getData(-id)` is the
        // not-yet-ported node-vector accessor (process::stubs marker); the
        // merged-into redirect uses node.rs `getMergedIntoIndividualNodeID()` /
        // `getIndividualNodeID()`. C++ returns nullptr when the vector is absent.
        Id::NONE
    }
}
