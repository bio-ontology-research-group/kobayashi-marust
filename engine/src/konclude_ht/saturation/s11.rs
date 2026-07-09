//! `saturation::s11` — Label mutation + status-flag propagation + nominal/
//! cardinality candidate propagation + allocation-pool helpers + cache hand-off
//! (port unit #11 of 12).
//!
//! Faithful port of Konclude
//! `Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`
//! groups K + L + M + N (manifest `03-saturation-calc.md`, PU-SAT-11). Methods +
//! exact `.cpp` line ranges:
//!
//!   Group K — concept-add / label mutation:
//!     * `addConceptsFilteredToIndividual` (4 overloads, 7145 / 7155 / 7165 / 7175),
//!     * `addConceptFilteredToIndividual`  (3 overloads, 7186 / 7192 / 7200),
//!     * `addConceptToIndividual`          (7228),
//!     * `insertConceptToIndividualConceptSet` (7424),
//!     * `processModificationUpdateLinkers`    (7540),
//!     * `updateImplicationReapplyConceptSaturationDescriptor` (7552),
//!     * `hasConceptLocalImpact`           (7579).
//!   Group L — status-flag propagation + nominal / cardinality candidate tracking:
//!     * `addNominalDependentIndividualNode` (6431), `addInfluencedNominal` (6444),
//!     * `delayNominalSaturationConceptProcessing` (6674),
//!     * `propagateUnloadedABoxCompletionGraphDependentIndividualNodeFlag` (6849),
//!     * `updateDirectAddingIndividualStatusFlags` (7626 cint64 / 7653 flags*),
//!     * `updateDirectNotDependentAddingIndividualStatusFlags` (7633 / 7685),
//!     * `requiresDirectAddingIndividualStatusFlagsUpdate` (7640),
//!     * `requiresIndirectAddingIndividualStatusFlagsUpdate` (7647),
//!     * `updateIndirectAddingIndividualStatusFlags` (7721),
//!     * `requiresAddingSuccessorConnectedNominals` (7796),
//!     * `updateAddingSuccessorConnectedNominal` (7809 set / 7819 cint64),
//!     * `requiresMaxCardinalityCandidatePropagation` (7897),
//!     * `updateMaxCardinalityCandidates` (7907).
//!   Group M — allocation-pool helpers (object reuse):
//!     * create/release `ConceptSaturationDescriptor` (7291 / 7302),
//!       `ConceptSaturationProcessLinker` (7330 / 7308),
//!       `RoleSaturationProcessLinker` (7320 / 7314),
//!       `IndividualSaturationNodeLinker` (7348 / 7358),
//!       `IndividualSaturationSuccessorLinkDataLinker` (7368 / 7378),
//!       `IndividualSaturationUpdateLinker` (7392 / 7402),
//!     * `createModifiedProcessUpdateLinker` (7409),
//!     * `createImplicationReapplyConceptSaturationDescriptor` (7415).
//!   Group N — caching / consistency-model hand-off:
//!     * `tryAssociateIndividualNodesWithBackendCache` (615),
//!     * `loadConsistenceModelData` (6362), `loadConsistenceRepresentativeData` (6403),
//!     * `isConsistenceDataAvailable` (6421).
//!
//! KONCLUDE-PORT-NOTE[ownership]: each method is a member of
//! `CCalculationTableauApproximationSaturationTaskHandleAlgorithm`, so it becomes
//! `&mut self`. Per the confirmed context convention, the shared
//! `CCalculationAlgorithmContextBase*` is threaded explicitly as a trailing
//! `calc_alg_context: &mut CalculationAlgorithmContextBase`; sat nodes resolve via
//! `calc_alg_context.process_context().sat_node(id)` / `_mut`, concepts via
//! `calc_alg_context.ontology_arenas().concept(id)`, the databox via
//! `calc_alg_context.processing_data_box_mut()`. A C++ `CIndividualSaturationProcessNode*&`
//! in/out pointer becomes `&mut SatNodeId`; a by-value `CIndividualSaturationProcessNode*`
//! becomes `SatNodeId`. Sibling algorithm methods → `self.x(...)`.
//!
//! KONCLUDE-PORT-NOTE[overload]: Rust has no overloading; the C++ same-name
//! overloads are disambiguated by suffix — `add_concepts_filtered_to_individual`
//! vs `_update_copy`; `add_concept_filtered_to_individual` / `_update_copy` /
//! `_label_set`; `update_direct_adding_individual_status_flags` (cint64 entry) vs
//! `_with_flags`; same for `_not_dependent_`; and the four
//! `CSortedNegLinker`/`CXNegLinker`/`CXSortedNegLinker` concept-linker overloads of
//! `addConceptsFilteredToIndividual` collapse to ONE `&[NegLink<ConceptId>]` body
//! (their bodies are byte-identical once the linker type is erased).
//!
//! KONCLUDE-PORT-NOTE[ownership]: the intrusive status-update worklist
//! (`CIndividualSaturationProcessNodeStatusUpdateLinker` with
//! `initUpdateNodeLinker`/`append`/`getNext`/`getData`/`clearNext` + pool
//! create/release) collapses — exactly as `process/db5.rs` already collapsed the
//! databox `mRemSatUpdateLinker` chain to `Vec<SatNodeId>` — to a `Vec<SatNodeId>`
//! stack (the linker carries only the node it updates). `append` (prepend, LIFO)
//! → `insert(0, …)`, head-pop → `remove(0)`. The per-iteration pool create/release
//! of update-linkers is elided under this collapse (`[memory-pool]`); the
//! propagation logic itself is ported faithfully.
//!
//! Deferrals (no logic dropped; recorded inline + in doc):
//!   * `// W4-DEFER[api]` — the unported saturation satellites this group bottoms
//!     out in: `CConceptSetFlags`, the remaining label-set copy/flag helpers, the
//!     `CSaturationNominalDependentNodeHash` / `CSaturationInfluencedNominalSet`
//!     membership ops; plus the consistence model chain (`CConcreteOntology` /
//!     `CConsistence` / `CConsistenceTaskData` / `CSatisfiableCalculationTask`).
//!     `CSuccessorConnectedNominalSet` and the role-backward fan-out arms are live.
//!   * `// W4-DEFER[memory-pool]` — the fresh `CObjectAllocator<…>` allocation
//!     branch of every create-from-pool helper (no per-test arena for these linker
//!     payload kinds yet; the helpers take from the databox remaining-pool and
//!     defer the empty-pool fresh-alloc).
//!   * `// W6-DEFER[api]` — `mBackendAssCaceHandler` (backend-association cache).
//!   * debug `STATINC(...)` / `g_ksat_*` atomic counters (manifest group O) are
//!     statistics-only and elided.

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

use super::super::completion::context::CalculationAlgorithmContextBase;
use super::super::completion::stubs::SatisfiableCalculationTask;
use super::super::model::op::{
    CCALL, CCAND, CCAQALL, CCAQAND, CCAQCHOOCE, CCAQSOME, CCATOM, CCBRANCHALL, CCBRANCHAQALL,
    CCBRANCHAQAND, CCBRANCHTRIG, CCIMPL, CCIMPLALL, CCIMPLAQALL, CCIMPLAQAND, CCIMPLTRIG, CCOR,
    CCSOME, CCSUB,
};
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, NegLink};
use super::super::process::nominal_conn::SuccessorConnectedNominalSetId;
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::stubs::{
    ConceptSaturationDescriptor, ConceptSaturationProcess, ConceptSaturationProcessLinkerId,
    IndividualSaturationSuccessorLinkDataLinker, IndividualSaturationSuccessorLinkDataLinkerId,
    ReapplyConceptSaturationLabelSetId, RoleSaturationProcess, SaturationNominalConnectionType,
};
use super::super::process::SatNodeId;
// W4.5: the saturation-satellite linker structs (for the create*-pool allocations).
use super::satellites::{
    ConceptSaturationProcessLinker, ImplicationReapplyConceptSaturationDescriptor,
    ImplicationReapplyConceptSaturationDescriptorId, RoleSaturationProcessLinker,
    SaturationModificationProcessUpdateType, SaturationModifiedProcessUpdateLinker,
    SaturationModifiedProcessUpdateLinkerId,
};

// ===========================================================================
// CIndividualSaturationProcessNodeStatusFlags — the status-flag word.
//
// KONCLUDE-PORT-NOTE[api]: the struct + its `flags` field live in
// `process/sat_node.rs` (the SD-4 unit declared the placeholder). Per the port
// directive, the status-flag MASKS land here as pending associated consts, and
// the small bit-op method surface this status-flag unit needs is provided as an
// inherent impl (faithful to `CIndividualSaturationProcessNodeStatusFlags.{h,cpp}`).
// ===========================================================================
impl IndividualSaturationProcessNodeStatusFlags {
    // Status-flag masks (Konclude `CIndividualSaturationProcessNodeStatusFlags.h`
    // lines 121–140).
    pub const INDSATFLAGCLASHED: Cint64 = 0x0001;
    pub const INDSATFLAGCRITICAL: Cint64 = 0x0002;
    pub const INDSATFLAGINSUFFICIENT: Cint64 = 0x0004;
    pub const INDSATFLAGNOMINALCONNECTION: Cint64 = 0x0008;
    pub const INDSATFLAGEQCANDPROPLEMATIC: Cint64 = 0x0010;
    pub const INDSATFLAGCARDINALITYRESTRICTED: Cint64 = 0x0020;
    pub const INDSATFLAGCARDINALITYPROPLEMATIC: Cint64 = 0x0040;
    pub const INDMISSEDABOXCONSISTENCYDATA: Cint64 = 0x0080;
    pub const INDSUCCESSORNODEEXTENSIONS: Cint64 = 0x0100;
    pub const INDSATFLAGPROPAGATIONINCOMPLETE: Cint64 = 0x0200;
    pub const INDSATFLAGUNREGISTEREDPROPAGATION: Cint64 = 0x0400;
    pub const INDSATFLAGUNMARKEDROLEASSERTION: Cint64 = 0x0800;
    pub const INDSATFLAGINITIALIZED: Cint64 = 0x1000;
    pub const INDSATFLAGCOMPLETED: Cint64 = 0x2000;
    pub const INDSATFLAGUNPROCESSED: Cint64 = 0x4000;

    /// Port of `initStatusFlags` (cpp 37–40).
    pub fn init_status_flags(&mut self) -> &mut Self {
        self.flags = 0;
        self
    }

    /// Port of `hasFlags(cint64,bool)` (cpp 193–202).
    pub fn has_flags_code(&self, flags: Cint64, check_all_flags: bool) -> bool {
        if flags == 0 {
            return true;
        }
        if check_all_flags {
            (!self.flags & flags) == 0
        } else {
            (self.flags & flags) != 0
        }
    }

    /// Port of `hasFlags(CIndividualSaturationProcessNodeStatusFlags*,bool)` (cpp 205–207).
    pub fn has_flags(
        &self,
        flags: &IndividualSaturationProcessNodeStatusFlags,
        check_all_flags: bool,
    ) -> bool {
        self.has_flags_code(flags.get_flags(), check_all_flags)
    }

    /// Port of `setFlags(cint64,bool)` (cpp 210–217).
    pub fn set_flags(&mut self, flags: Cint64, value: bool) -> &mut Self {
        if value {
            self.flags |= flags;
        } else {
            self.flags &= !flags;
        }
        self
    }

    /// Port of `addFlags(cint64)` (cpp 224–227).
    pub fn add_flags_code(&mut self, flags: Cint64) -> &mut Self {
        self.flags |= flags;
        self
    }

    /// Port of `addFlags(CIndividualSaturationProcessNodeStatusFlags*)` (cpp 219–222).
    pub fn add_flags(&mut self, flags: &IndividualSaturationProcessNodeStatusFlags) -> &mut Self {
        self.add_flags_code(flags.get_flags());
        self
    }

    /// Port of `clearFlags(cint64)` (cpp 229–232).
    pub fn clear_flags(&mut self, flags: Cint64) -> &mut Self {
        self.flags &= !flags;
        self
    }

    /// Port of `getFlags` (cpp 235–237).
    pub fn get_flags(&self) -> Cint64 {
        self.flags
    }

    /// Port of `hasClashedFlag` (cpp 42–44).
    pub fn has_clashed_flag(&self) -> bool {
        self.has_flags_code(Self::INDSATFLAGCLASHED, false)
    }
    /// Port of `hasInsufficientFlag` (cpp 51–53).
    pub fn has_insufficient_flag(&self) -> bool {
        self.has_flags_code(Self::INDSATFLAGINSUFFICIENT, false)
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::model::concept::Concept;
    use super::super::super::model::op::CCATOM;
    use super::super::super::model::RoleId;
    use super::super::super::process::sat_node::IndividualSaturationProcessNode;
    use super::super::super::saturation::satellites::{
        ConceptSaturationDescriptorId, ConceptSaturationDescriptorReapplyData,
        ImplicationReapplyConceptSaturationDescriptor,
        ImplicationReapplyConceptSaturationDescriptorId,
    };
    use super::super::algorithm::SaturationTaskHandleAlgorithm;
    use super::*;

    #[test]
    fn add_influenced_nominal_records_first_influence_once() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        algo.add_influenced_nominal(41, &mut ctx);
        let set = ctx.saturation_influenced_nominal_set(false);
        assert!(ctx
            .process_context()
            .sat_influenced_nominal_set(set)
            .is_nominal_influenced(41));

        assert!(!ctx
            .process_context_mut()
            .sat_influenced_nominal_set_mut(set)
            .set_nominal_influenced(41));
    }

    #[test]
    fn nominal_dependent_node_is_marked_insufficient_when_nominal_already_influenced() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let dependent = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(7));

        algo.add_influenced_nominal(11, &mut ctx);
        algo.add_nominal_dependent_individual_node(11, dependent, 0, &mut ctx);

        assert!(ctx
            .process_context()
            .sat_node(dependent)
            .direct_status_flags
            .has_insufficient_flag());
        assert!(ctx.processing_data_box().is_insufficient_node_occured());
    }

    #[test]
    fn influenced_nominal_marks_previously_registered_dependent_nodes() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();
        let first = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(3));
        let second = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(4));

        algo.add_nominal_dependent_individual_node(17, first, 1, &mut ctx);
        algo.add_nominal_dependent_individual_node(17, second, 2, &mut ctx);
        assert!(!ctx
            .process_context()
            .sat_node(first)
            .direct_status_flags
            .has_insufficient_flag());
        assert!(!ctx
            .process_context()
            .sat_node(second)
            .direct_status_flags
            .has_insufficient_flag());

        algo.add_influenced_nominal(17, &mut ctx);

        assert!(ctx
            .process_context()
            .sat_node(first)
            .direct_status_flags
            .has_insufficient_flag());
        assert!(ctx
            .process_context()
            .sat_node(second)
            .direct_status_flags
            .has_insufficient_flag());
        assert!(ctx.processing_data_box().is_insufficient_node_occured());
    }

    #[test]
    fn successor_link_data_linker_create_release_reuses_intrusive_free_list() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let first = algo.create_individual_saturation_successor_link_data_linker(&mut ctx);
        assert!(first.is_some());
        assert_eq!(
            ctx.process_context().indi_sat_succ_link_data_linker_count(),
            1
        );

        let succ_data = ctx
            .process_context_mut()
            .alloc_sat_succ_data(Default::default());
        ctx.process_context_mut()
            .indi_sat_succ_link_data_linker_mut(first)
            .init_successor_link_data_linker(succ_data)
            .set_next(first);

        algo.release_individual_saturation_successor_link_data_linker(first, &mut ctx);
        assert_eq!(
            ctx.processing_data_box()
                .remaining_individual_successor_link_data_linker(),
            first
        );
        assert_eq!(
            ctx.process_context()
                .indi_sat_succ_link_data_linker(first)
                .get_next(),
            Id::NONE
        );

        let reused = algo.create_individual_saturation_successor_link_data_linker(&mut ctx);
        assert_eq!(reused, first);
        assert!(ctx
            .processing_data_box()
            .remaining_individual_successor_link_data_linker()
            .is_none());
    }

    #[test]
    fn s11_implication_reapply_insert_triggered_prepends_chain_once_per_tag() {
        let mut ctx = CalculationAlgorithmContextBase::new();

        let trigger = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(211);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let direct_descriptor = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(trigger, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };
        let label_set = ctx.process_context_mut().alloc_reapply_con_sat_label_set(
            super::super::satellites::ReapplyConceptSaturationLabelSet::new(INVALID),
        );
        let trigger_tag = ctx.ontology_arenas().concept(trigger).get_concept_tag();
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(label_set)
            .concept_des_dep_hash
            .insert(
                trigger_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: direct_descriptor,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );

        let first = ctx
            .process_context_mut()
            .alloc_imp_reapply_con_sat_desc(ImplicationReapplyConceptSaturationDescriptor::new());
        let second = ctx
            .process_context_mut()
            .alloc_imp_reapply_con_sat_desc(ImplicationReapplyConceptSaturationDescriptor::new());
        let mut out_descriptor = ConceptSaturationDescriptorId::NONE;

        assert!(ctx
            .process_context_mut()
            .reapply_con_sat_label_set_insert_concept_reapplication_return_triggered(
                label_set,
                trigger_tag,
                first,
                Some(&mut out_descriptor),
            ));
        assert_eq!(out_descriptor, direct_descriptor);
        assert_eq!(
            ctx.process_context()
                .reapply_con_sat_label_set(label_set)
                .get_total_count(),
            1
        );

        assert!(ctx
            .process_context_mut()
            .reapply_con_sat_label_set_insert_concept_reapplication_return_triggered(
                label_set,
                trigger_tag,
                second,
                None,
            ));
        let head = ctx
            .process_context()
            .reapply_con_sat_label_set(label_set)
            .concept_des_dep_hash
            .get(&trigger_tag)
            .unwrap()
            .imp_reapply_con_sat_des;
        assert_eq!(head, second);
        assert_eq!(
            ctx.process_context()
                .imp_reapply_con_sat_desc(second)
                .get_next(),
            first
        );
        assert_eq!(
            ctx.process_context()
                .reapply_con_sat_label_set(label_set)
                .get_total_count(),
            1
        );
    }

    #[test]
    fn s11_update_implication_reapply_advances_trigger_and_executes_final_operand() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let conclusion = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(221);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let first_trigger = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(223);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let second_trigger = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(225);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let implication = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCATOM)
                .set_concept_tag(227)
                .add_operand_linker(conclusion, false)
                .add_operand_linker(second_trigger, false)
                .set_operand_count(2);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(root, true);
        let second_trigger_descriptor = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(second_trigger, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };
        let second_trigger_tag = ctx
            .ontology_arenas()
            .concept(second_trigger)
            .get_concept_tag();
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(label_set)
            .concept_des_dep_hash
            .insert(
                second_trigger_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: second_trigger_descriptor,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );

        let initial_reapply = {
            let triggers = [
                NegLink {
                    target: first_trigger,
                    negated: false,
                },
                NegLink {
                    target: second_trigger,
                    negated: false,
                },
            ];
            let mut descriptor = ImplicationReapplyConceptSaturationDescriptor::new();
            descriptor.init_implication_reaplly_concept_saturation_descriptor(
                implication,
                Some(&triggers),
            );
            ctx.process_context_mut()
                .alloc_imp_reapply_con_sat_desc(descriptor)
        };
        let before_count = ctx.process_context().con_sat_desc_count();
        let mut root_ref = root;

        assert!(
            algo.update_implication_reapply_concept_saturation_descriptor(
                initial_reapply,
                &mut root_ref,
                label_set,
                &mut ctx,
            )
        );

        let queued = ctx
            .process_context()
            .reapply_con_sat_label_set(label_set)
            .concept_des_dep_hash
            .get(&second_trigger_tag)
            .unwrap()
            .imp_reapply_con_sat_des;
        assert!(queued.is_some());
        assert_eq!(
            ctx.process_context()
                .imp_reapply_con_sat_desc(queued)
                .get_next_trigger_concept()
                .unwrap()[0]
                .target,
            second_trigger
        );
        assert_eq!(ctx.process_context().con_sat_desc_count(), before_count + 1);
    }

    #[test]
    fn s11_insert_concept_replays_matching_implication_reapply_chain() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let conclusion = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(231);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let trigger = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(233);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let implication = {
            let mut concept = Concept::new();
            concept
                .set_operator_code(CCATOM)
                .set_concept_tag(235)
                .add_operand_linker(conclusion, false)
                .set_operand_count(1);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };

        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(root, true);
        let trigger_tag = ctx.ontology_arenas().concept(trigger).get_concept_tag();
        let queued_reapply = {
            let triggers = [NegLink {
                target: trigger,
                negated: true,
            }];
            let mut descriptor = ImplicationReapplyConceptSaturationDescriptor::new();
            descriptor.init_implication_reaplly_concept_saturation_descriptor(
                implication,
                Some(&triggers),
            );
            ctx.process_context_mut()
                .alloc_imp_reapply_con_sat_desc(descriptor)
        };
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(label_set)
            .concept_des_dep_hash
            .insert(
                trigger_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: ConceptSaturationDescriptorId::NONE,
                    imp_reapply_con_sat_des: queued_reapply,
                },
            );
        let trigger_descriptor = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(trigger, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };

        let mut root_ref = root;
        assert!(!algo.insert_concept_to_individual_concept_set(
            trigger_descriptor,
            &mut root_ref,
            label_set,
            &mut ctx,
        ));

        let conclusion_tag = ctx.ontology_arenas().concept(conclusion).get_concept_tag();
        let mut conclusion_descriptor = ConceptSaturationDescriptorId::NONE;
        let mut imp_reapply = ImplicationReapplyConceptSaturationDescriptorId::NONE;
        assert!(ctx
            .process_context()
            .reapply_con_sat_label_set(label_set)
            .get_concept_saturation_descriptor_by_tag(
                conclusion_tag,
                &mut conclusion_descriptor,
                &mut imp_reapply,
            ));
        assert!(conclusion_descriptor.is_some());
    }

    #[test]
    fn s11_insert_concept_detects_opposite_polarity_clash() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let concept = {
            let mut concept = Concept::new();
            concept.set_operator_code(CCATOM).set_concept_tag(241);
            ctx.ontology_arenas_mut().alloc_concept(concept)
        };
        let root = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(root, true);
        let positive_descriptor = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(concept, false);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };
        let concept_tag = ctx.ontology_arenas().concept(concept).get_concept_tag();
        ctx.process_context_mut()
            .reapply_con_sat_label_set_mut(label_set)
            .concept_des_dep_hash
            .insert(
                concept_tag,
                ConceptSaturationDescriptorReapplyData {
                    con_sat_des: positive_descriptor,
                    imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId::NONE,
                },
            );
        let negative_descriptor = {
            let mut descriptor = ConceptSaturationDescriptor::new();
            descriptor.init_concept_saturation_descriptor(concept, true);
            ctx.process_context_mut().alloc_con_sat_desc(descriptor)
        };

        let mut root_ref = root;
        assert!(algo.insert_concept_to_individual_concept_set(
            negative_descriptor,
            &mut root_ref,
            label_set,
            &mut ctx,
        ));
        assert!(ctx
            .process_context()
            .sat_node(root)
            .direct_status_flags
            .has_clashed_flag());
        assert_eq!(
            ctx.process_context()
                .sat_node(root)
                .get_clashed_concept_saturation_descriptor_linker(),
            negative_descriptor
        );
    }

    #[test]
    fn s11_modified_update_linkers_prepend_on_label_set() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(node, true);

        let first = algo.create_modified_process_update_linker(&mut ctx);
        ctx.process_context_mut()
            .sat_modified_process_update_linker_mut(first)
            .init_process_update_linker(
                node,
                SaturationModificationProcessUpdateType::UpdateDisjunctCommonConceptExtraction,
            );
        ctx.process_context_mut()
            .reapply_con_sat_label_set_add_modified_update_linker(label_set, first);

        let second = algo.create_modified_process_update_linker(&mut ctx);
        ctx.process_context_mut()
            .sat_modified_process_update_linker_mut(second)
            .init_process_update_linker(
                node,
                SaturationModificationProcessUpdateType::UpdateDisjunctCommonConceptExtraction,
            );
        ctx.process_context_mut()
            .reapply_con_sat_label_set_add_modified_update_linker(label_set, second);

        let head = ctx
            .process_context()
            .reapply_con_sat_label_set(label_set)
            .get_modified_update_linker();
        assert_eq!(head, second);
        assert_eq!(
            ctx.process_context()
                .sat_modified_process_update_linker(head)
                .get_next(),
            first
        );
    }

    #[test]
    fn s11_process_modified_update_linker_enqueues_disjunct_extraction_once() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let label_set = ctx
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(node, true);
        let extraction_data = ctx
            .process_context_mut()
            .sat_node_ext_disjunct_common_concept_extraction_data(node, true);
        let continuation = ctx
            .process_context()
            .sat_disjunct_common_concept_extraction_data(extraction_data)
            .get_extraction_continue_process_linker();

        let update = algo.create_modified_process_update_linker(&mut ctx);
        ctx.process_context_mut()
            .sat_modified_process_update_linker_mut(update)
            .init_process_update_linker(
                node,
                SaturationModificationProcessUpdateType::UpdateDisjunctCommonConceptExtraction,
            );

        let mut root_ref = node;
        algo.process_modification_update_linkers(&mut root_ref, label_set, update, &mut ctx);
        assert_eq!(
            ctx.processing_data_box()
                .individual_disjunct_common_concept_extract_process_linker(),
            &[continuation]
        );
        assert!(ctx
            .process_context()
            .indi_sat_process_node_linker(continuation)
            .is_processing_queued());

        algo.process_modification_update_linkers(&mut root_ref, label_set, update, &mut ctx);
        assert_eq!(
            ctx.processing_data_box()
                .individual_disjunct_common_concept_extract_process_linker(),
            &[continuation]
        );
    }

    #[test]
    fn s11_direct_not_dependent_status_flags_fan_out_to_backward_sources() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let target = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_add_backward_propagation_link(target, RoleId::new(701), source);

        algo.update_direct_not_dependent_adding_individual_status_flags(
            target,
            IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
            &mut ctx,
        );

        assert!(ctx
            .process_context()
            .sat_node(target)
            .direct_status_flags
            .has_insufficient_flag());
        assert!(ctx
            .process_context()
            .sat_node(target)
            .indirect_status_flags
            .has_insufficient_flag());
        assert!(!ctx
            .process_context()
            .sat_node(source)
            .direct_status_flags
            .has_insufficient_flag());
        assert!(ctx
            .process_context()
            .sat_node(source)
            .indirect_status_flags
            .has_insufficient_flag());
    }

    #[test]
    fn s11_indirect_status_flags_fan_out_to_backward_sources() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let target = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_add_backward_propagation_link(target, RoleId::new(703), source);
        let mut flags = IndividualSaturationProcessNodeStatusFlags::default();
        flags.init_status_flags();
        flags.add_flags_code(IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCRITICAL);

        algo.update_indirect_adding_individual_status_flags(target, &flags, &mut ctx);

        assert!(ctx
            .process_context()
            .sat_node(target)
            .indirect_status_flags
            .has_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCRITICAL,
                true
            ));
        assert!(ctx
            .process_context()
            .sat_node(source)
            .indirect_status_flags
            .has_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCRITICAL,
                true
            ));
        assert!(!ctx
            .process_context()
            .sat_node(source)
            .direct_status_flags
            .has_flags_code(
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCRITICAL,
                true
            ));
    }

    #[test]
    fn s11_successor_connected_nominal_fan_out_to_backward_sources_once() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let target = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_add_backward_propagation_link(target, RoleId::new(719), source);

        algo.update_adding_successor_connected_nominal(target, 1101, &mut ctx);

        assert!(ctx
            .process_context_mut()
            .sat_node_has_successor_connected_nominal(target, 1101));
        assert!(ctx
            .process_context_mut()
            .sat_node_has_successor_connected_nominal(source, 1101));
        assert_eq!(algo.successor_connected_nominal_updated_count, 2);

        algo.update_adding_successor_connected_nominal(target, 1101, &mut ctx);
        assert_eq!(
            algo.successor_connected_nominal_updated_count, 2,
            "membership must stop duplicate successor-connected nominal propagation"
        );
    }

    #[test]
    fn s11_successor_connected_nominal_abox_gate_skips_source_fan_out() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let target = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let copy_dep = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let backward_source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let non_inverse_source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_mut(target)
            .abox_individual_representation_node = true;
        ctx.process_context_mut()
            .sat_node_mut(target)
            .depending_indi_node_linker
            .push(NegLink {
                target: copy_dep,
                negated: false,
            });
        ctx.process_context_mut()
            .sat_node_add_backward_propagation_link(target, RoleId::new(727), backward_source);
        ctx.process_context_mut()
            .sat_node_mut(target)
            .non_inverse_connected_indi_node_linker
            .push(non_inverse_source);

        algo.update_adding_successor_connected_nominal(target, 1103, &mut ctx);

        assert!(ctx
            .process_context_mut()
            .sat_node_has_successor_connected_nominal(target, 1103));
        assert!(ctx
            .process_context_mut()
            .sat_node_has_successor_connected_nominal(copy_dep, 1103));
        assert!(!ctx
            .process_context_mut()
            .sat_node_has_successor_connected_nominal(backward_source, 1103));
        assert!(!ctx
            .process_context_mut()
            .sat_node_has_successor_connected_nominal(non_inverse_source, 1103));
        assert_eq!(algo.successor_connected_nominal_updated_count, 2);
    }

    #[test]
    fn s11_max_cardinality_candidates_fan_out_to_backward_sources() {
        let mut algo = SaturationTaskHandleAlgorithm::new();
        let mut ctx = CalculationAlgorithmContextBase::new();

        let target = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        let source = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::default());
        ctx.process_context_mut()
            .sat_node_add_backward_propagation_link(target, RoleId::new(709), source);

        algo.update_max_cardinality_candidates(target, 4, 7, &mut ctx);

        assert_eq!(
            ctx.process_context()
                .sat_node(target)
                .get_max_atleast_cardinality_candidate(),
            4
        );
        assert_eq!(
            ctx.process_context()
                .sat_node(target)
                .get_max_atmost_cardinality_candidate(),
            7
        );
        assert_eq!(
            ctx.process_context()
                .sat_node(source)
                .get_max_atleast_cardinality_candidate(),
            4
        );
        assert_eq!(
            ctx.process_context()
                .sat_node(source)
                .get_max_atmost_cardinality_candidate(),
            7
        );
    }
}

impl super::algorithm::SaturationTaskHandleAlgorithm {
    // =======================================================================
    // Group N — caching / consistency-model hand-off.
    // =======================================================================

    /// Port of `tryAssociateIndividualNodesWithBackendCache` (cpp 615–629).
    ///
    /// PORT-PENDING — faithful structure recorded below. Bottoms out in the
    /// unported `CSatisfiableCalculationTask` (the task's processing databox +
    /// the saturation-individuals-analysation observer + the representative
    /// backend-cache updating adapter) and the `mBackendAssCaceHandler`
    /// (`W6-DEFER[api]`). The only locally-resolvable read is
    /// `satIndiNode->getIndirectStatusFlags()->hasClashedFlag()` (the node's
    /// by-value `indirect_status_flags.has_clashed_flag()`), reachable once the
    /// task hands over its analysation node linker.
    ///
    /// C++ structure:
    /// ```text
    /// procDataBox = statCalcTask->getProcessingDataBox()
    /// indiSaturationAnalysingNodeLinker = procDataBox->getIndividualSaturationAnalysationNodeLinker()
    /// if indiSaturationAnalysingNodeLinker
    ///    && calcAlgContext->getSatisfiableCalculationTask()->getSaturationIndividualsAnalysationObserver():
    ///     for satIndiNode in indiSaturationAnalysingNodeLinker:
    ///         satIndiNode->setOccurrenceStatisticsCollectingRequired(true)
    ///         if satIndiNode->getIndirectStatusFlags()->hasClashedFlag():
    ///             return
    ///     mBackendAssCaceHandler->tryAssociateNodesWithBackendCache(
    ///         indiSaturationAnalysingNodeLinker,
    ///         calcAlgContext->getSatisfiableCalculationTask()
    ///             ->getSatisfiableRepresentativeBackendCacheUpdatingAdapter(),
    ///         calcAlgContext)
    /// ```
    pub fn try_associate_individual_nodes_with_backend_cache(
        &mut self,
        stat_calc_task: Id<SatisfiableCalculationTask>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: statCalcTask->getProcessingDataBox()->getIndividualSaturationAnalysationNodeLinker()
        //   + getSatisfiableCalculationTask()->getSaturationIndividualsAnalysationObserver();
        //   the node loop sets setOccurrenceStatisticsCollectingRequired(true) and
        //   early-returns on the first node whose indirect_status_flags.has_clashed_flag().
        // W6-DEFER[api]: mBackendAssCaceHandler->tryAssociateNodesWithBackendCache(...).
        let _ = (stat_calc_task, &mut *calc_alg_context);
    }

    /// Port of `loadConsistenceModelData` (cpp 6362–6398).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the C++ takes `CCalculationAlgorithmContext*`; the
    /// port threads the shared `CalculationAlgorithmContextBase` per the context
    /// convention. The flag bookkeeping on `self` is ported real; the consistence
    /// model resolution (`getOntology()->getConsistence()->getConsistenceModelData()`
    /// → `dynamic_cast<CConsistenceTaskData>` → det/non-det cached satisfiable
    /// tasks) is `W4-DEFER[api]`.
    pub fn load_consistence_model_data(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut cons_comp_graph_available = false;
        if !self.cached_completion_graph_loaded {
            // W4-DEFER[api]: processingDataBox->getOntology()->getConsistence()
            //   ->getConsistenceModelData(); dynamic_cast<CConsistenceTaskData>; on a
            //   deterministic satisfiable task set mDetCachedCGIndiVector =
            //   detSatCalcTask->getProcessingDataBox()->getIndividualProcessNodeVector()
            //   and mDetConsistencyCG = true (else false); likewise the
            //   completion-graph-cached task → mNonDetCachedCGIndiVector /
            //   mNonDetConsistencyCG. CConcreteOntology / CConsistence /
            //   CConsistenceData / CConsistenceTaskData / CSatisfiableCalculationTask
            //   are unported; the det/non-det flags stay at their default `false`.
            self.cached_completion_graph_loaded = true;
        }
        if self.det_consistency_cg {
            cons_comp_graph_available = true;
        } else {
            self.cached_completion_graph_missing = true;
        }
        cons_comp_graph_available
    }

    /// Port of `loadConsistenceRepresentativeData` (cpp 6403–6417).
    pub fn load_consistence_representative_data(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if !self.representative_data_loaded {
            self.representative_data_available = false;
            // W4-DEFER[api]: mRepresentativeDataAvailable =
            //   processingDataBox->getOntology()->getConsistence()->areIndividualsRepresentativelyStored();
            //   CConsistence unported, so the availability stays `false`.
            self.representative_data_loaded = true;
        }
        self.representative_data_available
    }

    /// Port of `isConsistenceDataAvailable` (cpp 6421–6426).
    pub fn is_consistence_data_available(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        if self.load_consistence_model_data(calc_alg_context)
            || self.load_consistence_representative_data(calc_alg_context)
        {
            return true;
        }
        false
    }

    // =======================================================================
    // Group M — allocation-pool helpers (object reuse).
    //
    // KONCLUDE-PORT-NOTE[memory-pool]: each `create*` takes from the databox
    // "remaining" pool (`process/db5.rs` / `db6.rs`); the empty-pool branch
    // `CObjectAllocator<…>::allocateAndConstruct(taskMemMan)` has no per-test arena
    // for these linker payload kinds yet and is `W4-DEFER[memory-pool]` (the
    // helper returns the taken id, `Id::NONE`/`SatNodeId::NONE`/`INVALID` when the
    // pool is empty). `release*` clears the linker's `next` (satellite, deferred)
    // and returns it to the pool.
    // =======================================================================

    /// Port of `createConceptSaturationDescriptor` (cpp 7291–7299).
    pub fn create_concept_saturation_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Id<ConceptSaturationDescriptor> {
        let mut con_sat_des = calc_alg_context
            .processing_data_box_mut()
            .take_remaining_concept_saturation_descriptor();
        if con_sat_des.is_none() {
            // W4.5: conSatDes = CObjectAllocator<CConceptSaturationDescriptor>
            //   ::allocateAndConstruct(taskMemMan) — pool-allocate from the per-test arena.
            con_sat_des = calc_alg_context
                .process_context_mut()
                .alloc_con_sat_desc(ConceptSaturationDescriptor::new());
        }
        con_sat_des
    }

    /// Port of `releaseConceptSaturationDescriptor` (cpp 7302–7306).
    pub fn release_concept_saturation_descriptor(
        &mut self,
        con_sat_des: Id<ConceptSaturationDescriptor>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // conSatDes->clearNext() — a pooled descriptor keeping its stale next
        // re-enters chains as a CYCLE (see init_concept_saturation_process_linker).
        calc_alg_context
            .process_context_mut()
            .con_sat_desc_mut(con_sat_des)
            .set_next(Id::NONE);
        calc_alg_context
            .processing_data_box_mut()
            .add_remaining_concept_saturation_descriptor(con_sat_des);
    }

    /// Port of `releaseConceptSaturationProcessLinker` (cpp 7308–7312).
    pub fn release_concept_saturation_process_linker(
        &mut self,
        con_sat_proc_linker: ConceptSaturationProcessLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // conSatProcLinker->clearNext() — stale next on a pooled linker cycles
        // the node process-linker chain (gdb-proven infinite append walk).
        calc_alg_context
            .process_context_mut()
            .con_sat_proc_linker_mut(Id::new(con_sat_proc_linker.raw))
            .set_next(Id::NONE);
        // W4-RECONCILE[api]: the databox remaining-list is keyed by the linker
        // *payload* marker (`ConceptSaturationProcess`); the saturation layer threads
        // the linker id (`ConceptSaturationProcessLinkerId`). Same arena index, distinct
        // marker — convert via the raw index (faithful to the C++ payload/linker split).
        calc_alg_context
            .processing_data_box_mut()
            .add_remaining_concept_saturation_process_linker(Id::new(con_sat_proc_linker.raw));
    }

    /// Port of `releaseRoleSaturationProcessLinker` (cpp 7314–7318).
    pub fn release_role_saturation_process_linker(
        &mut self,
        role_sat_proc_linker: Id<RoleSaturationProcess>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // roleSatProcLinker->clearNext() — same stale-next pooling hazard.
        calc_alg_context
            .process_context_mut()
            .role_sat_proc_linker_mut(Id::new(role_sat_proc_linker.raw))
            .set_next(Id::NONE);
        calc_alg_context
            .processing_data_box_mut()
            .add_remaining_role_saturation_process_linker(role_sat_proc_linker);
    }

    /// Port of `createRoleSaturationProcessLinker` (cpp 7320–7328).
    pub fn create_role_saturation_process_linker(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Id<RoleSaturationProcess> {
        let mut role_sat_proc_linker = calc_alg_context
            .processing_data_box_mut()
            .take_remaining_role_saturation_process_linker();
        if role_sat_proc_linker.is_none() {
            // W4.5: CObjectAllocator<CRoleSaturationProcessLinker>::allocateAndConstruct(taskMemMan).
            // W4-RECONCILE[api]: the databox remaining-list / return type is keyed by the linker
            // *payload* marker (`RoleSaturationProcess`); the real arena yields a
            // `RoleSaturationProcessLinkerId`. Same arena index, distinct marker — convert via the
            // shared raw index (faithful to the C++ payload/linker split, mirrors `release*`).
            let new_linker = calc_alg_context
                .process_context_mut()
                .alloc_role_sat_proc_linker(RoleSaturationProcessLinker::new());
            role_sat_proc_linker = Id::new(new_linker.raw);
        }
        role_sat_proc_linker
    }

    /// Port of `createConceptSaturationProcessLinker` (cpp 7330–7338).
    pub fn create_concept_saturation_process_linker(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Id<ConceptSaturationProcess> {
        let mut con_sat_proc_linker = calc_alg_context
            .processing_data_box_mut()
            .take_remaining_concept_saturation_process_linker();
        if con_sat_proc_linker.is_none() {
            // W4.5: CObjectAllocator<CConceptSaturationProcessLinker>::allocateAndConstruct(taskMemMan).
            // W4-RECONCILE[api]: payload-keyed return (`ConceptSaturationProcess`) vs real
            // `ConceptSaturationProcessLinkerId` — convert via the shared raw index (mirrors `release*`).
            let new_linker = calc_alg_context
                .process_context_mut()
                .alloc_con_sat_proc_linker(ConceptSaturationProcessLinker::new());
            con_sat_proc_linker = Id::new(new_linker.raw);
        }
        con_sat_proc_linker
    }

    /// Port of `createIndividualSaturationNodeLinker` (cpp 7348–7356).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the databox models this linker chain as
    /// `Vec<SatNodeId>` (the linker's payload node), so the create returns a
    /// `SatNodeId`.
    pub fn create_individual_saturation_node_linker(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let indi_sat_node_linker = calc_alg_context
            .processing_data_box_mut()
            .take_remaining_individual_saturation_node_linker();
        if indi_sat_node_linker.is_none() {
            // W4-DEFER[memory-pool]: CObjectAllocator<CIndividualSaturationProcessNodeLinker>::allocateAndConstruct(taskMemMan)
        }
        indi_sat_node_linker
    }

    /// Port of `releaseIndividualSaturationNodeLinker` (cpp 7358–7362).
    pub fn release_individual_saturation_node_linker(
        &mut self,
        ind_sat_node_linker: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: indSatNodeLinker->clearNext();
        calc_alg_context
            .processing_data_box_mut()
            .add_remaining_individual_saturation_node_linker(ind_sat_node_linker);
    }

    /// Port of `createIndividualSaturationSuccessorLinkDataLinker` (cpp 7368–7376).
    pub fn create_individual_saturation_successor_link_data_linker(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> IndividualSaturationSuccessorLinkDataLinkerId {
        let ctx_base = &mut calc_alg_context.base;
        let mut succ_link_data_linker = ctx_base
            .used_processing_data_box
            .take_remaining_individual_successor_link_data_linker(
                &mut ctx_base.used_process_context,
            );
        if succ_link_data_linker.is_none() {
            succ_link_data_linker = calc_alg_context
                .process_context_mut()
                .alloc_indi_sat_succ_link_data_linker(
                    IndividualSaturationSuccessorLinkDataLinker::new(),
                );
        }
        succ_link_data_linker
    }

    /// Port of `releaseIndividualSaturationSuccessorLinkDataLinker` (cpp 7378–7384).
    pub fn release_individual_saturation_successor_link_data_linker(
        &mut self,
        succ_link_data_linker: IndividualSaturationSuccessorLinkDataLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if succ_link_data_linker.is_some() {
            let ctx_base = &mut calc_alg_context.base;
            ctx_base
                .used_process_context
                .indi_sat_succ_link_data_linker_mut(succ_link_data_linker)
                .clear_next();
            ctx_base
                .used_processing_data_box
                .add_remaining_individual_successor_link_data_linker(
                    &mut ctx_base.used_process_context,
                    succ_link_data_linker,
                );
        }
    }

    /// Port of `createIndividualSaturationUpdateLinker` (cpp 7392–7400).
    ///
    /// KONCLUDE-PORT-NOTE[api]: the databox models the status-update chain as
    /// `Vec<SatNodeId>` (the linker's payload node), so the create returns a
    /// `SatNodeId`.
    pub fn create_individual_saturation_update_linker(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SatNodeId {
        let con_sat_update_linker = calc_alg_context
            .processing_data_box_mut()
            .take_remaining_individual_saturation_update_linker();
        if con_sat_update_linker.is_none() {
            // W4-DEFER[memory-pool]: CObjectAllocator<CIndividualSaturationProcessNodeStatusUpdateLinker>::allocateAndConstruct(taskMemMan)
        }
        con_sat_update_linker
    }

    /// Port of `releaseIndividualSaturationUpdateLinker` (cpp 7402–7406).
    pub fn release_individual_saturation_update_linker(
        &mut self,
        con_sat_update_linker: SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: conSatUpdateLinker->clearNext();
        calc_alg_context
            .processing_data_box_mut()
            .add_remaining_individual_saturation_update_linker(con_sat_update_linker);
    }

    /// Port of `createModifiedProcessUpdateLinker` (cpp 7409–7412).
    pub fn create_modified_process_update_linker(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> SaturationModifiedProcessUpdateLinkerId {
        calc_alg_context
            .process_context_mut()
            .alloc_sat_modified_process_update_linker(SaturationModifiedProcessUpdateLinker::new())
    }

    /// Port of `createImplicationReapplyConceptSaturationDescriptor` (cpp 7415–7419).
    ///
    pub fn create_implication_reapply_concept_saturation_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> ImplicationReapplyConceptSaturationDescriptorId {
        calc_alg_context
            .process_context_mut()
            .alloc_imp_reapply_con_sat_desc(ImplicationReapplyConceptSaturationDescriptor::new())
    }

    // =======================================================================
    // Group K — concept-add / label mutation.
    // =======================================================================

    /// Port of `addConceptsFilteredToIndividual` — the 5-arg
    /// `updateCopyDependedIndividual` overload (cpp 7145–7153).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++ `CSortedNegLinker<CConcept*>*`
    /// concept linker becomes a `&[NegLink<ConceptId>]` slice (`getData()` →
    /// `.target`, `isNegated()` → `.negated`, `getNext()` → slice advance).
    pub fn add_concepts_filtered_to_individual_update_copy(
        &mut self,
        concept_add_linker: &[NegLink<ConceptId>],
        negate: bool,
        process_indi: &mut SatNodeId,
        update_copy_depended_individual: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        for concept_add_linker_it in concept_add_linker {
            let op_concept = concept_add_linker_it.target;
            let op_con_negation = concept_add_linker_it.negated ^ negate;
            self.add_concept_filtered_to_individual_update_copy(
                op_concept,
                op_con_negation,
                process_indi,
                update_copy_depended_individual,
                calc_alg_context,
            );
        }
    }

    /// Port of `addConceptsFilteredToIndividual` — the 4-arg overloads (cpp
    /// 7155–7163 / 7165–7173 / 7175–7183, identical bodies for `CSortedNegLinker`
    /// / `CXNegLinker` / `CXSortedNegLinker`; collapsed to one `&[NegLink<ConceptId>]`).
    pub fn add_concepts_filtered_to_individual(
        &mut self,
        concept_add_linker: &[NegLink<ConceptId>],
        negate: bool,
        process_indi: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        for concept_add_linker_it in concept_add_linker {
            let op_concept = concept_add_linker_it.target;
            let op_con_negation = concept_add_linker_it.negated ^ negate;
            self.add_concept_filtered_to_individual(
                op_concept,
                op_con_negation,
                process_indi,
                calc_alg_context,
            );
        }
    }

    /// Port of `addConceptFilteredToIndividual` — the 4-arg overload (cpp 7186–7189).
    pub fn add_concept_filtered_to_individual(
        &mut self,
        adding_concept: ConceptId,
        negate: bool,
        process_indi: &mut SatNodeId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // labelSet = processIndi->getReapplyConceptSaturationLabelSet();
        // KONCLUDE-PORT-NOTE[api]: the C++ no-arg getter DEFAULTS to create=true
        // (CIndividualSaturationProcessNode.h line 96) — reading the raw field
        // here passed NONE for a fresh node and blew up the label-set insert.
        let label_set = calc_alg_context
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(*process_indi, true);
        self.add_concept_filtered_to_individual_label_set(
            adding_concept,
            negate,
            process_indi,
            label_set,
            true,
            calc_alg_context,
        );
    }

    /// Port of `addConceptFilteredToIndividual` — the 5-arg
    /// `updateCopyDependedIndividual` overload (cpp 7192–7195).
    pub fn add_concept_filtered_to_individual_update_copy(
        &mut self,
        adding_concept: ConceptId,
        negate: bool,
        process_indi: &mut SatNodeId,
        update_copy_depended_individual: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // KONCLUDE-PORT-NOTE[api]: create=true default — see the 4-arg overload.
        let label_set = calc_alg_context
            .process_context_mut()
            .sat_node_reapply_concept_saturation_label_set(*process_indi, true);
        self.add_concept_filtered_to_individual_label_set(
            adding_concept,
            negate,
            process_indi,
            label_set,
            update_copy_depended_individual,
            calc_alg_context,
        );
    }

    /// Port of `addConceptFilteredToIndividual` — the 6-arg label-set dispatch
    /// (cpp 7200–7225).
    pub fn add_concept_filtered_to_individual_label_set(
        &mut self,
        adding_concept: ConceptId,
        negate: bool,
        root_process_indi: &mut SatNodeId,
        label_set: ReapplyConceptSaturationLabelSetId,
        update_copy_depended_individual: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let op_code = calc_alg_context
            .ontology_arenas()
            .concept(adding_concept)
            .get_operator_code();
        let mut insert_concept = self.conf_force_all_concept_insertion;
        if !insert_concept {
            if (!negate
                && (op_code == CCAND
                    || op_code == CCAQAND
                    || op_code == CCIMPLAQAND
                    || op_code == CCBRANCHAQAND))
                || (negate && op_code == CCOR)
            {
                // opConLinkerIt = addingConcept->getOperandList();
                let op_con_linker: Vec<NegLink<ConceptId>> = calc_alg_context
                    .ontology_arenas()
                    .concept(adding_concept)
                    .get_operand_list()
                    .to_vec();
                self.add_concepts_filtered_to_individual_update_copy(
                    &op_con_linker,
                    negate,
                    root_process_indi,
                    update_copy_depended_individual,
                    calc_alg_context,
                );
            } else if op_code == CCAQCHOOCE {
                let op_con_linker: Vec<NegLink<ConceptId>> = calc_alg_context
                    .ontology_arenas()
                    .concept(adding_concept)
                    .get_operand_list()
                    .to_vec();
                for op_con_linker_it in op_con_linker {
                    let op_concept = op_con_linker_it.target;
                    let op_negation = op_con_linker_it.negated;
                    if op_negation == negate {
                        self.add_concept_filtered_to_individual_label_set(
                            op_concept,
                            false,
                            root_process_indi,
                            label_set,
                            update_copy_depended_individual,
                            calc_alg_context,
                        );
                    }
                }
            } else if self.conf_implication_adding_skipping && op_code == CCIMPL {
                insert_concept = false;
            } else {
                insert_concept = true;
            }
        }
        if insert_concept {
            self.add_concept_to_individual(
                adding_concept,
                negate,
                root_process_indi,
                label_set,
                update_copy_depended_individual,
                calc_alg_context,
            );
        }
    }

    /// Port of `addConceptToIndividual` (cpp 7228–7288).
    pub fn add_concept_to_individual(
        &mut self,
        adding_concept: ConceptId,
        negate: bool,
        root_process_indi: &mut SatNodeId,
        label_set: ReapplyConceptSaturationLabelSetId,
        update_copy_depended_individual: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // STATINC(CONCEPTSADDEDINDINODELABELSETCOUNT) + g_ksat_concAdds — debug stats, elided.

        let concept_saturation_descriptor =
            self.create_concept_saturation_descriptor(calc_alg_context);
        calc_alg_context
            .process_context_mut()
            .con_sat_desc_mut(concept_saturation_descriptor)
            .init_concept_saturation_descriptor(adding_concept, negate);

        let contained = self.insert_concept_to_individual_concept_set(
            concept_saturation_descriptor,
            root_process_indi,
            label_set,
            calc_alg_context,
        );
        if !contained {
            // STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT) + g_ksat_* — debug stats, elided.
            let concept_saturation_process_linker_payload =
                self.create_concept_saturation_process_linker(calc_alg_context);
            let concept_saturation_process_linker = ConceptSaturationProcessLinkerId::new(
                concept_saturation_process_linker_payload.raw,
            );
            // conceptSaturationProcessLinker->initConceptSaturationProcessLinker(conceptSaturationDescriptor);
            calc_alg_context
                .process_context_mut()
                .con_sat_proc_linker_mut(concept_saturation_process_linker)
                .init_concept_saturation_process_linker(concept_saturation_descriptor);
            // rootProcessIndi->addConceptSaturationProcessLinker(conceptSaturationProcessLinker);
            calc_alg_context
                .process_context_mut()
                .sat_node_add_concept_saturation_process_linker(
                    *root_process_indi,
                    concept_saturation_process_linker,
                );
            self.add_individual_to_processing_queue(root_process_indi, calc_alg_context);

            // if (updateCopyDependedIndividual && rootProcessIndi->hasCopyDependingIndividualNodeLinker())
            let has_copy_depending = !calc_alg_context
                .process_context()
                .sat_node(*root_process_indi)
                .depending_indi_node_linker
                .is_empty();
            if update_copy_depended_individual && has_copy_depending {
                // KONCLUDE-PORT-NOTE[ownership]: snapshot the copy-depending linker
                // (`getCopyDependingIndividualNodeLinker`) before the `&mut`-ctx
                // recursion; NegLink<SatNodeId> is Copy.
                let copy_dep_indi_linker: Vec<NegLink<SatNodeId>> = calc_alg_context
                    .process_context()
                    .sat_node(*root_process_indi)
                    .depending_indi_node_linker
                    .clone();
                for copy_dep_indi_linker_it in copy_dep_indi_linker {
                    let mut copy_dep_indi_node = copy_dep_indi_linker_it.target;
                    // copyDepIndiNode->getReapplyConceptSaturationLabelSet(true) — lazy-create
                    // W4-DEFER[api]; the existing label-set field is read.
                    let cd_label_set = calc_alg_context
                        .process_context()
                        .sat_node(copy_dep_indi_node)
                        .reapply_con_sat_label_set;
                    self.add_concept_to_individual(
                        adding_concept,
                        negate,
                        &mut copy_dep_indi_node,
                        cd_label_set,
                        true,
                        calc_alg_context,
                    );
                }
            }
        } else {
            // C++: TODO (commented out) — may releaseConceptSaturationDescriptor(conceptSaturationDescriptor).
        }
    }

    /// Port of `insertConceptToIndividualConceptSet` (cpp 7424–7535).
    ///
    /// The operator-code dispatch, label-set insertion, matching implication replay,
    /// implication-trigger seeding, implication-adding-skipping seed generation, and
    /// clash side effects are live. The modified-update-linker hook now traverses the
    /// typed `CSaturationModifiedProcessUpdateLinker` chain and dispatches the
    /// disjunct-common-concept extraction update type.
    ///
    /// C++ structure:
    /// ```text
    /// contained = false; insertConcept = true; implTriggerGeneration = false
    /// requiredBackProp = rootProcessIndi->getRequiredBackwardPropagation()
    /// concept = conceptSaturationDescriptor->getConcept(); conNeg = ...->getNegation()
    /// opCode = concept->getOperatorCode()
    /// if !mConfForceAllConceptInsertion:
    ///     CCATOM|CCSUB                    -> ++mAddedSUBConcepts
    ///     !conNeg & (CCALL|CCIMPLALL)     -> ++mAddedALLConcepts; insertConcept=false; contained=!requiredBackProp
    ///     (!conNeg&(CCSOME|CCAQSOME))|(conNeg&CCALL) -> ++mAddedSOMEConcepts
    ///     CCIMPL                          -> ++mAddedIMPLConcepts;
    ///                                        if !requiredBackProp & !hasConceptLocalImpact(concept,false): insertConcept=false; contained=true
    ///                                        else: implTriggerGeneration=true; contained=true
    ///     CCIMPLTRIG|CCBRANCHTRIG         -> ++mAddedTRIGGConcepts
    ///     CCAQCHOOCE                      -> insertConcept=false; ++mAddedELSEConcepts
    ///     else                            -> ++mAddedELSEConcepts
    /// if insertConcept:
    ///     clashed = labelSet->insertConceptReturnClashed(conceptSaturationDescriptor,&newInsertion,&reapplyImpReapplyConSatDesPtr)
    ///     if !clashed:
    ///         if newInsertion:
    ///             replay reapplyImpReapplyConSatDes triggers matching this concept -> updateImplicationReapplyConceptSaturationDescriptor(...)
    ///             if implTriggerGeneration: seed first trigger (tmp descriptor) -> updateImplicationReapplyConceptSaturationDescriptor(...)
    ///             if mConfImplicationAddingSkipping & !conNeg & (CCATOM|CCSUB|CCIMPLTRIG|CCBRANCHTRIG):
    ///                 for non-negated CCIMPL operand: seed first trigger -> updateImplicationReapplyConceptSaturationDescriptor(...)
    ///             if labelSet->hasModifiedUpdateLinkers(): processModificationUpdateLinkers(rootProcessIndi,labelSet,labelSet->getModifiedUpdateLinker())
    ///         else: contained = true
    ///     else:
    ///         rootProcessIndi->addClashedConceptSaturationDescriptorLinker(conceptSaturationDescriptor)
    ///         updateDirectAddingIndividualStatusFlags(rootProcessIndi, INDSATFLAGCLASHED)
    ///         contained = true
    /// return contained
    /// ```
    pub fn insert_concept_to_individual_concept_set(
        &mut self,
        concept_saturation_descriptor: Id<ConceptSaturationDescriptor>,
        root_process_indi: &mut SatNodeId,
        label_set: ReapplyConceptSaturationLabelSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let mut contained = false;
        let mut insert_concept = true;
        let mut impl_trigger_generation = false;
        let required_back_prop = calc_alg_context
            .process_context()
            .sat_node(*root_process_indi)
            .get_required_backward_propagation();
        let (concept, con_neg, con_tag, op_code) = {
            let process_context = calc_alg_context.process_context();
            let con_sat_des = process_context.con_sat_desc(concept_saturation_descriptor);
            let concept = con_sat_des.get_concept();
            let con_neg = con_sat_des.get_negation();
            let concept_ref = calc_alg_context.ontology_arenas().concept(concept);
            (
                concept,
                con_neg,
                concept_ref.get_concept_tag(),
                concept_ref.get_operator_code(),
            )
        };

        if !self.conf_force_all_concept_insertion {
            if op_code == CCATOM {
                self.added_sub_concepts += 1;
            } else if op_code == CCSUB {
                self.added_sub_concepts += 1;
            } else if !con_neg && (op_code == CCALL || op_code == CCIMPLALL) {
                self.added_all_concepts += 1;
                insert_concept = false;
                contained = !required_back_prop;
            } else if (!con_neg && (op_code == CCSOME || op_code == CCAQSOME))
                || (con_neg && op_code == CCALL)
            {
                self.added_some_concepts += 1;
            } else if op_code == CCIMPL {
                self.added_impl_concepts += 1;
                if !required_back_prop
                    && !self.has_concept_local_impact(concept, false, calc_alg_context)
                {
                    insert_concept = false;
                    contained = true;
                } else {
                    impl_trigger_generation = true;
                    contained = true;
                }
            } else if op_code == CCIMPLTRIG || op_code == CCBRANCHTRIG {
                self.added_trigg_concepts += 1;
            } else if op_code == CCAQCHOOCE {
                insert_concept = false;
                self.added_else_concepts += 1;
            } else {
                self.added_else_concepts += 1;
            }
        }

        if insert_concept {
            let mut new_insertion = false;
            let mut reapply_imp_reapply_con_sat_des =
                ImplicationReapplyConceptSaturationDescriptorId::NONE;
            let clashed = calc_alg_context
                .process_context_mut()
                .reapply_con_sat_label_set_insert_concept_return_clashed(
                    label_set,
                    concept_saturation_descriptor,
                    con_tag,
                    Some(&mut new_insertion),
                    Some(&mut reapply_imp_reapply_con_sat_des),
                );

            if !clashed {
                if new_insertion {
                    let mut reapply_it = reapply_imp_reapply_con_sat_des;
                    while reapply_it.is_some() {
                        let (next_reapply, trigger) = {
                            let descriptor = calc_alg_context
                                .process_context()
                                .imp_reapply_con_sat_desc(reapply_it);
                            (
                                descriptor.get_next(),
                                descriptor
                                    .get_next_trigger_concept()
                                    .and_then(|linker| linker.first().copied()),
                            )
                        };
                        if let Some(trigger_con_linker) = trigger {
                            if trigger_con_linker.target == concept
                                && trigger_con_linker.negated != con_neg
                            {
                                self.update_implication_reapply_concept_saturation_descriptor(
                                    reapply_it,
                                    root_process_indi,
                                    label_set,
                                    calc_alg_context,
                                );
                            }
                        }
                        reapply_it = next_reapply;
                    }

                    if impl_trigger_generation {
                        let trigger_suffix = calc_alg_context
                            .ontology_arenas()
                            .concept(concept)
                            .get_operand_list()
                            .to_vec();
                        let new_reapply = self
                            .create_implication_reapply_concept_saturation_descriptor(
                                calc_alg_context,
                            );
                        calc_alg_context
                            .process_context_mut()
                            .imp_reapply_con_sat_desc_mut(new_reapply)
                            .init_implication_reaplly_concept_saturation_descriptor(
                                concept,
                                Some(&trigger_suffix),
                            );
                        self.update_implication_reapply_concept_saturation_descriptor(
                            new_reapply,
                            root_process_indi,
                            label_set,
                            calc_alg_context,
                        );
                    }

                    if self.conf_implication_adding_skipping
                        && !con_neg
                        && (op_code == CCATOM
                            || op_code == CCSUB
                            || op_code == CCIMPLTRIG
                            || op_code == CCBRANCHTRIG)
                    {
                        let op_concepts = calc_alg_context
                            .ontology_arenas()
                            .concept(concept)
                            .get_operand_list()
                            .to_vec();
                        for op_concept_linker_it in op_concepts {
                            if !op_concept_linker_it.negated {
                                let op_concept = op_concept_linker_it.target;
                                if calc_alg_context
                                    .ontology_arenas()
                                    .concept(op_concept)
                                    .get_operator_code()
                                    == CCIMPL
                                {
                                    let trigger_suffix = calc_alg_context
                                        .ontology_arenas()
                                        .concept(op_concept)
                                        .get_operand_list()
                                        .to_vec();
                                    let new_reapply = self
                                        .create_implication_reapply_concept_saturation_descriptor(
                                            calc_alg_context,
                                        );
                                    calc_alg_context
                                        .process_context_mut()
                                        .imp_reapply_con_sat_desc_mut(new_reapply)
                                        .init_implication_reaplly_concept_saturation_descriptor(
                                            op_concept,
                                            Some(&trigger_suffix),
                                        );
                                    self.update_implication_reapply_concept_saturation_descriptor(
                                        new_reapply,
                                        root_process_indi,
                                        label_set,
                                        calc_alg_context,
                                    );
                                }
                            }
                        }
                    }

                    if calc_alg_context
                        .process_context()
                        .reapply_con_sat_label_set(label_set)
                        .has_modified_update_linkers()
                    {
                        let mod_proc_update_linker = calc_alg_context
                            .process_context()
                            .reapply_con_sat_label_set(label_set)
                            .get_modified_update_linker();
                        self.process_modification_update_linkers(
                            root_process_indi,
                            label_set,
                            mod_proc_update_linker,
                            calc_alg_context,
                        );
                    }
                } else {
                    contained = true;
                }
            } else {
                calc_alg_context
                    .process_context_mut()
                    .sat_node_add_clashed_concept_saturation_descriptor_linker(
                        *root_process_indi,
                        concept_saturation_descriptor,
                    );
                self.update_direct_adding_individual_status_flags(
                    *root_process_indi,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,
                    calc_alg_context,
                );
                contained = true;
            }
        }
        contained
    }

    /// Port of `processModificationUpdateLinkers` (cpp 7540–7548).
    ///
    /// C++ structure:
    /// ```text
    /// for modProcUpdateLinkerIt in modProcUpdateLinker:
    ///     indiProcNode = modProcUpdateLinkerIt->getProcessingIndividual()
    ///     updateType   = modProcUpdateLinkerIt->getUpdateType()
    ///     if updateType == UPDATEPDISJUNCTCOMMONCONCEPTSEXTRACTION:
    ///         addDisjunctCommonConceptExtractionToProcessingQueue(indiProcNode)
    /// ```
    pub fn process_modification_update_linkers(
        &mut self,
        root_process_indi: &mut SatNodeId,
        label_set: ReapplyConceptSaturationLabelSetId,
        mod_proc_update_linker: SaturationModifiedProcessUpdateLinkerId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let _ = (&mut *root_process_indi, label_set);
        let mut mod_proc_update_linker_it = mod_proc_update_linker;
        while mod_proc_update_linker_it.is_some() {
            let (next, mut indi_proc_node, update_type) = {
                let linker = calc_alg_context
                    .process_context()
                    .sat_modified_process_update_linker(mod_proc_update_linker_it);
                (
                    linker.get_next(),
                    linker.get_processing_individual(),
                    linker.get_update_type(),
                )
            };
            if update_type
                == SaturationModificationProcessUpdateType::UpdateDisjunctCommonConceptExtraction
            {
                self.add_disjunct_common_concept_extraction_to_processing_queue(
                    &mut indi_proc_node,
                    calc_alg_context,
                );
            }
            mod_proc_update_linker_it = next;
        }
    }

    /// Port of `updateImplicationReapplyConceptSaturationDescriptor` (cpp 7552–7576).
    ///
    /// C++ structure:
    /// ```text
    /// currTriggerConcept = reapplyImpReapplyConSatDes->getNextTriggerConcept()
    /// nextTriggerConcept = currTriggerConcept->getNext()
    /// implConcept        = reapplyImpReapplyConSatDes->getImplicationConcept()
    /// if !nextTriggerConcept:
    ///     impExConOpLinker = implConcept->getOperandList()
    ///     addConceptFilteredToIndividual(impExConOpLinker->getData(), impExConOpLinker->isNegated(),
    ///                                    rootProcessIndi, labelSet, false)
    /// else:
    ///     nextTrigger = nextTriggerConcept->getData()
    ///     newReapply = createImplicationReapplyConceptSaturationDescriptor()
    ///     newReapply->initImplicationReapllyConceptSaturationDescriptor(implConcept, nextTriggerConcept)
    ///     triggered = labelSet->insertConceptReapplicationReturnTriggered(nextTrigger->getConceptTag(), newReapply, &conSatDes)
    ///     if triggered: updateImplicationReapplyConceptSaturationDescriptor(newReapply, rootProcessIndi, labelSet)
    /// return true
    /// ```
    pub fn update_implication_reapply_concept_saturation_descriptor(
        &mut self,
        reapply_imp_reapply_con_sat_des: ImplicationReapplyConceptSaturationDescriptorId,
        root_process_indi: &mut SatNodeId,
        label_set: ReapplyConceptSaturationLabelSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(IMPLICATIONTRIGGERINGCOUNT) / IMPLICATIONEXECUTINGCOUNT — debug stats, elided.
        let (impl_concept, curr_trigger_concepts) = {
            let descriptor = calc_alg_context
                .process_context()
                .imp_reapply_con_sat_desc(reapply_imp_reapply_con_sat_des);
            (
                descriptor.get_implication_concept(),
                descriptor
                    .get_next_trigger_concept()
                    .map(|trigger| trigger.to_vec())
                    .unwrap_or_default(),
            )
        };
        if curr_trigger_concepts.is_empty() {
            return true;
        }

        let next_trigger_concepts = &curr_trigger_concepts[1..];
        if next_trigger_concepts.is_empty() {
            // execute implication
            if let Some(imp_ex_con_op_linker) = calc_alg_context
                .ontology_arenas()
                .concept(impl_concept)
                .get_operand_list()
                .first()
                .copied()
            {
                self.add_concept_filtered_to_individual_label_set(
                    imp_ex_con_op_linker.target,
                    imp_ex_con_op_linker.negated,
                    root_process_indi,
                    label_set,
                    false,
                    calc_alg_context,
                );
            }
        } else {
            let next_trigger = next_trigger_concepts[0].target;
            let new_reapply_imp_reapply_con_sat_des =
                self.create_implication_reapply_concept_saturation_descriptor(calc_alg_context);
            calc_alg_context
                .process_context_mut()
                .imp_reapply_con_sat_desc_mut(new_reapply_imp_reapply_con_sat_des)
                .init_implication_reaplly_concept_saturation_descriptor(
                    impl_concept,
                    Some(next_trigger_concepts),
                );

            let next_trigger_tag = calc_alg_context
                .ontology_arenas()
                .concept(next_trigger)
                .get_concept_tag();
            let mut con_sat_des = Id::<ConceptSaturationDescriptor>::NONE;
            let triggered = calc_alg_context
                .process_context_mut()
                .reapply_con_sat_label_set_insert_concept_reapplication_return_triggered(
                    label_set,
                    next_trigger_tag,
                    new_reapply_imp_reapply_con_sat_des,
                    Some(&mut con_sat_des),
                );
            if triggered {
                self.update_implication_reapply_concept_saturation_descriptor(
                    new_reapply_imp_reapply_con_sat_des,
                    root_process_indi,
                    label_set,
                    calc_alg_context,
                );
            }
        }
        true
    }

    /// Port of `hasConceptLocalImpact` (cpp 7579–7623).
    pub fn has_concept_local_impact(
        &mut self,
        concept: ConceptId,
        con_neg: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let op_code = calc_alg_context
            .ontology_arenas()
            .concept(concept)
            .get_operator_code();
        if op_code == CCSUB || op_code == CCIMPLTRIG || op_code == CCBRANCHTRIG {
            true
        } else if (!con_neg && (op_code == CCALL || op_code == CCIMPLALL || op_code == CCBRANCHALL))
            || (con_neg && op_code == CCSOME)
        {
            false
        } else if (!con_neg
            && (op_code == CCAND
                || op_code == CCAQAND
                || op_code == CCBRANCHAQAND
                || op_code == CCIMPLAQAND))
            || (con_neg && op_code == CCOR)
        {
            let op_con_list: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            for op in op_con_list {
                let op_concept = op.target;
                let op_con_neg = op.negated ^ con_neg;
                if self.has_concept_local_impact(op_concept, op_con_neg, calc_alg_context) {
                    return true;
                }
            }
            false
        } else if (!con_neg && (op_code == CCSOME || op_code == CCAQSOME))
            || (con_neg && op_code == CCALL)
        {
            true
        } else if (!con_neg
            && (op_code == CCAQALL || op_code == CCIMPLAQALL || op_code == CCBRANCHAQALL))
            || (con_neg && (op_code == CCSOME || op_code == CCAQSOME))
        {
            false
        } else if op_code == CCAQCHOOCE {
            let op_con_list: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            for op in op_con_list {
                let op_concept = op.target;
                let op_negation = op.negated;
                if op_negation == con_neg
                    && self.has_concept_local_impact(op_concept, false, calc_alg_context)
                {
                    return true;
                }
            }
            false
        } else if op_code == CCIMPL {
            let op_con_list: Vec<NegLink<ConceptId>> = calc_alg_context
                .ontology_arenas()
                .concept(concept)
                .get_operand_list()
                .to_vec();
            if let Some(op) = op_con_list.first() {
                let op_concept = op.target;
                let op_negation = op.negated;
                if self.has_concept_local_impact(op_concept, op_negation, calc_alg_context) {
                    return true;
                }
            }
            false
        } else {
            false
        }
    }

    // =======================================================================
    // Group L — nominal dependency / influenced-nominal tracking.
    // =======================================================================

    /// Port of `addNominalDependentIndividualNode` (cpp 6431–6441).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the C++
    /// `CSaturationNominalDependentNodeData::NOMINALCONNECTIONTYPE connectionType`
    /// enum becomes an opaque `Cint64`.
    pub fn add_nominal_dependent_individual_node(
        &mut self,
        nominal_id: Cint64,
        dependent_indi_node: SatNodeId,
        connection_type: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let nominal_dependent_node_hash =
            calc_alg_context.saturation_nominal_dependent_node_hash(true);
        calc_alg_context
            .process_context_mut()
            .sat_nominal_dependent_node_hash_add_nominal_dependent_node(
                nominal_dependent_node_hash,
                nominal_id,
                dependent_indi_node,
                SaturationNominalConnectionType::from(connection_type),
            );
        let influenced_nominal_set = calc_alg_context.saturation_influenced_nominal_set(true);
        let is_nominal_influenced = calc_alg_context
            .process_context()
            .sat_influenced_nominal_set(influenced_nominal_set)
            .is_nominal_influenced(nominal_id);
        if is_nominal_influenced {
            self.update_direct_adding_individual_status_flags(
                dependent_indi_node,
                IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                calc_alg_context,
            );
            self.set_insufficient_node_occured(calc_alg_context);
        }
    }

    /// Port of `addInfluencedNominal` (cpp 6444–6457).
    pub fn add_influenced_nominal(
        &mut self,
        influenced_nominal_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let influenced_nominal_set = calc_alg_context.saturation_influenced_nominal_set(true);
        let first_influence = calc_alg_context
            .process_context_mut()
            .sat_influenced_nominal_set_mut(influenced_nominal_set)
            .set_nominal_influenced(influenced_nominal_id);
        if first_influence {
            let nominal_dependent_node_hash =
                calc_alg_context.saturation_nominal_dependent_node_hash(true);
            let mut nominal_dep_node_data_it = calc_alg_context
                .process_context()
                .sat_nominal_dependent_node_hash(nominal_dependent_node_hash)
                .get_nominal_dependent_node_data(influenced_nominal_id);
            while nominal_dep_node_data_it.is_some() {
                let dependent_ind_sat_proc_node = calc_alg_context
                    .process_context()
                    .sat_nominal_dependent_node_data(nominal_dep_node_data_it)
                    .get_dependent_individual_saturation_node();
                let next = calc_alg_context
                    .process_context()
                    .sat_nominal_dependent_node_data(nominal_dep_node_data_it)
                    .get_next_nominal_connection_type_data();
                self.update_direct_adding_individual_status_flags(
                    dependent_ind_sat_proc_node,
                    IndividualSaturationProcessNodeStatusFlags::INDSATFLAGINSUFFICIENT,
                    calc_alg_context,
                );
                self.set_insufficient_node_occured(calc_alg_context);
                nominal_dep_node_data_it = next;
            }
        }
    }

    /// Port of `delayNominalSaturationConceptProcessing` (cpp 6674–6680).
    pub fn delay_nominal_saturation_concept_processing(
        &mut self,
        process_indi: SatNodeId,
        con_pro_linker: ConceptSaturationProcessLinkerId,
        nominal_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        self.propagate_unloaded_abox_completion_graph_dependent_individual_node_flag(
            process_indi,
            con_pro_linker,
            nominal_id,
            calc_alg_context,
        );
        let nom_delayed_con_sat_proc_linker =
            self.create_concept_saturation_process_linker(calc_alg_context);
        // W4-DEFER[api]: nomDelayedConSatProcLinker->initConceptSaturationProcessLinker(
        //   conProLinker->getConceptSaturationDescriptor());
        // W4-DEFER[api]: processIndi->getNominalHandlingData(true)
        //   ->addDelayedNominalConceptSaturationProcessLinker(nomDelayedConSatProcLinker);
        self.set_delayed_nominal_processing_occured(calc_alg_context);
    }

    /// Port of `propagateUnloadedABoxCompletionGraphDependentIndividualNodeFlag`
    /// (cpp 6849–6851).
    pub fn propagate_unloaded_abox_completion_graph_dependent_individual_node_flag(
        &mut self,
        process_indi: SatNodeId,
        con_pro_linker: ConceptSaturationProcessLinkerId,
        nominal_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // conProLinker + nominalID are unused in the C++ body (kept for the call sig).
        let _ = (con_pro_linker, nominal_id);
        self.update_direct_adding_individual_status_flags(
            process_indi,
            IndividualSaturationProcessNodeStatusFlags::INDMISSEDABOXCONSISTENCYDATA,
            calc_alg_context,
        );
    }

    // =======================================================================
    // Group L — status-flag propagation.
    // =======================================================================

    /// Port of `updateDirectAddingIndividualStatusFlags` — the `cint64 flags`
    /// entry (cpp 7626–7631).
    pub fn update_direct_adding_individual_status_flags(
        &mut self,
        indi_node: SatNodeId,
        flags: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut adding_flags = IndividualSaturationProcessNodeStatusFlags::default();
        adding_flags.init_status_flags();
        adding_flags.add_flags_code(flags);
        self.update_direct_adding_individual_status_flags_with_flags(
            indi_node,
            &adding_flags,
            calc_alg_context,
        );
    }

    /// Port of `updateDirectNotDependentAddingIndividualStatusFlags` — the
    /// `cint64 flags` entry (cpp 7633–7638).
    pub fn update_direct_not_dependent_adding_individual_status_flags(
        &mut self,
        indi_node: SatNodeId,
        flags: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        let mut adding_flags = IndividualSaturationProcessNodeStatusFlags::default();
        adding_flags.init_status_flags();
        adding_flags.add_flags_code(flags);
        self.update_direct_not_dependent_adding_individual_status_flags_with_flags(
            indi_node,
            &adding_flags,
            calc_alg_context,
        );
    }

    /// Port of `requiresDirectAddingIndividualStatusFlagsUpdate` (cpp 7640–7643).
    pub fn requires_direct_adding_individual_status_flags_update(
        &mut self,
        indi_node: SatNodeId,
        adding_flags: &IndividualSaturationProcessNodeStatusFlags,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // indiDirectFlags = indiNode->getDirectStatusFlags();  (by-value field)
        !calc_alg_context
            .process_context()
            .sat_node(indi_node)
            .direct_status_flags
            .has_flags(adding_flags, true)
    }

    /// Port of `requiresIndirectAddingIndividualStatusFlagsUpdate` (cpp 7647–7650).
    pub fn requires_indirect_adding_individual_status_flags_update(
        &mut self,
        indi_node: SatNodeId,
        adding_flags: &IndividualSaturationProcessNodeStatusFlags,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        !calc_alg_context
            .process_context()
            .sat_node(indi_node)
            .indirect_status_flags
            .has_flags(adding_flags, true)
    }

    /// Port of `updateDirectAddingIndividualStatusFlags` — the flags-object
    /// worklist (cpp 7653–7681).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: see the module-header note — the intrusive
    /// update-linker worklist collapses to a `Vec<SatNodeId>` LIFO stack; the
    /// per-iteration update-linker pool create/release is elided (`[memory-pool]`).
    pub fn update_direct_adding_individual_status_flags_with_flags(
        &mut self,
        indi_node: SatNodeId,
        adding_flags: &IndividualSaturationProcessNodeStatusFlags,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.requires_direct_adding_individual_status_flags_update(
            indi_node,
            adding_flags,
            calc_alg_context,
        ) {
            let mut direct_update_linker: Vec<SatNodeId> = vec![indi_node];
            // directIndiFlags = indiNode->getDirectStatusFlags(); directIndiFlags->addFlags(addingFlags)
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(indi_node)
                .direct_status_flags
                .add_flags(adding_flags);
            self.direct_updated_status_indi_node_count += 1;

            while !direct_update_linker.is_empty() {
                let update_indi_node = direct_update_linker.remove(0);
                // for depending copy individuals (getCopyDependingIndividualNodeLinker):
                let depending_indi_linker: Vec<NegLink<SatNodeId>> = calc_alg_context
                    .process_context()
                    .sat_node(update_indi_node)
                    .depending_indi_node_linker
                    .clone();
                for depending_indi_linker_it in depending_indi_linker {
                    let depending_indi = depending_indi_linker_it.target;
                    if self.requires_direct_adding_individual_status_flags_update(
                        depending_indi,
                        adding_flags,
                        calc_alg_context,
                    ) {
                        calc_alg_context
                            .process_context_mut()
                            .sat_node_mut(depending_indi)
                            .direct_status_flags
                            .add_flags(adding_flags);
                        self.direct_updated_status_indi_node_count += 1;
                        direct_update_linker.insert(0, depending_indi);
                    }
                }

                self.update_indirect_adding_individual_status_flags(
                    update_indi_node,
                    adding_flags,
                    calc_alg_context,
                );
            }
        }
    }

    /// Port of `updateDirectNotDependentAddingIndividualStatusFlags` — the
    /// flags-object form (cpp 7685–7716).
    pub fn update_direct_not_dependent_adding_individual_status_flags_with_flags(
        &mut self,
        indi_node: SatNodeId,
        adding_flags: &IndividualSaturationProcessNodeStatusFlags,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.requires_direct_adding_individual_status_flags_update(
            indi_node,
            adding_flags,
            calc_alg_context,
        ) {
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(indi_node)
                .direct_status_flags
                .add_flags(adding_flags);
            if self.requires_indirect_adding_individual_status_flags_update(
                indi_node,
                adding_flags,
                calc_alg_context,
            ) {
                calc_alg_context
                    .process_context_mut()
                    .sat_node_mut(indi_node)
                    .indirect_status_flags
                    .add_flags(adding_flags);
                self.indirect_updated_status_indi_node_count += 1;
            }
            self.direct_updated_status_indi_node_count += 1;

            let is_abox = calc_alg_context
                .process_context()
                .sat_node(indi_node)
                .abox_individual_representation_node;
            if !is_abox {
                let backward_sources = calc_alg_context
                    .process_context()
                    .sat_node_role_backward_source_individuals(indi_node);
                for source_individual in backward_sources {
                    self.update_indirect_adding_individual_status_flags(
                        source_individual,
                        adding_flags,
                        calc_alg_context,
                    );
                }

                // non-inverse-connected fan-out (getNonInverseConnectedIndividualNodeLinker):
                let non_inv_conn_indi_linker: Vec<SatNodeId> = calc_alg_context
                    .process_context()
                    .sat_node(indi_node)
                    .non_inverse_connected_indi_node_linker
                    .clone();
                for non_inv_conn_indi_linker_it in non_inv_conn_indi_linker {
                    let source_individual = non_inv_conn_indi_linker_it;
                    self.update_indirect_adding_individual_status_flags(
                        source_individual,
                        adding_flags,
                        calc_alg_context,
                    );
                }
            }
        }
    }

    /// Port of `updateIndirectAddingIndividualStatusFlags` (cpp 7721–7780).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the update-linker worklist collapses to a
    /// `Vec<SatNodeId>` LIFO stack (see module header). The copy-depending and
    /// non-inverse-connected fan-out arms are ported; the role-backward-propagation
    /// hash arm is `W4-DEFER[api]` (the `CRoleBackwardSaturationPropagationHash`
    /// satellite is unported).
    pub fn update_indirect_adding_individual_status_flags(
        &mut self,
        indi_node: SatNodeId,
        adding_flags: &IndividualSaturationProcessNodeStatusFlags,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.requires_indirect_adding_individual_status_flags_update(
            indi_node,
            adding_flags,
            calc_alg_context,
        ) {
            let mut direct_update_linker: Vec<SatNodeId> = vec![indi_node];
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(indi_node)
                .indirect_status_flags
                .add_flags(adding_flags);
            self.indirect_updated_status_indi_node_count += 1;

            while !direct_update_linker.is_empty() {
                let update_indi_node = direct_update_linker.remove(0);

                let depending_indi_linker: Vec<NegLink<SatNodeId>> = calc_alg_context
                    .process_context()
                    .sat_node(update_indi_node)
                    .depending_indi_node_linker
                    .clone();
                for depending_indi_linker_it in depending_indi_linker {
                    let depending_indi = depending_indi_linker_it.target;
                    if self.requires_indirect_adding_individual_status_flags_update(
                        depending_indi,
                        adding_flags,
                        calc_alg_context,
                    ) {
                        calc_alg_context
                            .process_context_mut()
                            .sat_node_mut(depending_indi)
                            .indirect_status_flags
                            .add_flags(adding_flags);
                        self.indirect_updated_status_indi_node_count += 1;
                        direct_update_linker.insert(0, depending_indi);
                    }
                }

                let update_is_abox = calc_alg_context
                    .process_context()
                    .sat_node(update_indi_node)
                    .abox_individual_representation_node;

                if !update_is_abox {
                    let backward_sources = calc_alg_context
                        .process_context()
                        .sat_node_role_backward_source_individuals(update_indi_node);
                    for source_individual in backward_sources {
                        if self.requires_indirect_adding_individual_status_flags_update(
                            source_individual,
                            adding_flags,
                            calc_alg_context,
                        ) {
                            calc_alg_context
                                .process_context_mut()
                                .sat_node_mut(source_individual)
                                .indirect_status_flags
                                .add_flags(adding_flags);
                            self.indirect_updated_status_indi_node_count += 1;
                            direct_update_linker.insert(0, source_individual);
                        }
                    }

                    let non_inv_conn_indi_linker: Vec<SatNodeId> = calc_alg_context
                        .process_context()
                        .sat_node(update_indi_node)
                        .non_inverse_connected_indi_node_linker
                        .clone();
                    for non_inv_conn_indi_linker_it in non_inv_conn_indi_linker {
                        let source_individual = non_inv_conn_indi_linker_it;
                        if self.requires_indirect_adding_individual_status_flags_update(
                            source_individual,
                            adding_flags,
                            calc_alg_context,
                        ) {
                            calc_alg_context
                                .process_context_mut()
                                .sat_node_mut(source_individual)
                                .indirect_status_flags
                                .add_flags(adding_flags);
                            self.indirect_updated_status_indi_node_count += 1;
                            direct_update_linker.insert(0, source_individual);
                        }
                    }
                }
            }
        }
    }

    // =======================================================================
    // Group L — successor-connected-nominal candidate propagation.
    // =======================================================================

    /// Port of `requiresAddingSuccessorConnectedNominals` (cpp 7796–7804).
    pub fn requires_adding_successor_connected_nominals(
        &mut self,
        indi_node: SatNodeId,
        adding_nominal_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        !calc_alg_context
            .process_context_mut()
            .sat_node_has_successor_connected_nominal(indi_node, adding_nominal_id)
    }

    /// Port of `updateAddingSuccessorConnectedNominal` — the set-iterating overload
    /// (cpp 7809–7816).
    pub fn update_adding_successor_connected_nominal_set(
        &mut self,
        indi_node: SatNodeId,
        succ_conn_nom_set: SuccessorConnectedNominalSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if succ_conn_nom_set.is_none() {
            return;
        }
        let nominal_ids = calc_alg_context
            .process_context()
            .nominal_conn_set(succ_conn_nom_set)
            .iter_snapshot();
        for connected_nominal_id in nominal_ids {
            self.update_adding_successor_connected_nominal(
                indi_node,
                connected_nominal_id,
                calc_alg_context,
            );
        }
    }

    /// Port of `updateAddingSuccessorConnectedNominal` — the `cint64 addingNominalID`
    /// worklist (cpp 7819–7880).
    ///
    /// The copy-depending / role-backward-prop-hash / non-inverse-connected
    /// worklist mirrors `updateIndirectAddingIndividualStatusFlags`.
    ///
    /// C++ structure:
    /// ```text
    /// if requiresAddingSuccessorConnectedNominals(indiNode, addingNominalID):
    ///     worklist = [indiNode]
    ///     indiNode->getSuccessorConnectedNominalSet(true)->addSuccessorConnectedNominal(addingNominalID)
    ///     ++mSuccessorConnectedNominalUpdatedCount
    ///     while worklist:
    ///         updateIndiNode = pop head
    ///         for dependingIndi in updateIndiNode->getCopyDependingIndividualNodeLinker():
    ///             if requires(dependingIndi): dependingIndi.set.add(id); ++count; push
    ///         if !updateIndiNode->isABoxIndividualRepresentationNode():
    ///             for source in backwardPropHash links: if requires(source): source.set.add(id); ++count; push
    ///             for source in nonInverseConnected: if requires(source): source.set.add(id); ++count; push
    /// ```
    pub fn update_adding_successor_connected_nominal(
        &mut self,
        indi_node: SatNodeId,
        adding_nominal_id: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.requires_adding_successor_connected_nominals(
            indi_node,
            adding_nominal_id,
            calc_alg_context,
        ) {
            let mut direct_update_linker: Vec<SatNodeId> = vec![indi_node];
            if calc_alg_context
                .process_context_mut()
                .sat_node_add_successor_connected_nominal(indi_node, adding_nominal_id)
            {
                self.successor_connected_nominal_updated_count += 1;
            }

            while !direct_update_linker.is_empty() {
                let update_indi_node = direct_update_linker.remove(0);

                let depending_indi_linker: Vec<NegLink<SatNodeId>> = calc_alg_context
                    .process_context()
                    .sat_node(update_indi_node)
                    .depending_indi_node_linker
                    .clone();
                for depending_indi_linker_it in depending_indi_linker {
                    let depending_indi = depending_indi_linker_it.target;
                    if self.requires_adding_successor_connected_nominals(
                        depending_indi,
                        adding_nominal_id,
                        calc_alg_context,
                    ) {
                        if calc_alg_context
                            .process_context_mut()
                            .sat_node_add_successor_connected_nominal(
                                depending_indi,
                                adding_nominal_id,
                            )
                        {
                            self.successor_connected_nominal_updated_count += 1;
                        }
                        direct_update_linker.insert(0, depending_indi);
                    }
                }

                let update_is_abox = calc_alg_context
                    .process_context()
                    .sat_node(update_indi_node)
                    .abox_individual_representation_node;
                if !update_is_abox {
                    let backward_sources = calc_alg_context
                        .process_context()
                        .sat_node_role_backward_source_individuals(update_indi_node);
                    for source_individual in backward_sources {
                        if self.requires_adding_successor_connected_nominals(
                            source_individual,
                            adding_nominal_id,
                            calc_alg_context,
                        ) {
                            if calc_alg_context
                                .process_context_mut()
                                .sat_node_add_successor_connected_nominal(
                                    source_individual,
                                    adding_nominal_id,
                                )
                            {
                                self.successor_connected_nominal_updated_count += 1;
                            }
                            direct_update_linker.insert(0, source_individual);
                        }
                    }

                    let non_inv_conn_indi_linker: Vec<SatNodeId> = calc_alg_context
                        .process_context()
                        .sat_node(update_indi_node)
                        .non_inverse_connected_indi_node_linker
                        .clone();
                    for non_inv_conn_indi_linker_it in non_inv_conn_indi_linker {
                        let source_individual = non_inv_conn_indi_linker_it;
                        if self.requires_adding_successor_connected_nominals(
                            source_individual,
                            adding_nominal_id,
                            calc_alg_context,
                        ) {
                            if calc_alg_context
                                .process_context_mut()
                                .sat_node_add_successor_connected_nominal(
                                    source_individual,
                                    adding_nominal_id,
                                )
                            {
                                self.successor_connected_nominal_updated_count += 1;
                            }
                            direct_update_linker.insert(0, source_individual);
                        }
                    }
                }
            }
        }
    }

    // =======================================================================
    // Group L — maximum-cardinality candidate propagation.
    // =======================================================================

    /// Port of `requiresMaxCardinalityCandidatePropagation` (cpp 7897–7902).
    pub fn requires_max_cardinality_candidate_propagation(
        &mut self,
        indi_node: SatNodeId,
        atleast_candidate: Cint64,
        atmost_candidate: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let node = calc_alg_context.process_context().sat_node(indi_node);
        atleast_candidate > node.get_max_atleast_cardinality_candidate()
            || atmost_candidate > node.get_max_atmost_cardinality_candidate()
    }

    /// Port of `updateMaxCardinalityCandidates` (cpp 7907–7967).
    ///
    /// KONCLUDE-PORT-NOTE[ownership]: the update-linker worklist collapses to a
    /// `Vec<SatNodeId>` LIFO stack. The copy-depending, role-backward-propagation,
    /// and non-inverse-connected fan-out arms are ported through the context-owned
    /// saturation satellites.
    pub fn update_max_cardinality_candidates(
        &mut self,
        indi_node: SatNodeId,
        atleast_candidate: Cint64,
        atmost_candidate: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.requires_max_cardinality_candidate_propagation(
            indi_node,
            atleast_candidate,
            atmost_candidate,
            calc_alg_context,
        ) {
            let mut direct_update_linker: Vec<SatNodeId> = vec![indi_node];
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(indi_node)
                .add_max_atleast_cardinality_candidate(atleast_candidate);
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(indi_node)
                .add_max_atmost_cardinality_candidate(atmost_candidate);

            while !direct_update_linker.is_empty() {
                let update_indi_node = direct_update_linker.remove(0);
                self.maximum_cardinality_candidates_updated_count += 1;

                let depending_indi_linker: Vec<NegLink<SatNodeId>> = calc_alg_context
                    .process_context()
                    .sat_node(update_indi_node)
                    .depending_indi_node_linker
                    .clone();
                for depending_indi_linker_it in depending_indi_linker {
                    let depending_indi = depending_indi_linker_it.target;
                    if self.requires_max_cardinality_candidate_propagation(
                        depending_indi,
                        atleast_candidate,
                        atmost_candidate,
                        calc_alg_context,
                    ) {
                        calc_alg_context
                            .process_context_mut()
                            .sat_node_mut(depending_indi)
                            .add_max_atleast_cardinality_candidate(atleast_candidate);
                        calc_alg_context
                            .process_context_mut()
                            .sat_node_mut(depending_indi)
                            .add_max_atmost_cardinality_candidate(atmost_candidate);
                        self.maximum_cardinality_candidates_updated_count += 1;
                        direct_update_linker.insert(0, depending_indi);
                    }
                }

                let update_is_abox = calc_alg_context
                    .process_context()
                    .sat_node(update_indi_node)
                    .abox_individual_representation_node;

                if !update_is_abox {
                    let backward_sources = calc_alg_context
                        .process_context()
                        .sat_node_role_backward_source_individuals(update_indi_node);
                    for source_individual in backward_sources {
                        if self.requires_max_cardinality_candidate_propagation(
                            source_individual,
                            atleast_candidate,
                            atmost_candidate,
                            calc_alg_context,
                        ) {
                            calc_alg_context
                                .process_context_mut()
                                .sat_node_mut(source_individual)
                                .add_max_atleast_cardinality_candidate(atleast_candidate);
                            calc_alg_context
                                .process_context_mut()
                                .sat_node_mut(source_individual)
                                .add_max_atmost_cardinality_candidate(atmost_candidate);
                            self.maximum_cardinality_candidates_updated_count += 1;
                            direct_update_linker.insert(0, source_individual);
                        }
                    }

                    let non_inv_conn_indi_linker: Vec<SatNodeId> = calc_alg_context
                        .process_context()
                        .sat_node(update_indi_node)
                        .non_inverse_connected_indi_node_linker
                        .clone();
                    for non_inv_conn_indi_linker_it in non_inv_conn_indi_linker {
                        let source_individual = non_inv_conn_indi_linker_it;
                        if self.requires_max_cardinality_candidate_propagation(
                            source_individual,
                            atleast_candidate,
                            atmost_candidate,
                            calc_alg_context,
                        ) {
                            calc_alg_context
                                .process_context_mut()
                                .sat_node_mut(source_individual)
                                .add_max_atleast_cardinality_candidate(atleast_candidate);
                            calc_alg_context
                                .process_context_mut()
                                .sat_node_mut(source_individual)
                                .add_max_atmost_cardinality_candidate(atmost_candidate);
                            self.maximum_cardinality_candidates_updated_count += 1;
                            direct_update_linker.insert(0, source_individual);
                        }
                    }
                }
            }
        }
    }
}
