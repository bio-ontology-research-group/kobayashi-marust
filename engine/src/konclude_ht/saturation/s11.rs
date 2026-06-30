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
//!     out in: `CReapplyConceptSaturationLabelSet` (insertConceptReturnClashed /
//!     insertConceptReapplicationReturnTriggered / hasModifiedUpdateLinkers),
//!     `CConceptSaturationDescriptor` (initConceptSaturationDescriptor / getConcept /
//!     getNegation), `CImplicationReapplyConceptSaturationDescriptor`,
//!     `CSaturationModifiedProcessUpdateLinker`, the per-node
//!     `CRoleBackwardSaturationPropagationHash` (the backward-prop fan-out arm),
//!     `CSuccessorConnectedNominalSet`, the nominal-handling data, and the
//!     `CSaturationNominalDependentNodeHash` / `CSaturationInfluencedNominalSet`
//!     membership ops; plus the consistence model chain (`CConcreteOntology` /
//!     `CConsistence` / `CConsistenceTaskData` / `CSatisfiableCalculationTask`).
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
    CCALL, CCAND, CCAQALL, CCAQAND, CCAQCHOOCE, CCAQSOME, CCBRANCHALL, CCBRANCHAQALL, CCBRANCHAQAND,
    CCBRANCHTRIG, CCIMPL, CCIMPLALL, CCIMPLAQALL, CCIMPLAQAND, CCIMPLTRIG, CCOR, CCSOME, CCSUB,
};
use super::super::model::substrate::{Cint64, Id, INVALID};
use super::super::model::{ConceptId, NegLink};
use super::super::process::sat_node::IndividualSaturationProcessNodeStatusFlags;
use super::super::process::stubs::{
    ConceptSaturationDescriptor, ConceptSaturationProcess, ConceptSaturationProcessLinkerId,
    IndividualSaturationSuccessorLinkData, ReapplyConceptSaturationLabelSetId, RoleSaturationProcess,
};
use super::super::process::SatNodeId;
// W4.5: the saturation-satellite linker structs (for the create*-pool allocations).
use super::satellites::{ConceptSaturationProcessLinker, RoleSaturationProcessLinker};

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
    pub fn has_flags(&self, flags: &IndividualSaturationProcessNodeStatusFlags, check_all_flags: bool) -> bool {
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
        // W4-DEFER[api]: conSatDes->clearNext();
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
        // W4-DEFER[api]: conSatProcLinker->clearNext();
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
        // W4-DEFER[api]: roleSatProcLinker->clearNext();
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
    ) -> Id<IndividualSaturationSuccessorLinkData> {
        let succ_link_data_linker = calc_alg_context
            .processing_data_box_mut()
            .take_remaining_individual_successor_link_data_linker();
        if succ_link_data_linker.is_none() {
            // W4-DEFER[memory-pool]: CObjectAllocator<CIndividualSaturationSuccessorLinkDataLinker>::allocateAndConstruct(taskMemMan)
        }
        succ_link_data_linker
    }

    /// Port of `releaseIndividualSaturationSuccessorLinkDataLinker` (cpp 7378–7384).
    pub fn release_individual_saturation_successor_link_data_linker(
        &mut self,
        succ_link_data_linker: Id<IndividualSaturationSuccessorLinkData>,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if succ_link_data_linker.is_some() {
            // W4-DEFER[api]: succLinkDataLinker->clearNext();
            calc_alg_context
                .processing_data_box_mut()
                .add_remaining_individual_successor_link_data_linker(succ_link_data_linker);
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
    ///
    /// KONCLUDE-PORT-NOTE[memory-pool]: `CSaturationModifiedProcessUpdateLinker` has
    /// no databox pool and no per-test arena yet; the fresh `CObjectAllocator`
    /// allocation is `W4-DEFER[memory-pool]` and the handle stays opaque
    /// (`Cint64`, `INVALID` == the unallocated `nullptr`).
    pub fn create_modified_process_update_linker(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // W4-DEFER[memory-pool]: CObjectAllocator<CSaturationModifiedProcessUpdateLinker>::allocateAndConstruct(taskMemMan)
        INVALID
    }

    /// Port of `createImplicationReapplyConceptSaturationDescriptor` (cpp 7415–7419).
    ///
    /// KONCLUDE-PORT-NOTE[memory-pool]: as above for
    /// `CImplicationReapplyConceptSaturationDescriptor` — opaque `Cint64` handle.
    pub fn create_implication_reapply_concept_saturation_descriptor(
        &mut self,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> Cint64 {
        // W4-DEFER[memory-pool]: CObjectAllocator<CImplicationReapplyConceptSaturationDescriptor>::allocateAndConstruct(taskMemMan)
        INVALID
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
            self.add_concept_filtered_to_individual(op_concept, op_con_negation, process_indi, calc_alg_context);
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
        let label_set = calc_alg_context
            .process_context()
            .sat_node(*process_indi)
            .reapply_con_sat_label_set;
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
        let label_set = calc_alg_context
            .process_context()
            .sat_node(*process_indi)
            .reapply_con_sat_label_set;
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
            if (!negate && (op_code == CCAND || op_code == CCAQAND || op_code == CCIMPLAQAND || op_code == CCBRANCHAQAND))
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

        let concept_saturation_descriptor = self.create_concept_saturation_descriptor(calc_alg_context);
        // W4-DEFER[api]: conceptSaturationDescriptor->initConceptSaturationDescriptor(addingConcept,negate)
        //   — CConceptSaturationDescriptor satellite not yet ported.

        let contained = self.insert_concept_to_individual_concept_set(
            concept_saturation_descriptor,
            root_process_indi,
            label_set,
            calc_alg_context,
        );
        if !contained {
            // STATINC(CONCEPTSADDEDINDINODEPROCESSINGQUEUECOUNT) + g_ksat_* — debug stats, elided.
            let concept_saturation_process_linker =
                self.create_concept_saturation_process_linker(calc_alg_context);
            // W4-DEFER[api]: conceptSaturationProcessLinker->initConceptSaturationProcessLinker(conceptSaturationDescriptor);
            // W4-DEFER[api]: rootProcessIndi->addConceptSaturationProcessLinker(conceptSaturationProcessLinker);
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
    /// PORT-PENDING — faithful structure recorded below. The operator-code
    /// dispatch and the label-set insertion both read the concept off the
    /// (unported) `CConceptSaturationDescriptor` (`getConcept()` / `getNegation()`),
    /// and the insertion bottoms out in the unported `CReapplyConceptSaturationLabelSet`
    /// (`insertConceptReturnClashed` / `hasModifiedUpdateLinkers` /
    /// `getModifiedUpdateLinker`) and `CImplicationReapplyConceptSaturationDescriptor`.
    /// The locally-resolvable read is `rootProcessIndi->getRequiredBackwardPropagation()`.
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
        let contained = false;
        // requiredBackProp = rootProcessIndi->getRequiredBackwardPropagation() (locally resolvable).
        let required_back_prop = calc_alg_context
            .process_context()
            .sat_node(*root_process_indi)
            .get_required_backward_propagation();
        // W4-DEFER[api]: concept = conceptSaturationDescriptor->getConcept(); conNeg = ...->getNegation();
        //   opCode = concept->getOperatorCode(); the operator-code branch counters
        //   (mAddedSUBConcepts/mAddedALLConcepts/mAddedSOMEConcepts/mAddedIMPLConcepts/
        //   mAddedTRIGGConcepts/mAddedELSEConcepts) + insertConcept/contained/
        //   implTriggerGeneration are set per the doc-comment transcription. The
        //   CConceptSaturationDescriptor concept resolution and the
        //   CReapplyConceptSaturationLabelSet insertion (insertConceptReturnClashed /
        //   reapply-trigger replay / hasModifiedUpdateLinkers) + the
        //   CImplicationReapplyConceptSaturationDescriptor seeding are unported; the
        //   `updateDirectAddingIndividualStatusFlags(.., INDSATFLAGCLASHED)` /
        //   `processModificationUpdateLinkers` / `hasConceptLocalImpact` /
        //   `updateImplicationReapplyConceptSaturationDescriptor` leaves are siblings.
        let _ = (concept_saturation_descriptor, label_set, required_back_prop);
        contained
    }

    /// Port of `processModificationUpdateLinkers` (cpp 7540–7548).
    ///
    /// PORT-PENDING — the `CSaturationModifiedProcessUpdateLinker` chain (opaque
    /// `Cint64` head) + its `getProcessingIndividual()` / `getUpdateType()` are
    /// unported; the only `UPDATEPDISJUNCTCOMMONCONCEPTSEXTRACTION` branch calls the
    /// sibling `addDisjunctCommonConceptExtractionToProcessingQueue` (group I,
    /// PU-SAT-9).
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
        mod_proc_update_linker: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: the CSaturationModifiedProcessUpdateLinker chain + its
        //   per-element processing-individual / update-type; the
        //   UPDATEPDISJUNCTCOMMONCONCEPTSEXTRACTION branch is
        //   self.add_disjunct_common_concept_extraction_to_processing_queue(indiProcNode, ctx).
        let _ = (&mut *root_process_indi, label_set, mod_proc_update_linker, &mut *calc_alg_context);
    }

    /// Port of `updateImplicationReapplyConceptSaturationDescriptor` (cpp 7552–7576).
    ///
    /// PORT-PENDING — operates entirely on the unported
    /// `CImplicationReapplyConceptSaturationDescriptor` (`getNextTriggerConcept` /
    /// `getImplicationConcept` / `initImplicationReapllyConceptSaturationDescriptor`)
    /// and `CReapplyConceptSaturationLabelSet`
    /// (`insertConceptReapplicationReturnTriggered`); the implication-execution leaf
    /// is `addConceptFilteredToIndividual(... ,false)` (sibling).
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
        reapply_imp_reapply_con_sat_des: Cint64,
        root_process_indi: &mut SatNodeId,
        label_set: ReapplyConceptSaturationLabelSetId,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        // STATINC(IMPLICATIONTRIGGERINGCOUNT) / IMPLICATIONEXECUTINGCOUNT — debug stats, elided.
        // W4-DEFER[api]: CImplicationReapplyConceptSaturationDescriptor +
        //   CReapplyConceptSaturationLabelSet reapplication; the execution leaf is the
        //   sibling self.add_concept_filtered_to_individual_label_set(..., false, ctx).
        let _ = (reapply_imp_reapply_con_sat_des, &mut *root_process_indi, label_set, &mut *calc_alg_context);
        true
    }

    /// Port of `hasConceptLocalImpact` (cpp 7579–7623).
    pub fn has_concept_local_impact(
        &mut self,
        concept: ConceptId,
        con_neg: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        let op_code = calc_alg_context.ontology_arenas().concept(concept).get_operator_code();
        if op_code == CCSUB || op_code == CCIMPLTRIG || op_code == CCBRANCHTRIG {
            true
        } else if (!con_neg && (op_code == CCALL || op_code == CCIMPLALL || op_code == CCBRANCHALL))
            || (con_neg && op_code == CCSOME)
        {
            false
        } else if (!con_neg && (op_code == CCAND || op_code == CCAQAND || op_code == CCBRANCHAQAND || op_code == CCIMPLAQAND))
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
        } else if (!con_neg && (op_code == CCSOME || op_code == CCAQSOME)) || (con_neg && op_code == CCALL) {
            true
        } else if (!con_neg && (op_code == CCAQALL || op_code == CCIMPLAQALL || op_code == CCBRANCHAQALL))
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
                if op_negation == con_neg && self.has_concept_local_impact(op_concept, false, calc_alg_context) {
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
        let nominal_dependent_node_hash = calc_alg_context
            .processing_data_box_mut()
            .saturation_nominal_dependent_node_hash(true);
        // W4-DEFER[api]: nominalDependentNodeHash->addNominalDependentNode(nominalID,dependentIndiNode,connectionType)
        let influenced_nominal_set = calc_alg_context
            .processing_data_box_mut()
            .saturation_influenced_nominal_set(true);
        // W4-DEFER[api]: is_nominal_influenced = influencedNominalSet->isNominalInfluenced(nominalID);
        //   CSaturationInfluencedNominalSet membership op unported, stays `false`.
        let is_nominal_influenced = false;
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
        let influenced_nominal_set = calc_alg_context
            .processing_data_box_mut()
            .saturation_influenced_nominal_set(true);
        // W4-DEFER[api]: firstInfluence = influencedNominalSet->setNominalInfluenced(influencedNominalID);
        //   CSaturationInfluencedNominalSet op unported, stays `false`.
        let first_influence = false;
        if first_influence {
            let nominal_dependent_node_hash = calc_alg_context
                .processing_data_box_mut()
                .saturation_nominal_dependent_node_hash(true);
            // W4-DEFER[api]: for (nominalDepNodeDataIt = nominalDependentNodeHash
            //     ->getNominalDependentNodeData(influencedNominalID); nominalDepNodeDataIt;
            //     nominalDepNodeDataIt = nominalDepNodeDataIt->getNext()) {
            //   dependentIndSatProcNode = nominalDepNodeDataIt->getDependentIndividualSaturationNode();
            //   self.update_direct_adding_individual_status_flags(dependentIndSatProcNode, INDSATFLAGINSUFFICIENT, ctx);
            //   self.set_insufficient_node_occured(ctx);
            // } — CSaturationNominalDependentNodeData chain unported.
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
        let nom_delayed_con_sat_proc_linker = self.create_concept_saturation_process_linker(calc_alg_context);
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
        self.update_direct_adding_individual_status_flags_with_flags(indi_node, &adding_flags, calc_alg_context);
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
        if self.requires_direct_adding_individual_status_flags_update(indi_node, adding_flags, calc_alg_context) {
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
                    if self.requires_direct_adding_individual_status_flags_update(depending_indi, adding_flags, calc_alg_context) {
                        calc_alg_context
                            .process_context_mut()
                            .sat_node_mut(depending_indi)
                            .direct_status_flags
                            .add_flags(adding_flags);
                        self.direct_updated_status_indi_node_count += 1;
                        direct_update_linker.insert(0, depending_indi);
                    }
                }

                self.update_indirect_adding_individual_status_flags(update_indi_node, adding_flags, calc_alg_context);
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
        if self.requires_direct_adding_individual_status_flags_update(indi_node, adding_flags, calc_alg_context) {
            calc_alg_context
                .process_context_mut()
                .sat_node_mut(indi_node)
                .direct_status_flags
                .add_flags(adding_flags);
            if self.requires_indirect_adding_individual_status_flags_update(indi_node, adding_flags, calc_alg_context) {
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
                // W4-DEFER[api]: backwardPropHash = indiNode->getRoleBackwardPropagationHash(false);
                //   if backwardPropHash: for each (role -> backwardPropData.mLinkLinker -> link):
                //     sourceIndividual = link->getSourceIndividual();
                //     self.update_indirect_adding_individual_status_flags(sourceIndividual, addingFlags, ctx);
                //   — CRoleBackwardSaturationPropagationHash satellite unported.

                // non-inverse-connected fan-out (getNonInverseConnectedIndividualNodeLinker):
                let non_inv_conn_indi_linker: Vec<SatNodeId> = calc_alg_context
                    .process_context()
                    .sat_node(indi_node)
                    .non_inverse_connected_indi_node_linker
                    .clone();
                for non_inv_conn_indi_linker_it in non_inv_conn_indi_linker {
                    let source_individual = non_inv_conn_indi_linker_it;
                    self.update_indirect_adding_individual_status_flags(source_individual, adding_flags, calc_alg_context);
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
        if self.requires_indirect_adding_individual_status_flags_update(indi_node, adding_flags, calc_alg_context) {
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
                    if self.requires_indirect_adding_individual_status_flags_update(depending_indi, adding_flags, calc_alg_context) {
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

                // W4-DEFER[api]: if backwardPropHash(update) && !update_is_abox:
                //   for each (role -> backwardPropData.mLinkLinker -> link):
                //     sourceIndividual = link->getSourceIndividual();
                //     if requires_indirect(sourceIndividual): add INDIRECT flags; ++count; push sourceIndividual.

                if !update_is_abox {
                    let non_inv_conn_indi_linker: Vec<SatNodeId> = calc_alg_context
                        .process_context()
                        .sat_node(update_indi_node)
                        .non_inverse_connected_indi_node_linker
                        .clone();
                    for non_inv_conn_indi_linker_it in non_inv_conn_indi_linker {
                        let source_individual = non_inv_conn_indi_linker_it;
                        if self.requires_indirect_adding_individual_status_flags_update(source_individual, adding_flags, calc_alg_context) {
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
        // W4-DEFER[api]: succConnNomSet = indiNode->getSuccessorConnectedNominalSet(false);
        //   if succConnNomSet && succConnNomSet->hasSuccessorConnectedNominal(addingNominalID): return false;
        //   CSuccessorConnectedNominalSet satellite unported, so the membership test is
        //   treated as absent (returns true — "requires adding").
        let _ = (indi_node, adding_nominal_id, &mut *calc_alg_context);
        true
    }

    /// Port of `updateAddingSuccessorConnectedNominal` — the set-iterating overload
    /// (cpp 7809–7816).
    pub fn update_adding_successor_connected_nominal_set(
        &mut self,
        indi_node: SatNodeId,
        succ_conn_nom_set: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        // W4-DEFER[api]: for connectedNominalID in succConnNomSet:
        //   self.update_adding_successor_connected_nominal(indiNode, connectedNominalID, ctx);
        //   — CSuccessorConnectedNominalSet iteration unported.
        let _ = (indi_node, succ_conn_nom_set, &mut *calc_alg_context);
    }

    /// Port of `updateAddingSuccessorConnectedNominal` — the `cint64 addingNominalID`
    /// worklist (cpp 7819–7880).
    ///
    /// PORT-PENDING — faithful structure recorded below. The worklist body mutates
    /// each node's `CSuccessorConnectedNominalSet` (lazy
    /// `getSuccessorConnectedNominalSet(true)->addSuccessorConnectedNominal(id)`);
    /// the set satellite is unported, and `requiresAddingSuccessorConnectedNominals`
    /// (also unported) gates every step, so the worklist cannot terminate faithfully
    /// yet. The copy-depending / role-backward-prop-hash / non-inverse-connected
    /// fan-out structure mirrors `updateIndirectAddingIndividualStatusFlags`.
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
        // W4-DEFER[api]: CSuccessorConnectedNominalSet (membership + add) +
        //   CRoleBackwardSaturationPropagationHash unported; worklist deferred per the
        //   doc-comment transcription. The portable arms (copy-depending /
        //   non-inverse-connected) mirror update_indirect_adding_individual_status_flags.
        let _ = (indi_node, adding_nominal_id, &mut *calc_alg_context);
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
    /// `Vec<SatNodeId>` LIFO stack. The copy-depending and non-inverse-connected
    /// fan-out arms are ported; the role-backward-propagation hash arm is
    /// `W4-DEFER[api]`. The per-node `addMaxAtleast/AtmostCardinalityCandidate`
    /// mutators are sat-node methods scheduled for SAT-1; they are referenced by
    /// name (reconciled when the node unit lands) so the candidate semantics are not
    /// guessed here.
    pub fn update_max_cardinality_candidates(
        &mut self,
        indi_node: SatNodeId,
        atleast_candidate: Cint64,
        atmost_candidate: Cint64,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) {
        if self.requires_max_cardinality_candidate_propagation(indi_node, atleast_candidate, atmost_candidate, calc_alg_context) {
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
                    if self.requires_max_cardinality_candidate_propagation(depending_indi, atleast_candidate, atmost_candidate, calc_alg_context) {
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

                // W4-DEFER[api]: if backwardPropHash(update) && !update_is_abox:
                //   for each (role -> backwardPropData.mLinkLinker -> link):
                //     sourceIndividual = link->getSourceIndividual();
                //     if requires(sourceIndividual): source.add_max_atleast/atmost; ++count; push.

                if !update_is_abox {
                    let non_inv_conn_indi_linker: Vec<SatNodeId> = calc_alg_context
                        .process_context()
                        .sat_node(update_indi_node)
                        .non_inverse_connected_indi_node_linker
                        .clone();
                    for non_inv_conn_indi_linker_it in non_inv_conn_indi_linker {
                        let source_individual = non_inv_conn_indi_linker_it;
                        if self.requires_max_cardinality_candidate_propagation(source_individual, atleast_candidate, atmost_candidate, calc_alg_context) {
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
