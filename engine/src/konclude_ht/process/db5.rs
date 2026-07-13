//! `process/db5.rs` — method-batch unit **DB-5**: the `CProcessingDataBox`
//! saturation subsystem.
//!
//! Port of `Source/Reasoner/Kernel/Process/CProcessingDataBox.cpp` lines
//! 1680–2143: the saturation process-node / completion / completed / analysing /
//! nominal-delayed / ATMOST-merging linker chains, the remaining-saturation
//! work linkers (concept-saturation process / status-update / concept-descriptor /
//! concept-saturation-descriptor / role-saturation process), and the six
//! lazily-allocated saturation satellites (`mIndiSaturationProcessVector`,
//! `mSatCriticalIndiNodeConTestSet`, `mSatNominalDependentNodeHash`,
//! `mSatInfluencedNominalSet`, `mSatSuccExtIndNodeProcQueue`,
//! `mSatCriticalIndiNodeProcQueue`) — the lazy-getters DB-1's parent→child
//! handoff defers to (`init_processing_data_box_parent`, `.cpp` 519–536).
//!
//! Skipped (already ported in `databox.rs`): the occurred-flag accessors
//! `isInsufficientNodeOccured`/`setInsufficientNodeOccured` (1928),
//! `isProblematicEQCandidateOccured`/`setProblematicEQCandidateOccured` (1937),
//! `isDelayedNominalProcessingOccured`/`setDelayedNominalProcessingOccured`
//! (1947), and `getSeparatedSaturationConceptAssertionResolveNode`/
//! `setSeparatedSaturationConceptAssertionResolveNode` (2136).
//!
//! KONCLUDE-PORT-NOTE[ownership]: Konclude holds each `mX` as the *head pointer*
//! of an intrusive singly-linked `CIndividualSaturationProcessNodeLinker` (or
//! status-update / concept-saturation / concept-descriptor / role-saturation
//! linker) chain; `addX(l)` is `mX = l->append(mX)` (prepend, newest at head) and
//! `takeX()` pops the head, advancing to `getNext()`. Per the global substrate
//! decision (`model/substrate.rs`) each chain collapses to an owned `Vec` of the
//! element id. Process/disjunct-common/nominal-delayed/completion/completed queues now retain the real
//! `CIndividualSaturationProcessNodeLinker*` id because their linker substrate is
//! ported; the other queues remain collapsed until their exact linker/queued
//! state is available.
//!
//! KONCLUDE-PORT-NOTE[ownership→resolved]: ALIGNED to the canonical linker
//! convention (CLinker.cpp, confirmed by DB-6, recorded in `PORT.md`): the chain
//! head is at the **FRONT** of the `Vec`, so `add* == insert(0, …)` (front-splice,
//! newest at head, matching `append`/prepend), `take* == remove(0)` (pop head,
//! advance), `set* == replace`. This file originally modelled the head at the
//! Vec's back (`push`/`pop`); the take ORDER (LIFO) is identical either way, but
//! `getX` now returns the chain head→tail, matching db4/db6 and the C++
//! traversal. `setX(v)` still installs a single-element chain (or empty for
//! `Id::NONE`), since the collapsed model has no linker identity to splice a
//! multi-element chain from one id.
//!
//! KONCLUDE-PORT-NOTE[api]: the status-update chain is C++
//! `CIndividualSaturationProcessNodeStatusUpdateLinker*`; per `databox.rs` its
//! per-element status payload is collapsed and the chain is modelled as the
//! sat-node chain (`Vec<SatNodeId>`).

#![allow(dead_code)]

use super::super::model::substrate::Id;
use super::context::ProcessContext;
use super::databox::ProcessingDataBox;
use super::sat_linker::{
    IndividualSaturationProcessNodeLinker, IndividualSaturationProcessNodeLinkerId,
};
use super::sat_node_vector::IndividualSaturationProcessNodeVector;
use super::sat_nominal::{SaturationInfluencedNominalSet, SaturationNominalDependentNodeHash};
use super::sat_queue::{
    CriticalIndividualNodeConceptTestSet, CriticalIndividualNodeProcessingQueue,
};
use super::stubs::{
    ConceptSaturationDescriptor, ConceptSaturationProcess, RoleSaturationProcess,
    SaturationSuccessorExtensionIndividualNodeProcessingQueue,
};
use super::{ConDescId, SatNodeId};

impl ProcessingDataBox {
    // ======================================================================
    // mIndiSaturationProcessVector — lazy satellite (`.cpp` 1680).
    // ======================================================================

    /// Port of `CProcessingDataBox::getIndividualSaturationProcessNodeVector`.
    pub fn individual_saturation_process_node_vector(
        &mut self,
        create: bool,
    ) -> Option<&mut IndividualSaturationProcessNodeVector> {
        if self.indi_saturation_process_vector.is_none() && create {
            self.indi_saturation_process_vector =
                Some(IndividualSaturationProcessNodeVector::new());
        }
        self.indi_saturation_process_vector.as_mut()
    }

    /// Immutable borrow of the saturation-process vector, matching a `false`
    /// `getIndividualSaturationProcessNodeVector(false)` call-site.
    pub fn individual_saturation_process_node_vector_ref(
        &self,
    ) -> Option<&IndividualSaturationProcessNodeVector> {
        self.indi_saturation_process_vector.as_ref()
    }

    // ======================================================================
    // mIndiSaturationProcessNodeLinker — chain (`.cpp` 1687).
    // ======================================================================

    /// Port of `CProcessingDataBox::hasIndividualSaturationProcessNodeLinker`.
    pub fn has_individual_saturation_process_node_linker(&self) -> bool {
        !self.indi_saturation_process_node_linker.is_empty()
    }
    /// Port of `CProcessingDataBox::getIndividualSaturationProcessNodeLinker`.
    pub fn individual_saturation_process_node_linker(
        &self,
    ) -> Vec<IndividualSaturationProcessNodeLinkerId> {
        self.indi_saturation_process_node_linker
            .iter()
            .rev()
            .copied()
            .collect()
    }
    /// Port of `CProcessingDataBox::takeIndividualSaturationProcessNodeLinker`.
    pub fn take_individual_saturation_process_node_linker(
        &mut self,
    ) -> IndividualSaturationProcessNodeLinkerId {
        if self.indi_saturation_process_node_linker.is_empty() {
            IndividualSaturationProcessNodeLinkerId::NONE
        } else {
            self.indi_saturation_process_node_linker
                .pop()
                .expect("non-empty saturation process stack")
        }
    }
    /// Port of `CProcessingDataBox::setIndividualSaturationProcessNodeLinker`.
    pub fn set_individual_saturation_process_node_linker(
        &mut self,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.indi_saturation_process_node_linker.clear();
        if v.is_some() {
            self.indi_saturation_process_node_linker.push(v);
        }
        self
    }
    /// Port of `CProcessingDataBox::addIndividualSaturationProcessNodeLinker`.
    pub fn add_individual_saturation_process_node_linker(
        &mut self,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        // C++ prepends to a singly linked list and removes its head. Store the
        // head at the Vec tail so both operations remain O(1); the previous
        // insert(0)/remove(0) representation shifted the full queue for every
        // resolved successor-extension node.
        self.indi_saturation_process_node_linker.push(v);
        self
    }

    // ======================================================================
    // mDisjunctCommonConceptExtractProcessingLinker — chain (`.cpp` 1718).
    // ======================================================================

    /// Port of `CProcessingDataBox::hasIndividualDisjunctCommonConceptExtractProcessLinker`.
    pub fn has_individual_disjunct_common_concept_extract_process_linker(&self) -> bool {
        !self
            .disjunct_common_concept_extract_processing_linker
            .is_empty()
    }
    /// Port of `CProcessingDataBox::getIndividualDisjunctCommonConceptExtractProcessLinker`.
    pub fn individual_disjunct_common_concept_extract_process_linker(
        &self,
    ) -> &[IndividualSaturationProcessNodeLinkerId] {
        &self.disjunct_common_concept_extract_processing_linker
    }
    /// Port of `CProcessingDataBox::takeIndividualDisjunctCommonConceptExtractProcessLinker`.
    pub fn take_individual_disjunct_common_concept_extract_process_linker(
        &mut self,
    ) -> IndividualSaturationProcessNodeLinkerId {
        if self
            .disjunct_common_concept_extract_processing_linker
            .is_empty()
        {
            IndividualSaturationProcessNodeLinkerId::NONE
        } else {
            self.disjunct_common_concept_extract_processing_linker
                .remove(0)
        }
    }
    /// Port of `CProcessingDataBox::setIndividualDisjunctCommonConceptExtractProcessLinker`.
    pub fn set_individual_disjunct_common_concept_extract_process_linker(
        &mut self,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.disjunct_common_concept_extract_processing_linker
            .clear();
        if v.is_some() {
            self.disjunct_common_concept_extract_processing_linker
                .push(v);
        }
        self
    }
    /// Port of `CProcessingDataBox::addIndividualDisjunctCommonConceptExtractProcessLinker`.
    pub fn add_individual_disjunct_common_concept_extract_process_linker(
        &mut self,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.disjunct_common_concept_extract_processing_linker
            .insert(0, v);
        self
    }

    // ======================================================================
    // mRemConSatProcessLinker — remaining concept-saturation process (`.cpp` 1749).
    // ======================================================================

    /// Port of `CProcessingDataBox::getRemainingConceptSaturationProcessLinker`.
    pub fn remaining_concept_saturation_process_linker(&self) -> &[Id<ConceptSaturationProcess>] {
        &self.rem_con_sat_process_linker
    }
    /// Port of `CProcessingDataBox::takeRemainingConceptSaturationProcessLinker`.
    pub fn take_remaining_concept_saturation_process_linker(
        &mut self,
    ) -> Id<ConceptSaturationProcess> {
        self.rem_con_sat_process_linker.pop().unwrap_or(Id::NONE)
    }
    /// Port of `CProcessingDataBox::setRemainingConceptSaturationProcessLinker`.
    pub fn set_remaining_concept_saturation_process_linker(
        &mut self,
        v: Id<ConceptSaturationProcess>,
    ) -> &mut Self {
        self.rem_con_sat_process_linker.clear();
        if v.is_some() {
            self.rem_con_sat_process_linker.push(v);
        }
        self
    }
    /// Port of `CProcessingDataBox::addRemainingConceptSaturationProcessLinker`.
    pub fn add_remaining_concept_saturation_process_linker(
        &mut self,
        v: Id<ConceptSaturationProcess>,
    ) -> &mut Self {
        // Konclude stores this as an intrusive free-list: release prepends and
        // acquire removes the head, both O(1). Keep that head at the Vec tail
        // so `push`/`pop` preserve the exact LIFO order without shifting the
        // growing pool on every critical-concept descriptor release.
        self.rem_con_sat_process_linker.push(v);
        self
    }

    // ======================================================================
    // mRemSatUpdateLinker — remaining saturation status-update (`.cpp` 1762).
    // KONCLUDE-PORT-NOTE[api]: status-update payload collapsed to the sat-node chain.
    // ======================================================================

    /// Port of `CProcessingDataBox::getRemainingIndividualSaturationUpdateLinker`.
    pub fn remaining_individual_saturation_update_linker(&self) -> &[SatNodeId] {
        &self.rem_sat_update_linker
    }
    /// Port of `CProcessingDataBox::takeRemainingIndividualSaturationUpdateLinker`.
    pub fn take_remaining_individual_saturation_update_linker(&mut self) -> SatNodeId {
        if self.rem_sat_update_linker.is_empty() {
            SatNodeId::NONE
        } else {
            self.rem_sat_update_linker.remove(0)
        }
    }
    /// Port of `CProcessingDataBox::addRemainingIndividualSaturationUpdateLinker`.
    pub fn add_remaining_individual_saturation_update_linker(&mut self, v: SatNodeId) -> &mut Self {
        self.rem_sat_update_linker.insert(0, v);
        self
    }
    /// Port of `CProcessingDataBox::setRemainingIndividualSaturationUpdateLinker`.
    pub fn set_remaining_individual_saturation_update_linker(&mut self, v: SatNodeId) -> &mut Self {
        self.rem_sat_update_linker.clear();
        if v.is_some() {
            self.rem_sat_update_linker.push(v);
        }
        self
    }

    // ======================================================================
    // mRemConDes — remaining concept-descriptor (`.cpp` 1796).
    // ======================================================================

    /// Port of `CProcessingDataBox::getRemainingConceptDescriptor`.
    pub fn remaining_concept_descriptor(&self) -> &[ConDescId] {
        &self.rem_con_des
    }
    /// Port of `CProcessingDataBox::takeRemainingConceptDescriptor`.
    pub fn take_remaining_concept_descriptor(&mut self) -> ConDescId {
        if self.rem_con_des.is_empty() {
            ConDescId::NONE
        } else {
            self.rem_con_des.remove(0)
        }
    }
    /// Port of `CProcessingDataBox::setRemainingConceptDescriptor`.
    pub fn set_remaining_concept_descriptor(&mut self, v: ConDescId) -> &mut Self {
        self.rem_con_des.clear();
        if v.is_some() {
            self.rem_con_des.push(v);
        }
        self
    }
    /// Port of `CProcessingDataBox::addRemainingConceptDescriptor`.
    pub fn add_remaining_concept_descriptor(&mut self, v: ConDescId) -> &mut Self {
        self.rem_con_des.insert(0, v);
        self
    }

    // ======================================================================
    // mRemConSatDes — remaining concept-saturation-descriptor (`.cpp` 1824).
    // ======================================================================

    /// Port of `CProcessingDataBox::getRemainingConceptSaturationDescriptor`.
    pub fn remaining_concept_saturation_descriptor(&self) -> &[Id<ConceptSaturationDescriptor>] {
        &self.rem_con_sat_des
    }
    /// Port of `CProcessingDataBox::takeRemainingConceptSaturationDescriptor`.
    pub fn take_remaining_concept_saturation_descriptor(
        &mut self,
    ) -> Id<ConceptSaturationDescriptor> {
        if self.rem_con_sat_des.is_empty() {
            Id::NONE
        } else {
            self.rem_con_sat_des.remove(0)
        }
    }
    /// Port of `CProcessingDataBox::setRemainingConceptSaturationDescriptor`.
    pub fn set_remaining_concept_saturation_descriptor(
        &mut self,
        v: Id<ConceptSaturationDescriptor>,
    ) -> &mut Self {
        self.rem_con_sat_des.clear();
        if v.is_some() {
            self.rem_con_sat_des.push(v);
        }
        self
    }
    /// Port of `CProcessingDataBox::addRemainingConceptSaturationDescriptor`.
    pub fn add_remaining_concept_saturation_descriptor(
        &mut self,
        v: Id<ConceptSaturationDescriptor>,
    ) -> &mut Self {
        self.rem_con_sat_des.insert(0, v);
        self
    }

    // ======================================================================
    // mRemRoleSatProcessLinker — remaining role-saturation process (`.cpp` 1849).
    // ======================================================================

    /// Port of `CProcessingDataBox::getRemainingRoleSaturationProcessLinker`.
    pub fn remaining_role_saturation_process_linker(&self) -> &[Id<RoleSaturationProcess>] {
        &self.rem_role_sat_process_linker
    }
    /// Port of `CProcessingDataBox::takeRemainingRoleSaturationProcessLinker`.
    pub fn take_remaining_role_saturation_process_linker(&mut self) -> Id<RoleSaturationProcess> {
        if self.rem_role_sat_process_linker.is_empty() {
            Id::NONE
        } else {
            self.rem_role_sat_process_linker.remove(0)
        }
    }
    /// Port of `CProcessingDataBox::setRemainingRoleSaturationProcessLinker`.
    pub fn set_remaining_role_saturation_process_linker(
        &mut self,
        v: Id<RoleSaturationProcess>,
    ) -> &mut Self {
        self.rem_role_sat_process_linker.clear();
        if v.is_some() {
            self.rem_role_sat_process_linker.push(v);
        }
        self
    }
    /// Port of `CProcessingDataBox::addRemainingRoleSaturationProcessLinker`.
    pub fn add_remaining_role_saturation_process_linker(
        &mut self,
        v: Id<RoleSaturationProcess>,
    ) -> &mut Self {
        self.rem_role_sat_process_linker.insert(0, v);
        self
    }

    // ======================================================================
    // mSatCriticalIndiNodeConTestSet — lazy satellite (`.cpp` 1879).
    // ======================================================================

    /// Port of `CProcessingDataBox::getSaturationCriticalIndividualNodeConceptTestSet`.
    pub fn saturation_critical_individual_node_concept_test_set(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<CriticalIndividualNodeConceptTestSet> {
        ctx.processing_data_box_saturation_critical_individual_node_concept_test_set(self, create)
    }

    // ======================================================================
    // mSatNominalDependentNodeHash — lazy satellite (`.cpp` 1890).
    // ======================================================================

    /// Port of `CProcessingDataBox::getSaturationNominalDependentNodeHash`.
    pub fn saturation_nominal_dependent_node_hash(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<SaturationNominalDependentNodeHash> {
        ctx.processing_data_box_saturation_nominal_dependent_node_hash(self, create)
    }

    // ======================================================================
    // mSatInfluencedNominalSet — lazy satellite (`.cpp` 1900).
    // ======================================================================

    /// Port of `CProcessingDataBox::getSaturationInfluencedNominalSet`.
    pub fn saturation_influenced_nominal_set(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<SaturationInfluencedNominalSet> {
        ctx.processing_data_box_saturation_influenced_nominal_set(self, create)
    }

    // ======================================================================
    // mSatSuccExtIndNodeProcQueue — lazy satellite (`.cpp` 1911).
    // ======================================================================

    /// Port of `CProcessingDataBox::getSaturationSucessorExtensionIndividualNodeProcessingQueue`.
    pub fn saturation_sucessor_extension_individual_node_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<SaturationSuccessorExtensionIndividualNodeProcessingQueue> {
        ctx.processing_data_box_saturation_successor_extension_individual_node_processing_queue(
            self, create,
        )
    }

    // ======================================================================
    // mSatCriticalIndiNodeProcQueue — lazy satellite (`.cpp` 1919).
    // ======================================================================

    /// Port of `CProcessingDataBox::getSaturationCriticalIndividualNodeProcessingQueue`.
    pub fn saturation_critical_individual_node_processing_queue(
        &mut self,
        ctx: &mut ProcessContext,
        create: bool,
    ) -> Id<CriticalIndividualNodeProcessingQueue> {
        ctx.processing_data_box_saturation_critical_individual_node_processing_queue(self, create)
    }

    // `.cpp` 1928–1954: isInsufficientNodeOccured / setInsufficientNodeOccured /
    // isProblematicEQCandidateOccured / setProblematicEQCandidateOccured /
    // isDelayedNominalProcessingOccured / setDelayedNominalProcessingOccured —
    // already ported in `databox.rs`; skipped here.

    // ======================================================================
    // mIndiSaturationCompletionNodeLinker — chain (`.cpp` 1958).
    // ======================================================================

    /// Port of `CProcessingDataBox::hasIndividualSaturationCompletionNodeLinker`.
    pub fn has_individual_saturation_completion_node_linker(&self) -> bool {
        !self.indi_saturation_completion_node_linker.is_empty()
    }
    /// Port of `CProcessingDataBox::getIndividualSaturationCompletionNodeLinker`.
    pub fn individual_saturation_completion_node_linker(
        &self,
    ) -> &[IndividualSaturationProcessNodeLinkerId] {
        &self.indi_saturation_completion_node_linker
    }
    /// Port of `CProcessingDataBox::takeIndividualSaturationCompletionNodeLinker`.
    pub fn take_individual_saturation_completion_node_linker(
        &mut self,
    ) -> IndividualSaturationProcessNodeLinkerId {
        if self.indi_saturation_completion_node_linker.is_empty() {
            IndividualSaturationProcessNodeLinkerId::NONE
        } else {
            self.indi_saturation_completion_node_linker.remove(0)
        }
    }
    /// Port of `CProcessingDataBox::setIndividualSaturationCompletionNodeLinker`.
    pub fn set_individual_saturation_completion_node_linker(
        &mut self,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.indi_saturation_completion_node_linker.clear();
        if v.is_some() {
            self.indi_saturation_completion_node_linker.push(v);
        }
        self
    }
    /// Port of `CProcessingDataBox::addIndividualSaturationCompletionNodeLinker`.
    pub fn add_individual_saturation_completion_node_linker(
        &mut self,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.indi_saturation_completion_node_linker.insert(0, v);
        self
    }

    // ======================================================================
    // mIndiSaturationCompletedNodeLinker — chain (`.cpp` 1992).
    // ======================================================================

    /// Port of `CProcessingDataBox::hasIndividualSaturationCompletedNodeLinker`.
    pub fn has_individual_saturation_completed_node_linker(&self) -> bool {
        !self.indi_saturation_completed_node_linker.is_empty()
    }
    /// Port of `CProcessingDataBox::getIndividualSaturationCompletedNodeLinker`.
    pub fn individual_saturation_completed_node_linker(
        &self,
    ) -> &[IndividualSaturationProcessNodeLinkerId] {
        &self.indi_saturation_completed_node_linker
    }
    /// Port of `CProcessingDataBox::takeIndividualSaturationCompletedNodeLinker`.
    pub fn take_individual_saturation_completed_node_linker(
        &mut self,
    ) -> IndividualSaturationProcessNodeLinkerId {
        if self.indi_saturation_completed_node_linker.is_empty() {
            IndividualSaturationProcessNodeLinkerId::NONE
        } else {
            self.indi_saturation_completed_node_linker.remove(0)
        }
    }
    /// Port of `CProcessingDataBox::setIndividualSaturationCompletedNodeLinker`.
    pub fn set_individual_saturation_completed_node_linker(
        &mut self,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.indi_saturation_completed_node_linker.clear();
        if v.is_some() {
            self.indi_saturation_completed_node_linker.push(v);
        }
        self
    }
    /// Port of `CProcessingDataBox::addIndividualSaturationCompletedNodeLinker`.
    pub fn add_individual_saturation_completed_node_linker(
        &mut self,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.indi_saturation_completed_node_linker.insert(0, v);
        self
    }

    // ======================================================================
    // mIndiSaturationAnalysingNodeLinker — chain (`.cpp` 2026).
    // ======================================================================

    /// Port of `CProcessingDataBox::hasIndividualSaturationAnalysationNodeLinker`.
    pub fn has_individual_saturation_analysation_node_linker(&self) -> bool {
        !self.indi_saturation_analysing_node_linker.is_empty()
    }
    /// Port of `CProcessingDataBox::getIndividualSaturationAnalysationNodeLinker`.
    pub fn individual_saturation_analysation_node_linker(&self) -> &[SatNodeId] {
        &self.indi_saturation_analysing_node_linker
    }
    /// Port of `CProcessingDataBox::takeIndividualSaturationAnalysationNodeLinker`.
    pub fn take_individual_saturation_analysation_node_linker(&mut self) -> SatNodeId {
        if self.indi_saturation_analysing_node_linker.is_empty() {
            SatNodeId::NONE
        } else {
            self.indi_saturation_analysing_node_linker.remove(0)
        }
    }
    /// Port of `CProcessingDataBox::setIndividualSaturationAnalysationNodeLinker`.
    pub fn set_individual_saturation_analysation_node_linker(&mut self, v: SatNodeId) -> &mut Self {
        self.indi_saturation_analysing_node_linker.clear();
        if v.is_some() {
            self.indi_saturation_analysing_node_linker.push(v);
        }
        self
    }
    /// Port of `CProcessingDataBox::addIndividualSaturationAnalysationNodeLinker`.
    pub fn add_individual_saturation_analysation_node_linker(&mut self, v: SatNodeId) -> &mut Self {
        self.indi_saturation_analysing_node_linker.insert(0, v);
        self
    }

    // ======================================================================
    // mNominalDelayedIndiSaturationProcessNodeLinker — chain (`.cpp` 2061).
    // ======================================================================

    /// Port of `CProcessingDataBox::hasNominalDelayedIndividualSaturationProcessNodeLinker`.
    pub fn has_nominal_delayed_individual_saturation_process_node_linker(&self) -> bool {
        !self
            .nominal_delayed_indi_saturation_process_node_linker
            .is_empty()
    }
    /// Port of `CProcessingDataBox::getNominalDelayedIndividualSaturationProcessNodeLinker`.
    pub fn nominal_delayed_individual_saturation_process_node_linker(
        &self,
    ) -> &[IndividualSaturationProcessNodeLinkerId] {
        &self.nominal_delayed_indi_saturation_process_node_linker
    }
    /// Port of `CProcessingDataBox::takeNominalDelayedIndividualSaturationProcessNodeLinker`.
    pub fn take_nominal_delayed_individual_saturation_process_node_linker(
        &mut self,
    ) -> IndividualSaturationProcessNodeLinkerId {
        if self
            .nominal_delayed_indi_saturation_process_node_linker
            .is_empty()
        {
            IndividualSaturationProcessNodeLinkerId::NONE
        } else {
            self.nominal_delayed_indi_saturation_process_node_linker
                .remove(0)
        }
    }
    /// Port of `CProcessingDataBox::setNominalDelayedIndividualSaturationProcessNodeLinker`.
    pub fn set_nominal_delayed_individual_saturation_process_node_linker(
        &mut self,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.nominal_delayed_indi_saturation_process_node_linker
            .clear();
        if v.is_some() {
            self.nominal_delayed_indi_saturation_process_node_linker
                .push(v);
        }
        self
    }
    /// Port of `CProcessingDataBox::addNominalDelayedIndividualSaturationProcessNodeLinker`.
    pub fn add_nominal_delayed_individual_saturation_process_node_linker(
        &mut self,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.nominal_delayed_indi_saturation_process_node_linker
            .insert(0, v);
        self
    }

    // ======================================================================
    // mSaturationATMOSTMergingProcessLinker — chain (`.cpp` 2097).
    // ======================================================================

    /// Port of `CProcessingDataBox::hasSaturationATMOSTMergingProcessLinker`.
    pub fn has_saturation_atmost_merging_process_linker(&self) -> bool {
        self.saturation_atmost_merging_process_linker.is_some()
    }
    /// Port of `CProcessingDataBox::getSaturationATMOSTMergingProcessLinker`.
    pub fn saturation_atmost_merging_process_linker(
        &self,
    ) -> IndividualSaturationProcessNodeLinkerId {
        self.saturation_atmost_merging_process_linker
    }
    /// Port of `CProcessingDataBox::takeSaturationATMOSTMergingProcessLinker`.
    pub fn take_saturation_atmost_merging_process_linker(
        &mut self,
        ctx: &mut ProcessContext,
    ) -> IndividualSaturationProcessNodeLinkerId {
        let head = self.saturation_atmost_merging_process_linker;
        if head.is_some() {
            self.saturation_atmost_merging_process_linker =
                ctx.indi_sat_process_node_linker(head).get_next();
            ctx.indi_sat_process_node_linker_mut(head)
                .set_next(Id::NONE);
        }
        head
    }
    /// Port of `CProcessingDataBox::setSaturationATMOSTMergingProcessLinker`.
    pub fn set_saturation_atmost_merging_process_linker(
        &mut self,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        self.saturation_atmost_merging_process_linker = v;
        self
    }
    /// Port of `CProcessingDataBox::addSaturationATMOSTMergingProcessLinker`.
    pub fn add_saturation_atmost_merging_process_linker(
        &mut self,
        ctx: &mut ProcessContext,
        v: IndividualSaturationProcessNodeLinkerId,
    ) -> &mut Self {
        if v.is_some() {
            let old_head = self.saturation_atmost_merging_process_linker;
            ctx.indi_sat_process_node_linker_mut(v).set_next(old_head);
            self.saturation_atmost_merging_process_linker = v;
        }
        self
    }

    // `.cpp` 2136–2143: getSeparatedSaturationConceptAssertionResolveNode /
    // setSeparatedSaturationConceptAssertionResolveNode — already ported in
    // `databox.rs`; skipped here.
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn db5_process_linker_chain_uses_linker_ids_in_head_order() {
        let mut data_box = ProcessingDataBox::default();
        let first = IndividualSaturationProcessNodeLinkerId::new(11);
        let second = IndividualSaturationProcessNodeLinkerId::new(12);

        data_box.add_individual_saturation_process_node_linker(first);
        data_box.add_individual_saturation_process_node_linker(second);

        assert_eq!(
            data_box.individual_saturation_process_node_linker(),
            vec![second, first]
        );
        assert_eq!(
            data_box.take_individual_saturation_process_node_linker(),
            second
        );
        data_box.set_individual_saturation_process_node_linker(
            IndividualSaturationProcessNodeLinkerId::NONE,
        );
        assert!(!data_box.has_individual_saturation_process_node_linker());
    }

    #[test]
    fn db5_disjunct_extract_linker_chain_uses_linker_ids_in_head_order() {
        let mut data_box = ProcessingDataBox::default();
        let first = IndividualSaturationProcessNodeLinkerId::new(21);
        let second = IndividualSaturationProcessNodeLinkerId::new(22);

        data_box.add_individual_disjunct_common_concept_extract_process_linker(first);
        data_box.add_individual_disjunct_common_concept_extract_process_linker(second);

        assert_eq!(
            data_box.individual_disjunct_common_concept_extract_process_linker(),
            &[second, first]
        );
        assert_eq!(
            data_box.take_individual_disjunct_common_concept_extract_process_linker(),
            second
        );
        data_box.set_individual_disjunct_common_concept_extract_process_linker(
            IndividualSaturationProcessNodeLinkerId::NONE,
        );
        assert!(!data_box.has_individual_disjunct_common_concept_extract_process_linker());
    }

    #[test]
    fn db5_concept_saturation_process_free_list_is_lifo() {
        let mut data_box = ProcessingDataBox::default();
        let first = Id::<ConceptSaturationProcess>::new(41);
        let second = Id::<ConceptSaturationProcess>::new(42);

        data_box.add_remaining_concept_saturation_process_linker(first);
        data_box.add_remaining_concept_saturation_process_linker(second);

        assert_eq!(
            data_box.take_remaining_concept_saturation_process_linker(),
            second
        );
        assert_eq!(
            data_box.take_remaining_concept_saturation_process_linker(),
            first
        );
        assert!(data_box
            .take_remaining_concept_saturation_process_linker()
            .is_none());
    }

    #[test]
    fn db5_nominal_delayed_linker_chain_uses_linker_ids_in_head_order() {
        let mut data_box = ProcessingDataBox::default();
        let first = IndividualSaturationProcessNodeLinkerId::new(31);
        let second = IndividualSaturationProcessNodeLinkerId::new(32);

        data_box.add_nominal_delayed_individual_saturation_process_node_linker(first);
        data_box.add_nominal_delayed_individual_saturation_process_node_linker(second);

        assert_eq!(
            data_box.nominal_delayed_individual_saturation_process_node_linker(),
            &[second, first]
        );
        assert_eq!(
            data_box.take_nominal_delayed_individual_saturation_process_node_linker(),
            second
        );
        data_box.set_nominal_delayed_individual_saturation_process_node_linker(
            IndividualSaturationProcessNodeLinkerId::NONE,
        );
        assert!(!data_box.has_nominal_delayed_individual_saturation_process_node_linker());
    }

    #[test]
    fn db5_saturation_atmost_merging_process_linker_uses_intrusive_next_chain() {
        let mut ctx = ProcessContext::new();
        let mut data_box = ProcessingDataBox::default();
        let node_a = SatNodeId::new(101);
        let node_b = SatNodeId::new(102);

        let mut first = IndividualSaturationProcessNodeLinker::new();
        first.init_process_node_linker(node_a, true);
        let first = ctx.alloc_indi_sat_process_node_linker(first);
        let mut second = IndividualSaturationProcessNodeLinker::new();
        second.init_process_node_linker(node_b, false);
        let second = ctx.alloc_indi_sat_process_node_linker(second);

        data_box.set_saturation_atmost_merging_process_linker(first);
        data_box.add_saturation_atmost_merging_process_linker(&mut ctx, second);
        assert!(data_box.has_saturation_atmost_merging_process_linker());
        assert_eq!(data_box.saturation_atmost_merging_process_linker(), second);
        assert_eq!(
            ctx.indi_sat_process_node_linker(second)
                .get_processing_individual(),
            node_b
        );
        assert_eq!(ctx.indi_sat_process_node_linker(second).get_next(), first);
        assert!(ctx
            .indi_sat_process_node_linker(first)
            .is_processing_queued());

        assert_eq!(
            data_box.take_saturation_atmost_merging_process_linker(&mut ctx),
            second
        );
        assert!(ctx
            .indi_sat_process_node_linker(second)
            .get_next()
            .is_none());
        assert_eq!(data_box.saturation_atmost_merging_process_linker(), first);
        assert_eq!(
            data_box.take_saturation_atmost_merging_process_linker(&mut ctx),
            first
        );
        assert!(ctx.indi_sat_process_node_linker(first).get_next().is_none());
        assert!(!data_box.has_saturation_atmost_merging_process_linker());
        assert_eq!(
            data_box.take_saturation_atmost_merging_process_linker(&mut ctx),
            IndividualSaturationProcessNodeLinkerId::NONE
        );
    }

    #[test]
    fn db5_completion_linker_chain_uses_linker_ids_in_head_order() {
        let mut data_box = ProcessingDataBox::default();
        let first = IndividualSaturationProcessNodeLinkerId::new(1);
        let second = IndividualSaturationProcessNodeLinkerId::new(2);

        data_box.add_individual_saturation_completion_node_linker(first);
        data_box.add_individual_saturation_completion_node_linker(second);

        assert_eq!(
            data_box.individual_saturation_completion_node_linker(),
            &[second, first]
        );
        assert_eq!(
            data_box.take_individual_saturation_completion_node_linker(),
            second
        );
        assert_eq!(
            data_box.take_individual_saturation_completion_node_linker(),
            first
        );
        assert_eq!(
            data_box.take_individual_saturation_completion_node_linker(),
            IndividualSaturationProcessNodeLinkerId::NONE
        );
    }

    #[test]
    fn db5_completed_linker_chain_uses_linker_ids_in_head_order() {
        let mut data_box = ProcessingDataBox::default();
        let first = IndividualSaturationProcessNodeLinkerId::new(3);
        let second = IndividualSaturationProcessNodeLinkerId::new(4);

        data_box.set_individual_saturation_completed_node_linker(first);
        data_box.add_individual_saturation_completed_node_linker(second);

        assert_eq!(
            data_box.individual_saturation_completed_node_linker(),
            &[second, first]
        );
        data_box.set_individual_saturation_completed_node_linker(
            IndividualSaturationProcessNodeLinkerId::NONE,
        );
        assert!(!data_box.has_individual_saturation_completed_node_linker());
    }
}
