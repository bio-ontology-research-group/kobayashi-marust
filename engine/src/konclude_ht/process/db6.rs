//! `process/db6.rs` — method-batch unit **DB-6**: the `CProcessingDataBox`
//! incremental-expansion / possible-instance-merging / backend-cache /
//! referred-individual-tracking / remaining-saturation-linker methods.
//!
//! Port of `Source/Reasoner/Kernel/Process/CProcessingDataBox.cpp` lines
//! 2146–2517 (per `manifest/05-process-units.md`). Faithful, method-by-method:
//! snake_case names, original control flow preserved.
//!
//! Methods in this `.cpp` range that are pure trivial field get/set were already
//! ported in `databox.rs` and are NOT repeated here:
//!   `isIncrementalExpansionInitialised`/set, `getIncrementalExpansionID`/set,
//!   `getMaxIncrementalPreviousCompletionGraphNodeID`/set,
//!   `isIncrementalExpansionCompatibleMerged`/set,
//!   `isIncrementalExpansionCachingMerged`/set,
//!   `isIndividualDependenceTrackingRequired`/set,
//!   `has/get/set/clearBranchingInstruction`,
//!   `getRemainingPossibleInstanceIndividualMergingLimit`/set,
//!   `getPossibleInstanceIndividualMergedCount`/set,
//!   `getPossibleInstanceIndividualCurrentMergingCount`/set,
//!   `getPossibleInstanceIndividualMergingSize`/set,
//!   `isPossibleInstanceIndividualMergingStopped`/set,
//!   `getBackendCacheIntegratedIndividualNodeCount` (getter),
//!   `getBackendCacheIntegratedSameIndividualNodeCount` (getter),
//!   `has/setBackendCacheUpdateIndividualsInitialized`.
//!
//! KONCLUDE-PORT-NOTE[ownership]: Konclude's intrusive `CXLinker`/`C*Linker`
//! chains become owned `Vec`s (the global substrate decision). `append(head)`
//! splices the appending chain in front of the old head and returns it as the
//! new head, so the chain head is the most-recently-added element. To keep the
//! C++ iteration order (`get*` walks head → tail), the port stores the head at
//! the FRONT of the `Vec`: `add*` = `insert(0, …)` / front-splice, `take*` =
//! `remove(0)`, `set*` = replace. The take ORDER (LIFO) is identical to the C++.
//! This overrides the tentative "add == push" simplification noted in
//! `databox.rs`; only the in-memory layout differs, behaviour is preserved.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::databox::ProcessingDataBox;
use super::stubs::{
    BackendNeighbourExpansionControllingData, BackendNeighbourExpansionQueue,
    IndividualDelayedBackendInitializationProcessingQueue, IndividualSaturationSuccessorLinkData,
    IndividualRepresentativeBackendCacheConceptSetLabelProcessingHash,
    IndividualRepresentativeBackendCacheLoadedAssociationHash, ReferredIndividualTrackingVector,
};
use super::{NodeId, SatNodeId};

impl ProcessingDataBox {
    // ----------------------------------------------------------------------
    // id counters with optional increment (`.cpp` 2174–2189)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::getNextIncrementalIndividualExpansionID`.
    pub fn next_incremental_individual_expansion_id(&mut self, increment_next_id: bool) -> Cint64 {
        let next_id = self.next_incremental_indi_exp_id;
        if increment_next_id {
            self.next_incremental_indi_exp_id += 1;
        }
        next_id
    }

    /// Port of `CProcessingDataBox::getNextRoleAssertionCreationID`.
    pub fn next_role_assertion_creation_id(&mut self, increment_next_id: bool) -> Cint64 {
        let next_id = self.next_role_assertion_creation_id;
        if increment_next_id {
            self.next_role_assertion_creation_id += 1;
        }
        next_id
    }

    // ----------------------------------------------------------------------
    // referred-individual tracking vector (`.cpp` 2209–2219)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::getReferredIndividualTrackingVector`.
    pub fn referred_individual_tracking_vector(&self) -> Id<ReferredIndividualTrackingVector> {
        self.referred_indi_track_vec
    }

    /// Port of `CProcessingDataBox::setReferredIndividualTrackingVector`.
    pub fn set_referred_individual_tracking_vector(
        &mut self,
        ref_indi_track_vec: Id<ReferredIndividualTrackingVector>,
    ) -> &mut Self {
        self.referred_indi_track_vec = ref_indi_track_vec;
        self
    }

    // ----------------------------------------------------------------------
    // remaining individual-saturation node linker (`.cpp` 2235–2260)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::getRemainingIndividualSaturationNodeLinker`.
    pub fn remaining_individual_saturation_node_linker(&self) -> &[SatNodeId] {
        &self.rem_sat_indi_node_linker
    }

    /// Port of `CProcessingDataBox::takeRemainingIndividualSaturationNodeLinker`.
    ///
    /// Returns the chain head (front element) and advances the chain, or
    /// `SatNodeId::NONE` when the chain is empty (the C++ `nullptr`).
    pub fn take_remaining_individual_saturation_node_linker(&mut self) -> SatNodeId {
        if self.rem_sat_indi_node_linker.is_empty() {
            SatNodeId::NONE
        } else {
            self.rem_sat_indi_node_linker.remove(0)
        }
    }

    /// Port of `CProcessingDataBox::addRemainingIndividualSaturationNodeLinker`.
    pub fn add_remaining_individual_saturation_node_linker(
        &mut self,
        indi_process_node_linker: SatNodeId,
    ) -> &mut Self {
        self.rem_sat_indi_node_linker.insert(0, indi_process_node_linker);
        self
    }

    /// Port of `CProcessingDataBox::setRemainingIndividualSaturationProcessNodeLinker`.
    pub fn set_remaining_individual_saturation_process_node_linker(
        &mut self,
        indi_process_node_linker: Vec<SatNodeId>,
    ) -> &mut Self {
        self.rem_sat_indi_node_linker = indi_process_node_linker;
        self
    }

    // ----------------------------------------------------------------------
    // remaining individual-successor link-data linker (`.cpp` 2272–2297)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::getRemainingIndividualSuccessorLinkDataLinker`.
    pub fn remaining_individual_successor_link_data_linker(
        &self,
    ) -> &[Id<IndividualSaturationSuccessorLinkData>] {
        &self.rem_sat_indi_succ_link_data_linker
    }

    /// Port of `CProcessingDataBox::takeRemainingIndividualSuccessorLinkDataLinker`.
    pub fn take_remaining_individual_successor_link_data_linker(
        &mut self,
    ) -> Id<IndividualSaturationSuccessorLinkData> {
        if self.rem_sat_indi_succ_link_data_linker.is_empty() {
            Id::NONE
        } else {
            self.rem_sat_indi_succ_link_data_linker.remove(0)
        }
    }

    /// Port of `CProcessingDataBox::addRemainingIndividualSuccessorLinkDataLinker`.
    pub fn add_remaining_individual_successor_link_data_linker(
        &mut self,
        succ_link_data_linker: Id<IndividualSaturationSuccessorLinkData>,
    ) -> &mut Self {
        self.rem_sat_indi_succ_link_data_linker.insert(0, succ_link_data_linker);
        self
    }

    /// Port of `CProcessingDataBox::setRemainingIndividualSuccessorLinkDataLinker`.
    pub fn set_remaining_individual_successor_link_data_linker(
        &mut self,
        succ_link_data_linker: Vec<Id<IndividualSaturationSuccessorLinkData>>,
    ) -> &mut Self {
        self.rem_sat_indi_succ_link_data_linker = succ_link_data_linker;
        self
    }

    // ----------------------------------------------------------------------
    // possible-instance merging linkers (`.cpp` 2320–2342)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::getLastMergedPossibleInstanceIndividualLinker`.
    pub fn last_merged_possible_instance_individual_linker(&self) -> &[Cint64] {
        &self.last_merged_possible_instance_individual_linker
    }

    /// Port of `CProcessingDataBox::setLastMergedPossibleInstanceIndividualLinker`.
    pub fn set_last_merged_possible_instance_individual_linker(
        &mut self,
        last_merged_possible_instance_linker: Vec<Cint64>,
    ) -> &mut Self {
        self.last_merged_possible_instance_individual_linker = last_merged_possible_instance_linker;
        self
    }

    /// Port of `CProcessingDataBox::getCurrentMergedPossibleInstanceIndividualLinkersLinker`.
    pub fn current_merged_possible_instance_individual_linkers_linker(&self) -> &[Vec<Cint64>] {
        &self.current_merged_possible_instance_individual_linkers_linker
    }

    /// Port of `CProcessingDataBox::setCurrentMergedPossibleInstanceIndividualLinkersLinker`.
    pub fn set_current_merged_possible_instance_individual_linkers_linker(
        &mut self,
        merged_possible_instance_linker: Vec<Vec<Cint64>>,
    ) -> &mut Self {
        self.current_merged_possible_instance_individual_linkers_linker =
            merged_possible_instance_linker;
        self
    }

    // ----------------------------------------------------------------------
    // backend-cache integrated counts: increment (`.cpp` 2390–2405)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::incBackendCacheIntegratedIndividualNodeCount`.
    pub fn inc_backend_cache_integrated_individual_node_count(&mut self, count: Cint64) -> &mut Self {
        self.backend_cache_integrated_individual_node_count += count;
        self
    }

    /// Port of `CProcessingDataBox::incBackendCacheIntegratedSameIndividualNodeCount`.
    pub fn inc_backend_cache_integrated_same_individual_node_count(
        &mut self,
        count: Cint64,
    ) -> &mut Self {
        self.backend_cache_integrated_same_individual_node_count += count;
        self
    }

    // ----------------------------------------------------------------------
    // last backend-cache integrated individual-node linker (`.cpp` 2410–2425)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::getLastBackendCacheIntegratedIndividualNodeLinker`.
    pub fn last_backend_cache_integrated_individual_node_linker(&self) -> &[NodeId] {
        &self.last_backend_cache_integrated_indi_node_linker
    }

    /// Port of `CProcessingDataBox::setLastBackendCacheIntegratedIndividualNodeLinker`.
    ///
    /// Mirrors the C++ `mBackendCacheIntegratedIndividualNodeCount =
    /// indiLinker->getCount()` — the count is the chain length (`Vec::len`).
    pub fn set_last_backend_cache_integrated_individual_node_linker(
        &mut self,
        indi_linker: Vec<NodeId>,
    ) -> &mut Self {
        self.backend_cache_integrated_individual_node_count = indi_linker.len() as Cint64;
        self.last_backend_cache_integrated_indi_node_linker = indi_linker;
        self
    }

    /// Port of `CProcessingDataBox::addLastBackendCacheIntegratedIndividualNodeLinker`.
    ///
    /// C++ `indiLinker->append(mLast…)` splices `indiLinker` in front of the old
    /// head; front-prepend the supplied chain to preserve head-first order.
    pub fn add_last_backend_cache_integrated_individual_node_linker(
        &mut self,
        indi_linker: Vec<NodeId>,
    ) -> &mut Self {
        self.backend_cache_integrated_individual_node_count += indi_linker.len() as Cint64;
        let mut new_head = indi_linker;
        new_head.append(&mut self.last_backend_cache_integrated_indi_node_linker);
        self.last_backend_cache_integrated_indi_node_linker = new_head;
        self
    }

    // ----------------------------------------------------------------------
    // backend-cache loaded-association hash (`.cpp` 2428–2447)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::setBackendCacheLoadedAssociationHash`.
    pub fn set_backend_cache_loaded_association_hash(
        &mut self,
        backend_cache_loaded_association_hash: Id<IndividualRepresentativeBackendCacheLoadedAssociationHash>,
    ) -> &mut Self {
        self.use_backend_loaded_association_hash = backend_cache_loaded_association_hash;
        self.loc_backend_loaded_association_hash = backend_cache_loaded_association_hash;
        self
    }

    /// Port of `CProcessingDataBox::getBackendCacheLoadedAssociationHash`.
    pub fn backend_cache_loaded_association_hash(
        &mut self,
        create_or_force_localisation: bool,
    ) -> Id<IndividualRepresentativeBackendCacheLoadedAssociationHash> {
        if create_or_force_localisation && self.loc_backend_loaded_association_hash.is_none() {
            // W2-DEFER[api]: mLocBackendLoadedAssociationHash =
            //   CObjectParameterizingAllocator<…>::allocateAndConstructAndParameterize(…);
            //   mLocBackendLoadedAssociationHash->initIndividualRepresentativeBackendCacheLoadedAssociationHash(
            //       mUseBackendLoadedAssociationHash);
            //   mUseBackendLoadedAssociationHash = mLocBackendLoadedAssociationHash;
            // (lazy pool alloc + init on the not-yet-ported hash container.)
        }
        self.use_backend_loaded_association_hash
    }

    // ----------------------------------------------------------------------
    // backend-cache concept-set-label processing hash (`.cpp` 2450–2458)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::getBackendCacheConceptSetLabelProcessingHash`.
    pub fn backend_cache_concept_set_label_processing_hash(
        &mut self,
        create_or_force_localisation: bool,
    ) -> Id<IndividualRepresentativeBackendCacheConceptSetLabelProcessingHash> {
        if create_or_force_localisation && self.loc_backend_concept_set_label_processing_hash.is_none() {
            // W2-DEFER[api]: mLocBackendConceptSetLabelProcessingHash =
            //   CObjectParameterizingAllocator<…>::allocateAndConstructAndParameterize(…);
            //   mLocBackendConceptSetLabelProcessingHash
            //       ->initIndividualRepresentativeBackendCacheConceptSetLabelProcessingHash(
            //           mUseBackendConceptSetLabelProcessingHash);
            //   mUseBackendConceptSetLabelProcessingHash = mLocBackendConceptSetLabelProcessingHash;
        }
        self.use_backend_concept_set_label_processing_hash
    }

    // ----------------------------------------------------------------------
    // delayed backend-init processing queue (`.cpp` 2463–2480)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::getDelayedBackendConceptSetLabelProcessingInitializationQueue`.
    pub fn delayed_backend_concept_set_label_processing_initialization_queue(
        &mut self,
        create: bool,
    ) -> Id<IndividualDelayedBackendInitializationProcessingQueue> {
        if self.delayed_backend_init_proc_queue.is_none() && create {
            // W2-DEFER[api]: mDelayedBackendInitProcQueue =
            //   CObjectParameterizingAllocator<…>::allocateAndConstructAndParameterize(…);
            //   mDelayedBackendInitProcQueue->initProcessingQueue(mPrevDelayedBackendInitProcQueue);
            //   mUseDelayedBackendInitProcQueue = mDelayedBackendInitProcQueue;
        }
        self.use_delayed_backend_init_proc_queue
    }

    /// Port of `CProcessingDataBox::clearDelayedBackendConceptSetLabelProcessingInitializationQueue`.
    pub fn clear_delayed_backend_concept_set_label_processing_initialization_queue(
        &mut self,
    ) -> &mut Self {
        self.delayed_backend_init_proc_queue = Id::NONE;
        self.use_delayed_backend_init_proc_queue = Id::NONE;
        self.prev_delayed_backend_init_proc_queue = Id::NONE;
        self
    }

    // ----------------------------------------------------------------------
    // backend neighbour-expansion controlling data (`.cpp` 2483–2491)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::getBackendNeighbourExpansionControllingData`.
    pub fn backend_neighbour_expansion_controlling_data(
        &mut self,
        create_or_localize: bool,
    ) -> Id<BackendNeighbourExpansionControllingData> {
        if create_or_localize && self.loc_backend_neighbour_expansion_controlling_data.is_none() {
            // W2-DEFER[api]: mLocBackendNeighbourExpansionControllingData =
            //   CObjectParameterizingAllocator<…>::allocateAndConstructAndParameterize(…);
            //   mLocBackendNeighbourExpansionControllingData->initExpansionControllingData(
            //       mUseBackendNeighbourExpansionControllingData);
            //   mUseBackendNeighbourExpansionControllingData = mLocBackendNeighbourExpansionControllingData;
        }
        self.use_backend_neighbour_expansion_controlling_data
    }

    // ----------------------------------------------------------------------
    // backend neighbour-expansion queue (`.cpp` 2496–2511)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::getBackendNeighbourExpansionQueue`.
    pub fn backend_neighbour_expansion_queue(
        &mut self,
        create: bool,
    ) -> Id<BackendNeighbourExpansionQueue> {
        if self.backend_neighbour_expansion_queue.is_none() && create {
            // W2-DEFER[api]: mBackendNeighbourExpansionQueue =
            //   CObjectParameterizingAllocator<…>::allocateAndConstructAndParameterize(…);
            //   mBackendNeighbourExpansionQueue->initBackendNeighbourExpansionQueue(mPrevBackendNeighbourExpansion);
            //   mUseBackendNeighbourExpansion = mBackendNeighbourExpansionQueue;
        }
        self.use_backend_neighbour_expansion
    }

    /// Port of `CProcessingDataBox::clearBackendNeighbourExpansionQueue`.
    pub fn clear_backend_neighbour_expansion_queue(&mut self) -> &mut Self {
        self.backend_neighbour_expansion_queue = Id::NONE;
        self.use_backend_neighbour_expansion = Id::NONE;
        self.prev_backend_neighbour_expansion = Id::NONE;
        self
    }

    // ----------------------------------------------------------------------
    // representative neighbour-expansion individual-node linker (`.cpp` 2513–2517)
    // ----------------------------------------------------------------------

    /// Port of `CProcessingDataBox::getRepresentativeNeighbourExpansionIndividualNodeLinker`.
    pub fn representative_neighbour_expansion_individual_node_linker(&self) -> &[NodeId] {
        &self.representative_neighbour_expansion_individual_node_linker
    }

    /// Port of `CProcessingDataBox::addRepresentativeNeighbourExpansionIndividualNodeLinker`.
    ///
    /// C++ `indiLinker->append(mRepresentative…)` splices `indiLinker` in front
    /// of the old head; front-prepend to preserve head-first order.
    pub fn add_representative_neighbour_expansion_individual_node_linker(
        &mut self,
        indi_linker: Vec<NodeId>,
    ) -> &mut Self {
        let mut new_head = indi_linker;
        new_head.append(&mut self.representative_neighbour_expansion_individual_node_linker);
        self.representative_neighbour_expansion_individual_node_linker = new_head;
        self
    }
}
