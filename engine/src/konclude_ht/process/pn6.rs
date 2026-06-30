//! `process::pn6` — method-batch unit **PN-6** of `CIndividualProcessNode`:
//! reactivation / nominal-connection / datatype / incremental-expansion satellite
//! accessors + merge-state accessors
//! (`Source/Reasoner/Kernel/Process/CIndividualProcessNode.cpp` lines 2011–2159).
//!
//! This is the last PN unit. It holds the lazy-allocating `loc/use` accessors for
//! the six per-node satellite structs (reactivation data, nominal-connection set,
//! ATMOST-reactivation data, datatypes value-space data, incremental-expansion
//! data, individual-merging hash) plus the plain merge / blocker / following /
//! incremental-id getters/setters. See `manifest/05-process-units.md` §3 PN-6.
//!
//! KONCLUDE-PORT-NOTE[ownership]: the C++ `get*…Data(bool create)` accessors
//! lazily `CObjectParameterizingAllocator::allocateAndConstructAndParameterize`
//! the satellite object from the process-context memory pool, `init*` it from the
//! current `mUse…` generation, and store the new object into both `mLoc…` and
//! `mUse…`. The port keeps the control flow but the allocate+init pair needs the
//! ambient `&mut` process-context arena (the satellite classes are also not ported
//! yet — they live as `process::stubs` markers), so it is marked `W2-DEFER[api]`
//! and the new id is left `Id::NONE` until the context arena hand-off lands. The
//! `loc`/`use` shuffle itself is ported faithfully.
//!
//! KONCLUDE-PORT-NOTE[ownership]: `has/addSuccessorConnectionToNominal` read/mutate
//! the returned `CSuccessorConnectedNominalSet` (a `process::stubs` marker), so the
//! set-side call is `W2-DEFER[api]`; the get-set lazy-alloc dispatch is ported.

#![allow(dead_code)]

use super::super::model::{Cint64, Id};
use super::node::IndividualProcessNode;
use super::stubs::{
    ATMOSTReactivationDataId, DatatypesValueSpaceDataId, IncExpDataId, IndividualMergingHashId,
    NominalConnectionSetId, ReactivationDataId,
};
use super::{NodeId, TrackPointId};

impl IndividualProcessNode {
    // ===================================================================
    // Caching-loss reactivation flag (PN-6).
    // ===================================================================

    /// Port of `CIndividualProcessNode::isCachingLossNodeReactivationInstalled`.
    pub fn is_caching_loss_node_reactivation_installed(&self) -> bool {
        self.caching_loss_node_reactivation_installed
    }

    /// Port of `CIndividualProcessNode::setCachingLossNodeReactivationInstalled`.
    pub fn set_caching_loss_node_reactivation_installed(
        &mut self,
        reactivation_installed: bool,
    ) -> &mut Self {
        self.caching_loss_node_reactivation_installed = reactivation_installed;
        self
    }

    // ===================================================================
    // Lazy-allocating loc/use satellite accessors (PN-6).
    // ===================================================================

    /// Port of `CIndividualProcessNode::getNominalCachingLossReactivationData`.
    pub fn nominal_caching_loss_reactivation_data(&mut self, create: bool) -> ReactivationDataId {
        // CNominalCachingLossReactivationData* nominalNodeReactData = nullptr;
        if self.loc_reactivation_data.is_none() && create {
            // W2-DEFER[api]: nominalNodeReactData = CObjectParameterizingAllocator::
            //   allocate_and_construct_and_parameterize::<NominalCachingLossReactivationData>(
            //     process_context.get_used_memory_allocation_manager(), process_context);
            //   nominalNodeReactData.init_nominal_caching_loss_reactivation_data(
            //     self.individual_node_id(), self.use_reactivation_data);
            let nominal_node_react_data: ReactivationDataId = Id::NONE;
            self.loc_reactivation_data = nominal_node_react_data;
            self.use_reactivation_data = nominal_node_react_data;
        }
        self.use_reactivation_data
    }

    /// Port of `CIndividualProcessNode::getSuccessorNominalConnectionSet`.
    pub fn successor_nominal_connection_set(&mut self, create: bool) -> NominalConnectionSetId {
        // CSuccessorConnectedNominalSet* nomConnSet = nullptr;
        if self.loc_nominal_connection_set.is_none() && create {
            // W2-DEFER[api]: nomConnSet = allocate_and_construct_and_parameterize::<
            //   SuccessorConnectedNominalSet>(process_context);
            //   nomConnSet.init_successor_connected_nominal_set(self.use_nominal_connection_set);
            let nom_conn_set: NominalConnectionSetId = Id::NONE;
            self.loc_nominal_connection_set = nom_conn_set;
            self.use_nominal_connection_set = nom_conn_set;
        }
        self.use_nominal_connection_set
    }

    /// Port of `CIndividualProcessNode::getSuccessorIndividualATMOSTReactivationData`.
    pub fn successor_individual_atmost_reactivation_data(
        &mut self,
        create: bool,
    ) -> ATMOSTReactivationDataId {
        if self.loc_succ_indi_atmost_reactivation_data.is_none() && create {
            // W2-DEFER[api]: succIndiATMOSTReactivationData = allocate_and_construct_and_parameterize::<
            //   SuccessorIndividualATMOSTReactivationData>(process_context);
            //   succIndiATMOSTReactivationData.init_successor_individual_atmost_reactivation_data(
            //     self.use_succ_indi_atmost_reactivation_data);
            let succ_indi_atmost_reactivation_data: ATMOSTReactivationDataId = Id::NONE;
            self.loc_succ_indi_atmost_reactivation_data = succ_indi_atmost_reactivation_data;
            self.use_succ_indi_atmost_reactivation_data = succ_indi_atmost_reactivation_data;
        }
        self.use_succ_indi_atmost_reactivation_data
    }

    /// Port of `CIndividualProcessNode::hasSuccessorConnectionToNominal`.
    pub fn has_successor_connection_to_nominal(&mut self, _nominal_id: Cint64) -> bool {
        let nom_conn_set = self.successor_nominal_connection_set(false);
        if nom_conn_set.is_some() {
            // W2-DEFER[api]: return nom_conn_set.has_successor_connected_nominal(arena, nominal_id);
            return false;
        }
        false
    }

    /// Port of `CIndividualProcessNode::addSuccessorConnectionToNominal`.
    pub fn add_successor_connection_to_nominal(&mut self, _nominal_id: Cint64) -> bool {
        let nom_conn_set = self.successor_nominal_connection_set(true);
        if nom_conn_set.is_some() {
            // W2-DEFER[api]: return nom_conn_set.add_successor_connected_nominal(arena, nominal_id);
            return false;
        }
        false
    }

    /// Port of `CIndividualProcessNode::getDatatypesValueSpaceData`.
    pub fn datatypes_value_space_data(&mut self, create: bool) -> DatatypesValueSpaceDataId {
        // CDatatypesValueSpaceData* valueSpaceData = nullptr;
        if self.loc_datatypes_value_space_data.is_none() && create {
            // W2-DEFER[api]: valueSpaceData = allocate_and_construct_and_parameterize::<
            //   DatatypesValueSpaceData>(process_context);
            //   valueSpaceData.init_datatypes_value_space_data(self.use_datatypes_value_space_data);
            let value_space_data: DatatypesValueSpaceDataId = Id::NONE;
            self.loc_datatypes_value_space_data = value_space_data;
            self.use_datatypes_value_space_data = value_space_data;
        }
        self.use_datatypes_value_space_data
    }

    /// Port of `CIndividualProcessNode::getIncrementalExpansionData`.
    pub fn incremental_expansion_data(&mut self, create: bool) -> IncExpDataId {
        // CIndividualNodeIncrementalExpansionData* incExpData = nullptr;
        if self.loc_inc_exp_data.is_none() && create {
            // W2-DEFER[api]: incExpData = allocate_and_construct_and_parameterize::<
            //   IndividualNodeIncrementalExpansionData>(process_context);
            //   incExpData.init_incremental_expansion_data(self.use_inc_exp_data);
            let inc_exp_data: IncExpDataId = Id::NONE;
            self.loc_inc_exp_data = inc_exp_data;
            self.use_inc_exp_data = inc_exp_data;
        }
        self.use_inc_exp_data
    }

    /// Port of `CIndividualProcessNode::getIndividualMergingHash`.
    pub fn individual_merging_hash(&mut self, create: bool) -> IndividualMergingHashId {
        // CIndividualMergingHash* indiMergHash = nullptr;
        if self.loc_individual_merging_hash.is_none() && create {
            // W2-DEFER[api]: indiMergHash = allocate_and_construct_and_parameterize::<
            //   IndividualMergingHash>(process_context);
            //   indiMergHash.init_individual_merging_hash(self.use_individual_merging_hash);
            let indi_merg_hash: IndividualMergingHashId = Id::NONE;
            self.loc_individual_merging_hash = indi_merg_hash;
            self.use_individual_merging_hash = indi_merg_hash;
        }
        self.use_individual_merging_hash
    }

    // ===================================================================
    // Merge / blocker / following / incremental-id accessors (PN-6).
    // ===================================================================

    /// Port of `CIndividualProcessNode::getLastMergedIntoIndividualNode`.
    pub fn last_merged_into_individual_node(&self) -> NodeId {
        self.last_merged_into_individual_node
    }

    /// Port of `CIndividualProcessNode::setLastMergedIntoIndividualNode`.
    pub fn set_last_merged_into_individual_node(&mut self, indi_node: NodeId) -> &mut Self {
        self.last_merged_into_individual_node = indi_node;
        self
    }

    /// Port of `CIndividualProcessNode::getMergedDependencyTrackPoint`.
    pub fn merged_dependency_track_point(&self) -> TrackPointId {
        self.merged_dep_track_point
    }

    /// Port of `CIndividualProcessNode::setMergedDependencyTrackPoint`.
    pub fn set_merged_dependency_track_point(&mut self, dep_track_point: TrackPointId) -> &mut Self {
        self.merged_dep_track_point = dep_track_point;
        self
    }

    /// Port of `CIndividualProcessNode::setBlockerIndividualNode`.
    pub fn set_blocker_individual_node(&mut self, indi_node: NodeId) -> &mut Self {
        self.blocker_indi_node = indi_node;
        self
    }

    /// Port of `CIndividualProcessNode::getBlockerIndividualNode`.
    pub fn blocker_individual_node(&self) -> NodeId {
        self.blocker_indi_node
    }

    /// Port of `CIndividualProcessNode::setFollowingIndividualNode`.
    pub fn set_following_individual_node(&mut self, indi_node: NodeId) -> &mut Self {
        self.following_indi_node = indi_node;
        self
    }

    /// Port of `CIndividualProcessNode::getFollowingIndividualNode`.
    pub fn following_individual_node(&self) -> NodeId {
        self.following_indi_node
    }

    /// Port of `CIndividualProcessNode::setIncrementalExpansionID`.
    pub fn set_incremental_expansion_id(&mut self, inc_exp_id: Cint64) -> &mut Self {
        self.inc_exp_id = inc_exp_id;
        self
    }

    /// Port of `CIndividualProcessNode::getIncrementalExpansionID`.
    pub fn incremental_expansion_id(&self) -> Cint64 {
        self.inc_exp_id
    }
}
