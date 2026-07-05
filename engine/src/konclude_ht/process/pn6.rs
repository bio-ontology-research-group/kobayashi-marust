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
//! `mUse…`. The port threads the ambient `ProcessContext` for all six lazy
//! satellite accessors; the datatype and successor-ATMOST payload classes remain
//! placeholder structs until their own methods are ported.
//!
//! KONCLUDE-PORT-NOTE[ownership]: `has/addSuccessorConnectionToNominal` read/mutate
//! the returned `CSuccessorConnectedNominalSet` through `ProcessContext`, matching
//! the C++ pointer dereference through the per-test memory pool.

#![allow(dead_code)]

use super::super::model::substrate::INVALID;
use super::super::model::{Cint64, Id};
use super::context::ProcessContext;
use super::merging_hash::IndividualMergingHash;
use super::node::IndividualProcessNode;
use super::nominal_conn::SuccessorConnectedNominalSet;
use super::reactivation::NominalCachingLossReactivationData;
use super::reapply_sat::IndividualNodeIncrementalExpansionData;
use super::stubs::{
    ATMOSTReactivationDataId, DatatypesValueSpaceData, DatatypesValueSpaceDataId, IncExpDataId,
    IndividualMergingHashId, NominalConnectionSetId, ReactivationDataId,
    SuccessorIndividualATMOSTReactivationData,
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
    pub fn nominal_caching_loss_reactivation_data(
        &mut self,
        process_context: &mut ProcessContext,
        create: bool,
    ) -> ReactivationDataId {
        // CNominalCachingLossReactivationData* nominalNodeReactData = nullptr;
        if self.loc_reactivation_data.is_none() && create {
            let prev = self.use_reactivation_data;
            let nominal_node_react_data = process_context
                .alloc_nominal_caching_loss_reactivation_data(
                    NominalCachingLossReactivationData::new(INVALID),
                );
            if prev.is_some() {
                let taken = std::mem::replace(
                    process_context.nominal_caching_loss_reactivation_data_mut(prev),
                    NominalCachingLossReactivationData::new(INVALID),
                );
                process_context
                    .nominal_caching_loss_reactivation_data_mut(nominal_node_react_data)
                    .init_nominal_caching_loss_reactivation_data(
                        self.individual_node_id(),
                        Some(&taken),
                    );
                *process_context.nominal_caching_loss_reactivation_data_mut(prev) = taken;
            } else {
                process_context
                    .nominal_caching_loss_reactivation_data_mut(nominal_node_react_data)
                    .init_nominal_caching_loss_reactivation_data(self.individual_node_id(), None);
            }
            self.loc_reactivation_data = nominal_node_react_data;
            self.use_reactivation_data = nominal_node_react_data;
        }
        self.use_reactivation_data
    }

    /// Port of `CIndividualProcessNode::getSuccessorNominalConnectionSet`.
    pub fn successor_nominal_connection_set(
        &mut self,
        process_context: &mut ProcessContext,
        create: bool,
    ) -> NominalConnectionSetId {
        // CSuccessorConnectedNominalSet* nomConnSet = nullptr;
        if self.loc_nominal_connection_set.is_none() && create {
            let prev = self.use_nominal_connection_set;
            let nom_conn_set =
                process_context.alloc_nominal_conn_set(SuccessorConnectedNominalSet::new());
            if prev.is_some() {
                let taken = std::mem::replace(
                    process_context.nominal_conn_set_mut(prev),
                    SuccessorConnectedNominalSet::new(),
                );
                process_context
                    .nominal_conn_set_mut(nom_conn_set)
                    .init_successor_connected_nominal_set(Some(&taken));
                *process_context.nominal_conn_set_mut(prev) = taken;
            } else {
                process_context
                    .nominal_conn_set_mut(nom_conn_set)
                    .init_successor_connected_nominal_set(None);
            }
            self.loc_nominal_connection_set = nom_conn_set;
            self.use_nominal_connection_set = nom_conn_set;
        }
        self.use_nominal_connection_set
    }

    /// Port of `CIndividualProcessNode::getSuccessorIndividualATMOSTReactivationData`.
    pub fn successor_individual_atmost_reactivation_data(
        &mut self,
        process_context: &mut ProcessContext,
        create: bool,
    ) -> ATMOSTReactivationDataId {
        if self.loc_succ_indi_atmost_reactivation_data.is_none() && create {
            let prev = self.use_succ_indi_atmost_reactivation_data;
            let succ_indi_atmost_reactivation_data = process_context
                .alloc_successor_individual_atmost_reactivation_data(
                    SuccessorIndividualATMOSTReactivationData::default(),
                );
            if prev.is_some() {
                let taken = std::mem::take(
                    process_context.successor_individual_atmost_reactivation_data_mut(prev),
                );
                process_context
                    .successor_individual_atmost_reactivation_data_mut(
                        succ_indi_atmost_reactivation_data,
                    )
                    .init_successor_individual_atmost_reactivation_data(Some(&taken));
                *process_context.successor_individual_atmost_reactivation_data_mut(prev) = taken;
            } else {
                process_context
                    .successor_individual_atmost_reactivation_data_mut(
                        succ_indi_atmost_reactivation_data,
                    )
                    .init_successor_individual_atmost_reactivation_data(None);
            }
            self.loc_succ_indi_atmost_reactivation_data = succ_indi_atmost_reactivation_data;
            self.use_succ_indi_atmost_reactivation_data = succ_indi_atmost_reactivation_data;
        }
        self.use_succ_indi_atmost_reactivation_data
    }

    /// Port of `CIndividualProcessNode::hasSuccessorConnectionToNominal`.
    pub fn has_successor_connection_to_nominal(
        &mut self,
        process_context: &ProcessContext,
        nominal_id: Cint64,
    ) -> bool {
        let nom_conn_set = self.use_nominal_connection_set;
        if nom_conn_set.is_some() {
            return process_context
                .nominal_conn_set(nom_conn_set)
                .has_successor_connected_nominal(nominal_id);
        }
        false
    }

    /// Port of `CIndividualProcessNode::addSuccessorConnectionToNominal`.
    pub fn add_successor_connection_to_nominal(
        &mut self,
        process_context: &mut ProcessContext,
        nominal_id: Cint64,
    ) -> bool {
        let nom_conn_set = self.successor_nominal_connection_set(process_context, true);
        if nom_conn_set.is_some() {
            return process_context
                .nominal_conn_set_mut(nom_conn_set)
                .add_successor_connected_nominal(nominal_id);
        }
        false
    }

    /// Port of `CIndividualProcessNode::getDatatypesValueSpaceData`.
    pub fn datatypes_value_space_data(
        &mut self,
        process_context: &mut ProcessContext,
        create: bool,
    ) -> DatatypesValueSpaceDataId {
        // CDatatypesValueSpaceData* valueSpaceData = nullptr;
        if self.loc_datatypes_value_space_data.is_none() && create {
            let prev = self.use_datatypes_value_space_data;
            let value_space_data = process_context
                .alloc_datatypes_value_space_data(DatatypesValueSpaceData::default());
            if prev.is_some() {
                let taken = std::mem::take(process_context.datatypes_value_space_data_mut(prev));
                process_context
                    .datatypes_value_space_data_mut(value_space_data)
                    .init_datatypes_value_space_data(Some(&taken));
                *process_context.datatypes_value_space_data_mut(prev) = taken;
            } else {
                process_context
                    .datatypes_value_space_data_mut(value_space_data)
                    .init_datatypes_value_space_data(None);
            }
            self.loc_datatypes_value_space_data = value_space_data;
            self.use_datatypes_value_space_data = value_space_data;
        }
        self.use_datatypes_value_space_data
    }

    /// Port of `CIndividualProcessNode::getIncrementalExpansionData`.
    pub fn incremental_expansion_data(
        &mut self,
        process_context: &mut ProcessContext,
        create: bool,
    ) -> IncExpDataId {
        // CIndividualNodeIncrementalExpansionData* incExpData = nullptr;
        if self.loc_inc_exp_data.is_none() && create {
            let prev = self.use_inc_exp_data;
            let mut new_data = IndividualNodeIncrementalExpansionData::new(INVALID);
            if prev.is_some() {
                let prev_data = process_context.inc_exp_data(prev);
                new_data.init_incremental_expansion_data(Some(prev_data));
            } else {
                new_data.init_incremental_expansion_data(None);
            }
            let inc_exp_data = process_context.alloc_inc_exp_data(new_data);
            self.loc_inc_exp_data = inc_exp_data;
            self.use_inc_exp_data = inc_exp_data;
        }
        self.use_inc_exp_data
    }

    /// Port of `CIndividualProcessNode::getIndividualMergingHash`.
    pub fn individual_merging_hash(
        &mut self,
        process_context: &mut ProcessContext,
        create: bool,
    ) -> IndividualMergingHashId {
        // CIndividualMergingHash* indiMergHash = nullptr;
        if self.loc_individual_merging_hash.is_none() && create {
            let prev = self.use_individual_merging_hash;
            let mut new_hash = IndividualMergingHash::new();
            if prev.is_some() {
                let prev_hash = process_context.individual_merging_hash(prev);
                new_hash.init_individual_merging_hash(Some(prev_hash));
            } else {
                new_hash.init_individual_merging_hash(None);
            }
            let indi_merg_hash = process_context.alloc_individual_merging_hash(new_hash);
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
    pub fn set_merged_dependency_track_point(
        &mut self,
        dep_track_point: TrackPointId,
    ) -> &mut Self {
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

#[cfg(test)]
mod tests {
    use super::super::stubs::ProcessContextId;
    use super::*;

    #[test]
    fn pn6_nominal_connection_set_allocates_adds_and_reuses() {
        let mut ctx = ProcessContext::new();
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);

        assert_eq!(
            node.successor_nominal_connection_set(&mut ctx, false),
            NominalConnectionSetId::NONE
        );
        assert!(!node.has_successor_connection_to_nominal(&ctx, 42));

        let set = node.successor_nominal_connection_set(&mut ctx, true);
        assert!(set.is_some());
        assert_eq!(node.successor_nominal_connection_set(&mut ctx, true), set);
        assert!(node.add_successor_connection_to_nominal(&mut ctx, 42));
        assert!(node.has_successor_connection_to_nominal(&ctx, 42));
        assert!(!node.add_successor_connection_to_nominal(&mut ctx, 42));
    }

    #[test]
    fn pn6_reactivation_data_initializes_from_node_id_and_previous_data() {
        let mut ctx = ProcessContext::new();
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);
        node.set_individual_node_id(91);

        let first = node.nominal_caching_loss_reactivation_data(&mut ctx, true);
        ctx.nominal_caching_loss_reactivation_data_mut(first)
            .set_reactivated(true)
            .add_reactivation_individual_node(NodeId::new(7));

        node.loc_reactivation_data = ReactivationDataId::NONE;
        let second = node.nominal_caching_loss_reactivation_data(&mut ctx, true);

        assert_ne!(first, second);
        let copied = ctx.nominal_caching_loss_reactivation_data(second);
        assert_eq!(copied.get_nominal_id(), 91);
        assert!(copied.has_reactivated());
        assert_eq!(
            copied.get_reactivation_individual_node_linker(),
            &[NodeId::new(7)]
        );
    }

    #[test]
    fn pn6_incremental_expansion_data_and_merging_hash_copy_previous_generation() {
        let mut ctx = ProcessContext::new();
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);

        let first_inc = node.incremental_expansion_data(&mut ctx, true);
        ctx.inc_exp_data_mut(first_inc)
            .set_incremetnal_expansion_list_initialized(true)
            .set_expansion_priority(3.5);
        node.loc_inc_exp_data = IncExpDataId::NONE;
        let second_inc = node.incremental_expansion_data(&mut ctx, true);
        assert_ne!(first_inc, second_inc);
        assert!(ctx
            .inc_exp_data(second_inc)
            .is_incremetnal_expansion_list_initialized());
        assert_eq!(ctx.inc_exp_data(second_inc).get_expansion_priority(), 3.5);

        let first_hash = node.individual_merging_hash(&mut ctx, true);
        ctx.individual_merging_hash_mut(first_hash)
            .add_merged_individual_linker(vec![5, 6]);
        node.loc_individual_merging_hash = IndividualMergingHashId::NONE;
        let second_hash = node.individual_merging_hash(&mut ctx, true);
        assert_ne!(first_hash, second_hash);
        assert_eq!(
            ctx.individual_merging_hash(second_hash)
                .get_merged_individual_linker(),
            &[5, 6]
        );
        assert_eq!(
            ctx.individual_merging_hash(second_hash)
                .get_merged_individual_count(),
            2
        );
    }

    #[test]
    fn pn6_remaining_satellite_getters_allocate_and_reuse() {
        let mut ctx = ProcessContext::new();
        let mut node = IndividualProcessNode::new(ProcessContextId::NONE);

        assert_eq!(
            node.successor_individual_atmost_reactivation_data(&mut ctx, false),
            ATMOSTReactivationDataId::NONE
        );
        let first_atmost = node.successor_individual_atmost_reactivation_data(&mut ctx, true);
        assert!(first_atmost.is_some());
        assert_eq!(
            node.successor_individual_atmost_reactivation_data(&mut ctx, true),
            first_atmost
        );
        node.loc_succ_indi_atmost_reactivation_data = ATMOSTReactivationDataId::NONE;
        let second_atmost = node.successor_individual_atmost_reactivation_data(&mut ctx, true);
        assert!(second_atmost.is_some());
        assert_ne!(first_atmost, second_atmost);
        assert_eq!(node.use_succ_indi_atmost_reactivation_data, second_atmost);

        assert_eq!(
            node.datatypes_value_space_data(&mut ctx, false),
            DatatypesValueSpaceDataId::NONE
        );
        let first_value_space = node.datatypes_value_space_data(&mut ctx, true);
        assert!(first_value_space.is_some());
        assert_eq!(
            node.datatypes_value_space_data(&mut ctx, true),
            first_value_space
        );
        node.loc_datatypes_value_space_data = DatatypesValueSpaceDataId::NONE;
        let second_value_space = node.datatypes_value_space_data(&mut ctx, true);
        assert!(second_value_space.is_some());
        assert_ne!(first_value_space, second_value_space);
        assert_eq!(node.use_datatypes_value_space_data, second_value_space);
    }
}
