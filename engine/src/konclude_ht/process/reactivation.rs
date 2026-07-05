//! `process::reactivation` — nominal caching-loss reactivation data.
//!
//! Konclude source:
//! `Source/Reasoner/Kernel/Process/CNominalCachingLossReactivationData.{h,cpp}`.

#![allow(dead_code)]

use std::collections::BTreeMap;

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::NodeId;

/// `CNominalCachingLossReactivationData*`.
pub type NominalCachingLossReactivationDataId = Id<NominalCachingLossReactivationData>;

/// `CNominalCachingLossReactivationHash*`.
pub type NominalCachingLossReactivationHashId = Id<NominalCachingLossReactivationHash>;

/// Port of `CNominalCachingLossReactivationData`.
#[derive(Clone)]
pub struct NominalCachingLossReactivationData {
    /// `CProcessContext* mProcessContext`.
    pub process_context: Cint64,
    /// `cint64 mNominalID`.
    pub nominal_id: Cint64,
    /// `bool mReactivated`.
    pub reactivated: bool,
    /// `CXLinker<CIndividualProcessNode*>* mIndiReactivationLinker`.
    pub indi_reactivation_linker: Vec<NodeId>,
}

impl Default for NominalCachingLossReactivationData {
    fn default() -> Self {
        Self {
            process_context: INVALID,
            nominal_id: 0,
            reactivated: false,
            indi_reactivation_linker: Vec::new(),
        }
    }
}

impl NominalCachingLossReactivationData {
    /// Port of `CNominalCachingLossReactivationData::CNominalCachingLossReactivationData`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            ..Default::default()
        }
    }

    /// Port of `initNominalCachingLossReactivationData`.
    pub fn init_nominal_caching_loss_reactivation_data(
        &mut self,
        nominal_id: Cint64,
        data: Option<&NominalCachingLossReactivationData>,
    ) -> &mut Self {
        self.reactivated = false;
        self.nominal_id = nominal_id;
        self.indi_reactivation_linker.clear();
        if let Some(data) = data {
            self.reactivated = data.reactivated;
            self.indi_reactivation_linker = data.indi_reactivation_linker.clone();
        }
        self
    }

    /// Port of `getNominalID`.
    pub fn get_nominal_id(&self) -> Cint64 {
        self.nominal_id
    }

    /// Port of `hasReactivated`.
    pub fn has_reactivated(&self) -> bool {
        self.reactivated
    }

    /// Port of `setReactivated`.
    pub fn set_reactivated(&mut self, reactivated: bool) -> &mut Self {
        self.reactivated = reactivated;
        self
    }

    /// Port of `getReactivationIndividualNodeLinker`.
    pub fn get_reactivation_individual_node_linker(&self) -> &[NodeId] {
        &self.indi_reactivation_linker
    }

    /// Port of `takeReactivationIndividualNodeLinker`.
    pub fn take_reactivation_individual_node_linker(&mut self) -> Vec<NodeId> {
        std::mem::take(&mut self.indi_reactivation_linker)
    }

    /// Port of `addReactivationIndividualNode`.
    pub fn add_reactivation_individual_node(&mut self, indi_proc_node: NodeId) -> &mut Self {
        self.indi_reactivation_linker.insert(0, indi_proc_node);
        self
    }
}

/// Port of `CNominalCachingLossReactivationHashData`.
#[derive(Debug, PartialEq, Eq)]
pub struct NominalCachingLossReactivationHashData {
    /// `mReactivationData`.
    pub reactivation_data: NominalCachingLossReactivationDataId,
    /// `mPrevReactivationData`.
    pub prev_reactivation_data: NominalCachingLossReactivationDataId,
}

impl Default for NominalCachingLossReactivationHashData {
    fn default() -> Self {
        Self {
            reactivation_data: NominalCachingLossReactivationDataId::NONE,
            prev_reactivation_data: NominalCachingLossReactivationDataId::NONE,
        }
    }
}

impl Clone for NominalCachingLossReactivationHashData {
    /// Port of the C++ copy constructor: local data is reset, previous data is
    /// retained.
    fn clone(&self) -> Self {
        Self {
            reactivation_data: NominalCachingLossReactivationDataId::NONE,
            prev_reactivation_data: self.prev_reactivation_data,
        }
    }
}

/// Port of `CNominalCachingLossReactivationHash`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NominalCachingLossReactivationHash {
    /// `mNominalReactivationDataHash`.
    pub nominal_reactivation_data_hash: BTreeMap<Cint64, NominalCachingLossReactivationHashData>,
    /// `mProcessContext`.
    pub process_context: Cint64,
}

impl Default for NominalCachingLossReactivationHash {
    fn default() -> Self {
        Self::new(INVALID)
    }
}

impl NominalCachingLossReactivationHash {
    /// Port of the constructor.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            nominal_reactivation_data_hash: BTreeMap::new(),
            process_context,
        }
    }

    /// Port of `initNominalDependentNodeHash`.
    pub fn init_nominal_dependent_node_hash(
        &mut self,
        nominal_dependent_hash: Option<&NominalCachingLossReactivationHash>,
    ) -> &mut Self {
        if let Some(hash) = nominal_dependent_hash {
            self.nominal_reactivation_data_hash = hash.nominal_reactivation_data_hash.clone();
        } else {
            self.nominal_reactivation_data_hash.clear();
        }
        self
    }

    /// Non-creating part of `getNominalCachingLossReactivationData(cint64,false)`.
    pub fn get_nominal_caching_loss_reactivation_data(
        &self,
        nominal_id: Cint64,
    ) -> NominalCachingLossReactivationDataId {
        self.nominal_reactivation_data_hash
            .get(&nominal_id)
            .map_or(NominalCachingLossReactivationDataId::NONE, |data| {
                data.prev_reactivation_data
            })
    }
}
