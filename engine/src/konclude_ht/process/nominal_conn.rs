//! `process::nominal_conn` — port of `CSuccessorConnectedNominalSet`.
//!
//! Konclude source:
//! `Source/Reasoner/Kernel/Process/CSuccessorConnectedNominalSet.{h,cpp}`.
//! The C++ type derives from `CPROCESSSET<cint64>` and only adds init/copy,
//! add, and membership helpers. The process-context allocator argument is
//! dropped; the arena in `ProcessContext` owns this Rust value.

#![allow(dead_code)]

use std::collections::HashSet;

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::SatNodeId;

/// `CSuccessorConnectedNominalSet*` → `SuccessorConnectedNominalSetId`.
pub type SuccessorConnectedNominalSetId = Id<SuccessorConnectedNominalSet>;
/// `CSaturationIndividualNodeNominalHandlingData*`.
pub type SaturationIndividualNodeNominalHandlingDataId =
    Id<SaturationIndividualNodeNominalHandlingData>;

/// Port of `CSuccessorConnectedNominalSet` (`: public CPROCESSSET<cint64>`).
#[derive(Clone, Default)]
pub struct SuccessorConnectedNominalSet {
    /// The underlying `CPROCESSSET<cint64>` of connected nominal node ids.
    nominal_set: HashSet<Cint64>,
}

impl SuccessorConnectedNominalSet {
    /// Port of `CSuccessorConnectedNominalSet::CSuccessorConnectedNominalSet`.
    pub fn new() -> Self {
        Self {
            nominal_set: HashSet::new(),
        }
    }

    /// Port of `initSuccessorConnectedNominalSet`.
    pub fn init_successor_connected_nominal_set(
        &mut self,
        nominal_set: Option<&SuccessorConnectedNominalSet>,
    ) -> &mut Self {
        if let Some(nominal_set) = nominal_set {
            self.nominal_set = nominal_set.nominal_set.clone();
        } else {
            self.nominal_set.clear();
        }
        self
    }

    /// Port of `copySuccessorConnectedNominalSet`.
    pub fn copy_successor_connected_nominal_set(
        &mut self,
        nominal_set: Option<&SuccessorConnectedNominalSet>,
    ) -> &mut Self {
        self.init_successor_connected_nominal_set(nominal_set)
    }

    /// Port of `addSuccessorConnectedNominal`.
    pub fn add_successor_connected_nominal(&mut self, nominal_node_id: Cint64) -> bool {
        self.nominal_set.insert(nominal_node_id)
    }

    /// Port of `hasSuccessorConnectedNominal`.
    pub fn has_successor_connected_nominal(&self, nominal_node_id: Cint64) -> bool {
        self.nominal_set.contains(&nominal_node_id)
    }

    /// `CPROCESSSET<cint64>::isEmpty`.
    pub fn is_empty(&self) -> bool {
        self.nominal_set.is_empty()
    }

    /// `CPROCESSSET<cint64>::count`.
    pub fn count(&self) -> Cint64 {
        self.nominal_set.len() as Cint64
    }

    /// Snapshot equivalent of `constBegin()/constEnd()` iteration.
    pub fn iter_snapshot(&self) -> Vec<Cint64> {
        self.nominal_set.iter().copied().collect()
    }
}

/// Port of `CSaturationIndividualNodeNominalHandlingData`.
///
/// This wave needs the successor-connected nominal set; the delayed nominal
/// concept/process linkers remain opaque handles until their owning queues are
/// ported.
#[derive(Clone)]
pub struct SaturationIndividualNodeNominalHandlingData {
    /// `CProcessContext* mProcessContext`.
    pub process_context: Cint64,
    /// `CIndividualSaturationProcessNode* mIndiNode`.
    pub indi_node: SatNodeId,
    /// `CConceptSaturationProcessLinker* mDelayedNominalConceptSatProcessLinker`.
    pub delayed_nominal_con_sat_process_linker: Cint64,
    /// `CIndividualSaturationProcessNodeLinker* mDelayedNominalIndividualSatProcessLinker`.
    pub delayed_nominal_indi_sat_process_linker: Cint64,
    /// `bool mDelayedNominalIndiSaturationProcessLinkerQueued`.
    pub delayed_nominal_indi_sat_process_linker_queued: bool,
    /// `CSuccessorConnectedNominalSet* mSuccConnectedNominalSet`.
    pub succ_connected_nominal_set: SuccessorConnectedNominalSetId,
}

impl Default for SaturationIndividualNodeNominalHandlingData {
    fn default() -> Self {
        Self {
            process_context: INVALID,
            indi_node: SatNodeId::NONE,
            delayed_nominal_con_sat_process_linker: INVALID,
            delayed_nominal_indi_sat_process_linker: INVALID,
            delayed_nominal_indi_sat_process_linker_queued: false,
            succ_connected_nominal_set: SuccessorConnectedNominalSetId::NONE,
        }
    }
}

impl SaturationIndividualNodeNominalHandlingData {
    /// Port of `CSaturationIndividualNodeNominalHandlingData::CSaturationIndividualNodeNominalHandlingData`.
    pub fn new(process_context: Cint64) -> Self {
        Self {
            process_context,
            ..Default::default()
        }
    }

    /// Port of `initNominalHandlingData`.
    pub fn init_nominal_handling_data(&mut self, indi_node: SatNodeId) -> &mut Self {
        self.indi_node = indi_node;
        self.delayed_nominal_con_sat_process_linker = INVALID;
        self.delayed_nominal_indi_sat_process_linker = INVALID;
        self.delayed_nominal_indi_sat_process_linker_queued = false;
        self.succ_connected_nominal_set = SuccessorConnectedNominalSetId::NONE;
        self
    }

    /// `getSuccessorConnectedNominalSet(false)`.
    pub fn get_successor_connected_nominal_set(&self) -> SuccessorConnectedNominalSetId {
        self.succ_connected_nominal_set
    }

    /// Port of `setDelayedNominalConceptSaturationProcessLinker`.
    pub fn set_delayed_nominal_concept_saturation_process_linker(
        &mut self,
        linker: Cint64,
    ) -> &mut Self {
        self.delayed_nominal_con_sat_process_linker = linker;
        self
    }
}
