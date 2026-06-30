//! `task::task_data` — the per-test result record family → one tagged enum.
//!
//! Ports the `overtakeData()` family Konclude declares across
//! `Source/Reasoner/Kernel/Task/CConsistenceTaskData.h`,
//! `CIncrementalConsistenceTaskData.h` (`: public CConsistenceTaskData`), and
//! `CSaturationTaskData.h`. A small inheritance family with a virtual
//! `overtakeData()`, ported as ONE tagged `TaskData` enum with a single
//! `overtake_data` match — mirroring the W2 `DependencyNode`/`DepKind` decision.
//! Incremental "extends" Consistence, so its extra fields flatten into the
//! `IncrementalConsistence` variant.
//!
//! These records are consumed OUTSIDE the kernel (Consistiser / Realizer call
//! `overtakeData()` to pull the boolean/model out of a finished task); a
//! classification-only run exercises only `Consistence` + `Saturation`.

#![allow(dead_code)]

use std::collections::HashSet;

use super::super::model::substrate::{Cint64, Id, INVALID};
use super::satisfiable_task::SatTaskId;

/// `CConsistenceTaskData*` (a previous incremental record) → `TaskDataId`.
pub type TaskDataId = Id<TaskData>;

/// Port of the `C*TaskData` `overtakeData()` family.
///
/// KONCLUDE-PORT-NOTE[ownership]: the C++ family inherits from
/// `CConsistenceData` / `CSaturationData` (consumed by the Consistiser /
/// Realizer); the variant payloads hold the finished `CSatisfiableCalculationTask*`
/// as `SatTaskId`. `mPrevOntology` (`CConcreteOntology*`) is opaque [api]; the
/// previous-consistence-data back-pointer is a `TaskDataId` (self-referential).
#[derive(Debug, Clone)]
pub enum TaskData {
    /// Port of `CConsistenceTaskData` (`: public CConsistenceData`).
    Consistence {
        /// `CSatisfiableCalculationTask* mDetSatTask`.
        det_sat_task: SatTaskId,
        /// `CSatisfiableCalculationTask* mGraphCachedSatTask`.
        graph_cached_sat_task: SatTaskId,
    },
    /// Port of `CIncrementalConsistenceTaskData` (`: public CConsistenceTaskData`;
    /// flattens the base's two task fields + the seven incremental fields).
    IncrementalConsistence {
        /// inherited `mDetSatTask`.
        det_sat_task: SatTaskId,
        /// inherited `mGraphCachedSatTask`.
        graph_cached_sat_task: SatTaskId,
        /// `QSet<cint64> mIndirectlyChangedNodeSet`.
        indirectly_changed_node_set: HashSet<Cint64>,
        /// `QSet<cint64> mDeterministicallyChangedNodeSet`.
        deterministically_changed_node_set: HashSet<Cint64>,
        /// `QSet<cint64> mChangedCompatibleNodeSet`.
        changed_compatible_node_set: HashSet<Cint64>,
        /// `CConcreteOntology* mPrevOntology`. [api] opaque.
        prev_ontology: Cint64,
        /// `CConsistenceTaskData* mPrevConsData`.
        prev_cons_data: TaskDataId,
        /// `cint64 mAddedNodeCount`.
        added_node_count: Cint64,
        /// `cint64 mTotalNodeCount`.
        total_node_count: Cint64,
        /// `cint64 mPreviousNodeCount`.
        previous_node_count: Cint64,
    },
    /// Port of `CSaturationTaskData` (`: public CSaturationData`).
    Saturation {
        /// `CSatisfiableCalculationTask* mSaturationTask`.
        saturation_task: SatTaskId,
    },
}

impl TaskData {
    /// Port of `CConsistenceTaskData::CConsistenceTaskData`.
    pub fn new_consistence(det_sat_task: SatTaskId, graph_cached_sat_task: SatTaskId) -> Self {
        TaskData::Consistence {
            det_sat_task,
            graph_cached_sat_task,
        }
    }
    /// Port of `CSaturationTaskData::CSaturationTaskData`.
    pub fn new_saturation(saturation_task: SatTaskId) -> Self {
        TaskData::Saturation { saturation_task }
    }
    /// Port of `CIncrementalConsistenceTaskData::CIncrementalConsistenceTaskData`.
    pub fn new_incremental_consistence(
        det_sat_task: SatTaskId,
        graph_cached_sat_task: SatTaskId,
        prev_ontology: Cint64,
        prev_cons_data: TaskDataId,
    ) -> Self {
        TaskData::IncrementalConsistence {
            det_sat_task,
            graph_cached_sat_task,
            indirectly_changed_node_set: HashSet::new(),
            deterministically_changed_node_set: HashSet::new(),
            changed_compatible_node_set: HashSet::new(),
            prev_ontology,
            prev_cons_data,
            added_node_count: 0,
            total_node_count: 0,
            previous_node_count: 0,
        }
    }
    /// Port of the virtual `overtakeData()` for all three records (single match).
    ///
    /// Marks the finished task(s) + their parent chains as NOT memory-releaseable,
    /// so the consuming Consistiser / Realizer can read the model out before the
    /// task pool is reclaimed. `CIncrementalConsistenceTaskData` does NOT override
    /// `overtakeData`, so it uses the `CConsistenceTaskData` body (the det + the
    /// graph-cached chain), matched here for both consistence variants.
    ///
    /// W6-DEFER[api]: setting `taskIt->getTaskStatus()->setMemoryReleaseable(false)`
    /// and walking `taskIt->getParentTask()` derefs a `SatTaskId` to its by-value
    /// status + parent, which needs the (not-yet-ported) task arena. The
    /// task-selection control flow is faithful; the per-task status write is
    /// deferred.
    pub fn overtake_data(&self) -> bool {
        match self {
            TaskData::Consistence { det_sat_task, graph_cached_sat_task }
            | TaskData::IncrementalConsistence { det_sat_task, graph_cached_sat_task, .. } => {
                // if (mDetSatTask) mDetSatTask->getTaskStatus()->setMemoryReleaseable(false);
                let _ = det_sat_task;
                // if (mGraphCachedSatTask) { for taskIt in chain { taskIt.status.setMemoryReleaseable(false); taskIt = taskIt.getParentTask(); } }
                let _ = graph_cached_sat_task;
            }
            TaskData::Saturation { saturation_task } => {
                // if (mSaturationTask) mSaturationTask->getTaskStatus()->setMemoryReleaseable(false);
                // for taskIt in parent-chain(mSaturationTask) { taskIt.status.setMemoryReleaseable(false); }
                let _ = saturation_task;
            }
        }
        true
    }

    /// Port of `CConsistenceTaskData::getDeterministicSatisfiableTask` (consistence
    /// variants only; `Id::NONE` for `Saturation`).
    pub fn get_deterministic_satisfiable_task(&self) -> SatTaskId {
        match self {
            TaskData::Consistence { det_sat_task, .. }
            | TaskData::IncrementalConsistence { det_sat_task, .. } => *det_sat_task,
            TaskData::Saturation { .. } => SatTaskId::NONE,
        }
    }

    /// Port of `CConsistenceTaskData::getCompletionGraphCachedSatisfiableTask`
    /// (consistence variants only; `Id::NONE` for `Saturation`).
    pub fn get_completion_graph_cached_satisfiable_task(&self) -> SatTaskId {
        match self {
            TaskData::Consistence { graph_cached_sat_task, .. }
            | TaskData::IncrementalConsistence { graph_cached_sat_task, .. } => *graph_cached_sat_task,
            TaskData::Saturation { .. } => SatTaskId::NONE,
        }
    }

    /// Port of `CSaturationTaskData::getSaturationTask` (`Saturation` only).
    pub fn get_saturation_task(&self) -> SatTaskId {
        match self {
            TaskData::Saturation { saturation_task } => *saturation_task,
            _ => SatTaskId::NONE,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::getIndirectlyChangedNodeSet`.
    pub fn get_indirectly_changed_node_set(&self) -> Option<&HashSet<Cint64>> {
        match self {
            TaskData::IncrementalConsistence { indirectly_changed_node_set, .. } => Some(indirectly_changed_node_set),
            _ => None,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::getDeterministicallyChangedNodeSet`.
    pub fn get_deterministically_changed_node_set(&self) -> Option<&HashSet<Cint64>> {
        match self {
            TaskData::IncrementalConsistence { deterministically_changed_node_set, .. } => Some(deterministically_changed_node_set),
            _ => None,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::getChangedCompatibleNodeSet`.
    pub fn get_changed_compatible_node_set(&self) -> Option<&HashSet<Cint64>> {
        match self {
            TaskData::IncrementalConsistence { changed_compatible_node_set, .. } => Some(changed_compatible_node_set),
            _ => None,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::getPreviousOntology`. [api] opaque.
    pub fn get_previous_ontology(&self) -> Cint64 {
        match self {
            TaskData::IncrementalConsistence { prev_ontology, .. } => *prev_ontology,
            _ => INVALID,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::getPreviousConsistenceData`.
    pub fn get_previous_consistence_data(&self) -> TaskDataId {
        match self {
            TaskData::IncrementalConsistence { prev_cons_data, .. } => *prev_cons_data,
            _ => TaskDataId::NONE,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::setPreviousOntology`.
    pub fn set_previous_ontology(&mut self, prev_ontology: Cint64) -> &mut Self {
        if let TaskData::IncrementalConsistence { prev_ontology: po, .. } = self {
            *po = prev_ontology;
        }
        self
    }

    /// Port of `CIncrementalConsistenceTaskData::setPreviousConsistenceData`.
    pub fn set_previous_consistence_data(&mut self, prev_cons_data: TaskDataId) -> &mut Self {
        if let TaskData::IncrementalConsistence { prev_cons_data: pc, .. } = self {
            *pc = prev_cons_data;
        }
        self
    }

    /// Port of `CIncrementalConsistenceTaskData::getAddedNodeCount`.
    pub fn get_added_node_count(&self) -> Cint64 {
        match self {
            TaskData::IncrementalConsistence { added_node_count, .. } => *added_node_count,
            _ => 0,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::getTotalNodeCount`.
    pub fn get_total_node_count(&self) -> Cint64 {
        match self {
            TaskData::IncrementalConsistence { total_node_count, .. } => *total_node_count,
            _ => 0,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::getPreviousNodeCount`.
    pub fn get_previous_node_count(&self) -> Cint64 {
        match self {
            TaskData::IncrementalConsistence { previous_node_count, .. } => *previous_node_count,
            _ => 0,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::getChangedCompatibleNodeCount`
    /// (`mChangedCompatibleNodeSet.count()`).
    pub fn get_changed_compatible_node_count(&self) -> Cint64 {
        match self {
            TaskData::IncrementalConsistence { changed_compatible_node_set, .. } => changed_compatible_node_set.len() as Cint64,
            _ => 0,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::getDeterministicallyChangedNodeCount`.
    pub fn get_deterministically_changed_node_count(&self) -> Cint64 {
        match self {
            TaskData::IncrementalConsistence { deterministically_changed_node_set, .. } => deterministically_changed_node_set.len() as Cint64,
            _ => 0,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::getIndirectlyChangedCount`.
    pub fn get_indirectly_changed_count(&self) -> Cint64 {
        match self {
            TaskData::IncrementalConsistence { indirectly_changed_node_set, .. } => indirectly_changed_node_set.len() as Cint64,
            _ => 0,
        }
    }

    /// Port of `CIncrementalConsistenceTaskData::setAddedNodeCount`.
    pub fn set_added_node_count(&mut self, added_node_count: Cint64) -> &mut Self {
        if let TaskData::IncrementalConsistence { added_node_count: a, .. } = self {
            *a = added_node_count;
        }
        self
    }

    /// Port of `CIncrementalConsistenceTaskData::setTotalNodeCount`.
    pub fn set_total_node_count(&mut self, total_node_count: Cint64) -> &mut Self {
        if let TaskData::IncrementalConsistence { total_node_count: t, .. } = self {
            *t = total_node_count;
        }
        self
    }

    /// Port of `CIncrementalConsistenceTaskData::setPreviousNodeCount`.
    pub fn set_previous_node_count(&mut self, prev_node_count: Cint64) -> &mut Self {
        if let TaskData::IncrementalConsistence { previous_node_count: p, .. } = self {
            *p = prev_node_count;
        }
        self
    }
}
