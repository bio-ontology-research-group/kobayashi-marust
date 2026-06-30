//! `task::stats` — the per-task statistics sink.
//!
//! Ports Konclude `Source/Reasoner/Kernel/Task/CCalculationStatisticsCollector.h`.
//! The base class is abstract (`addProcessingStatistics(name,value)` is pure
//! virtual) and declares NO data members; the concrete sink (a name→value hash
//! flushed at `completeTask`) lives in the deriving collector. Ported as a
//! zero-size marker the task holds a back-pointer to.

#![allow(dead_code)]

use super::super::model::substrate::Cint64;

/// Port of `Reasoner::Kernel::Task::CCalculationStatisticsCollector` (abstract;
/// no data members).
#[derive(Debug, Default, Clone)]
pub struct CalculationStatisticsCollector;

impl CalculationStatisticsCollector {
    /// Port of `CCalculationStatisticsCollector::CCalculationStatisticsCollector`.
    pub fn new() -> Self {
        CalculationStatisticsCollector
    }
    /// Port of `CCalculationStatisticsCollector::addProcessingStatistics`.
    ///
    /// W6-DEFER[api]: pure-virtual (`= 0`) in the C++ base; the concrete name→value
    /// hash sink (flushed at `completeTask`) lives in the deriving collector, which
    /// is not yet ported. Faithful stub.
    pub fn add_processing_statistics(&mut self, _stat_name: &str, _stat_value: Cint64) -> bool {
        false
    }
}
