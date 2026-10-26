// SPDX-License-Identifier: LGPL-3.0-only
//
// This file is part of Kobayashi-MaRust (KM). It is a Rust translation of
// source code from the reasoning system Konclude, Copyright (C) by the
// Konclude Developer Team (<http://konclude.com/>,
// <https://github.com/konclude/Konclude>), which is licensed under version 3
// of the GNU Lesser General Public License (LGPLv3). As a derivative work it
// is distributed under the same licence.
// Translation Copyright (C) 2026 Robert Hoehndorf and the Bio-Ontology
// Research Group, KAUST.
//
// This file is free software: you can redistribute it and/or modify it under
// the terms of version 3 of the GNU Lesser General Public License as published
// by the Free Software Foundation. It is distributed in the hope that it will
// be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
// General Public License for more details. Copies of the LGPLv3 and GPLv3
// accompany this repository as LICENSE-LGPL-3.0.txt and LICENSE-GPL-3.0.txt;
// see also <https://www.gnu.org/licenses/>.

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
