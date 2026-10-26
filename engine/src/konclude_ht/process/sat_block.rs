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

//! `process::sat_block` — port of `CIndividualNodeSaturationBlockingData`.
//!
//! This tiny process satellite connects a completion-graph individual to the
//! saturation node whose completed label can be used for saturation expansion
//! cache writes.

#![allow(dead_code)]

use super::super::model::substrate::{Cint64, Id};
use super::{ConDescId, SatNodeId};

/// Port of `CIndividualNodeSaturationBlockingData`.
#[derive(Clone)]
pub struct IndividualNodeSaturationBlockingData {
    /// `cint64 mSaturationBlockedConceptCount`.
    pub saturation_blocked_concept_count: Cint64,
    /// `CConceptDescriptor* mLastConfConDes`.
    pub last_confirmed_concept_descriptor: ConDescId,
    /// `CIndividualSaturationProcessNode* mSaturationNode`.
    pub saturation_node: SatNodeId,
}

impl Default for IndividualNodeSaturationBlockingData {
    fn default() -> Self {
        Self {
            saturation_blocked_concept_count: 0,
            last_confirmed_concept_descriptor: Id::NONE,
            saturation_node: Id::NONE,
        }
    }
}

impl IndividualNodeSaturationBlockingData {
    /// Port of `CIndividualNodeSaturationBlockingData::CIndividualNodeSaturationBlockingData`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initSaturationBlockingData`.
    pub fn init_saturation_blocking_data(
        &mut self,
        cached_concept_count: Cint64,
        last_confirmed_concept_descriptor: ConDescId,
        saturation_node: SatNodeId,
    ) -> &mut Self {
        self.saturation_blocked_concept_count = cached_concept_count;
        self.last_confirmed_concept_descriptor = last_confirmed_concept_descriptor;
        self.saturation_node = saturation_node;
        self
    }

    /// Port of `setSaturationBlockedConceptCount`.
    pub fn set_saturation_blocked_concept_count(&mut self, cached_count: Cint64) -> &mut Self {
        self.saturation_blocked_concept_count = cached_count;
        self
    }

    /// Port of `getSaturationBlockedConceptCount`.
    pub fn get_saturation_blocked_concept_count(&self) -> Cint64 {
        self.saturation_blocked_concept_count
    }

    /// Port of `getLastConfirmedConceptDescriptior`.
    pub fn get_last_confirmed_concept_descriptior(&self) -> ConDescId {
        self.last_confirmed_concept_descriptor
    }

    /// Port of `getSaturationIndividualNode`.
    pub fn get_saturation_individual_node(&self) -> SatNodeId {
        self.saturation_node
    }
}
