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

//! `process::sat_linker` — port of `CIndividualSaturationProcessNodeLinker`.
//!
//! Konclude implements this as `CNegLinkerBase<CIndividualSaturationProcessNode*, Self>`:
//! the data pointer is the saturation node, and the negation bit stores whether
//! the node is currently queued for processing.

#![allow(dead_code)]

use super::super::model::substrate::Id;
use super::SatNodeId;

/// `CIndividualSaturationProcessNodeLinker*`.
pub type IndividualSaturationProcessNodeLinkerId = Id<IndividualSaturationProcessNodeLinker>;

/// Port of `CIndividualSaturationProcessNodeLinker`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndividualSaturationProcessNodeLinker {
    /// `CNegLinkerBase` data (`getData()`).
    pub processing_individual: SatNodeId,
    /// `CNegLinkerBase` negation bit (`isNegated()`).
    pub processing_queued: bool,
    /// Intrusive next pointer from the linker base.
    pub next: IndividualSaturationProcessNodeLinkerId,
}

impl Default for IndividualSaturationProcessNodeLinker {
    fn default() -> Self {
        Self {
            processing_individual: SatNodeId::NONE,
            processing_queued: false,
            next: IndividualSaturationProcessNodeLinkerId::NONE,
        }
    }
}

impl IndividualSaturationProcessNodeLinker {
    /// Port of `CIndividualSaturationProcessNodeLinker::CIndividualSaturationProcessNodeLinker`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Port of `initProcessNodeLinker`.
    pub fn init_process_node_linker(
        &mut self,
        individual: SatNodeId,
        processing_queued: bool,
    ) -> &mut Self {
        self.processing_individual = individual;
        self.processing_queued = processing_queued;
        self.next = IndividualSaturationProcessNodeLinkerId::NONE;
        self
    }

    /// Port of `getProcessingIndividual`.
    pub fn get_processing_individual(&self) -> SatNodeId {
        self.processing_individual
    }

    /// Port of `isProcessingQueued`.
    pub fn is_processing_queued(&self) -> bool {
        self.processing_queued
    }

    /// Port of `clearProcessingQueued`.
    pub fn clear_processing_queued(&mut self) -> &mut Self {
        self.processing_queued = false;
        self
    }

    /// Port of `setProcessingQueued`.
    pub fn set_processing_queued(&mut self, processing_queued: bool) -> &mut Self {
        self.processing_queued = processing_queued;
        self
    }

    /// `CLinkerBase::getNext`.
    pub fn get_next(&self) -> IndividualSaturationProcessNodeLinkerId {
        self.next
    }

    /// `CLinkerBase::setNext`.
    pub fn set_next(&mut self, next: IndividualSaturationProcessNodeLinkerId) -> &mut Self {
        self.next = next;
        self
    }
}
