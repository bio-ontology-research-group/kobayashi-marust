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

//! `preprocess` — ports of `Reasoner/Preprocess/*` (the ontology-rewriting
//! passes that run between build and calculation).
//!
//! First unit: `CRoleChainAutomataTransformationPreProcess` — compiles
//! transitive roles / role chains / the sub-role hierarchy into role-automaton
//! state + transition concepts (`CCAQCHOOCE` / `CCAQALL` / `CCAQAND`), the
//! producer for the already-ported automat choose/AND rules in
//! `completion/u05.rs`.

pub mod role_chain_automata;

#[cfg(test)]
mod automata_test;
