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

//! `konclude_ht::cache` — W6, the cache subtree (Konclude
//! `Source/Reasoner/Kernel/Cache/`). Nine families ported as struct-definition
//! files (the `// W6-CACHE method-batch` markers flag where method bodies land
//! in a later wave). See `PORT.md` §W6.

pub mod backend;
pub mod backend_data;
pub mod backend_facade1;
pub mod backend_facade2;
pub mod backend_facade3;
pub mod backend_facade_gap;
pub mod base;
pub mod consequences;
pub mod context;
pub mod events;
pub mod occstats;
pub mod pending;
pub mod reuse;
pub mod satnode;
pub mod sigexpand;
pub mod unsat;
pub mod value;
