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

//! `konclude_ht` — a direct, exact Rust port of Konclude's hypertableau
//! reasoning algorithm (see `PORT.md` for methodology and the source mapping).
//!
//! This module is built additively and is wired into KM from `lib.rs`. The port
//! proceeds in dependency-ordered waves; submodules are added as each wave lands.
//!
//! Porting tag taxonomy (grep `KONCLUDE-PORT-NOTE`): every place the Rust port
//! deviates from the literal C++ is annotated, so the two trees stay diffable
//! function-by-function.

// Submodules are declared here as waves land:
pub mod bridge; // Production-route input: TInput (cb_to_ht) → OntologyArenas + probe driver
pub mod cache; // W6: cache subtree (struct skeleton)
pub mod calculation;
pub mod classifier; // Optimized classifier caller seams
pub mod completion; // W3: the apply*Rule expansion engine (struct fields; bodies u01..u36)
pub mod generator; // Query-job → kernel-task generator seams
pub mod model; // W1: ontology concept/role/individual model
pub mod preprocess; // Reasoner/Preprocess ports (role-chain automata)
pub mod process; // W1/W2: the runtime completion-graph data model
pub mod realizer; // Optimized realizer caller seams
pub mod saturation; // W4: approximate saturation
pub mod task; // W6: Task/ scheduler + satisfiable-task subtree // W6: calculation controllers / task handles
