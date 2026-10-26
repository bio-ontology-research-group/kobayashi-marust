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

//! `calculation` — the Calculation/ entry controllers (Konclude
//! `Source/Reasoner/Kernel/Calculation/`): the manager / environment / factory /
//! builder classes that drive the two `CTaskHandleAlgorithm`s — the full tableau
//! completion (`completion::algorithm::CompletionTaskHandleAlgorithm`) and the
//! approximate-saturation pre-pass (`saturation::algorithm::SaturationTaskHandleAlgorithm`).
//!
//! Control flow (cpp): `ConfigDependedCalculationFactory::createCalculationManager`
//! → `ConcurrentTaskCalculationManager`; `initializeManager` hands it a
//! `ConfigDependedCalculationEnvironmentFactory` (carrying a
//! `TaskHandleAlgorithmBuilder`); `createCalculationContext` builds the
//! `ConcurrentTaskCalculationEnvironment` thread pool, each worker thread getting
//! its OWN freshly built task-handle algorithm + per-thread memory pool. Per job,
//! `calculateTask` posts a satisfiability task to the scheduler thread.
//!
//! Struct-definition wave (W4) only — every method body is deferred behind a
//! `// W4-CALC method-batch` marker. NOT yet wired into `konclude_ht/mod.rs`.

#![allow(dead_code)]

use super::model::substrate::Id;

pub mod builder; // CTaskHandleAlgorithmBuilder (the completion/saturation seam)
pub mod env_factory; // CCalculationEnvironmentFactory + CConfigDependedCalculationEnvironmentFactory
pub mod environment; // CCalculationEnviroment + CConcurrentTaskCalculationEnvironment
pub mod factory; // CCalculationFactory + CConfigDependedCalculationFactory
pub mod manager; // CCalculationManager + CConcurrentTaskCalculationManager (the ENTRY point)

// --- calculation-layer ids ---
/// `CTaskHandleAlgorithmBuilder*` → `TaskHandleAlgorithmBuilderId`.
/// KONCLUDE-PORT-NOTE[ownership]: a non-owning, ctor-injected handle (the builder
/// is owned by the caller that wires the calculation factory).
pub type TaskHandleAlgorithmBuilderId = Id<builder::TaskHandleAlgorithmBuilder>;
