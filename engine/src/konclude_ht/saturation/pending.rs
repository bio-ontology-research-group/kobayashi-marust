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

//! `saturation::pending` — W4-RECONCILE minimal PORT-PENDING sibling stubs.
//!
//! The saturation-layer twin of `completion::pending`. Methods that EVERY
//! s01..s12 unit deferred (called as `self.foo(...)` but defined in no unit),
//! plus C++ overloads that Rust cannot express under one name, get ONE
//! faithful-signature stub here so the `saturation` module compiles. Bodies
//! return a neutral default; they are filled in later (W4.5/W5) fill waves.
//! Each is tagged `// W4-RECONCILE-STUB[api]: PORT-PENDING`.

#![allow(dead_code, unused_variables)]

#[allow(unused_imports)]
use super::super::model::substrate::{Cint64, Id, INVALID};

#[allow(unused_imports)]
use super::super::completion::context::CalculationAlgorithmContextBase;

impl super::algorithm::SaturationTaskHandleAlgorithm {
    // (filled in during W4-reconcile as missing siblings are discovered)
}
