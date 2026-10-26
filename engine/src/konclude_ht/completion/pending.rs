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

//! `completion::pending` — W3-RECONCILE minimal PORT-PENDING sibling stubs.
//!
//! Methods that EVERY u01..u36 unit deferred (called as `self.foo(...)` but
//! defined in no unit), plus C++ overloads that Rust cannot express under one
//! name, get ONE faithful-signature stub here so the module compiles. Bodies
//! return a neutral default; they are filled in later fill waves. Each is
//! tagged `// W3-RECONCILE-STUB[api]: PORT-PENDING`.

#![allow(dead_code, unused_variables)]

use super::super::model::substrate::NegLink;
use super::super::model::ConceptId;
use super::super::process::LabelSetId;
use super::context::CalculationAlgorithmContextBase;

impl super::algorithm::CompletionTaskHandleAlgorithm {
    // W3-RECONCILE-STUB[api]: PORT-PENDING — the `CReapplyConceptLabelSet*` overload
    // of `containsIndividualNodeConcepts` (Konclude header overload #2,
    // `containsIndividualNodeConcepts(CReapplyConceptLabelSet*, CSortedNegLinker<CConcept*>*, bool negated, ctx)`).
    // Rust cannot overload by name; the node-keyed overload lives in u35 as
    // `contains_individual_node_concepts`, so the label-set-keyed overload gets this
    // distinct name and a faithful stub.
    pub fn contains_individual_node_concepts_for_label_set(
        &mut self,
        con_label_set: LabelSetId,
        con_test_linker: &[NegLink<ConceptId>],
        negated: bool,
        calc_alg_context: &mut CalculationAlgorithmContextBase,
    ) -> bool {
        false
    }
}
