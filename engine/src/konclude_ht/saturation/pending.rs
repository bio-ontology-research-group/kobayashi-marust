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
