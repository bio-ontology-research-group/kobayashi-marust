//! `kobayashi-marust` library: shared modules for the reasoner binary and the
//! `.ofn` normalisation frontend (`bin/ofn.rs`).
//!
//! The reasoner pipeline (`calc`/`clause`/`engine`/`reasoner`) and the JSON
//! clause schema (`json_io`) are exposed here so both the main reasoner binary
//! and the standalone frontend can reuse the exact same serde types for the
//! `{"clauses":[...]}` contract.

pub mod calc;
pub mod cli;
pub mod clause;
pub mod elcomplete;
pub mod engine;
pub mod frontend;
pub mod json_io;
pub mod orchestrate;
pub mod reasoner;
pub mod tableau;
