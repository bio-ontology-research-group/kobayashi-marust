//! `konclude_ht` — a direct, exact Rust port of Konclude's hypertableau
//! reasoning algorithm (see `PORT.md` for methodology and the source mapping).
//!
//! This module is built additively and is NOT yet wired into the rest of KM
//! (`lib.rs` does not declare it until it compiles). The port proceeds in
//! dependency-ordered waves; submodules are added as each wave lands.
//!
//! Porting tag taxonomy (grep `KONCLUDE-PORT-NOTE`): every place the Rust port
//! deviates from the literal C++ is annotated, so the two trees stay diffable
//! function-by-function.

// Submodules are declared here as waves land:
pub mod model;        // W1: ontology concept/role/individual model
pub mod process;      // W1/W2: the runtime completion-graph data model
pub mod completion;   // W3: the apply*Rule expansion engine (struct fields; bodies u01..u36)
pub mod saturation;   // W4: approximate saturation
pub mod cache;        // W6: cache subtree (struct skeleton)
pub mod task;         // W6: Task/ scheduler + satisfiable-task subtree
pub mod calculation;  // W6: calculation controllers / task handles
