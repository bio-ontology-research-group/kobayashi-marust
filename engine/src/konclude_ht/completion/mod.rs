//! `completion` — the SROIQ hypertableau completion engine
//! (Konclude `Source/Reasoner/Kernel/Algorithm/`).
//!
//! Layer 7 of the type-dependency DAG (`manifest/00-type-dag.md`): the per-thread
//! algorithm context (`CCalculationAlgorithmContext` /
//! `CCalculationAlgorithmContextBase`) and the completion task-handle algorithm
//! (`CCalculationTableauCompletionTaskHandleAlgorithm`) that drives every
//! `apply*Rule` over the `process/` completion-graph data model.
//!
//! W3 ports the STRUCT DEFINITIONS (member fields) here; the ~450 method bodies
//! land later as the `u01..u36` batches (see `manifest/01-completion-methods.md`).
//!
//! KONCLUDE-PORT-NOTE[ownership]: unlike the `model/` and `process/` layers, the
//! context and the algorithm are NOT arena-allocated — Konclude holds exactly one
//! of each PER WORKER THREAD (created in `createCalculationAlgorithmContext`).
//! They are therefore plain owned Rust structs, not `Id<T>`-addressed arena
//! elements; there are no completion-layer id aliases.

pub mod stubs;     // W3: Algorithm-layer not-yet-ported placeholder markers
pub mod context;   // W3: CCalculationAlgorithmContext{,Base} — the per-thread context
pub mod algorithm; // W3: CCalculationTableauCompletionTaskHandleAlgorithm — fields
pub mod strategy;  // W3: Strategy/ rule-application priority + cache-retrieval policies
pub mod clash;     // W3c: clash/stop propagation (CCalculation{Clash,Stop}ProcessingException)
pub mod dependency_factory; // W3c: the create*Dependency allocator (CDependencyFactory)

// W3 method-batch units u01..u36 (the apply*Rule engine bodies). Wired by the
// W3-RECONCILE integrator; cross-unit disagreements reconciled in pending.rs.
pub mod u01;
pub mod u02;
pub mod u03;
pub mod u04;
pub mod u05;
pub mod u06;
pub mod u07;
pub mod u08;
pub mod u09;
pub mod u10;
pub mod u11;
pub mod u12;
pub mod u13;
pub mod u14;
pub mod u15;
pub mod u16;
pub mod u17;
pub mod u18;
pub mod u19;
pub mod u20;
pub mod u21;
pub mod u22;
pub mod u23;
pub mod u24;
pub mod u25;
pub mod u26;
pub mod u27;
pub mod u28;
pub mod u29;
pub mod u30;
pub mod u31;
pub mod u32;
pub mod u33;
pub mod u34;
pub mod u35;
pub mod u36;
pub mod pending;   // W3-RECONCILE: minimal PORT-PENDING sibling stubs (api gaps)
