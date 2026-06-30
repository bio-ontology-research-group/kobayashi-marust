//! `saturation` — the approximate-saturation pre-pass
//! (Konclude `Source/Reasoner/Kernel/Algorithm/`
//! `CCalculationTableauApproximationSaturationTaskHandleAlgorithm.{h,cpp}`).
//!
//! The cheap, non-branching, deterministic tableau-style saturation that runs
//! BEFORE the full backtracking completion: it applies the expansion rules but
//! never case-splits (disjunctions fold into a common-disjunct over-approximation,
//! successors merge rather than branch), and per concept/individual computes a
//! saturated label plus insufficiency / criticality flags marking where the cheap
//! over-approximation is unsound (the spots a real completion must revisit). See
//! `manifest/03-saturation-calc.md`.
//!
//! W4 ports the STRUCT DEFINITION (member fields) here; the ~195 method bodies
//! land later as the `SAT u01..u12` batches (see `manifest/03-saturation-calc.md`).
//!
//! KONCLUDE-PORT-NOTE[ownership]: like the `completion/` layer, the saturation
//! task-handle algorithm is NOT arena-allocated — Konclude holds exactly one PER
//! WORKER THREAD (built by the `CTaskHandleAlgorithmBuilder` injection seam). It
//! is therefore a plain owned Rust struct, not an `Id<T>`-addressed arena element;
//! there are no saturation-layer id aliases.

pub mod stubs;     // W4: saturation-layer not-yet-ported placeholder markers
pub mod satellites; // W4.5: saturation-layer per-test satellites (linkers/descriptors/label-set)
pub mod algorithm; // W4: CCalculationTableauApproximationSaturationTaskHandleAlgorithm — fields

// W4 method-batch units SAT u01..u12 (the ~195 apply*Rule / driver / node-init /
// ATMOST-merging / critical-concept / extension-propagation / cache-handoff
// method bodies — see manifest/03-saturation-calc.md). Reconciled in W4-reconcile.
pub mod s01;
pub mod s02;
pub mod s03;
pub mod s04;
pub mod s05;
pub mod s06;
pub mod s07;
pub mod s08;
pub mod s09;
pub mod s10;
pub mod s11;
pub mod s12;

// W4-RECONCILE: minimal PORT-PENDING sibling stubs (the cross-unit `self.foo(...)`
// calls defined in no s-unit). See completion/pending.rs for the W3 twin.
pub mod pending;
