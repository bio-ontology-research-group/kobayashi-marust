//! `kobayashi-marust`: the consequence-based (ELK/Sequoia-style) DL saturation
//! reasoner (standalone shim).
//!
//! Reads `{ "clauses": [<dlclause>] }` on stdin and writes
//! `{ "subsumptions": {...}, "derived_clauses": [...], "inconsistent": bool }`.
//! The implementation is `kobayashi_marust::cli::run_engine`, shared with the
//! `km engine` subcommand. This binary additionally wires the optional `dhat`
//! heap profiler (a bin-level global allocator).

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

fn main() {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();
    kobayashi_marust::cli::run_engine();
}
