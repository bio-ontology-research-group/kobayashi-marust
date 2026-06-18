//! CLI for the hypertableau consistency checker / classifier (standalone shim).
//! Reads a `TInput` JSON on stdin, writes a `TOutput` JSON on stdout. The
//! implementation is `kobayashi_marust::cli::run_tableau`, shared with the
//! `km tableau` subcommand. This binary additionally wires the optional `dhat`
//! heap profiler (a bin-level global allocator).

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

fn main() {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();
    kobayashi_marust::cli::run_tableau();
}
