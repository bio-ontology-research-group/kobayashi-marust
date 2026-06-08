//! CLI for the hypertableau consistency checker / classifier (milestone M1).
//! Reads a `TInput` JSON on stdin, writes a `TOutput` JSON on stdout. See
//! `tableau.rs` for the schema and `docs/HYBRID-TABLEAU.md` for the design.

#[path = "../tableau.rs"]
mod tableau;

use std::io::{Read, Write};

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

fn main() {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();
    let mut buf = String::new();
    if let Err(e) = std::io::stdin().read_to_string(&mut buf) {
        eprintln!("failed to read stdin: {e}");
        std::process::exit(1);
    }
    match tableau::run_json(&buf) {
        Ok(s) => {
            let stdout = std::io::stdout();
            let mut h = stdout.lock();
            h.write_all(s.as_bytes()).expect("write stdout");
            h.write_all(b"\n").expect("write newline");
        }
        Err(e) => {
            eprintln!("tableau error: {e}");
            std::process::exit(1);
        }
    }
}
