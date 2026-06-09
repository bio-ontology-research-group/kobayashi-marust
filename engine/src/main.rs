//! `kobayashi-marust`: Rust port of the moose context-based
//! (consequence-based, ELK/Sequoia-style) DL saturation reasoner.
//!
//! Reads `{ "clauses": [<dlclause>] }` on stdin, runs the same algorithm as
//! `cbr_reference.py`, and writes
//! `{ "subsumptions": {...}, "derived_clauses": [...], "inconsistent": bool }`
//! on stdout.

use std::io::{Read, Write};

use kobayashi_marust::json_io::{JInput, JOutput};
use kobayashi_marust::reasoner::Reasoner;

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
    let input: JInput = match serde_json::from_str(&buf) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("failed to parse input JSON: {e}");
            std::process::exit(1);
        }
    };

    let mut r = Reasoner::new(&input.clauses);
    r.saturate();

    let subs = r.subsumptions();
    let subsumptions = subs
        .into_iter()
        .map(|(k, v)| (k, v.into_iter().collect::<Vec<_>>()))
        .collect();

    let out = JOutput {
        subsumptions,
        derived_clauses: r.emit_clauses(),
        inconsistent: r.inconsistent(),
        dropped: r.dropped_unsupported(),
    };

    let s = serde_json::to_string(&out).expect("serialise output");
    let stdout = std::io::stdout();
    let mut h = stdout.lock();
    h.write_all(s.as_bytes()).expect("write stdout");
    h.write_all(b"\n").expect("write newline");
}
