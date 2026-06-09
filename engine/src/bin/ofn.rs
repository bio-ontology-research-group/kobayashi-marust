//! `ofn`: OWL functional-syntax normalisation frontend.
//!
//! Usage: `ofn <ontology.ofn>`. Reads the `.ofn` file, runs the Rust port of
//! the moose SROIQ normalisation + augment pipeline, and prints
//! `{"clauses":[...], "iri_map":{...}, "named":[...], "declared":[...]}` to
//! stdout. The `clauses` array is structurally equivalent (modulo
//! internal-symbol renaming) to `frontend.ofn_to_clauses(path)`.
//!
//! This is a FRONTEND, not the reasoner: it never saturates or classifies.

use std::process::exit;

use kobayashi_marust::frontend::ofn_to_clauses;
use kobayashi_marust::json_io::JClause;
use serde::Serialize;

#[derive(Serialize)]
struct Output {
    clauses: Vec<JClause>,
    iri_map: std::collections::BTreeMap<String, String>,
    named: Vec<String>,
    declared: Vec<String>,
    el_rbox_safe: bool,
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: ofn <ontology.ofn>");
        exit(2);
    }
    let path = &args[1];
    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("failed to read {}: {}", path, e);
            exit(1);
        }
    };
    let result = match ofn_to_clauses(&text) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("out of fragment: {}", e.0);
            exit(3);
        }
    };
    let out = Output {
        clauses: result.clauses,
        iri_map: result.iri_map,
        named: result.named,
        declared: result.declared,
        el_rbox_safe: result.el_rbox_safe,
    };
    // Stream the JSON straight to a buffered stdout instead of building the
    // whole output string in memory first (the clause array is O(ontology size)
    // and dominates peak memory on large ontologies).
    let stdout = std::io::stdout();
    let mut w = std::io::BufWriter::new(stdout.lock());
    if let Err(e) = serde_json::to_writer(&mut w, &out) {
        eprintln!("serialise error: {}", e);
        exit(1);
    }
    use std::io::Write;
    let _ = w.write_all(b"\n");
    let _ = w.flush();
}
