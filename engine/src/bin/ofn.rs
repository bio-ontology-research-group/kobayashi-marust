//! `ofn`: OWL functional-syntax normalisation frontend.
//!
//! Usage:
//!   `ofn <ontology.ofn>`
//!       prints `{"clauses":[...], "iri_map":{...}, "named":[...],
//!       "declared":[...], "el_rbox_safe":<bool>}` to stdout (one object).
//!   `ofn <ontology.ofn> --meta <meta.json>`
//!       prints ONLY `{"clauses":[...]}` to stdout (the exact engine/elc stdin
//!       contract) and writes the side data `{iri_map, named, declared,
//!       el_rbox_safe}` to `<meta.json>`. This lets `owl_classify` stream the
//!       (large) clause set straight into the reasoner via a file without ever
//!       parsing+re-serialising it in Python — the clause round-trip dominated
//!       the EL fast path on big ontologies.
//!
//! The `clauses` array is structurally equivalent (modulo internal-symbol
//! renaming) to `frontend.ofn_to_clauses(path)`.
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
    abox_inconsistent: bool,
}

/// Side data written to the `--meta` file: everything `owl_classify` needs to
/// map the reasoner's output back to OWL, minus the clauses themselves.
#[derive(Serialize)]
struct Meta {
    iri_map: std::collections::BTreeMap<String, String>,
    named: Vec<String>,
    declared: Vec<String>,
    el_rbox_safe: bool,
    abox_inconsistent: bool,
}

#[derive(Serialize)]
struct ClausesOnly {
    clauses: Vec<JClause>,
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: ofn <ontology.ofn> [--meta <meta.json>]");
        exit(2);
    }
    let path = &args[1];
    // optional `--meta <path>`: split clauses (stdout) from side data (file).
    let meta_path: Option<&str> = match args.get(2).map(String::as_str) {
        Some("--meta") => match args.get(3) {
            Some(p) => Some(p.as_str()),
            None => {
                eprintln!("--meta requires a path argument");
                exit(2);
            }
        },
        _ => None,
    };
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
    use std::io::Write;
    // Stream the JSON straight to a buffered stdout instead of building the
    // whole output string in memory first (the clause array is O(ontology size)
    // and dominates peak memory on large ontologies).
    let stdout = std::io::stdout();
    let mut w = std::io::BufWriter::new(stdout.lock());

    if let Some(mp) = meta_path {
        // Split mode: side data to the meta file, clauses-only to stdout.
        let meta = Meta {
            iri_map: result.iri_map,
            named: result.named,
            declared: result.declared,
            el_rbox_safe: result.el_rbox_safe,
            abox_inconsistent: result.abox_inconsistent,
        };
        match std::fs::File::create(mp) {
            Ok(f) => {
                let mut mw = std::io::BufWriter::new(f);
                if let Err(e) = serde_json::to_writer(&mut mw, &meta) {
                    eprintln!("meta serialise error: {}", e);
                    exit(1);
                }
                let _ = mw.flush();
            }
            Err(e) => {
                eprintln!("failed to write meta {}: {}", mp, e);
                exit(1);
            }
        }
        let out = ClausesOnly {
            clauses: result.clauses,
        };
        if let Err(e) = serde_json::to_writer(&mut w, &out) {
            eprintln!("serialise error: {}", e);
            exit(1);
        }
    } else {
        let out = Output {
            clauses: result.clauses,
            iri_map: result.iri_map,
            named: result.named,
            declared: result.declared,
            el_rbox_safe: result.el_rbox_safe,
            abox_inconsistent: result.abox_inconsistent,
        };
        if let Err(e) = serde_json::to_writer(&mut w, &out) {
            eprintln!("serialise error: {}", e);
            exit(1);
        }
    }
    let _ = w.write_all(b"\n");
    let _ = w.flush();
}
