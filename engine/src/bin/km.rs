//! `km`: the multi-call entry point. `km classify <ont.ofn>` is the pure-Rust
//! classify orchestrator (the replacement for `engine/py/owl_classify.py`); it
//! spawns the worker reasoners (`ofn`/`elc`/`kobayashi-marust`/`tableau_cli`)
//! resolved as siblings of this binary (or via the `KM_*_BIN` env overrides).
//!
//! Worker subcommands (`km ofn|elc|engine|tableau`) collapse the standalone
//! binaries into this one in a later phase; for now the orchestrator simply
//! spawns the existing sibling binaries, so classifying needs no Python.

use std::path::Path;
use std::process::exit;

use kobayashi_marust::orchestrate::{self, Config, OrchestrateError};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("classify") => classify_cmd(&args[2..]),
        _ => {
            eprintln!("usage: km classify [--lines] <ontology.ofn>");
            exit(2);
        }
    }
}

fn classify_cmd(rest: &[String]) {
    let lines = rest.iter().any(|a| a == "--lines");
    let positional: Vec<&str> = rest
        .iter()
        .map(String::as_str)
        .filter(|a| !a.starts_with("--"))
        .collect();
    if positional.len() != 1 {
        eprintln!("usage: km classify [--lines] <ontology.ofn>");
        exit(2);
    }
    let cfg = Config::from_env();
    match orchestrate::classify(&cfg, Path::new(positional[0])) {
        Ok(res) => {
            use std::io::Write;
            let stdout = std::io::stdout();
            let mut w = stdout.lock();
            if lines {
                let _ = writeln!(w, "{}", res.to_lines());
            } else {
                let _ = w.write_all(&res.to_json());
                let _ = w.write_all(b"\n");
            }
            let _ = w.flush();
        }
        // honest decline: outside the supported fragment (datatypes)
        Err(OrchestrateError::OutOfFragment(e)) => {
            eprintln!("unsupported: {e}");
            exit(3);
        }
        Err(e) => {
            eprintln!("{e}");
            exit(1);
        }
    }
}
