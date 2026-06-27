//! `km`: the multi-call entry point — the whole reasoner in one binary.
//!
//!   `km classify [--lines] <ont.ofn>`  the pure-Rust classify orchestrator
//!                                      (replacement for `owl_classify.py`)
//!   `km ofn|elc|engine|tableau`        the worker reasoners
//!
//! `km classify` spawns the workers by re-invoking ITSELF with the worker
//! subcommand (`current_exe()` + `ofn`/`elc`/`engine`/`tableau`), unless a
//! `KM_*_BIN` env var overrides a worker with a standalone binary. The standalone
//! `ofn`/`elc`/`kobayashi-marust`/`tableau_cli` binaries remain as thin shims
//! over the same `cli::*` entrypoints. Either way, classifying needs no Python.

use std::path::Path;
use std::process::exit;

use kobayashi_marust::cli;
use kobayashi_marust::orchestrate::{self, Config, OrchestrateError};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("classify") => classify_cmd(&args[2..]),
        // worker subcommands: the orchestrator re-invokes `km <sub>` for these.
        Some("ofn") => cli::run_ofn(&args[2..]),
        Some("elc") => cli::run_elc(),
        Some("engine") => cli::run_engine(),
        Some("tableau") => cli::run_tableau(),
        // routing features: the structural + DL-construct vector the decision-tree
        // router consumes. `km features <ont>...` prints one JSON object per
        // ontology (NDJSON for >1) — same code path used at classify time.
        Some("features") => features_cmd(&args[2..]),
        // hidden debug subcommand: stdin {clauses, rbox?} -> TInput JSON (the
        // Phase-2 byte-identity gate vs engine/py/cb_to_ht.py)
        Some("cb_to_ht") => cb_to_ht_cmd(),
        _ => {
            eprintln!("usage: km classify [--lines] <ontology.ofn>");
            eprintln!("       km features <ontology.ofn> ...");
            eprintln!("       km ofn|elc|engine|tableau   (worker subcommands)");
            exit(2);
        }
    }
}

fn features_cmd(rest: &[String]) {
    let onts: Vec<&str> = rest.iter().map(String::as_str).filter(|a| !a.starts_with("--")).collect();
    if onts.is_empty() {
        eprintln!("usage: km features <ontology.ofn> ...");
        exit(2);
    }
    let cfg = Config::from_env();
    let multi = onts.len() > 1;
    let stdout = std::io::stdout();
    let mut w = stdout.lock();
    use std::io::Write;
    for o in onts {
        let f = orchestrate::features::extract(&cfg, Path::new(o));
        if multi {
            // NDJSON: one compact object per line (the training-table format)
            let _ = serde_json::to_writer(&mut w, &f);
            let _ = w.write_all(b"\n");
        } else {
            let s = serde_json::to_string_pretty(&f).unwrap_or_default();
            let _ = writeln!(w, "{s}");
        }
    }
    let _ = w.flush();
}

fn cb_to_ht_cmd() {
    use kobayashi_marust::json_io::JClause;
    use std::io::Read;
    #[derive(serde::Deserialize)]
    struct CbInput {
        clauses: Vec<JClause>,
        #[serde(default)]
        rbox: Option<Vec<Vec<String>>>,
        #[serde(default)]
        cardinalities: Vec<kobayashi_marust::json_io::CardMeta>,
        #[serde(default)]
        rules: Vec<kobayashi_marust::json_io::JRule>,
    }
    let mut buf = String::new();
    if std::io::stdin().read_to_string(&mut buf).is_err() {
        eprintln!("failed to read stdin");
        exit(1);
    }
    let input: CbInput = match serde_json::from_str(&buf) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("bad input JSON: {e}");
            exit(1);
        }
    };
    let named = std::collections::HashSet::new();
    let tin = orchestrate::cb_to_ht::convert(&input.clauses, input.rbox.as_deref(), &named, &input.cardinalities, std::env::var_os("KM_HT_CARD").is_some(), &input.rules, std::env::var_os("KM_HT_RULES").is_some());
    let stdout = std::io::stdout();
    if let Err(e) = serde_json::to_writer(stdout.lock(), &tin) {
        eprintln!("serialise error: {e}");
        exit(1);
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
