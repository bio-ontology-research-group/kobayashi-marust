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
        // Single-pass Konclude-compatible expressivity and structural stats.
        // The same profile is carried by the normal classify frontend meta, so
        // offline training and production routing cannot drift.
        Some("profile") => profile_cmd(&args[2..]),
        Some("routes") => routes_cmd(),
        // routing features: the structural + DL-construct vector the decision-tree
        // router consumes. `km features <ont>...` prints one JSON object per
        // ontology (NDJSON for >1) — same code path used at classify time.
        Some("features") => features_cmd(&args[2..]),
        // hidden debug subcommand: stdin {clauses, rbox?} -> TInput JSON (the
        // Phase-2 byte-identity gate vs engine/py/cb_to_ht.py)
        Some("cb_to_ht") => cb_to_ht_cmd(),
        _ => {
            eprintln!("usage: km classify [--lines] [--route ROUTE] <ontology.ofn>");
            eprintln!("       km features <ontology.ofn> ...");
            eprintln!("       km profile <ontology.ofn> ...");
            eprintln!("       km routes");
            eprintln!("       km ofn|elc|engine|tableau   (worker subcommands)");
            exit(2);
        }
    }
}

fn routes_cmd() {
    println!("auto\tlearned source-profile decision tree (classify default)");
    println!("manual\tpreserve individually supplied KM_* options");
    for route in kobayashi_marust::routing::Route::NAMED {
        println!("{}", route.as_str());
    }
}

fn profile_cmd(rest: &[String]) {
    #[derive(serde::Serialize)]
    struct ProfileRow {
        ont: String,
        status: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        el_rbox_safe: Option<bool>,
        #[serde(skip_serializing_if = "Option::is_none")]
        profile: Option<kobayashi_marust::frontend::profile::OntologyProfile>,
        #[serde(skip_serializing_if = "Option::is_none")]
        error: Option<String>,
    }

    let onts: Vec<&str> = rest
        .iter()
        .map(String::as_str)
        .filter(|a| !a.starts_with("--"))
        .collect();
    if onts.is_empty() {
        eprintln!("usage: km profile <ontology.ofn> ...");
        exit(2);
    }
    // Full statistics are intentionally opt-in on the normal frontend path so
    // the production classifier does not rescan its complete clause vector.
    std::env::set_var("KM_PROFILE_CLAUSES", "1");
    // Corpus profiles use the stable plain frontend. A caller can still obtain
    // route-specific clauses via `km classify --route ...`; source statistics
    // and expressivity are route-independent.
    kobayashi_marust::routing::Route::CbPlain16.apply_environment();
    std::env::set_var("KM_ROUTE", "manual");
    let cfg = Config::from_env();
    let multi = onts.len() > 1;
    let stdout = std::io::stdout();
    let mut w = stdout.lock();
    use std::io::Write;
    for ont in onts {
        let path = Path::new(ont);
        let name = path
            .file_name()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| ont.to_string());
        let row = match orchestrate::frontend_run::run_ofn_split(&cfg, path) {
            Ok((_clauses, meta)) => ProfileRow {
                ont: name,
                status: "ok".to_string(),
                el_rbox_safe: Some(meta.el_rbox_safe),
                profile: Some(meta.profile),
                error: None,
            },
            Err(e) => ProfileRow {
                ont: name,
                status: "error".to_string(),
                el_rbox_safe: None,
                profile: None,
                error: Some(e.to_string()),
            },
        };
        if multi {
            let _ = serde_json::to_writer(&mut w, &row);
            let _ = w.write_all(b"\n");
        } else {
            let _ = serde_json::to_writer_pretty(&mut w, &row);
            let _ = w.write_all(b"\n");
        }
    }
    let _ = w.flush();
}

fn features_cmd(rest: &[String]) {
    let onts: Vec<&str> = rest
        .iter()
        .map(String::as_str)
        .filter(|a| !a.starts_with("--"))
        .collect();
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
        definers: Vec<kobayashi_marust::json_io::DefinerMeta>,
        #[serde(default)]
        source_axioms: Vec<kobayashi_marust::json_io::SourceAxiomMeta>,
        #[serde(default)]
        rules: Vec<kobayashi_marust::json_io::JRule>,
        /// declared class names (frontend meta `named`): a declared class is
        /// always a query even when its local name looks internal (contains
        /// ':' or a Q_/__/aux_/def_ prefix)
        #[serde(default)]
        named: Vec<String>,
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
    let named: std::collections::HashSet<String> = input.named.iter().cloned().collect();
    let tin = orchestrate::cb_to_ht::convert(
        &input.clauses,
        input.rbox.as_deref(),
        &named,
        &input.cardinalities,
        &input.definers,
        &input.source_axioms,
        std::env::var_os("KM_NO_HT_CARD").is_none(),
        &input.rules,
        // Default ON; cb_to_ht's `rules_active` makes it inert unless the ont
        // actually carries DL-safe rules (opt out with KM_NO_HT_RULES).
        std::env::var_os("KM_NO_HT_RULES").is_none(),
    );
    let stdout = std::io::stdout();
    if let Err(e) = serde_json::to_writer(stdout.lock(), &tin) {
        eprintln!("serialise error: {e}");
        exit(1);
    }
}

fn classify_cmd(rest: &[String]) {
    let mut lines = false;
    let mut route: Option<&str> = None;
    let mut ontology: Option<&str> = None;
    let mut index = 0;
    while index < rest.len() {
        match rest[index].as_str() {
            "--lines" => lines = true,
            "--route" => {
                index += 1;
                route = rest.get(index).map(String::as_str);
                if route.is_none() {
                    eprintln!("--route requires a route name");
                    exit(2);
                }
            }
            value if value.starts_with("--route=") => {
                route = Some(value.trim_start_matches("--route="));
            }
            value if value.starts_with('-') => {
                eprintln!("unknown classify option: {value}");
                exit(2);
            }
            value if ontology.is_none() => ontology = Some(value),
            value => {
                eprintln!("unexpected positional argument: {value}");
                exit(2);
            }
        }
        index += 1;
    }
    let Some(ontology) = ontology else {
        eprintln!("usage: km classify [--lines] [--route ROUTE] <ontology.ofn>");
        exit(2);
    };
    if let Some(requested) = route {
        if let Err(error) = requested.parse::<kobayashi_marust::routing::Route>() {
            eprintln!("{error}");
            exit(2);
        }
        std::env::set_var("KM_ROUTE", requested);
    } else if std::env::var_os("KM_ROUTE").is_none() {
        // Auto is the main reasoner's default. Standalone `km ofn` remains
        // manual unless explicitly asked, preserving its existing JSON option
        // contract and the absorption portfolio's second frontend pass.
        std::env::set_var("KM_ROUTE", "auto");
    } else if let Err(error) = std::env::var("KM_ROUTE")
        .unwrap_or_default()
        .parse::<kobayashi_marust::routing::Route>()
    {
        eprintln!("{error}");
        exit(2);
    }
    let cfg = Config::from_env();
    match orchestrate::classify(&cfg, Path::new(ontology)) {
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
