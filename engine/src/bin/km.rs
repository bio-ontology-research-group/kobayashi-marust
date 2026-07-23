//! `km`: the multi-call entry point — the whole reasoner in one binary.
//!
//!   `km classify [--lines] <ont.ofn>`  the pure-Rust classify orchestrator
//!                                      (replacement for `owl_classify.py`)
//!   `km explain <ont.ofn> ...`          one source-axiom justification
//!   `km ofn|elc|engine|tableau`        the worker reasoners
//!   `km incremental`                   stateful exact EL++/CB session
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
        Some("explain") => explain_cmd(&args[2..]),
        // worker subcommands: the orchestrator re-invokes `km <sub>` for these.
        Some("ofn") => cli::run_ofn(&args[2..]),
        Some("elc") => cli::run_elc(),
        Some("engine") => cli::run_engine(),
        Some("tableau") => cli::run_tableau(),
        Some("incremental") => cli::run_incremental(),
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
            eprintln!("usage: km classify [--lines] [--route ROUTE] [--format FORMAT] <ontology>");
            eprintln!("       km explain [OPTIONS] <ontology.ofn> subclass <SUB> <SUPER>");
            eprintln!("       km explain [OPTIONS] <ontology.ofn> unsatisfiable <CLASS>");
            eprintln!("       km explain [OPTIONS] <ontology.ofn> inconsistent");
            eprintln!("       km features [--format FORMAT] <ontology> ...");
            eprintln!("       km profile [--format FORMAT] <ontology> ...");
            eprintln!("       km routes");
            eprintln!("       km incremental   (JSONL exact EL++/CB session)");
            eprintln!("       km ofn|elc|engine|tableau   (worker subcommands)");
            exit(2);
        }
    }
}

fn explain_cmd(rest: &[String]) {
    use kobayashi_marust::orchestrate::explain::{self, ExplainError, Options, Query};

    let usage = || {
        eprintln!("usage: km explain [--pretty] [--route auto] [--max-axioms N] [--max-checks N] [--max-justifications N] [--max-source-bytes N] <ontology.ofn> subclass <SUB> <SUPER>");
        eprintln!("       km explain [OPTIONS] <ontology.ofn> unsatisfiable <CLASS>");
        eprintln!("       km explain [OPTIONS] <ontology.ofn> inconsistent");
    };
    let mut pretty = false;
    let mut route: Option<String> = None;
    let mut max_axioms = explain::DEFAULT_MAX_AXIOMS;
    let mut max_checks: Option<usize> = None;
    let mut max_justifications = explain::DEFAULT_MAX_JUSTIFICATIONS;
    let mut max_source_bytes = explain::DEFAULT_MAX_SOURCE_BYTES;
    let mut positional: Vec<&str> = Vec::new();

    let parse_usize = |option: &str, value: &str| -> usize {
        match value.parse::<usize>() {
            Ok(number) => number,
            Err(_) => {
                eprintln!("{option} requires a non-negative integer, got {value:?}");
                exit(2);
            }
        }
    };
    let mut index = 0usize;
    while index < rest.len() {
        match rest[index].as_str() {
            "--pretty" => pretty = true,
            "--route"
            | "--max-axioms"
            | "--max-checks"
            | "--max-justifications"
            | "--max-source-bytes" => {
                let option = rest[index].as_str();
                index += 1;
                let Some(value) = rest.get(index) else {
                    eprintln!("{option} requires a value");
                    usage();
                    exit(2);
                };
                match option {
                    "--route" => route = Some(value.clone()),
                    "--max-axioms" => max_axioms = parse_usize(option, value),
                    "--max-checks" => max_checks = Some(parse_usize(option, value)),
                    "--max-justifications" => max_justifications = parse_usize(option, value),
                    "--max-source-bytes" => max_source_bytes = parse_usize(option, value) as u64,
                    _ => unreachable!(),
                }
            }
            value if value.starts_with("--route=") => {
                route = Some(value.trim_start_matches("--route=").to_string())
            }
            value if value.starts_with("--max-axioms=") => {
                max_axioms = parse_usize("--max-axioms", value.trim_start_matches("--max-axioms="))
            }
            value if value.starts_with("--max-checks=") => {
                max_checks = Some(parse_usize(
                    "--max-checks",
                    value.trim_start_matches("--max-checks="),
                ))
            }
            value if value.starts_with("--max-justifications=") => {
                max_justifications = parse_usize(
                    "--max-justifications",
                    value.trim_start_matches("--max-justifications="),
                )
            }
            value if value.starts_with("--max-source-bytes=") => {
                max_source_bytes = parse_usize(
                    "--max-source-bytes",
                    value.trim_start_matches("--max-source-bytes="),
                ) as u64
            }
            value if value.starts_with('-') => {
                eprintln!("unknown explain option: {value}");
                usage();
                exit(2);
            }
            value => positional.push(value),
        }
        index += 1;
    }

    let query = match positional.as_slice() {
        [_, "subclass", sub_class, super_class] => Query::SubClass {
            sub_class: (*sub_class).to_string(),
            super_class: (*super_class).to_string(),
        },
        [_, "unsatisfiable", class_iri] => Query::Unsatisfiable {
            class_iri: (*class_iri).to_string(),
        },
        [_, "inconsistent"] => Query::Inconsistent,
        _ => {
            usage();
            exit(2);
        }
    };
    let ontology = Path::new(positional[0]);

    // Unlike `classify`, explanation extraction never inherits an ambient
    // KM_ROUTE. Its no-option default is unconditionally the production gate.
    let requested_route_name = route.unwrap_or_else(|| "auto".to_string());
    let requested_route = match requested_route_name.parse::<kobayashi_marust::routing::Route>() {
        Ok(route) => route,
        Err(error) => {
            eprintln!("{error}");
            exit(2);
        }
    };
    if !requested_route.is_explanation_safe() {
        eprintln!(
            "route {:?} is not an explanation-safe production oracle; use auto",
            requested_route.as_str()
        );
        exit(3);
    }
    std::env::set_var("KM_ROUTE", requested_route.as_str());
    let options = Options {
        max_axioms,
        max_checks: max_checks.unwrap_or_else(|| {
            max_axioms
                .saturating_add(2)
                .saturating_mul(max_justifications)
        }),
        max_source_bytes,
        max_justifications,
    };
    let cfg = Config::from_env();
    match explain::explain(&cfg, ontology, query, &options, requested_route) {
        Ok(report) => {
            use std::io::Write;
            let stdout = std::io::stdout();
            let mut writer = stdout.lock();
            let result = if pretty {
                serde_json::to_writer_pretty(&mut writer, &report)
            } else {
                serde_json::to_writer(&mut writer, &report)
            };
            if let Err(error) = result {
                eprintln!("explanation serialise error: {error}");
                exit(1);
            }
            let _ = writer.write_all(b"\n");
            let _ = writer.flush();
        }
        Err(error) => {
            eprintln!("explanation failed: {error}");
            match error {
                ExplainError::Parse(_)
                | ExplainError::Limit(_)
                | ExplainError::UnsafeRoute(_)
                | ExplainError::Classify(OrchestrateError::OutOfFragment(_)) => exit(3),
                _ => exit(1),
            }
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

    let onts = parse_multi_input_args("profile", rest);
    if onts.is_empty() {
        eprintln!("usage: km profile [--format FORMAT] <ontology> ...");
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
    let onts = parse_multi_input_args("features", rest);
    if onts.is_empty() {
        eprintln!("usage: km features [--format FORMAT] <ontology> ...");
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

fn parse_multi_input_args<'a>(command: &str, rest: &'a [String]) -> Vec<&'a str> {
    let mut onts = Vec::new();
    let mut index = 0;
    while index < rest.len() {
        match rest[index].as_str() {
            "--format" => {
                index += 1;
                let Some(format) = rest.get(index) else {
                    eprintln!("--format requires a format name");
                    exit(2);
                };
                std::env::set_var("KM_INPUT_FORMAT", format);
            }
            value if value.starts_with("--format=") => {
                std::env::set_var("KM_INPUT_FORMAT", value.trim_start_matches("--format="));
            }
            value if value.starts_with('-') => {
                eprintln!("unknown {command} option: {value}");
                exit(2);
            }
            value => onts.push(value),
        }
        index += 1;
    }
    onts
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
        nominal_abox: kobayashi_marust::json_io::NominalAboxMeta,
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
    let mut tin = orchestrate::cb_to_ht::convert(
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
    orchestrate::cb_to_ht::install_nominal_abox(&mut tin, &input.nominal_abox);
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
            "--format" => {
                index += 1;
                let Some(format) = rest.get(index) else {
                    eprintln!("--format requires a format name");
                    exit(2);
                };
                std::env::set_var("KM_INPUT_FORMAT", format);
            }
            value if value.starts_with("--format=") => {
                std::env::set_var("KM_INPUT_FORMAT", value.trim_start_matches("--format="));
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
        eprintln!("usage: km classify [--lines] [--route ROUTE] [--format FORMAT] <ontology>");
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
