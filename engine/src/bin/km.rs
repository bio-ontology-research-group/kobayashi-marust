//! `km`: the multi-call entry point — the whole reasoner in one binary.
//!
//!   `km classify [--lines | --json-edges] <ont.ofn>`  the pure-Rust classify orchestrator
//!                                      (replacement for `owl_classify.py`)
//!   `km classify --realize[=all|direct] ...`  also report the entailed types
//!                                      (`TYPE a C`) and equalities (`SAME a b`)
//!                                      of named individuals; see docs/REALIZATION.md
//!   `km explain <ont.ofn> ...`          one source-axiom justification
//!   `km ofn|elc|engine|tableau`        the worker reasoners
//!   `km incremental`                   stateful exact EL++/CB/direct-HT session
//!
//! `km classify` spawns the workers by re-invoking ITSELF with the worker
//! subcommand (`current_exe()` + `ofn`/`elc`/`engine`/`tableau`), unless a
//! `KM_*_BIN` env var overrides a worker with a standalone binary. The standalone
//! `ofn`/`elc`/`kobayashi-marust`/`tableau_cli` binaries remain as thin shims
//! over the same `cli::*` entrypoints. Either way, classifying needs no Python.

use std::path::Path;
use std::process::exit;

use kobayashi_marust::cli;

#[cfg(feature = "mimalloc")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
use kobayashi_marust::orchestrate::{self, Config, OrchestrateError};

fn main() {
    #[cfg(feature = "sample-profiler")]
    kobayashi_marust::sample_prof::install();
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
        Some("incremental-source") => cli::run_source_incremental(),
        Some("locality-probe") if args.len() == 4 => {
            let read = |p: &str| std::fs::read_to_string(p).unwrap_or_else(|e| { eprintln!("{p}: {e}"); exit(2) });
            match kobayashi_marust::source_locality::probe(&read(&args[2]), &read(&args[3])) {
                Ok(line) => println!("{line}"),
                Err(e) => { eprintln!("locality probe: {e}"); exit(1) }
            }
        }
        // Single-pass Konclude-compatible expressivity and structural stats.
        // The same profile is carried by the normal classify frontend meta, so
        // offline training and production routing cannot drift.
        Some("profile") => profile_cmd(&args[2..]),
        Some("routes") => routes_cmd(&args[2..]),
        // routing features: the structural + DL-construct vector the decision-tree
        // router consumes. `km features <ont>...` prints one JSON object per
        // ontology (NDJSON for >1) — same code path used at classify time.
        Some("features") => features_cmd(&args[2..]),
        // hidden debug subcommand: stdin {clauses, rbox?} -> TInput JSON (the
        // Phase-2 byte-identity gate vs engine/py/cb_to_ht.py)
        Some("cb_to_ht") => cb_to_ht_cmd(),
        _ => {
            eprintln!("usage: km classify [--lines | --json-edges] [--realize[=all|direct]] [--route ROUTE] [--format FORMAT] <ontology>");
            eprintln!("       km explain [OPTIONS] <ontology.ofn> subclass <SUB> <SUPER>");
            eprintln!("       km explain [OPTIONS] <ontology.ofn> unsatisfiable <CLASS>");
            eprintln!("       km explain [OPTIONS] <ontology.ofn> inconsistent");
            eprintln!("       km features [--format FORMAT] <ontology> ...");
            eprintln!("       km profile [--format FORMAT] <ontology> ...");
            eprintln!("       km routes [--help]");
            eprintln!("       km incremental   (JSONL exact EL++/CB/direct-HT session)");
            eprintln!("       km incremental-source   (JSONL complete OWL source session)");
            eprintln!("       km ofn|elc|engine|tableau   (worker subcommands)");
            exit(2);
        }
    }
}

fn explain_cmd(rest: &[String]) {
    // Workers watch this pid and exit when the supervisor is gone
    // (`cli::die_with_supervisor`). Set before any thread is spawned.
    std::env::set_var(cli::SUPERVISOR_PID_ENV, std::process::id().to_string());
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

fn routes_help() {
    println!("usage: km routes [--help]");
    println!();
    println!("Prints one route per line: `auto`, `manual`, then every named procedure.");
    println!("`km classify --route ROUTE` (or KM_ROUTE=ROUTE) forces one.");
    println!();
    println!("auto applies the source gate that selects, for each input, a mechanism");
    println!("that represents it; where none represents part of it, auto reports the");
    println!("omission as DROPPED N > 0. A forced route (manual or any named route)");
    println!("bypasses that gate. When the forced mechanism drops or approximates part of");
    println!("the input (ABox assertions outside nominal clausification, nominals,");
    println!("data-property assertions, unread DL-safe rules, keys, unknown axioms,");
    println!("clauses outside the worker's fragment), classify exits 3 and names the");
    println!("route and the dropped constructs instead of publishing a consistent answer.");
    println!("With KM_ALLOW_APPROXIMATE=1 it publishes that answer, marked by an");
    println!("`APPROXIMATE<TAB>reason` line (JSON key `approximate`) and a DROPPED count");
    println!("that includes every drop. Drops never make an inconsistent answer");
    println!("approximate: each one only weakens the ontology. Measurement-only routes");
    println!("can still be incomplete on input they represent (docs/ROUTING.md, \"Named");
    println!("procedures\" and \"Forced routes\").");
}

fn routes_cmd(rest: &[String]) {
    match rest.first().map(String::as_str) {
        None => {}
        Some("-h" | "--help") => {
            routes_help();
            exit(0);
        }
        Some(other) => {
            eprintln!("unknown routes option: {other}");
            exit(2);
        }
    }
    println!("auto\tgeneral source-profile policy: fragment gate, certificate and construct rules, portfolio default (classify default)");
    println!("manual\tpreserve individually supplied KM_* options (forced: fails closed on input it does not represent)");
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
        /// Route selected from the source profile under the current automatic
        /// production policy. This is diagnostic only: `km profile` still
        /// normalizes with the stable plain frontend below.
        #[serde(skip_serializing_if = "Option::is_none")]
        selected_route: Option<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        routing_policy: Option<&'static str>,
        /// Every general-policy rule that matches, in evaluation order; the
        /// first one selects the route (contract G4 admission counts).
        #[serde(skip_serializing_if = "Option::is_none")]
        matched_rules: Option<Vec<&'static str>>,
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
    // Profile under the automatic request so that the source certificates and
    // the selected route are the ones `km classify` computes (routing
    // contract G3). `KM_PROFILE_MANUAL=1` restores the v1.5.3 plain-frontend
    // profile.
    if std::env::var_os("KM_PROFILE_MANUAL").is_some() {
        kobayashi_marust::routing::Route::CbPlain16.apply_environment();
        std::env::set_var("KM_ROUTE", "manual");
    } else {
        std::env::set_var("KM_ROUTE", "auto");
    }
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
            Ok((_clauses, meta)) => {
                let selected_route = kobayashi_marust::routing::select(&meta.profile)
                    .as_str()
                    .to_string();
                let matched_rules = kobayashi_marust::routing::general_rules(&meta.profile)
                    .into_iter()
                    .filter(|r| r.matched)
                    .map(|r| r.rule)
                    .collect();
                ProfileRow {
                    ont: name,
                    status: "ok".to_string(),
                    el_rbox_safe: Some(meta.el_rbox_safe),
                    selected_route: Some(selected_route),
                    routing_policy: Some(match kobayashi_marust::routing::routing_policy() {
                        kobayashi_marust::routing::RoutingPolicy::General => "general",
                        kobayashi_marust::routing::RoutingPolicy::V153 => "v153",
                    }),
                    matched_rules: Some(matched_rules),
                    profile: Some(meta.profile),
                    error: None,
                }
            }
            Err(e) => ProfileRow {
                ont: name,
                status: "error".to_string(),
                el_rbox_safe: None,
                selected_route: None,
                routing_policy: None,
                matched_rules: None,
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

fn classify_help() {
    println!("usage: km classify [--lines | --json-edges] [--realize[=all|direct]] [--route ROUTE] [--format FORMAT] <ontology>");
    println!();
    println!("  --lines             tab-separated line output (default: JSON)");
    println!("  --json-edges        JSON whose subsumptions are graph edges (take their transitive closure)");
    println!("  --realize[=all]     also report every entailed named type of each named individual");
    println!("  --realize=direct    also report only the most specific entailed named types");
    println!("  --route ROUTE       force a reasoning route (see `km routes --help`); a forced");
    println!("                      route that cannot represent the input exits 3 unless");
    println!("                      KM_ALLOW_APPROXIMATE=1, which publishes an APPROXIMATE answer");
    println!("  --format FORMAT     auto, functional, owlxml, rdfxml or turtle");
    println!();
    println!("line output (--lines):");
    println!("  CONSISTENT 0|1      ontology consistency");
    println!("  DROPPED N           clauses outside the handled fragment (N > 0: incomplete answer)");
    println!("  APPROXIMATE<TAB>R   (forced route, KM_ALLOW_APPROXIMATE=1) the answer is approximate: R");
    println!("  SUB<TAB>C<TAB>D     C is subsumed by D");
    println!("  UNSAT<TAB>C         C is unsatisfiable");
    println!("  TYPE<TAB>a<TAB>C    (--realize) O entails C(a); owl:Thing is never listed");
    println!("  SAME<TAB>a<TAB>b    (--realize) O entails a = b, once per pair with a < b");
    println!("With --realize the JSON object carries the same rows under \"types\" and \"same\".");
    println!("An inconsistent ontology reports CONSISTENT 0 and no TYPE or SAME rows.");
}

fn classify_cmd(rest: &[String]) {
    // Workers watch this pid and exit when the supervisor is gone
    // (`cli::die_with_supervisor`). Set before any thread is spawned.
    std::env::set_var(cli::SUPERVISOR_PID_ENV, std::process::id().to_string());
    let mut lines = false;
    let mut graph_edges = std::env::var("KM_JSON_GRAPH_EDGES").is_ok_and(|v| v == "1");
    let mut route: Option<&str> = None;
    let mut ontology: Option<&str> = None;
    let mut realize: Option<orchestrate::realize::TypeMode> = None;
    let mut index = 0;
    while index < rest.len() {
        match rest[index].as_str() {
            "-h" | "--help" => {
                classify_help();
                exit(0);
            }
            "--lines" => lines = true,
            "--realize" | "--realize=all" => realize = Some(orchestrate::realize::TypeMode::All),
            "--realize=direct" => realize = Some(orchestrate::realize::TypeMode::Direct),
            value if value.starts_with("--realize=") => {
                eprintln!("--realize takes all or direct, got {:?}", value.trim_start_matches("--realize="));
                exit(2);
            }
            "--json-edges" => graph_edges = true,
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
    if lines && graph_edges {
        eprintln!("--lines cannot be combined with --json-edges or KM_JSON_GRAPH_EDGES=1");
        exit(2);
    }
    let Some(ontology) = ontology else {
        eprintln!("usage: km classify [--lines | --json-edges] [--realize[=all|direct]] [--route ROUTE] [--format FORMAT] <ontology>");
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
    if let Some(mode) = realize {
        if graph_edges {
            eprintln!("--realize cannot be combined with --json-edges or KM_JSON_GRAPH_EDGES=1");
            exit(2);
        }
        match orchestrate::realize::realize(&cfg, Path::new(ontology), mode) {
            Ok(res) => {
                use std::io::{BufWriter, Write};
                let stdout = std::io::stdout();
                let mut w = BufWriter::new(stdout.lock());
                if lines {
                    let _ = writeln!(w, "{}", res.to_lines());
                } else {
                    if let Err(error) = res.write_json(&mut w) {
                        eprintln!("classification serialise error: {error}");
                        exit(1);
                    }
                    let _ = w.write_all(b"\n");
                }
                let _ = w.flush();
                return;
            }
            Err(OrchestrateError::OutOfFragment(e)) => {
                eprintln!("unsupported: {e}");
                exit(3);
            }
            Err(e) => {
                eprintln!("{e}");
                exit(e.exit_code());
            }
        }
    }
    if !lines {
        match orchestrate::classify_json(&cfg, Path::new(ontology)) {
            Ok(res) => {
                if std::env::var_os("KM_TIMING").is_some() {
                    eprintln!("KM_TIMING mark: classify_json returned");
                }
                use std::io::{BufWriter, Write};
                let stdout = std::io::stdout();
                let mut w = BufWriter::new(stdout.lock());
                let written = if graph_edges {
                    res.write_graph_json(&mut w)
                } else {
                    res.write_json(&mut w)
                };
                if let Err(error) = written {
                    eprintln!("classification serialise error: {error}");
                    exit(1);
                }
                let _ = w.write_all(b"\n");
                let _ = w.flush();
                if std::env::var_os("KM_TIMING").is_some() {
                    eprintln!("KM_TIMING mark: output written");
                }
                return;
            }
            Err(OrchestrateError::OutOfFragment(e)) => {
                eprintln!("unsupported: {e}");
                exit(3);
            }
            Err(e) => {
                eprintln!("{e}");
                exit(e.exit_code());
            }
        }
    }
    match orchestrate::classify(&cfg, Path::new(ontology)) {
        Ok(res) => {
            use std::io::{BufWriter, Write};
            let stdout = std::io::stdout();
            // serde emits many small writes. Buffer them so direct streaming
            // remains fast when stdout is a network-backed harness file, while
            // still avoiding a whole-classification byte vector.
            let mut w = BufWriter::new(stdout.lock());
            let _ = writeln!(w, "{}", res.to_lines());
            let _ = w.flush();
        }
        // honest decline: outside the supported fragment (datatypes)
        Err(OrchestrateError::OutOfFragment(e)) => {
            eprintln!("unsupported: {e}");
            exit(3);
        }
        Err(e) => {
            eprintln!("{e}");
            exit(e.exit_code());
        }
    }
}
