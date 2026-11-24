//! `km`: the multi-call entry point — the whole reasoner in one binary.
//!
//!   `km classify [--lines | --json-edges] <ont.ofn>`  the pure-Rust classify orchestrator
//!                                      (replacement for `owl_classify.py`)
//!   `km classify --realize[=all|direct] ...`  also report the entailed types
//!                                      (`TYPE a C`) and equalities (`SAME a b`)
//!                                      of named individuals; see docs/REALIZATION.md
//!   `km classify --properties ...`     also report the inferred object property
//!                                      hierarchy, domains and ranges; see docs/PROPERTIES.md
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
    // E4: before any allocation of note and before any worker starts.
    kobayashi_marust::mem::disable_transparent_huge_pages();
    #[cfg(feature = "sample-profiler")]
    kobayashi_marust::sample_prof::install();
    // Before any route bundle rewrites KM_THREADS (`routing::apply_environment`).
    kobayashi_marust::routing::capture_caller_thread_budget();
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
            eprintln!("usage: km classify [--lines | --json-edges] [--realize[=all|direct]] [--properties] [--top] [--route ROUTE] [--format FORMAT] [--iris source|full] <ontology>");
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
    strip_worker_only_environment("explain");
    // Workers watch this pid and exit when the supervisor is gone
    // (`cli::die_with_supervisor`). Set before any thread is spawned.
    std::env::set_var(cli::SUPERVISOR_PID_ENV, std::process::id().to_string());
    // E11: one run directory for every temporary file, removed on exit.
    kobayashi_marust::orchestrate::tmpfile::install_supervisor_run_dir();
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
    println!("usage: km classify [--lines | --json-edges] [--realize[=all|direct]] [--properties] [--top] [--route ROUTE] [--format FORMAT] [--iris source|full] <ontology>");
    println!();
    println!("  --lines             tab-separated line output (default: JSON)");
    println!("  --json-edges        JSON whose subsumptions are graph edges (take their transitive closure)");
    println!("  --realize[=all]     also report every entailed named type of each named individual");
    println!("  --realize=direct    also report only the most specific entailed named types");
    println!("  --properties        also report the inferred object property hierarchy, domains and ranges");
    println!("  --export-model FILE after the answer, write a model of the ontology to FILE (JSON lines, docs/MODEL-EXPORT.md)");
    println!("  --export-model-budget SECONDS");
    println!("                      wall-clock budget for post-classify model verification/witness probes");
    println!("                      (default: 1x classify_time + 2 s); writes status=\"partial\" when exceeded");
    println!("  --values            also report every entailed object property assertion between named individuals");
    println!("  --different         also report every entailed pair of different named individuals");
    println!("  --data-properties   also report the data property hierarchy, empty data properties,");
    println!("                      domains and disjoint data properties (docs/PROPERTIES.md)");
    println!("  --top               also report the named classes equivalent to owl:Thing");
    println!("  --route ROUTE       force a reasoning route (see `km routes --help`); a forced");
    println!("                      route that cannot represent the input exits 3 unless");
    println!("                      KM_ALLOW_APPROXIMATE=1, which publishes an APPROXIMATE answer");
    println!("  --format FORMAT     auto, functional, owlxml, rdfxml or turtle");
    println!("  --iris source|full  entity names in every output: source (default) as the input spells them");
    println!("                      (ex:A stays ex:A); full: every name as its full IRI, expanded with the");
    println!("                      input's Prefix declarations, for every input syntax (env KM_IRIS;");
    println!("                      docs/INPUT-FORMATS.md, \"Entity names in output\")");
    println!("  --unknown-datatypes=strict|free");
    println!("                      strict (default): reject a datatype outside the OWL 2 datatype map;");
    println!("                      free: read it as a fresh datatype and its literals as opaque values");
    println!("                      (see docs/DATATYPES.md, \"Unknown datatypes\")");
    println!("  --lenient           accept inputs OWL API and HermiT load in Protege by a source-level");
    println!("                      rewrite to valid OWL 2 DL (see docs/V1.7.0-LENIENT-INPUT.md)");
    println!();
    println!("line output (--lines):");
    println!("  CONSISTENT 0|1      ontology consistency");
    println!("  DROPPED N           clauses outside the handled fragment (N > 0: incomplete answer)");
    println!("  APPROXIMATE<TAB>R   (forced route, KM_ALLOW_APPROXIMATE=1) the answer is approximate: R");
    println!("  LENIENT<TAB>W       (--lenient) source rewrite applied before the certified pipeline: W");
    println!("  SUB<TAB>C<TAB>D     C is subsumed by D");
    println!("  UNSAT<TAB>C         C is unsatisfiable");
    println!("  TYPE<TAB>a<TAB>C    (--realize) O entails C(a); owl:Thing is never listed");
    println!("  SAME<TAB>a<TAB>b    (--realize) O entails a = b, once per pair with a < b");
    println!("  TOP<TAB>C           (--top) C is equivalent to owl:Thing");
    println!("  SUBPROP<TAB>r<TAB>f (--properties) O entails r SubPropertyOf f; r named and not empty,");
    println!("                      f named or ObjectInverseOf(s); owl:topObjectProperty is never listed");
    println!("  TOPPROP<TAB>r       (--properties) r is equivalent to owl:topObjectProperty");
    println!("  BOTPROP<TAB>r       (--properties) r is equivalent to owl:bottomObjectProperty;");
    println!("                      an empty property has no SUBPROP, DOMAIN or RANGE rows");
    println!("  DOMAIN<TAB>r<TAB>C  (--properties) O entails ObjectPropertyDomain(r C); owl:Thing is never listed");
    println!("  RANGE<TAB>r<TAB>C   (--properties) O entails ObjectPropertyRange(r C); owl:Thing is never listed");
    println!("  VALUE<TAB>r<TAB>a<TAB>b (--values) O entails r(a, b), r a named object property");
    println!("  DIFFERENT<TAB>a<TAB>b (--different) O entails a != b, once per pair with a < b");
    println!("  SUBDATAPROP<TAB>p<TAB>q (--data-properties) O entails p SubDataPropertyOf q; p not empty");
    println!("  BOTDATAPROP<TAB>p   (--data-properties) data property p is empty");
    println!("  DATADOMAIN<TAB>p<TAB>C (--data-properties) O entails DataPropertyDomain(p C)");
    println!("  DISJOINTDATAPROP<TAB>p<TAB>q (--data-properties) O entails DisjointDataProperties(p q)");
    println!("  NODATADISJOINT      (--data-properties) over 64 data properties: no DISJOINTDATAPROP rows computed");
    println!("With --realize the JSON object carries the same rows under \"types\" and \"same\";");
    println!("with --properties under \"subproperties\", \"topproperties\", \"bottomproperties\",");
    println!("\"domains\" and \"ranges\" (see docs/PROPERTIES.md); with --top under \"top\".");
    println!("An inconsistent ontology reports CONSISTENT 0 and no TOP, TYPE, SAME or property rows.");
}

fn classify_cmd(rest: &[String]) {
    strip_worker_only_environment("classify");
    // Run the configuration the release benchmarks measured
    // (`routing::RELEASE_DEFAULTS`); set before any worker is spawned, so the
    // workers inherit it.
    kobayashi_marust::routing::apply_release_defaults();
    // Workers watch this pid and exit when the supervisor is gone
    // (`cli::die_with_supervisor`). Set before any thread is spawned.
    std::env::set_var(cli::SUPERVISOR_PID_ENV, std::process::id().to_string());
    // E11: one run directory for every temporary file, removed on exit.
    kobayashi_marust::orchestrate::tmpfile::install_supervisor_run_dir();
    let mut lines = false;
    let mut graph_edges = std::env::var("KM_JSON_GRAPH_EDGES").is_ok_and(|v| v == "1");
    let mut route: Option<&str> = None;
    let mut ontology: Option<&str> = None;
    let mut realize: Option<orchestrate::realize::TypeMode> = None;
    let mut properties = false;
    let mut data_properties = false;
    let mut values = false;
    let mut different = false;
    let mut top = false;
    let mut export_model: Option<String> = None;
    let mut export_model_budget: Option<f64> = None;
    let mut iris = match orchestrate::output_names::IriMode::from_env() {
        Ok(mode) => mode,
        Err(error) => {
            eprintln!("KM_IRIS: {error}");
            exit(2);
        }
    };
    let mut index = 0;
    while index < rest.len() {
        match rest[index].as_str() {
            "-h" | "--help" => {
                classify_help();
                exit(0);
            }
            "--iris" | "--iris=source" | "--iris=full" => {
                let value = if rest[index] == "--iris" {
                    index += 1;
                    rest.get(index).map(String::as_str).unwrap_or("")
                } else {
                    rest[index].trim_start_matches("--iris=")
                };
                iris = match orchestrate::output_names::IriMode::parse(value) {
                    Ok(mode) => mode,
                    Err(error) => {
                        eprintln!("{error}");
                        exit(2);
                    }
                };
            }
            value if value.starts_with("--iris=") => {
                eprintln!("--iris takes source or full, got {:?}", value.trim_start_matches("--iris="));
                exit(2);
            }
            "--lines" => lines = true,
            "--realize" | "--realize=all" => realize = Some(orchestrate::realize::TypeMode::All),
            "--realize=direct" => realize = Some(orchestrate::realize::TypeMode::Direct),
            value if value.starts_with("--realize=") => {
                eprintln!("--realize takes all or direct, got {:?}", value.trim_start_matches("--realize="));
                exit(2);
            }
            "--properties" => properties = true,
            "--data-properties" => data_properties = true,
            "--values" => values = true,
            "--different" => different = true,
            "--top" => top = true,
            "--json-edges" => graph_edges = true,
            "--export-model" => {
                index += 1;
                export_model = rest.get(index).cloned();
                if export_model.is_none() {
                    eprintln!("--export-model requires a file name");
                    exit(2);
                }
            }
            value if value.starts_with("--export-model=") => {
                export_model = Some(value.trim_start_matches("--export-model=").to_string());
            }
            "--export-model-budget" => {
                index += 1;
                let Some(val) = rest.get(index) else {
                    eprintln!("--export-model-budget requires a positive number of seconds");
                    exit(2);
                };
                match val.parse::<f64>() {
                    Ok(secs) if secs.is_finite() && secs > 0.0 => export_model_budget = Some(secs),
                    _ => {
                        eprintln!("--export-model-budget requires a positive number of seconds, got {val:?}");
                        exit(2);
                    }
                }
            }
            value if value.starts_with("--export-model-budget=") => {
                let raw = value.trim_start_matches("--export-model-budget=");
                match raw.parse::<f64>() {
                    Ok(secs) if secs.is_finite() && secs > 0.0 => export_model_budget = Some(secs),
                    _ => {
                        eprintln!("--export-model-budget requires a positive number of seconds, got {raw:?}");
                        exit(2);
                    }
                }
            }
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
            // W7: datatypes outside the OWL 2 datatype map (see
            // `frontend::conformance::unknown_datatypes_free`).
            "--unknown-datatypes=strict" => std::env::remove_var("KM_UNKNOWN_DATATYPES"),
            "--unknown-datatypes=free" => std::env::set_var("KM_UNKNOWN_DATATYPES", "free"),
            "--lenient" | "--lenient=true" | "--lenient=1" => std::env::set_var("KM_LENIENT", "1"),
            "--lenient=false" | "--lenient=0" => std::env::remove_var("KM_LENIENT"),
            value if value.starts_with("--lenient=") => {
                eprintln!("--lenient takes true or false, got {value:?}");
                exit(2);
            }
            value if value.starts_with("--unknown-datatypes") => {
                eprintln!("--unknown-datatypes takes strict or free, got {value:?}");
                exit(2);
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
        eprintln!("usage: km classify [--lines | --json-edges] [--realize[=all|direct]] [--properties] [--top] [--route ROUTE] [--format FORMAT] [--iris source|full] <ontology>");
        exit(2);
    };
    // `--iris full`: every printed entity name as its full IRI
    // (`orchestrate::output_names`, docs/INPUT-FORMATS.md, "Entity names in output"). Read before
    // classification so a malformed prefix header fails at once.
    let full_iris = match iris {
        orchestrate::output_names::IriMode::Source => None,
        orchestrate::output_names::IriMode::Full => {
            match orchestrate::output_names::FullIris::for_input(Path::new(ontology)) {
                Ok(names) => Some(names),
                Err(error) => {
                    eprintln!("{error}");
                    exit(error.exit_code());
                }
            }
        }
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
    // KM_LEAN_CHECKERS=<dir>: certificates are checked by the Lean checkers
    // in <dir>; a rejection publishes nothing (see `lean_checkers`).
    let lean_run = kobayashi_marust::lean_checkers::start_classify();
    let lean_gate = move |lean_run: Option<kobayashi_marust::lean_checkers::Run>| {
        if let Some(run) = lean_run {
            if let Err(message) = run.finish() {
                eprintln!("{message}");
                exit(kobayashi_marust::lean_checkers::REJECTED_EXIT);
            }
        }
    };
    // KM_FRONTEND_CHECK=1: the OWL reference procedure checks the final
    // answer; a disagreement publishes nothing, as a rejected Lean checker
    // does (see `orchestrate::frontend_check`).
    let frontend_gate = |checked: Result<(), String>| {
        if let Err(message) = checked {
            eprintln!("{message}");
            exit(kobayashi_marust::lean_checkers::REJECTED_EXIT);
        }
    };
    let cfg = Config::from_env();
    if export_model.is_some() {
        orchestrate::model_export::begin_session(export_model_budget);
    }
    // `--export-model FILE`: after the answer is written, the model of the
    // same clause stream (docs/MODEL-EXPORT.md). Never runs otherwise.
    let export = |cfg: &Config| {
        if let Some(file) = &export_model {
            match orchestrate::model_export::finish_and_write(
                cfg,
                Path::new(ontology),
                Path::new(file),
            ) {
                Ok(status) => eprintln!("{status}"),
                Err(error) => {
                    eprintln!("model export failed: {error}");
                    exit(1);
                }
            }
        }
    };
    if realize.is_some() || properties || top || data_properties || values || different {
        if graph_edges {
            eprintln!("--realize, --properties and --top cannot be combined with --json-edges or KM_JSON_GRAPH_EDGES=1");
            exit(2);
        }
        let realized = orchestrate::realize::classify_extended(
            &cfg,
            Path::new(ontology),
            realize,
            properties,
            top,
            data_properties,
            values,
            different,
        );
        lean_gate(lean_run);
        match realized {
            Ok(mut res) => {
                if let Some(names) = &full_iris {
                    names.extended(&mut res);
                }
                use std::io::{BufWriter, Write};
                let stdout = std::io::stdout();
                let mut w = BufWriter::new(stdout.lock());
                if lines {
                    let _ = writeln!(w, "{}", res.to_lines());
                } else {
                    if let Err(error) = res.write_json(&mut w, realize.is_some()) {
                        eprintln!("classification serialise error: {error}");
                        exit(1);
                    }
                    let _ = w.write_all(b"\n");
                }
                let _ = w.flush();
                drop(w);
                export(&cfg);
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
        let classified = orchestrate::classify_json(&cfg, Path::new(ontology));
        lean_gate(lean_run);
        match classified {
            Ok(mut res) => {
                frontend_gate(res.frontend_check_gate(Path::new(ontology)));
                if std::env::var_os("KM_TIMING").is_some() {
                    eprintln!("KM_TIMING mark: classify_json returned");
                }
                if let Some(names) = &full_iris {
                    names.json(&mut res);
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
                drop(w);
                export(&cfg);
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
    let classified = orchestrate::classify(&cfg, Path::new(ontology));
    lean_gate(lean_run);
    match classified {
        Ok(mut res) => {
            frontend_gate(res.frontend_check_gate(Path::new(ontology)));
            if let Some(names) = &full_iris {
                names.classification(&mut res);
            }
            use std::io::{BufWriter, Write};
            let stdout = std::io::stdout();
            // serde emits many small writes. Buffer them so direct streaming
            // remains fast when stdout is a network-backed harness file, while
            // still avoiding a whole-classification byte vector.
            let mut w = BufWriter::new(stdout.lock());
            let _ = writeln!(w, "{}", res.to_lines());
            let _ = w.flush();
            drop(w);
            export(&cfg);
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

/// Strip worker-only protocol variables from the user's environment
/// (`routing::WORKER_ONLY_KEYS`), so no published answer depends on them.
fn strip_worker_only_environment(command: &str) {
    let removed = kobayashi_marust::routing::strip_worker_only_environment();
    if !removed.is_empty() {
        eprintln!(
            "km {command}: ignoring worker-only environment variable(s) {}",
            removed.join(", ")
        );
    }
}
